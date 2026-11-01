#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Jembatan UCI lokal untuk userscript "Catur Bantu".

Jalanin di Termux:  python bridge.py
Server cuma dengerin 127.0.0.1 (nggak kebuka ke jaringan).

  GET  /ping     -> status engine + batas UCI_Elo
  POST /analyze  -> {fen, multipv, movetime, options} -> kandidat langkah

Cuma pakai library bawaan Python (nggak perlu pip).
"""
import argparse
import json
import os
import queue
import re
import shlex
import signal
import subprocess
import sys
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

VERSION = "1.0.0"
ALLOWED_ORIGIN = "https://www.chess.com"
MAX_BODY = 4096

# Format FEN dasar. Stockfish 19 langsung mati kalau dikasih FEN jelek,
# jadi di sini kita tolak duluan sebelum nyampe ke engine.
FEN_RE = re.compile(
    r"^[1-8pnbrqkPNBRQK/]{15,71} [wb] (?:-|[KQkq]{1,4}) (?:-|[a-h][36]) \d{1,3} \d{1,4}$"
)

# Opsi yang boleh diatur dari userscript: nama -> (tipe, min, max)
OPTION_RULES = {
    "MultiPV": ("int", 1, 32),
    "UCI_LimitStrength": ("bool", None, None),
    "UCI_Elo": ("int", 100, 4000),
    "Skill Level": ("int", 0, 20),
}

ARCHIVE_SUFFIXES = (
    ".zip", ".tar", ".gz", ".xz", ".bz2", ".7z", ".txt", ".md", ".py", ".js",
    ".json", ".sh", ".nnue", ".wasm", ".apk", ".so",
)


def log(msg):
    print(msg, flush=True)


class EngineDead(Exception):
    pass


class EngineRejected(Exception):
    pass


# ---------------------------------------------------------------------------
# Parsing UCI
# ---------------------------------------------------------------------------
INFO_DEPTH = re.compile(r"\bdepth (\d+)")
INFO_MPV = re.compile(r"\bmultipv (\d+)")
INFO_SCORE = re.compile(r"\bscore (cp|mate) (-?\d+)( lowerbound| upperbound)?")
INFO_PV = re.compile(r"\bpv ((?:[a-h][1-8][a-h][1-8][qrbn]?\s*)+)")


def parse_info(line):
    """Balikin dict satu baris 'info ...' atau None kalau bukan baris skor yang lengkap."""
    if not line.startswith("info ") or " score " not in line or " pv " not in line:
        return None
    ms = INFO_SCORE.search(line)
    if not ms or ms.group(3):  # lewati lowerbound/upperbound (belum final)
        return None
    md = INFO_DEPTH.search(line)
    mp = INFO_PV.search(line)
    if not md or not mp:
        return None
    mm = INFO_MPV.search(line)
    pv = mp.group(1).split()
    entry = {
        "rank": int(mm.group(1)) if mm else 1,
        "depth": int(md.group(1)),
        "move": pv[0],
        "pv": pv[:6],
        "cp": None,
        "mate": None,
    }
    if ms.group(1) == "cp":
        entry["cp"] = int(ms.group(2))
    else:
        entry["mate"] = int(ms.group(2))
    return entry


class LineCollector:
    """
    Kumpulin baris 'info' per iterasi (satu blok = satu kedalaman, rank 1..N berurutan).
    Pas pencarian dipotong waktu, Stockfish nge-print ulang baris dengan label kedalaman yang
    campur aduk; makanya kita nyari blok TERAKHIR yang lengkap (rank 1..N, langkah unik),
    bukan nimpa per-rank.
    """

    def __init__(self):
        self.blocks = []
        self.cur = {}

    def add(self, e):
        if e["rank"] == 1 and self.cur:
            self.blocks.append(self.cur)
            self.cur = {}
        self.cur[e["rank"]] = e

    def result(self):
        blocks = self.blocks + ([self.cur] if self.cur else [])
        if not blocks:
            return [], 0

        def rows(b):
            return [b[k] for k in sorted(b)]

        def ok(b, n):
            r = rows(b)
            return (
                len(r) == n
                and [x["rank"] for x in r] == list(range(1, n + 1))
                and len({x["move"] for x in r}) == n
            )

        n = max(len(b) for b in blocks)
        for b in reversed(blocks):
            if ok(b, n):
                r = rows(b)
                return r, max(x["depth"] for x in r)
        # darurat: blok terbesar yang paling akhir, buang langkah dobel
        for b in reversed(blocks):
            if len(b) == n:
                seen, r = set(), []
                for x in rows(b):
                    if x["move"] not in seen:
                        seen.add(x["move"])
                        r.append(x)
                return r, max(x["depth"] for x in r)
        return [], 0


OPT_RE = re.compile(r"^option name (.+?) type (spin|check|combo|button|string)(.*)$")


def parse_option(line):
    m = OPT_RE.match(line)
    if not m:
        return None
    name, typ, rest = m.group(1), m.group(2), m.group(3)
    info = {"type": typ}
    for key in ("default", "min", "max"):
        mm = re.search(r"\b%s (\S+)" % key, rest)
        if mm:
            info[key] = mm.group(1)
    return name, info


# ---------------------------------------------------------------------------
# Engine
# ---------------------------------------------------------------------------
class Engine:
    def __init__(self, cmd, threads, hash_mb):
        self.cmd = cmd
        self.threads = threads
        self.hash_mb = hash_mb
        self.proc = None
        self.q = queue.Queue()
        self.name = "?"
        self.options = {}
        self.applied = {}
        self.searching = False
        self.lock = threading.Lock()  # satu pencarian dalam satu waktu
        self.restarts = 0
        self.gen = 0  # naik tiap ada request baru (buat batalin pencarian lama)

    # -- proses ------------------------------------------------------------
    @staticmethod
    def _reader(proc, q):
        try:
            for line in proc.stdout:
                q.put(line.rstrip("\r\n"))
        except Exception:
            pass
        q.put(None)

    def alive(self):
        return self.proc is not None and self.proc.poll() is None

    def kill(self):
        p = self.proc
        self.proc = None
        self.searching = False
        if p is not None:
            try:
                p.kill()
            except Exception:
                pass
            try:
                p.wait(timeout=2)
            except Exception:
                pass

    def start(self):
        self.kill()
        self.q = queue.Queue()
        self.applied = {}
        self.options = {}
        try:
            self.proc = subprocess.Popen(
                self.cmd,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                bufsize=1,
            )
        except OSError as e:
            raise EngineDead("engine nggak bisa dijalanin: %s" % e)
        threading.Thread(target=self._reader, args=(self.proc, self.q), daemon=True).start()
        self._send("uci")
        for line in self._read_until(lambda l: l == "uciok", 20):
            if line.startswith("id name "):
                self.name = line[8:].strip()
            else:
                opt = parse_option(line)
                if opt:
                    self.options[opt[0]] = opt[1]
        pre = {}
        if "Threads" in self.options:
            pre["Threads"] = self.threads
        if "Hash" in self.options:
            pre["Hash"] = self.hash_mb
        for k, v in pre.items():
            self._send("setoption name %s value %s" % (k, v))
            self.applied[k] = v
        self._send("isready")
        self._read_until(lambda l: l == "readyok", 20)

    def ensure(self):
        if not self.alive():
            if self.proc is not None:
                self.restarts += 1
                log("[!] engine mati, nyalain ulang...")
            self.start()

    # -- IO ----------------------------------------------------------------
    def _send(self, text):
        try:
            self.proc.stdin.write(text + "\n")
            self.proc.stdin.flush()
        except Exception:
            raise EngineDead("engine nggak bisa dikirimi perintah")

    def _read_until(self, pred, timeout):
        """Baca baris sampai pred(baris) benar. Balikin semua baris sebelum itu."""
        end = time.time() + timeout
        out = []
        while True:
            left = end - time.time()
            if left <= 0:
                raise EngineDead("engine nggak jawab (timeout)")
            try:
                line = self.q.get(timeout=left)
            except queue.Empty:
                raise EngineDead("engine nggak jawab (timeout)")
            if line is None:
                raise EngineDead("engine berhenti mendadak")
            if line.startswith("info string CRITICAL ERROR"):
                raise EngineRejected(line)
            if pred(line):
                return out
            out.append(line)

    # -- opsi --------------------------------------------------------------
    def _apply_options(self, opts):
        changed = False
        for name, val in opts.items():
            if name not in self.options:
                continue
            if self.applied.get(name) == val:
                continue
            if isinstance(val, bool):
                text = "true" if val else "false"
            else:
                text = str(val)
            self._send("setoption name %s value %s" % (name, text))
            self.applied[name] = val
            changed = True
        if changed:
            self._send("isready")
            self._read_until(lambda l: l == "readyok", 10)

    def clamp_option(self, name, val):
        rule = OPTION_RULES[name]
        if rule[0] == "bool":
            return bool(val)
        v = int(val)
        lo, hi = rule[1], rule[2]
        info = self.options.get(name, {})
        try:
            if "min" in info:
                lo = max(lo, int(info["min"]))
            if "max" in info:
                hi = min(hi, int(info["max"]))
        except ValueError:
            pass
        return max(lo, min(hi, v))

    # -- analisis ----------------------------------------------------------
    def request_stop(self):
        """Dipanggil request baru biar pencarian lama cepet kelar."""
        self.gen += 1
        if self.searching and self.alive():
            try:
                self._send("stop")
            except EngineDead:
                pass

    def _run_search(self, movetime):
        """Kirim 'go' lalu kumpulin info sampai bestmove. Balikin (collector, best, ponder)."""
        t0 = time.time()
        self._send("go movetime %d" % movetime)
        self.searching = True
        coll = LineCollector()
        best = None
        ponder = None
        deadline = t0 + movetime / 1000.0 + 4.0
        stopped = False
        try:
            while True:
                left = deadline - time.time()
                if left <= 0:
                    if stopped:
                        self.kill()
                        raise EngineDead("engine nggak ngasih bestmove")
                    self._send("stop")
                    stopped = True
                    deadline = time.time() + 2.0
                    continue
                try:
                    line = self.q.get(timeout=left)
                except queue.Empty:
                    continue
                if line is None:
                    raise EngineDead("engine berhenti mendadak")
                if line.startswith("info string CRITICAL ERROR"):
                    raise EngineRejected(line)
                if line.startswith("bestmove"):
                    parts = line.split()
                    if len(parts) > 1 and parts[1] != "(none)":
                        best = parts[1]
                    if "ponder" in parts:
                        i = parts.index("ponder")
                        if i + 1 < len(parts):
                            ponder = parts[i + 1]
                    break
                e = parse_info(line)
                if e:
                    coll.add(e)
        finally:
            self.searching = False
        return coll, best, ponder

    def _clean_options(self, options, extra=None):
        opts = {}
        for k, v in (options or {}).items():
            if k in OPTION_RULES:
                opts[k] = self.clamp_option(k, v)
        if extra:
            for k, v in extra.items():
                opts.setdefault(k, v)
        return opts

    def analyze(self, fen, multipv, movetime, options, probe=None):
        """
        Fase 1: pencarian kekuatan penuh dengan MultiPV -> daftar kandidat yang bersih.
        Fase 2 (opsional, 'probe'): pencarian pendek dengan batas kekuatan (UCI_Elo / Skill Level)
        cuma buat ngambil 'bestmove' versi lemah. Baris info dari mode terbatas sengaja
        nggak dipakai: Stockfish nuker urutannya pas mode skill, jadi nggak bisa dipercaya.
        """
        with self.lock:
            my_gen = self.gen
            self.ensure()
            t0 = time.time()
            base = {"UCI_LimitStrength": False, "Skill Level": 20}
            opts = self._clean_options(options, base)
            opts["MultiPV"] = self.clamp_option("MultiPV", multipv)
            self._apply_options(opts)
            self._send("position fen " + fen)
            coll, best, ponder = self._run_search(movetime)
            rows, depth = coll.result()
            out = {
                "bestmove": best,
                "ponder": ponder,
                "lines": rows,
                "depth": depth,
                "probe_bestmove": None,
            }
            if probe and best and my_gen == self.gen:
                popts = self._clean_options(probe.get("options"), {})
                popts["MultiPV"] = self.clamp_option("MultiPV", probe.get("multipv", 6))
                pt = max(20, min(2000, int(probe.get("movetime", 120))))
                self._apply_options(popts)
                self._send("position fen " + fen)
                _, pbest, _ = self._run_search(pt)
                out["probe_bestmove"] = pbest
            out["cancelled"] = my_gen != self.gen
            out["ms"] = int((time.time() - t0) * 1000)
            return out

    def info(self):
        def rng(name):
            o = self.options.get(name)
            if not o or "min" not in o:
                return None
            try:
                return {"min": int(o["min"]), "max": int(o["max"])}
            except (ValueError, KeyError):
                return None

        return {
            "name": self.name,
            "uci_elo": rng("UCI_Elo"),
            "skill": rng("Skill Level"),
            "threads": self.applied.get("Threads"),
            "hash": self.applied.get("Hash"),
            "restarts": self.restarts,
        }


# ---------------------------------------------------------------------------
# Cari file engine
# ---------------------------------------------------------------------------
def is_elf(path):
    try:
        with open(path, "rb") as f:
            return f.read(4) == b"\x7fELF"
    except OSError:
        return False


def find_engine():
    home = os.path.expanduser("~")
    here = os.path.dirname(os.path.abspath(__file__))
    roots = [os.path.join(home, "stockfish"), here, home, os.getcwd()]
    seen = set()
    cands = []
    for root in roots:
        root = os.path.abspath(root)
        if root in seen or not os.path.isdir(root):
            continue
        seen.add(root)
        base_depth = root.rstrip(os.sep).count(os.sep)
        for dp, dns, fns in os.walk(root):
            if dp.count(os.sep) - base_depth >= 4:
                dns[:] = []
            dns[:] = [d for d in dns if not d.startswith(".") and d not in ("storage", "node_modules")]
            for fn in fns:
                low = fn.lower()
                if "stockfish" not in low or low.endswith(ARCHIVE_SUFFIXES):
                    continue
                p = os.path.join(dp, fn)
                try:
                    if os.path.getsize(p) < 2 * 1024 * 1024:
                        continue
                except OSError:
                    continue
                if is_elf(p):
                    score = 0
                    for w in ("arm64", "android", "universal"):
                        if w in low:
                            score += 1
                    cands.append((-score, len(p), p))
        if cands:
            break
    if not cands:
        return None
    cands.sort()
    return cands[0][2]


def resolve_engine(arg):
    if arg and arg != "auto":
        cmd = shlex.split(arg)
    else:
        path = find_engine()
        if not path:
            return None
        cmd = [path]
    exe = cmd[0]
    if os.path.isfile(exe) and not os.access(exe, os.X_OK):
        try:
            os.chmod(exe, os.stat(exe).st_mode | 0o111)
            log("[i] chmod +x %s" % exe)
        except OSError as e:
            log("[!] gagal chmod: %s" % e)
    return cmd


# ---------------------------------------------------------------------------
# HTTP
# ---------------------------------------------------------------------------
ENGINE = None


class Handler(BaseHTTPRequestHandler):
    server_version = "CaturBantuBridge/" + VERSION
    protocol_version = "HTTP/1.0"

    def log_message(self, fmt, *args):
        pass

    def _headers(self, code, length):
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(length))
        origin = self.headers.get("Origin")
        if origin == ALLOWED_ORIGIN:
            self.send_header("Access-Control-Allow-Origin", origin)
            self.send_header("Vary", "Origin")
        self.send_header("Access-Control-Allow-Private-Network", "true")
        self.send_header("Cache-Control", "no-store")
        self.end_headers()

    def _json(self, code, obj):
        body = json.dumps(obj).encode("utf-8")
        try:
            self._headers(code, len(body))
            self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def do_OPTIONS(self):
        self.send_response(204)
        origin = self.headers.get("Origin")
        if origin == ALLOWED_ORIGIN:
            self.send_header("Access-Control-Allow-Origin", origin)
            self.send_header("Vary", "Origin")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.send_header("Access-Control-Allow-Private-Network", "true")
        self.send_header("Content-Length", "0")
        self.end_headers()

    def do_GET(self):
        if self.path.split("?")[0] != "/ping":
            return self._json(404, {"ok": False, "error": "tidak ada"})
        try:
            if not ENGINE.alive():
                with ENGINE.lock:
                    ENGINE.ensure()
            self._json(200, {"ok": True, "bridge": VERSION, "engine": ENGINE.info()})
        except (EngineDead, EngineRejected) as e:
            self._json(200, {"ok": False, "error": str(e)})

    def do_POST(self):
        if self.path.split("?")[0] != "/analyze":
            return self._json(404, {"ok": False, "error": "tidak ada"})
        try:
            n = int(self.headers.get("Content-Length") or 0)
            if n <= 0 or n > MAX_BODY:
                return self._json(400, {"ok": False, "error": "body tidak valid"})
            req = json.loads(self.rfile.read(n).decode("utf-8"))
            fen = str(req.get("fen", "")).strip()
            if not FEN_RE.match(fen):
                return self._json(400, {"ok": False, "error": "FEN tidak valid"})
            multipv = int(req.get("multipv", 6))
            movetime = max(20, min(5000, int(req.get("movetime", 300))))
            options = req.get("options") or {}
            if not isinstance(options, dict):
                options = {}
            probe = req.get("probe")
            if not isinstance(probe, dict):
                probe = None
        except (ValueError, TypeError, KeyError):
            return self._json(400, {"ok": False, "error": "permintaan tidak valid"})

        ENGINE.request_stop()
        last_err = "?"
        for attempt in range(2):
            try:
                res = ENGINE.analyze(fen, multipv, movetime, options, probe)
                res["ok"] = True
                res["engine"] = ENGINE.info()["name"]
                return self._json(200, res)
            except EngineRejected as e:
                last_err = "engine nolak posisi: %s" % e
                log("[!] " + last_err)
                ENGINE.kill()  # Stockfish 19 keluar sendiri setelah error ini
                break
            except EngineDead as e:
                last_err = str(e)
                log("[!] %s (percobaan %d)" % (last_err, attempt + 1))
                ENGINE.kill()
        self._json(200, {"ok": False, "error": last_err})


def main():
    global ENGINE
    ap = argparse.ArgumentParser(description="Jembatan UCI lokal buat Catur Bantu")
    ap.add_argument("--engine", default="auto", help="path/perintah engine (default: cari otomatis)")
    ap.add_argument("--port", type=int, default=8765)
    ap.add_argument("--threads", type=int, default=min(4, os.cpu_count() or 2))
    ap.add_argument("--hash", type=int, default=64, help="Hash dalam MB")
    args = ap.parse_args()

    cmd = resolve_engine(args.engine)
    if not cmd:
        log("[X] File Stockfish nggak ketemu.")
        log("    Ekstrak arsipnya ke ~/stockfish lalu jalanin lagi, atau pakai:")
        log("    python bridge.py --engine /path/ke/stockfish")
        sys.exit(1)

    ENGINE = Engine(cmd, args.threads, args.hash)
    log("[i] Engine: %s" % " ".join(cmd))
    try:
        ENGINE.start()
    except (EngineDead, EngineRejected) as e:
        log("[X] Engine gagal jalan: %s" % e)
        log("    Cek: file bener buat arm64 Android? sudah chmod +x? ada di ~ (bukan /sdcard)?")
        sys.exit(1)
    inf = ENGINE.info()
    log("[i] %s | UCI_Elo %s | threads %s | hash %s MB" % (
        inf["name"],
        "%d-%d" % (inf["uci_elo"]["min"], inf["uci_elo"]["max"]) if inf["uci_elo"] else "?",
        inf["threads"] or "-",
        inf["hash"] or "-",
    ))

    try:
        srv = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    except OSError as e:
        log("[X] Port %d nggak bisa dipakai: %s" % (args.port, e))
        log("    Mungkin jembatan sudah jalan di sesi Termux lain? Tutup dulu, atau pakai --port lain.")
        sys.exit(1)
    srv.daemon_threads = True

    def bye(*_):
        log("\n[i] Berhenti.")
        ENGINE.kill()
        os._exit(0)

    signal.signal(signal.SIGINT, bye)
    signal.signal(signal.SIGTERM, bye)
    log("[OK] Jembatan siap di http://127.0.0.1:%d  (Ctrl+C buat berhenti)" % args.port)
    srv.serve_forever()


if __name__ == "__main__":
    main()
