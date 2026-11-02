// ==UserScript==
// @name         Catur Bantu
// @namespace    local.caturbantu
// @version      1.0.0
// @description  Saran langkah + panah (Stockfish 19) di chess.com
// @match        https://www.chess.com/*
// @run-at       document-idle
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_xmlhttpRequest
// @connect      127.0.0.1
// @connect      localhost
// @connect      github.com
// @connect      githubusercontent.com
// @connect      objects.githubusercontent.com
// @connect      release-assets.githubusercontent.com
// @connect      cdn.jsdelivr.net
// ==/UserScript==

(function () {
  'use strict';

  const CFG = {
    name: 'Catur Bantu',
    host: 'www.chess.com',
    pathRe: /.*/,
    bridge: 'http://127.0.0.1:8765',
    wasmSources: [
      'https://github.com/nmrugg/stockfish.js/releases/download/v19.0.1/',
      'https://cdn.jsdelivr.net/npm/stockfish@19.0.1/bin/',
    ],
    wasmJs: 'stockfish-19-lite-single.js',
    wasmBin: 'stockfish-19-lite-single.wasm',
    presets: {
      peluru: { movetime: 100, probeTime: 50, multipv: 4, multipvWasm: 4, specCands: 3, specMax: 4, hint: 'Buat 1-2 menit: secepat mungkin, fokus ke langkah terbaik.' },
      kilat: { movetime: 300, probeTime: 120, multipv: 6, multipvWasm: 6, specCands: 4, specMax: 6, hint: 'Buat 3-9 menit: cepat tapi masih lumayan teliti.' },
      cepat: { movetime: 800, probeTime: 250, multipv: 12, multipvWasm: 6, specCands: 5, specMax: 8, hint: 'Buat 10 menit ke atas atau tanpa pemasa: lebih teliti, kandidat lebih banyak.' },
    },
    defaultSpeed: 'kilat',
    tier: { t1: 30, t2: 100, t3: 150 },
    bridgePingMs: 8000,
    bridgeAlivePingMs: 30000,
    clockPollMs: 150,
    clockSettleMs: 350,
    clockTickMs: 1300,
    premoveMissDelayMs: 900,
    speculate: true,
    specWindow: 100,
    specWasmCands: 2,
    oppElo: null,
    arrow: { w: 0.22, head: 0.6, outline: 0.05 },
  };

  try {
    if (typeof GM_getValue === 'function') {
      const t = GM_getValue('cch_test_config');
      if (t && typeof t === 'object') Object.assign(CFG, t);
      if (t && typeof t === 'object' && typeof t.pathRe === 'string') CFG.pathRe = new RegExp(t.pathRe);
    }
  } catch (e) { }

  const DEFAULTS = {
    v: 1,
    elo: 3000,
    style: 'bot',
    speed: 'kilat',
    premove: false,
    tiers: { t1: true, t2: true, t3: true },
    pos: null,
  };

  const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
  const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
  const logBuf = [];
  function dbg(msg) {
    const d = new Date();
    logBuf.push(d.toTimeString().slice(0, 8) + ' ' + msg);
    if (logBuf.length > 80) logBuf.shift();
  }

  const store = {
    get(k, d) {
      try {
        if (typeof GM_getValue === 'function') {
          const v = GM_getValue(k);
          return v === undefined ? d : v;
        }
      } catch (e) { }
      try {
        const v = localStorage.getItem('cch:' + k);
        return v === null ? d : JSON.parse(v);
      } catch (e) { return d; }
    },
    set(k, v) {
      try {
        if (typeof GM_setValue === 'function') { GM_setValue(k, v); return; }
      } catch (e) { }
      try { localStorage.setItem('cch:' + k, JSON.stringify(v)); } catch (e) { }
    },
  };

  function mulberry32(seed) {
    let a = seed >>> 0;
    return function () {
      a = (a + 0x6D2B79F5) >>> 0;
      let t = a;
      t = Math.imul(t ^ (t >>> 15), t | 1);
      t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }
  function hashStr(s) {
    let h = 2166136261 >>> 0;
    for (let i = 0; i < s.length; i++) { h ^= s.charCodeAt(i); h = Math.imul(h, 16777619) >>> 0; }
    return h;
  }

  function gmRequest(o) {
    let handle = null;
    const p = new Promise((resolve, reject) => {
      if (typeof GM_xmlhttpRequest !== 'function') {
        const e = new Error('GM_xmlhttpRequest nggak tersedia'); e.kind = 'net'; reject(e); return;
      }
      const fail = (m) => { const e = new Error(m); e.kind = 'net'; reject(e); };
      try {
        handle = GM_xmlhttpRequest({
          method: o.method || 'GET',
          url: o.url,
          data: o.data,
          headers: o.headers,
          responseType: o.responseType || 'text',
          timeout: o.timeout || 5000,
          onload: (r) => resolve(r),
          onerror: () => fail('koneksi gagal'),
          ontimeout: () => fail('timeout'),
          onabort: () => fail('abort'),
        });
      } catch (e) { fail(String(e && e.message || e)); }
    });
    p.abort = () => { try { if (handle && handle.abort) handle.abort(); } catch (e) { } };
    return p;
  }

  const FILES = 'abcdefgh';
  const sqName = (i) => FILES[i & 7] + ((i >> 3) + 1);
  const sqIdx = (s) => (s.charCodeAt(0) - 97) + (s.charCodeAt(1) - 49) * 8;
  const mirrorSq = (i) => (7 - (i >> 3)) * 8 + (i & 7);
  const isWhitePc = (ch) => ch >= 'A' && ch <= 'Z';
  const VAL = { p: 100, n: 300, b: 300, r: 500, q: 900, k: 0 };
  const ATT_VAL = { p: 100, n: 300, b: 300, r: 500, q: 900, k: 2000 };
  const PROMO_NAME = { n: 'kuda', r: 'benteng', b: 'gajah', q: 'ratu' };
  const START_PLACEMENT = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR';
  const KN = [[1, 2], [2, 1], [2, -1], [1, -2], [-1, -2], [-2, -1], [-2, 1], [-1, 2]];
  const KG = [[1, 0], [1, 1], [0, 1], [-1, 1], [-1, 0], [-1, -1], [0, -1], [1, -1]];
  const ORTH = [[1, 0], [-1, 0], [0, 1], [0, -1]];
  const DIAG = [[1, 1], [1, -1], [-1, 1], [-1, -1]];

  function fenPlacement(bd) {
    const rows = [];
    for (let r = 7; r >= 0; r--) {
      let s = '', e = 0;
      for (let f = 0; f < 8; f++) {
        const ch = bd[r * 8 + f];
        if (!ch) e++;
        else { if (e) { s += e; e = 0; } s += ch; }
      }
      if (e) s += e;
      rows.push(s);
    }
    return rows.join('/');
  }

  function buildFEN(bd, turn, rights, ep) {
    return fenPlacement(bd) + ' ' + turn + ' ' + (rights || '-') + ' ' + (ep || '-') + ' 0 1';
  }

  function findKing(bd, white) {
    const k = white ? 'K' : 'k';
    for (let i = 0; i < 64; i++) if (bd[i] === k) return i;
    return -1;
  }

  function attackersOf(bd, idx, white) {
    const out = [];
    const f = idx & 7, r = idx >> 3;
    const P = white ? 'P' : 'p', N = white ? 'N' : 'n', B = white ? 'B' : 'b';
    const R = white ? 'R' : 'r', Q = white ? 'Q' : 'q', K = white ? 'K' : 'k';
    const pr = white ? r - 1 : r + 1;
    if (pr >= 0 && pr < 8) {
      for (const df of [-1, 1]) {
        const pf = f + df;
        if (pf >= 0 && pf < 8 && bd[pr * 8 + pf] === P) out.push({ i: pr * 8 + pf, t: 'p' });
      }
    }
    for (const [df, dr] of KN) {
      const nf = f + df, nr = r + dr;
      if (nf >= 0 && nf < 8 && nr >= 0 && nr < 8 && bd[nr * 8 + nf] === N) out.push({ i: nr * 8 + nf, t: 'n' });
    }
    for (const [df, dr] of KG) {
      const nf = f + df, nr = r + dr;
      if (nf >= 0 && nf < 8 && nr >= 0 && nr < 8 && bd[nr * 8 + nf] === K) out.push({ i: nr * 8 + nf, t: 'k' });
    }
    for (const [df, dr] of ORTH) {
      let nf = f + df, nr = r + dr;
      while (nf >= 0 && nf < 8 && nr >= 0 && nr < 8) {
        const c = bd[nr * 8 + nf];
        if (c) {
          if (c === R) out.push({ i: nr * 8 + nf, t: 'r' });
          else if (c === Q) out.push({ i: nr * 8 + nf, t: 'q' });
          break;
        }
        nf += df; nr += dr;
      }
    }
    for (const [df, dr] of DIAG) {
      let nf = f + df, nr = r + dr;
      while (nf >= 0 && nf < 8 && nr >= 0 && nr < 8) {
        const c = bd[nr * 8 + nf];
        if (c) {
          if (c === B) out.push({ i: nr * 8 + nf, t: 'b' });
          else if (c === Q) out.push({ i: nr * 8 + nf, t: 'q' });
          break;
        }
        nf += df; nr += dr;
      }
    }
    return out;
  }
  const isAttacked = (bd, idx, byWhite) => attackersOf(bd, idx, byWhite).length > 0;

  function validateBoard(bd, turn) {
    let wk = 0, bk = 0, wp = 0, bp = 0, wt = 0, bt = 0;
    for (let i = 0; i < 64; i++) {
      const c = bd[i];
      if (!c) continue;
      const w = isWhitePc(c);
      if (w) wt++; else bt++;
      if (c === 'K') wk++;
      else if (c === 'k') bk++;
      else if (c === 'P' || c === 'p') {
        if (w) wp++; else bp++;
        const r = i >> 3;
        if (r === 0 || r === 7) return 'ada pion di baris 1/8';
      }
    }
    if (wk !== 1 || bk !== 1) return 'raja nggak lengkap (putih ' + wk + ', hitam ' + bk + ')';
    if (wp > 8 || bp > 8) return 'pion kebanyakan';
    if (wt > 16 || bt > 16) return 'bidak kebanyakan';
    const a = findKing(bd, true), b = findKing(bd, false);
    if (Math.abs((a & 7) - (b & 7)) <= 1 && Math.abs((a >> 3) - (b >> 3)) <= 1) return 'dua raja berdempetan';
    const white = turn === 'w';
    if (isAttacked(bd, findKing(bd, !white), white)) return 'raja lawan lagi di-skak (giliran salah tebak?)';
    return null;
  }

  function guessRights(bd) {
    let s = '';
    if (bd[4] === 'K' && bd[7] === 'R') s += 'K';
    if (bd[4] === 'K' && bd[0] === 'R') s += 'Q';
    if (bd[60] === 'k' && bd[63] === 'r') s += 'k';
    if (bd[60] === 'k' && bd[56] === 'r') s += 'q';
    return s;
  }
  const intersectRights = (a, b) => 'KQkq'.split('').filter((c) => a.indexOf(c) >= 0 && b.indexOf(c) >= 0).join('');

  function applyMove(bd, uci) {
    const from = sqIdx(uci.slice(0, 2)), to = sqIdx(uci.slice(2, 4)), promo = uci[4] || '';
    const pc = bd[from];
    if (!pc) return null;
    const nb = bd.slice();
    const white = isWhitePc(pc), t = pc.toLowerCase();
    let captured = nb[to] || '';
    let castle = 0, ep = false;
    nb[to] = pc; nb[from] = '';
    if (t === 'k' && Math.abs((to & 7) - (from & 7)) === 2) {
      castle = (to & 7) > (from & 7) ? 1 : -1;
      const rf = castle > 0 ? from + 3 : from - 4;
      const rt = castle > 0 ? from + 1 : from - 1;
      nb[rt] = nb[rf]; nb[rf] = '';
    }
    if (t === 'p' && (to & 7) !== (from & 7) && !captured) {
      ep = true;
      const ci = white ? to - 8 : to + 8;
      captured = nb[ci] || ''; nb[ci] = '';
    }
    if (promo) nb[to] = white ? promo.toUpperCase() : promo;
    else if (t === 'p' && ((to >> 3) === 7 || (to >> 3) === 0)) nb[to] = white ? 'Q' : 'q';
    return { bd: nb, from, to, piece: pc, captured, castle, ep, promo };
  }

  function givesCheck(res, moverWhite) {
    const k = findKing(res.bd, !moverWhite);
    return k >= 0 && isAttacked(res.bd, k, moverWhite);
  }

  function attackedPieces(bd, white) {
    const out = [];
    for (let i = 0; i < 64; i++) {
      const c = bd[i];
      if (!c || isWhitePc(c) !== white) continue;
      const t = c.toLowerCase();
      if (t === 'p' || t === 'k') continue;
      const atk = attackersOf(bd, i, !white);
      if (!atk.length) continue;
      let min = 1e9;
      for (const a of atk) min = Math.min(min, ATT_VAL[a.t]);
      out.push({ i, t, minAtt: min, byPawn: atk.some((a) => a.t === 'p'), defended: attackersOf(bd, i, white).length > 0 });
    }
    return out;
  }

  const undevMinors = (bd, white) => {
    const sqs = white ? [1, 2, 5, 6] : [57, 58, 61, 62];
    const pcs = white ? ['N', 'B', 'B', 'N'] : ['n', 'b', 'b', 'n'];
    let n = 0;
    for (let k = 0; k < 4; k++) if (bd[sqs[k]] === pcs[k]) n++;
    return n;
  };
  const pieceCount = (bd) => { let n = 0; for (let i = 0; i < 64; i++) if (bd[i]) n++; return n; };

  function describeMove(bd, uci) {
    if (!uci) return '';
    const from = uci.slice(0, 2), to = uci.slice(2, 4);
    const pc = bd[sqIdx(from)];
    if (!pc) return uci;
    const t = pc.toLowerCase();
    if (t === 'k' && Math.abs(sqIdx(to) - sqIdx(from)) === 2) return sqIdx(to) > sqIdx(from) ? 'O-O' : 'O-O-O';
    const cap = bd[sqIdx(to)] || (t === 'p' && from[0] !== to[0]);
    const letter = t === 'p' ? '' : t.toUpperCase();
    return letter + from + (cap ? 'x' : '→') + to + (uci[4] ? '=' + uci[4].toUpperCase() : '');
  }

  function arrowLane(uci) {
    const i1 = sqIdx(uci.slice(0, 2)), i2 = sqIdx(uci.slice(2, 4));
    const df = (i2 & 7) - (i1 & 7), dr = (i2 >> 3) - (i1 >> 3);
    const adf = Math.abs(df), adr = Math.abs(dr);
    const knight = (adf === 1 && adr === 2) || (adf === 2 && adr === 1);
    const dx = knight ? (adf === 2 ? Math.sign(df) : 0) : Math.sign(df);
    const dy = knight ? (adf === 2 ? 0 : Math.sign(dr)) : Math.sign(dr);
    return uci.slice(0, 2) + ':' + dx + ',' + dy;
  }

  function diffInfo(prev, bd) {
    const arrivals = [], departures = [];
    let colors = 0;
    for (let i = 0; i < 64; i++) {
      if (bd[i] && bd[i] !== prev[i]) { arrivals.push(i); colors |= isWhitePc(bd[i]) ? 1 : 2; }
      if (prev[i] && !bd[i]) departures.push(i);
    }
    return { arrivals, departures, mover: colors === 1 ? 'w' : colors === 2 ? 'b' : null };
  }
  function highlightMover(bd, hl, prev) {
    const occ = hl.filter((i) => bd[i]);
    if (occ.length !== 1) return null;
    if (prev && prev[occ[0]] === bd[occ[0]]) return null;
    return isWhitePc(bd[occ[0]]) ? 'w' : 'b';
  }

  function parseClockText(t) {
    const s = String(t == null ? '' : t).replace(/\s+/g, '').replace(',', '.');
    if (!/^\d+(?::\d{1,2}){0,2}(?:\.\d+)?$/.test(s) || !/[:.]/.test(s)) return null;
    let sec = 0;
    for (const p of s.split(':')) sec = sec * 60 + parseFloat(p);
    return sec;
  }

  function clockTurn(clocks, bottomColor, mem, now, tickMs) {
    const other = (c) => (c === 'w' ? 'b' : 'w');
    const by = {};
    for (const c of clocks) {
      const color = c.color || (c.pos === 'bottom' ? bottomColor : c.pos === 'top' ? other(bottomColor) : null);
      if (color && !by[color]) by[color] = c;
    }
    if (!by.w || !by.b) {
      return { turn: null, src: '', weak: false, note: clocks.length ? 'jam ketemu ' + clocks.length + ', warnanya nggak jelas' : 'nggak ada jam' };
    }
    for (const col of ['w', 'b']) {
      const sec = parseClockText(by[col].text);
      const m = mem[col] || (mem[col] = { sec: null, dec: 0 });
      if (sec != null) { if (m.sec != null && sec < m.sec) m.dec = now; m.sec = sec; }
    }
    const note = ['w', 'b'].map((col) => col + ':' + (by[col].pos || '?') + ':' + (by[col].turnClass ? 'ON' : 'off')).join(' | ');
    const on = ['w', 'b'].filter((col) => by[col].turnClass);
    if (on.length === 1) return { turn: on[0], src: 'jam (kelas)', weak: false, note };
    const run = ['w', 'b'].filter((col) => mem[col].dec && now - mem[col].dec <= tickMs);
    if (run.length === 1) return { turn: run[0], src: 'jam (berdetak)', weak: true, note };
    return { turn: null, src: '', weak: false, note };
  }

  function arbitrateTurn(ck, boardTurn, boardSrc, st, now, settleMs) {
    if (!ck || !ck.turn) { st.since = 0; return { turn: boardTurn || null, src: boardTurn ? boardSrc : '', pending: false }; }
    if (!boardTurn || boardTurn === ck.turn) { st.since = 0; return { turn: ck.turn, src: ck.src, pending: false }; }
    if (ck.weak) { st.since = 0; return { turn: boardTurn, src: boardSrc + ' (jam berdetak beda, diabaikan)', pending: false }; }
    if (!st.since) st.since = now;
    if (now - st.since < settleMs) return { turn: null, src: 'jam beda dari papan, nunggu sinkron', pending: true };
    return { turn: ck.turn, src: ck.src + ' (beda dari papan)', pending: false };
  }

  const scoreOf = (l) => (l.mate != null ? (l.mate > 0 ? 100000 - l.mate : -100000 - l.mate) : l.cp);

  function fmtEval(score, mate) {
    if (mate != null) return (mate > 0 ? 'M' : '-M') + Math.abs(mate);
    const v = score / 100;
    return (v > 0 ? '+' : '') + v.toFixed(2);
  }

  function eloPlan(elo, uciMin, uciMax, probeTime) {
    if (elo >= 3000) return { mode: 'full', probe: null, errChance: 0, maxRank: 0 };
    if (elo >= uciMin) {
      return {
        mode: 'uci',
        probe: { movetime: probeTime, multipv: 6, options: { UCI_LimitStrength: true, UCI_Elo: clamp(elo, uciMin, uciMax) } },
        errChance: 0, maxRank: 0,
      };
    }
    const t = clamp((elo - 100) / Math.max(1, uciMin - 100), 0, 1);
    return {
      mode: 'low',
      probe: { movetime: probeTime, multipv: 6, options: { UCI_LimitStrength: false, 'Skill Level': Math.round(t * 3) } },
      errChance: 0.05 + 0.8 * Math.pow(1 - t, 1.2),
      maxRank: 2 + Math.round((1 - t) * 4),
    };
  }

  function sampleWeighted(items, scoreFn, temp, rnd) {
    const sc = items.map(scoreFn);
    const m = Math.max.apply(null, sc);
    const w = sc.map((s) => Math.exp((s - m) / temp));
    const sum = w.reduce((a, b) => a + b, 0);
    let x = rnd() * sum;
    for (let i = 0; i < w.length; i++) { x -= w[i]; if (x <= 0) return items[i]; }
    return items[items.length - 1];
  }

  function moveInfo(ctx, c) {
    if (c._mi !== undefined) return c._mi;
    const r = applyMove(ctx.bd, c.move);
    if (!r) { c._mi = null; return null; }
    const t = r.piece.toLowerCase();
    const rank = (i) => (ctx.white ? i >> 3 : 7 - (i >> 3));
    c._mi = {
      r, t, from: r.from, to: r.to,
      fromFile: r.from & 7, toFile: r.to & 7,
      fromRank: rank(r.from), toRank: rank(r.to),
      capture: !!r.captured,
      capVal: r.captured ? VAL[r.captured.toLowerCase()] : 0,
      movedVal: VAL[t],
      castle: r.castle,
      check: givesCheck(r, ctx.white),
    };
    return c._mi;
  }

  function humanEval(c, ctx) {
    const m = moveInfo(ctx, c);
    const tags = [];
    let b = 0;
    if (!m) return { b, tags };
    const edgeFile = m.toFile === 0 || m.toFile === 7;
    if (m.castle) { b += 35; tags.push('rokade'); }
    if ((m.t === 'n' || m.t === 'b') && m.fromRank === 0 && ctx.opening) { b += 30; tags.push('develop bidak'); }
    if (m.t === 'p' && (m.fromFile === 3 || m.fromFile === 4) && ctx.opening) { b += 25; tags.push('pion tengah'); }
    if (m.t === 'p' && (m.fromFile === 2 || m.fromFile === 5) && ctx.opening) b += 8;
    if (m.capture && m.capVal >= m.movedVal - 50) { b += 22; tags.push(m.capVal > m.movedVal ? 'ambil materi' : 'tukar'); }
    const ol = ctx.oppLast;
    if (ol && m.capture && m.to === ol.to) { b += 28; tags.push('makan balik'); }
    if ((m.t === 'n' || m.t === 'b') && Math.abs(m.toFile - 3.5) <= 1.5 && Math.abs(m.toRank - 3.5) <= 1.5) b += 10;
    if (m.check) { b += 8; tags.push('skak'); }
    if (m.t === 'k' && !m.castle && ctx.opening) b -= 35;
    if (m.t === 'q' && ctx.opening && m.fromRank === 0) b -= 30;
    if (m.t === 'p' && edgeFile && ctx.opening) b -= 15;
    if (m.t === 'n' && edgeFile) b -= 20;
    if ((m.t === 'n' || m.t === 'b' || m.t === 'r' || m.t === 'q') && m.toRank === 0 && m.fromRank !== 0) b -= 12;
    if (ctx.lastMine && ctx.lastMine.to === m.from && ctx.opening) b -= 12;
    if (m.r.promo && m.r.promo !== 'q') b -= 40;
    return { b, tags };
  }

  function trollEval(c, ctx, best) {
    const m = moveInfo(ctx, c);
    const tags = [];
    let b = 0;
    if (!m) return { b, tags };
    const winning = best >= 300;
    const mateAvail = best >= 90000;
    const isMate = c.mate != null && c.mate > 0;

    if (m.t === 'q' && ctx.opening) { b += 40 + (m.toRank >= 3 ? 10 : 0); tags.push('Q keluar awal'); }
    if (m.t === 'p' && (m.toFile === 0 || m.toFile === 7) && (m.fromFile === 0 || m.fromFile === 7)) {
      b += 30 + (Math.abs(m.toRank - m.fromRank) === 2 ? 8 : 0); tags.push('pion pinggir');
    }
    const lm = ctx.lastMine;
    if (m.t === 'n' && lm && lm.piece === 'n' && lm.to === m.from && lm.from === m.to) { b += 45; tags.push('knight bolak-balik'); }
    if (m.t === 'k' && !m.castle && ctx.opening && !m.capture) { b += 30; tags.push('Bongcloud'); }
    const canCastle = ctx.white ? /[KQ]/.test(ctx.rights) : /[kq]/.test(ctx.rights);
    if (canCastle && ctx.opening) {
      if (m.castle) b -= 10;
      else { b += 12; tags.push('rokade ditunda'); }
    }

    const ol = ctx.oppLast;
    if (ol && m.from === mirrorSq(ol.from) && m.to === mirrorSq(ol.to)) { b += 40; tags.push('niru langkah lawan'); }

    const before = new Set(ctx.attackedBefore);
    let bait = 0;
    for (const a of attackedPieces(m.r.bd, ctx.white)) {
      const isNew = a.i === m.to || !before.has(a.i);
      if (!isNew) continue;
      if (a.minAtt < VAL[a.t] || !a.defended) bait = Math.max(bait, 30 + (a.byPawn ? 10 : 0));
      else bait = Math.max(bait, 12);
    }
    if (bait) { b += bait; tags.push('tahan bidak yang bisa dimakan'); }

    if (winning) {
      if (isMate) b -= 90;
      else if (mateAvail) { b += 35; tags.push('sengaja nggak skakmat'); }
      if (m.r.promo && m.r.promo !== 'q') { b += 55; tags.push('promosi jadi ' + PROMO_NAME[m.r.promo]); }
      if (m.capture && m.capVal <= 100 && !isMate) { b += 18; tags.push('sikat pion dulu'); }
      if ((m.t === 'k' || m.t === 'r') && !m.capture && !m.check) { b += 12; tags.push('muter-muter'); }
      if (m.toRank < m.fromRank && !m.capture) { b += 8; tags.push('mundur dulu'); }
      if (m.check && !isMate) { b += 10; tags.push('skak iseng'); }
    }
    return { b, tags };
  }

  function decide(res, ctx) {
    const lines = res.lines || [];
    if (!lines.length) return null;
    const T = CFG.tier;
    const sc = lines.map(scoreOf);
    const best = Math.max.apply(null, sc);
    const cs = lines.map((l, i) => ({
      move: l.move, rank: l.rank, score: sc[i], loss: best - sc[i], mate: l.mate, cp: l.cp, depth: l.depth, pv: l.pv,
    }));
    const bestC = cs.find((c) => c.move === res.bestmove) || cs.reduce((a, b) => (b.score > a.score ? b : a), cs[0]);
    const safe = (c) => {
      if (c.loss > T.t3) return false;
      if (c.score <= -90000 && best > -90000) return false;
      if (best >= 200 && c.score < 100) return false;
      return true;
    };
    const tierOf = (c) => (!safe(c) ? 0 : c.loss <= T.t1 ? 1 : c.loss <= T.t2 ? 2 : 3);

    const rnd = mulberry32(hashStr(ctx.seed));
    const plan = ctx.plan;
    let base = cs.find((c) => c.move === res.probe_bestmove) || bestC;
    if (plan.errChance > 0 && rnd() < plan.errChance) {
      const pool = cs.slice(1, Math.min(cs.length, 1 + plan.maxRank));
      if (pool.length) base = pool[Math.floor(rnd() * pool.length)];
    }

    let pick = base, tags = [], styleUsed = ctx.style, note = '', trollWin = false;
    const humanPick = () => {
      const budget = Math.max(base.loss, T.t2);
      const cands = cs.filter((c) => (c.loss <= budget && safe(c)) || c === base);
      const ev = new Map();
      cands.forEach((c) => ev.set(c, humanEval(c, ctx)));
      const wt = (c) => ev.get(c).b - 0.6 * c.loss + (c === base ? 10 : 0);
      const slipPool = cands.filter((c) => c.loss >= 15 && c.loss <= T.t2);
      const slip = slipPool.length > 0 && rnd() < (ctx.humanSlip == null ? 0.35 : ctx.humanSlip);
      const pool = slip ? slipPool : cands;
      const p = sampleWeighted(pool, wt, 18, rnd);
      const t = ev.get(p).tags.slice();
      if (p.loss >= 15) t.push('agak meleset');
      return { p, tags: t };
    };

    if (ctx.style === 'human') {
      const h = humanPick();
      pick = h.p; tags = h.tags;
    } else if (ctx.style === 'troll') {
      const winning = best >= 300;
      const floor = Math.max(250, Math.min(best - 400, 600));
      const cands = winning
        ? cs.filter((c) => c.score >= floor)
        : cs.filter((c) => c.loss <= Math.max(base.loss, 120) && safe(c));
      const ev = new Map();
      cands.forEach((c) => ev.set(c, trollEval(c, ctx, best)));
      const good = winning ? cands : cands.filter((c) => ev.get(c).b >= 20);
      if (good.length) {
        pick = sampleWeighted(good, (c) => ev.get(c).b - (winning ? 0 : 0.35 * c.loss), 15, rnd);
        tags = ev.get(pick).tags;
        trollWin = winning;
      } else {
        const h = humanPick();
        pick = h.p; tags = h.tags; styleUsed = 'human';
        note = 'nggak ada langkah troll yang aman, turun ke gaya manusia';
      }
    }

    const styleGreen = ctx.style !== 'bot' && pick !== bestC && (trollWin || safe(pick));
    const tiers = { 1: styleGreen ? pick : bestC, 2: null, 3: null };
    const pickTier = pick === bestC || styleGreen ? 1 : tierOf(pick);
    if (!styleGreen && pick !== bestC) {
      if (pickTier === 1 || pickTier === 2) tiers[2] = pick;
      else if (pickTier === 3) tiers[3] = pick;
    }
    const risk = (c) => (c.score <= -90000 && best > -90000 ? 2 : 0) + (best >= 200 && c.score < 100 ? 1 : 0);
    const taken = () => new Set([bestC, pick, tiers[1], tiers[2], tiers[3]].filter(Boolean));
    const laneSet = () => new Set([tiers[1], tiers[2], tiers[3]].filter(Boolean).map((c) => arrowLane(c.move)));
    const choose = (want) => {
      const used = taken(), ln = laneSet();
      const rest = cs.filter((c) => !used.has(c));
      const pools = [
        rest.filter((c) => safe(c) && !ln.has(arrowLane(c.move))),
        rest.filter(safe),
        rest.slice().sort((x, y) => risk(x) - risk(y) || x.loss - y.loss),
      ];
      for (let k = 0; k < 3; k++) {
        const pool = pools[k];
        if (!pool.length) continue;
        if (k === 2) return pool[0];
        if (want === 'weakest') return pool.reduce((x, y) => (y.loss > x.loss ? y : x));
        return pool.reduce((x, y) => {
          const dx = Math.abs(x.loss - want), dy = Math.abs(y.loss - want);
          return dy < dx || (dy === dx && y.loss < x.loss) ? y : x;
        });
      }
      return null;
    };
    if (!tiers[3]) tiers[3] = choose('weakest');
    if (!tiers[2]) tiers[2] = choose(tiers[3] ? tiers[3].loss / 2 : T.t1);
    if (tiers[2] && tiers[3] && tiers[2] !== pick && tiers[3] !== pick && tiers[2].loss > tiers[3].loss) { const t = tiers[2]; tiers[2] = tiers[3]; tiers[3] = t; }
    for (const t of [2, 3]) if (!tiers[t] && ![tiers[1], tiers[2], tiers[3]].includes(bestC)) tiers[t] = bestC;
    return { cs, best, bestC, pick, base, tiers, tags, styleUsed, note, pickTier, trollWin, evalScore: bestC.score, evalMate: bestC.mate };
  }

  function parseInfo(line) {
    if (line.indexOf('info ') !== 0 || line.indexOf(' score ') < 0 || line.indexOf(' pv ') < 0) return null;
    const ms = /\bscore (cp|mate) (-?\d+)( lowerbound| upperbound)?/.exec(line);
    if (!ms || ms[3]) return null;
    const md = /\bdepth (\d+)/.exec(line);
    const mp = /\bpv ((?:[a-h][1-8][a-h][1-8][qrbn]?\s*)+)/.exec(line);
    if (!md || !mp) return null;
    const mm = /\bmultipv (\d+)/.exec(line);
    const pv = mp[1].trim().split(/\s+/);
    return {
      rank: mm ? +mm[1] : 1, depth: +md[1], move: pv[0], pv: pv.slice(0, 6),
      cp: ms[1] === 'cp' ? +ms[2] : null, mate: ms[1] === 'mate' ? +ms[2] : null,
    };
  }

  class LineCollector {
    constructor() { this.blocks = []; this.cur = {}; this.n = 0; }
    add(e) {
      if (e.rank === 1 && this.n) { this.blocks.push(this.cur); this.cur = {}; this.n = 0; }
      this.cur[e.rank] = e; this.n++;
    }
    result() {
      const blocks = this.blocks.concat(this.n ? [this.cur] : []);
      if (!blocks.length) return { lines: [], depth: 0 };
      const rows = (b) => Object.keys(b).map(Number).sort((a, c) => a - c).map((k) => b[k]);
      const n = Math.max.apply(null, blocks.map((b) => Object.keys(b).length));
      const ok = (b) => {
        const r = rows(b);
        return r.length === n && r.every((x, i) => x.rank === i + 1) && new Set(r.map((x) => x.move)).size === n;
      };
      for (let i = blocks.length - 1; i >= 0; i--) {
        if (ok(blocks[i])) { const r = rows(blocks[i]); return { lines: r, depth: Math.max.apply(null, r.map((x) => x.depth)) }; }
      }
      for (let i = blocks.length - 1; i >= 0; i--) {
        if (Object.keys(blocks[i]).length === n) {
          const seen = new Set(); const r = [];
          rows(blocks[i]).forEach((x) => { if (!seen.has(x.move)) { seen.add(x.move); r.push(x); } });
          return { lines: r, depth: Math.max.apply(null, r.map((x) => x.depth)) };
        }
      }
      return { lines: [], depth: 0 };
    }
  }

  class BridgeEngine {
    constructor(base) { this.base = base; this.cur = null; this.info = null; }
    async ping() {
      const r = await gmRequest({ method: 'GET', url: this.base + '/ping', timeout: 2500 });
      let j;
      try { j = JSON.parse(r.responseText); } catch (e) { const er = new Error('balasan jembatan aneh'); er.kind = 'net'; throw er; }
      if (!j.ok) { const er = new Error(j.error || 'engine di jembatan bermasalah'); er.kind = 'engine'; throw er; }
      this.info = j.engine;
      return j;
    }
    abort() { if (this.cur) this.cur.abort(); }
    async analyze(req) {
      this.abort();
      const p = gmRequest({
        method: 'POST', url: this.base + '/analyze', data: JSON.stringify(req),
        headers: { 'Content-Type': 'application/json' }, timeout: 6000,
      });
      this.cur = p;
      const r = await p;
      let j;
      try { j = JSON.parse(r.responseText); } catch (e) { const er = new Error('balasan jembatan aneh'); er.kind = 'net'; throw er; }
      if (!j.ok) { const er = new Error(j.error || 'analisis gagal'); er.kind = 'engine'; throw er; }
      return j;
    }
  }

  class WasmEngine {
    constructor(cfg) {
      this.cfg = cfg;
      this.worker = null;
      this.state = 'idle';
      this.failure = null;
      this.booting = null;
      this.sink = null;
      this.applied = {};
      this.range = { min: 1320, max: 3190 };
      this.gen = 0;
      this.searching = false;
      this.chain = Promise.resolve();
      this.sourceUsed = '';
    }

    async _fetchAsset(name, type) {
      const errs = [];
      for (const base of this.cfg.wasmSources) {
        const url = base + name;
        try {
          if (typeof caches !== 'undefined') {
            const c = await caches.open('catur-bantu-v1');
            const hit = await c.match(url);
            if (hit) return { data: type === 'text' ? await hit.text() : await hit.arrayBuffer(), url };
          }
        } catch (e) { }
        try {
          const r = await gmRequest({ url, responseType: type === 'text' ? 'text' : 'arraybuffer', timeout: 60000 });
          if (r.status !== 200) throw new Error('HTTP ' + r.status);
          const data = type === 'text' ? r.responseText : r.response;
          if (!data || (type !== 'text' && !data.byteLength)) throw new Error('kosong');
          try {
            if (typeof caches !== 'undefined') {
              const c = await caches.open('catur-bantu-v1');
              await c.put(url, new Response(data));
            }
          } catch (e) { }
          return { data, url };
        } catch (e) { errs.push(url + ' -> ' + e.message); }
      }
      throw new Error(errs.join(' | '));
    }

    ensure(onState) {
      if (this.state === 'ready' && this.worker) return Promise.resolve();
      if (this.booting) return this.booting;
      this.booting = this._boot(onState).finally(() => { this.booting = null; });
      return this.booting;
    }

    _fail(kind, msg) {
      this.state = 'failed'; this.failure = kind;
      try { if (this.worker) this.worker.terminate(); } catch (e) { }
      this.worker = null; this.applied = {}; this.searching = false;
      const s = this.sink; this.sink = null;
      const er = new Error(msg); er.kind = 'wasm'; er.wasmFailure = kind;
      if (s && s.reject) s.reject(er);
      return er;
    }

    async _boot(onState) {
      this.state = 'loading'; this.failure = null;
      if (onState) onState('loading');
      let js, bin;
      try {
        const a = await this._fetchAsset(this.cfg.wasmJs, 'text');
        const b = await this._fetchAsset(this.cfg.wasmBin, 'arraybuffer');
        js = a.data; bin = b.data; this.sourceUsed = a.url;
      } catch (e) { throw this._fail('download', 'gagal unduh WASM: ' + e.message); }
      let w;
      try {
        const jsUrl = URL.createObjectURL(new Blob([js], { type: 'text/javascript' }));
        const binUrl = URL.createObjectURL(new Blob([bin], { type: 'application/wasm' }));
        w = new Worker(jsUrl + '#' + encodeURIComponent(binUrl));
      } catch (e) { throw this._fail('blocked', 'worker diblokir: ' + (e && e.message || e)); }
      this.worker = w;
      w.onmessage = (ev) => {
        if (typeof ev.data !== 'string') return;
        const s = this.sink;
        if (s) s.line(ev.data);
      };
      w.onerror = (ev) => {
        const kind = this.state === 'ready' ? 'crash' : 'blocked';
        this._fail(kind, kind === 'blocked' ? 'worker diblokir / gagal jalan' : 'worker mati mendadak');
        if (ev && ev.preventDefault) ev.preventDefault();
      };
      try {
        await this._expect((l) => l === 'uciok', 20000, (l) => {
          const m = /^option name UCI_Elo type spin default \S+ min (\d+) max (\d+)/.exec(l);
          if (m) this.range = { min: +m[1], max: +m[2] };
        }, 'uci');
        await this._expect((l) => l === 'readyok', 20000, null, 'isready');
      } catch (e) {
        if (this.state === 'failed') throw e;
        throw this._fail(this.failure || 'blocked', 'worker nggak merespons: ' + e.message);
      }
      this.state = 'ready';
      if (onState) onState('ready');
    }

    _send(s) { if (this.worker) this.worker.postMessage(s); }

    _expect(pred, timeout, onLine, cmd) {
      return new Promise((resolve, reject) => {
        const t = setTimeout(() => { if (this.sink === sink) this.sink = null; reject(new Error('timeout')); }, timeout);
        const sink = {
          reject: (er) => { clearTimeout(t); reject(er); },
          line: (l) => {
            if (l.indexOf('info string CRITICAL ERROR') === 0) {
              clearTimeout(t); this.sink = null;
              const er = new Error(l); er.kind = 'engine'; reject(er); return;
            }
            if (onLine) onLine(l);
            if (pred(l)) { clearTimeout(t); this.sink = null; resolve(l); }
          },
        };
        this.sink = sink;
        if (cmd) this._send(cmd);
      });
    }

    async _setOptions(opts) {
      let changed = false;
      for (const k of Object.keys(opts)) {
        if (this.applied[k] === opts[k]) continue;
        const v = typeof opts[k] === 'boolean' ? (opts[k] ? 'true' : 'false') : String(opts[k]);
        this._send('setoption name ' + k + ' value ' + v);
        this.applied[k] = opts[k]; changed = true;
      }
      if (changed) await this._expect((l) => l === 'readyok', 10000, null, 'isready');
    }

    async _search(fen, movetime, collect) {
      this._send('position fen ' + fen);
      const coll = new LineCollector();
      let bestLine = '';
      this.searching = true;
      try {
        bestLine = await this._expect((l) => l.indexOf('bestmove') === 0, movetime + 6000, (l) => {
          if (!collect) return;
          const e = parseInfo(l); if (e) coll.add(e);
        }, 'go movetime ' + movetime);
      } catch (e) {
        if (e.message === 'timeout') { this._send('stop'); throw this._fail('crash', 'engine WASM nggak ngasih bestmove'); }
        throw e;
      } finally { this.searching = false; }
      const parts = bestLine.split(/\s+/);
      return { best: parts[1] && parts[1] !== '(none)' ? parts[1] : null, coll };
    }

    analyze(req, onState) {
      const myGen = ++this.gen;
      if (this.searching) this._send('stop');
      const run = async () => {
        await this.ensure(onState);
        if (myGen !== this.gen) return { ok: true, cancelled: true, lines: [], bestmove: null, probe_bestmove: null };
        const t0 = performance.now();
        const base = { UCI_LimitStrength: false, 'Skill Level': 20 };
        await this._setOptions(Object.assign({}, base, req.options || {}, { MultiPV: req.multipv }));
        const a = await this._search(req.fen, req.movetime, true);
        const { lines, depth } = a.coll.result();
        const out = { ok: true, bestmove: a.best, lines, depth, probe_bestmove: null, cancelled: false };
        if (req.probe && a.best && myGen === this.gen) {
          const p = req.probe;
          await this._setOptions(Object.assign({}, p.options || {}, { MultiPV: p.multipv || 6 }));
          const b = await this._search(req.fen, p.movetime || 120, false);
          out.probe_bestmove = b.best;
        }
        out.cancelled = myGen !== this.gen;
        out.ms = Math.round(performance.now() - t0);
        return out;
      };
      const p = this.chain.then(run, run);
      this.chain = p.catch(() => { });
      return p;
    }

    terminate() {
      this.gen++;
      try { if (this.worker) this.worker.terminate(); } catch (e) { }
      this.worker = null; this.state = 'idle'; this.applied = {}; this.sink = null; this.searching = false;
    }
  }

  const NS_SVG = 'http://www.w3.org/2000/svg';
  const TIER_COLOR = { 0: '#7d7a72', 1: '#3f9d66', 2: '#e0a526', 3: '#d4543f' };

  const CSS = `
:host{all:initial}
*,*::before,*::after{box-sizing:border-box}
.root{--bg:#faf9f5;--surface:#f0eee6;--text:#141413;--muted:#6b6a64;--accent:#c6613f;--border:#e3dfd3;
  --ok:#3f8f5f;--warn:#c98a12;--err:#c2412f;--shadow:0 10px 30px rgba(20,20,19,.22);
  font:14px/1.45 system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;color:var(--text);
  -webkit-text-size-adjust:100%}
@media (prefers-color-scheme:dark){.root{--bg:#262624;--surface:#30302e;--text:#f5f4ee;--muted:#a9a79c;--accent:#d97757;
  --border:#42413c;--shadow:0 10px 30px rgba(0,0,0,.55)}}
.arrows{position:fixed;pointer-events:none;z-index:2147483640;overflow:visible}
.fab{position:fixed;width:48px;height:48px;border-radius:50%;background:var(--accent);color:#fff;border:2px solid rgba(255,255,255,.55);
  display:grid;place-items:center;font-size:24px;line-height:1;box-shadow:var(--shadow);cursor:grab;
  touch-action:none;user-select:none;-webkit-user-select:none;z-index:2147483647;pointer-events:auto}
.fab:active{cursor:grabbing}
.panel{position:fixed;width:min(330px,calc(100vw - 12px));max-height:calc(100vh - 12px);max-height:calc(100dvh - 12px);overflow:auto;
  background:var(--bg);border:1px solid var(--border);border-radius:20px;box-shadow:var(--shadow);z-index:2147483647;pointer-events:auto;
  overscroll-behavior:contain}
.hd{display:flex;align-items:center;gap:8px;padding:12px 12px 6px 16px;cursor:grab;touch-action:none;user-select:none;-webkit-user-select:none}
.title{flex:1;font:600 20px/1.2 ui-serif,Georgia,"Times New Roman",serif;letter-spacing:-.01em}
.ibtn{width:34px;height:34px;border-radius:11px;border:0;background:var(--surface);color:var(--text);font:600 20px/1 system-ui,sans-serif;
  display:grid;place-items:center;cursor:pointer;padding:0}
.ibtn:active{background:var(--border)}
.body{padding:2px 16px 14px;display:flex;flex-direction:column;gap:11px}
.card{background:var(--surface);border-radius:16px;padding:10px 14px;min-height:72px}
.lbl{font-size:12px;color:var(--muted);letter-spacing:.02em}
.move{font:600 26px/1.2 ui-serif,Georgia,serif;margin-top:2px;word-break:break-word}
.sub{font-size:13px;color:var(--muted);margin-top:2px;white-space:pre-line}
.row{display:flex;justify-content:space-between;align-items:baseline;gap:8px}
.val{font-weight:600}
input[type=range]{width:100%;height:30px;accent-color:var(--accent);margin:0}
.note{font-size:12px;color:var(--muted)}
.seg{display:grid;grid-template-columns:repeat(3,1fr);gap:4px;background:var(--surface);padding:4px;border-radius:14px}
.seg button{border:0;background:transparent;color:var(--text);padding:8px 4px;border-radius:10px;font:600 14px system-ui,sans-serif;cursor:pointer}
.seg button.on{background:var(--accent);color:#fff}
.chips{display:grid;grid-template-columns:repeat(3,1fr);gap:6px}
.chip{display:flex;flex-direction:column;align-items:flex-start;gap:6px;padding:9px 10px;background:var(--surface);border-radius:12px;
  cursor:pointer;font-size:12.5px;line-height:1.25;min-height:62px;position:relative}
.chip input{position:absolute;top:8px;right:8px;width:19px;height:19px;accent-color:var(--accent);margin:0}
.dot{width:13px;height:13px;border-radius:50%;flex:none}
.status{display:flex;gap:8px;align-items:flex-start;font-size:13px}
.led{width:9px;height:9px;border-radius:50%;margin-top:5px;flex:none;background:var(--muted)}
.led.ok{background:var(--ok)}.led.warn{background:var(--warn)}.led.err{background:var(--err)}
details{background:var(--surface);border-radius:12px;padding:8px 12px}
summary{cursor:pointer;font-size:13px;color:var(--muted)}
pre{margin:8px 0 0;font:11.5px/1.45 ui-monospace,Menlo,Consolas,monospace;white-space:pre-wrap;word-break:break-all;max-height:200px;overflow:auto}
.tbtn{width:100%;display:flex;justify-content:space-between;align-items:center;border:0;background:var(--surface);color:var(--text);
  padding:10px 12px;border-radius:12px;font:600 14px system-ui,sans-serif;cursor:pointer}
.tbtn .sw{width:38px;height:22px;border-radius:11px;background:var(--border);position:relative;flex:none;transition:background .15s}
.tbtn .sw::after{content:'';position:absolute;top:3px;left:3px;width:16px;height:16px;border-radius:50%;background:#fff;transition:transform .15s}
.tbtn.on .sw{background:var(--accent)}
.tbtn.on .sw::after{transform:translateX(16px)}
.mini{display:flex;gap:6px;margin-top:8px}
.mini button{flex:1;border:0;border-radius:9px;background:var(--bg);color:var(--text);padding:8px;font:600 12px system-ui,sans-serif;cursor:pointer}
`;

  function createUI(S, handlers) {
    const host = document.createElement('div');
    host.setAttribute('data-catur-bantu', '1');
    host.style.cssText = 'position:fixed;top:0;left:0;width:0;height:0;z-index:2147483647;';
    const root = host.attachShadow({ mode: 'open' });
    root.innerHTML = '<style>' + CSS + '</style>' +
      '<div class="root">' +
      '<svg class="arrows" xmlns="' + NS_SVG + '"></svg>' +
      '<div class="fab" part="fab" title="' + CFG.name + '">♞︎</div>' +
      '<div class="panel" style="display:none">' +
        '<div class="hd"><div class="title">' + CFG.name + '</div>' +
          '<button class="ibtn" data-act="min" title="Kecilkan">−</button>' +
          '<button class="ibtn" data-act="close" title="Tutup sampai reload">×</button></div>' +
        '<div class="body">' +
          '<div class="card"><div class="lbl">Saran</div><div class="move" data-r="move">—</div><div class="sub" data-r="sub">Nunggu papan…</div></div>' +
          '<div><div class="row"><span class="lbl">Elo mesin</span><span class="val" data-r="elo">3000+</span></div>' +
            '<input type="range" min="100" max="3000" step="50" data-r="slider">' +
            '<div class="note" data-r="elonote"></div></div>' +
          '<div><div class="lbl" style="margin-bottom:6px">Kecepatan game</div>' +
            '<div class="seg"><button data-speed="peluru">Peluru</button><button data-speed="kilat">Kilat</button><button data-speed="cepat">Cepat</button></div>' +
            '<div class="note" data-r="speednote" style="margin-top:6px"></div></div>' +
          '<div><div class="lbl" style="margin-bottom:6px">Gaya saran</div>' +
            '<div class="seg"><button data-style="bot">Bot</button><button data-style="human">Manusia</button><button data-style="troll">Troll</button></div>' +
            '<div class="note" data-r="stylenote" style="margin-top:6px"></div></div>' +
          '<div><button class="tbtn" data-premove><span>Premove</span><span class="sw"></span></button>' +
            '<div class="note" data-r="premovenote" style="margin-top:6px"></div></div>' +
          '<div><div class="lbl" style="margin-bottom:6px">Panah</div><div class="chips">' +
            '<label class="chip"><input type="checkbox" data-tier="t1"><span class="dot" style="background:' + TIER_COLOR[1] + '"></span>Utama</label>' +
            '<label class="chip"><input type="checkbox" data-tier="t2"><span class="dot" style="background:' + TIER_COLOR[2] + '"></span>Biasa aja</label>' +
            '<label class="chip"><input type="checkbox" data-tier="t3"><span class="dot" style="background:' + TIER_COLOR[3] + '"></span>Meleset dikit</label>' +
          '</div></div>' +
          '<div class="status"><span class="led" data-r="led"></span><span data-r="status">Mulai…</span></div>' +
          '<details><summary>Debug</summary><pre data-r="debug"></pre>' +
            '<div class="mini"><button data-act="copyfen">Salin FEN</button><button data-act="copylog">Salin log</button></div></details>' +
        '</div></div></div>';

    const $ = (sel) => root.querySelector(sel);
    const el = {
      arrows: $('.arrows'), fab: $('.fab'), panel: $('.panel'), hd: $('.hd'),
      move: $('[data-r=move]'), sub: $('[data-r=sub]'), elo: $('[data-r=elo]'), slider: $('[data-r=slider]'),
      elonote: $('[data-r=elonote]'), stylenote: $('[data-r=stylenote]'), speednote: $('[data-r=speednote]'), led: $('[data-r=led]'),
      status: $('[data-r=status]'), debug: $('[data-r=debug]'),
      premovebtn: $('[data-premove]'), premovenote: $('[data-r=premovenote]'),
    };
    const FAB = 48;
    let open = false;
    const UIstate = { x: 0, y: 0 };

    function defaultPos() { return { x: Math.max(6, window.innerWidth - FAB - 10), y: Math.round(window.innerHeight * 0.45) }; }
    const saved = S.settings.pos;
    Object.assign(UIstate, saved && isFinite(saved.x) && isFinite(saved.y) ? saved : defaultPos());

    function place() {
      const vw = window.innerWidth, vh = window.innerHeight;
      UIstate.x = clamp(UIstate.x, 6, Math.max(6, vw - FAB - 6));
      UIstate.y = clamp(UIstate.y, 6, Math.max(6, vh - FAB - 6));
      el.fab.style.left = UIstate.x + 'px';
      el.fab.style.top = UIstate.y + 'px';
      if (open) {
        const pw = el.panel.offsetWidth || 330, ph = el.panel.offsetHeight || 400;
        el.panel.style.left = clamp(UIstate.x, 6, Math.max(6, vw - pw - 6)) + 'px';
        el.panel.style.top = clamp(UIstate.y, 6, Math.max(6, vh - ph - 6)) + 'px';
      }
    }

    function savePos() { S.settings.pos = { x: UIstate.x, y: UIstate.y }; handlers.save(); }

    function setOpen(v) {
      open = v;
      el.panel.style.display = v ? 'block' : 'none';
      el.fab.style.display = v ? 'none' : 'grid';
      place();
      if (v) { renderDebug(); place(); }
    }

    function drag(handle, getXY, setXY, onTap) {
      let id = null, sx = 0, sy = 0, ox = 0, oy = 0, moved = false;
      handle.addEventListener('pointerdown', (e) => {
        if (e.target.closest && e.target.closest('button')) return;
        id = e.pointerId; moved = false; sx = e.clientX; sy = e.clientY;
        const p = getXY(); ox = p[0]; oy = p[1];
        try { handle.setPointerCapture(id); } catch (er) { }
      });
      handle.addEventListener('pointermove', (e) => {
        if (id !== e.pointerId) return;
        const dx = e.clientX - sx, dy = e.clientY - sy;
        if (!moved && Math.hypot(dx, dy) > 6) moved = true;
        if (moved) { setXY(ox + dx, oy + dy); e.preventDefault(); }
      });
      const end = (e) => {
        if (id !== e.pointerId) return;
        try { handle.releasePointerCapture(id); } catch (er) { }
        id = null;
        if (moved) savePos(); else if (onTap) onTap();
      };
      handle.addEventListener('pointerup', end);
      handle.addEventListener('pointercancel', end);
    }
    drag(el.fab, () => [UIstate.x, UIstate.y], (x, y) => { UIstate.x = x; UIstate.y = y; place(); }, () => setOpen(true));
    drag(el.hd, () => [UIstate.x, UIstate.y], (x, y) => { UIstate.x = x; UIstate.y = y; place(); }, null);

    root.addEventListener('click', (e) => {
      const b = e.target.closest && e.target.closest('[data-act]');
      if (!b) return;
      const a = b.getAttribute('data-act');
      if (a === 'min') setOpen(false);
      else if (a === 'close') handlers.close();
      else if (a === 'copyfen') copyText(S.dbg.fen || '');
      else if (a === 'copylog') copyText(logBuf.join('\n'));
    });

    function copyText(t) {
      const done = () => dbg('disalin ' + t.length + ' karakter');
      try {
        if (navigator.clipboard && navigator.clipboard.writeText) { navigator.clipboard.writeText(t).then(done, () => fallback()); return; }
      } catch (e) { }
      fallback();
      function fallback() {
        try {
          const ta = document.createElement('textarea');
          ta.value = t; ta.style.cssText = 'position:fixed;opacity:0;top:0;left:0';
          document.body.appendChild(ta); ta.select(); document.execCommand('copy'); ta.remove(); done();
        } catch (e) { dbg('gagal menyalin'); }
      }
    }

    const STYLE_NOTE = {
      bot: 'Langkah terbaik Stockfish, dingin dan akurat.',
      human: 'Natural kayak manusia: develop, rokade, makan balik. Sering agak meleset, jadi hijau pun nggak selalu terbaik.',
      troll: 'Nyepelein lawan: Q keluar awal, pion pinggir, niru langkah, nggak buru-buru skakmat, promosi jadi kuda. Tetap aman.',
    };
    function eloText(v) { return v >= 3000 ? '3000+ (penuh)' : '~' + v; }
    function renderSettings() {
      el.slider.value = S.settings.elo;
      el.elo.textContent = eloText(S.settings.elo);
      root.querySelectorAll('[data-style]').forEach((b) => b.classList.toggle('on', b.getAttribute('data-style') === S.settings.style));
      root.querySelectorAll('[data-tier]').forEach((c) => { c.checked = !!S.settings.tiers[c.getAttribute('data-tier')]; });
      el.stylenote.textContent = STYLE_NOTE[S.settings.style];
      el.premovebtn.classList.toggle('on', !!S.settings.premove);
      el.premovenote.textContent = S.settings.premove
        ? 'Nyala: panah tebakan lawan tampil pas giliran lawan (buat premove). Tebakan meleset = panah hilang, muncul lagi setelah jeda.'
        : 'Mati: panah muncul pas giliran kamu. Tebakan tetap disiapin diam-diam, jadi panahnya langsung keluar kalau lawan main sesuai tebakan.';
      root.querySelectorAll('[data-speed]').forEach((b) => b.classList.toggle('on', b.getAttribute('data-speed') === S.settings.speed));
      const sp = CFG.presets[S.settings.speed] || CFG.presets[CFG.defaultSpeed];
      el.speednote.textContent = sp.hint + ' (~' + String(sp.movetime / 1000).replace('.', ',') + ' detik, ' + sp.multipv + ' kandidat)';
      const lo = S.uciMin || 1320;
      el.elonote.textContent = S.settings.elo >= 3000
        ? 'Kekuatan penuh, tanpa batas.'
        : S.settings.elo < lo
          ? 'Di bawah ~' + lo + ' ini TIRUAN KASAR (Skill Level rendah + peluang salah). Angkanya cuma perkiraan.'
          : 'Pakai UCI_Elo bawaan Stockfish. Dihitung cuma ~0,3 detik, jadi angkanya perkiraan.';
    }

    el.slider.addEventListener('input', () => {
      S.settings.elo = +el.slider.value;
      el.elo.textContent = eloText(S.settings.elo);
      renderSettings();
      handlers.eloChanged();
    });
    el.slider.addEventListener('change', () => handlers.save());
    root.querySelectorAll('[data-style]').forEach((b) => b.addEventListener('click', () => {
      S.settings.style = b.getAttribute('data-style');
      renderSettings(); handlers.save(); handlers.styleChanged();
    }));
    el.premovebtn.addEventListener('click', () => {
      S.settings.premove = !S.settings.premove;
      renderSettings(); handlers.save(); handlers.premoveChanged();
    });
    root.querySelectorAll('[data-speed]').forEach((b) => b.addEventListener('click', () => {
      S.settings.speed = b.getAttribute('data-speed');
      renderSettings(); handlers.save(); handlers.speedChanged();
    }));
    root.querySelectorAll('[data-tier]').forEach((c) => c.addEventListener('change', () => {
      S.settings.tiers[c.getAttribute('data-tier')] = c.checked;
      handlers.save(); handlers.redraw();
    }));

    function renderDebug() {
      if (!open) return;
      const d = S.dbg;
      const lines = [
        'halaman : ' + (d.path || '-'),
        'papan   : ' + (d.board || '-'),
        'bidak   : ' + (d.pieces == null ? '-' : d.pieces) + ' | dibalik: ' + (d.flipped ? 'ya' : 'tidak'),
        'giliran : ' + (d.turn || '?') + ' (' + (d.turnSrc || '-') + ') | kamu: ' + (d.me || '-'),
        'jam     : ' + (d.clock || '-'),
        'kandidat: ' + (d.cands || '-'),
        'tebakan : ' + (d.pre || '-'),
        'skor teb: kena ' + S.specStat.hit + ' | nyambung ' + S.specStat.adopt + ' | meleset ' + S.specStat.miss,
        'lawan   : Elo ' + (d.oppElo || '?') + ' | tebak ' + (d.specK || '-') + ' langkah (naik ' + S.specBoost + ')',
        'FEN     : ' + (d.fen || '-'),
        'engine  : ' + (d.engine || '-'),
        'terakhir: ' + (d.last || '-'),
        'galat   : ' + (d.err || '-'),
        '--- log ---',
      ].concat(logBuf.slice(-14));
      el.debug.textContent = lines.join('\n');
    }

    function setStatus(kind, text) {
      el.led.className = 'led ' + (kind || '');
      el.status.textContent = text;
      renderDebug();
    }
    function setSuggestion(main, sub) {
      el.move.textContent = main || '—';
      el.sub.textContent = sub || '';
    }

    let lastArrows = null;
    function drawArrows(arrows, bd, flipped, board) {
      lastArrows = arrows ? { arrows, flipped, board } : null;
      layoutArrows();
    }
    function layoutArrows() {
      const svg = el.arrows;
      while (svg.firstChild) svg.removeChild(svg.firstChild);
      if (!lastArrows || !lastArrows.board || !lastArrows.board.isConnected) { svg.style.display = 'none'; return; }
      const rect = lastArrows.board.getBoundingClientRect();
      const size = Math.min(rect.width, rect.height);
      if (size < 40) { svg.style.display = 'none'; return; }
      svg.style.display = 'block';
      svg.style.left = rect.left + 'px'; svg.style.top = rect.top + 'px';
      svg.style.width = size + 'px'; svg.style.height = size + 'px';
      svg.setAttribute('viewBox', '0 0 ' + size + ' ' + size);
      const sq = size / 8;
      const flipped = lastArrows.flipped;
      const ctr = (idx) => {
        const f = idx & 7, r = idx >> 3;
        return [((flipped ? 7 - f : f) + 0.5) * sq, ((flipped ? r : 7 - r) + 0.5) * sq];
      };
      const Z = { 0: 0, 3: 1, 2: 2, 1: 3 };
      const list = lastArrows.arrows.slice().sort((a, b) => Z[a.tier] - Z[b.tier]);
      const AR = CFG.arrow;
      const w = sq * AR.w, head = sq * AR.head, ol = sq * AR.outline;
      for (const a of list) {
        const i1 = sqIdx(a.move.slice(0, 2)), i2 = sqIdx(a.move.slice(2, 4));
        const df = (i2 & 7) - (i1 & 7), dr = (i2 >> 3) - (i1 >> 3);
        const knight = (Math.abs(df) === 1 && Math.abs(dr) === 2) || (Math.abs(df) === 2 && Math.abs(dr) === 1);
        const p1 = ctr(i1), p2 = ctr(i2);
        const mid = knight ? ctr(Math.abs(df) === 2 ? (i2 & 7) + (i1 >> 3) * 8 : (i1 & 7) + (i2 >> 3) * 8) : null;
        const unit = (u, v) => { const dx = v[0] - u[0], dy = v[1] - u[1], l = Math.hypot(dx, dy) || 1; return [dx / l, dy / l]; };
        const d0 = unit(p1, mid || p2), d1 = unit(mid || p1, p2);
        const sx = p1[0] + d0[0] * sq * 0.18, sy = p1[1] + d0[1] * sq * 0.18;
        const bx = p2[0] - d1[0] * head * 0.9, by = p2[1] - d1[1] * head * 0.9;
        const tx = p2[0] - d1[0] * sq * 0.06, ty = p2[1] - d1[1] * sq * 0.06;
        const nx = -d1[1], ny = d1[0], hw = head * 0.5;
        const dPath = 'M' + sx + ' ' + sy + (mid ? ' L' + mid[0] + ' ' + mid[1] : '') + ' L' + bx + ' ' + by;
        const pts = [tx, ty, bx + nx * hw, by + ny * hw, bx - nx * hw, by - ny * hw].join(',');
        const g = document.createElementNS(NS_SVG, 'g');
        g.setAttribute('opacity', '0.92');
        for (const layer of [{ c: '#ffffff', extra: ol * 2 }, { c: TIER_COLOR[a.tier], extra: 0 }]) {
          const pa = document.createElementNS(NS_SVG, 'path');
          pa.setAttribute('d', dPath); pa.setAttribute('fill', 'none'); pa.setAttribute('stroke', layer.c);
          pa.setAttribute('stroke-width', w + layer.extra); pa.setAttribute('stroke-linecap', 'round'); pa.setAttribute('stroke-linejoin', 'round');
          g.appendChild(pa);
          const pg = document.createElementNS(NS_SVG, 'polygon');
          pg.setAttribute('points', pts); pg.setAttribute('fill', layer.c);
          if (layer.extra) { pg.setAttribute('stroke', layer.c); pg.setAttribute('stroke-width', layer.extra); pg.setAttribute('stroke-linejoin', 'round'); }
          g.appendChild(pg);
        }
        svg.appendChild(g);
      }
    }

    let raf = 0;
    function relayout() {
      if (raf) return;
      raf = requestAnimationFrame(() => { raf = 0; place(); layoutArrows(); });
    }
    window.addEventListener('resize', relayout);
    window.addEventListener('scroll', relayout, true);
    if (window.visualViewport) window.visualViewport.addEventListener('resize', relayout);

    renderSettings();
    place();
    (document.documentElement || document.body).appendChild(host);

    return {
      host, setStatus, setSuggestion, drawArrows, relayout, renderSettings, renderDebug,
      setVisible(v) { host.style.display = v ? '' : 'none'; },
      destroy() {
        try { window.removeEventListener('resize', relayout); window.removeEventListener('scroll', relayout, true); } catch (e) { }
        host.remove();
      },
    };
  }

  function onActivePage() {
    return location.hostname === CFG.host;
  }

  function init() {
    if (!onActivePage()) return;

    const S = {
      settings: Object.assign({}, DEFAULTS, store.get('cch_settings', {})),
      dead: false, suspended: false,
      board: null, observer: null, resizeObs: null,
      sig: '', prevBd: null, rights: null, turn: null, turnSrc: '', lastMove: { w: null, b: null },
      boardTurn: null, boardTurnSrc: '', needRun: true, arb: { since: 0 }, clockMem: {}, flippedSeen: null, pendingShown: false,
      flipped: false, me: null,
      reqId: 0, last: null, ep: '', pingP: null, oppElo: null, specBoost: 0, spec: null, specHit: null, specAdopt: null, specStat: { hit: 0, adopt: 0, miss: 0 }, preMiss: false,
      dbg: {}, uciMin: 1320, uciMax: 3190,
      bridgeOk: false, bridgeChecked: false, bridgeErr: '', lastPing: 0, pinging: false,
      snapTimer: 0, snapTries: 0, tickTimer: 0, clockTimer: 0, redrawTimer: 0, eloTimer: 0,
    };
    S.settings.tiers = Object.assign({}, DEFAULTS.tiers, S.settings.tiers || {});
    if (!['bot', 'human', 'troll'].includes(S.settings.style)) S.settings.style = 'bot';
    if (!CFG.presets[S.settings.speed]) S.settings.speed = CFG.defaultSpeed;
    S.settings.elo = clamp(+S.settings.elo || 3000, 100, 3000);
    S.settings.premove = !!S.settings.premove;

    const bridge = new BridgeEngine(CFG.bridge);
    const wasm = new WasmEngine(CFG);
    let ui = null;

    const save = () => store.set('cch_settings', S.settings);

    function engineLabel() {
      if (S.bridgeOk) return 'jembatan: ' + ((bridge.info && bridge.info.name) || 'Stockfish');
      if (wasm.state === 'ready') return 'WASM lite (cadangan, lebih lemah)';
      if (wasm.state === 'loading') return 'memuat WASM…';
      return S.bridgeChecked ? 'jembatan tidak terhubung' : 'mengecek jembatan…';
    }
    function status(kind, text) {
      S.dbg.engine = engineLabel();
      if (ui) ui.setStatus(kind, text);
    }

    function pingBridge() {
      if (S.dead) return Promise.resolve();
      if (S.pinging) return S.pingP || Promise.resolve();
      S.pingP = doPing();
      return S.pingP;
    }
    async function doPing() {
      S.pinging = true;
      try {
        const j = await bridge.ping();
        const was = S.bridgeOk;
        S.bridgeOk = true; S.bridgeErr = '';
        const r = j.engine && j.engine.uci_elo;
        if (r) { S.uciMin = r.min; S.uciMax = r.max; }
        if (!was) dbg('jembatan terhubung: ' + (j.engine && j.engine.name));
      } catch (e) {
        if (S.bridgeOk) dbg('jembatan putus: ' + e.message);
        S.bridgeOk = false; S.bridgeErr = e.message;
      } finally {
        S.pinging = false; S.bridgeChecked = true; S.lastPing = Date.now();
        S.dbg.engine = engineLabel();
        if (ui) ui.renderSettings();
      }
    }

    function findBoard() {
      return document.querySelector('wc-chess-board') || document.querySelector('chess-board') ||
        document.querySelector('#board-single') || document.querySelector('.board');
    }
    function readSnapshot(board) {
      const bd = new Array(64).fill('');
      let dup = false, count = 0;
      for (const el of board.querySelectorAll('.piece')) {
        let type = null, sq = -1;
        for (const c of el.classList) {
          if (c.length === 2 && /^[wb][pnbrqk]$/.test(c)) type = c;
          else if (c.length === 9 && c.indexOf('square-') === 0) {
            const f = +c[7], r = +c[8];
            if (f >= 1 && f <= 8 && r >= 1 && r <= 8) sq = (f - 1) + (r - 1) * 8;
          }
        }
        if (!type || sq < 0) continue;
        if (bd[sq]) dup = true;
        bd[sq] = type[0] === 'w' ? type[1].toUpperCase() : type[1];
        count++;
      }
      const hl = [];
      for (const el of board.querySelectorAll('.highlight')) {
        for (const c of el.classList) {
          if (c.length === 9 && c.indexOf('square-') === 0) {
            const f = +c[7], r = +c[8];
            if (f >= 1 && f <= 8 && r >= 1 && r <= 8) { const i = (f - 1) + (r - 1) * 8; if (hl.indexOf(i) < 0) hl.push(i); }
          }
        }
      }
      return { bd, dup, count, hl, flipped: board.classList.contains('flipped') };
    }

    function scheduleSnapshot(delay) {
      if (S.dead || S.suspended) return;
      clearTimeout(S.snapTimer);
      S.snapTimer = setTimeout(takeSnapshot, delay == null ? 35 : delay);
    }

    function takeSnapshot(force) {
      if (S.dead || S.suspended) return;
      if (!S.board || !S.board.isConnected) return;
      const snap = readSnapshot(S.board);
      S.dbg.pieces = snap.count; S.dbg.flipped = snap.flipped;
      if (snap.dup) {
        if (S.snapTries++ < 8) { scheduleSnapshot(50); return; }
        status('err', 'Papan nggak terbaca (bidak numpuk)'); return;
      }
      S.snapTries = 0;
      const placement = fenPlacement(snap.bd);
      const sig = placement + '|' + (snap.flipped ? 'f' : 'n');
      if (sig === S.sig && force !== true) return;
      S.sig = sig;
      processSnapshot(snap, placement);
    }

    function processSnapshot(snap, placement) {
      const prev = S.prevBd;
      const changedPos = !prev || fenPlacement(prev) !== placement;
      S.flipped = snap.flipped;
      if (S.me == null || placement === START_PLACEMENT) S.me = snap.flipped ? 'b' : 'w';
      S.dbg.me = S.me === 'w' ? 'putih' : 'hitam';
      if (S.flippedSeen !== snap.flipped) { S.flippedSeen = snap.flipped; S.needRun = true; }

      if (changedPos) {
        const spec = S.spec;
        const shown = !!(S.last && S.last.pre);
        const hitLast = spec ? spec.cache.get(placement) || null : null;
        const adopt = spec && !hitLast && spec.inflight && spec.inflight.placement === placement ? spec.inflight : null;
        if (hitLast) cancelAnalysis(hitLast === S.last);
        else if (adopt) { spec.stop = true; clearArrowsNow(); S.last = null; }
        else cancelAnalysis();
        if (spec) {
          if (hitLast) { S.specStat.hit++; S.specBoost++; } else if (adopt) { S.specStat.adopt++; S.specBoost++; } else { S.specStat.miss++; S.specBoost = 0; }
        }
        S.specHit = hitLast; S.specAdopt = adopt;
        S.preMiss = !hitLast && !adopt && S.settings.premove && shown;
        S.spec = null;
        let turn = null, src = '';
        let diff = null;
        S.ep = '';
        if (placement === START_PLACEMENT) {
          turn = 'w'; src = 'posisi awal'; S.rights = 'KQkq'; S.lastMove = { w: null, b: null }; S.specBoost = 0;
        } else {
          diff = prev ? diffInfo(prev, snap.bd) : null;
          const dm = diff ? diff.mover : null;
          const hm = highlightMover(snap.bd, snap.hl, prev);
          const mover = dm || hm;
          if (mover) {
            turn = mover === 'w' ? 'b' : 'w';
            src = dm ? (hm && hm !== dm ? 'selisih papan (highlight beda)' : 'selisih papan') : 'highlight';
          }
        }
        const guess = guessRights(snap.bd);
        S.rights = S.rights == null ? guess : intersectRights(S.rights, guess);
        if (diff && diff.mover && diff.arrivals.length === 1 && diff.departures.length === 1) {
          const to = diff.arrivals[0], from = diff.departures[0];
          const pc = snap.bd[to];
          S.lastMove[diff.mover] = { from, to, piece: prev[from] ? prev[from].toLowerCase() : pc.toLowerCase() };
          if ((pc === 'P' || pc === 'p') && Math.abs(to - from) === 16) {
            const enemy = diff.mover === 'w' ? 'p' : 'P';
            const f = to & 7;
            if ((f > 0 && snap.bd[to - 1] === enemy) || (f < 7 && snap.bd[to + 1] === enemy)) S.ep = sqName((to + from) / 2);
          }
        } else if (diff && diff.mover && diff.arrivals.length === 2 && diff.departures.length === 2) {
          const k = diff.arrivals.find((i) => snap.bd[i] === 'K' || snap.bd[i] === 'k');
          if (k != null) {
            const kf = diff.departures.find((i) => prev[i] === 'K' || prev[i] === 'k');
            if (kf != null) S.lastMove[diff.mover] = { from: kf, to: k, piece: 'k' };
          }
        }
        S.boardTurn = turn; S.boardTurnSrc = src;
        S.arb.since = 0; S.needRun = true;
      }
      S.prevBd = snap.bd;
      S.bd = snap.bd;
      syncTurn();
    }

    function readClocks(board) {
      let els = Array.from(document.querySelectorAll('.clock-component'));
      if (!els.length) {
        els = Array.from(document.querySelectorAll('[class*="clock"]'))
          .filter((e) => parseClockText((e.textContent || '').replace(/\s+/g, '')) != null);
        els = els.filter((e) => !els.some((o) => o !== e && o.contains(e)));
      }
      els = els.filter((e) => e.getClientRects().length > 0);
      let midY = null;
      try { const br = board.getBoundingClientRect(); if (br.height > 0) midY = br.top + br.height / 2; } catch (e) { }
      return els.slice(0, 6).map((e) => {
        const cls = e.getAttribute('class') || '';
        let pos = /\bclock-bottom\b/.test(cls) ? 'bottom' : /\bclock-top\b/.test(cls) ? 'top' : null;
        if (!pos && e.closest) {
          if (e.closest('#board-layout-player-bottom, .board-layout-bottom')) pos = 'bottom';
          else if (e.closest('#board-layout-player-top, .board-layout-top')) pos = 'top';
        }
        if (!pos && midY != null) {
          const r = e.getBoundingClientRect();
          if (r.height > 0) pos = (r.top + r.height / 2) > midY ? 'bottom' : 'top';
        }
        return {
          color: /\bclock-white\b/.test(cls) ? 'w' : /\bclock-black\b/.test(cls) ? 'b' : null,
          pos, turnClass: /\bclock-player-turn\b/.test(cls), text: (e.textContent || '').replace(/\s+/g, ''),
        };
      });
    }

    function syncTurn() {
      if (S.dead || S.suspended || !S.board || !S.bd || S.me == null) return;
      const now = Date.now();
      const ck = clockTurn(readClocks(S.board), S.flipped ? 'b' : 'w', S.clockMem, now, CFG.clockTickMs);
      if (S.dbg.clock !== ck.note) { S.dbg.clock = ck.note; if (ui) ui.renderDebug(); }
      const d = arbitrateTurn(ck, S.boardTurn, S.boardTurnSrc, S.arb, now, CFG.clockSettleMs);
      if (d.pending) {
        if (!S.pendingShown) {
          S.pendingShown = true;
          if (ui) ui.setSuggestion('—', 'Nyocokin jam dan papan…');
          status('warn', 'Jam dan papan belum sepakat, nunggu bentar…');
        }
        return;
      }
      S.pendingShown = false;
      const turnChanged = d.turn !== S.turn;
      S.turn = d.turn; S.turnSrc = d.src;
      S.dbg.turn = d.turn ? (d.turn === 'w' ? 'putih' : 'hitam') : null; S.dbg.turnSrc = d.src;
      if (turnChanged || S.needRun) { S.needRun = false; onPositionReady(); }
    }

    function readOppElo() {
      let box = null;
      for (const sel of ['#board-layout-player-top', '.board-layout-top', '[class*="player-top"]', '.player-top']) {
        const e = document.querySelector(sel);
        if (e) { box = e; break; }
      }
      if (!box) return null;
      const ok = (v) => (v >= 100 && v <= 3600 ? v : null);
      for (const e of box.querySelectorAll('[class*="rating"]')) {
        const m = /(\d{3,4})/.exec(String(e.textContent || '').replace(/[,\s]/g, ''));
        if (m && ok(+m[1])) return +m[1];
      }
      const txt = String(box.textContent || '');
      let m = /\((\d{3,4})\)/.exec(txt);
      if (m && ok(+m[1])) return +m[1];
      const all = txt.match(/\b\d{3,4}\b/g);
      if (all) { const v = +all[all.length - 1]; if (ok(v)) return v; }
      return null;
    }

    function clearArrowsNow() { if (ui) ui.drawArrows(null); }

    function cancelAnalysis(keepArrows) {
      S.reqId++;
      bridge.abort();
      wasm.gen++; if (wasm.searching) wasm._send('stop');
      if (!keepArrows) { clearArrowsNow(); S.last = null; }
    }

    function showHit(last) {
      S.dbg.err = ''; S.dbg.fen = last.fen; S.dbg.pre = '';
      S.last = Object.assign({}, last, { bd: S.bd, flipped: S.flipped, board: S.board, pre: false, hit: true });
      render();
    }

    async function onPositionReady() {
      const turnMe = !!S.turn && S.turn === S.me;
      if (turnMe && S.specHit) {
        const hit = S.specHit; S.specHit = null; S.specAdopt = null; S.preMiss = false;
        showHit(hit);
        return;
      }
      if (turnMe && S.specAdopt) {
        const ad = S.specAdopt; S.specAdopt = null; S.preMiss = false;
        const id0 = S.reqId;
        ui.setSuggestion('—', 'Tebakan lawan benar, hitungan lagi diselesein…');
        status('warn', 'Tebakan benar, nunggu hitungan yang lagi jalan…');
        let last = null;
        try { last = await ad.promise; } catch (e) { last = null; }
        if (id0 !== S.reqId) return;
        if (last) { showHit(last); return; }
      }
      cancelAnalysis();
      const id = S.reqId;
      if (!S.turn) {
        ui.setSuggestion('—', '');
        status('warn', 'Giliran belum ketahuan, tunggu langkah berikutnya.');
        return;
      }
      if (S.turn !== S.me) {
        S.specHit = null; S.specAdopt = null; S.preMiss = false; S.spec = null;
        if (S.settings.premove) { ui.setSuggestion('—', 'Giliran lawan, nebak langkahnya…'); status('warn', 'Nebak langkah lawan…'); }
        else { ui.setSuggestion('—', 'Giliran lawan'); status('ok', 'Giliran lawan.'); }
        if (CFG.speculate) await speculate(id);
        return;
      }
      const miss = S.preMiss; S.preMiss = false; S.specHit = null; S.specAdopt = null;
      const bd = S.bd;
      const err = validateBoard(bd, S.turn);
      const fen = buildFEN(bd, S.turn, S.rights, S.ep);
      S.dbg.fen = fen;
      if (err) {
        S.dbg.err = err;
        ui.setSuggestion('—', '');
        status('err', 'Posisi nggak valid: ' + err + '. Nggak dikirim ke engine.');
        return;
      }
      S.dbg.err = '';
      if (miss) {
        ui.setSuggestion('—', 'Tebakan lawan meleset, hitung ulang…');
        status('warn', 'Tebakan meleset, panah baru sebentar lagi…');
        await sleep(CFG.premoveMissDelayMs);
        if (id !== S.reqId) return;
      }
      await analyze(id, fen);
    }

    function preset() { return CFG.presets[S.settings.speed] || CFG.presets[CFG.defaultSpeed]; }

    const resCache = new Map();
    const resKey = (fen) => fen + '|' + S.settings.speed + '|' + S.settings.elo;
    function remember(fen, res, via, ms) {
      if (!res || !res.lines || !res.lines.length) return;
      const k = resKey(fen);
      resCache.delete(k); resCache.set(k, { res, via, ms });
      if (resCache.size > 60) resCache.delete(resCache.keys().next().value);
    }

    function buildRequest(fen, usingWasm, plan) {
      const p = preset();
      return {
        fen, multipv: usingWasm ? p.multipvWasm : p.multipv, movetime: p.movetime,
        options: {}, probe: plan.probe,
      };
    }

    async function runEngine(id, fen, opt) {
      opt = opt || {};
      const mk = (usingWasm, plan) => {
        const rq = buildRequest(fen, usingWasm, plan);
        if (opt.multipv) rq.multipv = opt.multipv;
        if (opt.probe !== undefined) rq.probe = opt.probe;
        return rq;
      };
      let res = null, via = '';
      if (S.bridgeOk) {
        try {
          const plan = eloPlan(S.settings.elo, S.uciMin, S.uciMax, preset().probeTime);
          res = await bridge.analyze(mk(false, plan));
          via = 'jembatan';
        } catch (e) {
          if (id !== S.reqId) return null;
          if (e.kind === 'engine') throw e;
          S.bridgeOk = false; S.bridgeErr = e.message;
          dbg('jembatan gagal, pindah ke WASM: ' + e.message);
          if (ui) ui.renderSettings();
        }
      }
      if (id !== S.reqId) return null;
      if (!res) {
        if (wasm.state !== 'ready') status('warn', 'Jembatan tidak terhubung. Memuat WASM (±1,8 MB)…');
        S.uciMin = wasm.range.min; S.uciMax = wasm.range.max;
        const plan = eloPlan(S.settings.elo, S.uciMin, S.uciMax, preset().probeTime);
        res = await wasm.analyze(mk(true, plan), (st) => { if (st === 'loading') status('warn', 'Memuat WASM (±1,8 MB)…'); });
        S.uciMin = wasm.range.min; S.uciMax = wasm.range.max;
        if (ui) ui.renderSettings();
        via = 'WASM';
      }
      if (id !== S.reqId || res.cancelled) return null;
      return { res, via };
    }

    function engineFail(e) {
      const msg = String(e && e.message || e);
      S.dbg.err = msg;
      dbg('analisis gagal: ' + msg);
      ui.setSuggestion('—', '');
      if (e.kind === 'wasm') {
        status('err', e.wasmFailure === 'blocked' ? 'Worker diblokir (' + msg + ')' :
          e.wasmFailure === 'download' ? 'WASM gagal diunduh (' + msg + ')' : 'Engine WASM error (' + msg + ')');
      } else status('err', 'Engine error: ' + msg);
    }

    async function analyze(id, fen) {
      const cached = resCache.get(resKey(fen));
      if (cached && id === S.reqId) {
        S.last = { res: cached.res, fen, via: cached.via, ms: cached.ms, bd: S.bd, flipped: S.flipped, board: S.board };
        S.dbg.last = cached.via + ' | cache | depth ' + cached.res.depth + ' | ' + cached.res.lines.length + ' kandidat';
        render();
        return;
      }
      if (!S.bridgeChecked) { status('warn', 'Mengecek jembatan…'); await pingBridge(); if (id !== S.reqId) return; }
      const t0 = performance.now();
      status('warn', 'Menghitung…');
      let out;
      try { out = await runEngine(id, fen); } catch (e) { if (id !== S.reqId) return; engineFail(e); return; }
      if (!out) return;
      const res = out.res, via = out.via;
      if (!res.lines || !res.lines.length) {
        ui.setSuggestion('—', 'Nggak ada langkah');
        status('warn', 'Engine nggak nemu langkah (game selesai?).');
        return;
      }
      S.last = { res, fen, via, ms: Math.round(performance.now() - t0), bd: S.bd, flipped: S.flipped, board: S.board };
      S.dbg.last = via + ' | ' + S.last.ms + ' ms | depth ' + res.depth + ' | ' + res.lines.length + ' kandidat';
      remember(fen, res, via, S.last.ms);
      render();
    }

    async function speculate(id) {
      const bd = S.bd, oppTurn = S.turn;
      const spec = { base: fenPlacement(bd), cache: new Map(), inflight: null, stop: false, first: null };
      S.spec = spec;
      const vis = () => S.settings.premove && S.spec === spec && !spec.stop;
      const err = validateBoard(bd, oppTurn);
      if (err) {
        dbg('tebakan dilewati: ' + err);
        if (S.settings.premove) { S.dbg.err = err; ui.setSuggestion('—', ''); status('err', 'Posisi nggak valid: ' + err + '. Nggak dikirim ke engine.'); }
        return;
      }
      S.dbg.err = '';
      const fenOpp = buildFEN(bd, oppTurn, S.rights, S.ep);
      S.dbg.fen = fenOpp;
      if (!S.bridgeChecked) { await pingBridge(); if (id !== S.reqId) return; }
      const pr = preset();
      const baseK = pr.specCands || 3;
      const K0 = Math.min(pr.specMax || baseK, baseK + S.specBoost);
      const oppElo = CFG.oppElo || readOppElo() || S.oppElo || null;
      if (oppElo) S.oppElo = oppElo;
      S.dbg.oppElo = oppElo ? oppElo + (CFG.oppElo ? ' (manual)' : '') : null;
      const oplan = oppElo ? eloPlan(oppElo, S.uciMin, S.uciMax, pr.probeTime) : null;
      let o1;
      try { o1 = await runEngine(id, fenOpp, { multipv: K0, probe: oplan ? oplan.probe : null }); } catch (e) {
        if (id !== S.reqId) return;
        if (vis()) engineFail(e); else dbg('tebakan gagal: ' + String(e && e.message || e));
        return;
      }
      if (!o1) return;
      const K = o1.via === 'jembatan' ? K0 : Math.min(K0, CFG.specWasmCands);
      const lines = (o1.res.lines || []).slice().sort((x, y) => x.rank - y.rank);
      const sc = lines.map(scoreOf);
      const top = sc.length ? Math.max.apply(null, sc) : 0;
      const win = oppElo ? Math.round(clamp(CFG.specWindow + (2800 - oppElo) / 8, CFG.specWindow, 350)) : CFG.specWindow;
      const moves = [];
      const bm = o1.res.bestmove || (lines[0] && lines[0].move);
      if (bm) moves.push(bm);
      const pb = o1.res.probe_bestmove;
      if (pb && moves.indexOf(pb) < 0) moves.push(pb);
      lines.forEach((l, i) => { if (top - sc[i] <= win && moves.indexOf(l.move) < 0) moves.push(l.move); });
      const cands = moves.slice(0, K);
      if (!cands.length) {
        if (vis()) { ui.setSuggestion('—', 'Giliran lawan'); status('warn', 'Nggak bisa nebak langkah lawan (game selesai?).'); }
        return;
      }
      S.dbg.pre = cands.map((m) => describeMove(bd, m)).join(' | ') + ' (' + o1.via + ')';
      S.dbg.specK = cands.length;
      if (ui) ui.renderDebug();
      for (let i = 0; i < cands.length; i++) {
        if (S.spec !== spec || spec.stop || id !== S.reqId) return;
        const t1 = performance.now();
        const m = cands[i];
        const ap = applyMove(bd, m);
        if (!ap || isWhitePc(ap.piece) !== (oppTurn === 'w')) continue;
        const rights2 = S.rights == null ? guessRights(ap.bd) : intersectRights(S.rights, guessRights(ap.bd));
        let ep2 = '';
        if (ap.piece.toLowerCase() === 'p' && Math.abs(ap.to - ap.from) === 16) {
          const enemy = isWhitePc(ap.piece) ? 'p' : 'P';
          const f = ap.to & 7;
          if ((f > 0 && ap.bd[ap.to - 1] === enemy) || (f < 7 && ap.bd[ap.to + 1] === enemy)) ep2 = sqName((ap.to + ap.from) / 2);
        }
        const err2 = validateBoard(ap.bd, S.me);
        if (err2) { dbg('tebakan ' + m + ' dilewati: ' + err2); continue; }
        const placement = fenPlacement(ap.bd);
        const fenMe = buildFEN(ap.bd, S.me, rights2, ep2);
        const predText = describeMove(bd, m);
        if (i === 0 && vis()) status('warn', 'Premove: hitung saran kalau lawan main ' + predText + '…');
        const p = (async () => {
          const o2 = await runEngine(id, fenMe);
          if (!o2 || !o2.res.lines || !o2.res.lines.length) return null;
          remember(fenMe, o2.res, o2.via, Math.round(performance.now() - t1));
          return {
            res: o2.res, fen: fenMe, via: o2.via, ms: Math.round(performance.now() - t1), bd: ap.bd, flipped: S.flipped, board: S.board,
            pre: true, predText, rights: rights2, oppLast: { from: ap.from, to: ap.to, piece: ap.piece.toLowerCase() },
          };
        })();
        spec.inflight = { placement, promise: p };
        let last = null;
        try { last = await p; } catch (e) {
          spec.inflight = null;
          if (S.spec !== spec || id !== S.reqId) return;
          if (i === 0 && vis()) engineFail(e); else dbg('tebakan ' + m + ' gagal: ' + String(e && e.message || e));
          return;
        }
        spec.inflight = null;
        if (last) { spec.cache.set(placement, last); if (i === 0) spec.first = last; }
        if (S.spec !== spec || spec.stop || id !== S.reqId) return;
        if (!last) continue;
        if (i === 0) {
          S.dbg.last = 'tebakan | ' + last.via + ' | ' + last.ms + ' ms | depth ' + last.res.depth + ' | ' + last.res.lines.length + ' kandidat';
          if (vis()) { S.last = last; render(); }
        }
      }
    }

    function render() {
      const L = S.last;
      if (!L || !ui) return;
      const white = S.me === 'w';
      const plan = eloPlan(S.settings.elo, S.uciMin, S.uciMax, preset().probeTime);
      const ctx = {
        bd: L.bd, white, rights: L.rights != null ? L.rights : (S.rights || ''), lastMine: S.lastMove[S.me],
        oppLast: L.oppLast !== undefined ? L.oppLast : S.lastMove[white ? 'b' : 'w'],
        plan, style: S.settings.style,
        opening: pieceCount(L.bd) >= 26 && undevMinors(L.bd, white) >= 2,
        attackedBefore: attackedPieces(L.bd, white).map((a) => a.i),
        humanSlip: 0.3 + 0.3 * (1 - S.settings.elo / 3000),
        seed: L.fen + '|' + S.settings.style + '|' + S.settings.elo,
      };
      const d = decide(L.res, ctx);
      if (!d) return;
      S.dbg.cands = d.cs.map((c) => c.move + ' ' + fmtEval(c.score, c.mate)
        + (c === d.tiers[1] ? ' [H]' : c === d.tiers[2] ? ' [K]' : c === d.tiers[3] ? ' [M]' : '') + (c === d.pick ? ' *' : '')).join(' | ');
      ui.renderDebug();
      const arrows = [], seen = new Set();
      const add = (move, tier, emph) => {
        if (seen.has(move)) { dbg('panah dobel dibuang: ' + move + ' (tingkat ' + tier + ')'); return; }
        seen.add(move); arrows.push({ move, tier, emph });
      };
      for (const t of [1, 2, 3]) {
        const c = d.tiers[t];
        if (c && S.settings.tiers['t' + t]) add(c.move, t, c === d.pick);
      }
      if (d.pickTier === 0 && S.settings.tiers.t3) add(d.pick.move, 0, true);
      ui.drawArrows(arrows, L.bd, L.flipped, L.board);
      const styleName = { bot: 'Bot', human: 'Manusia', troll: 'Troll' }[d.styleUsed];
      const tierName = {
        1: d.pick === d.bestC ? 'terbaik' : (d.trollWin ? 'masih menang' : 'hampir terbaik'),
        2: 'biasa', 3: 'jelek tapi aman', 0: 'di luar batas aman (tiruan Elo rendah)',
      }[d.pickTier] || '';
      const ev = fmtEval(d.evalScore, d.evalMate);
      const sub = ['Eval ' + ev + (d.evalScore >= 150 ? ' (kamu unggul)' : d.evalScore <= -150 ? ' (kamu ketinggalan)' : ' (seimbang)'),
        styleName + (tierName ? ' · ' + tierName : '') + (d.tags.length ? ' · ' + d.tags.join(', ') : '')].join('\n');
      const bestLine = d.styleUsed !== 'bot' && d.pick !== d.bestC
        ? '\nTerbaik engine: ' + describeMove(L.bd, d.bestC.move) + ' (' + fmtEval(d.bestC.score, d.bestC.mate) + ')' : '';
      const preLine = L.pre ? 'Premove: kalau lawan main ' + L.predText + '\n' : '';
      ui.setSuggestion(describeMove(L.bd, d.pick.move), preLine + sub + bestLine + (d.note ? '\n' + d.note : ''));
      status('ok', L.pre ? 'Premove (tebakan ' + L.predText + ') · ' + L.via + ' · ' + L.ms + ' ms · depth ' + L.res.depth
        : L.hit ? 'Tebakan lawan benar, udah dihitung duluan · ' + L.via + ' · depth ' + L.res.depth
        : 'Siap · ' + L.via + ' · ' + L.ms + ' ms · depth ' + L.res.depth);
    }

    function attachBoard(board) {
      if (S.observer) S.observer.disconnect();
      if (S.resizeObs) S.resizeObs.disconnect();
      S.board = board;
      S.observer = new MutationObserver(() => scheduleSnapshot());
      S.observer.observe(board, { subtree: true, childList: true, attributes: true, attributeFilter: ['class'] });
      if (typeof ResizeObserver === 'function') {
        S.resizeObs = new ResizeObserver(() => ui && ui.relayout());
        S.resizeObs.observe(board);
      }
      S.dbg.board = board.tagName.toLowerCase() + (board.id ? '#' + board.id : '');
      S.sig = ''; S.prevBd = null; S.rights = null; S.lastMove = { w: null, b: null };
      S.me = null; S.turn = null; S.boardTurn = null; S.boardTurnSrc = ''; S.arb.since = 0;
      S.clockMem = {}; S.needRun = true; S.flippedSeen = null; S.pendingShown = false;
      S.spec = null; S.specHit = null; S.specAdopt = null; S.preMiss = false; S.specBoost = 0; S.oppElo = null;
      dbg('papan ketemu: ' + S.dbg.board);
      takeSnapshot(true);
    }

    function suspend() {
      if (S.suspended) return;
      S.suspended = true;
      S.reqId++; bridge.abort(); wasm.terminate();
      if (S.observer) S.observer.disconnect();
      if (S.resizeObs) S.resizeObs.disconnect();
      S.observer = null; S.resizeObs = null; S.board = null;
      S.spec = null; S.specHit = null; S.specAdopt = null; S.preMiss = false;
      clearTimeout(S.snapTimer);
      if (ui) { ui.drawArrows(null); ui.setVisible(false); }
      dbg('halaman tidak didukung, script istirahat');
    }
    function resume() {
      if (!S.suspended) return;
      S.suspended = false; S.sig = ''; S.prevBd = null;
      if (ui) ui.setVisible(true);
      dbg('di halaman chess.com, script lanjut');
    }

    function tick() {
      if (S.dead) return;
      S.dbg.path = location.pathname;
      if (!onActivePage()) { suspend(); return; }
      if (S.suspended) resume();
      const b = findBoard();
      if (!b) {
        if (S.board) { S.board = null; if (S.observer) S.observer.disconnect(); clearArrowsNow(); }
        status('warn', 'Papan nggak ketemu (selektor DOM mungkin berubah).');
        return;
      }
      if (b !== S.board) attachBoard(b);
      const gap = S.bridgeOk ? CFG.bridgePingMs * 4 : CFG.bridgePingMs;
      if (Date.now() - S.lastPing > (S.bridgeOk ? CFG.bridgeAlivePingMs : gap)) pingBridge();
    }

    function shutdown() {
      S.dead = true;
      clearInterval(S.tickTimer); clearInterval(S.clockTimer); clearTimeout(S.snapTimer); clearTimeout(S.eloTimer);
      S.reqId++;
      try { bridge.abort(); } catch (e) { }
      try { wasm.terminate(); } catch (e) { }
      if (S.observer) S.observer.disconnect();
      if (S.resizeObs) S.resizeObs.disconnect();
      if (ui) ui.destroy();
      ui = null;
    }

    function recompute(clearFirst) {
      if (S.dead || !S.me || !S.turn) return;
      if (S.turn === S.me) {
        if (!S.dbg.fen || S.dbg.err) return;
        if (clearFirst) cancelAnalysis(); else S.reqId++;
        analyze(S.reqId, S.dbg.fen);
      } else if (CFG.speculate) {
        cancelAnalysis(); S.spec = null;
        speculate(S.reqId);
      }
    }

    ui = createUI(S, {
      save,
      close: shutdown,
      redraw: () => render(),
      styleChanged: () => render(),
      speedChanged: () => recompute(true),
      eloChanged: () => { clearTimeout(S.eloTimer); S.eloTimer = setTimeout(() => recompute(false), 350); },
      premoveChanged: () => {
        S.preMiss = false;
        if (S.dead || !S.me || !S.turn || S.turn === S.me) return;
        if (S.settings.premove) {
          if (S.spec && S.spec.first) { S.last = S.spec.first; render(); }
          else if (!S.spec) { cancelAnalysis(); speculate(S.reqId); }
          else { ui.setSuggestion('—', 'Giliran lawan, nebak langkahnya…'); status('warn', 'Nebak langkah lawan…'); }
        } else if (S.last && S.last.pre) {
          clearArrowsNow(); S.last = null;
          ui.setSuggestion('—', 'Giliran lawan'); status('ok', 'Giliran lawan.');
        }
      },
    });
    S.dbg.engine = engineLabel();
    status('warn', 'Mulai…');
    pingBridge();
    S.tickTimer = setInterval(tick, 400);
    S.clockTimer = setInterval(syncTurn, CFG.clockPollMs);
    tick();

    if (typeof globalThis.__CCH_TEST_HOOK__ === 'function') globalThis.__CCH_TEST_HOOK__({ S, bridge, wasm, tick, takeSnapshot, shutdown });
  }

  if (typeof globalThis.__CCH_TEST_CORE__ === 'function') {
    globalThis.__CCH_TEST_CORE__({
      fenPlacement, buildFEN, validateBoard, applyMove, attackersOf, isAttacked, attackedPieces, guessRights, intersectRights,
      diffInfo, highlightMover, decide, eloPlan, scoreOf, fmtEval, describeMove, parseInfo, LineCollector, sqName, sqIdx,
      undevMinors, pieceCount, CFG, START_PLACEMENT, parseClockText, clockTurn, arbitrateTurn, arrowLane,
    });
  }
  if (!globalThis.__CCH_NOSTART__) init();
})();
