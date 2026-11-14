// ==UserScript==
// @name         NebulaChess
// @namespace    local.nebulachess
// @version      0.1.1
// @description  Tool Assisten Chess
// @match        https://www.chess.com/play/computer*
// @match        https://www.chess.com/play/online*
// @match        https://www.chess.com/game/*
// @match        https://www.chess.com/live*
// @match        https://www.chess.com/daily*
// @match        https://www.chess.com/home*
// @match        https://www.chess.com/play
// @match        https://www.chess.com/
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
    name: 'NebulaChess',
    host: 'www.chess.com',
    pathRe: /^\/(play\/(computer|online)|game(\/(live|daily))?|live|daily)(\/|$)/,
    setupRe: /^\/(home|play)?\/?$/,
    bridge: 'http://127.0.0.1:8765',
    wasmSources: [
      'https://github.com/nmrugg/stockfish.js/releases/download/v19.0.1/',
      'https://cdn.jsdelivr.net/npm/stockfish@19.0.1/bin/',
    ],
    wasmJs: 'stockfish-19-lite-single.js',
    wasmBin: 'stockfish-19-lite-single.wasm',
    presets: {
      bullet: { label: 'Bullet', movetime: 100, probeTime: 50, multipv: 4, multipvWasm: 4, specDeep: 6, moveDelay: [120, 350] },
      blitz: { label: 'Blitz', movetime: 300, probeTime: 120, multipv: 6, multipvWasm: 6, specDeep: 8, moveDelay: [250, 800] },
      rapid: { label: 'Rapid', movetime: 800, probeTime: 250, multipv: 12, multipvWasm: 6, specDeep: 12, moveDelay: [400, 1400] },
    },
    defaultSpeed: 'blitz',
    tier: { t1: 30, t2: 100, t3: 150 },
    bridgePingMs: 8000,
    bridgeAlivePingMs: 30000,
    clockPollMs: 200,
    clockSettleMs: 350,
    clockTickMs: 1300,
    premoveMissDelayMs: 900,
    speculate: true,
    specWindow: 160,
    specBudgetMs: 25000,
    specLowFrac: 0.6,
    showPct: true,
    specWasmCands: 2,
    oppElo: null,
    arrow: { w: 0.2, head: 0.55, bodyOpacity: 0.85 },
    autoEloMargin: 0,
    bookMaxLoss: 80,
  };

  const DEFAULTS = {
    v: 2,
    elo: 3000,
    style: 'bot',
    speed: 'blitz',
    autoSpeed: false,
    premove: false,
    autoMove: false,
    autoElo: false,
    ppos: null,
    tiers: { t1: true, t2: true, t3: true },
    colors: { c1: '#3b82f6', c2: '#a855f7', c3: '#ef4444' },
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
        const e = new Error('GM_xmlhttpRequest is not available'); e.kind = 'net'; reject(e); return;
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
          onerror: () => fail('connection failed'),
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
  const PROMO_NAME = { n: 'knight', r: 'rook', b: 'bishop', q: 'queen' };
  const LITE = (() => {
    try { return matchMedia('(pointer: coarse)').matches; } catch (e) { return false; }
  })();
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

  function nearStart(bd) {
    const sb = boardFromPlacement(START_PLACEMENT);
    let diff = 0;
    for (let i = 0; i < 64; i++) {
      if (bd[i] === sb[i]) continue;
      diff++;
      if ((bd[i] && !isWhitePc(bd[i])) || (sb[i] && !isWhitePc(sb[i]))) return false;
    }
    return diff <= 2;
  }

  function boardFromPlacement(pl) {
    const bd = new Array(64).fill('');
    pl.split('/').forEach((row, i) => {
      let f = 0;
      for (const ch of row) {
        if (ch >= '1' && ch <= '8') f += +ch;
        else bd[(7 - i) * 8 + f++] = ch;
      }
    });
    return bd;
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
        if (r === 0 || r === 7) return 'pawn on rank 1/8';
      }
    }
    if (wk !== 1 || bk !== 1) return 'missing king (white ' + wk + ', black ' + bk + ')';
    if (wp > 8 || bp > 8) return 'too many pawns';
    if (wt > 16 || bt > 16) return 'too many pieces';
    const a = findKing(bd, true), b = findKing(bd, false);
    if (Math.abs((a & 7) - (b & 7)) <= 1 && Math.abs((a >> 3) - (b >> 3)) <= 1) return 'kings are adjacent';
    const white = turn === 'w';
    if (isAttacked(bd, findKing(bd, !white), white)) return "opponent's king is in check (wrong side to move?)";
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
      return { turn: null, src: '', weak: false, note: clocks.length ? 'found ' + clocks.length + ' clock(s), colors unclear' : 'no clocks' };
    }
    for (const col of ['w', 'b']) {
      const sec = parseClockText(by[col].text);
      const m = mem[col] || (mem[col] = { sec: null, dec: 0 });
      if (sec != null) { if (m.sec != null && sec < m.sec) m.dec = now; m.sec = sec; }
    }
    const note = ['w', 'b'].map((col) => col + ':' + (by[col].pos || '?') + ':' + (by[col].turnClass ? 'ON' : 'off')).join(' | ');
    const on = ['w', 'b'].filter((col) => by[col].turnClass);
    if (on.length === 1) return { turn: on[0], src: 'clock (class)', weak: false, note };
    const run = ['w', 'b'].filter((col) => mem[col].dec && now - mem[col].dec <= tickMs);
    if (run.length === 1) return { turn: run[0], src: 'clock (ticking)', weak: true, note };
    return { turn: null, src: '', weak: false, note };
  }

  function arbitrateTurn(ck, boardTurn, boardSrc, st, now, settleMs) {
    if (!ck || !ck.turn) { st.since = 0; return { turn: boardTurn || null, src: boardTurn ? boardSrc : '', pending: false }; }
    if (!boardTurn || boardTurn === ck.turn) { st.since = 0; return { turn: ck.turn, src: ck.src, pending: false }; }
    if (ck.weak) { st.since = 0; return { turn: boardTurn, src: boardSrc + ' (ticking clock disagrees, ignored)', pending: false }; }
    if (!st.since) st.since = now;
    if (now - st.since < settleMs) return { turn: null, src: 'clock differs from board, waiting to sync', pending: true };
    return { turn: ck.turn, src: ck.src + ' (differs from board)', pending: false };
  }

  const scoreOf = (l) => (l.mate != null ? (l.mate > 0 ? 100000 - l.mate : -100000 - l.mate) : l.cp);

  function fmtEval(score, mate) {
    if (mate != null) return (mate > 0 ? 'M' : '-M') + Math.abs(mate);
    const v = score / 100;
    return (v > 0 ? '+' : '') + v.toFixed(2);
  }

  const winPct = (cp) => 50 + 50 * (2 / (1 + Math.exp(-0.00368208 * cp)) - 1);

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

  const BOOK_LINES = [
    ['Ruy Lopez', 8, 'e2e4 e7e5 g1f3 b8c6 f1b5 a7a6 b5a4 g8f6 e1g1 f8e7 f1e1 b7b5 a4b3 d7d6 c2c3 e8g8'],
    ['Italian Game', 8, 'e2e4 e7e5 g1f3 b8c6 f1c4 f8c5 c2c3 g8f6 d2d3 d7d6 e1g1 e8g8'],
    ['Evans Gambit', 3, 'e2e4 e7e5 g1f3 b8c6 f1c4 f8c5 b2b4 c5b4 c2c3 b4a5 d2d4 e5d4 e1g1 d7d6'],
    ['Scotch Game', 3, 'e2e4 e7e5 g1f3 b8c6 d2d4 e5d4 f3d4 f8c5 d4b3 c5b6'],
    ["King's Gambit", 2, 'e2e4 e7e5 f2f4 e5f4 g1f3 g7g5 h2h4 g5g4 f3e5 g8f6'],
    ['Vienna Gambit', 2, 'e2e4 e7e5 b1c3 g8f6 f2f4 d7d5 f4e5 f6e4 g1f3 f8e7 d2d4 e8g8'],
    ['Danish Gambit', 2, 'e2e4 e7e5 d2d4 e5d4 c2c3 d4c3 f1c4 c3b2 c1b2 d7d5 c4d5 g8f6'],
    ['Petroff', 3, 'e2e4 e7e5 g1f3 g8f6 f3e5 d7d6 e5f3 f6e4 d2d4 d7d5 f1d3 f8e7 e1g1 b8c6'],
    ['Sicilian Najdorf', 5, 'e2e4 c7c5 g1f3 d7d6 d2d4 c5d4 f3d4 g8f6 b1c3 a7a6 c1e3 e7e5 d4b3 c8e6'],
    ['Sicilian Dragon', 2, 'e2e4 c7c5 g1f3 d7d6 d2d4 c5d4 f3d4 g8f6 b1c3 g7g6 c1e3 f8g7 f2f3 b8c6 d1d2 e8g8'],
    ['Smith-Morra Gambit', 3, 'e2e4 c7c5 d2d4 c5d4 c2c3 d4c3 b1c3 b8c6 g1f3 d7d6 f1c4 e7e6 e1g1 g8f6'],
    ['Sicilian Alapin', 2, 'e2e4 c7c5 c2c3 g8f6 e4e5 f6d5 d2d4 c5d4 g1f3 b8c6 c3d4 d7d6'],
    ['French Defense', 3, 'e2e4 e7e6 d2d4 d7d5 b1c3 g8f6 c1g5 f8e7 e4e5 f6d7 g5e7 d8e7 f2f4 e8g8'],
    ['French Advance', 2, 'e2e4 e7e6 d2d4 d7d5 e4e5 c7c5 c2c3 b8c6 g1f3 d8b6 a2a3 c5c4'],
    ['Caro-Kann', 3, 'e2e4 c7c6 d2d4 d7d5 b1c3 d5e4 c3e4 c8f5 e4g3 f5g6 h2h4 h7h6 g1f3 b8d7 h4h5 g6h7 f1d3 h7d3 d1d3 e7e6'],
    ['Caro-Kann Advance', 2, 'e2e4 c7c6 d2d4 d7d5 e4e5 c8f5 g1f3 e7e6 f1e2 c6c5 e1g1 b8c6'],
    ['Scandinavian', 2, 'e2e4 d7d5 e4d5 d8d5 b1c3 d5a5 d2d4 g8f6 g1f3 c7c6 f1c4 c8f5'],
    ['Pirc', 1, 'e2e4 d7d6 d2d4 g8f6 b1c3 g7g6 g1f3 f8g7 f1e2 e8g8 e1g1 c7c6'],
    ["Queen's Gambit Declined", 4, 'd2d4 d7d5 c2c4 e7e6 b1c3 g8f6 c1g5 f8e7 e2e3 e8g8 g1f3 b8d7'],
    ["Queen's Gambit Accepted", 2, 'd2d4 d7d5 c2c4 d5c4 g1f3 g8f6 e2e3 e7e6 f1c4 c7c5 e1g1 a7a6'],
    ['Slav', 3, 'd2d4 d7d5 c2c4 c7c6 g1f3 g8f6 b1c3 d5c4 a2a4 c8f5 e2e3 e7e6 f1c4 f8b4'],
    ['Nimzo-Indian', 4, 'd2d4 g8f6 c2c4 e7e6 b1c3 f8b4 e2e3 e8g8 f1d3 d7d5 g1f3 c7c5'],
    ["King's Indian", 3, 'd2d4 g8f6 c2c4 g7g6 b1c3 f8g7 e2e4 d7d6 g1f3 e8g8 f1e2 e7e5'],
    ['London', 2, 'd2d4 d7d5 c1f4 g8f6 e2e3 c7c5 c2c3 b8c6 b1d2 e7e6 g1f3 f8d6'],
    ['Budapest Gambit', 1, 'd2d4 g8f6 c2c4 e7e5 d4e5 f6g4 c1f4 b8c6 g1f3 f8b4 b1d2 d8e7'],
    ['Albin Countergambit', 1, 'd2d4 d7d5 c2c4 e7e5 d4e5 d5d4 g1f3 b8c6 g2g3 c8e6'],
    ['English Opening', 3, 'c2c4 e7e5 b1c3 g8f6 g1f3 b8c6 g2g3 d7d5 c4d5 f6d5 f1g2 d5b6'],
    ['Reti', 3, 'g1f3 d7d5 g2g3 g8f6 f1g2 e7e6 e1g1 f8e7 d2d4 e8g8'],
  ];
  const BOOK = new Map();
  (function buildBook() {
    for (const line of BOOK_LINES) {
      const name = line[0], w = line[1];
      let bd = boardFromPlacement(START_PLACEMENT), turn = 'w';
      for (const uci of line[2].split(' ')) {
        const pc = bd[sqIdx(uci.slice(0, 2))];
        if (!pc || isWhitePc(pc) !== (turn === 'w')) break;
        const key = fenPlacement(bd) + ' ' + turn;
        let m = BOOK.get(key);
        if (!m) { m = new Map(); BOOK.set(key, m); }
        const e = m.get(uci);
        if (!e) m.set(uci, { w, name, top: w });
        else { e.w += w; if (w > e.top) { e.top = w; e.name = name; } }
        const r = applyMove(bd, uci);
        if (!r) break;
        bd = r.bd; turn = turn === 'w' ? 'b' : 'w';
      }
    }
  })();
  const bookLookup = (bd, turn) => BOOK.get(fenPlacement(bd) + ' ' + turn) || null;

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
    if (m.castle) { b += 35; tags.push('castling'); }
    if ((m.t === 'n' || m.t === 'b') && m.fromRank === 0 && ctx.opening) { b += 30; tags.push('develops a piece'); }
    if (m.t === 'p' && (m.fromFile === 3 || m.fromFile === 4) && ctx.opening) { b += 25; tags.push('center pawn'); }
    if (m.t === 'p' && (m.fromFile === 2 || m.fromFile === 5) && ctx.opening) b += 8;
    if (m.capture && m.capVal >= m.movedVal - 50) { b += 22; tags.push(m.capVal > m.movedVal ? 'wins material' : 'trade'); }
    const ol = ctx.oppLast;
    if (ol && m.capture && m.to === ol.to) { b += 28; tags.push('recapture'); }
    if ((m.t === 'n' || m.t === 'b') && Math.abs(m.toFile - 3.5) <= 1.5 && Math.abs(m.toRank - 3.5) <= 1.5) b += 10;
    if (m.check) { b += 8; tags.push('check'); }
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

    if (m.t === 'q' && ctx.opening) { b += 40 + (m.toRank >= 3 ? 10 : 0); tags.push('early queen'); }
    if (m.t === 'p' && (m.toFile === 0 || m.toFile === 7) && (m.fromFile === 0 || m.fromFile === 7)) {
      b += 30 + (Math.abs(m.toRank - m.fromRank) === 2 ? 8 : 0); tags.push('edge pawn');
    }
    const lm = ctx.lastMine;
    if (m.t === 'n' && lm && lm.piece === 'n' && lm.to === m.from && lm.from === m.to) { b += 45; tags.push('knight shuffle'); }
    if (m.t === 'k' && !m.castle && ctx.opening && !m.capture) { b += 30; tags.push('Bongcloud'); }
    const canCastle = ctx.white ? /[KQ]/.test(ctx.rights) : /[kq]/.test(ctx.rights);
    if (canCastle && ctx.opening) {
      if (m.castle) b -= 10;
      else { b += 12; tags.push('delayed castling'); }
    }

    const ol = ctx.oppLast;
    if (ol && m.from === mirrorSq(ol.from) && m.to === mirrorSq(ol.to)) { b += 40; tags.push('mirrors the opponent'); }

    const before = new Set(ctx.attackedBefore);
    let bait = 0;
    for (const a of attackedPieces(m.r.bd, ctx.white)) {
      const isNew = a.i === m.to || !before.has(a.i);
      if (!isNew) continue;
      if (a.minAtt < VAL[a.t] || !a.defended) bait = Math.max(bait, 30 + (a.byPawn ? 10 : 0));
      else bait = Math.max(bait, 12);
    }
    if (bait) { b += bait; tags.push('hangs a piece as bait'); }

    if (winning) {
      if (isMate) b -= 90;
      else if (mateAvail) { b += 35; tags.push('skips mate on purpose'); }
      if (m.r.promo && m.r.promo !== 'q') { b += 55; tags.push('promotes to ' + PROMO_NAME[m.r.promo]); }
      if (m.capture && m.capVal <= 100 && !isMate) { b += 18; tags.push('grabs a pawn first'); }
      if ((m.t === 'k' || m.t === 'r') && !m.capture && !m.check) { b += 12; tags.push('shuffles around'); }
      if (m.toRank < m.fromRank && !m.capture) { b += 8; tags.push('steps back'); }
      if (m.check && !isMate) { b += 10; tags.push('pointless check'); }
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

    const bookPick = () => {
      const bk = ctx.book;
      if (!bk || !bk.size) return null;
      if (rnd() >= (ctx.bookProb == null ? 0.9 : ctx.bookProb)) return null;
      const maxLoss = CFG.bookMaxLoss;
      const cands = cs.filter((c) => bk.has(c.move) && c.loss <= maxLoss && c.score > -90000 && !(best >= 200 && c.score < 100));
      if (!cands.length) return null;
      const p = sampleWeighted(cands, (c) => Math.log(bk.get(c.move).w) - c.loss / 50, 1, rnd);
      const e = bk.get(p.move);
      const t = ['opening: ' + e.name];
      if (p.loss >= 30) t.push('gambit (small risk)');
      return { p, tags: t };
    };

    const humanPick = () => {
      const budget = Math.max(base.loss, 45);
      const cands = cs.filter((c) => (c.loss <= budget && safe(c)) || c === base);
      const ev = new Map();
      const evOf = (c) => { if (!ev.has(c)) ev.set(c, humanEval(c, ctx)); return ev.get(c); };
      const wt = (c) => evOf(c).b - 1.0 * c.loss + (c === base ? 10 : 0);
      const slipPool = ctx.opening ? [] : cs.filter((c) => c.loss >= 20 && c.loss <= 70 && safe(c));
      const slip = slipPool.length > 0 && rnd() < (ctx.humanSlip == null ? 0.08 : ctx.humanSlip);
      const pool = slip ? slipPool : cands;
      const p = sampleWeighted(pool, slip ? (c) => evOf(c).b - 0.3 * c.loss : wt, 18, rnd);
      const t = evOf(p).tags.slice();
      if (p.loss >= 20) t.push('slight inaccuracy');
      return { p, tags: t };
    };

    if (ctx.style === 'human') {
      const bk = bookPick();
      const h = bk || humanPick();
      pick = h.p; tags = h.tags;
    } else if (ctx.style === 'troll') {
      const winning = best >= 300;
      const floor = Math.max(250, Math.min(best - 400, 600));
      const cands = winning
        ? cs.filter((c) => c.score >= floor)
        : cs.filter((c) => c.loss <= Math.max(base.loss, 90) && safe(c));
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
        note = 'No safe Troll move, using Human style instead';
      }
    }

    const styleGreen = ctx.style !== 'bot' && pick !== bestC && (trollWin || safe(pick));
    const tiers = { 1: styleGreen ? pick : bestC, 2: null, 3: null };
    const pickTier = pick === bestC || styleGreen ? 1 : tierOf(pick);
    if (styleGreen) tiers[2] = bestC;
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
    if (tiers[2] && tiers[3] && tiers[2] !== pick && tiers[3] !== pick && tiers[2] !== bestC && tiers[2].loss > tiers[3].loss) { const t = tiers[2]; tiers[2] = tiers[3]; tiers[3] = t; }
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
      try { j = JSON.parse(r.responseText); } catch (e) { const er = new Error('unexpected bridge reply'); er.kind = 'net'; throw er; }
      if (!j.ok) { const er = new Error(j.error || 'bridge engine problem'); er.kind = 'engine'; throw er; }
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
      try { j = JSON.parse(r.responseText); } catch (e) { const er = new Error('unexpected bridge reply'); er.kind = 'net'; throw er; }
      if (!j.ok) { const er = new Error(j.error || 'analysis failed'); er.kind = 'engine'; throw er; }
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
            const c = await caches.open('nebulachess-v1');
            const hit = await c.match(url);
            if (hit) return { data: type === 'text' ? await hit.text() : await hit.arrayBuffer(), url };
          }
        } catch (e) { }
        try {
          const r = await gmRequest({ url, responseType: type === 'text' ? 'text' : 'arraybuffer', timeout: 60000 });
          if (r.status !== 200) throw new Error('HTTP ' + r.status);
          const data = type === 'text' ? r.responseText : r.response;
          if (!data || (type !== 'text' && !data.byteLength)) throw new Error('empty file');
          try {
            if (typeof caches !== 'undefined') {
              const c = await caches.open('nebulachess-v1');
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
      } catch (e) { throw this._fail('download', 'download failed: ' + e.message); }
      let w;
      try {
        const jsUrl = URL.createObjectURL(new Blob([js], { type: 'text/javascript' }));
        const binUrl = URL.createObjectURL(new Blob([bin], { type: 'application/wasm' }));
        w = new Worker(jsUrl + '#' + encodeURIComponent(binUrl));
      } catch (e) { throw this._fail('blocked', 'worker blocked: ' + (e && e.message || e)); }
      this.worker = w;
      w.onmessage = (ev) => {
        if (typeof ev.data !== 'string') return;
        const s = this.sink;
        if (s) s.line(ev.data);
      };
      w.onerror = (ev) => {
        const kind = this.state === 'ready' ? 'crash' : 'blocked';
        this._fail(kind, kind === 'blocked' ? 'worker blocked / failed to run' : 'worker crashed');
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
        throw this._fail(this.failure || 'blocked', 'worker not responding: ' + e.message);
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
        if (e.message === 'timeout') { this._send('stop'); throw this._fail('crash', 'WASM engine returned no bestmove'); }
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
  const TIER_COLOR = { 0: '#ef4444', 1: '#3b82f6', 2: '#a855f7', 3: '#ef4444' };
  const HEX_RE = /^#[0-9a-f]{6}$/i;
  function applyColors(c) {
    if (!c) return;
    if (HEX_RE.test(c.c1)) TIER_COLOR[1] = c.c1;
    if (HEX_RE.test(c.c2)) TIER_COLOR[2] = c.c2;
    if (HEX_RE.test(c.c3)) { TIER_COLOR[3] = c.c3; TIER_COLOR[0] = c.c3; }
  }

  const CSS = `
:host{all:initial}
*,*::before,*::after{box-sizing:border-box}
::selection{background:rgba(96,130,246,.45);color:#fff}
button,summary,label{-webkit-tap-highlight-color:transparent}
button:focus-visible,summary:focus-visible,input:focus-visible{outline:2px solid rgba(96,165,250,.8);outline-offset:2px}
.root{--bg:#0a0e1f;--surface:#111831;--surface2:#18224a;--text:#e8efff;--muted:#8d9bc9;
  --accent:#3b82f6;--border:#2b3763;
  --ok:#34d399;--warn:#fbbf24;--err:#f87171;
  font:13px/1.4 system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;color:var(--text);-webkit-text-size-adjust:100%}
.arrows{position:fixed;pointer-events:none;z-index:2147483640;overflow:visible}
.fab{position:fixed;width:48px;height:48px;border-radius:16px;
  background:#1e3a8a;color:#dbeafe;
  border:1.5px solid rgba(96,165,250,.8);display:grid;place-items:center;font-size:24px;line-height:1;
  
  cursor:grab;touch-action:none;user-select:none;-webkit-user-select:none;z-index:2147483647;pointer-events:auto}
.fab:active{cursor:grabbing}
.panel{--pw:min(264px,calc(100vw - 12px));position:fixed;width:var(--pw);
  height:min(calc(var(--pw) * 1.3334),calc(100vh - 12px));height:min(calc(var(--pw) * 1.3334),calc(100dvh - 12px));
  display:flex;flex-direction:column;overflow:hidden;
  background:#0a0e1f;border:1px solid var(--border);
  border-radius:16px;z-index:2147483647;pointer-events:auto}
.hd{flex:none;position:relative;z-index:1;display:flex;align-items:center;gap:6px;padding:7px 8px 6px 10px;cursor:grab;touch-action:none;user-select:none;-webkit-user-select:none;
  background:#121a3a;border-bottom:1px solid var(--border);border-radius:15px 15px 0 0;}
.hd:active{cursor:grabbing}
.grip{width:12px;height:18px;flex:none;box-sizing:border-box;border-left:2px solid #8fa3d8;border-right:2px solid #8fa3d8}
.title{flex:1;font:800 13px/1.2 system-ui,sans-serif;letter-spacing:.2em;text-transform:uppercase;
  color:#dbeafe;}
.ibtn{width:28px;height:28px;border-radius:9px;border:1px solid var(--border);background:var(--surface);color:var(--text);
  font:600 18px/1 system-ui,sans-serif;display:grid;place-items:center;cursor:pointer;padding:0;}
.ibtn:active{background:rgba(79,110,246,.34);border-color:rgba(139,92,246,.6);}
.body{flex:1;min-height:0;overflow-y:auto;overflow-x:hidden;overscroll-behavior:contain;scrollbar-width:thin;scrollbar-color:rgba(99,130,246,.55) transparent;
  padding:8px 10px 10px;display:flex;flex-direction:column;gap:8px}
.body>*{flex:none}
.body::-webkit-scrollbar,pre::-webkit-scrollbar{width:5px;height:5px}
.body::-webkit-scrollbar-thumb,pre::-webkit-scrollbar-thumb{background:rgba(99,130,246,.5);border-radius:3px}
.body::-webkit-scrollbar-track,pre::-webkit-scrollbar-track{background:transparent}
.card{background:var(--surface);border:1px solid var(--border);border-radius:14px;padding:6px 11px;min-height:54px;}
.lbl{font-size:10.5px;color:var(--muted);letter-spacing:.08em;text-transform:uppercase}
.move{font:700 21px/1.2 ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;margin-top:2px;word-break:break-word;color:#f1f5ff;}
.sub{font-size:11.5px;color:var(--muted);margin-top:2px;white-space:pre-line}
.lrow{display:flex;justify-content:space-between;align-items:center;gap:6px;min-height:22px}
.lact{display:flex;align-items:center;gap:7px}
.val{font-weight:700;font-size:12px;color:#dbeafe;}
.lnk{border:0;background:transparent;color:#9db4ff;font:600 10.5px system-ui,sans-serif;padding:3px 0;cursor:pointer;text-decoration:underline;text-underline-offset:2px}
.lnk:active{color:#fff}
.hint{margin-top:6px;padding:0 2px;font-size:10.5px;line-height:1.45;color:var(--muted);white-space:pre-line}
input[type=range]{-webkit-appearance:none;appearance:none;width:100%;height:26px;margin:0;background:transparent;cursor:pointer}
input[type=range]:disabled{opacity:.4;cursor:not-allowed}
input[type=range]::-webkit-slider-runnable-track{height:6px;border-radius:999px;
  background:#2b3a78;}
input[type=range]::-webkit-slider-thumb{-webkit-appearance:none;appearance:none;width:20px;height:20px;margin-top:-7px;border-radius:50%;
  border:2px solid #eef4ff;background:#6aa0ff;}
input[type=range]::-moz-range-track{height:6px;border-radius:999px;
  background:#2b3a78;}
input[type=range]::-moz-range-thumb{width:18px;height:18px;border-radius:50%;border:2px solid #eef4ff;
  background:#6aa0ff;}
.seg{display:grid;grid-template-columns:repeat(3,1fr);gap:4px;background:var(--surface);border:1px solid var(--border);padding:4px;border-radius:13px}
.seg.lock{opacity:.5;pointer-events:none}
.seg button{border:0;background:transparent;color:var(--text);padding:5px 4px;min-height:30px;border-radius:9px;font:600 12.5px system-ui,sans-serif;cursor:pointer}
.seg button:active{background:rgba(79,110,246,.22)}
.seg button.on{background:var(--accent);color:#fff;}
.chips{display:grid;grid-template-columns:repeat(3,1fr);gap:5px}
.chip{display:flex;flex-direction:column;gap:6px;padding:6px 7px;background:var(--surface);border:1px solid var(--border);border-radius:11px}
.chip:has(input[type=checkbox]:checked){border-color:rgba(120,140,250,.6);}
.chip input[type=color]{-webkit-appearance:none;appearance:none;width:100%;height:22px;padding:0;border:1.5px solid rgba(255,255,255,.5);border-radius:8px;background:none;cursor:pointer}
.chip input[type=color]::-webkit-color-swatch-wrapper{padding:0}
.chip input[type=color]::-webkit-color-swatch{border:0;border-radius:6px}
.chip input[type=color]::-moz-color-swatch{border:0;border-radius:6px}
.ck{display:flex;align-items:center;gap:6px;font-size:11.5px;cursor:pointer}
.ck input{width:16px;height:16px;accent-color:var(--accent);margin:0}
.status{display:flex;gap:7px;align-items:flex-start;font-size:11.5px}
.led{width:9px;height:9px;border-radius:50%;margin-top:5px;flex:none;background:var(--muted)}
.led.ok{background:var(--ok);}.led.warn{background:var(--warn);}
.led.err{background:var(--err);}
details{background:var(--surface);border:1px solid var(--border);border-radius:12px;padding:0 12px}
details[open]{padding-bottom:10px}
summary{cursor:pointer;font-size:12px;color:var(--muted);padding:6px 0}
details[open] summary{color:var(--text)}
pre{margin:8px 0 0;padding:8px 10px;background:rgba(4,5,13,.7);border:1px solid rgba(99,130,246,.2);border-radius:9px;
  font:10.5px/1.4 ui-monospace,Menlo,Consolas,monospace;white-space:pre-wrap;word-break:break-all;max-height:160px;overflow:auto;color:#c5d0f0;
  scrollbar-width:thin;scrollbar-color:rgba(99,130,246,.55) transparent}
.mini{display:flex;gap:6px;margin-top:8px}
.mini button{flex:1;border:1px solid var(--border);border-radius:9px;background:rgba(59,100,246,.15);color:var(--text);padding:8px;min-height:34px;font:600 12px system-ui,sans-serif;cursor:pointer}
.mini button:active{background:rgba(79,110,246,.36);}
.tg{display:flex;gap:6px;align-items:center}
.tbtn{flex:1;display:flex;justify-content:space-between;align-items:center;border:1px solid var(--border);background:var(--surface);color:var(--text);
  padding:6px 10px;min-height:32px;border-radius:11px;font:600 12.5px system-ui,sans-serif;cursor:pointer}
.tbtn:active{background:rgba(79,110,246,.22)}
.tbtn .sw{width:38px;height:22px;border-radius:11px;background:rgba(141,155,201,.22);
  position:relative;flex:none;}
.tbtn .sw::after{content:'';position:absolute;top:3px;left:3px;width:16px;height:16px;border-radius:50%;background:#c5d0f0;}
.tbtn.on{border-color:rgba(120,140,250,.65);}
.tbtn.on .sw{background:var(--accent);}
.tbtn.on .sw::after{transform:translateX(16px);background:#fff;}
`;

  function createUI(S, handlers) {
    const host = document.createElement('div');
    host.setAttribute('data-nebulachess', '1');
    host.style.cssText = 'position:fixed;top:0;left:0;width:0;height:0;z-index:2147483647;';
    const root = host.attachShadow({ mode: 'open' });
    const chip = (t, c, label) => '<div class="chip"><input type="color" data-color="' + c + '" title="Pick color">' +
      '<label class="ck"><input type="checkbox" data-tier="' + t + '"><span>' + label + '</span></label></div>';
    root.innerHTML = '<style>' + CSS + '</style>' +
      '<div class="root">' +
      '<svg class="arrows" xmlns="' + NS_SVG + '"></svg>' +
      '<div class="fab" part="fab" title="' + CFG.name + '">♞︎</div>' +
      '<div class="panel" style="display:none">' +
        '<div class="hd"><span class="grip" title="Drag panel"></span><div class="title">' + CFG.name + '</div>' +
          '<button class="ibtn" data-act="min" title="Minimize">−</button>' +
          '<button class="ibtn" data-act="close" title="Close until reload">×</button></div>' +
        '<div class="body">' +
          '<div class="card"><div class="lbl">Suggestion</div><div class="move" data-r="move">—</div><div class="sub" data-r="sub">Waiting for the board…</div></div>' +
          '<div><div class="lrow"><span class="lbl">Engine Elo</span><span class="val" data-r="elo">3000+</span></div>' +
            '<input type="range" min="100" max="3000" step="50" data-r="slider">' +
            '<div class="hint" data-tip="elo"></div>' +
            '<div class="tg" style="margin-top:8px"><button class="tbtn" data-autoelo><span>Auto Elo</span><span class="sw"></span></button></div>' +
            '<div class="hint" data-tip="autoelo"></div></div>' +
          '<div><div class="lrow"><span class="lbl">Game speed</span><span class="val" data-r="speedval"></span></div>' +
            '<div class="seg" data-r="speedseg"><button data-speed="bullet">Bullet</button><button data-speed="blitz">Blitz</button><button data-speed="rapid">Rapid</button></div>' +
            '<div class="hint" data-tip="speed"></div>' +
            '<div class="tg" style="margin-top:8px"><button class="tbtn" data-autospeed><span>Auto speed</span><span class="sw"></span></button></div>' +
            '<div class="hint" data-tip="autospeed"></div></div>' +
          '<div><div class="lrow"><span class="lbl">Suggestion style</span></div>' +
            '<div class="seg"><button data-style="bot">Bot</button><button data-style="human">Human</button><button data-style="troll">Troll</button></div>' +
            '<div class="hint" data-tip="style"></div></div>' +
          '<div><div class="tg"><button class="tbtn" data-premove><span>Premove</span><span class="sw"></span></button></div>' +
            '<div class="hint" data-tip="premove"></div></div>' +
          '<div><div class="tg"><button class="tbtn" data-automove><span>Auto move</span><span class="sw"></span></button></div>' +
            '<div class="hint" data-tip="automove"></div></div>' +
          '<div><div class="lrow"><span class="lbl">Arrows</span><span class="lact"><button class="lnk" data-act="rescolors">Reset colors</button></span></div>' +
            '<div class="chips">' + chip('t1', 'c1', 'Best') + chip('t2', 'c2', 'Good') + chip('t3', 'c3', 'Weak') + '</div>' +
            '<div class="hint" data-tip="arrows"></div></div>' +
          '<div class="status"><span class="led" data-r="led"></span><span data-r="status">Starting…</span></div>' +
          '<details><summary>Debug</summary><pre data-r="debug"></pre>' +
            '<div class="mini"><button data-act="copyfen">Copy FEN</button><button data-act="copylog">Copy log</button></div></details>' +
        '</div></div></div>';

    const $ = (sel) => root.querySelector(sel);
    const el = {
      arrows: $('.arrows'), fab: $('.fab'), panel: $('.panel'), hd: $('.hd'),
      move: $('[data-r=move]'), sub: $('[data-r=sub]'), elo: $('[data-r=elo]'), slider: $('[data-r=slider]'),
      speedval: $('[data-r=speedval]'), speedseg: $('[data-r=speedseg]'), led: $('[data-r=led]'),
      status: $('[data-r=status]'), debug: $('[data-r=debug]'),
      premovebtn: $('[data-premove]'), automovebtn: $('[data-automove]'), autobtn: $('[data-autoelo]'), autospeedbtn: $('[data-autospeed]'),
    };
    const FAB = 48;
    let open = false;
    const UIstate = { x: 0, y: 0 };
    const PanelState = { x: null, y: null };
    const shown = { x: 0, y: 0 };

    function defaultPos() { return { x: Math.max(6, window.innerWidth - FAB - 10), y: Math.round(window.innerHeight * 0.45) }; }
    const saved = S.settings.pos;
    Object.assign(UIstate, saved && isFinite(saved.x) && isFinite(saved.y) ? saved : defaultPos());
    const savedP = S.settings.ppos;
    if (savedP && isFinite(savedP.x) && isFinite(savedP.y)) { PanelState.x = savedP.x; PanelState.y = savedP.y; }

    function clampPanel(x, y) {
      const vw = window.innerWidth, vh = window.innerHeight;
      const pw = el.panel.offsetWidth || 264, ph = el.panel.offsetHeight || 352;
      return [clamp(x, 6, Math.max(6, vw - pw - 6)), clamp(y, 6, Math.max(6, vh - ph - 6))];
    }

    function place() {
      const vw = window.innerWidth, vh = window.innerHeight;
      UIstate.x = clamp(UIstate.x, 6, Math.max(6, vw - FAB - 6));
      UIstate.y = clamp(UIstate.y, 6, Math.max(6, vh - FAB - 6));
      el.fab.style.left = UIstate.x + 'px';
      el.fab.style.top = UIstate.y + 'px';
      if (open) {
        const p = clampPanel(PanelState.x == null ? UIstate.x : PanelState.x, PanelState.y == null ? UIstate.y : PanelState.y);
        shown.x = p[0]; shown.y = p[1];
        el.panel.style.left = p[0] + 'px';
        el.panel.style.top = p[1] + 'px';
      }
    }

    function savePos() { S.settings.pos = { x: UIstate.x, y: UIstate.y }; handlers.save(); }
    function savePanelPos() { PanelState.x = shown.x; PanelState.y = shown.y; S.settings.ppos = { x: shown.x, y: shown.y }; handlers.save(); }

    function guardOpen(ms) {
      const swallow = (e) => { e.stopImmediatePropagation(); e.preventDefault(); };
      const evs = ['click', 'mousedown', 'mouseup', 'dblclick'];
      el.panel.style.pointerEvents = 'none';
      evs.forEach((t) => window.addEventListener(t, swallow, true));
      setTimeout(() => {
        el.panel.style.pointerEvents = '';
        evs.forEach((t) => window.removeEventListener(t, swallow, true));
      }, ms);
    }

    function setOpen(v) {
      open = v;
      if (v) guardOpen(450);
      el.panel.style.display = v ? 'flex' : 'none';
      el.fab.style.display = v ? 'none' : 'grid';
      place();
      if (v) { renderDebug(); place(); }
    }

    function drag(handle, getXY, setXY, onTap, onEnd) {
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
        if (moved) { if (onEnd) onEnd(); } else if (onTap) onTap();
      };
      handle.addEventListener('pointerup', end);
      handle.addEventListener('pointercancel', end);
    }
    drag(el.fab, () => [UIstate.x, UIstate.y], (x, y) => { UIstate.x = x; UIstate.y = y; place(); }, () => setOpen(true), savePos);
    drag(el.hd, () => [shown.x, shown.y], (x, y) => { const p = clampPanel(x, y); PanelState.x = p[0]; PanelState.y = p[1]; place(); }, null, savePanelPos);

    root.addEventListener('click', (e) => {
      const b = e.target.closest && e.target.closest('[data-act]');
      if (!b) return;
      const a = b.getAttribute('data-act');
      if (a === 'min') setOpen(false);
      else if (a === 'close') handlers.close();
      else if (a === 'copyfen') copyText(S.dbg.fen || '');
      else if (a === 'copylog') copyText(logBuf.join('\n'));
      else if (a === 'rescolors') { S.settings.colors = Object.assign({}, DEFAULTS.colors); applyColors(S.settings.colors); renderSettings(); handlers.save(); handlers.redraw(); }
    });

    function copyText(t) {
      const done = () => dbg('copied ' + t.length + ' characters');
      try {
        if (navigator.clipboard && navigator.clipboard.writeText) { navigator.clipboard.writeText(t).then(done, () => fallback()); return; }
      } catch (e) { }
      fallback();
      function fallback() {
        try {
          const ta = document.createElement('textarea');
          ta.value = t; ta.style.cssText = 'position:fixed;opacity:0;top:0;left:0';
          document.body.appendChild(ta); ta.select(); document.execCommand('copy'); ta.remove(); done();
        } catch (e) { dbg('copy failed'); }
      }
    }

    const STYLE_TIP = "Bot: always Stockfish's best move.\nHuman: plays like a strong person, with real openings and rare small slips, scaled by your Elo.\nTroll: still-good moves with attitude: early queen, mirroring you, skipping mate, underpromotions.";
    function eloText(v) { return v >= 3000 ? '3000+ (full)' : '~' + v; }
    const speedLabel = (k) => (CFG.presets[k] || CFG.presets[CFG.defaultSpeed]).label;
    const setTip = (k, text) => {
      const t = root.querySelector('[data-tip="' + k + '"]');
      if (t && t.textContent !== text) t.textContent = text;
    };
    function renderSettings() {
      const auto = !!S.settings.autoElo, detected = !!S.autoElo, eff = handlers.elo();
      const aSpd = !!S.settings.autoSpeed, spd = handlers.speed();
      const lo = S.uciMin || 1320;
      el.slider.value = S.settings.elo;
      el.slider.disabled = auto;
      el.autobtn.classList.toggle('on', auto);
      el.elo.textContent = (auto ? (detected ? 'auto ' : 'auto (slider) ') : '') + eloText(eff);
      el.autospeedbtn.classList.toggle('on', aSpd);
      el.speedseg.classList.toggle('lock', aSpd);
      el.speedval.textContent = aSpd ? 'auto ' + speedLabel(spd) : '';
      root.querySelectorAll('[data-speed]').forEach((b) => b.classList.toggle('on', b.getAttribute('data-speed') === spd));
      root.querySelectorAll('[data-style]').forEach((b) => b.classList.toggle('on', b.getAttribute('data-style') === S.settings.style));
      root.querySelectorAll('[data-tier]').forEach((c) => { c.checked = !!S.settings.tiers[c.getAttribute('data-tier')]; });
      root.querySelectorAll('[data-color]').forEach((c) => {
        const v = String(S.settings.colors[c.getAttribute('data-color')]).toLowerCase();
        if (c.value !== v) c.value = v;
      });
      el.premovebtn.classList.toggle('on', !!S.settings.premove);
      el.automovebtn.classList.toggle('on', !!S.settings.autoMove);

      setTip('elo', 'How strong the engine plays when picking your moves (100–3000). ' + (eff >= 3000
        ? 'Now: full strength, no limit.'
        : eff < lo
          ? 'Below ~' + lo + ' it imitates a weaker player with extra mistakes, so the number is only approximate.'
          : 'Now: limited to about ' + eff + ' Elo.'));
      setTip('autoelo', "Reads your rating and your opponent's rating from the page and uses the higher one. Locks the slider." +
        (auto ? (detected ? ' Now: ' + S.autoInfo + '.' : ' No ratings found yet, using the slider for now.') : ''));
      setTip('speed', 'How long the engine thinks per move. Longer is more accurate, but arrows show up later.\nBullet: 1–2 min games. Blitz: 3–9 min. Rapid: 10+ min or no clock.');
      setTip('autospeed', "Picks Bullet, Blitz or Rapid from the game's starting clock (no clock = Rapid). If the script loads mid-game it may pick a faster mode than the real one. Locks the speed buttons." +
        (aSpd ? (S.speedInfo ? ' Now: ' + S.speedInfo + '.' : ' Not detected yet, using the selected speed.') : ''));
      setTip('style', STYLE_TIP);
      setTip('premove', "While the opponent is thinking, predicts their likely moves and prepares your reply to each.\nOn: shows those arrows right away so you can premove. Off: " + (LITE
        ? "the engine rests during the opponent's turn, which keeps the phone cool and the page smooth. Arrows appear on your turn only."
        : "arrows appear on your turn only, but a correct prediction still shows instantly."));
      setTip('automove', 'Plays the suggested move for you by clicking the board on your turn. Bot style: fixed quick delay. Human and Troll styles: human-like play (varied thinking time, slightly off-center taps, uneven press times). If nothing moves, chess.com ignored the clicks, so play the arrow yourself.');
      setTip('arrows', 'Best (blue): the top move. Good (purple): a solid alternative. Weak (red): a weaker option or a possible mistake.\nTap a color to change it, tick the box to show that arrow. The % on an arrow is your winning chance after that move.');
    }

    el.slider.addEventListener('input', () => {
      S.settings.elo = +el.slider.value;
      el.elo.textContent = eloText(S.settings.elo);
      renderSettings();
      handlers.eloChanged();
    });
    el.slider.addEventListener('change', () => handlers.save());
    el.autobtn.addEventListener('click', () => {
      S.settings.autoElo = !S.settings.autoElo;
      handlers.autoEloChanged(); renderSettings(); handlers.save();
    });
    el.autospeedbtn.addEventListener('click', () => {
      S.settings.autoSpeed = !S.settings.autoSpeed;
      handlers.autoSpeedChanged(); renderSettings(); handlers.save();
    });
    root.querySelectorAll('[data-style]').forEach((b) => b.addEventListener('click', () => {
      S.settings.style = b.getAttribute('data-style');
      renderSettings(); handlers.save(); handlers.styleChanged();
    }));
    el.premovebtn.addEventListener('click', () => {
      S.settings.premove = !S.settings.premove;
      renderSettings(); handlers.save(); handlers.premoveChanged();
    });
    el.automovebtn.addEventListener('click', () => {
      S.settings.autoMove = !S.settings.autoMove;
      renderSettings(); handlers.save(); handlers.autoMoveChanged();
    });
    root.querySelectorAll('[data-speed]').forEach((b) => b.addEventListener('click', () => {
      if (S.settings.autoSpeed) return;
      S.settings.speed = b.getAttribute('data-speed');
      renderSettings(); handlers.save(); handlers.speedChanged();
    }));
    root.querySelectorAll('[data-tier]').forEach((c) => c.addEventListener('change', () => {
      S.settings.tiers[c.getAttribute('data-tier')] = c.checked;
      handlers.save(); handlers.redraw();
    }));
    root.querySelectorAll('[data-color]').forEach((c) => {
      c.addEventListener('input', () => {
        S.settings.colors[c.getAttribute('data-color')] = c.value;
        applyColors(S.settings.colors);
        handlers.redraw();
      });
      c.addEventListener('change', () => handlers.save());
    });

    function renderDebug() {
      if (!open) return;
      const d = S.dbg;
      const lines = [
        'page      : ' + (d.path || '-'),
        'board     : ' + (d.board || '-'),
        'pieces    : ' + (d.pieces == null ? '-' : d.pieces) + ' | flipped: ' + (d.flipped ? 'yes' : 'no') + ' (' + (d.flipSrc || '-') + ')',
        'turn      : ' + (d.turn || '?') + ' (' + (d.turnSrc || '-') + ') | you: ' + (d.me || '-'),
        'clock     : ' + (d.clock || '-'),
        'candidates: ' + (d.cands || '-'),
        'predicted : ' + (d.pre || '-'),
        'pred. rate: hit ' + S.specStat.hit + ' | adopted ' + S.specStat.adopt + ' | missed ' + S.specStat.miss,
        'engine Elo: ' + (d.engElo || '-'),
        'auto Elo  : ' + (d.autoInfo || '-'),
        'auto speed: ' + (d.autoSpeed || '-'),
        'opp Elo   : ' + (d.oppElo || '?') + ' (used for predictions) | predicting ' + (d.specK || '-') + ' moves, done ' + (d.specDone || 0),
        'FEN       : ' + (d.fen || '-'),
        'engine    : ' + (d.engine || '-'),
        'mode      : ' + (LITE ? 'light (touch screen)' : 'full'),
        'last      : ' + (d.last || '-'),
        'error     : ' + (d.err || '-'),
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

    let lastArrows = null, arrowSeq = 0, drawnKey = '';
    function drawArrows(arrows, bd, flipped, board) {
      lastArrows = arrows ? { arrows, flipped, board, id: ++arrowSeq } : null;
      layoutArrows();
    }
    function layoutArrows() {
      const svg = el.arrows;
      const hide = () => { while (svg.firstChild) svg.removeChild(svg.firstChild); svg.style.display = 'none'; drawnKey = ''; };
      if (!lastArrows || !lastArrows.board || !lastArrows.board.isConnected) { hide(); return; }
      const rect = lastArrows.board.getBoundingClientRect();
      const size = Math.min(rect.width, rect.height);
      if (size < 40) { hide(); return; }
      svg.style.display = 'block';
      svg.style.left = rect.left + 'px'; svg.style.top = rect.top + 'px';
      svg.style.width = size + 'px'; svg.style.height = size + 'px';
      const key = lastArrows.id + '|' + size.toFixed(1) + '|' + lastArrows.flipped;
      if (key === drawnKey && svg.firstChild) return;
      drawnKey = key;
      while (svg.firstChild) svg.removeChild(svg.firstChild);
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
      const w = sq * AR.w, head = sq * AR.head;
      const mk = (tag, attrs) => { const e = document.createElementNS(NS_SVG, tag); for (const k in attrs) e.setAttribute(k, attrs[k]); return e; };
      const labels = [];
      list.forEach((a) => {
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
        const g = mk('g', { opacity: AR.bodyOpacity });
        g.appendChild(mk('path', { d: dPath, fill: 'none', stroke: TIER_COLOR[a.tier], 'stroke-width': w, 'stroke-linecap': 'round', 'stroke-linejoin': 'round' }));
        g.appendChild(mk('polygon', { points: pts, fill: TIER_COLOR[a.tier] }));
        svg.appendChild(g);
        if (CFG.showPct && a.label) labels.push({ a, p2, dest: i2 });
      });
      const LP = { 1: 0, 2: 1, 3: 2, 0: 3 };
      const topByDest = {};
      for (const L of labels) {
        const cur = topByDest[L.dest];
        if (!cur || LP[L.a.tier] < LP[cur.a.tier]) topByDest[L.dest] = L;
      }
      labels.splice(0, labels.length, ...Object.keys(topByDest).map((k) => topByDest[k]));
      for (const L of labels) {
        const fs = sq * 0.19, bh = sq * 0.29;
        const bw = Math.max(sq * 0.5, L.a.label.length * fs * 0.62 + sq * 0.18);
        const cx = clamp(L.p2[0] + sq * 0.3, bw / 2 + 1, size - bw / 2 - 1);
        const cy = clamp(L.p2[1] - sq * 0.32, bh / 2 + 1, size - bh / 2 - 1);
        const g2 = mk('g', {});
        g2.appendChild(mk('rect', { x: cx - bw / 2, y: cy - bh / 2, width: bw, height: bh, rx: bh * 0.4, fill: 'rgba(4,5,13,0.9)', stroke: TIER_COLOR[L.a.tier], 'stroke-width': Math.max(1, sq * 0.03) }));
        const tx = mk('text', { x: cx, y: cy, 'text-anchor': 'middle', 'dominant-baseline': 'central', fill: '#ffffff', 'font-size': fs, 'font-weight': 700, 'font-family': 'system-ui,-apple-system,sans-serif' });
        tx.textContent = L.a.label;
        g2.appendChild(tx);
        svg.appendChild(g2);
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

  function pageKind() {
    if (location.hostname !== CFG.host) return null;
    if (CFG.pathRe.test(location.pathname)) return 'game';
    if (CFG.setupRe.test(location.pathname)) return 'setup';
    return null;
  }

  function init() {
    if (!pageKind()) return;

    const S = {
      settings: Object.assign({}, DEFAULTS, store.get('cch_settings', {})),
      dead: false, suspended: false,
      board: null, observer: null, resizeObs: null,
      sig: '', prevBd: null, rights: null, turn: null, turnSrc: '', lastMove: { w: null, b: null },
      boardTurn: null, boardTurnSrc: '', needRun: true, arb: { since: 0 }, clockMem: {}, flippedSeen: null, pendingShown: false,
      flipped: false, me: null,
      reqId: 0, last: null, ep: '', pingP: null, am: { fen: '', move: '', timer: 0, done: false }, oppElo: null, autoElo: null, autoMe: null, autoOpp: null, autoInfo: '', autoSpeedKey: null, clockMax: 0, speedInfo: '', specBoost: 0, spec: null, specHit: null, specAdopt: null, specStat: { hit: 0, adopt: 0, miss: 0 }, preMiss: false,
      premoveGhost: false,
      dbg: {}, uciMin: 1320, uciMax: 3190,
      bridgeOk: false, bridgeChecked: false, bridgeErr: '', lastPing: 0, pinging: false,
      snapTimer: 0, snapTries: 0, tickTimer: 0, clockTimer: 0, redrawTimer: 0, eloTimer: 0,
    };
    S.settings.tiers = Object.assign({}, DEFAULTS.tiers, S.settings.tiers || {});
    if (!['bot', 'human', 'troll'].includes(S.settings.style)) S.settings.style = 'bot';
    S.settings.speed = { peluru: 'bullet', kilat: 'blitz', cepat: 'rapid' }[S.settings.speed] || S.settings.speed;
    if (!CFG.presets[S.settings.speed]) S.settings.speed = CFG.defaultSpeed;
    S.settings.autoSpeed = !!S.settings.autoSpeed;
    S.settings.colors = Object.assign({}, DEFAULTS.colors, S.settings.colors || {});
    ['c1', 'c2', 'c3'].forEach((k) => {
      if (!HEX_RE.test(S.settings.colors[k])) S.settings.colors[k] = DEFAULTS.colors[k];
      S.settings.colors[k] = S.settings.colors[k].toLowerCase();
    });
    applyColors(S.settings.colors);
    S.settings.elo = clamp(+S.settings.elo || 3000, 100, 3000);
    S.settings.autoElo = !!S.settings.autoElo;
    S.settings.premove = !!S.settings.premove;
    S.settings.autoMove = !!S.settings.autoMove;

    const bridge = new BridgeEngine(CFG.bridge);
    const wasm = new WasmEngine(CFG);
    let ui = null;

    const save = () => store.set('cch_settings', S.settings);
    const curElo = () => (S.settings.autoElo && S.autoElo ? S.autoElo : S.settings.elo);
    const curSpeed = () => (S.settings.autoSpeed && S.autoSpeedKey ? S.autoSpeedKey : S.settings.speed);

    function engineLabel() {
      const builtin = wasm.state === 'ready' ? 'built-in Stockfish' : wasm.state === 'loading' ? 'loading built-in Stockfish…'
        : wasm.state === 'failed' ? 'built-in Stockfish failed to load' : 'built-in Stockfish (not loaded)';
      if (S.bridgeOk) return 'bridge: ' + ((bridge.info && bridge.info.name) || 'Stockfish');
      return S.bridgeChecked ? 'bridge not connected, using ' + builtin : 'checking bridge…';
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
        if (!was) dbg('bridge connected: ' + (j.engine && j.engine.name));
      } catch (e) {
        if (S.bridgeOk) dbg('bridge disconnected: ' + e.message);
        S.bridgeOk = false; S.bridgeErr = e.message;
      } finally {
        S.pinging = false; S.bridgeChecked = true; S.lastPing = Date.now();
        S.dbg.engine = engineLabel();
        if (ui) ui.renderSettings();
        preloadBuiltin();
      }
    }

    function findBoard() {
      return document.querySelector('wc-chess-board') || document.querySelector('chess-board') ||
        document.querySelector('#board-single') || document.querySelector('.board');
    }
    function readOrientation(board) {
      const br = board.getBoundingClientRect();
      const size = Math.min(br.width, br.height);
      if (size < 80) return null;
      const sq = size / 8;
      let normal = 0, flipped = 0;
      for (const el of board.querySelectorAll('.piece')) {
        let f = 0, r = 0;
        for (const c of el.classList) {
          if (c.length === 9 && c.indexOf('square-') === 0) { f = +c[7]; r = +c[8]; }
        }
        if (f < 1 || f > 8 || r < 1 || r > 8) continue;
        const pr = el.getBoundingClientRect();
        if (!(pr.width > 0)) continue;
        const col = Math.floor((pr.left + pr.width / 2 - br.left) / sq);
        const row = Math.floor((pr.top + pr.height / 2 - br.top) / sq);
        if (col === f - 1 && row === 8 - r) normal++;
        else if (col === 8 - f && row === r - 1) flipped++;
      }
      if (normal + flipped < 4 || normal === flipped) return null;
      return flipped > normal;
    }

    function visualBottom(board) {
      const br = board.getBoundingClientRect();
      const size = Math.min(br.width, br.height);
      if (size < 80) return null;
      let w = 0, wy = 0, b = 0, by = 0;
      for (const el of board.querySelectorAll('.piece')) {
        let c = null;
        for (const k of el.classList) if (k.length === 2 && /^[wb][pnbrqk]$/.test(k)) c = k[0];
        if (!c) continue;
        const r = el.getBoundingClientRect();
        if (!(r.width > 0)) continue;
        const y = r.top + r.height / 2;
        if (c === 'w') { w++; wy += y; } else { b++; by += y; }
      }
      if (w < 4 || b < 4) return null;
      const d = wy / w - by / b;
      if (Math.abs(d) < size / 8) return null;
      return d > 0 ? 'w' : 'b';
    }

    function detectFlipped(board, count) {
      const vb = count >= 28 ? visualBottom(board) : null;
      if (vb) return { flipped: vb === 'b', src: 'visual', vb };
      const geo = readOrientation(board);
      if (geo != null) return { flipped: geo, src: 'pieces', vb: null };
      return { flipped: board.classList.contains('flipped'), src: 'class', vb: null };
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
      const f = detectFlipped(board, count);
      return { bd, dup, count, hl, flipped: f.flipped, flipSrc: f.src, vb: f.vb };
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
        status('err', "Can't read the board (pieces overlap)."); return;
      }
      S.snapTries = 0;
      const placement = fenPlacement(snap.bd);
      const sig = placement + '|' + (snap.flipped ? 'f' : 'n');
      if (sig === S.sig && force !== true) return;
      S.sig = sig;
      processSnapshot(snap, placement);
    }

    function oppTurnSource() {
      if (S.me == null || !S.turn || S.turn === S.me) return '';
      let ck = null;
      try { ck = clockTurn(readClocks(S.board), S.flipped ? 'b' : 'w', S.clockMem, Date.now(), CFG.clockTickMs); } catch (e) { }
      if (ck && ck.turn) return ck.turn !== S.me ? 'clock' : '';
      return 'board';
    }

    function isPremoveGhost(prev, bd, placement) {
      if (!prev || placement === START_PLACEMENT) return '';
      const src = oppTurnSource();
      if (!src) return '';
      const oppWhite = S.me !== 'w';
      for (let i = 0; i < 64; i++) {
        if (bd[i] && bd[i] !== prev[i] && isWhitePc(bd[i]) === oppWhite) return '';
      }
      return src;
    }

    function bottomColor(snap) {
      if (snap.vb) return snap.vb;
      try {
        const c = readClocks(S.board).find((x) => x.pos === 'bottom' && x.color);
        if (c) return c.color;
      } catch (e) { }
      return snap.flipped ? 'b' : 'w';
    }

    function processSnapshot(snap, placement) {
      const prev = S.prevBd;
      const changedPos = !prev || fenPlacement(prev) !== placement;
      const newGame = changedPos && !!prev && nearStart(snap.bd) && !nearStart(prev);
      const prevMe = S.me;
      if (newGame) {
        S.me = null; S.rights = null; S.lastMove = { w: null, b: null };
        S.specBoost = 0; S.clockMax = 0; S.clockMem = {}; S.oppElo = null;
        S.autoMe = null; S.autoOpp = null; S.autoInfo = ''; S.autoSpeedKey = null; S.speedInfo = '';
        if (S.spec) S.spec.stop = true;
        S.spec = null; S.specHit = null; S.specAdopt = null; S.preMiss = false;
        resetAutoMove();
        cancelAnalysis();
        dbg('new game detected');
        [150, 400, 900, 1600].forEach((ms) => setTimeout(() => { if (!S.dead && !S.suspended) takeSnapshot(true); }, ms));
      }
      S.flipped = snap.flipped; S.dbg.flipSrc = snap.flipSrc;
      if (S.me == null || nearStart(snap.bd)) S.me = bottomColor(snap);
      if (snap.vb && snap.count >= 30 && S.me !== snap.vb) { S.me = snap.vb; S.needRun = true; dbg('color corrected from the board: ' + S.me); }
      if (newGame) S.holdUntil = S.me === prevMe ? Date.now() + 800 : 0;
      S.dbg.me = S.me === 'w' ? 'white' : 'black';
      if (S.flippedSeen !== snap.flipped) { S.flippedSeen = snap.flipped; S.needRun = true; }

      const ghost = changedPos ? isPremoveGhost(prev, snap.bd, placement) : '';
      if (ghost) {
        if (!S.premoveGhost) { S.premoveGhost = true; dbg('premove detected, still the opponent\'s turn (from ' + ghost + '), keeping arrows'); }
        return;
      }
      S.premoveGhost = false;

      if (changedPos) {
        resetAutoMove();
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
          turn = 'w'; src = 'start position'; S.rights = 'KQkq'; S.lastMove = { w: null, b: null }; S.specBoost = 0; S.clockMax = 0;
        } else {
          diff = prev ? diffInfo(prev, snap.bd) : null;
          const dm = diff ? diff.mover : null;
          const hm = highlightMover(snap.bd, snap.hl, prev);
          const mover = dm || hm;
          if (mover) {
            turn = mover === 'w' ? 'b' : 'w';
            src = dm ? (hm && hm !== dm ? 'board diff (highlight differs)' : 'board diff') : 'highlight';
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

    const clockCache = { els: [], at: 0 };
    function readClocks(board) {
      const now = Date.now();
      let els = clockCache.els;
      if (now - clockCache.at > (els.length ? 2500 : 1500) || els.some((e) => !e.isConnected)) {
        els = Array.from(document.querySelectorAll('.clock-component'));
        if (!els.length) {
          els = Array.from(document.querySelectorAll('[class*="clock"]'))
            .filter((e) => parseClockText((e.textContent || '').replace(/\s+/g, '')) != null);
          els = els.filter((e) => !els.some((o) => o !== e && o.contains(e)));
        }
        clockCache.els = els; clockCache.at = now;
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
          if (ui) ui.setSuggestion('—', 'Syncing clock and board…');
          status('warn', 'Clock and board disagree. Syncing…');
        }
        return;
      }
      S.pendingShown = false;
      const turnChanged = d.turn !== S.turn;
      S.turn = d.turn; S.turnSrc = d.src;
      S.dbg.turn = d.turn ? (d.turn === 'w' ? 'white' : 'black') : null; S.dbg.turnSrc = d.src;
      if (turnChanged || S.needRun) { S.needRun = false; onPositionReady(); }
    }

    function readElo(which) {
      let box = null;
      const sels = which === 'bottom'
        ? ['#board-layout-player-bottom', '.board-layout-bottom', '[class*="player-bottom"]', '.player-bottom']
        : ['#board-layout-player-top', '.board-layout-top', '[class*="player-top"]', '.player-top'];
      for (const sel of sels) {
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

    const readOppElo = () => readElo('top');

    function refreshAutoElo() {
      if (S.suspended) return;
      if (S.settings.autoElo) {
        const me = readElo('bottom');
        const opp = CFG.oppElo || readElo('top');
        if (me) S.autoMe = me;
        if (opp) S.autoOpp = opp;
        const a = S.autoMe, b = S.autoOpp;
        const raw = a && b ? Math.max(a, b) : (a || b || null);
        if (raw) {
          const info = a && b
            ? 'you ' + a + ' vs opponent ' + b + ' \u2192 using ' + (a >= b ? 'your' : "the opponent's") + ' Elo'
            : 'only ' + (a ? 'your Elo (' + a + ')' : "the opponent's Elo (" + b + ')') + ' was detected';
          const v = clamp(Math.round((raw + (CFG.autoEloMargin || 0)) / 50) * 50, 100, 3000);
          if (v !== S.autoElo || info !== S.autoInfo) {
            S.autoElo = v; S.autoInfo = info;
            if (ui) ui.renderSettings();
          }
        }
      }
      S.dbg.engElo = curElo() + (S.settings.autoElo && S.autoElo ? ' (auto)' : ' (slider)');
      S.dbg.autoInfo = S.settings.autoElo ? (S.autoInfo || 'not detected') : null;
    }

    function fmtClock(sec) { return Math.floor(sec / 60) + ':' + String(Math.round(sec % 60)).padStart(2, '0'); }

    function refreshAutoSpeed() {
      if (!S.settings.autoSpeed || !S.board) { S.dbg.autoSpeed = null; return; }
      const cl = readClocks(S.board);
      const secs = cl.map((c) => parseClockText(c.text)).filter((v) => v != null);
      if (secs.length) S.clockMax = Math.max(S.clockMax, Math.max.apply(null, secs));
      let key = null, info = '';
      if (S.clockMax > 0) {
        key = S.clockMax < 180 ? 'bullet' : S.clockMax < 600 ? 'blitz' : 'rapid';
        info = 'clock ' + fmtClock(S.clockMax) + ' \u2192 ' + CFG.presets[key].label;
      } else if (!cl.length) {
        key = 'rapid'; info = 'no clock \u2192 Rapid';
      }
      if (key && (key !== S.autoSpeedKey || info !== S.speedInfo)) {
        S.autoSpeedKey = key; S.speedInfo = info;
        if (ui) ui.renderSettings();
      }
      S.dbg.autoSpeed = S.autoSpeedKey ? info : 'not detected';
    }

    function preloadBuiltin() {
      if (S.dead || S.suspended || wasm.state !== 'idle') return;
      if (!S.bridgeChecked || S.bridgeOk) return;
      status('warn', 'Loading built-in Stockfish (one-time download)…');
      wasm.ensure().then(() => {
        dbg('built-in Stockfish ready');
        if (!S.last) status('ok', 'Built-in Stockfish ready.');
      }, (e) => {
        dbg('built-in Stockfish failed: ' + e.message);
        status('err', 'Built-in Stockfish failed to load: ' + e.message);
      });
    }

    function clearArrowsNow() { if (ui) ui.drawArrows(null); }

    function cancelAnalysis(keepArrows) {
      S.reqId++;
      clearTimeout(S.am.timer); S.am.timer = 0;
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
      if (S.holdUntil && Date.now() < S.holdUntil) {
        clearTimeout(S.holdTimer);
        S.holdTimer = setTimeout(() => { if (!S.dead && !S.suspended) onPositionReady(); }, S.holdUntil - Date.now() + 20);
        ui.setSuggestion('—', 'Checking which side you play…');
        return;
      }
      refreshAutoElo();
      refreshAutoSpeed();
      const turnMe = !!S.turn && S.turn === S.me;
      if (turnMe && S.specHit) {
        const hit = S.specHit; S.specHit = null; S.specAdopt = null; S.preMiss = false;
        showHit(hit);
        return;
      }
      if (turnMe && S.specAdopt) {
        const ad = S.specAdopt; S.specAdopt = null; S.preMiss = false;
        const id0 = S.reqId;
        ui.setSuggestion('—', 'Prediction was right, finishing the calculation…');
        status('warn', 'Prediction was right, waiting for the calculation…');
        let last = null;
        try { last = await ad.promise; } catch (e) { last = null; }
        if (id0 !== S.reqId) return;
        if (last) { showHit(last); return; }
      }
      cancelAnalysis();
      const id = S.reqId;
      if (!S.turn) {
        ui.setSuggestion('—', '');
        status('warn', "Can't tell whose turn it is yet. Waiting for the next move…");
        return;
      }
      if (S.turn !== S.me) {
        S.specHit = null; S.specAdopt = null; S.preMiss = false; S.spec = null;
        if (S.settings.premove) { ui.setSuggestion('—', "Opponent's turn. Predicting their move…"); status('warn', "Predicting the opponent's move…"); }
        else { ui.setSuggestion('—', "Opponent's turn"); status('ok', "Opponent's turn."); }
        if (specAllowed()) await speculate(id);
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
        status('err', 'Invalid position (' + err + '), not sent to the engine.');
        return;
      }
      S.dbg.err = '';
      if (miss) {
        ui.setSuggestion('—', 'Prediction missed, recalculating…');
        status('warn', 'Prediction missed, new arrows coming…');
        await sleep(CFG.premoveMissDelayMs);
        if (id !== S.reqId) return;
      }
      await analyze(id, fen);
    }

    function preset() { return CFG.presets[curSpeed()] || CFG.presets[CFG.defaultSpeed]; }

    const resCache = new Map();
    const resKey = (fen) => fen + '|' + curSpeed() + '|' + curElo() + '|' + (S.settings.style === 'human' ? 'h' : '');
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
      const parts = fen.split(' ');
      const wantBook = S.settings.style === 'human' && parts[1] === S.me && BOOK.has(parts[0] + ' ' + parts[1]);
      const mk = (usingWasm, plan) => {
        const rq = buildRequest(fen, usingWasm, plan);
        if (wantBook) rq.multipv = Math.max(rq.multipv, usingWasm ? 8 : 10);
        if (opt.multipv) rq.multipv = opt.multipv;
        if (opt.probe !== undefined) rq.probe = opt.probe;
        if (opt.movetime) rq.movetime = opt.movetime;
        return rq;
      };
      let res = null, via = '';
      if (S.bridgeOk) {
        try {
          const plan = eloPlan(curElo(), S.uciMin, S.uciMax, preset().probeTime);
          res = await bridge.analyze(mk(false, plan));
          via = 'bridge';
        } catch (e) {
          if (id !== S.reqId) return null;
          if (e.kind === 'engine') throw e;
          S.bridgeOk = false; S.bridgeErr = e.message;
          dbg('bridge failed, switching to WASM: ' + e.message);
          if (ui) ui.renderSettings();
        }
      }
      if (id !== S.reqId) return null;
      if (!res) {
        if (wasm.state !== 'ready') status('warn', 'Loading built-in Stockfish (one-time download)…');
        S.uciMin = wasm.range.min; S.uciMax = wasm.range.max;
        const plan = eloPlan(curElo(), S.uciMin, S.uciMax, preset().probeTime);
        res = await wasm.analyze(mk(true, plan), (st) => { if (st === 'loading') status('warn', 'Loading built-in Stockfish (one-time download)…'); });
        S.uciMin = wasm.range.min; S.uciMax = wasm.range.max;
        if (ui) ui.renderSettings();
        via = 'built-in';
      }
      if (id !== S.reqId || res.cancelled) return null;
      return { res, via };
    }

    function engineFail(e) {
      const msg = String(e && e.message || e);
      S.dbg.err = msg;
      dbg('analysis failed: ' + msg);
      ui.setSuggestion('—', '');
      if (e.kind === 'wasm') {
        status('err', e.wasmFailure === 'blocked' ? 'Browser blocked the built-in engine (' + msg + ')' :
          e.wasmFailure === 'download' ? "Couldn't download the built-in engine (" + msg + ')' : 'Built-in engine error (' + msg + ')');
      } else status('err', 'Engine error: ' + msg);
    }

    async function analyze(id, fen) {
      const cached = resCache.get(resKey(fen));
      if (cached && id === S.reqId) {
        S.last = { res: cached.res, fen, via: cached.via, ms: cached.ms, bd: S.bd, flipped: S.flipped, board: S.board };
        S.dbg.last = cached.via + ' | cache | depth ' + cached.res.depth + ' | ' + cached.res.lines.length + ' candidates';
        render();
        return;
      }
      if (!S.bridgeChecked) { status('warn', 'Checking bridge…'); await pingBridge(); if (id !== S.reqId) return; }
      const t0 = performance.now();
      status('warn', 'Calculating…');
      let out;
      try { out = await runEngine(id, fen); } catch (e) { if (id !== S.reqId) return; engineFail(e); return; }
      if (!out) return;
      const res = out.res, via = out.via;
      if (!res.lines || !res.lines.length) {
        ui.setSuggestion('—', 'No moves');
        status('warn', 'No legal moves found (game over?).');
        return;
      }
      S.last = { res, fen, via, ms: Math.round(performance.now() - t0), bd: S.bd, flipped: S.flipped, board: S.board };
      S.dbg.last = via + ' | ' + S.last.ms + ' ms | depth ' + res.depth + ' | ' + res.lines.length + ' candidates';
      remember(fen, res, via, S.last.ms);
      render();
    }

    function specAllowed() {
      return CFG.speculate && (!LITE || !!S.settings.premove);
    }

    async function speculate(id) {
      const bd = S.bd, oppTurn = S.turn;
      const spec = { base: fenPlacement(bd), cache: new Map(), inflight: null, stop: false, first: null };
      S.spec = spec;
      const vis = () => S.settings.premove && S.spec === spec && !spec.stop;
      const err = validateBoard(bd, oppTurn);
      if (err) {
        dbg('guess skipped: ' + err);
        if (S.settings.premove) { S.dbg.err = err; ui.setSuggestion('—', ''); status('err', 'Invalid position (' + err + '), not sent to the engine.'); }
        return;
      }
      S.dbg.err = '';
      const fenOpp = buildFEN(bd, oppTurn, S.rights, S.ep);
      S.dbg.fen = fenOpp;
      if (!S.bridgeChecked) { await pingBridge(); if (id !== S.reqId) return; }
      const pr = preset();
      const deep = pr.specDeep || 8;
      const K0 = S.bridgeOk ? deep : Math.min(deep, CFG.specWasmCands);
      const oppElo = CFG.oppElo || readOppElo() || S.autoOpp || S.oppElo || null;
      if (oppElo) S.oppElo = oppElo;
      S.dbg.oppElo = oppElo ? oppElo + (CFG.oppElo ? ' (manual)' : '') : null;
      const oplan = oppElo ? eloPlan(oppElo, S.uciMin, S.uciMax, pr.probeTime) : null;
      let o1;
      try { o1 = await runEngine(id, fenOpp, { multipv: K0, probe: oplan ? oplan.probe : null }); } catch (e) {
        if (id !== S.reqId) return;
        if (vis()) engineFail(e); else dbg('guess failed: ' + String(e && e.message || e));
        return;
      }
      if (!o1) return;
      const K = o1.via === 'bridge' ? deep : Math.min(deep, CFG.specWasmCands);
      const lines = (o1.res.lines || []).slice().sort((x, y) => x.rank - y.rank);
      const sc = lines.map(scoreOf);
      const top = sc.length ? Math.max.apply(null, sc) : 0;
      const win = oppElo ? Math.round(clamp(CFG.specWindow + (2800 - oppElo) / 8, CFG.specWindow, 450)) : CFG.specWindow;
      const moves = [];
      const bm = o1.res.bestmove || (lines[0] && lines[0].move);
      if (bm) moves.push(bm);
      const pb = o1.res.probe_bestmove;
      if (pb && moves.indexOf(pb) < 0) moves.push(pb);
      lines.forEach((l, i) => { if (top - sc[i] <= win && moves.indexOf(l.move) < 0) moves.push(l.move); });
      const cands = moves.slice(0, K);
      if (!cands.length) {
        if (vis()) { ui.setSuggestion('—', "Opponent's turn"); status('warn', "Can't predict the opponent's move (game over?)."); }
        return;
      }
      S.dbg.pre = cands.map((m) => describeMove(bd, m)).join(' | ') + ' (' + o1.via + ')';
      S.dbg.specK = cands.length; S.dbg.specDone = 0;
      if (ui) ui.renderDebug();
      const tStart = performance.now();
      for (let i = 0; i < cands.length; i++) {
        if (S.spec !== spec || spec.stop || id !== S.reqId) return;
        if (performance.now() - tStart > CFG.specBudgetMs) { dbg('guessing stopped: time limit'); return; }
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
        if (err2) { dbg('guess ' + m + ' skipped: ' + err2); continue; }
        const placement = fenPlacement(ap.bd);
        const fenMe = buildFEN(ap.bd, S.me, rights2, ep2);
        const predText = describeMove(bd, m);
        if (i === 0 && vis()) status('warn', 'Premove: preparing a reply in case the opponent plays ' + predText + '…');
        const cachedHit = resCache.get(resKey(fenMe));
        const p = (async () => {
          if (cachedHit) {
            return {
              res: cachedHit.res, fen: fenMe, via: cachedHit.via, ms: cachedHit.ms, bd: ap.bd, flipped: S.flipped, board: S.board,
              pre: true, predText, rights: rights2, oppLast: { from: ap.from, to: ap.to, piece: ap.piece.toLowerCase() },
            };
          }
          const o2 = await runEngine(id, fenMe, i >= 3 ? { movetime: Math.max(80, Math.round(pr.movetime * CFG.specLowFrac)) } : undefined);
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
          if (i === 0 && vis()) engineFail(e); else dbg('guess ' + m + ' failed: ' + String(e && e.message || e));
          return;
        }
        spec.inflight = null;
        if (last) { spec.cache.set(placement, last); if (i === 0) spec.first = last; }
        if (S.spec !== spec || spec.stop || id !== S.reqId) return;
        S.dbg.specDone = i + 1;
        if (!last) continue;
        if (i === 0) {
          S.dbg.last = 'guess | ' + last.via + ' | ' + last.ms + ' ms | depth ' + last.res.depth + ' | ' + last.res.lines.length + ' candidates';
          if (vis()) { S.last = last; render(); }
        }
      }
    }

    function squareCenter(idx) {
      const r = S.board.getBoundingClientRect();
      const sq = Math.min(r.width, r.height) / 8;
      const f = idx & 7, rk = idx >> 3;
      return [r.left + ((S.flipped ? 7 - f : f) + 0.5) * sq, r.top + ((S.flipped ? rk : 7 - rk) + 0.5) * sq];
    }

    function clickAt(x, y) {
      let t = document.elementFromPoint(x, y);
      if (!t || (t.hasAttribute && t.hasAttribute('data-nebulachess'))) t = S.board;
      const mouse = { bubbles: true, cancelable: true, composed: true, clientX: x, clientY: y, screenX: x, screenY: y, button: 0 };
      const ptr = Object.assign({ pointerId: 1, pointerType: 'mouse', isPrimary: true }, mouse);
      t.dispatchEvent(new PointerEvent('pointerdown', Object.assign({ buttons: 1 }, ptr)));
      t.dispatchEvent(new MouseEvent('mousedown', Object.assign({ buttons: 1 }, mouse)));
      t.dispatchEvent(new PointerEvent('pointerup', Object.assign({ buttons: 0 }, ptr)));
      t.dispatchEvent(new MouseEvent('mouseup', Object.assign({ buttons: 0 }, mouse)));
      t.dispatchEvent(new MouseEvent('click', Object.assign({ buttons: 0 }, mouse)));
    }

    async function playMove(uci, human) {
      if (human) return playMoveHuman(uci);
      const a = squareCenter(sqIdx(uci.slice(0, 2)));
      clickAt(a[0], a[1]);
      await sleep(90 + Math.random() * 130);
      const b = squareCenter(sqIdx(uci.slice(2, 4)));
      clickAt(b[0], b[1]);
      if (!uci[4]) return;
      const want = S.me + uci[4];
      for (let i = 0; i < 15; i++) {
        await sleep(100);
        const el = document.querySelector('.promotion-window [class~="' + want + '"]');
        if (el) { const r = el.getBoundingClientRect(); clickAt(r.left + r.width / 2, r.top + r.height / 2); return; }
      }
      throw new Error('promotion window not found');
    }

    function hitTarget(x, y) {
      let t = document.elementFromPoint(x, y);
      if (!t || (t.hasAttribute && t.hasAttribute('data-nebulachess'))) t = S.board;
      return t;
    }

    function pointerEv(type, x, y, buttons) {
      const o = { bubbles: true, cancelable: true, composed: true, clientX: x, clientY: y, screenX: x, screenY: y, button: 0, buttons };
      if (type.indexOf('pointer') === 0) {
        o.pointerId = 1; o.pointerType = 'mouse'; o.isPrimary = true;
        return new PointerEvent(type, o);
      }
      return new MouseEvent(type, o);
    }

    function emit(x, y, types, buttons) {
      const t = hitTarget(x, y);
      for (const ty of types) t.dispatchEvent(pointerEv(ty, x, y, buttons));
    }

    function pointOnSquare(idx) {
      const c = squareCenter(idx);
      const r = S.board.getBoundingClientRect();
      const sq = Math.min(r.width, r.height) / 8;
      return [c[0] + (Math.random() + Math.random() - 1) * sq * 0.3, c[1] + (Math.random() + Math.random() - 1) * sq * 0.3];
    }

    async function pressAt(x, y, hold) {
      emit(x, y, ['pointerdown', 'mousedown'], 1);
      await sleep(hold);
      emit(x, y, ['pointerup', 'mouseup', 'click'], 0);
    }

    const humanTiming = () => ({
      bullet: { think: [60, 260], hold: [25, 55], gap: [35, 100], promo: [40, 120] },
      blitz: { think: [200, 800], hold: [35, 75], gap: [60, 170], promo: [60, 180] },
      rapid: { think: [450, 1700], hold: [40, 90], gap: [90, 250], promo: [80, 240] },
    })[curSpeed()] || { think: [200, 800], hold: [35, 75], gap: [60, 170], promo: [60, 180] };

    const humanRnd = (r) => r[0] + Math.random() * (r[1] - r[0]);

    function humanClickGap() {
      return humanRnd(humanTiming().gap) * (Math.random() < 0.08 ? 2.5 : 1);
    }

    async function playMoveHuman(uci) {
      const t = humanTiming();
      const from = pointOnSquare(sqIdx(uci.slice(0, 2)));
      await pressAt(from[0], from[1], humanRnd(t.hold));
      await sleep(humanClickGap());
      if (S.dead || S.suspended || !S.settings.autoMove) throw new Error('stopped');
      const to = pointOnSquare(sqIdx(uci.slice(2, 4)));
      await pressAt(to[0], to[1], humanRnd(t.hold));
      if (!uci[4]) return;
      const want = S.me + uci[4];
      for (let i = 0; i < 20; i++) {
        await sleep(60);
        const el = document.querySelector('.promotion-window [class~="' + want + '"]');
        if (el) {
          const r = el.getBoundingClientRect();
          await sleep(humanRnd(t.promo));
          await pressAt(r.left + r.width * (0.35 + Math.random() * 0.3), r.top + r.height * (0.35 + Math.random() * 0.3), humanRnd(t.hold));
          return;
        }
      }
      throw new Error('promotion window not found');
    }

    function humanThinkMs(move, L, d) {
      const t = humanTiming();
      let ms = humanRnd(t.think);
      let k = 1;
      const to = sqIdx(move.slice(2, 4));
      const ol = L.oppLast;
      if (ol && ol.to === to) k *= 0.6;
      if (L.hit) k *= 0.8;
      try {
        if (pieceCount(L.bd) >= 28 && undevMinors(L.bd, S.me === 'w') >= 2) k *= 0.6;
        if (d && d.cs && d.cs.length > 1) {
          const best = Math.max.apply(null, d.cs.map((c) => c.score));
          const close = d.cs.filter((c) => c.mate == null && Math.abs(best - c.score) <= 60).length;
          k *= 0.9 + 0.1 * Math.min(close, 4);
        }
      } catch (e) { }
      const r = Math.random();
      if (r < 0.1) k *= 1.8 + Math.random() * 1.2;
      else if (r < 0.28) k *= 0.6;
      return Math.max(t.think[0] * 0.6, Math.min(ms * k, t.think[1] * 3));
    }

    function scheduleAutoMove(move, L, d) {
      if (!S.settings.autoMove || L.pre || !S.me || S.turn !== S.me) return false;
      if (S.am.fen === L.fen && S.am.done) return false;
      if (S.am.fen === L.fen && S.am.move === move && S.am.timer) return true;
      clearTimeout(S.am.timer);
      const human = S.settings.style !== 'bot';
      const range = preset().moveDelay;
      const wait = human ? humanThinkMs(move, L, d) : range[0] + Math.random() * (range[1] - range[0]);
      S.am = { fen: L.fen, move, timer: 0, done: false, human };
      S.am.timer = setTimeout(() => runAutoMove(L.fen, move), wait);
      return true;
    }

    function resetAutoMove() {
      if (S.am && S.am.timer) clearTimeout(S.am.timer);
      S.am = { fen: '', move: '', timer: 0, done: false };
    }

    function runAutoMove(fen, move) {
      const am = S.am;
      am.timer = 0;
      const placement = fen.split(' ')[0];
      if (S.dead || S.suspended || !S.settings.autoMove || S.turn !== S.me || !S.board || !S.board.isConnected || !S.bd || fenPlacement(S.bd) !== placement) return;
      const cur = detectFlipped(S.board, S.dbg.pieces || 32);
      if (cur.flipped !== S.flipped) { resetAutoMove(); takeSnapshot(true); return; }
      const pcFrom = S.bd[sqIdx(move.slice(0, 2))];
      if (!pcFrom || isWhitePc(pcFrom) !== (S.me === 'w')) { dbg('auto move skipped, not my piece: ' + move); return; }
      am.done = true;
      playMove(move, !!am.human).then(() => {
        setTimeout(() => {
          if (S.dead || S.am !== am || S.turn !== S.me || !S.bd || fenPlacement(S.bd) !== placement) return;
          dbg('auto move did not register: ' + move);
          status('warn', "Auto move didn't go through. Play the arrow yourself.");
        }, 1200);
      }, (e) => {
        if (e && e.message === 'stopped') return;
        dbg('auto move failed: ' + e.message);
        status('warn', 'Auto move failed (' + e.message + '). Play the arrow yourself.');
      });
    }

    function render() {
      const L = S.last;
      if (!L || !ui) return;
      const white = S.me === 'w';
      const plan = eloPlan(curElo(), S.uciMin, S.uciMax, preset().probeTime);
      const elo = curElo();
      const ctx = {
        bd: L.bd, white, rights: L.rights != null ? L.rights : (S.rights || ''), lastMine: S.lastMove[S.me],
        oppLast: L.oppLast !== undefined ? L.oppLast : S.lastMove[white ? 'b' : 'w'],
        plan, style: S.settings.style,
        opening: pieceCount(L.bd) >= 26 && undevMinors(L.bd, white) >= 2,
        attackedBefore: attackedPieces(L.bd, white).map((a) => a.i),
        humanSlip: 0.03 + 0.12 * (1 - elo / 3000),
        bookProb: 0.4 + 0.55 * (elo / 3000),
        book: bookLookup(L.bd, S.me),
        seed: L.fen + '|' + S.settings.style + '|' + elo,
      };
      const d = decide(L.res, ctx);
      if (!d) return;
      S.dbg.cands = d.cs.map((c) => c.move + ' ' + fmtEval(c.score, c.mate)
        + (c === d.tiers[1] ? ' [B]' : c === d.tiers[2] ? ' [U]' : c === d.tiers[3] ? ' [M]' : '') + (c === d.pick ? ' *' : '')).join(' | ');
      ui.renderDebug();
      const arrows = [], seen = new Set();
      const pctLabel = (c) => (c.mate != null ? fmtEval(c.score, c.mate) : Math.round(winPct(c.score)) + '%');
      const add = (c, tier, emph) => {
        if (seen.has(c.move)) { dbg('duplicate arrow dropped: ' + c.move + ' (tier ' + tier + ')'); return; }
        seen.add(c.move); arrows.push({ move: c.move, tier, emph, label: pctLabel(c) });
      };
      for (const t of [1, 2, 3]) {
        const c = d.tiers[t];
        if (c && S.settings.tiers['t' + t]) add(c, t, c === d.pick);
      }
      if (d.pickTier === 0 && S.settings.tiers.t3) add(d.pick, 0, true);
      if (S.settings.autoMove && !L.pre) { arrows.length = 0; seen.clear(); add(d.pick, d.pickTier, true); }
      else if (!seen.has(d.pick.move)) add(d.pick, d.pickTier, true);
      ui.drawArrows(arrows, L.bd, L.flipped, L.board);
      const styleName = { bot: 'Bot', human: 'Human', troll: 'Troll' }[d.styleUsed];
      const tierName = {
        1: d.pick === d.bestC ? 'best move' : (d.trollWin ? 'still winning' : 'near-best'),
        2: 'solid', 3: 'weaker option', 0: 'risky (outside the safe range)',
      }[d.pickTier] || '';
      const ev = fmtEval(d.evalScore, d.evalMate);
      const sub = ['Eval ' + ev + (d.evalScore >= 150 ? ' (you are ahead)' : d.evalScore <= -150 ? ' (you are behind)' : ' (balanced)'),
        styleName + (tierName ? ' · ' + tierName : '') + (d.tags.length ? ' · ' + d.tags.join(', ') : '')].join('\n');
      const bestLine = d.styleUsed !== 'bot' && d.pick !== d.bestC
        ? '\nEngine best: ' + describeMove(L.bd, d.bestC.move) + ' (' + fmtEval(d.bestC.score, d.bestC.mate) + ')' : '';
      const preLine = L.pre ? 'Premove: if the opponent plays ' + L.predText + '\n' : '';
      ui.setSuggestion(describeMove(L.bd, d.pick.move), preLine + sub + bestLine + (d.note ? '\n' + d.note : ''));
      const queued = scheduleAutoMove(d.pick.move, L, d);
      status('ok', queued ? 'Auto move: playing ' + describeMove(L.bd, d.pick.move) + '…'
        : L.pre ? 'Premove (if ' + L.predText + ') · ' + L.via + ' · ' + L.ms + ' ms · depth ' + L.res.depth
        : L.hit ? 'Prediction was right, reply ready · ' + L.via + ' · depth ' + L.res.depth
        : 'Ready · ' + L.via + ' · ' + L.ms + ' ms · depth ' + L.res.depth);
    }

    function attachBoard(board) {
      if (S.observer) S.observer.disconnect();
      if (S.resizeObs) S.resizeObs.disconnect();
      S.board = board;
      const relevantNode = (n) => !!(n && n.classList && (n.classList.contains('piece') || n.classList.contains('highlight')));
      S.observer = new MutationObserver((muts) => {
        for (const m of muts) {
          if (m.type === 'attributes') { if (m.target === board || relevantNode(m.target)) { scheduleSnapshot(); return; } }
          else {
            for (const n of m.addedNodes) if (relevantNode(n)) { scheduleSnapshot(); return; }
            for (const n of m.removedNodes) if (relevantNode(n)) { scheduleSnapshot(); return; }
          }
        }
      });
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
      S.autoMe = null; S.autoOpp = null; S.autoInfo = ''; S.clockMax = 0; S.autoSpeedKey = null; S.speedInfo = '';
      S.premoveGhost = false;
      dbg('board found: ' + S.dbg.board);
      takeSnapshot(true);
    }

    function suspend(keepUI) {
      if (!S.suspended) {
        S.suspended = true;
        S.reqId++; bridge.abort(); wasm.terminate();
        if (S.observer) S.observer.disconnect();
        if (S.resizeObs) S.resizeObs.disconnect();
        S.observer = null; S.resizeObs = null; S.board = null;
        S.spec = null; S.specHit = null; S.specAdopt = null; S.preMiss = false;
        clearTimeout(S.snapTimer); clearTimeout(S.holdTimer);
        resetAutoMove();
        if (ui) ui.drawArrows(null);
        dbg(keepUI ? 'setup page, game logic paused' : 'not a game page, script paused');
      }
      if (ui) ui.setVisible(!!keepUI);
    }

    function switchKind(kind) {
      S.kind = kind;
      if (kind === 'game') { if (S.suspended) resume(); return; }
      suspend(kind === 'setup');
      if (kind === 'setup' && ui) {
        ui.setSuggestion('\u2014', 'Setup mode. Open a game to start.');
        status('ok', 'Setup mode: adjust your settings here. Arrows and auto move only run in a game.');
      }
    }
    function resume() {
      if (!S.suspended) return;
      S.suspended = false; S.sig = ''; S.prevBd = null;
      if (ui) ui.setVisible(true);
      dbg('back on a game page, script resumed');
      preloadBuiltin();
    }

    function tick() {
      if (S.dead) return;
      S.dbg.path = location.pathname;
      const kind = pageKind();
      if (kind !== S.kind) switchKind(kind);
      if (kind !== 'game') {
        if (kind === 'setup' && Date.now() - S.lastPing > (S.bridgeOk ? CFG.bridgeAlivePingMs : CFG.bridgePingMs)) pingBridge();
        return;
      }
      const b = findBoard();
      if (!b) {
        if (S.board) { S.board = null; if (S.observer) S.observer.disconnect(); clearArrowsNow(); }
        status('warn', "Can't find the board. chess.com may have changed its layout.");
        return;
      }
      if (b !== S.board) attachBoard(b); else takeSnapshot();
      if (Date.now() - S.lastPing > (S.bridgeOk ? CFG.bridgeAlivePingMs : CFG.bridgePingMs)) pingBridge();
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
      } else if (specAllowed()) {
        cancelAnalysis(); S.spec = null;
        speculate(S.reqId);
      }
    }

    ui = createUI(S, {
      save,
      close: shutdown,
      redraw: () => render(),
      styleChanged: () => recompute(false),
      elo: () => curElo(),
      speed: () => curSpeed(),
      autoEloChanged: () => {
        refreshAutoElo(); save();
        clearTimeout(S.eloTimer); S.eloTimer = setTimeout(() => recompute(false), 200);
      },
      speedChanged: () => recompute(true),
      autoMoveChanged: () => {
        clearTimeout(S.am.timer);
        S.am = { fen: '', move: '', timer: 0, done: false };
        if (S.settings.autoMove && S.last && !S.last.pre) render();
      },
      autoSpeedChanged: () => { refreshAutoSpeed(); save(); recompute(true); },
      eloChanged: () => { clearTimeout(S.eloTimer); S.eloTimer = setTimeout(() => recompute(false), 350); },
      premoveChanged: () => {
        S.preMiss = false;
        if (S.dead || !S.me || !S.turn || S.turn === S.me) return;
        if (S.settings.premove) {
          if (S.spec && S.spec.first) { S.last = S.spec.first; render(); }
          else if (!S.spec) { cancelAnalysis(); speculate(S.reqId); }
          else { ui.setSuggestion('—', "Opponent's turn. Predicting their move…"); status('warn', "Predicting the opponent's move…"); }
        } else if (S.last && S.last.pre) {
          clearArrowsNow(); S.last = null;
          ui.setSuggestion('—', "Opponent's turn"); status('ok', "Opponent's turn.");
        }
      },
    });
    S.dbg.engine = engineLabel();
    status('warn', 'Starting…');
    pingBridge();
    if (pageKind() === 'game') preloadBuiltin();
    S.tickTimer = setInterval(tick, 400);
    S.clockTimer = setInterval(syncTurn, CFG.clockPollMs);
    tick();

  }

  init();
})();
