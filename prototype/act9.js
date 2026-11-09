// =====================================================================
//  Act 9: The Divided Mill (rational expressions and equations)
// =====================================================================
// Stage 39   Simplify rational expressions   (x² − 9)/(x + 3), (3x + 6)/(x² + 2x), (x² − 4)/(2 − x), 6x³/(9x)
// Stage 40   Multiply and divide              (x/3) ÷ (x²/6), (x² − 9)/(2x) · 4x/(x + 3)
// Stage 41   Add and subtract                 1/x + 1/(x + 1), 3/(x − 2) − 1/(x + 2), x/3 + x/4
// Stage 42   Rational equations               3/x + 1/2 = 2, x/(x − 2) = 2/(x − 2) + 3 (with Check)
// Stage 43   Variation                        y varies inversely with x; y = 4 when x = 3
// Stage 43b  Rational inequalities            (x + 1)/(x − 2) > 0: critical points, test intervals
//
// States have their own kind, `k9`:
//   rs  one fraction { fr: { top, bot } } of factors. A factor is { t: 'l', a, b } (a·x + b), { t: 'k', v }
//       (a number), { t: 'x', e } (xᵉ) or { t: 'p', p } (a polynomial not factored yet). `ex` lists the
//       excluded values stamped so far: a factor can only cancel once its "x ≠ v" stamp is down.
//   rm  two fractions multiplied or divided { fs: [fr, fr], op: '*' | '/' }; becomes rs once multiplied across.
//   ra  two fractions added or subtracted { fs, op: '+' | '-' }; `res` is the combined fraction.
//   re  a rational equation: sides of terms { n: polynomial top, d: factors }; after "Multiply both sides
//       by the LCD" the sides are polynomials (`poly`). Clearing a variable bottom makes Check owed.
//   va  a variation problem, worked one step at a time (`ph`).
//   ri  a rational inequality: (top)/(bottom) rel c, then critical points, intervals tested, the graph.
// index.html switches to this engine (through kit9.js) for generators that return { r9 }.
'use strict';
(function () {
  const KT = window.KIT9;
  if (!KT) return;
  const { P, FN, chance, qid, isTutorial, lvl, supH, supT, XV, numH, parenF, frH, sgnJoin, ptrim, pdeg, pco, padd, pscale, psub, pmul, peval, pEq, P1, ptext,
    numberLine, nlWindow, W9, sym, rowEl, colEl, TOK, EQTOK, refOf, kickClass, clone, fNeg, fSub, fDiv, fEq, fz, fv, svgI } = KT;

  // ================================================================ factors
  const Lf = (a, b) => ({ t: 'l', a, b });
  const Kf = v => ({ t: 'k', v });
  const Xf = (e = 1) => ({ t: 'x', e });
  const Pf = p => ({ t: 'p', p: ptrim(p.map(FN)) });
  const polyOf = f => (f.t === 'l' ? P1(f.a, f.b) : f.t === 'k' ? [F(f.v)] : f.t === 'x' ? [...Array(f.e).fill(F(0)), F(1)] : f.p);
  const prodPoly = fs => fs.reduce((a, f) => pmul(a, polyOf(f)), [F(1)]);
  const zeroOf = f => (f.t === 'l' ? F(-f.b, f.a) : f.t === 'x' ? F(0) : null);
  const keyF = f => (f.t === 'l' ? `l${f.a},${f.b}` : f.t === 'x' ? `x${f.e}` : f.t === 'k' ? `k${f.v}` : 'p' + JSON.stringify(f.p));
  const sameF = (f, g) => !!f && !!g && f.t === g.t && (f.t === 'l' ? f.a === g.a && f.b === g.b : f.t === 'x' ? true : f.t === 'k' ? f.v === g.v : pEq(f.p, g.p));
  const oppF = (f, g) => f.t === 'l' && g.t === 'l' && f.a === -g.a && f.b === -g.b;
  const sameList = (a, b) => { const ka = a.map(keyF).sort(), kb = b.map(keyF).sort(); return ka.length === kb.length && ka.every((k, i) => k === kb[i]); };
  // The whole factored form of a polynomial with whole coefficients (quadratics have whole roots once the
  // common factor is out): 2x² − 18 -> 2 · (x − 3)(x + 3), x² + 5x -> x(x + 5), 3x + 6 -> 3(x + 2).
  function factorize(p) {
    p = ptrim(p);
    const nz = p.filter(c => !fz(c)).map(c => c.n);
    let g = nz.reduce((a, b) => gcd(a, b), 0) || 1;
    if (p[p.length - 1].n < 0) g = -g;
    let q = p.map(c => F(c.n / g));
    const out = [];
    if (g !== 1) out.push(Kf(g));
    let xe = 0; while (q.length > 1 && fz(q[0])) { q = q.slice(1); xe++; }
    if (xe) out.push(Xf(xe));
    if (q.length === 2) out.push(Lf(q[1].n, q[0].n));
    else if (q.length === 3) {
      const rs = intRoots(q);
      if (rs) rs.forEach(r => out.push(Lf(1, -r)));
      else out.push(Pf(q));
    }
    return out;
  }
  function intRoots(q) {   // whole roots of x² + bx + c (leading 1), biggest first, or null
    if (q.length !== 3 || !fIs(q[2], 1)) return null;
    for (let r = -80; r <= 80; r++) {
      if (!fz(peval(q, F(r)))) continue;
      const o = fNeg(q[1]).n - r;
      if (pEq(pmul(P1(1, -r), P1(1, -o)), q)) return [r, o].sort((a, b) => b - a);
    }
    return null;
  }
  // A side: numbers first (multiplied together), then x, then the brackets.
  function tidySide(fs, keepOne) {
    let k = 1, xe = 0; const rest = [];
    for (const f of fs) { if (f.t === 'k') k *= f.v; else if (f.t === 'x') xe += f.e; else rest.push(f); }
    const out = [];
    if (k !== 1 || (keepOne && !xe && !rest.length)) out.push(Kf(k));
    if (xe) out.push(Xf(xe));
    return out.concat(rest);
  }
  const kOf = fs => fs.filter(f => f.t === 'k').reduce((a, f) => a * f.v, 1);
  function tidyFr(fr) {
    fr.top = tidySide(fr.top); fr.bot = tidySide(fr.bot);
    const kb = kOf(fr.bot);
    if (kb < 0) { fr.bot = tidySide([...fr.bot, Kf(-1)]); fr.top = tidySide([...fr.top, Kf(-1)]); }
    // x on top and bottom only cancels by the player's move (it may need its stamp)
    return fr;
  }
  // ---------------------------------------------------------------- text
  function facH(f, html, wrap) {
    const X = html ? XV() : 'x';
    if (f.t === 'k') return numText(f.v);
    if (f.t === 'x') return X + (f.e > 1 ? (html ? supH(f.e) : supT(f.e)) : '');
    const body = f.t === 'p' ? ptext(f.p, html) : linH(f.a, f.b, html);
    return wrap ? `(${body})` : body;
  }
  // a·x + b, written "2 − x" when x is negative and the number positive
  function linH(a, b, html) {
    const X = html ? XV() : 'x';
    if (a < 0 && b > 0) return `${b} ${MINUS} ${a === -1 ? '' : -a}${X}`;
    return ptext(P1(a, b), html);
  }
  function sideH(fs, html) {   // a product of factors: 3x(x + 2)(x − 1); −(x + 2); 1 when empty
    if (!fs.length) return '1';
    const many = fs.length > 1;
    return fs.map((f, i) => {
      if (f.t === 'k' && f.v === -1 && many) return MINUS;
      if (f.t === 'k') return numText(f.v);
      return facH(f, html, many && (f.t === 'l' || f.t === 'p') && !(fs.length === 2 && fs[0].t === 'k' && fs[0].v === -1 && false));
    }).join('');
  }
  const wrapT = (fs, t) => (fs.length > 1 || / /.test(t) ? `(${t})` : t);
  const frText = (fr, html) => (!fr.bot.length ? sideH(fr.top, html) : html ? frH(sideH(fr.top, true), sideH(fr.bot, true)) : `${wrapT(fr.top, sideH(fr.top, false))}/${wrapT(fr.bot, sideH(fr.bot, false))}`);
  const exText = (ex, html) => (ex.length ? `${html ? XV() : 'x'} ≠ ${ex.map(v => numH(v, html)).join(', ')}` : '');

  // ================================================================ rs: one fraction (stage 39)
  const rsState = (top, bot, o = {}) => ({ k9: 'rs', fr: tidyFr({ top, bot }), ex: o.ex || [], skill: o.skill || 'ratsimp', qid: qid() });
  const stamped = (e, f) => e.ex.some(v => fEq(v, zeroOf(f)));
  function frMoves(e, fr, pre) {
    const out = [];
    fr.bot.forEach((f, j) => { if (f.t === 'p') out.push({ op: 'fac9', refs: [pre + 'b' + j], fs: factorize(f.p) }); });
    fr.top.forEach((f, i) => { if (f.t === 'p') out.push({ op: 'fac9', refs: [pre + 't' + i], fs: factorize(f.p) }); });
    return out;
  }
  function rsMoves(e) {
    const fr = e.fr, out = frMoves(e, fr, '');
    fr.top.forEach((f, i) => fr.bot.forEach((g, j) => {
      if (oppF(f, g)) { const neg = f.a < 0 ? 't' + i : 'b' + j; if (!out.some(m => m.op === 'neg9' && m.refs[0] === neg)) out.push({ op: 'neg9', refs: [neg] }); }
    }));
    const stampsOwed = new Set();
    fr.top.forEach((f, i) => fr.bot.forEach((g, j) => {
      if ((f.t !== 'l' && f.t !== 'x') || !sameF(f, g)) return;
      if (stamped(e, g)) out.push({ op: 'can9', refs: ['t' + i, 'b' + j], ti: i, bj: j });
      else if (!stampsOwed.has(j)) { stampsOwed.add(j); out.push({ op: 'ex9', refs: ['b' + j], v: zeroOf(g) }); }
    }));
    const kt = kOf(fr.top), kb = kOf(fr.bot), g = gcd(kt, kb);
    if (fr.bot.length && g > 1) out.push({ op: 'red9', refs: ['bar'], d: g });
    // canonical order: factor, then stamp/cancel in place order, then reduce numbers
    const rank = { fac9: 0, neg9: 1, ex9: 2, can9: 2, red9: 3 };
    return out.sort((a, b) => rank[a.op] - rank[b.op]);
  }
  const facAt = (fr, ref) => { const m = /([tb])(\d+)$/.exec(ref || ''); if (!m) return null; return (m[1] === 't' ? fr.top : fr.bot)[+m[2]] || null; };
  function setFac(fr, ref, fs) {
    const m = /([tb])(\d+)$/.exec(ref); const side = m[1] === 't' ? 'top' : 'bot', i = +m[2];
    fr[side] = [...fr[side].slice(0, i), ...fs, ...fr[side].slice(i + 1)];
  }
  function applyFr(fr, e, m, c, ref) {
    switch (m.op) {
      case 'fac9': setFac(fr, ref, clone(c.fs)); break;
      case 'neg9': { const f = facAt(fr, ref); setFac(fr, ref, [Kf(-1), Lf(-f.a, -f.b)]); break; }
      case 'ex9': if (!e.ex.some(v => fEq(v, c.v))) e.ex.push(clone(c.v)); break;
      case 'can9': {
        const f = fr.top[m.ti], g = fr.bot[m.bj];
        if (f.t === 'x') { const k = Math.min(f.e, g.e); f.e -= k; g.e -= k; fr.top = fr.top.filter(x => x.t !== 'x' || x.e > 0); fr.bot = fr.bot.filter(x => x.t !== 'x' || x.e > 0); }
        else { fr.top.splice(m.ti, 1); fr.bot.splice(m.bj, 1); }
        break;
      }
      case 'red9': {
        const d = c.d, kt = kOf(fr.top), kb = kOf(fr.bot);
        fr.top = [...fr.top.filter(f => f.t !== 'k'), Kf(kt / d)]; fr.bot = [...fr.bot.filter(f => f.t !== 'k'), Kf(kb / d)];
        break;
      }
    }
    return tidyFr(fr);
  }

  // ================================================================ rm: multiply and divide (stage 40)
  const rmState = (f0, f1, op, o = {}) => ({ k9: 'rm', fs: [tidyFr(f0), tidyFr(f1)], op, ex: [], skill: o.skill || 'ratmul', qid: qid() });
  function rmMoves(e) {
    const out = [];
    if (e.op === '/') out.push({ op: 'flip9', refs: ['F1'] });
    else out.push({ op: 'mrg9', both: true });
    e.fs.forEach((fr, i) => out.push(...frMoves(e, fr, 'F' + i)));
    return out;
  }

  // ================================================================ ra: add and subtract (stage 41)
  const raState = (f0, f1, op, o = {}) => ({ k9: 'ra', fs: [f0, f1].map(f => ({ top: tidySide(f.top, true), bot: tidySide(f.bot) })), op, res: null,
    orig: [f0, f1].map(f => prodPoly(f.top)), skill: o.skill || 'ratadd', qid: qid() });
  // The least common denominator of factored bottoms: each bracket as often as it is needed, x to the
  // highest power, and the least common multiple of the numbers.
  function lcdOf(bots) {
    let k = 1, xe = 0; const need = {};
    for (const b of bots) {
      const cnt = {};
      for (const f of b) {
        if (f.t === 'k') k = k * Math.abs(f.v) / gcd(k, Math.abs(f.v));
        else if (f.t === 'x') xe = Math.max(xe, f.e);
        else { const kk = keyF(f); cnt[kk] = (cnt[kk] || 0) + 1; need[kk] = need[kk] || { f, n: 0 }; }
      }
      for (const [kk, n] of Object.entries(cnt)) need[kk].n = Math.max(need[kk].n, n);
    }
    const out = [];
    if (k > 1) out.push(Kf(k));
    if (xe) out.push(Xf(xe));
    for (const { f, n } of Object.values(need)) for (let i = 0; i < n; i++) out.push(clone(f));
    return out;
  }
  function missing(bot, lcd) {   // what bot needs to become the LCD
    const out = [], have = {};
    let kb = 1, xb = 0;
    for (const f of bot) { if (f.t === 'k') kb *= f.v; else if (f.t === 'x') xb += f.e; else have[keyF(f)] = (have[keyF(f)] || 0) + 1; }
    const kl = kOf(lcd), xl = lcd.filter(f => f.t === 'x').reduce((a, f) => a + f.e, 0);
    if (kl / kb !== 1) out.push(Kf(kl / kb));
    if (xl > xb) out.push(Xf(xl - xb));
    for (const f of lcd) if (f.t === 'l' || f.t === 'p') { const kk = keyF(f); if (have[kk]) have[kk]--; else out.push(clone(f)); }
    return out;
  }
  const sameBot = (a, b) => sameList(tidySide(a), tidySide(b));
  function raMoves(e) {
    if (e.res) return [];
    const out = [];
    e.fs.forEach((fr, i) => fr.bot.forEach((f, j) => { if (f.t === 'p') out.push({ op: 'fac9', refs: ['F' + i + 'b' + j], fs: factorize(f.p) }); }));
    if (out.length) return out;
    if (sameBot(e.fs[0].bot, e.fs[1].bot)) return [{ op: 'cmb9', both: true, p: combined(e) }];
    const lcd = lcdOf(e.fs.map(f => f.bot));
    e.fs.forEach((fr, i) => { const m = missing(fr.bot, lcd); if (m.length) out.push({ op: 'lcd9', refs: ['F' + i], m }); });
    return out;
  }
  const combined = e => padd(prodPoly(e.fs[0].top), pscale(prodPoly(e.fs[1].top), e.op === '-' ? F(-1) : F(1)));

  // ================================================================ re: rational equations (stage 42)
  const Tm = (n, d = []) => ({ n: ptrim((Array.isArray(n) ? n : [n]).map(FN)), d });
  const reState = (L, R, o = {}) => ({ k9: 're', L, R, poly: false, ck: false, orig: clone({ L, R }), cands: null, pend: null, skill: o.skill || 'rateq', qid: qid() });
  const termsBots = e => [...e.L, ...e.R].map(t => t.d).filter(d => d.length);
  const reDone = e => (!!e.cands && !e.pend && e.cands.every(c => c.st !== 'open')) || (e.poly && !e.ck && !e.cands && isXalone(e));
  const isXalone = e => pdeg(e.L) === 1 && fIs(pco(e.L, 1), 1) && fz(pco(e.L, 0)) && pdeg(e.R) === 0;
  function reMoves(e) {
    if (reDone(e)) return [];
    if (e.cands) {
      if (e.pend) return [{ op: e.pend.ok ? 'keep9' : 'rej9', both: true }];
      return e.cands.filter(c => c.st === 'open').map(c => ({ op: 'chk9', refs: ['O'], v: c.v }));
    }
    if (!e.poly) {
      const out = [];
      ['L', 'R'].forEach(s => e[s].forEach((t, i) => t.d.forEach((f, j) => { if (f.t === 'p') out.push({ op: 'fac9', refs: [s + i + 'b'], fs: factorize(f.p), side: s, i, j }); })));
      if (out.length) return out;
      return [{ op: 'lcd9e', both: true, m: lcdOf(termsBots(e)) }];
    }
    const L = e.L, R = e.R, deg = Math.max(pdeg(L), pdeg(R));
    if (deg === 2) {
      if (!(pdeg(R) === 0 && fz(pco(R, 0)))) return [{ op: 'zero9', both: true, p: R }];
      const rs = intRoots(L);
      if (rs && !e.fac) return [{ op: 'facq9', refs: ['L'], r1: F(rs[0]), r2: F(rs[1]) }];
      if (e.fac) return [{ op: 'zp9', both: true }];
      return [];
    }
    if (!fz(pco(R, 1))) return [{ op: 'asx9', both: true, n: fNeg(pco(R, 1)) }];
    if (!fz(pco(L, 0))) return [{ op: 'as9', both: true, n: fNeg(pco(L, 0)) }];
    if (!fIs(pco(L, 1), 1)) return [{ op: 'dv9', both: true, n: pco(L, 1) }];
    return [];
  }
  function sideAt(ts, v) {   // a side of the original worked out at x = v: { val, undef, parts }
    let val = F(0), undef = false;
    for (const t of ts) {
      const top = peval(t.n, v), bot = t.d.length ? peval(prodPoly(t.d), v) : F(1);
      if (fz(bot)) { undef = true; continue; }
      val = fAdd(val, fDiv(top, bot));
    }
    return { val, undef };
  }
  function checkAt(e, v) {
    const l = sideAt(e.orig.L, v), r = sideAt(e.orig.R, v);
    return { v, l, r, ok: !l.undef && !r.undef && fEq(l.val, r.val) };
  }
  function applyRe(r, m, c) {
    switch (m.op) {
      case 'fac9': { const t = r[m.side][m.i]; t.d = [...t.d.slice(0, m.j), ...clone(c.fs), ...t.d.slice(m.j + 1)]; t.d = tidySide(t.d); break; }
      case 'lcd9e': {
        const lcd = c.m;
        const side = ts => ts.reduce((a, t) => padd(a, pmul(t.n, prodPoly(missing(t.d, lcd)))), [F(0)]);
        r.ck = lcd.some(f => f.t !== 'k');
        r.L = side(r.L); r.R = side(r.R); r.poly = true; r.lcd = lcd;
        break;
      }
      case 'zero9': r.L = psub(r.L, r.R); r.R = [F(0)]; break;
      case 'facq9': r.fac = [m.r1, m.r2]; break;
      case 'zp9': { const rs = r.fac.slice().sort((a, b) => fv(a) - fv(b)); r.cands = rs.filter((v, i) => !i || !fEq(v, rs[0])).map(v => ({ v, st: 'open' })); break; }
      case 'asx9': { const k = [F(0), c.n]; r.L = padd(r.L, k); r.R = padd(r.R, k); break; }
      case 'as9': r.L = padd(r.L, [c.n]); r.R = padd(r.R, [c.n]); break;
      case 'dv9': r.L = pscale(r.L, fDiv(F(1), c.n)); r.R = pscale(r.R, fDiv(F(1), c.n)); break;
      case 'chk9': r.pend = checkAt(r, c.v); r.pend.i = r.cands.findIndex(o => fEq(o.v, c.v)); break;
      case 'keep9': case 'rej9': r.cands[r.pend.i].st = m.op === 'keep9' ? 'keep' : 'rej'; r.pend = null; break;
    }
    if (r.poly && r.ck && !r.cands && isXalone(r)) r.cands = [{ v: pco(r.R, 0), st: 'open' }];
    return r;
  }
  function reAnswer(e, html) {
    const X = html ? XV() : 'x';
    if (e.cands) { const kept = e.cands.filter(c => c.st === 'keep'); return kept.length ? kept.map(c => `${X} = ${numH(c.v, html)}`).join(' or ') : 'No solution'; }
    return `${X} = ${numH(pco(e.R, 0), html)}`;
  }

  // ================================================================ va: variation (stage 43)
  // kind: direct y = kx, inverse y = k/x, square y = kx², joint y = kxz. find: 'y' or 'x'.
  const vaState = (kind, known, q, o = {}) => ({ k9: 'va', kind, known, q, ph: 'form', k: null, skill: o.skill || 'vary', qid: qid() });
  const kFactor = (kind, v) => (kind === 'square' ? v.x * v.x : kind === 'joint' ? v.x * v.z : v.x);
  function vaMoves(e) {
    switch (e.ph) {
      case 'form': return [{ op: 'form9', both: true, f: e.kind }];
      case 'plug': return [{ op: 'plug9', both: true, sw: false }];
      case 'k': return [{ op: 'kdv9', both: true, how: e.kind === 'inverse' ? 'mul' : 'div', n: F(kFactor(e.kind, e.known)) }];
      case 'rew': return [{ op: 'rew9', both: true }];
      case 'q': return [{ op: 'plq9', both: true, v: e.q.find }];
      case 'ev': return [{ op: 'ev9', both: true }];
      case 'mx': return [{ op: 'mx9', both: true }];
      case 'div2': return [{ op: 'kdv9', both: true, how: 'div', n: e.kind === 'inverse' ? F(e.q.y) : e.k }];
    }
    return [];
  }
  function applyVa(r, m, c) {
    switch (m.op) {
      case 'form9': r.ph = 'plug'; break;
      case 'plug9': r.ph = 'k'; break;
      case 'kdv9':
        if (r.ph === 'k') { const n = F(kFactor(r.kind, r.known)); r.k = r.kind === 'inverse' ? fMul(F(r.known.y), n) : fDiv(F(r.known.y), n); r.ph = 'rew'; }
        else r.ph = 'done';
        break;
      case 'rew9': r.ph = 'q'; break;
      case 'plq9': r.ph = r.q.find === 'y' ? 'ev' : r.kind === 'inverse' ? 'mx' : 'div2'; break;
      case 'ev9': r.ph = 'done'; break;
      case 'mx9': r.ph = 'div2'; break;
    }
    return r;
  }
  const vaAns = e => (e.q.find === 'y' ? (e.kind === 'inverse' ? fDiv(e.k, F(e.q.x)) : fMul(e.k, F(kFactor(e.kind, e.q)))) : e.kind === 'inverse' ? fDiv(e.k, F(e.q.y)) : fDiv(F(e.q.y), e.k));
  const FORMS = { direct: 'y = kx', inverse: 'y = k/x', square: 'y = kx²', joint: 'y = kxz' };
  function formH(f, kv, html = true) {
    const X = XV(), Y = XV('y'), Z = XV('z'), k = kv ? numH(kv, true) : XV('k');
    switch (f) {
      case 'direct': return `${Y} = ${k}${kv ? ' · ' : ''}${X}`;
      case 'inverse': return `${Y} = ${frH(k, X)}`;
      case 'square': return `${Y} = ${k}${kv ? ' · ' : ''}${X}${supH(2)}`;
      case 'joint': return `${Y} = ${k}${kv ? ' · ' : ''}${X}${Z}`;
      case 'sum': return `${Y} = ${k} + ${X}`;
    }
    return '';
  }
  const vaWords = e => {
    const how = { direct: 'varies directly with <i>x</i>', inverse: 'varies inversely with <i>x</i>', square: 'varies directly with the square of <i>x</i>', joint: 'varies jointly with <i>x</i> and <i>z</i>' }[e.kind];
    const kn = `<i>y</i> = ${numText(e.known.y)} when <i>x</i> = ${numText(e.known.x)}${e.kind === 'joint' ? ` and <i>z</i> = ${numText(e.known.z)}` : ''}`;
    const ask = e.q.find === 'y' ? `Find <i>y</i> when <i>x</i> = ${numText(e.q.x)}${e.kind === 'joint' ? ` and <i>z</i> = ${numText(e.q.z)}` : ''}.` : `Find <i>x</i> when <i>y</i> = ${numText(e.q.y)}.`;
    return `<i>y</i> ${how}. ${kn}. ${ask}`;
  };
  function vaLine(e) {   // the equation on screen at each step
    const X = XV(), Y = XV('y'), K_ = XV('k'), n = v => numText(v);
    const kn = e.known, q = e.q;
    switch (e.ph) {
      case 'form': return `${Y} = ?`;
      case 'plug': return formH(e.kind);
      case 'k': return e.kind === 'inverse' ? `${n(kn.y)} = ${frH(K_, n(kn.x))}` : `${n(kn.y)} = ${K_} · ${n(kFactor(e.kind, kn))}`;
      case 'rew': return `${K_} = ${numH(e.k, true)}`;
      case 'q': return formH(e.kind, e.k);
      case 'ev': return e.kind === 'inverse' ? `${Y} = ${frH(numH(e.k, true), n(q.x))}` : `${Y} = ${numH(e.k, true)} · ${n(kFactor(e.kind, q))}`;
      case 'mx': return `${n(q.y)} = ${frH(numH(e.k, true), X)}`;
      case 'div2': return e.kind === 'inverse' ? `${n(q.y)}${X} = ${numH(e.k, true)}` : `${n(q.y)} = ${numH(e.k, true)}${X}`;
      case 'done': return `${q.find === 'y' ? Y : X} = ${numH(vaAns(e), true)}`;
    }
    return '';
  }

  // ================================================================ ri: rational inequalities (stage 43b)
  // top a·x + b, bottom x − q; rel; c on the right (0 once moved). ph: move, comb, crit, test, graph, done.
  const riState = (top, bot, rel, c, o = {}) => ({ k9: 'ri', top, bot, rel, c: FN(c), ph: fz(FN(c)) ? 'crit' : 'move', pts: null, tests: [], pend: null, gr: null,
    skill: o.skill || 'ratineq', qid: qid() });
  const strict = rel => rel === '<' || rel === '>';
  const holds = (v, rel) => (rel === '>' ? v > 0 : rel === '<' ? v < 0 : rel === '≥' ? v >= 0 : v <= 0);
  const critOf = e => { const out = []; if (e.top.a) out.push({ x: F(-e.top.b, e.top.a), top: true }); out.push({ x: F(-e.bot.b, e.bot.a), top: false }); return out.sort((a, b) => fv(a.x) - fv(b.x)); };
  const ivsOf = pts => pts.map((p, i) => [i ? pts[i - 1].x : null, p.x]).concat([[pts[pts.length - 1].x, null]]);
  function testVal(iv) {
    const [a, b] = iv;
    if (a === null) return F(Math.floor(fv(b)) - (Number.isInteger(fv(b)) ? 1 : 0));
    if (b === null) return F(Math.ceil(fv(a)) + (Number.isInteger(fv(a)) ? 1 : 0));
    const lo = Math.floor(fv(a)) + 1;
    return lo < fv(b) ? F(lo) : fDiv(fAdd(a, b), F(2));
  }
  const riVal = (e, v) => fDiv(fAdd(fMul(F(e.top.a), v), F(e.top.b)), fAdd(fMul(F(e.bot.a), v), F(e.bot.b)));
  const riTruth = e => { const pts = critOf(e); return { pts, sh: ivsOf(pts).map(iv => holds(fv(riVal(e, testVal(iv))), e.rel)), cl: pts.map(p => p.top && !strict(e.rel)) }; };
  function riMoves(e) {
    switch (e.ph) {
      case 'move': return [{ op: 'zri9', both: true, n: fNeg(e.c) }];
      case 'comb': return [{ op: 'cri9', both: true, p: riNewTop(e) }];
      case 'crit': return [{ op: 'crit9', refs: ['Q'], xs: critOf(e).map(p => p.x) }];
      case 'test':
        if (e.pend) return [{ op: e.pend.ok ? 'tt9' : 'tf9', both: true }];
        return ivsOf(e.pts).map((iv, i) => (e.tests.some(t => t.i === i) ? null : { op: 'test9', refs: ['I' + i], i })).filter(Boolean);
      case 'graph': { const t = riTruth(e); return [{ op: 'gr9', both: true, sh: t.sh, cl: t.cl }]; }
    }
    return [];
  }
  const riNewTop = e => psub(P1(e.top.a, e.top.b), pscale(P1(e.bot.a, e.bot.b), e.c));
  function applyRi(r, m, c) {
    switch (m.op) {
      case 'zri9': r.ph = 'comb'; break;
      case 'cri9': { const p = riNewTop(r); r.top = { a: pco(p, 1).n, b: pco(p, 0).n }; r.c = F(0); r.ph = 'crit'; break; }
      case 'crit9': r.pts = critOf(r); r.ph = 'test'; break;
      case 'test9': { const iv = ivsOf(r.pts)[m.i], v = testVal(iv), val = riVal(r, v); r.pend = { i: m.i, x: v, val, ok: holds(fv(val), r.rel) }; break; }
      case 'tt9': case 'tf9': r.tests.push({ ...r.pend, said: m.op === 'tt9' }); r.pend = null; if (r.tests.length === ivsOf(r.pts).length) r.ph = 'graph'; break;
      case 'gr9': r.gr = { sh: clone(c.sh), cl: clone(c.cl) }; r.ph = 'done'; break;
    }
    return r;
  }
  function riAnswer(e, html) {
    const t = riTruth(e), X = html ? XV() : 'x', ivs = ivsOf(t.pts);
    const rel = (i, lower) => (t.cl[i] ? (lower ? '≥' : '≤') : lower ? '>' : '<');
    const parts = [];
    ivs.forEach((iv, i) => {
      if (!t.sh[i]) return;
      if (iv[0] === null) parts.push(`${X} ${rel(i, false)} ${numH(iv[1], html)}`);
      else if (iv[1] === null) parts.push(`${X} ${rel(i - 1, true)} ${numH(iv[0], html)}`);
      else parts.push(`${numH(iv[0], html)} ${rel(i - 1, false).replace('≥', '≤').replace('>', '<')} ${X} ${rel(i, false)} ${numH(iv[1], html)}`);
    });
    return parts.join(' or ') || 'No solution';
  }
  const riLine = (e, html = true) => {
    const top = ptext(P1(e.top.a, e.top.b), html), bot = ptext(P1(e.bot.a, e.bot.b), html);
    const fr = html ? frH(top, bot) : `(${top})/(${bot})`;
    if (e.ph === 'move') return `${fr} ${e.rel} ${numH(e.c, html)}`;
    if (e.ph === 'comb') return `${fr} ${MINUS} ${numH(e.c, html)} ${e.rel} 0`;
    return `${fr} ${e.rel} 0`;
  };
  function riNl(e, extra = {}) {
    const pts = e.pts || critOf(e), xs = pts.map(p => fv(p.x)), w = nlWindow(xs);
    const ivs = ivsOf(pts);
    const show = { lo: w.lo, hi: w.hi, ivs, targets: e.ph === 'test' && !e.pend, labels: true,
      pts: pts.map((p, i) => ({ x: fv(p.x), open: e.gr ? !e.gr.cl[i] : true, lab: fracText(p.x) })),
      tests: [...e.tests.map(t => ({ x: fv(t.x), ok: t.ok })), ...(e.pend ? [{ x: fv(e.pend.x) }] : [])],
      shade: e.gr ? ivs.map((iv, i) => (e.gr.sh[i] ? [iv[0] === null ? null : fv(iv[0]), iv[1] === null ? null : fv(iv[1])] : null)).filter(Boolean) : [] };
    show.ivs = ivs.map((iv, i) => { const a = [iv[0] === null ? null : fv(iv[0]), iv[1] === null ? null : fv(iv[1])]; a.cls = e.tests.some(t => t.i === i) ? 'done9' : ''; return a; });
    return numberLine({ ...show, ...extra });
  }

  // ================================================================ moves, cards
  const BOTH = new Set(['mrg9', 'cmb9', 'lcd9e', 'zero9', 'zp9', 'asx9', 'as9', 'dv9', 'keep9', 'rej9', 'form9', 'plug9', 'kdv9', 'rew9', 'plq9', 'ev9', 'mx9', 'zri9', 'cri9', 'tt9', 'tf9', 'gr9']);
  const COPY = new Set(['rew9', 'form9', 'flip9', 'plq9', 'crit9', 'test9', 'gr9', 'ex9', 'zri9', 'neg9']);
  const PARAMS = ['fs', 'v', 'd', 'm', 'p', 'n', 'r1', 'r2', 'f', 'sw', 'how', 'xs', 'sh', 'cl'];
  function moves(e) {
    switch (e.k9) {
      case 'rs': return rsMoves(e);
      case 'rm': return rmMoves(e);
      case 'ra': return raMoves(e);
      case 're': return reMoves(e);
      case 'va': return vaMoves(e);
      case 'ri': return riMoves(e);
    }
    return [];
  }
  const sameVals = (a, b) => a.length === b.length && a.map(fv).sort().every((v, i) => Math.abs(v - b.map(fv).sort()[i]) < 1e-12);
  function ok(e, m, c, ref) {
    switch (c.op) {
      case 'fac9': return !!c.fs && sameList(c.fs, m.fs);
      case 'ex9': return !!c.v && fEq(c.v, m.v);
      case 'red9': return Number.isInteger(c.d) && c.d > 1 && m.d % c.d === 0;
      case 'lcd9': return !!c.m && sameList(tidySide(c.m), tidySide(m.m));
      case 'lcd9e': return !!c.m && sameList(tidySide(c.m), tidySide(m.m));
      case 'cmb9': case 'cri9': return !!c.p && pEq(c.p, m.p);
      case 'zero9': return !!c.p && pEq(c.p, m.p);
      case 'facq9': return !!c.r1 && ((fEq(c.r1, m.r1) && fEq(c.r2, m.r2)) || (fEq(c.r1, m.r2) && fEq(c.r2, m.r1)));
      case 'as9': case 'asx9': case 'dv9': return !!c.n && fEq(c.n, m.n);
      case 'chk9': return !!c.v && fEq(c.v, m.v);
      case 'form9': return c.f === m.f;
      case 'plug9': return !c.sw;
      case 'kdv9': return c.how === m.how && !!c.n && fEq(c.n, m.n);
      case 'plq9': return c.v === m.v;
      case 'zri9': return !!c.n && fEq(c.n, m.n);
      case 'crit9': return !!c.xs && sameVals(c.xs, m.xs);
      case 'gr9': return !!c.sh && c.sh.every((v, i) => v === m.sh[i]) && c.cl.every((v, i) => v === m.cl[i]);
    }
    return true;
  }
  function apply(r, m, c, ref) {
    switch (r.k9) {
      case 'rs': return applyFr(r.fr, r, m, c, ref) && r;
      case 'rm': {
        if (m.op === 'flip9') { const f = r.fs[1]; r.fs[1] = tidyFr({ top: f.bot.length ? f.bot : [Kf(1)], bot: f.top }); r.op = '*'; r.fs[1].top = tidySide(r.fs[1].top, true); return r; }
        if (m.op === 'mrg9') return rsState([...r.fs[0].top, ...r.fs[1].top], [...r.fs[0].bot, ...r.fs[1].bot], { ex: r.ex, skill: r.skill });
        const i = +ref[1]; applyFr(r.fs[i], r, m, c, ref.slice(2)); return r;
      }
      case 'ra': {
        if (m.op === 'fac9') { const i = +ref[1]; const fr = r.fs[i], j = +ref.slice(3); fr.bot = tidySide([...fr.bot.slice(0, j), ...clone(c.fs), ...fr.bot.slice(j + 1)]); return r; }
        if (m.op === 'lcd9') { const fr = r.fs[+ref[1]]; fr.top = tidySide([...fr.top, ...clone(c.m)], true); fr.bot = tidySide([...fr.bot, ...clone(c.m)]); return r; }
        if (m.op === 'cmb9') { r.res = { top: combined(r), bot: tidySide(r.fs[0].bot) }; return r; }
        return r;
      }
      case 're': return applyRe(r, m, c);
      case 'va': return applyVa(r, m, c);
      case 'ri': return applyRi(r, m, c);
    }
    return r;
  }
  function answer(e, html) {
    switch (e.k9) {
      case 'rs': return '= ' + frText(e.fr, html) + (e.ex.length ? (html ? ', ' : ', ') + exText(e.ex, html) : '');
      case 'rm': return '';
      case 'ra': return e.res ? '= ' + (html ? frH(ptext(e.res.top, true), sideH(e.res.bot, true)) : `${wrapT([1], ptext(e.res.top))}/${wrapT(e.res.bot, sideH(e.res.bot, false))}`) : '';
      case 're': return reAnswer(e, html);
      case 'va': return `${e.q.find} = ${numH(vaAns(e), html)}`;
      case 'ri': return riAnswer(e, html);
    }
    return '';
  }

  // ---------------------------------------------------------------- card faces
  const signedN = (n, html) => (n.n < 0 ? MINUS : '+') + numH(fAbs(n), html);
  const facLabel = fs => sideH(tidySide(fs), true);
  const mulLabel = m => { const s = sideH(tidySide(m), true); return frH(s, s); };
  const CARD = {
    fac9:  c => ({ label: facLabel(c.fs), text: 'Factor it', kind: 'Factor', icon: 'fac9' }),
    ex9:   c => ({ label: `${XV()} ≠ ${numH(c.v, true)}`, text: 'Mark the excluded value (the bottom can\'t be 0)', kind: 'Mark excluded value', icon: 'ex9' }),
    neg9:  () => ({ label: `${MINUS}1 out`, text: 'Factor out −1: a − x = −(x − a)', kind: 'Factor out −1', icon: 'neg9' }),
    can9:  () => ({ label: 'Cancel', text: 'Cancel a common factor, top and bottom', kind: 'Cancel a common factor', icon: 'can9' }),
    red9:  c => ({ label: `${DIV} ${c.d}`, text: `Divide top and bottom by ${c.d}`, kind: 'Reduce the numbers', icon: 'div' }),
    flip9: () => ({ label: 'Flip and ×', text: 'Divide = multiply by the second fraction flipped over', kind: 'Flip and multiply', icon: 'flip9' }),
    mrg9:  () => ({ label: 'Multiply across', text: 'Tops times tops, bottoms times bottoms', kind: 'Multiply across', icon: 'mul' }),
    lcd9:  c => ({ label: `${TIMES} ${mulLabel(c.m)}`, text: `Build the common denominator: multiply top and bottom by ${sideH(tidySide(c.m), false)}`, kind: 'Build a common denominator', icon: 'lcd' }),
    cmb9:  c => ({ label: `Tops: ${ptext(c.p, true)}`, text: 'Same bottom: combine the tops', kind: 'Combine the tops', icon: 'comb' }),
    lcd9e: c => ({ label: `${TIMES} ${sideH(tidySide(c.m), true)}`, text: `Multiply both sides by the LCD, ${sideH(tidySide(c.m), false)}`, kind: 'Multiply by the LCD', icon: 'lcd' }),
    zero9: c => ({ label: `${MINUS} (${ptext(c.p, true)})`, text: `Subtract ${ptext(c.p)} from both sides`, kind: 'Get 0 on one side', icon: 'sub' }),
    facq9: c => ({ label: [c.r1, c.r2].map(r => `(${ptext(P1(1, fNeg(FN(r))), true)})`).join(''), text: 'Factor the quadratic', kind: 'Factor', icon: 'fac9' }),
    zp9:   () => ({ label: 'Zero product', text: 'Set each factor equal to 0', kind: 'Zero product', icon: 'zp9' }),
    asx9:  c => ({ label: `${c.n.n < 0 ? MINUS : '+'}${ptext([F(0), fAbs(c.n)], true)}`, text: `${c.n.n < 0 ? 'Subtract' : 'Add'} ${ptext([F(0), fAbs(c.n)])} ${c.n.n < 0 ? 'from' : 'to'} both sides`, kind: 'Move the x term', icon: c.n.n < 0 ? 'sub' : 'add' }),
    as9:   c => ({ label: signedN(c.n, true), text: c.n.n < 0 ? `Subtract ${fracText(fAbs(c.n))} from both sides` : `Add ${fracText(c.n)} to both sides`, kind: c.n.n < 0 ? 'Subtract' : 'Add', icon: c.n.n < 0 ? 'sub' : 'add' }),
    dv9:   c => ({ label: `${DIV} ${parenF(c.n, true)}`, text: `Divide both sides by ${fracText(c.n)}`, kind: 'Divide', icon: 'div' }),
    chk9:  c => ({ label: `Check ${XV()} = ${numH(c.v, true)}`, text: 'Put it into the original equation', kind: 'Check an answer', icon: 'check8' }),
    keep9: () => ({ label: '✓ Keep', text: 'It works in the original: keep it', kind: 'Keep the answer', icon: 'keep8' }),
    rej9:  () => ({ label: '✗ Reject', text: 'It fails (or makes a bottom 0): reject it', kind: 'Reject the answer', icon: 'rej8' }),
    form9: c => ({ label: formH(c.f), text: { direct: 'Direct variation', inverse: 'Inverse variation', square: 'Varies with the square', joint: 'Joint variation', sum: 'Add a constant' }[c.f], kind: 'Pick the formula', icon: 'form9' }),
    plug9: c => ({ label: c.sw ? 'Swap them in' : 'Plug in', text: c.sw ? 'Put the x value in for y and the y value in for x' : 'Put the known x and y into the formula', kind: 'Plug in', icon: 'plug9' }),
    kdv9:  c => ({ label: `${c.how === 'mul' ? TIMES : DIV} ${parenF(c.n, true)}`, text: `${c.how === 'mul' ? 'Multiply' : 'Divide'} both sides by ${fracText(c.n)}`, kind: c.how === 'mul' ? 'Multiply' : 'Divide', icon: c.how === 'mul' ? 'mul' : 'div' }),
    rew9:  () => ({ label: 'Use k', text: 'Write the formula with the k you found', kind: 'Write the formula', icon: 'form9' }),
    plq9:  c => ({ label: `New ${c.v === 'y' ? 'x' : 'y'} in`, text: `Put in the new ${c.v === 'y' ? 'x' : 'y'} to find ${c.v}`, kind: 'Plug in', icon: 'plug9' }),
    ev9:   () => ({ label: 'Work it out', text: 'Do the arithmetic', kind: 'Work it out', icon: 'mul' }),
    mx9:   () => ({ label: `${TIMES} ${XV()}`, text: 'Multiply both sides by x', kind: 'Multiply by x', icon: 'mul' }),
    zri9:  c => ({ label: signedN(c.n, true), text: `${c.n.n < 0 ? 'Subtract' : 'Add'} ${fracText(fAbs(c.n))} ${c.n.n < 0 ? 'from' : 'to'} both sides: 0 on the right`, kind: 'Get 0 on one side', icon: c.n.n < 0 ? 'sub' : 'add' }),
    cri9:  c => ({ label: `Top: ${ptext(c.p, true)}`, text: 'Combine into one fraction', kind: 'Combine into one fraction', icon: 'comb' }),
    crit9: c => ({ label: `${XV()} = ${c.xs.map(v => numH(v, true)).join(', ')}`, text: 'Critical points: where the top or the bottom is 0', kind: 'Find the critical points', icon: 'crit9' }),
    test9: () => ({ label: 'Test', text: 'Test a number from one interval', kind: 'Test an interval', icon: 'test9' }),
    tt9:   () => ({ label: '✓ True', text: 'The inequality holds there', kind: 'True', icon: 'keep8' }),
    tf9:   () => ({ label: '✗ False', text: 'The inequality fails there', kind: 'False', icon: 'rej8' }),
    gr9:   c => ({ label: cardNl(c), text: 'Graph the solution', kind: 'Graph the solution', icon: 'graph3' }),
  };
  let cardPts = null;   // the critical points a graph card is drawn over (set while dealing)
  function cardNl(c) {
    const pts = cardPts || c.sh.map((_, i) => ({ x: F(i) })).slice(0, c.cl.length);
    const xs = pts.map(p => fv(p.x)), w = nlWindow(xs), ivs = ivsOf(pts);
    return numberLine({ lo: w.lo, hi: w.hi, labels: false, pts: pts.map((p, i) => ({ x: fv(p.x), open: !c.cl[i], lab: fracText(p.x) })),
      shade: ivs.map((iv, i) => (c.sh[i] ? [iv[0] === null ? null : fv(iv[0]), iv[1] === null ? null : fv(iv[1])] : null)).filter(Boolean) });
  }

  // ================================================================ decoys
  let A = null;   // the engine pieces (C, trap) once made
  const C9 = (op, o) => A.C(op, o);
  const T9 = (...a) => A.trap(...a);
  function specials(e) {
    const out = { rule: [], traps: [] };
    const ms = moves(e), has = op => ms.some(m => m.op === op), mv = op => ms.find(m => m.op === op);
    if (e.k9 === 'rs' || e.k9 === 'rm') {
      const fr = e.k9 === 'rs' ? e.fr : e.fs[0];
      const t0 = fr.top.find(f => f.t === 'p' || (f.t === 'l' && f.b)), b0 = fr.bot.find(f => f.t === 'p' || (f.t === 'l' && f.b));
      if (t0 && b0) out.rule.push(T9('cancel terms', 'can9', `Cancel ${XV()}`, 'Cross out an x on top and on the bottom',
        P(`You can only cancel <b>factors</b> (things multiplied), never <b>terms</b> (things added). In ${frText(fr, true)} the x is inside a sum, so it can't be crossed out on its own. (Try x = 2: (2 + 3)/(2 + 1) is 5/3, not 3/1.) Factor first, then cancel whole brackets that match.`), 'can9'));
      if (has('ex9')) {
        const m = mv('ex9');
        out.rule.push(C9('can9'));
        out.traps.push(T9('no restriction', 'ex9', 'No limit', 'It cancels away, so x can be anything',
          P(`The original expression has ${XV()} = ${numH(m.v, true)} make a bottom 0, so it's undefined there. Cancelling doesn't change that: the simplified form must carry <b>${XV()} ≠ ${numH(m.v, true)}</b> or it would claim a value where the original has none.`), 'ex9'));
      }
      if (has('flip9')) out.rule.push(T9('flip the first', 'flip9', 'Flip first', 'Flip the first fraction, then multiply',
        P('Dividing by a fraction means multiplying by its <b>reciprocal</b>: the <b>second</b> fraction (the divisor) flips over. The first stays as it is: a/b ÷ c/d = a/b · d/c.'), 'flip9'));
      if (has('mrg9') && e.k9 === 'rm') out.rule.push(T9('cross multiply', 'mrg9', 'Cross-multiply', 'Top of one times bottom of the other',
        P('Cross-multiplying is for solving an equation with one fraction on each side. To multiply two fractions, multiply straight across: tops times tops, bottoms times bottoms.'), 'mul', 'both'));
    }
    if (e.k9 === 'ra' && !e.res) {
      const [f0, f1] = e.fs;
      out.rule.push(T9('add the bottoms', 'cmb9', 'Add across', 'Add the tops and add the bottoms',
        P(`Fractions add only over the <b>same</b> bottom: 1/2 + 1/3 isn't 2/5. Build a common denominator first, then add the tops and keep the bottom.`), 'comb', 'both'));
      if (has('lcd9')) { const m = mv('lcd9'); out.rule.push(T9('top only', 'lcd9', `${TIMES} ${sideH(tidySide(m.m), true)} top`, `Multiply just the top by ${sideH(tidySide(m.m), false)}`,
        P('Multiplying only the top changes the fraction\'s value. Multiply the top <b>and</b> the bottom by the same thing: that is multiplying by 1.'), 'lcd')); }
      if (has('cmb9') && e.op === '-') { const p = padd(prodPoly(f0.top), prodPoly(f1.top).map((c, i) => (i === pdeg(prodPoly(f1.top)) ? fNeg(c) : c))); if (!pEq(p, combined(e))) out.rule.push(C9('cmb9', { p })); }
    }
    if (e.k9 === 're') {
      if (has('lcd9e')) {
        const m = mv('lcd9e');
        if (e.L.length + e.R.length > 2) out.rule.push(T9('fractions only', 'lcd9e', `${TIMES} LCD fractions`, 'Multiply only the fraction terms by the LCD',
          P(`Multiplying both sides means <b>every term</b> on both sides, whole numbers too. If 2 isn't multiplied by ${sideH(tidySide(m.m), true)}, the sides stop being equal.`), 'lcd', 'both'));
        if (e.L.length + e.R.length > 2) out.traps.push(T9('cross multiply', 'lcd9e', 'Cross-multiply', 'Top of each side times the other bottom',
          P('Cross-multiplying only works when each side is a single fraction. With more terms, multiply every term by the LCD.'), 'mul', 'both'));
      }
      if (e.cands && !e.pend) out.rule.push(T9('skip the check', 'chk9', 'Done!', 'The algebra is right, no check needed',
        P('Multiplying by an expression with x can bring in a <b>fake answer</b>: a number that makes a bottom 0 in the original, where the equation isn\'t even defined. Every answer has to be checked.'), 'keep8', 'both'));
    }
    if (e.k9 === 'va') {
      if (e.ph === 'plug') out.rule.push(C9('plug9', { sw: true }));
      if (e.ph === 'q') out.rule.push(C9('plq9', { v: e.q.find === 'y' ? 'x' : 'y' }));
    }
    if (e.k9 === 'ri' && (e.ph === 'move' || e.ph === 'comb' || e.ph === 'crit')) {
      out.rule.push(T9('multiply by the bottom', 'zri9', `${TIMES} (${ptext(P1(e.bot.a, e.bot.b), true)})`, `Multiply both sides by ${ptext(P1(e.bot.a, e.bot.b))}`,
        P(`You can't multiply an inequality by ${ptext(P1(e.bot.a, e.bot.b), true)}: you don't know if it's positive or negative, so you don't know whether to flip the sign. Instead find where the top and bottom are 0 and test each interval.`), 'mul', 'both'));
    }
    if (e.k9 === 'ri' && e.ph === 'graph') {
      const t = riTruth(e);
      if (t.pts.some(p => !p.top) && !strict(e.rel)) out.rule.push(C9('gr9', { sh: t.sh, cl: t.pts.map(() => true) }));
    }
    return out;
  }
  function wrongFacs(fs) {   // classic factoring slips: signs swapped, a square instead of a difference
    const ls = fs.filter(f => f.t === 'l'), rest = fs.filter(f => f.t !== 'l');
    const out = [];
    if (ls.length === 2) {
      out.push([...rest, ...ls.map(f => Lf(f.a, -f.b))]);
      out.push([...rest, Lf(1, ls[0].b), Lf(1, ls[0].b)]);
      out.push([...rest, Lf(1, ls[0].b + 1), Lf(1, ls[1].b - 1)]);
    }
    if (ls.length === 1) { out.push([...rest, Lf(ls[0].a, -ls[0].b)]); if (rest.length) out.push([Lf(ls[0].a, ls[0].b)]); }
    if (rest.some(f => f.t === 'k')) out.push(fs.filter(f => f.t !== 'k'));
    return out.filter(w => !sameList(w, fs));
  }
  function family(e) {
    const f = [], ms = moves(e);
    const facM = ms.find(m => m.op === 'fac9');
    if (facM) wrongFacs(facM.fs).forEach(w => f.push(C9('fac9', { fs: w })));
    if (e.k9 === 'rs' || e.k9 === 'rm') {
      const fr = e.k9 === 'rs' ? e.fr : e.fs[1];
      const g = fr.bot.find(x => x.t === 'l') || fr.top.find(x => x.t === 'l');
      if (g) { const z = zeroOf(g); f.push(C9('ex9', { v: fNeg(z) })); if (!fz(z)) f.push(C9('ex9', { v: z })); }
      f.push(C9('can9'), C9('neg9'), C9('red9', { d: 2 }), C9('red9', { d: 3 }));
      if (e.k9 === 'rm') f.push(C9('mrg9'), C9('flip9'));
      if (e.k9 === 'rs' && fr.bot.some(x => x.t === 'x')) f.push(C9('ex9', { v: F(1) }));
      return f;
    }
    if (e.k9 === 'ra') {
      const lcd = lcdOf(e.fs.map(x => x.bot));
      e.fs.forEach(fr => { fr.bot.forEach(b => f.push(C9('lcd9', { m: [b] }))); f.push(C9('lcd9', { m: lcd })); });
      f.push(C9('cmb9', { p: padd(prodPoly(e.fs[0].top), prodPoly(e.fs[1].top)) }), C9('cmb9', { p: padd(e.orig[0], pscale(e.orig[1], e.op === '-' ? F(-1) : F(1))) }));
      if (ms.some(m => m.op === 'cmb9')) { const p = ms[0].p; f.push(C9('cmb9', { p: padd(p, [F(1)]) }), C9('cmb9', { p: pscale(p, F(-1)) })); }
      return f;
    }
    if (e.k9 === 're') {
      if (e.cands) { e.cands.forEach(c => f.push(C9('chk9', { v: c.v }))); f.push(C9('keep9'), C9('rej9')); return f; }
      if (!e.poly) {
        const lcd = lcdOf(termsBots(e));
        termsBots(e).forEach(b => f.push(C9('lcd9e', { m: b })));
        if (lcd.length > 1) f.push(C9('lcd9e', { m: lcd.slice(1) }), C9('lcd9e', { m: lcd.slice(0, -1) }));
        f.push(C9('dv9', { n: F(2) }), C9('as9', { n: F(-1) }));
        return f;
      }
      const L = e.L, R = e.R;
      if (Math.max(pdeg(L), pdeg(R)) === 2) {
        if (!(pdeg(R) === 0 && fz(pco(R, 0)))) { f.push(C9('zero9', { p: pscale(R, F(-1)) }), C9('zero9', { p: [pco(R, 0)] }), C9('dv9', { n: F(2) })); return f; }
        const rs = intRoots(L) || [1, 2];
        f.push(C9('facq9', { r1: F(-rs[0]), r2: F(-rs[1]) }), C9('facq9', { r1: F(rs[0]), r2: F(-rs[1]) }), C9('facq9', { r1: F(rs[0] + 1), r2: F(rs[1] - 1) }), C9('zp9'));
        if (e.fac) f.push(C9('as9', { n: F(-1) }));
        return f;
      }
      const a1 = pco(L, 1), b1 = pco(L, 0), a2 = pco(R, 1);
      if (!fz(a2)) f.push(C9('asx9', { n: a2 }), C9('as9', { n: fNeg(b1.n ? b1 : F(1)) }));
      if (!fz(b1)) f.push(C9('as9', { n: b1 }), C9('dv9', { n: fz(a1) ? F(2) : a1 }));
      if (!fIs(a1, 1) && !fz(a1)) f.push(C9('dv9', { n: fNeg(a1) }), C9('as9', { n: fNeg(a1) }));
      f.push(C9('zp9'));
      return f;
    }
    if (e.k9 === 'va') {
      if (e.ph === 'form') ['direct', 'inverse', 'square', 'joint', 'sum'].forEach(x => f.push(C9('form9', { f: x })));
      const n = F(kFactor(e.kind, e.known));
      if (e.ph === 'k') f.push(C9('kdv9', { how: e.kind === 'inverse' ? 'div' : 'mul', n }), C9('kdv9', { how: 'div', n: F(e.known.y) }), C9('kdv9', { how: 'mul', n: F(e.known.y) }));
      if (e.ph === 'div2') { const n2 = e.kind === 'inverse' ? F(e.q.y) : e.k; f.push(C9('kdv9', { how: 'mul', n: n2 }), C9('kdv9', { how: 'div', n: e.kind === 'inverse' ? e.k : F(e.q.y) })); }
      f.push(C9('plug9'), C9('rew9'), C9('ev9'), C9('mx9'), C9('plq9', { v: 'y' }), C9('form9', { f: e.kind === 'direct' ? 'inverse' : 'direct' }));
      return f;
    }
    if (e.k9 === 'ri') {
      const pts = critOf(e).map(p => p.x);
      f.push(C9('crit9', { xs: pts.map(fNeg) }), C9('crit9', { xs: [pts.find((_, i) => critOf(e)[i].top) || pts[0]] }), C9('test9'), C9('tt9'), C9('tf9'), C9('zri9', { n: e.c }));
      if (e.ph === 'comb') f.push(C9('cri9', { p: psub(P1(e.top.a, e.top.b), [e.c]) }), C9('cri9', { p: padd(P1(e.top.a, e.top.b), pscale(P1(e.bot.a, e.bot.b), e.c)) }));
      if (e.ph === 'graph') {
        const t = riTruth(e);
        f.push(C9('gr9', { sh: t.sh.map(v => !v), cl: t.cl }), C9('gr9', { sh: t.sh, cl: t.cl.map(v => !v) }), C9('gr9', { sh: t.sh.map(v => !v), cl: t.cl.map(v => !v) }));
      }
      return f;
    }
    return f;
  }
  const filler = () => [2, 3, 5, 4, 6, 7].map(n => C9('as9', { n: F(n) }));
  function placesOf(e, op) {
    if (e.k9 === 'rs') {
      const all = [...e.fr.top.map((_, i) => 't' + i), ...e.fr.bot.map((_, j) => 'b' + j)];
      if (op === 'fac9' || op === 'neg9' || op === 'can9') return all;
      if (op === 'ex9') return e.fr.bot.map((_, j) => 'b' + j);
      if (op === 'red9') return e.fr.bot.length ? ['bar'] : [];
    }
    if (e.k9 === 'rm') { if (op === 'flip9') return ['F0', 'F1']; if (op === 'fac9' || op === 'ex9' || op === 'can9' || op === 'neg9') return e.fs.flatMap((fr, i) => [...fr.top.map((_, k) => `F${i}t${k}`), ...fr.bot.map((_, k) => `F${i}b${k}`)]); }
    if (e.k9 === 'ra') { if (op === 'lcd9') return e.res ? [] : ['F0', 'F1']; if (op === 'fac9') return e.res ? [] : e.fs.flatMap((fr, i) => fr.bot.map((_, k) => `F${i}b${k}`)); }
    if (e.k9 === 're') { if (op === 'chk9') return e.cands ? ['O'] : []; if (op === 'facq9') return e.poly && !e.cands ? ['L'] : []; }
    if (e.k9 === 'ri') { if (op === 'crit9') return ['Q']; if (op === 'test9') return e.ph === 'test' && e.pts ? ivsOf(e.pts).map((_, i) => 'I' + i) : []; }
    return [];
  }
  const sel = c => (c.op === 'lcd9' || (c.op === 'trap' && c.like === 'lcd9') || c.op === 'flip9' ? '#equation .tok.fr9[data-ref]' : c.op === 'test9' ? '#equation .tg9[data-ref]' : null);

  // ================================================================ wrong-move reasons
  function why(e, card, ref, S, next) {
    const ms = moves(e), want = ms[0];
    if (e.k9 === 'rs' || e.k9 === 'rm') {
      const fr = e.k9 === 'rs' ? e.fr : null;
      switch (card.op) {
        case 'fac9': {
          const m = ms.find(x => x.op === 'fac9');
          if (!m) return S('Everything is factored already.');
          return S('Those factors don\'t multiply back to it.', `Multiply the factors out to check: they must give exactly ${facAt(e.k9 === 'rs' ? e.fr : e.fs[+((m.refs[0] || 'F0')[1])], m.refs[0].replace(/^F\d/, '')) ? ptext(facAt(e.k9 === 'rs' ? e.fr : e.fs[+((m.refs[0] || 'F0')[1])], m.refs[0].replace(/^F\d/, '')).p, true) : 'the polynomial'}. ${facLabel(m.fs)} does.`);
        }
        case 'ex9': {
          const m = ms.find(x => x.op === 'ex9');
          if (!m) return S(ms.some(x => x.op === 'fac9') ? 'Factor first: then you can see which brackets match.' : 'No bracket is about to cancel, so there\'s nothing to stamp.', 'A stamp marks the value a <b>cancelled</b> bracket would make 0. It is owed just before a bracket on the bottom cancels.');
          return S(`That bracket is 0 at ${XV()} = ${numH(m.v, true)}, not ${numH(card.v, true)}.`, `Set the bottom bracket equal to 0 and solve: that x is the one that isn't allowed. Watch the sign: x + 3 = 0 at x = ${MINUS}3.`);
        }
        case 'can9':
          if (ms.some(x => x.op === 'ex9')) return S('Mark the excluded value first.', `Before a bracket on the bottom cancels, stamp the value that makes it 0 (${exText([ms.find(x => x.op === 'ex9').v], true)}): the original is undefined there, even after the bracket is gone.`);
          if (ms.some(x => x.op === 'fac9')) return S('Factor first.', 'Only whole factors cancel. Factor every polynomial first, then look for brackets that match on top and bottom.');
          if (ms.some(x => x.op === 'neg9')) return S('Those brackets are opposites, not the same.', '(x − 2) and (2 − x) are opposites: 2 − x = −(x − 2). Factor out −1 first, then they match.');
          return S('Nothing matches on top and bottom.', `To cancel, the same factor must be on the top and the bottom. ${next}`);
        case 'neg9': return S('There are no opposite brackets here.');
        case 'red9': return ms.some(x => x.op === 'red9') ? S(`${card.d} doesn't go into both numbers.`) : S('The numbers can\'t be reduced.');
        case 'flip9': return e.k9 === 'rm' && e.op === '/' ? S('Flip the second fraction, not the first.') : S('Only for dividing: this is already multiplying.');
        case 'mrg9': return e.k9 === 'rm' && e.op === '/' ? S('Dividing: flip the second fraction first.', 'a/b ÷ c/d = a/b · d/c: change the division into multiplying by the reciprocal, then multiply across.') : S('It\'s one fraction already.');
      }
      return null;
    }
    if (e.k9 === 'ra') {
      if (card.op === 'lcd9') {
        if (ms.some(m => m.op === 'fac9')) return S('Factor the bottom first: it may share a bracket.');
        if (ms.some(m => m.op === 'cmb9')) return S('The bottoms already match: combine the tops.');
        const m = ms.find(x => x.op === 'lcd9' && x.refs.includes(ref)) || ms.find(x => x.op === 'lcd9');
        return S(`That fraction needs ${sideH(tidySide(m.m), true)}.`, `The common denominator is ${sideH(lcdOf(e.fs.map(f => f.bot)), true)}. Each fraction gets exactly the factor its bottom is missing, on top and bottom.`);
      }
      if (card.op === 'cmb9') {
        if (!ms.some(m => m.op === 'cmb9')) return S('The bottoms aren\'t the same yet.', 'Add or subtract tops only over a common bottom. Build the common denominator first.');
        return S(`The top is ${ptext(ms[0].p, true)}.`, e.op === '-' ? `Subtract the <b>whole</b> second top: the minus goes to every term in it. (${ptext(prodPoly(e.fs[0].top), true)}) ${MINUS} (${ptext(prodPoly(e.fs[1].top), true)}) = ${ptext(ms[0].p, true)}.` : `Add the tops: (${ptext(prodPoly(e.fs[0].top), true)}) + (${ptext(prodPoly(e.fs[1].top), true)}) = ${ptext(ms[0].p, true)}.`);
      }
      if (card.op === 'fac9') return S('Those factors don\'t multiply back.');
      return null;
    }
    if (e.k9 === 're') {
      if (e.cands) {
        if (e.pend) {
          const { l, r, v } = e.pend, side = s => (s.undef ? 'undefined (a bottom is 0)' : fracText(s.val));
          if (card.op === 'keep9') return S(l.undef || r.undef ? 'A bottom is 0 there: it\'s not allowed.' : `${fracText(l.val)} ≠ ${fracText(r.val)}.`, `At ${XV()} = ${numH(v, true)} the left side is ${side(l)} and the right side is ${side(r)}. ${l.undef || r.undef ? 'Dividing by 0 is undefined, so this answer is a fake: reject it.' : 'They aren\'t equal, so reject it.'}`);
          if (card.op === 'rej9') return S('It checks out: keep it.', `At ${XV()} = ${numH(v, true)} both sides are ${fracText(l.val)}, and no bottom is 0.`);
          return S('Decide first: keep it or reject it?');
        }
        if (card.op === 'keep9' || card.op === 'rej9') return S('Check an answer first.');
        return S('Now check each answer in the original equation.');
      }
      if (card.op === 'chk9' || card.op === 'keep9' || card.op === 'rej9') return S('There\'s no answer to check yet.');
      if (!e.poly) {
        if (card.op === 'lcd9e') return S('That doesn\'t clear every fraction.', `The LCD has to contain every bottom: ${sideH(tidySide(lcdOf(termsBots(e))), true)}. Multiplying by it cancels each denominator.`);
        return S('Clear the fractions first: multiply both sides by the LCD.');
      }
      if (card.op === 'lcd9e') return S('The fractions are already cleared.');
      if (Math.max(pdeg(e.L), pdeg(e.R)) === 2) {
        if (card.op === 'zero9') return S('Subtract the whole right side.', `To get 0 on the right, subtract exactly ${ptext(e.R, true)}.`);
        if (card.op === 'facq9') { const rs = intRoots(e.L); return S('Those factors don\'t multiply back.', rs ? `Two numbers that multiply to ${fracText(pco(e.L, 0))} and add to ${fracText(pco(e.L, 1))}: ${numText(-rs[0])} and ${numText(-rs[1])}.` : ''); }
        if (card.op === 'zp9') return S(e.fac ? 'Zero product is right.' : 'Factor first.');
        return S('With an x² term, get 0 on one side and factor.');
      }
      if (card.op === 'as9' || card.op === 'asx9' || card.op === 'dv9') {
        if (!fz(pco(e.R, 1)) && card.op !== 'asx9') return S('Get the x terms on one side first.');
        if (!fz(pco(e.L, 0)) && card.op === 'dv9') return S('Undo the + or − first.');
        return S('That doesn\'t get x alone.', `Undo what's attached to x: + or − first, then × or ÷.${next}`);
      }
      return null;
    }
    if (e.k9 === 'va') {
      switch (card.op) {
        case 'form9': return e.ph === 'form' ? S(`"${vaWords(e).split('.')[0].replace(/<[^>]+>/g, '')}" means ${FORMS[e.kind]}.`, 'Directly: y = kx (y grows as x grows). Inversely: y = k/x (y shrinks as x grows). With the square of x: y = kx². Jointly with x and z: y = kxz.') : S('The formula is already chosen.');
        case 'plug9': return card.sw ? S('x and y are swapped.', `Put y = ${e.known.y} in for y and x = ${e.known.x} in for x.`) : S('Not now.');
        case 'kdv9': return e.ph === 'k' ? S(e.kind === 'inverse' ? `k is divided by ${kFactor(e.kind, e.known)}: multiply both sides by it.` : `k is multiplied by ${kFactor(e.kind, e.known)}: divide both sides by it.`) : e.ph === 'div2' ? S('Divide by the number next to x.') : S('Not now.');
        case 'plq9': return S(card.v === e.q.find ? 'Not now.' : `You're finding ${e.q.find}: put in the other value.`);
      }
      return S(`One step at a time.${next}`);
    }
    if (e.k9 === 'ri') {
      switch (card.op) {
        case 'crit9': return e.ph !== 'crit' ? S(e.ph === 'move' || e.ph === 'comb' ? 'Get 0 on the right first.' : 'The critical points are already marked.', 'Critical points only tell you where the sign can change when one side is 0.') : S('Those aren\'t where the top and bottom are 0.', `Set the top = 0 and the bottom = 0 and solve each: ${critOf(e).map(p => `${XV()} = ${numH(p.x, true)}`).join(', ')}. Both matter: the bottom's point is where the fraction is undefined.`);
        case 'test9': return e.ph !== 'test' ? S('Mark the critical points first.') : e.pend ? S('Say whether the test is true first.') : S('Test an interval that hasn\'t been tested.');
        case 'tt9': case 'tf9':
          if (!e.pend) return S('Test an interval first.');
          return S(`At ${XV()} = ${numH(e.pend.x, true)} the fraction is ${numH(e.pend.val, true)}: is that ${e.rel} 0? ${e.pend.ok ? 'Yes.' : 'No.'}`);
        case 'gr9': {
          if (e.ph !== 'graph') return S('Test every interval first.');
          const t = riTruth(e);
          if (card.sh.some((v, i) => v !== t.sh[i])) return S('Shade the intervals that tested true.');
          return S(t.pts.some((p, i) => !p.top && card.cl[i]) ? 'The bottom\'s point is always an open dot: it makes the fraction undefined.' : strict(e.rel) ? 'With < or >, the dots are open.' : 'With ≤ or ≥, the top\'s point is included: closed dot.');
        }
        case 'zri9': return S('Not now.');
        case 'cri9': return S('Multiply the number by the bottom before combining.', `${numH(e.c, true)} = ${numH(e.c, true)}(${ptext(P1(e.bot.a, e.bot.b), true)})/(${ptext(P1(e.bot.a, e.bot.b), true)}), so the top is (${ptext(P1(e.top.a, e.top.b), true)}) ${MINUS} ${numH(e.c, true)}(${ptext(P1(e.bot.a, e.bot.b), true)}) = ${ptext(riNewTop(e), true)}.`);
      }
      return null;
    }
    return null;
  }

  // ================================================================ rendering
  function frEls(fr, pre, R, opts = {}) {
    const many = s => s.length > 1;
    const facTok = (f, ref, wrap) => R.TOK(R.W9(f.t === 'k' && f.v === -1 && wrap ? MINUS : facH(f, true, wrap && (f.t === 'l' || f.t === 'p'))), 'f9', pre + ref, 'f9');
    const row = (fs, s) => (fs.length ? fs.map((f, i) => facTok(f, s + i, many(fs))) : [R.sym('1', 'one9')]);
    if (!fr.bot.length) return R.rowEl(row(fr.top, 't'));
    const w = document.createElement('span'); w.className = 'n4 frac4 frac9';
    w.append(R.rowEl(row(fr.top, 't')), R.TOK('<span class="bar4"></span>', 'bar', opts.noBar ? null : pre + 'bar', 'bar9'), R.rowEl(row(fr.bot, 'b')));
    return w;
  }
  function wrapFr(el, ref, R) { const t = R.TOK('', 'fr', ref, 'fr9'); t.appendChild(el); return t; }
  function render(e, el, R) {
    if (e.k9 === 'rs') {
      el.appendChild(frEls(e.fr, '', R));
      if (e.ex.length) el.appendChild(R.sym(exText(e.ex, true), 'stamp9'));
      return;
    }
    if (e.k9 === 'rm' || e.k9 === 'ra') {
      if (e.k9 === 'ra' && e.res) { el.appendChild(R.TOK(R.W9(frH(ptext(e.res.top, true), sideH(e.res.bot, true))), 'res', 'RES', 't9')); return; }
      el.appendChild(wrapFr(frEls(e.fs[0], 'F0', R, { noBar: true }), 'F0', R));
      el.appendChild(R.sym(e.op === '*' ? '·' : e.op === '/' ? DIV : e.op === '+' ? '+' : MINUS, 'op9'));
      el.appendChild(wrapFr(frEls(e.fs[1], 'F1', R, { noBar: true }), 'F1', R));
      if (e.ex && e.ex.length) el.appendChild(R.sym(exText(e.ex, true), 'stamp9'));
      return;
    }
    if (e.k9 === 're') return renderRe(e, el, R);
    if (e.k9 === 'va') {
      const col = R.colEl([R.rowEl([R.sym(vaWords(e), 'words9')]), R.rowEl([R.TOK(R.W9(vaLine(e)), 'va', 'V', 't9')])]);
      el.appendChild(col);
      return;
    }
    if (e.k9 === 'ri') {
      const rows = [R.rowEl([R.TOK(R.W9(riLine(e)), 'q', 'Q', 't9')])];
      if (e.pts) rows.push(R.rowEl([R.TOK(riNl(e), 'nl', 'NL', 'nlTok9')]));
      if (e.pend) rows.push(R.rowEl([R.TOK(`<span class="nonum">${XV()} = ${numH(e.pend.x, true)}:</span> ${frH(ptext(P1(e.top.a, e.top.b), false).replace(/x/g, '(' + fracText(e.pend.x) + ')'), ptext(P1(e.bot.a, e.bot.b), false).replace(/x/g, '(' + fracText(e.pend.x) + ')'), 'nonum')} = ${numH(e.pend.val, true)} <span class="nonum">${e.rel} 0 ?</span>`, 'pd', 'PD', 't9 small9')]));
      if (e.ph === 'done') rows.push(R.rowEl([R.sym(riAnswer(e, true), 'fin9')]));
      el.appendChild(R.colEl(rows));
    }
  }
  function termH(t) {
    if (!t.d.length) return ptext(t.n, true);
    return frH(ptext(t.n, true), sideH(t.d, true));
  }
  function sideEls(ts, s, R) {
    const out = [];
    ts.forEach((t, i) => {
      const neg = !t.d.length && pdeg(t.n) === 0 && t.n[0].n < 0 && i;
      if (i) out.push(R.sym(neg ? MINUS : '+'));
      const body = neg ? termH({ n: pscale(t.n, F(-1)), d: [] }) : termH(t);
      out.push(R.TOK(R.W9(body), 'tm', s + i, 't9'));
      if (t.d.some(f => f.t === 'p')) out[out.length - 1].dataset.ref = s + i + 'b';
    });
    return out;
  }
  function renderRe(e, el, R) {
    if (!e.cands) {
      if (!e.poly) { sideEls(e.L, 'L', R).forEach(x => el.appendChild(x)); el.appendChild(R.EQTOK()); sideEls(e.R, 'R', R).forEach(x => el.appendChild(x)); return; }
      const L = e.fac ? e.fac.map(r => `(${ptext(P1(1, fNeg(r)), true)})`).join('') : ptext(e.L, true);
      el.appendChild(R.TOK(R.W9(L), 'l9', 'L', 't9')); el.appendChild(R.EQTOK()); el.appendChild(R.TOK(R.W9(ptext(e.R, true)), 'r9', 'R', 't9'));
      return;
    }
    const orig = [...e.orig.L.map(termH)].join(' + ') + ' = ' + e.orig.R.map(termH).join(' + ');
    const rows = [R.rowEl([R.sym('Check in the original:', 'lab9'), R.TOK(R.W9(orig.replace(/\+ (−)/g, '$1 ')), 'o9', 'O', 't9 small9')])];
    const cs = [];
    e.cands.forEach((c, i) => { if (i) cs.push(R.sym('or', 'lab9')); cs.push(R.TOK(R.W9(`${XV()} = ${numH(c.v, true)}`), 'c9', 'c' + i, 't9 c9 st9-' + c.st + (e.pend && e.pend.i === i ? ' now9' : ''))); });
    rows.push(R.rowEl(cs));
    if (e.pend) {
      const s = x => (x.undef ? '<span class="bad9t">undefined</span>' : numH(x.val, true));
      rows.push(R.rowEl([R.TOK(`<span class="nonum">left</span> ${s(e.pend.l)} <span class="nonum">≟ right</span> ${s(e.pend.r)}`, 'pd', 'PD', 't9 small9')]));
    } else if (reDone(e)) rows.push(R.rowEl([R.sym(reAnswer(e, true), 'fin9')]));
    el.appendChild(R.colEl(rows));
  }

  // ================================================================ prompts
  const PR = {
    simp: ['Simplify. State any excluded values.', 'Simplify the rational expression.', 'Write in simplest form.'],
    mul: ['Multiply. Simplify your answer.', 'Simplify the product.', 'Multiply and simplify.'],
    div: ['Divide. Simplify your answer.', 'Simplify the quotient.', 'Divide and simplify.'],
    add: ['Add. Simplify your answer.', 'Find the sum.', 'Add the fractions.'],
    sub: ['Subtract. Simplify your answer.', 'Find the difference.', 'Subtract the fractions.'],
    eq: ['Solve. Check for extraneous solutions.', 'Solve the rational equation.', 'Solve and check.'],
    eqn: ['Solve for x.', 'Solve the equation.', 'Solve.'],
    vary: ['Solve the variation problem.', 'Use the variation to answer.', 'Find the constant of variation, then answer.'],
    ineq: ['Solve the inequality. Graph the solution.', 'Solve the rational inequality.', 'Solve and graph.'],
  };
  function promptKey(s) {
    switch (s.k9) {
      case 'rs': return 'simp';
      case 'rm': return s.op === '/' ? 'div' : 'mul';
      case 'ra': return s.op === '-' ? 'sub' : 'add';
      case 're': return termsBots(s).some(d => d.some(f => f.t !== 'k')) ? 'eq' : 'eqn';
      case 'va': return 'vary';
      case 'ri': return 'ineq';
    }
    return 'eqn';
  }
  function textOf(e) {
    switch (e.k9) {
      case 'rs': return 'rs ' + frText(e.fr, false);
      case 'rm': return 'rm ' + e.fs.map(f => frText(f, false)).join(e.op);
      case 'ra': return 'ra ' + e.fs.map(f => frText(f, false)).join(e.op);
      case 're': return 're ' + e.L.map(t => ptext(t.n) + '/' + sideH(t.d, false)).join('+') + '=' + e.R.map(t => ptext(t.n) + '/' + sideH(t.d, false)).join('+');
      case 'va': return `va ${e.kind} ${e.q.find} ${JSON.stringify(e.known)} ${JSON.stringify(e.q)}`;
      case 'ri': return `ri ${riLine(e, false)}`;
    }
    return '';
  }

  // ================================================================ animations
  // Timing follows the game: what's written fades in fast, hold() (scaled by the speed setting), the
  // calculation runs fast, the result shows, hold(). Each operation has its own motion.
  const anim = {
    async fac9(c, s, ns, ref, H) {
      const t = H.tk(ref); H.mark([ref]);
      const kindTxt = c.fs.some(f => f.t === 'k' || f.t === 'x') ? 'Take out the common factor first, then factor what\'s left' : 'Two numbers that multiply to the last number and add to the middle one';
      const n = await H.written(facLabel(c.fs), [t], kindTxt); dropNote(n);
      await H.result(ns, [], `Factored: ${sideH(tidySide(c.fs), false)}`);
    },
    async ex9(c, s, ns, ref, H) {
      const t = H.tk(ref); H.mark([ref]);
      const n = await H.written(`${XV()} ≠ ${numH(c.v, true)}`, [t], `This bracket would be 0 at x = ${fracText(c.v)}, so x can never be ${fracText(c.v)}. The stamp stays even after the bracket cancels`, 'stamp4');
      const from = t && t.getBoundingClientRect(); dropNote(n);
      H.render(ns);
      const dest = $('equation').querySelector('.stamp9');
      if (from && dest) { dest.style.opacity = '0.2'; await H.fly(`${XV()} ≠ ${numH(c.v, true)}`, from, dest); dest.style.opacity = ''; kickClass(dest, 'pop'); }
      await quick(200); await hold();
    },
    async neg9(c, s, ns, ref, H) {
      const t = H.tk(ref); H.mark([ref]); if (t) t.classList.add('spin');
      const f = facAt(s.k9 === 'rs' ? s.fr : s.fs[+ref[1]], ref.replace(/^F\d/, ''));
      const n = await H.written(`${MINUS}(${linH(-f.a, -f.b, true)})`, [t], `${linH(f.a, f.b, false)} = −(${linH(-f.a, -f.b, false)}): pull out −1 so the bracket matches its partner`); dropNote(n);
      await H.result(ns, [], 'Now the brackets match');
    },
    async can9(c, s, ns, ref, H) {
      const m = H.moveAt(s, c, ref), refs = m.refs;
      H.cls(refs, 'hot9');
      caption('The same factor on top and bottom divides to 1');
      const ns2 = refs.map(r => { const n = note('= 1', [H.tk(r)]); n.classList.add('lift4', 'n9'); return n; });
      await quick(150); await hold();
      ns2.forEach(dropNote);
      H.cls(refs, 'crack9'); await quick(500);
      await H.result(ns, [], `Cancelled: ${frText((ns.fr || ns.fs[0]), false)}`);
    },
    async red9(c, s, ns, ref, H) {
      caption(`Both numbers share ${c.d}: divide the top and the bottom by ${c.d}`);
      const tops = [...$('equation').querySelectorAll('[data-ref^="t"]')], bots = [...$('equation').querySelectorAll('[data-ref^="b"]')];
      const n1 = note(`${DIV} ${c.d}`, tops), n2 = note(`${DIV} ${c.d}`, bots);
      [n1, n2].forEach(n => n.classList.add('lift4', 'n9'));
      await quick(150); await hold(); dropNote(n1); dropNote(n2);
      await H.result(ns, [], `Reduced: ${frText(ns.fr, false)}`);
    },
    async flip9(c, s, ns, ref, H) {
      const t = H.tk('F1'); H.mark(['F1']);
      caption('Dividing by a fraction is multiplying by its reciprocal: the second fraction flips over');
      if (t) { t.style.transition = 'transform .45s'; t.style.transform = 'rotateX(180deg)'; }
      await quick(480);
      await H.result(ns, ['F1'], 'Now it\'s a multiplication');
    },
    async mrg9(c, s, ns, ref, H) {
      const a = H.tk('F0'), b = H.tk('F1');
      caption('Multiply straight across: tops times tops, bottoms times bottoms');
      if (a && b) await H.fly(b.innerHTML, b.getBoundingClientRect(), a, 450);
      if (b) b.classList.add('slide9');
      await quick(200);
      await H.result(ns, [], 'One fraction. Now factor and cancel');
    },
    async lcd9(c, s, ns, ref, H) {
      const t = H.tk(ref); H.mark([ref]);
      const n = await H.written(`${TIMES} ${mulLabel(c.m)}`, [t], `This bottom is missing ${sideH(tidySide(c.m), false)}: multiply top and bottom by it (that's multiplying by 1)`); dropNote(n);
      await H.result(ns, [ref], 'Its bottom grew the missing factor');
    },
    async cmb9(c, s, ns, ref, H) {
      const a = H.tk('F0'), b = H.tk('F1');
      caption(s.op === '-' ? 'Same bottom: subtract the tops. The minus goes to every term of the second top' : 'Same bottom: add the tops and keep the bottom');
      const n = note(`(${ptext(prodPoly(s.fs[0].top), true)}) ${s.op === '-' ? MINUS : '+'} (${ptext(prodPoly(s.fs[1].top), true)})`, [a, b]); n.classList.add('lift4', 'n9');
      await quick(150); await hold(); dropNote(n);
      if (a && b) await H.fly(b.innerHTML, b.getBoundingClientRect(), a, 400);
      await H.result(ns, ['RES'], `= ${ptext(c.p)} over the common bottom`);
    },
    async lcd9e(c, s, ns, ref, H) {
      const toks = [...$('equation').querySelectorAll('[data-ref^="L"], [data-ref^="R"]')];
      caption(`Multiply every term on both sides by the LCD, ${sideH(tidySide(c.m), false)}`);
      const nts = toks.map(t => { const n = note(`${TIMES} ${sideH(tidySide(c.m), true)}`, [t]); n.classList.add('lift4', 'n9'); return n; });
      await quick(150); await hold();
      nts.forEach(dropNote);
      toks.forEach(t => t.querySelectorAll('.frac > span:last-child').forEach(d => d.classList.add('pop9')));
      await quick(450);
      await H.result(ns, ['L', 'R'], `The denominators cancel: no fractions left${ns.ck ? '. x was in a bottom, so every answer must be checked' : ''}`);
    },
    async zero9(c, s, ns, ref, H) { await H.both(`${MINUS} (${ptext(c.p, true)})`, ['L', 'R'], 'Get 0 on one side so the quadratic can be factored'); await H.result(ns, ['L', 'R'], ''); },
    async facq9(c, s, ns, ref, H) {
      const t = H.tk('L'); H.mark(['L']);
      const n = await H.written(`${numText(-fv(c.r1))} · ${numText(-fv(c.r2))} = ${fracText(pco(s.L, 0))}, sum ${fracText(pco(s.L, 1))}`, [t], 'Two numbers that multiply to the last number and add to the middle one'); dropNote(n);
      await H.result(ns, ['L'], '');
    },
    async zp9(c, s, ns, ref, H) { const t = H.tk('L'); H.mark(['L']); const n = await H.written(s.fac.map(r => `${ptext(P1(1, fNeg(r)), true)} = 0`).join(' or '), [t], 'Zero product: one of the factors must be 0'); dropNote(n); await H.result(ns, ['c0', 'c1'], ns.cands ? 'Possible answers: x was in a bottom, so check each' : ''); },
    async asx9(c, s, ns, ref, H) { await H.both(`${c.n.n < 0 ? MINUS : '+'} ${ptext([F(0), fAbs(c.n)], true)}`, ['L', 'R'], cardText(c)); await H.result(ns, ['L', 'R'], 'The x terms are on one side now'); },
    async as9(c, s, ns, ref, H) { await H.both(signedN(c.n, true), ['L', 'R'], cardText(c)); await H.result(ns, ['L', 'R'], 'Both sides changed the same way'); },
    async dv9(c, s, ns, ref, H) {
      caption(cardText(c));
      const ns2 = ['L', 'R'].map(H.tk).filter(Boolean).map(a => { const n = note(numH(c.n, true), [a], { bar: true }); n.classList.add('n9'); return n; });
      await quick(150); await hold(); ns2.forEach(dropNote);
      await H.result(ns, ['L', 'R'], ns.cands ? 'x is alone. It came from clearing an x bottom, so check it' : 'Each side divided by the same number');
    },
    async chk9(c, s, ns, ref, H) {
      const i = s.cands.findIndex(o => fEq(o.v, c.v)), from = H.tk('c' + i), to = H.tk('O');
      H.mark(['c' + i]);
      if (from && to) await H.fly(`${XV()} = ${numH(c.v, true)}`, from.getBoundingClientRect(), to, 520);
      H.render(ns);
      caption(`Put x = ${fracText(c.v)} into every term of the original. Is a bottom 0? Are the sides equal?`);
      const p = H.tk('PD'); if (p) kickClass(p, 'pop');
      await quick(250); await hold();
    },
    async keep9(c, s, ns, ref, H) { const t = H.tk('c' + s.pend.i); if (t) t.classList.add('keep9'); caption(`x = ${fracText(s.pend.v)} works: keep it`); await quick(400); await H.result(ns, [], ''); },
    async rej9(c, s, ns, ref, H) { const t = H.tk('c' + s.pend.i); if (t) t.classList.add('crack9'); caption(`x = ${fracText(s.pend.v)} is a fake answer: it shatters`); await quick(650); await H.result(ns, [], ''); },
    async form9(c, s, ns, ref, H) { const t = H.tk('V'); H.mark(['V']); const n = await H.written(formH(c.f), [t], { direct: 'Directly: y = kx', inverse: 'Inversely: y = k/x', square: 'With the square of x: y = kx²', joint: 'Jointly with x and z: y = kxz' }[c.f]); dropNote(n); await H.result(ns, ['V'], 'k is the constant of variation: find it next'); },
    async plug9(c, s, ns, ref, H) { const t = H.tk('V'); H.mark(['V']); const n = await H.written(`${XV()} = ${s.known.x}, ${XV('y')} = ${s.known.y}${s.kind === 'joint' ? `, ${XV('z')} = ${s.known.z}` : ''}`, [t], 'Put the known values into the formula'); dropNote(n); await H.result(ns, ['V'], s.kind === 'square' ? `${s.known.x}² = ${s.known.x * s.known.x}` : s.kind === 'joint' ? `${s.known.x} · ${s.known.z} = ${s.known.x * s.known.z}` : ''); },
    async kdv9(c, s, ns, ref, H) {
      caption(cardText(c));
      const t = H.tk('V');
      const n = c.how === 'mul' ? note(`${TIMES} ${parenF(c.n, true)}`, [t]) : note(numH(c.n, true), [t], { bar: true }); n.classList.add('n9', 'lift4');
      await quick(150); await hold(); dropNote(n);
      await H.result(ns, ['V'], ns.ph === 'rew' ? `The constant of variation: k = ${fracText(ns.k)}` : '');
    },
    async rew9(c, s, ns, ref, H) { const t = H.tk('V'); if (t) t.classList.add('slide9'); caption('Write the formula with k filled in: it works for every pair'); await quick(350); await H.result(ns, ['V'], ''); },
    async plq9(c, s, ns, ref, H) { const t = H.tk('V'); H.mark(['V']); const n = await H.written(s.q.find === 'y' ? `${XV()} = ${s.q.x}${s.kind === 'joint' ? `, ${XV('z')} = ${s.q.z}` : ''}` : `${XV('y')} = ${s.q.y}`, [t], 'Reuse the formula with the new value'); dropNote(n); await H.result(ns, ['V'], ''); },
    async ev9(c, s, ns, ref, H) { const t = H.tk('V'); H.mark(['V']); caption('Work it out'); await quick(200); await H.result(ns, ['V'], `${s.q.find} = ${fracText(vaAns(s))}`); },
    async mx9(c, s, ns, ref, H) { caption('Multiply both sides by x to get it out of the bottom'); const t = H.tk('V'); const n = note(`${TIMES} ${XV()}`, [t]); n.classList.add('n9', 'lift4'); await quick(150); await hold(); dropNote(n); await H.result(ns, ['V'], ''); },
    async zri9(c, s, ns, ref, H) { await H.both(signedN(c.n, true), ['Q'], 'Get 0 on the right: the sign of one fraction is easy to test'); await H.result(ns, ['Q'], ''); },
    async cri9(c, s, ns, ref, H) { const t = H.tk('Q'); H.mark(['Q']); const n = await H.written(`${numH(s.c, true)} = ${frH(`${numH(s.c, true)}(${ptext(P1(s.bot.a, s.bot.b), true)})`, ptext(P1(s.bot.a, s.bot.b), true))}`, [t], 'Write the number over the same bottom, then combine the tops'); dropNote(n); await H.result(ns, ['Q'], ''); },
    async crit9(c, s, ns, ref, H) {
      const t = H.tk('Q'); H.mark(['Q']);
      const n = await H.written(critOf(s).map(p => `${p.top ? 'top' : 'bottom'} = 0 at ${XV()} = ${numH(p.x, true)}`).join(', '), [t], 'The sign can only change where the top or the bottom is 0'); dropNote(n);
      await H.result(ns, ['NL'], 'The critical points cut the number line into intervals. Test each one');
    },
    async test9(c, s, ns, ref, H) { const t = H.tk(ref); if (t) t.classList.add('hover'); caption('Pick a number in that interval and put it in the fraction'); await quick(250); await H.result(ns, ['PD'], 'Is it true there?'); },
    async tt9(c, s, ns, ref, H) { caption(`True: every number in that interval works`); await quick(200); await H.result(ns, ['NL'], ''); },
    async tf9(c, s, ns, ref, H) { caption(`False: no number in that interval works`); await quick(200); await H.result(ns, ['NL'], ''); },
    async gr9(c, s, ns, ref, H) { caption('Shade the true intervals. The bottom\'s point is always open: the fraction is undefined there'); await quick(250); await H.result(ns, ['NL'], `Answer: ${riAnswer(ns, false)}`); },
  };

  // ================================================================ generators
  // Every case comes up at every level; the level changes how hard: bigger numbers, an extra factor,
  // negatives, common factors to take out first.
  const sgn = () => (chance(0.5) ? 1 : -1);
  const nz = (a, b) => nonZero(a, b);
  const big = L => [5, 7, 9, 12][L];
  const done = (st, n) => st && A.okPath(st, n);
  const lin = r => Lf(1, -r);   // (x − r)
  // ---------------------------------------------------------------- stage 39
  const SIMP_CASES = ['dos', 'tri', 'gcf', 'opp', 'mono', 'nocancel'];
  function genSimp(cs, tut = isTutorial()) {
    const L = lvl(tut), M = big(L);
    cs = cs || pick(SIMP_CASES);
    for (let t = 0; t < 400; t++) {
      let st = null;
      const r = nz(-M, M), s2 = nz(-M, M), u = nz(-M, M);
      if (cs === 'dos') {
        const a = rand(2, M), top = Pf(pmul(P1(1, -a), P1(1, a))), k = L >= 2 && chance(0.4) ? rand(2, 4) : 1;
        const bot = Lf(1, a * sgn());
        st = chance(0.7) ? rsState([k > 1 ? Pf(pscale(top.p, F(k))) : top], [bot]) : rsState([bot], [top]);
      } else if (cs === 'tri') {
        if (r === s2 || r === u || s2 === u) continue;
        const kt = L >= 2 && chance(0.35) ? rand(2, 3) : 1;
        st = rsState([Pf(pscale(pmul(P1(1, -r), P1(1, -s2)), F(kt)))], [Pf(pmul(P1(1, -r), P1(1, -u)))]);
      } else if (cs === 'gcf') {
        const k = rand(2, [5, 6, 8, 9][L]), a = nz(-M, M);
        st = chance(0.5) ? rsState([Pf(pscale(P1(1, a), F(k)))], [Pf(pmul([F(0), F(1)], P1(1, a)))]) : rsState([Pf(pscale(pmul(P1(1, a), P1(1, nz(-M, M))), F(1)))], [Pf(pscale(P1(1, a), F(k)))]);
      } else if (cs === 'opp') {
        const a = rand(1, M), b = nz(-M, M);
        if (a === -b) continue;
        st = chance(0.5) ? rsState([Pf(pmul(P1(1, -a), P1(1, b)))], [Lf(-1, a)]) : rsState([Lf(-1, a)], [Pf(pmul(P1(1, -a), P1(1, b)))]);
      } else if (cs === 'mono') {
        const g = rand(2, [4, 5, 6, 8][L]), p = rand(1, 3), q = rand(1, 4), et = rand(1, 4), eb = rand(1, 3);
        if (gcd(p, q) !== 1 || et === eb || (p === 1 && q === 1)) continue;
        st = rsState([Kf(g * p), Xf(et)], [Kf(g * q), Xf(eb)]);
      } else {   // nocancel: factor both, nothing matches
        if (r === s2 || r === u || s2 === u) continue;
        const v = nz(-M, M); if ([r, s2].includes(v) || [r, s2].includes(u)) continue;
        st = rsState([Pf(pmul(P1(1, -r), P1(1, -s2)))], [Pf(pmul(P1(1, -u), P1(1, -v)))]);
      }
      if (done(st, 9)) return { r9: st, enemy: 'cogling' };
    }
    return { r9: rsState([Pf([F(-9), F(0), F(1)])], [Lf(1, 3)]), enemy: 'cogling' };
  }
  // ---------------------------------------------------------------- stage 40
  const MUL_CASES = ['mul', 'div', 'polymul', 'polydiv'];
  function genMul(cs, tut = isTutorial()) {
    const L = lvl(tut), M = big(L);
    cs = cs || pick(MUL_CASES);
    for (let t = 0; t < 400; t++) {
      let st = null;
      if (cs === 'mul' || cs === 'div') {
        const a = rand(2, [6, 8, 10, 12][L]), b = rand(2, [6, 8, 10, 12][L]), e1 = rand(1, 3), e2 = rand(1, 3);
        if (a === b || a % b === 0 || b % a === 0 || e1 === e2) continue;
        const f0 = { top: [Xf(e1)], bot: [Kf(a)] }, f1 = { top: [Kf(b)], bot: [Xf(e2)] };
        if (cs === 'div') { st = rmState(f0, { top: [Xf(e2)], bot: [Kf(b)] }, '/'); }
        else st = rmState(f0, f1, '*');
      } else {
        const r = nz(-M, M), s2 = nz(-M, M), k = rand(2, [4, 5, 6, 8][L]);
        if (r === s2 || r === -s2) continue;
        if (cs === 'polymul') st = rmState({ top: [Pf(pmul(P1(1, -r), P1(1, -s2)))], bot: [Kf(k), Xf(1)] }, { top: [Kf(2 * k), Xf(1)], bot: [lin(r)] }, '*');
        else st = rmState({ top: [lin(r)], bot: [lin(-s2)] }, { top: [Pf(pmul(P1(1, -r), P1(1, s2)))], bot: [Pf(pmul(P1(1, s2), P1(1, -s2)))] }, '/');
      }
      if (done(st, 14)) return { r9: st, enemy: 'ratchet' };
    }
    return { r9: rmState({ top: [Xf(1)], bot: [Kf(3)] }, { top: [Xf(2)], bot: [Kf(6)] }, '/'), enemy: 'ratchet' };
  }
  // ---------------------------------------------------------------- stage 41
  const ADD_CASES = ['same', 'num', 'var', 'sub', 'share'];
  function genAdd(cs, tut = isTutorial()) {
    const L = lvl(tut), M = big(L);
    cs = cs || pick(ADD_CASES);
    for (let t = 0; t < 400; t++) {
      let st = null;
      const a = nz(-M, M), b = nz(-M, M), p = rand(1, [5, 7, 9, 12][L]), q = rand(1, [5, 7, 9, 12][L]);
      if (cs === 'same') { st = raState({ top: [Kf(p), Xf(1)], bot: [lin(a)] }, { top: [Kf(q)], bot: [lin(a)] }, chance(0.5) ? '+' : '-'); }
      else if (cs === 'num') { const d1 = rand(2, [5, 6, 8, 9][L]), d2 = rand(2, [5, 6, 8, 9][L]); if (d1 === d2 || d1 % d2 === 0 || d2 % d1 === 0) continue; st = raState({ top: [Xf(1)], bot: [Kf(d1)] }, { top: p > 1 ? [Kf(p), Xf(1)] : [Xf(1)], bot: [Kf(d2)] }, chance(0.3) ? '-' : '+'); }
      else if (cs === 'var') { st = raState({ top: [Kf(p)], bot: [Xf(1)] }, { top: [Kf(q)], bot: [lin(a)] }, '+'); }
      else if (cs === 'sub') { if (a === b) continue; st = raState({ top: [Kf(p)], bot: [lin(a)] }, { top: [Kf(q)], bot: [lin(b)] }, '-'); }
      else { if (a === -a) continue; st = raState({ top: [Kf(p)], bot: [Pf(pmul(P1(1, -a), P1(1, a)))] }, { top: [Kf(q)], bot: [lin(-a)] }, chance(0.5) ? '+' : '-'); }
      if (st && pdeg(combined({ ...st, fs: st.fs })) >= 0 && done(st, 6)) {
        const end = A.pathOf(st, st.skill).end;
        if (!end.res || ptrim(end.res.top).every(c => fz(c))) continue;
        // the answer must already be in lowest terms: no number or bracket shared by the top and the bottom
        const content = end.res.top.filter(c => !fz(c)).reduce((g, c) => gcd(g, c.n), 0);
        if (gcd(content, Math.abs(kOf(end.res.bot))) > 1) continue;
        if (end.res.bot.some(f => zeroOf(f) && fz(peval(end.res.top, zeroOf(f))))) continue;
        if (st.fs.some(f => f.top.some(x => x.t === 'k') && gcd(kOf(f.top), Math.abs(kOf(f.bot))) > 1)) continue;
        return { r9: st, enemy: 'gearwing' };
      }
    }
    return { r9: raState({ top: [Kf(1)], bot: [Xf(1)] }, { top: [Kf(1)], bot: [lin(-1)] }, '+'), enemy: 'gearwing' };
  }
  // ---------------------------------------------------------------- stage 42
  const EQ_CASES = ['num', 'one', 'prop', 'fake', 'quad', 'quadfake', 'quadden'];
  function genEq(cs, tut = isTutorial()) {
    const L = lvl(tut), M = big(L);
    cs = cs || pick(EQ_CASES);
    for (let t = 0; t < 600; t++) {
      let st = null;
      const x0 = nz(-M, M);
      if (cs === 'num') {   // x/a + x/b = c
        const a = rand(2, [4, 5, 6, 8][L]), b = rand(2, [5, 6, 8, 9][L]); if (a === b) continue;
        const m = a * b / gcd(a, b), X = m * nz(-3, 4), c = F(X / a + X / b); if (!isInt(c)) continue;
        st = reState([Tm([0, 1], [Kf(a)]), Tm([0, 1], [Kf(b)])], [Tm([c])]);
      } else if (cs === 'one') {   // p/x + 1/q = r  with answer x0
        const q = rand(2, [3, 4, 5, 6][L]), p = rand(1, [6, 8, 10, 12][L]);
        const rr = fAdd(F(p, x0), F(1, q)); if (!isInt(rr) || fz(rr)) continue;
        st = reState([Tm([p], [Xf(1)]), Tm([1], [Kf(q)])], [Tm([rr])]);
      } else if (cs === 'prop') {   // a/(x + b) = c/(x + d)
        const a = rand(1, [5, 7, 9, 12][L]), c = rand(1, [5, 7, 9, 12][L]), b = nz(-M, M); if (a === c) continue;
        // a(x + d) = c(x + b) at x0: d = (c(x0 + b) − a x0)/a
        const d = F(c * (x0 + b) - a * x0, a); if (!isInt(d) || d.n === b || x0 + b === 0 || x0 + d.n === 0) continue;
        st = reState([Tm([a], [Lf(1, b)])], [Tm([c], [Lf(1, d.n)])]);
      } else if (cs === 'fake') {   // x/(x − a) = a/(x − a) + k  -> x = a (rejected)
        const a = nz(-M, M), k = nz(-4, 4); if (k === 1) continue;
        st = reState([Tm([0, 1], [lin(a)])], [Tm([a], [lin(a)]), Tm([k])]);
      } else if (cs === 'quad') {   // x + c/x = s  with roots r1, r2
        const r1 = nz(-M, M), r2 = nz(-M, M); if (r1 === r2 || r1 * r2 === 0) continue;
        st = reState([Tm([0, 1]), Tm([r1 * r2], [Xf(1)])], [Tm([r1 + r2])]);
      } else if (cs === 'quadfake') {   // x²/(x − a) = (s x − p)/(x − a)  roots a and r
        const a = nz(-M, M), r = nz(-M, M); if (a === r) continue;
        st = reState([Tm([0, 0, 1], [lin(a)])], [Tm([-a * r, a + r], [lin(a)])]);
      } else {   // quadden: p/(x − a) + q/(x + a) = n/(x² − a²)
        const a = rand(1, M), p = rand(1, 4), q = rand(1, 4); if (p + q === 0) continue;
        const v = chance(0.5) ? a : x0; if (v === -a) continue;
        const nn = p * (v + a) + q * (v - a);
        st = reState([Tm([p], [lin(a)]), Tm([q], [lin(-a)])], [Tm([nn], [Pf(pmul(P1(1, -a), P1(1, a)))])]);
      }
      if (st && done(st, 14)) {
        const end = A.pathOf(st, st.skill).end;
        if (end.poly && end.L && !end.cands && !isXalone(end)) continue;
        return { r9: st, enemy: 'sluice' };
      }
    }
    return { r9: reState([Tm([3], [Xf(1)]), Tm([1], [Kf(2)])], [Tm([2])]), enemy: 'sluice' };
  }
  // ---------------------------------------------------------------- stage 43
  const VARY_CASES = ['direct', 'inverse', 'square', 'joint', 'findx'];
  function genVary(cs, tut = isTutorial()) {
    const L = lvl(tut);
    cs = cs || pick(VARY_CASES);
    for (let t = 0; t < 300; t++) {
      const kind = cs === 'findx' ? pick(['direct', 'inverse']) : cs;
      const k = rand(2, [6, 9, 12, 15][L]) * (L >= 2 && chance(0.25) ? -1 : 1);
      const x = rand(2, [6, 8, 10, 12][L]), z = rand(2, 5), x2 = rand(2, [8, 10, 12, 15][L]), z2 = rand(2, 6);
      if (x === x2) continue;
      const yOf = (xx, zz) => (kind === 'inverse' ? F(k, xx) : F(k * kFactor(kind, { x: xx, z: zz })));
      const y = yOf(x, z); if (!isInt(y)) continue;
      const known = { x, y: y.n, ...(kind === 'joint' ? { z } : {}) };
      let q;
      if (cs === 'findx') { const yy = yOf(x2, z2); if (!isInt(yy) || yy.n === 0) continue; q = { find: 'x', y: yy.n }; }
      else { const yy = yOf(x2, z2); if (!isInt(yy)) continue; q = { find: 'y', x: x2, ...(kind === 'joint' ? { z: z2 } : {}) }; }
      const st = vaState(kind, known, q);
      if (done(st, 9)) return { r9: st, enemy: 'pendulum' };
    }
    return { r9: vaState('inverse', { x: 3, y: 4 }, { find: 'y', x: 6 }), enemy: 'pendulum' };
  }
  // ---------------------------------------------------------------- stage 43b
  const INEQ_CASES = ['gt', 'lt', 'ge', 'le', 'rhs'];
  function genIneq(cs, tut = isTutorial()) {
    const L = lvl(tut), M = [5, 6, 8, 9][L];
    cs = cs || pick(INEQ_CASES);
    for (let t = 0; t < 300; t++) {
      const r = rand(-M, M), q = rand(-M, M);
      if (Math.abs(r - q) < 2) continue;
      const rel = cs === 'gt' ? '>' : cs === 'lt' ? '<' : cs === 'ge' ? '≥' : cs === 'le' ? '≤' : pick(['>', '<', '≥', '≤']);
      const a = L >= 2 && chance(0.3) ? -1 : 1;
      let st;
      if (cs === 'rhs') {
        const c = nz(-3, 3), k = sgn();
        // new top k(x − r) = top − c(x − q)  ->  top = (k + c)x − kr − cq
        if (k + c === 0) continue;
        st = riState({ a: k + c, b: -k * r - c * q }, { a: 1, b: -q }, rel, c);
      } else st = riState({ a, b: -a * r }, { a: 1, b: -q }, rel, 0);
      if (done(st, 12)) return { r9: st, enemy: 'floodgate' };
    }
    return { r9: riState({ a: 1, b: 1 }, { a: 1, b: -2 }, '>', 0), enemy: 'floodgate' };
  }
  const GENS = { ratsimp: genSimp, ratmul: genMul, ratadd: genAdd, rateq: genEq, vary: genVary, ratineq: genIneq };
  const HARD = { ratsimp: ['tri', 'opp', 'gcf'], ratmul: ['polymul', 'polydiv'], ratadd: ['sub', 'share', 'var'], rateq: ['fake', 'quadfake', 'quadden'], vary: ['joint', 'findx', 'square'], ratineq: ['rhs', 'ge', 'le'] };
  function bossLast(mine) {
    if (mine.includes('ratineq')) return genIneq('rhs');
    if (mine.includes('rateq')) return genEq(pick(['quadfake', 'quadden']));
    if (mine.includes('ratadd')) return genAdd('share');
    return genMul('polydiv');
  }

  // ================================================================ act
  const HOME = { fac9: 'ratsimp', ex9: 'ratsimp', neg9: 'ratsimp', can9: 'ratsimp', red9: 'ratsimp', flip9: 'ratmul', mrg9: 'ratmul', lcd9: 'ratadd', cmb9: 'ratadd',
    lcd9e: 'rateq', zero9: 'rateq', facq9: 'rateq', zp9: 'rateq', asx9: 'rateq', as9: 'rateq', dv9: 'rateq', chk9: 'rateq', keep9: 'rateq', rej9: 'rateq',
    form9: 'vary', plug9: 'vary', kdv9: 'vary', rew9: 'vary', plq9: 'vary', ev9: 'vary', mx9: 'vary',
    zri9: 'ratineq', cri9: 'ratineq', crit9: 'ratineq', test9: 'ratineq', tt9: 'ratineq', tf9: 'ratineq', gr9: 'ratineq' };
  const spec = {
    act: 9, sk: 'k9', key: 'r9', tag: 'a9', BOTH, COPY, PARAMS, moves, ok, apply, CARD, specials, family, filler, places: placesOf, sel, why, render, anim,
    answer, textOf, promptKey, PR, HOME, gens: GENS, hard: HARD, elite: 'governor', boss: 'millwright', bossLast,
    skills: [
      { id: 'ratsimp', stage: 39, act: 9, name: 'Simplify rational expressions', cases: SIMP_CASES, gen: cycled('ratsimp', c => genSimp(c)),
        title: 'Stage 39: Simplifying rational expressions',
        intro: 'A rational expression is a fraction with polynomials. To simplify, factor the top and the bottom, then cancel factors that match. Only whole factors cancel, never single terms. Before a bracket on the bottom cancels, stamp the value that would make it 0 (x ≠ −3): the original is undefined there, and that stays true after the cancel.',
        example: '(x² − 9)/(x + 3)<br>Factor → (x − 3)(x + 3)/(x + 3)<br>Stamp x ≠ −3, then cancel → x − 3, x ≠ −3',
        tutorial: [() => genSimp('dos', true), () => genSimp('tri', true)] },
      { id: 'ratmul', stage: 40, act: 9, name: 'Multiply and divide', cases: MUL_CASES, gen: cycled('ratmul', c => genMul(c)),
        title: 'Stage 40: Multiplying and dividing',
        intro: 'To multiply fractions, multiply straight across: tops times tops, bottoms times bottoms, then factor and cancel. To divide, flip the second fraction over (its reciprocal) and multiply.',
        example: '(x/3) ÷ (x²/6)<br>Flip and × → (x/3) · (6/x²)<br>Multiply across → 6x/(3x²) → 2/x, x ≠ 0',
        tutorial: [() => genMul('mul', true), () => genMul('div', true)] },
      { id: 'ratadd', stage: 41, act: 9, name: 'Add and subtract', cases: ADD_CASES, gen: cycled('ratadd', c => genAdd(c)),
        title: 'Stage 41: Adding and subtracting',
        intro: 'Fractions add only over the same bottom. Find the least common denominator, multiply each fraction top and bottom by the factor it is missing, then combine the tops. When subtracting, the minus goes to every term of the second top.',
        example: '1/x + 1/(x + 1)<br>× (x + 1)/(x + 1) and × x/x<br>→ (x + 1)/(x(x + 1)) + x/(x(x + 1)) = (2x + 1)/(x(x + 1))',
        tutorial: [() => genAdd('same', true), () => genAdd('var', true)] },
      { id: 'rateq', stage: 42, act: 9, name: 'Rational equations', cases: EQ_CASES, gen: cycled('rateq', c => genEq(c)),
        title: 'Stage 42: Rational equations',
        intro: 'Multiply both sides (every term) by the LCD: all the denominators cancel. Solve what is left. If x was in a bottom, Check each answer in the original equation: one that makes a bottom 0 is a fake and gets rejected.',
        example: '3/x + 1/2 = 2<br>× 2x → 6 + x = 4x → x = 2<br>Check x = 2: 3/2 + 1/2 = 2 ✓',
        tutorial: [() => genEq('num', true), () => genEq('one', true)] },
      { id: 'vary', stage: 43, act: 9, name: 'Variation', cases: VARY_CASES, gen: cycled('vary', c => genVary(c)),
        title: 'Stage 43: Variation',
        intro: 'Directly: y = kx. Inversely: y = k/x. With the square: y = kx². Jointly: y = kxz. Pick the formula, plug in the pair you know to find k, then reuse the formula with k for the question.',
        example: 'y varies inversely with x; y = 4 when x = 3<br>y = k/x → 4 = k/3 → k = 12<br>x = 6: y = 12/6 = 2',
        tutorial: [() => genVary('direct', true), () => genVary('inverse', true)] },
      { id: 'ratineq', stage: '43b', act: 9, name: 'Rational inequalities', cases: INEQ_CASES, gen: cycled('ratineq', c => genIneq(c)),
        title: 'Stage 43b: Rational inequalities',
        intro: 'You can\'t multiply an inequality by (x − 2): its sign is unknown. Instead get 0 on one side and one fraction, find the critical points (where the top or the bottom is 0), and test one number in each interval. The bottom\'s point is always an open dot.',
        example: '(x + 1)/(x − 2) > 0<br>Critical points −1 and 2<br>Test −2 ✓, 0 ✗, 3 ✓ → x < −1 or x > 2',
        tutorial: [() => genIneq('gt', true), () => genIneq('le', true)] },
    ],
    enemies: {
      cogling:    { name: 'Cogling',        rank: 'Normal', color: '#b08968', size: 84 },
      ratchet:    { name: 'Ratchet',        rank: 'Normal', color: '#9c6644', size: 84 },
      gearwing:   { name: 'Gearwing',       rank: 'Normal', color: '#7f5539', size: 84 },
      sluice:     { name: 'Sluice Sprite',  rank: 'Normal', color: '#4ea8de', size: 84 },
      pendulum:   { name: 'Pendulum',       rank: 'Normal', color: '#ddb892', size: 84 },
      floodgate:  { name: 'Floodgate',      rank: 'Normal', color: '#48cae4', size: 84 },
      governor:   { name: 'The Governor',   rank: 'Elite',  color: '#e6ccb2', size: 100, horns: true },
      millwright: { name: 'The Millwright', rank: 'Boss',   color: '#c9a227', size: 120, crown: true },
    },
    actInfo: { name: 'The Divided Mill', sub: 'Rational expressions and equations', boss: 'The Millwright', firstSkill: 'ratsimp',
      blurb: 'At the Divided Mill every gear turns on a fraction bar. Simplify rational expressions, add, multiply and divide them, solve rational equations and inequalities, and check for answers that would make a bottom 0. Defeat The Millwright.',
      cleared: () => `The Millwright's wheel turns true again. ${KT.nextActText(9)}` },
    icons: {
      fac9:  { name: 'Factor', svg: svgI('<path d="M5 5c-2 4-2 10 0 14M10 5c2 4 2 10 0 14M14 5c-2 4-2 10 0 14M19 5c2 4 2 10 0 14"/>') },
      ex9:   { name: 'Mark an excluded value (x ≠ a)', svg: svgI('<rect x="3" y="5" width="18" height="14" rx="3"/><path d="M8 9l8 6M8 15l8-6" stroke-width="2"/>') },
      neg9:  { name: 'Factor out −1', svg: svgI('<path d="M4 12h6"/><path d="M14 6c-2 3-2 9 0 12M20 6c2 3 2 9 0 12"/>') },
      can9:  { name: 'Cancel a common factor', svg: svgI('<path d="M4 12h16"/><path d="M6 3l12 6M6 15l12 6" stroke-width="2"/>') },
      flip9: { name: 'Flip the second fraction and multiply', svg: svgI('<path d="M4 12h16"/><path d="M8 4l4-2 4 2M8 20l4 2 4-2"/>') },
      zp9:   { name: 'Zero product (each factor = 0)', svg: svgI('<ellipse cx="12" cy="12" rx="5" ry="7"/><path d="M4 4l4 4M20 4l-4 4"/>') },
      form9: { name: 'Pick or write the variation formula', svg: svgI('<path d="M4 6h16M4 12h10M4 18h6"/><path d="M17 15l3 3-3 3" stroke-width="2"/>') },
      plug9: { name: 'Plug values in', svg: svgI('<path d="M9 3v6M15 3v6M6 9h12v3a6 6 0 01-12 0zM12 18v3"/>') },
      crit9: { name: 'Find the critical points', svg: svgI('<path d="M2 14h20"/><circle cx="8" cy="14" r="2.5"/><circle cx="16" cy="14" r="2.5"/><path d="M8 4v6M16 4v6" stroke-width="2"/>') },
      test9: { name: 'Test an interval', svg: svgI('<path d="M2 16h20"/><path d="M8 16V8h8v8" stroke-dasharray="2 2"/><path d="M12 4v4" stroke-width="2"/>') },
    },
    css: `
      .frac9 .tok.a4 { min-height:0; padding:2px 3px; }
      .tok.a4.fr9 { padding:2px 4px; min-height:0; }
      .tok.a4.f9 { padding:3px 3px; min-width:0; white-space:nowrap; min-height:0; }
      .tok.a4.s9.op9 { font-size:.9em; color:var(--ink); }
      .tok.a4.s9.one9 { color:var(--ink); }
      .tok.a4.s9.words9 { font-size:max(.3em, 12px); color:var(--ink); white-space:normal; max-width:min(560px, 86vw); text-align:center; line-height:1.3; }
      .tok.a4.nlTok9 { padding:2px; min-height:0; }
      .tok.a4.c9.now9 { color:var(--accent); }
      .tok.a4.c9.st9-keep { color:var(--good); } .tok.a4.c9.st9-keep::after { content:' ✓'; }
      .tok.a4.c9.st9-rej { color:var(--bad); text-decoration:line-through; opacity:.75; }
      .bad9t { color:var(--bad); }
      .pop9 { animation: crack8 .5s ease-in forwards; }
      .tok.fr9 > .frac9 > .bar4, .frac9 > .tok.bar9 { width:100%; }
    `,
    graph: null,
  };
  A = KT.makeAct(spec);
  KT.install(spec, A);
  // The card faces for graph cards need the critical points of the problem on screen.
  const baseLabel = A.E.label;
  A.E.label = c => { if (c && c.a9 && c.op === 'gr9' && cur && cur.state && cur.state.k9 === 'ri') cardPts = critOf(cur.state); return baseLabel(c); };
})();
