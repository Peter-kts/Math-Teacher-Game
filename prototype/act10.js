// =====================================================================
//  Act 10: The Hall of Mirrors (functions in depth)
// =====================================================================
// Stage 44  Domain and range        1/(x − 2), √(x + 5), 3/(x² − 9), 4/√(x − 1), √(x + 2)/(x − 5), range of √(x − 1) + 3
// Stage 45  Composition             f(g(2)), (f ∘ g)(x), g(f(x)), f(f(x))
// Stage 46  Inverses                inverse of 3x − 5, (x + 4)/2, x³ + 2; find f⁻¹(7)
// Stage 47  Transformations         y = 2|x − 3| + 1 built from y = |x|; piecewise f(1)
//
// States have their own kind, `k10`:
//   dm  domain or range: the function's parts that limit x (a bottom, a root), conditions set up and
//       solved one at a time, then the answer picked in interval notation. Range builds an inequality
//       from a starting fact (√u ≥ 0, u² ≥ 0, |u| ≥ 0).
//   cp  a composition: evaluate inside out, or put the inner function into the outer one and simplify.
//   iv  an inverse: swap x and y, then solve for y (or find f⁻¹(a) by solving f(x) = a).
//   tf  a transformation: the parent graph is shifted, reflected and stretched until it matches.
//   pw  a piecewise function evaluated at a number: pick the right piece, then work it out.
// index.html switches to this engine (through kit9.js) for generators that return { r10 }.
'use strict';
(function () {
  const KT = window.KIT9;
  if (!KT) return;
  const { P, FN, chance, qid, isTutorial, lvl, supH, supT, XV, numH, parenF, frH, ptrim, pdeg, pco, padd, pscale, psub, pmul, peval, pEq, P1, ptext,
    numberLine, nlWindow, drawCurves, TOK, EQTOK, refOf, kickClass, W9, sym, rowEl, colEl, clone, fNeg, fSub, fDiv, fEq, fz, fv, svgI } = KT;
  const ROOT = (inner, html = true) => (html ? `<span class="rt8"><span class="rs8">√</span><span class="rr8">${inner}</span></span>` : `√(${inner})`);
  const CROOT = (inner, html = true) => (html ? `<span class="rt8"><sup class="nonum ri8">3</sup><span class="rs8">√</span><span class="rr8">${inner}</span></span>` : `∛(${inner})`);
  const INF = '∞';

  // ================================================================ intervals
  // A set of x: { lo: { v, cl } | null, hi: { v, cl } | null, ex: [values] } -> "(−∞, 2) ∪ (2, ∞)"
  function ivText(D) {
    const ex = (D.ex || []).slice().sort((a, b) => fv(a) - fv(b)).filter(v => (!D.lo || fv(v) > fv(D.lo.v)) && (!D.hi || fv(v) < fv(D.hi.v)));
    const pts = [D.lo ? { v: D.lo.v, cl: D.lo.cl } : null, ...ex.map(v => ({ v, cl: false })), D.hi ? { v: D.hi.v, cl: D.hi.cl } : null];
    const segs = [];
    for (let i = 0; i < pts.length - 1; i++) {
      const a = pts[i], b = pts[i + 1];
      segs.push(`${a ? (a.cl ? '[' : '(') + fracText(a.v) : '(' + MINUS + INF}, ${b ? fracText(b.v) + (b.cl ? ']' : ')') : INF + ')'}`);
    }
    return segs.join(' ∪ ');
  }

  // ================================================================ dm: domain and range (stage 44)
  // f forms: den k/(lin), rad √(lin), quadden k/(x² + bx + c), raddown k/√(lin), all (a polynomial), both √(lin)/(lin)
  const dmState = (f, parts, o = {}) => ({ k10: 'dm', f, parts, cs: [], ph: parts.length ? 'pick' : 'all', ans: null, mode: 'dom', skill: o.skill || 'domain', qid: qid() });
  const rgState = (u, h, a, k, o = {}) => ({ k10: 'dm', mode: 'rng', u, h, a: FN(a), k: FN(k), ph: 'base', step: 0, ans: null, skill: o.skill || 'domain', qid: qid() });
  const relFor = kind => (kind === 'den' ? '≠' : kind === 'rad' ? '≥' : '>');
  const flipRel = r => ({ '≥': '≤', '≤': '≥', '>': '<', '<': '>', '≠': '≠' })[r];
  const activeC = e => (e.cs.length && !e.cs[e.cs.length - 1].vals ? e.cs[e.cs.length - 1] : null);
  function dmMoves(e) {
    if (e.mode === 'rng') return rgMoves(e);
    if (e.ph === 'all') return [{ op: 'all10', both: true }];
    if (e.ph === 'pick') return e.parts.map((p, i) => (p.used ? null : { op: 'cond10', refs: ['D' + i], rel: relFor(p.kind), i })).filter(Boolean);
    if (e.ph === 'solve') {
      const c = activeC(e), Lp = c.L;
      if (pdeg(Lp) === 2) return c.fac ? [{ op: 'zp10', both: true }] : [{ op: 'fac10', refs: ['C' + (e.cs.length - 1)], fs: quadRoots(Lp) }];
      if (!fz(pco(Lp, 0))) return [{ op: 'as10', both: true, n: fNeg(pco(Lp, 0)) }];
      if (!fIs(pco(Lp, 1), 1)) return [{ op: 'dv10', both: true, n: pco(Lp, 1), flip: pco(Lp, 1).n < 0 && c.rel !== '≠' }];
      return [];
    }
    if (e.ph === 'final') return [{ op: 'int10', both: true, txt: ivText(dmSet(e)) }];
    return [];
  }
  function quadRoots(p) {   // x² + bx + c with whole roots -> [r1, r2]
    for (let r = -60; r <= 60; r++) { if (!fz(peval(p, F(r)))) continue; const o = fNeg(p[1]).n - r; if (pEq(pmul(P1(1, -r), P1(1, -o)), p)) return [F(r), F(o)].sort((a, b) => fv(b) - fv(a)); }
    return [F(0), F(0)];
  }
  function dmSet(e) {   // the domain from the solved conditions
    const D = { lo: null, hi: null, ex: [] };
    for (const c of e.cs) {
      if (!c.vals) continue;
      if (c.rel === '≠') D.ex.push(...c.vals);
      else if (c.rel === '≥' || c.rel === '>') D.lo = { v: c.vals[0], cl: c.rel === '≥' };
      else D.hi = { v: c.vals[0], cl: c.rel === '≤' };
    }
    return D;
  }
  function solveDone(e) {
    const c = e.cs[e.cs.length - 1]; if (!c || e.ph !== 'solve') return;
    if (!c.vals && pdeg(c.L) === 1 && fIs(pco(c.L, 1), 1) && fz(pco(c.L, 0))) c.vals = [c.R];
    if (c.vals) e.ph = e.parts.every(p => p.used) ? 'final' : 'pick';
  }
  function applyDm(r, m, c) {
    if (r.mode === 'rng') return applyRg(r, m, c);
    switch (m.op) {
      case 'all10': r.ans = '(' + MINUS + INF + ', ' + INF + ')'; r.ph = 'done'; break;
      case 'cond10': { const p = r.parts[m.i]; p.used = true; r.cs.push({ pi: m.i, rel: m.rel, L: clone(p.p), R: F(0), fac: null, vals: null }); r.ph = 'solve'; break; }
      case 'as10': { const k = activeC(r); k.L = padd(k.L, [c.n]); k.R = fAdd(k.R, c.n); break; }
      case 'dv10': { const k = activeC(r); k.L = pscale(k.L, fDiv(F(1), c.n)); k.R = fDiv(k.R, c.n); if (c.n.n < 0) k.rel = flipRel(k.rel); break; }
      case 'fac10': activeC(r).fac = clone(m.fs); break;
      case 'zp10': { const k = activeC(r); k.vals = k.fac.slice().sort((a, b) => fv(a) - fv(b)); break; }
      case 'int10': r.ans = ivText(dmSet(r)); r.ph = 'done'; break;
    }
    solveDone(r);
    return r;
  }
  // range: u ≥ 0, then × a (flip if negative), then + k, then the interval
  function rgMoves(e) {
    if (e.ph === 'base') return [{ op: 'base10', both: true, rel: '≥' }];
    if (e.ph === 'mul') return [{ op: 'ml10', both: true, n: e.a, flip: e.a.n < 0 }];
    if (e.ph === 'add') return [{ op: 'as10', both: true, n: e.k }];
    if (e.ph === 'final') return [{ op: 'int10', both: true, txt: ivText(rgSet(e)) }];
    return [];
  }
  const rgSet = e => (e.a.n > 0 ? { lo: { v: e.k, cl: true }, hi: null } : { lo: null, hi: { v: e.k, cl: true } });
  function applyRg(r, m, c) {
    switch (m.op) {
      case 'base10': r.ph = !fIs(r.a, 1) ? 'mul' : !fz(r.k) ? 'add' : 'final'; r.rel = '≥'; r.did = []; break;
      case 'ml10': r.did.push('mul'); r.rel = r.a.n < 0 ? '≤' : '≥'; r.ph = !fz(r.k) ? 'add' : 'final'; break;
      case 'as10': r.did.push('add'); r.ph = 'final'; break;
      case 'int10': r.ans = ivText(rgSet(r)); r.ph = 'done'; break;
    }
    return r;
  }
  const uH = (e, html = true) => { const inner = ptext(P1(1, fNeg(FN(e.h))), html); return e.u === 'sqrt' ? ROOT(inner, html) : e.u === 'sq' ? `(${inner})${html ? supH(2) : '²'}` : `|${inner}|`; };
  function rgFx(e, html = true) {   // y = a·u + k
    const a = e.a, k = e.k;
    const pre = fIs(a, 1) ? '' : fIs(a, -1) ? MINUS : numH(a, html);
    return pre + uH(e, html) + (fz(k) ? '' : (k.n < 0 ? ` ${MINUS} ` : ' + ') + numH(fAbs(k), html));
  }
  function rgLine(e) {   // the inequality built so far
    if (e.ph === 'base') return null;
    const did = e.did || [];
    const a = did.includes('mul') ? e.a : F(1), k = did.includes('add') ? e.k : F(0);
    const pre = fIs(a, 1) ? '' : fIs(a, -1) ? MINUS : numH(a, true);
    const left = pre + uH(e) + (fz(k) ? '' : (k.n < 0 ? ` ${MINUS} ` : ' + ') + numH(fAbs(k), true));
    return `${left} ${e.rel} ${numH(k, true)}`;
  }
  function fxH(f, html = true, refs = false) {   // the function, with its limiting parts marked as targets
    const T = (h, i) => (refs ? `<span class="tg9 pt10" data-ref="D${i}">${h}</span>` : h);
    const L = p => ptext(p, html);
    switch (f.form) {
      case 'den': return frH(numText(f.k), T(L(f.d), 0));
      case 'rad': return ROOT(T(L(f.r), 0), html);
      case 'quadden': return frH(numText(f.k), T(L(f.d), 0));
      case 'raddown': return frH(numText(f.k), T(ROOT(L(f.r), html), 0));
      case 'all': return L(f.p);
      case 'both': return frH(T(ROOT(L(f.r), html), 0), T(L(f.d), 1));
    }
    return '';
  }

  // ================================================================ cp: composition (stage 45)
  const cpState = (f, g, outer, inner, arg, circ, o = {}) => ({ k10: 'cp', f: f.map(FN), g: g.map(FN), outer, inner, arg: arg === null ? null : FN(arg), circ, ph: circ ? 'circ' : arg === null ? 'sub' : 'in', val: null, res: null, skill: o.skill || 'compose', qid: qid() });
  const fnOf = (e, n) => (n === 'f' ? e.f : e.g);
  const plugged = (outer, inner) => outer.reduce((acc, c, i) => padd(acc, pscale(Array.from({ length: i }).reduce(a => pmul(a, inner), [F(1)]), c)), [F(0)]);
  function plugH(outer, innerH, html = true) {   // 2(x² − 3) + 1, (2x + 1)² − 3
    const ts = [];
    for (let i = outer.length - 1; i >= 0; i--) {
      const c = FN(outer[i]); if (fz(c)) continue;
      const a = fAbs(c), body = i === 0 ? '' : `(${innerH})` + (i > 1 ? (html ? supH(i) : supT(i)) : '');
      ts.push({ neg: c.n < 0, s: (fIs(a, 1) && body ? '' : numH(a, html)) + body });
    }
    return ts.map((t, i) => (i ? (t.neg ? ` ${MINUS} ` : ' + ') : t.neg ? MINUS : '') + t.s).join('');
  }
  function cpMoves(e) {
    switch (e.ph) {
      case 'circ': return [{ op: 'cir10', both: true, form: 'in' }];
      case 'in': return [{ op: 'ev10', both: true, fn: e.inner }];
      case 'out': return [{ op: 'ev10', both: true, fn: e.outer }];
      case 'sub': return [{ op: 'sb10', both: true, form: 'in' }];
      case 'sim': return [{ op: 'sm10', both: true, p: plugged(fnOf(e, e.outer), fnOf(e, e.inner)) }];
    }
    return [];
  }
  function applyCp(r, m, c) {
    switch (m.op) {
      case 'cir10': r.ph = r.arg === null ? 'sub' : 'in'; break;
      case 'ev10': if (r.ph === 'in') { r.val = peval(fnOf(r, r.inner), r.arg); r.ph = 'out'; } else { r.res = peval(fnOf(r, r.outer), r.val); r.ph = 'done'; } break;
      case 'sb10': r.ph = 'sim'; break;
      case 'sm10': r.res = plugged(fnOf(r, r.outer), fnOf(r, r.inner)); r.ph = 'done'; break;
    }
    return r;
  }
  const callH = (e, html = true) => {
    const A_ = e.arg === null ? (html ? XV() : 'x') : numH(e.arg, html);
    return `${e.outer}(${e.inner}(${A_}))`;
  };
  function cpLine(e) {
    const A_ = e.arg === null ? XV() : numH(e.arg, true);
    switch (e.ph) {
      case 'circ': return `(${e.outer} ∘ ${e.inner})(${A_})`;
      case 'in': return `${e.outer}(<span class="tg9 in10" data-ref="IN">${e.inner}(${A_})</span>)`;
      case 'out': return `${e.outer}(${numH(e.val, true)})`;
      case 'sub': return callH(e);
      case 'sim': return plugH(fnOf(e, e.outer), ptext(fnOf(e, e.inner), true));
      case 'done': return e.arg === null ? ptext(e.res, true) : numH(e.res, true);
    }
    return '';
  }

  // ================================================================ iv: inverses (stage 46)
  // f: { t: 'lin', a, b } a·x + b, { t: 'frac', a, b, d } (a·x + b)/d, { t: 'cube', a, b } a·x³ + b.
  // The equation: L (a polynomial in x, or ∛ of one once the cube root is taken) = R: (c·v + d), cube or not.
  const ivState = (f, mode, target, o = {}) => ({ k10: 'iv', f, mode, target: target === null ? null : FN(target), ph: mode === 'val' ? 'set' : 'swap', L: null, R: null, croot: false, skill: o.skill || 'inverse', qid: qid() });
  const fPoly = f => (f.t === 'cube' ? [FN(f.b), F(0), F(0), FN(f.a)] : f.t === 'frac' ? [F(f.b, f.d), F(f.a, f.d)] : [FN(f.b), FN(f.a)]);
  const fEval = (f, v) => peval(fPoly(f), v);
  function fH(f, v = 'x', html = true) {
    const X = html ? XV(v) : v;
    const lin = (a, b, cube) => { const t = (fIs(FN(a), 1) ? '' : fIs(FN(a), -1) ? MINUS : numH(a, html)) + X + (cube ? (html ? supH(3) : '³') : ''); return fz(FN(b)) ? t : t + (b < 0 ? ` ${MINUS} ` : ' + ') + numH(Math.abs(b), html); };
    if (f.t === 'frac') return html ? frH(lin(f.a, f.b), String(f.d)) : `(${lin(f.a, f.b)})/${f.d}`;
    return lin(f.a, f.b, f.t === 'cube');
  }
  const lcmD = fs => fs.reduce((a, f) => a * f.d / gcd(a, f.d), 1);
  function ivMoves(e) {
    if (e.ph === 'set') return [{ op: 'set10', both: true, form: 'solve' }];
    if (e.ph === 'swap') return [{ op: 'sw10', both: true, form: 'swap' }];
    if (e.ph !== 'solve') return [];
    const R = e.R, den = lcmD([R.c, R.d]);
    if (den > 1) return [{ op: 'mlt10', both: true, n: F(den) }];
    if (!fz(R.d)) return [{ op: 'as10y', both: true, n: fNeg(R.d) }];
    if (!fIs(R.c, 1)) return [{ op: 'dv10y', both: true, n: R.c }];
    if (R.cube) return [{ op: 'cr10', both: true }];
    return [];
  }
  function applyIv(r, m, c) {
    const v = r.mode === 'val' ? 'x' : 'y';
    switch (m.op) {
      case 'set10': r.L = [r.target]; r.R = rOf(r.f); r.ph = 'solve'; break;
      case 'sw10': r.L = [F(0), F(1)]; r.R = rOf(r.f); r.ph = 'solve'; break;
      case 'mlt10': r.L = pscale(r.L, c.n); r.R.c = fMul(r.R.c, c.n); r.R.d = fMul(r.R.d, c.n); break;
      case 'as10y': r.L = padd(r.L, [c.n]); r.R.d = fAdd(r.R.d, c.n); break;
      case 'dv10y': r.L = pscale(r.L, fDiv(F(1), c.n)); r.R.c = F(1); r.R.d = fDiv(r.R.d, c.n); break;
      case 'cr10': { r.croot = true; r.R.cube = false; const k = pco(r.L, 0); if (pdeg(r.L) <= 0 && k.d === 1 && Number.isInteger(Math.round(Math.cbrt(k.n))) && Math.round(Math.cbrt(k.n)) ** 3 === k.n) { r.L = [F(Math.round(Math.cbrt(k.n)))]; r.croot = false; } break; }
    }
    if (r.ph === 'solve' && !ivMoves(r).length) r.ph = 'done';
    return r;
  }
  const rOf = f => (f.t === 'frac' ? { c: F(f.a, f.d), d: F(f.b, f.d), cube: false } : { c: FN(f.a), d: FN(f.b), cube: f.t === 'cube' });
  function rH(R, v, html = true) {   // c·v + d written over one bottom when it has fractions
    const den = lcmD([R.c, R.d]);
    const X = (html ? XV(v) : v) + (R.cube ? (html ? supH(3) : '³') : '');
    const top = ptext([fMul(R.d, F(den)), F(1)], html, '§').replace(html ? `<i class="xv">§</i>` : '§', X);
    const cTop = fMul(R.c, F(den));
    const t2 = (fIs(cTop, 1) ? '' : fIs(cTop, -1) ? MINUS : numH(cTop, html)) + X + (fz(R.d) ? '' : (R.d.n < 0 ? ` ${MINUS} ` : ' + ') + numH(fAbs(fMul(R.d, F(den))), html));
    void top;
    return den > 1 ? (html ? frH(t2, String(den)) : `(${t2})/${den}`) : t2;
  }
  function lH(e, html = true) {   // the x side: a polynomial over one bottom, under a cube root once it's taken
    const p = e.L, den = lcmD(p);
    const body = ptext(pscale(p, F(den)), html);
    const t = den > 1 ? (html ? frH(body, String(den)) : `(${body})/${den}`) : body;
    return e.croot ? CROOT(t, html) : t;
  }
  const ivAnsH = (e, html = true) => (e.mode === 'val' ? `f${html ? '<sup class="nonum">−1</sup>' : '⁻¹'}(${numH(e.target, html)}) = ${lH(e, html)}` : `f${html ? '<sup class="nonum">−1</sup>' : '⁻¹'}(${html ? XV() : 'x'}) = ${lH(e, html)}`);
  function invF(e) {   // the inverse as a function, for the graph
    const f = e.f;
    if (f.t === 'cube') return x => Math.cbrt((x - fv(FN(f.b))) / fv(FN(f.a)));
    const p = fPoly(f); return x => (x - fv(p[0])) / fv(p[1]);
  }

  // ================================================================ tf: transformations (stage 47)
  const tfState = (par, T, o = {}) => ({ k10: 'tf', par, T: { a: FN(T.a), h: T.h, k: T.k }, cur: { a: F(1), h: 0, k: 0 }, skill: o.skill || 'transform', qid: qid() });
  function tfMoves(e) {
    const c = e.cur, T = e.T, out = [];
    if (c.h !== T.h) out.push({ op: 'sh10', both: true, h: T.h });
    if (c.k === 0 && Math.sign(c.a.n) !== Math.sign(T.a.n)) out.push({ op: 'rf10', both: true });
    if (c.k === 0 && !fEq(fAbs(c.a), fAbs(T.a))) out.push({ op: 'st10', both: true, s: fAbs(T.a) });
    if (c.k !== T.k && fEq(c.a, T.a)) out.push({ op: 'sv10', both: true, k: T.k });
    return out;
  }
  function applyTf(r, m, c) {
    switch (m.op) {
      case 'sh10': r.cur.h = m.h; break;
      case 'rf10': r.cur.a = fNeg(r.cur.a); break;
      case 'st10': r.cur.a = fMul(F(Math.sign(r.cur.a.n)), m.s); break;
      case 'sv10': r.cur.k = m.k; break;
    }
    return r;
  }
  const PAR = { abs: 'y = |x|', sq: 'y = x²', sqrt: 'y = √x' };
  function tfH(par, s, html = true) {   // y = a·parent(x − h) + k
    const X = html ? XV() : 'x', a = FN(s.a);
    const inner = s.h === 0 ? X : `${X} ${s.h > 0 ? MINUS : '+'} ${Math.abs(s.h)}`;
    const body = par === 'abs' ? `|${inner}|` : par === 'sq' ? (s.h === 0 ? X : `(${inner})`) + (html ? supH(2) : '²') : html ? ROOT(inner) : `√(${inner})`;
    const pre = fIs(a, 1) ? '' : fIs(a, -1) ? MINUS : a.d > 1 ? (html ? frH(String(Math.abs(a.n)), String(a.d)) : fracText(fAbs(a))).replace(/^/, a.n < 0 ? MINUS : '') : numText(a.n);
    return `${html ? XV('y') : 'y'} = ${pre}${body}${s.k === 0 ? '' : (s.k < 0 ? ` ${MINUS} ` : ' + ') + Math.abs(s.k)}`;
  }
  const parF = (par, s) => x => { const u = x - s.h, b = par === 'abs' ? Math.abs(u) : par === 'sq' ? u * u : u >= 0 ? Math.sqrt(u) : NaN; return fv(FN(s.a)) * b + s.k; };

  // ================================================================ pw: piecewise (stage 47)
  // pieces: [{ lo, hi, loC, hiC, p }] (null = no bound); v: the input
  const pwState = (ps, v, o = {}) => ({ k10: 'pw', ps, v, ph: 'pick', i: null, skill: o.skill || 'transform', qid: qid() });
  const inPiece = (pc, v) => (pc.lo === null || (pc.loC ? v >= pc.lo : v > pc.lo)) && (pc.hi === null || (pc.hiC ? v <= pc.hi : v < pc.hi));
  const condH = (pc, html = true) => {
    const X = html ? XV() : 'x';
    if (pc.lo !== null && pc.hi !== null) return `${numText(pc.lo)} ${pc.loC ? '≤' : '<'} ${X} ${pc.hiC ? '≤' : '<'} ${numText(pc.hi)}`;
    if (pc.lo !== null) return `${X} ${pc.loC ? '≥' : '>'} ${numText(pc.lo)}`;
    return `${X} ${pc.hiC ? '≤' : '<'} ${numText(pc.hi)}`;
  };
  function pwMoves(e) {
    if (e.ph === 'pick') return [{ op: 'pc10', both: true, i: e.ps.findIndex(pc => inPiece(pc, e.v)) }];
    if (e.ph === 'ev') return [{ op: 'ev10p', both: true }];
    return [];
  }

  // ================================================================ moves, cards
  const BOTH = new Set(['all10', 'as10', 'dv10', 'zp10', 'int10', 'base10', 'ml10', 'cir10', 'ev10', 'sb10', 'sm10', 'set10', 'sw10', 'mlt10', 'as10y', 'dv10y', 'cr10', 'sh10', 'rf10', 'st10', 'sv10', 'pc10', 'ev10p']);
  const COPY = new Set(['cir10', 'sb10', 'set10', 'sw10', 'pc10', 'all10', 'base10', 'cond10', 'int10', 'sh10', 'rf10', 'st10', 'sv10']);
  const PARAMS = ['rel', 'n', 'flip', 'fs', 'txt', 'form', 'fn', 'p', 'h', 's', 'k', 'i'];
  function moves(e) {
    switch (e.k10) {
      case 'dm': return dmMoves(e);
      case 'cp': return cpMoves(e);
      case 'iv': return ivMoves(e);
      case 'tf': return tfMoves(e);
      case 'pw': return pwMoves(e);
    }
    return [];
  }
  function ok(e, m, c) {
    switch (c.op) {
      case 'cond10': case 'base10': return c.rel === m.rel;
      case 'as10': case 'as10y': case 'dv10y': case 'mlt10': return !!c.n && fEq(FN(c.n), m.n);
      case 'dv10': case 'ml10': return !!c.n && fEq(FN(c.n), m.n) && !!c.flip === !!m.flip;
      case 'fac10': return !!c.fs && c.fs.length === 2 && ((fEq(c.fs[0], m.fs[0]) && fEq(c.fs[1], m.fs[1])) || (fEq(c.fs[0], m.fs[1]) && fEq(c.fs[1], m.fs[0])));
      case 'int10': return c.txt === m.txt;
      case 'cir10': case 'sb10': case 'set10': case 'sw10': return c.form === m.form;
      case 'ev10': return c.fn === m.fn;
      case 'sm10': return !!c.p && pEq(c.p, m.p);
      case 'sh10': return c.h === m.h;
      case 'st10': return !!c.s && fEq(FN(c.s), m.s);
      case 'sv10': return c.k === m.k;
      case 'pc10': return c.i === m.i;
    }
    return true;
  }
  function apply(r, m, c) {
    switch (r.k10) {
      case 'dm': return applyDm(r, m, c);
      case 'cp': return applyCp(r, m, c);
      case 'iv': return applyIv(r, m, c);
      case 'tf': return applyTf(r, m, c);
      case 'pw': if (m.op === 'pc10') { r.i = m.i; r.ph = 'ev'; } else r.ph = 'done'; return r;
    }
    return r;
  }
  const pwVal = e => peval(e.ps[e.i === null ? e.ps.findIndex(pc => inPiece(pc, e.v)) : e.i].p, F(e.v));
  function answer(e, html) {
    switch (e.k10) {
      case 'dm': return e.mode === 'rng' ? `Range: ${e.ans || ''}` : `Domain: ${e.ans || ''}`;
      case 'cp': return e.arg === null ? `${callH(e, html)} = ${ptext(e.res || [F(0)], html)}` : `${callH(e, html)} = ${numH(e.res || F(0), html)}`;
      case 'iv': return ivAnsH(e, html);
      case 'tf': return tfH(e.par, e.cur, html);
      case 'pw': return `f(${e.v}) = ${numH(pwVal(e), html)}`;
    }
    return '';
  }
  const signedN = (n, html) => (FN(n).n < 0 ? MINUS : '+') + numH(fAbs(FN(n)), html);
  const relSym = r => r;
  const CARD = {
    cond10: c => ({ label: { '≠': 'Bottom ≠ 0', '≥': 'Inside ≥ 0', '>': 'Inside > 0', '≤': 'Inside ≤ 0' }[c.rel], text: { '≠': 'A bottom can\'t be 0', '≥': 'A square root needs what\'s inside to be 0 or more', '>': 'Inside a root on the bottom: it must be more than 0', '≤': 'What\'s inside is 0 or less' }[c.rel], kind: 'Set a condition', icon: 'cond10' }),
    all10: () => ({ label: 'All reals', text: 'No bottom, no root: every x works', kind: 'All real numbers', icon: 'all' }),
    as10:  c => ({ label: signedN(c.n, true), text: FN(c.n).n < 0 ? `Subtract ${fracText(fAbs(FN(c.n)))} from both sides` : `Add ${fracText(FN(c.n))} to both sides`, kind: FN(c.n).n < 0 ? 'Subtract' : 'Add', icon: FN(c.n).n < 0 ? 'sub' : 'add' }),
    dv10:  c => ({ label: `${DIV} ${parenF(c.n, true)}${c.flip ? ', flip' : ''}`, text: `Divide both sides by ${fracText(FN(c.n))}${c.flip ? ' and flip the sign' : ''}`, kind: 'Divide', icon: c.flip ? 'flip' : 'div' }),
    ml10:  c => ({ label: `${TIMES} ${parenF(c.n, true)}${c.flip ? ', flip' : ''}`, text: `Multiply both sides by ${fracText(FN(c.n))}${c.flip ? ' and flip the sign' : ''}`, kind: 'Multiply', icon: c.flip ? 'flip' : 'mul' }),
    fac10: c => ({ label: c.fs.map(r => `(${ptext(P1(1, fNeg(FN(r))), true)})`).join(''), text: 'Factor it', kind: 'Factor', icon: 'fac9' }),
    zp10:  () => ({ label: 'Each ≠ 0', text: 'Each factor can\'t be 0', kind: 'Each factor ≠ 0', icon: 'zp9' }),
    int10: c => ({ label: c.txt, text: 'Write it in interval notation', kind: 'Interval notation', icon: 'int10' }),
    base10: c => ({ label: `start ${c.what || ''} ${c.rel} 0`.replace('  ', ' '), text: { '≥': 'It\'s never negative: 0 or more', '>': 'It\'s always more than 0', '≤': 'It\'s never positive' }[c.rel], kind: 'Start from what you know', icon: 'base10' }),
    cir10: c => ({ label: c.lab || c.form, text: { in: 'The inner function goes inside the outer one', rev: 'The other function goes first', mul: 'Multiply the two values' }[c.form], kind: 'Read the notation', icon: 'comp10' }),
    ev10:  c => ({ label: `Work out ${c.fn}(${c.at || '…'})`, text: `Evaluate ${c.fn} at that number`, kind: 'Evaluate', icon: 'plug9' }),
    sb10:  c => ({ label: c.lab || c.form, text: { in: 'Put the inner function in for x', rev: 'Put the outer function in for x', mul: 'Multiply the functions' }[c.form], kind: 'Plug a function in', icon: 'comp10' }),
    sm10:  c => ({ label: ptext(c.p, true), text: 'Distribute and combine like terms', kind: 'Simplify', icon: 'comb' }),
    set10: c => ({ label: c.lab || c.form, text: { solve: 'f⁻¹(a) is the x with f(x) = a', eval: 'Put the number into f', recip: 'One over f of the number' }[c.form], kind: 'Set it up', icon: 'inv10' }),
    sw10:  c => ({ label: c.lab || c.form, text: { swap: 'Swap x and y', recip: 'Flip the right side over', neg: 'Change every sign', undo: 'Change + to −' }[c.form], kind: 'Swap x and y', icon: 'inv10' }),
    mlt10: c => ({ label: `${TIMES} ${numH(c.n, true)}`, text: `Multiply both sides by ${fracText(FN(c.n))}`, kind: 'Multiply', icon: 'mul' }),
    as10y: c => ({ label: signedN(c.n, true), text: FN(c.n).n < 0 ? `Subtract ${fracText(fAbs(FN(c.n)))} from both sides` : `Add ${fracText(FN(c.n))} to both sides`, kind: FN(c.n).n < 0 ? 'Subtract' : 'Add', icon: FN(c.n).n < 0 ? 'sub' : 'add' }),
    dv10y: c => ({ label: `${DIV} ${parenF(c.n, true)}`, text: `Divide both sides by ${fracText(FN(c.n))}`, kind: 'Divide', icon: 'div' }),
    cr10:  () => ({ label: '∛ both', text: 'Take the cube root of both sides', kind: 'Cube root', icon: 'root8' }),
    sh10:  c => ({ label: c.h > 0 ? `Right ${c.h}` : `Left ${-c.h}`, text: `Shift the graph ${c.h > 0 ? 'right' : 'left'} ${Math.abs(c.h)}`, kind: 'Shift sideways', icon: c.h > 0 ? 'right10' : 'left10' }),
    rf10:  () => ({ label: 'Reflect', text: 'Reflect over the x-axis (flip upside down)', kind: 'Reflect', icon: 'refl10' }),
    st10:  c => ({ label: fv(FN(c.s)) > 1 ? `Stretch ${TIMES}${numH(c.s, true)}` : `Shrink ${TIMES}${numH(c.s, true)}`, text: `Stretch it vertically by ${fracText(FN(c.s))}`, kind: 'Stretch', icon: 'str10' }),
    sv10:  c => ({ label: c.k > 0 ? `Up ${c.k}` : `Down ${-c.k}`, text: `Shift the graph ${c.k > 0 ? 'up' : 'down'} ${Math.abs(c.k)}`, kind: 'Shift up or down', icon: c.k > 0 ? 'up10' : 'down10' }),
    pc10:  c => ({ label: c.lab || `Piece ${c.i + 1}`, text: 'Use the piece whose condition fits the number', kind: 'Pick the piece', icon: 'pw10' }),
    ev10p: () => ({ label: 'Work it out', text: 'Put the number into that piece', kind: 'Evaluate', icon: 'plug9' }),
  };

  // ================================================================ decoys
  let A = null;
  const C10 = (op, o) => A.C(op, o);
  const T10 = (...a) => A.trap(...a);
  function specials(e) {
    const out = { rule: [], traps: [] };
    const ms = moves(e), mv = op => ms.find(m => m.op === op);
    if (e.k10 === 'dm' && e.mode === 'dom') {
      if (mv('dv10') && mv('dv10').flip) out.rule.push(C10('dv10', { n: mv('dv10').n, flip: false }));
      if (e.ph === 'pick') { const p = e.parts.find(x => !x.used); if (p && p.kind === 'raddown') out.rule.push(C10('cond10', { rel: '≥' })); if (p && p.kind === 'rad') out.rule.push(C10('cond10', { rel: '>' })); }
      if (e.ph === 'final') { const D = dmSet(e); if (D.ex.length && (D.lo || D.hi)) out.rule.push(C10('int10', { txt: ivText({ ...D, ex: [] }) })); }
      if (e.ph === 'all') out.traps.push(T10('x can\'t be 0', 'all10', `${XV()} ≠ 0`, 'x can never be 0', P('Nothing here divides by x or takes a root, so x = 0 is fine. Only a bottom that could be 0 or a square root of a negative limits the domain.'), 'cond10', 'both'));
    }
    if (e.k10 === 'dm' && e.mode === 'rng') {
      if (mv('ml10') && mv('ml10').flip) out.rule.push(C10('ml10', { n: e.a, flip: false }));
      if (e.ph === 'final') out.traps.push(C10('int10', { txt: ivText(e.a.n > 0 ? { lo: { v: e.k, cl: false } } : { hi: { v: e.k, cl: false } }) }));
    }
    if (e.k10 === 'cp') {
      if (e.ph === 'in' && e.inner !== e.outer) out.rule.push(C10('ev10', { fn: e.outer, at: numH(e.arg, true) }));
      if (e.ph === 'in' || e.ph === 'circ') out.traps.push(T10('multiply them', 'ev10', `${e.outer}(${numText(fv(e.arg || F(0)))}) · ${e.inner}(${numText(fv(e.arg || F(0)))})`, 'Composition means multiplying the two values',
        P(`${callH(e)} means "put ${e.inner}'s answer into ${e.outer}", not multiply. The ∘ is a chain, not a product.`), 'comp10', 'both'));
      if (e.ph === 'sim') { const pr = plugged(fnOf(e, e.outer), fnOf(e, e.inner)); const bad = forgotDist(e); if (bad && !pEq(bad, pr)) out.rule.push(C10('sm10', { p: bad })); }
    }
    if (e.k10 === 'iv') {
      if (e.ph === 'swap') out.rule.push(C10('sw10', { form: 'recip', lab: swapLab(e, 'recip') }));
      if (e.ph === 'set') out.rule.push(C10('set10', { form: 'eval', lab: setLab(e, 'eval') }));
      if (e.ph === 'set') out.traps.push(C10('set10', { form: 'recip', lab: setLab(e, 'recip') }));
    }
    if (e.k10 === 'tf') {
      const sh = mv('sh10'); if (sh) out.rule.push(C10('sh10', { h: -sh.h }));
      const sv = mv('sv10'); if (sv && e.T.h) out.traps.push(C10('sh10', { h: sv.k }));
    }
    if (e.k10 === 'pw' && e.ph === 'pick') {
      const bad = e.ps.findIndex(pc => !inPiece(pc, e.v) && (pc.lo === e.v || pc.hi === e.v));
      if (bad >= 0) out.rule.push(C10('pc10', { i: bad, lab: pcLab(e, bad) }));
    }
    return out;
  }
  function forgotDist(e) {   // 2(x² − 3) + 1 -> 2x² − 3 + 1: only the first term multiplied
    const o = fnOf(e, e.outer), inn = fnOf(e, e.inner);
    if (pdeg(o) !== 1) { const sq = pmul(inn, inn); return padd(pscale([sq[0], F(0), ...sq.slice(2)], o[2] || F(1)), padd(pscale(inn, o[1] || F(0)), [o[0]])); }
    const lead = inn.map((c, i) => (i === pdeg(inn) ? fMul(c, o[1]) : c));
    return padd(lead, [o[0]]);
  }
  const swapLab = (e, form) => {
    const f = e.f, y = XV('y'), x = XV();
    if (form === 'swap') return `${x} = ${fH(f, 'y')}`;
    if (form === 'recip') return `${y} = ${frH('1', fH(f))}`;
    if (form === 'neg') return `${y} = ${MINUS}(${fH(f)})`;
    return `${y} = ${fH({ ...f, b: -f.b })}`;
  };
  const setLab = (e, form) => (form === 'solve' ? `${fH(e.f)} = ${numH(e.target, true)}` : form === 'eval' ? `f(${numH(e.target, true)})` : frH('1', `f(${numH(e.target, true)})`));
  const pcLab = (e, i) => `${ptext(e.ps[i].p, true)} <small>(${condH(e.ps[i])})</small>`;
  const cirLab = (e, form) => { const A_ = e.arg === null ? XV() : numH(e.arg, true); return form === 'in' ? `${e.outer}(${e.inner}(${A_}))` : form === 'rev' ? `${e.inner}(${e.outer}(${A_}))` : `${e.outer}(${A_}) · ${e.inner}(${A_})`; };
  const sbLab = (e, form) => form === 'in' ? plugH(fnOf(e, e.outer), ptext(fnOf(e, e.inner), true)) : form === 'rev' ? plugH(fnOf(e, e.inner), ptext(fnOf(e, e.outer), true)) : `(${ptext(fnOf(e, e.outer), true)})(${ptext(fnOf(e, e.inner), true)})`;
  function family(e) {
    const f = [], ms = moves(e), m0 = ms[0];
    if (e.k10 === 'dm' && e.mode === 'dom') {
      ['≠', '≥', '>'].forEach(rel => f.push(C10('cond10', { rel })));
      f.push(C10('all10'));
      const c = activeC(e);
      if (c && pdeg(c.L) === 1) { const a = pco(c.L, 1), b = pco(c.L, 0); f.push(C10('as10', { n: b.n ? b : F(1) }), C10('dv10', { n: fNeg(a.n === 1 && a.d === 1 ? F(2) : a), flip: false })); if (!fz(b)) f.push(C10('dv10', { n: fIs(a, 1) ? F(2) : a, flip: c.rel !== '≠' && a.n < 0 })); if (fz(b) && !fIs(a, 1)) f.push(C10('dv10', { n: a, flip: !(a.n < 0 && c.rel !== '≠') && c.rel !== '≠' })); }
      if (c && pdeg(c.L) === 2) { const rs = quadRoots(c.L); f.push(C10('fac10', { fs: rs.map(fNeg) }), C10('fac10', { fs: [rs[0], fNeg(rs[1])] }), C10('zp10')); }
      if (e.ph === 'final') { const D = dmSet(e); [{ ...D, lo: D.lo && { ...D.lo, cl: !D.lo.cl }, hi: D.hi && { ...D.hi, cl: !D.hi.cl } }, D.lo ? { hi: { v: D.lo.v, cl: D.lo.cl }, ex: D.ex } : D.hi ? { lo: { v: D.hi.v, cl: D.hi.cl }, ex: D.ex } : { ex: D.ex.map(fNeg) }, { lo: null, hi: null, ex: [] }].forEach(x => f.push(C10('int10', { txt: ivText(x) }))); if (D.ex.length > 1) f.push(C10('int10', { txt: ivText({ ...D, ex: D.ex.slice(1) }) })); }
      return f;
    }
    if (e.k10 === 'dm') {
      const what = uH(e);
      ['≥', '>', '≤'].forEach(rel => f.push(C10('base10', { rel, what })));
      f.push(C10('ml10', { n: e.a, flip: !(e.a.n < 0) }), C10('as10', { n: fNeg(e.k.n ? e.k : F(1)) }), C10('ml10', { n: fNeg(e.a), flip: true }));
      const S_ = rgSet(e); f.push(C10('int10', { txt: ivText(S_.lo ? { hi: { v: S_.lo.v, cl: true } } : { lo: { v: S_.hi.v, cl: true } }) }), C10('int10', { txt: ivText(S_.lo ? { lo: { v: fNeg(S_.lo.v), cl: true } } : { hi: { v: fNeg(S_.hi.v), cl: true } }) }), C10('int10', { txt: '(' + MINUS + INF + ', ' + INF + ')' }));
      return f;
    }
    if (e.k10 === 'cp') {
      const A_ = e.arg === null ? '…' : numH(e.arg, true);
      ['in', 'rev', 'mul'].forEach(form => { f.push(C10('cir10', { form, lab: cirLab(e, form) })); f.push(C10('sb10', { form, lab: sbLab(e, form) })); });
      f.push(C10('ev10', { fn: e.inner, at: A_ }), C10('ev10', { fn: e.outer, at: e.ph === 'out' ? numH(e.val || F(0), true) : A_ }));
      if (e.ph === 'sim') { const p = m0.p; f.push(C10('sm10', { p: padd(p, [F(2)]) }), C10('sm10', { p: plugged(fnOf(e, e.inner), fnOf(e, e.outer)) }), C10('sm10', { p: pmul(fnOf(e, e.outer), fnOf(e, e.inner)) })); }
      return f;
    }
    if (e.k10 === 'iv') {
      if (e.ph === 'swap') ['swap', 'recip', 'neg', 'undo'].forEach(form => f.push(C10('sw10', { form, lab: swapLab(e, form) })));
      if (e.ph === 'set') ['solve', 'eval', 'recip'].forEach(form => f.push(C10('set10', { form, lab: setLab(e, form) })));
      if (e.ph === 'solve') {
        const R = e.R;
        if (!fz(R.d)) f.push(C10('as10y', { n: R.d }), C10('dv10y', { n: fIs(R.c, 1) ? F(2) : R.c }));
        if (!fIs(R.c, 1)) f.push(C10('dv10y', { n: fNeg(R.c) }), C10('as10y', { n: fNeg(R.c) }), C10('mlt10', { n: R.c.d > 1 ? F(R.c.n) : R.c }));
        if (R.cube) f.push(C10('cr10'), C10('dv10y', { n: F(3) }));
        else f.push(C10('cr10'));
        f.push(C10('mlt10', { n: F(2) }));
      }
      return f;
    }
    if (e.k10 === 'tf') {
      const T = e.T;
      f.push(C10('sh10', { h: T.h || 2 }), C10('sh10', { h: -(T.h || 2) }), C10('sv10', { k: T.k || 1 }), C10('sv10', { k: -(T.k || 1) }), C10('rf10'), C10('st10', { s: fAbs(T.a).n > 1 || fAbs(T.a).d > 1 ? fAbs(T.a) : F(2) }), C10('st10', { s: fDiv(F(1), fAbs(T.a).n > 1 ? fAbs(T.a) : F(2)) }));
      if (T.h) f.push(C10('sv10', { k: T.h }), C10('sv10', { k: -T.h }));
      if (T.k) f.push(C10('sh10', { h: T.k }), C10('sh10', { h: -T.k }));
      return f;
    }
    if (e.k10 === 'pw') { e.ps.forEach((_, i) => f.push(C10('pc10', { i, lab: pcLab(e, i) }))); f.push(C10('ev10p')); return f; }
    return f;
  }
  // The hand's card faces that depend on the problem (labels with its numbers) are filled in here.
  function dress(e, c) {
    if (!c || !c.a10) return c;
    if (c.op === 'cir10' && !c.lab) c.lab = cirLab(e, c.form);
    if (c.op === 'sb10' && !c.lab) c.lab = sbLab(e, c.form);
    if (c.op === 'sw10' && !c.lab) c.lab = swapLab(e, c.form);
    if (c.op === 'set10' && !c.lab) c.lab = setLab(e, c.form);
    if (c.op === 'pc10' && !c.lab) c.lab = pcLab(e, c.i);
    if (c.op === 'ev10' && !c.at) c.at = e.ph === 'out' ? numH(e.val, true) : e.arg === null ? XV() : numH(e.arg, true);
    if (c.op === 'base10' && !c.what) c.what = uH(e);
    return c;
  }
  const filler = () => [2, 3, 5, 4, 6, 7].map(n => C10('as10', { n: F(n) }));
  function placesOf(e, op) {
    if (e.k10 === 'dm' && e.mode === 'dom') { if (op === 'cond10') return e.ph === 'pick' ? e.parts.map((_, i) => 'D' + i) : []; if (op === 'fac10') return activeC(e) ? ['C' + (e.cs.length - 1)] : []; }
    return [];
  }

  // ================================================================ wrong-move reasons
  function why(e, card, ref, S, next) {
    const ms = moves(e), m0 = ms[0];
    if (e.k10 === 'dm' && e.mode === 'dom') {
      switch (card.op) {
        case 'cond10': {
          if (e.ph !== 'pick') return S('Finish this condition first.');
          const p = e.parts[+(ref || 'D0').slice(1)] || e.parts.find(x => !x.used);
          if (!p) return S('There\'s nothing left to check.');
          if (p.kind === 'den') return S('A bottom just can\'t be 0.', 'Dividing by 0 is undefined, so set the bottom ≠ 0. Any other value (negative too) is fine.');
          if (p.kind === 'rad') return S(card.rel === '>' ? 'A square root of 0 is fine: use ≥.' : 'Inside a square root must be 0 or more.', `√0 = 0 is allowed; only negatives aren't (no real square root). So what's inside must be ≥ 0.`);
          return S('This root is on the bottom: it can\'t be 0 either.', 'A square root on the bottom must be more than 0: negative has no real root, and 0 would divide by 0. Use > 0.');
        }
        case 'all10': return S(`Something here limits x: ${e.parts.length > 1 ? 'a bottom and a root' : e.parts[0].kind === 'den' ? 'a bottom' : 'a square root'}.`, 'Every x works only when there\'s no bottom with x in it and no square root of an expression with x.');
        case 'as10': case 'dv10': {
          if (e.ph !== 'solve') return S('Set up the condition first.');
          const c = activeC(e);
          if (card.op === 'dv10' && m0.op === 'dv10' && fEq(FN(card.n), m0.n) && !!card.flip !== !!m0.flip) return S(m0.flip ? 'Dividing by a negative flips the sign.' : 'Only a negative flips the sign.', m0.flip ? `Dividing both sides of an inequality by a negative number reverses it: ${c.rel} becomes ${flipRel(c.rel)}. (−2 < 4 but 1 > −2.)` : 'Flip the inequality only when multiplying or dividing by a negative number.');
          return S('That doesn\'t get x alone.', `Undo + or − first, then × or ÷.${next}`);
        }
        case 'fac10': return m0 && m0.op === 'fac10' ? S('Those factors don\'t multiply back.') : S('There\'s no quadratic to factor.');
        case 'zp10': return S('Factor first.');
        case 'int10': {
          if (e.ph !== 'final') return S('Finish the conditions first.');
          const D = dmSet(e);
          return S(`It's ${m0.txt}.`, `${D.ex.length ? `x ≠ ${D.ex.map(fracText).join(', ')} leaves gaps: each one is a round bracket on both sides of it, joined with ∪. ` : ''}${D.lo ? `x ${D.lo.cl ? '≥' : '>'} ${fracText(D.lo.v)}: ${D.lo.cl ? 'a square bracket [ includes the number' : 'a round bracket ( leaves it out'}. ` : ''}${D.hi ? `x ${D.hi.cl ? '≤' : '<'} ${fracText(D.hi.v)}: ${D.hi.cl ? ']' : ')'} at the end. ` : ''}∞ always gets a round bracket.`);
        }
      }
      return null;
    }
    if (e.k10 === 'dm') {
      switch (card.op) {
        case 'base10': return e.ph !== 'base' ? S('You started already.') : S(`${uH(e)} is never negative: it's ≥ 0.`, `${e.u === 'sqrt' ? 'A square root' : e.u === 'sq' ? 'A square' : 'An absolute value'} is 0 or more, and it can be exactly 0 (at x = ${fracText(FN(e.h))}). So start from ${uH(e)} ≥ 0.`);
        case 'ml10': return e.ph !== 'mul' ? S('Not now.') : S(e.a.n < 0 ? 'Multiplying by a negative flips the sign.' : 'Multiply by the number in front.', `The function has ${numH(e.a, true)} in front, so multiply both sides by ${numH(e.a, true)}${e.a.n < 0 ? ', and flip ≥ to ≤ because it\'s negative' : ''}.`);
        case 'as10': return e.ph === 'mul' ? S('Multiply first, then add.', `Order matters: the function is ${rgFx(e)}, the number in front multiplies first.`) : S(`Add ${fracText(e.k)}, the number on the end.`);
        case 'int10': return e.ph !== 'final' ? S('Build the inequality first.') : S(`It's ${m0.txt}.`, `y ${e.a.n > 0 ? '≥' : '≤'} ${fracText(e.k)}: the value ${fracText(e.k)} is reached, so its bracket is square.`);
      }
      return null;
    }
    if (e.k10 === 'cp') {
      switch (card.op) {
        case 'cir10': return S(`(${e.outer} ∘ ${e.inner}) means ${e.outer} of ${e.inner}.`, `Read (f ∘ g)(x) as f(g(x)): g acts first, then f acts on g's answer.`);
        case 'ev10': return e.ph === 'in' ? S('Work from the inside out.', `In ${callH(e)}, first find ${e.inner}(${numH(e.arg, true)}), then put that answer into ${e.outer}.`) : e.ph === 'out' ? S(`Now ${e.outer} of that answer.`) : S('Rewrite it first.');
        case 'sb10': return S(`${e.inner}(x) goes inside ${e.outer}.`, `${callH(e)}: replace every x in ${e.outer}(x) = ${ptext(fnOf(e, e.outer), true)} with (${ptext(fnOf(e, e.inner), true)}).`);
        case 'sm10': return e.ph !== 'sim' ? S('Plug in first.') : S(`It simplifies to ${ptext(m0.p, true)}.`, `Distribute to <b>every</b> term in the bracket${pdeg(fnOf(e, e.outer)) > 1 ? ', and square the whole bracket: (a + b)² = a² + 2ab + b²' : ''}, then combine like terms.`);
      }
      return null;
    }
    if (e.k10 === 'iv') {
      switch (card.op) {
        case 'sw10': return e.ph !== 'swap' ? S('Already swapped.') : card.form === 'recip' ? S('f⁻¹ isn\'t 1/f.', 'The −1 in f⁻¹ means "inverse", not a power. The inverse undoes f: swap x and y, then solve for y.') : S('Swap x and y.', 'The inverse undoes f: its inputs are f\'s outputs. Swap x and y, then solve for y.');
        case 'set10': return card.form === 'eval' ? S('f⁻¹(a) isn\'t f(a).', `f⁻¹(${fracText(e.target)}) is the input that gives ${fracText(e.target)}: solve ${fH(e.f, 'x', true)} = ${numH(e.target, true)}.`) : S('The −1 isn\'t a power.', `f⁻¹(${fracText(e.target)}) is the x with f(x) = ${fracText(e.target)}, not 1/f(${fracText(e.target)}).`);
        case 'cr10': return e.R && e.R.cube ? S('Get the cube alone first.') : S('There\'s no cube to undo.');
        default: return S('That doesn\'t get it alone.', `Undo what's done to ${e.mode === 'val' ? 'x' : 'y'} in reverse order: + or − first, then × or ÷.${next}`);
      }
    }
    if (e.k10 === 'tf') {
      const T = e.T, c = e.cur;
      switch (card.op) {
        case 'sh10': return c.h === T.h ? S('It\'s already in the right place sideways.') : S(`(x ${T.h > 0 ? MINUS : '+'} ${Math.abs(T.h)}) moves it ${T.h > 0 ? 'right' : 'left'}.`, `Inside the function the shift goes the opposite way to the sign: x − 3 is 0 at x = 3, so the corner moves to x = 3 (right). x + 3 moves it left.`);
        case 'sv10': return !fEq(c.a, T.a) ? S('Stretch and reflect before shifting up or down.', 'A stretch multiplies everything, including a shift you already made. Do the stretch or reflection first, then the shift up or down.') : S(`The number added at the end is ${T.k}.`, 'A number added outside the function moves the graph up (+) or down (−).');
        case 'rf10': return c.k ? S('Reflect before shifting up or down.') : S('It isn\'t upside down.', 'Reflect over the x-axis only when the number in front is negative.');
        case 'st10': return c.k ? S('Stretch before shifting up or down.') : S(`The number in front is ${fracText(fAbs(T.a))}.`, `A number in front stretches it vertically (bigger than 1) or squashes it (between 0 and 1).`);
      }
      return null;
    }
    if (e.k10 === 'pw') {
      if (card.op === 'pc10' && e.ph !== 'pick') return S('The piece is already picked: now put the number in.');
      if (card.op === 'pc10') { const i = m0 ? m0.i : 0; return S(`${e.v} fits ${condH(e.ps[i])}.`, `Check the condition of each piece with x = ${e.v}. Watch the ends: ≤ and ≥ include the number, < and > don't.`); }
      return S('Pick the piece first.');
    }
    return null;
  }

  // ================================================================ rendering and graph
  function render(e, el, R) {
    const T = (h, ref, cls = 't9') => R.TOK(R.W9(h), 'x', ref, cls);
    if (e.k10 === 'dm' && e.mode === 'dom') {
      const rows = [R.rowEl([T(`f(${XV()}) = ${fxH(e.f, true, e.ph === 'pick')}`, null)])];
      e.cs.forEach((c, i) => {
        let h;
        if (c.vals) h = `${XV()} ${c.rel} ${c.vals.map(v => numH(v, true)).join(c.rel === '≠' ? ', ' : '')}`;
        else if (c.fac) h = `${c.fac.map(r => `(${ptext(P1(1, fNeg(r)), true)})`).join('')} ${c.rel} 0`;
        else h = `${ptext(c.L, true)} ${c.rel} ${numH(c.R, true)}`;
        rows.push(R.rowEl([T(h, 'C' + i, 't9 small9' + (c.vals ? ' done10' : ''))]));
      });
      if (e.ph === 'done') rows.push(R.rowEl([R.sym(`Domain: ${e.ans}`, 'fin9')]));
      if (e.ph === 'final' || e.ph === 'done') rows.push(R.rowEl([R.TOK(domNl(dmSet(e)), 'nl', 'NL', 'nlTok9')]));
      el.appendChild(R.colEl(rows));
      return;
    }
    if (e.k10 === 'dm') {
      const rows = [R.rowEl([T(`f(${XV()}) = ${rgFx(e)}`, null)])];
      const ln = rgLine(e); if (ln) rows.push(R.rowEl([T(ln, 'G', 't9 small9')]));
      if (e.ph === 'final' || e.ph === 'done') rows.push(R.rowEl([T(`f(${XV()}) ${e.a.n > 0 ? '≥' : '≤'} ${numH(e.k, true)}`, 'Y', 't9 small9')]));
      if (e.ph === 'done') rows.push(R.rowEl([R.sym(`Range: ${e.ans}`, 'fin9')]));
      el.appendChild(R.colEl(rows));
      return;
    }
    if (e.k10 === 'cp') {
      const defs = `f(${XV()}) = ${ptext(e.f, true)}   ·   g(${XV()}) = ${ptext(e.g, true)}`;
      const rows = [R.rowEl([R.sym(defs, 'defs10')]), R.rowEl([T(e.ph === 'done' || e.ph === 'sim' ? `${callH(e)} = ${cpLine(e)}` : cpLine(e), 'W')])];
      if (e.ph === 'done') rows.push(R.rowEl([R.sym(answer(e, true), 'fin9')]));
      el.appendChild(R.colEl(rows));
      return;
    }
    if (e.k10 === 'iv') {
      const top = e.mode === 'val' ? `f(${XV()}) = ${fH(e.f)}` : `f(${XV()}) = ${fH(e.f)}`;
      const rows = [R.rowEl([R.sym(top, 'defs10')])];
      if (e.ph === 'swap') rows.push(R.rowEl([T(`${XV('y')} = ${fH(e.f)}`, 'W')]));
      else if (e.ph === 'set') rows.push(R.rowEl([T(`f<sup class="nonum">−1</sup>(${numH(e.target, true)}) = ?`, 'W')]));
      else {
        const v = e.mode === 'val' ? 'x' : 'y';
        const line = e.mode === 'val' ? `${rH(e.R, v)} = ${lH(e)}` : `${lH(e)} = ${rH(e.R, v)}`;
        if (e.ph === 'done') rows.push(R.rowEl([T(ivAnsH(e), 'W', 't9 fin9')]));
        else rows.push(R.rowEl([T(line, 'W')]));
      }
      el.appendChild(R.colEl(rows));
      return;
    }
    if (e.k10 === 'tf') {
      const rows = [R.rowEl([R.sym(`Make: ${tfH(e.par, e.T)}`, 'defs10')]), R.rowEl([T(tfH(e.par, e.cur), 'W')])];
      el.appendChild(R.colEl(rows));
      return;
    }
    if (e.k10 === 'pw') {
      const brace = `<span class="pw10">${e.ps.map((pc, i) => `<span class="pwr10 ${e.i === i ? 'on10' : ''}">${ptext(pc.p, true)}, <span class="nonum">${condH(pc)}</span></span>`).join('')}</span>`;
      const rows = [R.rowEl([T(`f(${XV()}) = ${brace}`, null, 't9 small9')]), R.rowEl([T(e.ph === 'done' ? `f(${e.v}) = ${numH(pwVal(e), true)}` : e.ph === 'ev' ? `f(${e.v}) = ${ptext(e.ps[e.i].p, true).replace(/<i class="xv">x<\/i>/g, `(${numText(e.v)})`)}` : `f(${numText(e.v)}) = ?`, 'W')])];
      el.appendChild(R.colEl(rows));
    }
  }
  function domNl(D) {
    const xs = [...(D.ex || []), D.lo && D.lo.v, D.hi && D.hi.v].filter(Boolean).map(fv), w = nlWindow(xs.length ? xs : [0]);
    const pts = [...(D.ex || []).map(v => ({ x: fv(v), open: true })), ...(D.lo ? [{ x: fv(D.lo.v), open: !D.lo.cl }] : []), ...(D.hi ? [{ x: fv(D.hi.v), open: !D.hi.cl }] : [])];
    const lo = D.lo ? fv(D.lo.v) : null, hi = D.hi ? fv(D.hi.v) : null;
    return numberLine({ lo: w.lo, hi: w.hi, pts: pts.map(p => ({ ...p, lab: fracText(F(p.x)) })), shade: [[lo, hi]] });
  }
  function graph(e) {
    if (e.k10 === 'tf') {
      const T = e.T, c = e.cur, a = fv(T.a);
      const win = KT.square(T.h, T.k + (a > 0 ? 2.5 : -2.5), 6);
      drawCurves({ win, qid: 'tf' + e.qid, curves: [{ f: parF(e.par, T), cls: 'ghost9', key: 'T' }, { f: parF(e.par, c), cls: '', key: JSON.stringify(c) }] });
      return;
    }
    if (e.k10 === 'iv' && e.mode === 'inv') {
      const f = x => fv(fEval(e.f, F(Math.round(x * 1000), 1000)));
      const curves = [{ f, cls: '', key: 'f' }];
      if (e.ph === 'done') curves.push({ f: x => x, cls: 'mir9', key: 'yx' }, { f: invF(e), cls: 'alt9', key: 'inv' });
      drawCurves({ win: { x0: -8, x1: 8, y0: -8, y1: 8 }, qid: 'iv' + e.qid, curves });
    }
  }

  // ================================================================ prompts, text
  const PR = {
    dom: ['Find the domain. Write it in interval notation.', 'State the domain of f.', 'What is the domain? Use interval notation.'],
    rng: ['Find the range. Write it in interval notation.', 'State the range of f.', 'What is the range?'],
    cpn: ['Evaluate.', 'Find the value.', 'Evaluate the composition.'],
    cpx: ['Find and simplify.', 'Write the composition as one polynomial.', 'Simplify the composite function.'],
    inv: ['Find the inverse function.', 'Find f⁻¹(x).', 'Write the inverse of f.'],
    val: ['Find the value of the inverse.', 'Evaluate the inverse.', 'Find the input that gives this output.'],
    tf: ['Build the graph from its parent.', 'Describe the transformations, in order.', 'Transform the parent graph to match.'],
    pw: ['Evaluate the piecewise function.', 'Find the value.', 'Evaluate.'],
  };
  function promptKey(s) {
    switch (s.k10) {
      case 'dm': return s.mode === 'rng' ? 'rng' : 'dom';
      case 'cp': return s.arg === null ? 'cpx' : 'cpn';
      case 'iv': return s.mode === 'val' ? 'val' : 'inv';
      case 'tf': return 'tf';
      case 'pw': return 'pw';
    }
    return 'dom';
  }
  function textOf(e) {
    switch (e.k10) {
      case 'dm': return e.mode === 'rng' ? `rng ${rgFx(e, false)}` : `dom ${fxH(e.f, false).replace(/<[^>]+>/g, '')}`;
      case 'cp': return `cp ${ptext(e.f)} ; ${ptext(e.g)} ; ${callH(e, false)} ${e.circ ? 'o' : ''}`;
      case 'iv': return `iv ${e.mode} ${fH(e.f, 'x', false)} ${e.target ? fracText(e.target) : ''}`;
      case 'tf': return `tf ${tfH(e.par, e.T, false)}`;
      case 'pw': return `pw ${e.ps.map(p => ptext(p.p) + condH(p, false)).join(';')} @${e.v}`;
    }
    return '';
  }

  // ================================================================ animations
  const anim = {
    async cond10(c, s, ns, ref, H) {
      const t = H.tk(ref); H.mark([ref]);
      const n = await H.written(`${c.rel} 0`, [t], { '≠': 'A bottom can\'t be 0', '≥': 'Inside a square root: 0 or more', '>': 'A root on the bottom: more than 0' }[c.rel]); dropNote(n);
      await H.result(ns, ['C' + (ns.cs.length - 1)], 'Now solve that condition for x');
    },
    async all10(c, s, ns, ref, H) { caption('No bottom with x, no square root: nothing can go wrong, so every real number works'); await quick(300); await H.result(ns, ['NL'], ''); },
    async as10(c, s, ns, ref, H) { const ref0 = s.mode === 'rng' ? 'G' : 'C' + (s.cs.length - 1); await H.both(signedN(c.n, true), [ref0], cardText(c)); await H.result(ns, [ref0, 'Y'], ''); },
    async dv10(c, s, ns, ref, H) {
      const ref0 = 'C' + (s.cs.length - 1); caption(cardText(c));
      const n = note(numH(FN(c.n), true), [H.tk(ref0)], { bar: true }); n.classList.add('n9'); await quick(150); await hold(); dropNote(n);
      await H.result(ns, [ref0], c.flip ? 'Divided by a negative: the sign flipped' : '');
    },
    async ml10(c, s, ns, ref, H) { await H.both(`${TIMES} ${parenF(c.n, true)}`, ['G'], cardText(c) + (c.flip ? ': a negative flips ≥ to ≤' : '')); await H.result(ns, ['G'], ''); },
    async fac10(c, s, ns, ref, H) { const t = H.tk(ref); H.mark([ref]); const n = await H.written(CARD.fac10(c).label, [t], 'Factor the bottom: it is 0 when either factor is 0'); dropNote(n); await H.result(ns, [ref], ''); },
    async zp10(c, s, ns, ref, H) { caption('A product is 0 when a factor is 0, so neither factor may be 0'); await quick(250); await H.result(ns, ['C' + (s.cs.length - 1)], ''); },
    async int10(c, s, ns, ref, H) { caption('Write the set: [ ] includes the number, ( ) leaves it out, ∪ joins the pieces'); await quick(250); await H.result(ns, ['NL'], `${s.mode === 'rng' ? 'Range' : 'Domain'}: ${c.txt}`); },
    async base10(c, s, ns, ref, H) { caption(`${uH(s, false).replace(/<[^>]+>/g, '')} is never negative: start from ≥ 0`); await quick(250); await H.result(ns, ['G'], 'Now build the function on the left, doing the same to the right'); },
    async cir10(c, s, ns, ref, H) { const t = H.tk('W'); H.mark(['W']); const n = await H.written(cirLab(s, 'in'), [t], `(${s.outer} ∘ ${s.inner}) means ${s.outer} of ${s.inner}: ${s.inner} acts first`); dropNote(n); await H.result(ns, ['W'], ''); },
    async ev10(c, s, ns, ref, H) {
      const inner = s.ph === 'in', fn = inner ? s.inner : s.outer, at = inner ? s.arg : s.val, val = peval(fnOf(s, fn), at);
      const t = H.tk(inner ? 'IN' : 'W') || H.tk('W'); H.mark([inner ? 'IN' : 'W']);
      const sub = ptext(fnOf(s, fn), true).replace(/<i class="xv">x<\/i>/g, `(${numText(fv(at))})`);
      const n = await H.written(`${fn}(${numText(fv(at))}) = ${sub}`, [t], inner ? 'Inside first: work out the inner function' : 'Now put that answer into the outer function'); dropNote(n);
      await H.result(ns, ['W'], `${fn}(${fracText(at)}) = ${fracText(val)}`);
    },
    async sb10(c, s, ns, ref, H) {
      const t = H.tk('W'); H.mark(['W']);
      const n = await H.written(`${XV()} → (${ptext(fnOf(s, s.inner), true)})`, [t], `Replace every x in ${s.outer}(x) with ${s.inner}(x)`); dropNote(n);
      await H.result(ns, ['W'], 'Now simplify');
    },
    async sm10(c, s, ns, ref, H) { const t = H.tk('W'); H.mark(['W']); caption('Distribute to every term, then combine like terms'); await quick(300); await H.result(ns, ['W'], `= ${ptext(c.p)}`); },
    async set10(c, s, ns, ref, H) { const t = H.tk('W'); H.mark(['W']); const n = await H.written(setLab(s, 'solve'), [t], `f⁻¹(${fracText(s.target)}) is the input that f turns into ${fracText(s.target)}`); dropNote(n); await H.result(ns, ['W'], 'Solve for x'); },
    async sw10(c, s, ns, ref, H) {
      const t = H.tk('W'); H.mark(['W']); if (t) t.classList.add('spin');
      caption('Swap x and y: the inverse runs f backwards. On the graph it mirrors across y = x');
      await quick(450); await H.result(ns, ['W'], 'Now solve for y');
    },
    async mlt10(c, s, ns, ref, H) { await H.both(`${TIMES} ${numH(FN(c.n), true)}`, ['W'], cardText(c)); await H.result(ns, ['W'], ''); },
    async as10y(c, s, ns, ref, H) { await H.both(signedN(c.n, true), ['W'], cardText(c)); await H.result(ns, ['W'], ''); },
    async dv10y(c, s, ns, ref, H) { caption(cardText(c)); const n = note(numH(FN(c.n), true), [H.tk('W')], { bar: true }); n.classList.add('n9'); await quick(150); await hold(); dropNote(n); await H.result(ns, ['W'], ns.ph === 'done' ? 'Alone. The graph of the inverse is the mirror image across y = x' : ''); },
    async cr10(c, s, ns, ref, H) { await H.both('∛', ['W'], 'A cube root undoes a cube'); await H.result(ns, ['W'], ''); },
    async sh10(c, s, ns, ref, H) { caption(`Inside the function, ${c.h > 0 ? 'x − ' + c.h : 'x + ' + (-c.h)} moves the graph ${c.h > 0 ? 'right' : 'left'} ${Math.abs(c.h)}`); await quick(250); await H.result(ns, ['W'], ''); },
    async rf10(c, s, ns, ref, H) { caption('A minus in front flips the graph over the x-axis'); await quick(250); await H.result(ns, ['W'], ''); },
    async st10(c, s, ns, ref, H) { caption(`The number in front stretches every height by ${fracText(FN(c.s))}`); await quick(250); await H.result(ns, ['W'], ''); },
    async sv10(c, s, ns, ref, H) { caption(`A number added at the end moves the graph ${c.k > 0 ? 'up' : 'down'} ${Math.abs(c.k)}`); await quick(250); await H.result(ns, ['W'], ns.k10 === 'tf' && !moves(ns).length ? 'It matches' : ''); },
    async pc10(c, s, ns, ref, H) { caption(`${s.v} fits the condition of that piece`); await quick(250); await H.result(ns, ['W'], 'Put the number into that piece'); },
    async ev10p(c, s, ns, ref, H) { caption('Work it out'); await quick(200); await H.result(ns, ['W'], `f(${s.v}) = ${fracText(pwVal(ns))}`); },
  };

  // ================================================================ generators
  const sgn = () => (chance(0.5) ? 1 : -1);
  const nz = (a, b) => nonZero(a, b);
  const big = L => [6, 8, 10, 12][L];
  const done = (st, n) => st && A.okPath(st, n);
  // ---------------------------------------------------------------- stage 44
  const DOM_CASES = ['den', 'rad', 'radneg', 'quadden', 'raddown', 'all', 'both', 'range'];
  function genDom(cs, tut = isTutorial()) {
    const L = lvl(tut), M = big(L);
    cs = cs || pick(DOM_CASES);
    for (let t = 0; t < 300; t++) {
      let st = null;
      const a = nz(-M, M), k = rand(1, 9), m = L >= 1 && chance(0.5) ? rand(2, 4) : 1;
      if (cs === 'den') st = dmState({ form: 'den', k, d: P1(m, -m * a) }, [{ kind: 'den', p: P1(m, -m * a) }]);
      else if (cs === 'rad') st = dmState({ form: 'rad', r: P1(m, -m * a) }, [{ kind: 'rad', p: P1(m, -m * a) }]);
      else if (cs === 'radneg') { const q = rand(1, 4); st = dmState({ form: 'rad', r: P1(-q, q * a) }, [{ kind: 'rad', p: P1(-q, q * a) }]); }
      else if (cs === 'quadden') { const r = rand(1, M); const p = chance(0.6) ? pmul(P1(1, -r), P1(1, r)) : pmul(P1(1, -r), P1(1, -nz(-M, M))); if (pdeg(p) < 2 || fz(p[1]) && fz(p[0])) continue; st = dmState({ form: 'quadden', k, d: p }, [{ kind: 'den', p }]); }
      else if (cs === 'raddown') st = dmState({ form: 'raddown', k, r: P1(m, -m * a) }, [{ kind: 'radden', p: P1(m, -m * a) }]);
      else if (cs === 'all') { const p = chance(0.5) ? [F(nz(-9, 9)), F(nz(-6, 6)), F(nz(-3, 3))] : [F(nz(-9, 9)), F(nz(-6, 6))]; st = dmState({ form: 'all', p }, []); }
      else if (cs === 'both') { const b = a + rand(1, 6); st = dmState({ form: 'both', r: P1(1, -a), d: P1(1, -b) }, [{ kind: 'rad', p: P1(1, -a) }, { kind: 'den', p: P1(1, -b) }]); }
      else { const u = pick(['sqrt', 'sq', 'abs']), aa = pick(L ? [1, -1, 2, -2] : [1, -1]); st = rgState(u, nz(-M, M), aa, nz(-M, M)); }
      if (done(st, 10)) return { r10: st, enemy: 'glimmer' };
    }
    return { r10: dmState({ form: 'den', k: 1, d: P1(1, -2) }, [{ kind: 'den', p: P1(1, -2) }]), enemy: 'glimmer' };
  }
  // ---------------------------------------------------------------- stage 45
  const COMP_CASES = ['num', 'num2', 'circ', 'expr', 'expr2', 'self'];
  function genComp(cs, tut = isTutorial()) {
    const L = lvl(tut), M = [4, 5, 6, 8][L];
    cs = cs || pick(COMP_CASES);
    for (let t = 0; t < 300; t++) {
      const f = [F(nz(-M, M)), F(nz(-M, M))], g = chance(0.6) ? [F(nz(-M, M)), F(0), F(1)] : [F(nz(-M, M)), F(nz(-4, 4)), F(1)];
      const arg = rand(-4, 5);
      let st;
      if (cs === 'num') st = cpState(f, g, 'f', 'g', arg, false);
      else if (cs === 'num2') st = cpState(f, g, 'g', 'f', arg, false);
      else if (cs === 'circ') st = chance(0.5) ? cpState(f, g, 'f', 'g', arg, true) : cpState(f, g, 'g', 'f', null, true);
      else if (cs === 'expr') st = cpState(f, g, 'f', 'g', null, false);
      else if (cs === 'expr2') st = cpState(f, g, 'g', 'f', null, false);
      else st = chance(0.5) ? cpState(f, g, 'f', 'f', null, false) : cpState(f, g, 'f', 'f', arg, false);
      const end = A.pathOf(st, st.skill).end;
      if (end.res && (Array.isArray(end.res) ? end.res.some(c => Math.abs(c.n) > 400) : Math.abs(end.res.n) > 400)) continue;
      if (done(st, 6)) return { r10: st, enemy: 'twinling' };
    }
    return { r10: cpState([F(1), F(2)], [F(-3), F(0), F(1)], 'f', 'g', 2, false), enemy: 'twinling' };
  }
  // ---------------------------------------------------------------- stage 46
  const INV_CASES = ['lin', 'neg', 'frac', 'cube', 'value'];
  function genInv(cs, tut = isTutorial()) {
    const L = lvl(tut), M = big(L);
    cs = cs || pick(INV_CASES);
    for (let t = 0; t < 300; t++) {
      let st;
      if (cs === 'lin') st = ivState({ t: 'lin', a: rand(2, [5, 7, 9, 9][L]), b: nz(-M, M) }, 'inv', null);
      else if (cs === 'neg') st = ivState({ t: 'lin', a: -rand(2, [5, 7, 9, 9][L]), b: nz(-M, M) }, 'inv', null);
      else if (cs === 'frac') { const d = rand(2, [4, 5, 6, 6][L]), a = L >= 2 && chance(0.4) ? rand(2, 3) : 1; if (gcd(a, d) > 1) continue; st = ivState({ t: 'frac', a, b: nz(-M, M), d }, 'inv', null); }
      else if (cs === 'cube') st = ivState({ t: 'cube', a: L >= 2 && chance(0.4) ? 2 : 1, b: nz(-M, M) }, 'inv', null);
      else { const f = chance(0.7) ? { t: 'lin', a: nz(-6, 6), b: nz(-M, M) } : { t: 'cube', a: 1, b: nz(-M, M) }; if (f.t === 'lin' && Math.abs(f.a) === 1) continue; const x0 = rand(-4, 5); st = ivState(f, 'val', fEval(f, F(x0))); }
      if (done(st, 6)) return { r10: st, enemy: 'mirrorling' };
    }
    return { r10: ivState({ t: 'lin', a: 3, b: -5 }, 'inv', null), enemy: 'mirrorling' };
  }
  // ---------------------------------------------------------------- stage 47
  const TF_CASES = ['shift', 'stretch', 'reflect', 'all', 'piece'];
  function genTf(cs, tut = isTutorial()) {
    const L = lvl(tut), M = [4, 5, 6, 6][L];
    cs = cs || pick(TF_CASES);
    for (let t = 0; t < 300; t++) {
      const par = pick(['abs', 'sq', 'sqrt']);
      let st;
      if (cs === 'piece') {
        const b = rand(-3, 3), n3 = L >= 2 && chance(0.4);
        const ps = n3 ? [{ lo: null, hi: b, loC: false, hiC: false, p: [F(nz(-5, 5)), F(nz(-3, 3))] }, { lo: b, hi: b + 3, loC: true, hiC: false, p: [F(nz(-5, 5)), F(0), F(1)] }, { lo: b + 3, hi: null, loC: true, hiC: false, p: [F(nz(-9, 9))] }]
          : [{ lo: null, hi: b, loC: false, hiC: chance(0.5), p: [F(nz(-5, 5)), F(0), F(1)] }, { lo: b, hi: null, loC: false, hiC: false, p: [F(nz(-5, 5)), F(nz(-4, 4))] }];
        if (!n3) ps[1].loC = !ps[0].hiC;
        const v = chance(0.5) ? b : b + rand(-3, 4);
        st = pwState(ps, v);
      } else {
        const h = cs === 'reflect' || cs === 'all' || chance(0.7) ? nz(-M, M) : 0, k = nz(-M, M);
        const a = cs === 'shift' ? 1 : cs === 'reflect' ? -1 : cs === 'stretch' ? pick([2, 3, F(1, 2)]) : pick([-2, -3, 2, 3, F(-1, 2)]);
        st = tfState(par, { a, h, k });
      }
      if (done(st, 5)) return { r10: st, enemy: 'shade' };
    }
    return { r10: tfState('abs', { a: 2, h: 3, k: 1 }), enemy: 'shade' };
  }
  const GENS = { domain: genDom, compose: genComp, inverse: genInv, transform: genTf };
  const HARD = { domain: ['both', 'quadden', 'radneg', 'range'], compose: ['expr2', 'circ', 'self'], inverse: ['frac', 'cube', 'value'], transform: ['all', 'reflect', 'piece'] };
  const bossLast = mine => (mine.includes('transform') ? genTf('all') : mine.includes('inverse') ? genInv('frac') : mine.includes('compose') ? genComp('expr2') : genDom('both'));

  // ================================================================ act
  const HOME = { cond10: 'domain', all10: 'domain', dv10: 'domain', fac10: 'domain', zp10: 'domain', int10: 'domain', base10: 'domain', ml10: 'domain', as10: 'domain',
    cir10: 'compose', ev10: 'compose', sb10: 'compose', sm10: 'compose', set10: 'inverse', sw10: 'inverse', mlt10: 'inverse', as10y: 'inverse', dv10y: 'inverse', cr10: 'inverse',
    sh10: 'transform', rf10: 'transform', st10: 'transform', sv10: 'transform', pc10: 'transform', ev10p: 'transform' };
  const spec = {
    act: 10, sk: 'k10', key: 'r10', tag: 'a10', BOTH, COPY, PARAMS, moves, ok, apply, CARD, specials, family, filler, places: placesOf, why, render, anim, graph,
    answer, textOf, promptKey, PR, HOME, gens: GENS, hard: HARD, elite: 'doppel', boss: 'lookingglass', bossLast,
    skills: [
      { id: 'domain', stage: 44, act: 10, name: 'Domain and range', cases: DOM_CASES, gen: cycled('domain', c => genDom(c)),
        title: 'Stage 44: Domain and range',
        intro: 'The domain is every x the function accepts. Two things limit it: a bottom can\'t be 0 (set it ≠ 0), and a square root needs what\'s inside to be 0 or more (≥ 0; > 0 if the root is on the bottom). Solve each condition, then write the answer in interval notation: [ ] includes a number, ( ) leaves it out. The range is every output: start from a fact like √u ≥ 0 and build the function.',
        example: 'f(x) = √(x + 5)<br>Inside ≥ 0 → x + 5 ≥ 0 → x ≥ −5<br>Domain: [−5, ∞)',
        tutorial: [() => genDom('den', true), () => genDom('rad', true)] },
      { id: 'compose', stage: 45, act: 10, name: 'Composition', cases: COMP_CASES, gen: cycled('compose', c => genComp(c)),
        title: 'Stage 45: Composition',
        intro: 'f(g(x)), also written (f ∘ g)(x), means: do g first, then put its answer into f. With a number, work from the inside out. With x, replace every x in f with the whole of g(x) in brackets, then simplify.',
        example: 'f(x) = 2x + 1, g(x) = x² − 3<br>f(g(2)): g(2) = 1, then f(1) = 3<br>f(g(x)) = 2(x² − 3) + 1 = 2x² − 5',
        tutorial: [() => genComp('num', true), () => genComp('expr', true)] },
      { id: 'inverse', stage: 46, act: 10, name: 'Inverses', cases: INV_CASES, gen: cycled('inverse', c => genInv(c)),
        title: 'Stage 46: Inverse functions',
        intro: 'The inverse f⁻¹ undoes f. Write y = f(x), swap x and y, then solve for y with the moves you know. The −1 is not a power: f⁻¹ is not 1/f. On a graph, f⁻¹ is f mirrored across the line y = x. To find f⁻¹(a), solve f(x) = a.',
        example: 'f(x) = 3x − 5<br>Swap: x = 3y − 5<br>+5, ÷3 → f⁻¹(x) = (x + 5)/3',
        tutorial: [() => genInv('lin', true), () => genInv('value', true)] },
      { id: 'transform', stage: 47, act: 10, name: 'Transformations', cases: TF_CASES, gen: cycled('transform', c => genTf(c)),
        title: 'Stage 47: Transformations and piecewise functions',
        intro: 'y = a·f(x − h) + k is the parent graph moved: x − h shifts it right h (x + h shifts left), a stretches it (a minus flips it over the x-axis), + k shifts it up. Do the shift sideways, then the stretch or flip, then the shift up or down. A piecewise function uses the piece whose condition the input fits.',
        example: 'y = 2|x − 3| + 1 from y = |x|<br>Right 3 → Stretch ×2 → Up 1',
        tutorial: [() => genTf('shift', true), () => genTf('piece', true)] },
    ],
    enemies: {
      glimmer:    { name: 'Glimmer',          rank: 'Normal', color: '#a2d2ff', size: 84 },
      twinling:   { name: 'Twinling',         rank: 'Normal', color: '#bde0fe', size: 84 },
      mirrorling: { name: 'Mirrorling',       rank: 'Normal', color: '#cdb4db', size: 84 },
      shade:      { name: 'Shade',            rank: 'Normal', color: '#ffafcc', size: 84 },
      doppel:     { name: 'The Doppelganger', rank: 'Elite',  color: '#9d8df1', size: 100, horns: true },
      lookingglass: { name: 'The Looking-Glass', rank: 'Boss', color: '#e0e1dd', size: 120, crown: true },
    },
    actInfo: { name: 'The Hall of Mirrors', sub: 'Functions in depth', boss: 'The Looking-Glass', firstSkill: 'domain',
      blurb: 'In the Hall of Mirrors every function has a reflection. Find domains and ranges, chain functions together, undo them with inverses, and move graphs into place. Defeat The Looking-Glass.',
      cleared: () => `The Looking-Glass cracks and the reflections line up. ${KT.nextActText(10)}` },
    icons: {
      cond10: { name: 'Set a condition (bottom ≠ 0, inside ≥ 0)', svg: svgI('<path d="M4 8h16M4 16h16"/><path d="M14 4L10 20" stroke-width="2"/>') },
      int10:  { name: 'Interval notation', svg: svgI('<path d="M7 4c-3 4-3 12 0 16M17 4h3v16h-3"/><path d="M10 12h4"/>') },
      base10: { name: 'Start from a fact (√u ≥ 0)', svg: svgI('<path d="M4 18h16"/><path d="M8 18V8l4-4 4 4v10" stroke-width="2"/>') },
      comp10: { name: 'Composition (a function inside a function)', svg: svgI('<circle cx="12" cy="12" r="8"/><circle cx="12" cy="12" r="3.5"/>') },
      inv10:  { name: 'Swap x and y (inverse)', svg: svgI('<path d="M4 20L20 4" stroke-dasharray="2 3"/><path d="M5 9l4-4 4 4M19 15l-4 4-4-4" stroke-width="2"/>') },
      left10: { name: 'Shift left', svg: svgI('<path d="M20 12H5M10 6l-6 6 6 6"/>') },
      right10: { name: 'Shift right', svg: svgI('<path d="M4 12h15M14 6l6 6-6 6"/>') },
      up10:   { name: 'Shift up', svg: svgI('<path d="M12 20V5M6 10l6-6 6 6"/>') },
      down10: { name: 'Shift down', svg: svgI('<path d="M12 4v15M6 14l6 6 6-6"/>') },
      refl10: { name: 'Reflect over the x-axis', svg: svgI('<path d="M2 12h20" stroke-dasharray="2 2"/><path d="M6 9l6-5 6 5M6 15l6 5 6-5"/>') },
      str10:  { name: 'Stretch or shrink vertically', svg: svgI('<path d="M12 3v18M8 7l4-4 4 4M8 17l4 4 4-4"/>') },
      pw10:   { name: 'Pick the piece', svg: svgI('<path d="M9 3c-3 0-3 4-3 6s-2 3-3 3c1 0 3 1 3 3s0 6 3 6"/><path d="M13 8h8M13 16h8"/>') },
    },
    css: `
      .tok.a4.s9.defs10 { font-size:.45em; color:var(--muted); white-space:nowrap; }
      .tok.a4.done10 { color:var(--good); }
      .tg9.pt10, .tg9.in10 { display:inline-block; border:2px dashed #ffffff40; border-radius:6px; padding:0 .12em; }
      .tg9.pt10.hover, .tg9.in10.hover { border-color:#7bdff2; background:#7bdff222; }
      span.tg9.ok9 { border-color:var(--good) !important; background:#06d6a022 !important; }
      .pw10 { display:inline-flex; flex-direction:column; border-left:3px solid currentColor; border-radius:10px 0 0 10px; padding-left:.3em; vertical-align:middle; font-size:.8em; }
      .pwr10 { white-space:nowrap; } .pwr10 .nonum { color:var(--muted); font-size:.8em; }
      .pwr10.on10 { color:var(--accent); }
      .card .clong.l9 small { font-size:.7em; opacity:.8; }
    `,
  };
  A = KT.makeAct(spec);
  KT.install(spec, A);
  // Some card faces show the problem's own numbers (the swapped equation, the plugged-in form): they
  // are filled in from the state when a hand is dealt.
  const baseHand = A.E.makeHand;
  A.E.makeHand = (e, correct, size) => { dress(e, correct); return baseHand(e, correct, size).map(c => dress(e, c)); };
  const baseFam = spec.family; spec.family = e => baseFam(e).map(c => dress(e, c));
})();
