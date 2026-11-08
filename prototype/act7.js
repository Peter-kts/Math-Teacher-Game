// =====================================================================
//  Act 7: The Archery Gallery (factoring, quadratics, complex numbers)
// =====================================================================
// Stage 27  Greatest common factor        6x² + 9x = 3x(2x + 3)
// Stage 28  Factor trinomials             x² + 5x + 6, 2x² + 7x + 3 (by grouping)
// Stage 29  Special patterns              x² − 9, x² + 6x + 9, x² + 16 (prime)
// Stage 30  Solve by factoring            x² − 5x + 6 = 0, x² = 3x, (x − 2)(x − 3) = 6
// Stage 31  Square root both sides        (x − 3)² = 16, with the owed ± card
// Stage 32  Complete the square           x² + 6x = 7, and vertex form y = (x + 3)² − 4
// Stage 33  Quadratic formula             2x² − 3x − 4 = 0, and the discriminant
// Stage 34  Complex numbers               x² + 4 = 0, (3 + 2i)(1 − i)
// Stage 35  Quadratic graphs              vertex, axis, max/min and roots of y = −x² + 4x
//
// States carry their own kind, `k7`:
//   fx   an expression to factor: { L: X, prime }
//   eq   an equation: { L: X, R: X, method: 'factor' | 'root' | 'square' | 'formula', ask, gq? }
//   rt   after √ both sides: a·x + b = q ± s·√(rad) (or q ± s·√n once worked out, n < 0 meaning i√|n|)
//   qf   the quadratic formula with a, b, c plugged in, before the discriminant is worked out
//   cs   separate answers or cases: x − 2 = 0 or x − 3 = 0 (solved in turn)
//   vd   a verdict that ends a problem: "No real solution", "2 real solutions"
//   vf   vertex form: y = x² + bx + c rewritten as y = (x + h)² + k
//   cx   complex numbers: a row of brackets, products and terms in i
//   gr   a parabola y = ax² + bx + c and a question about its graph
// A side X = c · xᵐ · (factor)(factor)… + k, so a plain polynomial, a factored one, a square k(x + h)² + q,
// and "product plus a number" (x − 2)(x − 3) − 6 all share one shape. Factors: { t: 'p', p } a
// polynomial (dense coefficients, index = power), { t: 'sq', p } a squared bracket, { t: 'g4', ts } four
// terms after splitting the middle term, { t: 'gp', A, B, C, D } two factored pairs A(B) + C(D).
//
// Every legal move counts. movesOf(state) lists the legal moves as slots { op, refs, ok(card), card }:
// the first slot's card is the canonical next move (par). Most cards are ◎ and go on one part; with only
// one place to go they drop anywhere. Moves done to both sides (add, divide, √) are ⇔.
//
// index.html switches to this engine for generators that return { q7 } (cur.act7).
'use strict';
(function () {
  const A4 = window.ACT4;
  if (!A4 || !A4.kit) return;
  const K = A4.kit;
  const { TOK, EQTOK, refOf, P, kickClass, clone, fNeg, fSub, fDiv, fEq, fz, fv } = K;
  const isTutorial = K.isTutorial, lvl = K.lvl;
  const chance = p => Math.random() < p;
  const qid = () => Math.random().toString(36).slice(2, 8);
  const sgnR = () => (Math.random() < 0.5 ? -1 : 1);

  // ================================================================ numbers
  const SUPD = '⁰¹²³⁴⁵⁶⁷⁸⁹';
  const sup = n => (n === 1 ? '' : String(n).split('').map(d => SUPD[+d]).join(''));
  const XV = (v = 'x') => `<i class="xv">${v}</i>`;
  const isSq = n => n >= 0 && Number.isInteger(Math.sqrt(n));
  const isqrt = n => Math.round(Math.sqrt(Math.abs(n)));
  const sqfree = n => { n = Math.abs(n); if (n < 2) return false; for (let k = 2; k * k <= n; k++) if (n % (k * k) === 0) return false; return true; };
  const okRad = n => isSq(Math.abs(n)) || sqfree(n);          // radicands Act 7 can finish without simplifying radicals (Act 8)
  const iv = f => f.n / f.d;
  const FI = v => (typeof v === 'number' ? F(v) : v);
  const lcm = (a, b) => Math.abs(a * b) / gcd(a, b);
  const fNum = (f, html) => (html ? fracHtml(f) : fracText(f));

  // ================================================================ polynomials (dense, index = power)
  const PL = cs => cs.map(FI);
  const pdeg = p => { for (let i = p.length - 1; i >= 0; i--) if (!fz(p[i])) return i; return -1; };
  const ptrim = p => { const d = pdeg(p); return d < 0 ? [F(0)] : p.slice(0, d + 1); };
  const pcoef = (p, i) => p[i] || F(0);
  const padd = (a, b) => { const n = Math.max(a.length, b.length), o = []; for (let i = 0; i < n; i++) o.push(fAdd(pcoef(a, i), pcoef(b, i))); return ptrim(o); };
  const pscale = (p, f) => ptrim(p.map(c => fMul(c, f)));
  const pmul = (a, b) => { const o = []; for (let i = 0; i < a.length + b.length - 1; i++) o.push(F(0)); a.forEach((x, i) => b.forEach((y, j) => { o[i + j] = fAdd(o[i + j], fMul(x, y)); })); return ptrim(o); };
  const pshift = (p, m) => (m ? ptrim([...Array(m).fill(F(0)), ...p]) : p);
  const pEq = (a, b) => { const x = ptrim(a), y = ptrim(b); return x.length === y.length && x.every((c, i) => fEq(c, y[i])); };
  const mono = (c, e) => pshift([FI(c)], e);
  const pTerms = p => { const o = []; for (let e = p.length - 1; e >= 0; e--) if (!fz(p[e])) o.push({ c: p[e], e }); return o; };
  const isIntP = p => p.every(isInt);
  // the greatest common factor of the terms: the number (positive) and the lowest power of x
  function pCont(p) {
    const ts = pTerms(p);
    if (!ts.length || !isIntP(p)) return { g: 1, e: 0 };
    const g = ts.reduce((a, t) => gcd(a, t.c.n), 0);
    return { g: ts[0].c.n < 0 ? -g : g, e: Math.min(...ts.map(t => t.e)) };   // a negative lead comes out with the GCF: −x² + 4x = −x(x − 4)
  }
  function mBody(t, html, v = 'x') {
    const a = fAbs(t.c), lit = t.e ? (html ? XV(v) : v) + sup(t.e) : '';
    return (lit && fIs(a, 1) ? '' : fNum(a, html)) + lit;
  }
  const mText = (t, first, html, v) => (t.c.n < 0 ? (first ? MINUS : MINUS + ' ') : first ? '' : '+ ') + mBody(t, html, v);
  const pText = (p, html, v) => { const ts = pTerms(p); return ts.length ? ts.map((t, i) => mText(t, i === 0, html, v)).join(' ') : '0'; };
  const tText = (t, html) => mText(t, true, html);         // one term on its own: 3x, −6, x²
  // a monomial factor like 3x or 2 or x²: written with its sign
  const monoText = (g, html) => mText({ c: g.c, e: g.e }, true, html) || '1';

  // Factoring a trinomial ax² + bx + c over the integers: (px + q)(rx + s), each bracket with no common factor.
  function trinomPair(a, b, c) {
    if (!a || !c) return null;
    const ds = n => { const o = []; for (let k = 1; k <= Math.abs(n); k++) if (n % k === 0) o.push(k); return o; };
    for (const p of ds(a)) {
      const r = a / p;
      for (const q0 of ds(c)) for (const sq of [1, -1]) {
        const q = q0 * sq, s = c / q;
        if (p * s + q * r === b && gcd(p, q) === 1 && gcd(r, s) === 1) {
          const A = PL([q, p]), B = PL([s, r]);
          return iv(A[0]) / iv(A[1]) >= iv(B[0]) / iv(B[1]) ? { A, B } : { A: B, B: A };
        }
      }
    }
    return null;
  }
  // The two numbers that split the middle term of ax² + bx + c for grouping: u + w = b, u·w = a·c.
  function splitPairs(a, b, c) {
    const o = [], ac = a * c;
    for (let u = -Math.abs(ac); u <= Math.abs(ac); u++) { if (!u) continue; const w = b - u; if (w && u * w === ac) o.push({ u, w }); }
    return o.sort((x, y) => gcd(a, y.u) - gcd(a, x.u) || Math.abs(y.u) - Math.abs(x.u));
  }
  const isDos = p => pdeg(p) === 2 && fz(pcoef(p, 1)) && isIntP(p) && isSq(p[2].n) && p[0].n < 0 && isSq(-p[0].n);
  const isPsq = p => pdeg(p) === 2 && !fz(pcoef(p, 1)) && isIntP(p) && p[2].n > 0 && isSq(p[2].n) && isSq(p[0].n) && p[1].n ** 2 === 4 * p[2].n * p[0].n;
  // the bracket of a perfect square: x² + 6x + 9 → x + 3 (works for fractions too: x² + 3x + 9/4 → x + 3/2)
  const psqBase = p => { const a = isqrt(p[2].n), s = p[1].n < 0 ? -1 : 1; return p[2].d === 1 && isSq(p[2].n) ? PL([fMul(F(s), F(isqrt(p[0].n), isqrt(p[0].d))), a]) : null; };
  const monicPsq = p => pdeg(p) === 2 && fIs(p[2], 1) && fEq(fMul(fMul(p[1], p[1]), F(1, 4)), p[0]);

  // ================================================================ sides: X = c·xᵐ·(factors) + k
  const X = (fs, o = {}) => ({ c: FI(o.c ?? 1), m: o.m || 0, fs, k: FI(o.k ?? 0) });
  const Xp = p => X([{ t: 'p', p: ptrim(p) }]);
  const Xn = n => Xp([FI(n)]);
  function facPoly(f) {
    if (f.t === 'p') return f.p;
    if (f.t === 'sq') return pmul(f.p, f.p);
    if (f.t === 'g4') return f.ts.reduce((a, t) => padd(a, mono(t.c, t.e)), [F(0)]);
    return padd(pmul(mono(f.A.c, f.A.e), f.B), pmul(mono(f.C.c, f.C.e), f.D));
  }
  const prodPoly = x => pscale(pshift(x.fs.reduce((a, f) => pmul(a, facPoly(f)), [F(1)]), x.m), x.c);
  const xPoly = x => padd(prodPoly(x), [x.k]);
  const isPlain = x => fIs(x.c, 1) && !x.m && fz(x.k) && x.fs.length === 1 && x.fs[0].t === 'p';
  const plainP = x => (isPlain(x) ? x.fs[0].p : null);
  const isZero = x => isPlain(x) && pdeg(x.fs[0].p) < 0;
  const isConst = x => isPlain(x) && pdeg(x.fs[0].p) <= 0;
  const constOf = x => pcoef(x.fs[0].p, 0);
  const isSqSide = x => x.fs.length === 1 && x.fs[0].t === 'sq' && !x.m;          // c(x + h)² + k
  const isBareX2 = x => isPlain(x) && pdeg(x.fs[0].p) === 2 && fz(pcoef(x.fs[0].p, 1));   // cx² + k
  // all the factors that can be set to 0: the xᵐ part and every bracket, each linear (or a squared bracket)
  function zeroFactors(x) {
    const out = [];
    if (x.m) out.push(PL([0, 1]));
    for (const f of x.fs) {
      if (f.t === 'p' && pdeg(f.p) === 1) out.push(f.p);
      else if (f.t === 'sq' && pdeg(f.p) === 1) out.push(f.p);
      else if (!(f.t === 'p' && pdeg(f.p) <= 0)) return null;
    }
    return out;
  }
  const countFactors = x => x.m + x.fs.reduce((a, f) => a + (f.t === 'sq' ? 2 : f.t === 'p' && pdeg(f.p) >= 1 ? 1 : 0), 0);

  function facText(f, html, solo) {
    const wrap = s => (solo ? s : `(${s})`);
    if (f.t === 'p') return wrap(pText(f.p, html));
    if (f.t === 'sq') return `(${pText(f.p, html)})²`;
    if (f.t === 'g4') { const s = f.ts.map((t, i) => mText(t, i === 0, html)).join(' '); return solo ? s : `[${s}]`; }
    const pair = (m, b, first) => `${first ? (m.c.n < 0 ? MINUS : '') : m.c.n < 0 ? MINUS + ' ' : '+ '}${mBody({ c: m.c, e: m.e }, html) || '1'}(${pText(b, html)})`;
    const s = pair(f.A, f.B, true) + ' ' + pair(f.C, f.D, false);
    return solo ? s : `[${s}]`;
  }
  const leadText = (x, html) => {
    const lit = x.m ? (html ? XV() : 'x') + sup(x.m) : '';
    if (fIs(x.c, 1)) return lit;
    if (fIs(x.c, -1)) return MINUS + lit;
    return fNum(x.c, html) + lit;
  };
  const soloX = x => x.fs.length === 1 && fIs(x.c, 1) && !x.m && x.fs[0].t !== 'sq';
  const kText = (k, html, alone) => (fz(k) ? '' : alone ? fNum(k, html) : (k.n < 0 ? ` ${MINUS} ` : ' + ') + fNum(fAbs(k), html));
  function xText(x, html) {
    const solo = soloX(x);
    let body = leadText(x, html) + x.fs.map(f => facText(f, html, solo)).join('');
    if (!body && !x.fs.length) body = '1';
    if (!x.fs.length && !x.m) body = fNum(x.c, html);
    return body + kText(x.k, html, false);
  }

  // ================================================================ states
  const fxState = (p, o = {}) => ({ k7: 'fx', L: Xp(PL(p)), prime: false, skill: o.skill || 'gcf7', qid: qid() });
  const eqState = (L, R, method, o = {}) => ({ k7: 'eq', L, R, method, ask: o.ask || 'solve', skill: o.skill || 'zprod', gq: o.gq || null, cplx: !!o.cplx, qid: qid() });
  const csState = (cs, o = {}) => ({ k7: 'cs', cs, gq: o.gq || null, skill: o.skill, qid: o.qid || qid() });
  const lin = p => ({ a: pcoef(p, 1), b: pcoef(p, 0) });

  // ================================================================ the moves that are legal
  // A slot: { op, refs, ok: card → bool, card }. refs '*' = a both-sides move (dropped anywhere).
  const C7 = (op, o = {}) => ({ op, a7: true, scope: BOTH.has(op) ? 'both' : 'part', ...o });
  const BOTH = new Set(['mv7', 'dv7', 'sqrt7']);
  const slot = (op, refs, card, ok) => ({ op, refs, card: { ...C7(op), ...card }, ok: ok || (() => true) });
  const sideRefs = (x, S) => { const r = []; if (!fIs(x.c, 1) || x.m) r.push(S + 'c'); x.fs.forEach((f, i) => r.push(S + 'f' + i)); if (!fz(x.k)) r.push(S + 'k'); if (!r.length) r.push(S + 'c'); return r; };

  // factoring moves on one side (S = 'L')
  function facSlots(x, S, out) {
    x.fs.forEach((f, i) => {
      const r = S + 'f' + i;
      if (f.t === 'g4') { out.push(slot('grp7', [r], {})); return; }
      if (f.t === 'gp') { out.push(slot('out7', [r], {})); return; }
      if (f.t !== 'p' || pTerms(f.p).length < 2 || !isIntP(f.p)) return;
      const { g, e } = pCont(f.p);
      if (g !== 1 || e > 0) { out.push(slot('gcf7', [r], { g: { c: F(g), e } }, c => c.g && fEq(c.g.c, F(g)) && c.g.e === e)); return; }
      if (pdeg(f.p) !== 2) return;
      const [c0, b, a] = [0, 1, 2].map(j => pcoef(f.p, j).n);
      const pair = trinomPair(a, b, c0);
      if (!pair) return;
      const triOk = c => c.A && c.B && pEq(pmul(c.A, c.B), f.p);
      const sps = splitPairs(a, b, c0);
      const splitOk = c => sps.some(s => s.u === c.u && s.w === c.w);
      if (isDos(f.p)) out.push(slot('dos7', [r], {}));
      else if (isPsq(f.p)) out.push(slot('psq7', [r], {}));
      else if (a === 1) out.push(slot('tri7', [r], { A: pair.A, B: pair.B }, triOk));
      else out.push(slot('split7', [r], sps[0], splitOk));
      // the other ways that are also right
      if (isDos(f.p) || isPsq(f.p) || a !== 1) out.push(slot('tri7', [r], { A: pair.A, B: pair.B }, triOk));
      if (a !== 1 && (isDos(f.p) || isPsq(f.p))) out.push(slot('split7', [r], sps[0], splitOk));
    });
  }
  const zeroP = [F(0)];
  // moving a term from the right side to the left: legal when the left side can take it
  function moveSlots(e, out, onlyConst) {
    const Rp = plainP(e.R);
    if (!Rp || pdeg(Rp) < 0) return;
    const plainL = isPlain(e.L);
    for (const t of pTerms(Rp)) {
      if (onlyConst && t.e) continue;
      if (t.e && !plainL) continue;
      const nt = { c: fNeg(t.c), e: t.e };
      out.push(slot('mv7', ['*'], { t: nt }, c => c.t && fEq(c.t.c, nt.c) && c.t.e === nt.e));
    }
  }
  // moving the left side's number across (undo + and − first)
  function constOffL(e) {
    const L = e.L;
    if (isPlain(L)) { const k = pcoef(L.fs[0].p, 0); return pdeg(L.fs[0].p) >= 1 && !fz(k) ? k : null; }
    return fz(L.k) ? null : L.k;
  }
  const mvSlot = k => { const nt = { c: fNeg(k), e: 0 }; return slot('mv7', ['*'], { t: nt }, c => c.t && fEq(c.t.c, nt.c) && c.t.e === 0); };
  const dvSlot = n => slot('dv7', ['*'], { n }, c => c.n && fEq(c.n, n));
  function eqSlots(e) {
    const out = [], L = e.L, R = e.R, R0 = isZero(R), Lr = sideRefs(L, 'L');
    if (e.ask === 'count') {
      if (!R0) { moveSlots(e, out); return out; }
      const p = plainP(L); if (p && pdeg(p) === 2) out.push(slot('dsc7', Lr, { v: discCount(p) }, c => c.v === discCount(p)));
      return out;
    }
    if (e.method === 'factor') {
      if (!R0) {
        const Rp = plainP(R), xTerm = Rp && pTerms(Rp).some(t => t.e);
        if (!isPlain(L) && countFactors(L) >= 2) out.push(slot('box7', Lr, {}));   // multiplying out is fine any time
        moveSlots(e, out);                                                         // an x-term only comes over once the left is multiplied out
        if (!xTerm && out.length && out[0].op === 'box7') out.push(out.shift());   // a number can come over first
        return out;
      }
      if (!isPlain(L) && !fz(L.k) && L.fs.length >= 1 && (countFactors(L) >= 2 || L.fs[0].t !== 'p')) out.push(slot('box7', Lr, {}));
      if (fIs(L.c, 1) && !L.m && L.fs.length === 1 && L.fs[0].t === 'p' && !fz(L.k)) out.push(slot('cmb7', Lr, {}));
      if (fz(L.k)) {
        facSlots(L, 'L', out);
        const zf = zeroFactors(L);
        if (!out.length && zf && countFactors(L) >= 2) out.push(slot('zp7', Lr, {}));
      }
      return out;
    }
    if (e.method === 'formula') {
      if (!R0) { moveSlots(e, out); return out; }
      const p = plainP(L); if (p && pdeg(p) === 2) out.push(slot('qf7', Lr, { v: 'ok', e7: { a: p[2], b: pcoef(p, 1), c: pcoef(p, 0) } }, c => c.v === 'ok'));
      return out;
    }
    if (!isConst(R)) return out;
    if (e.method === 'root') {
      const k = constOffL(e);
      if (k) { out.push(mvSlot(k)); return out; }
      const lead = isSqSide(L) ? L.c : isBareX2(L) ? L.fs[0].p[2] : null;
      if (lead && !fIs(lead, 1)) { out.push(dvSlot(lead)); return out; }
      if ((isSqSide(L) && fIs(L.c, 1) && fz(L.k)) || (isBareX2(L) && fIs(L.fs[0].p[2], 1) && fz(pcoef(L.fs[0].p, 0)))) out.push(slot('sqrt7', ['*'], {}));
      return out;
    }
    if (e.method === 'square') {
      if (isSqSide(L)) { if (fIs(L.c, 1) && fz(L.k)) out.push(slot('sqrt7', ['*'], {})); return out; }
      const p = plainP(L); if (!p || pdeg(p) !== 2) return out;
      const a = p[2], b = pcoef(p, 1), c0 = pcoef(p, 0);
      if (!fz(c0) && !(fIs(a, 1) && monicPsq(p))) out.push(mvSlot(c0));
      if (!fIs(a, 1)) out.push(dvSlot(a));
      if (fIs(a, 1) && fz(c0) && !fz(b)) { const h = fMul(b, F(1, 2)), n = fMul(h, h); out.push(slot('mv7', ['*'], { t: { c: n, e: 0 } }, c => c.t && fEq(c.t.c, n) && c.t.e === 0)); }
      if (fIs(a, 1) && monicPsq(p)) { const h = fMul(b, F(1, 2)); out.push(slot('fold7', Lr, { h }, c => c.h && fEq(c.h, h))); }
      return out;
    }
    return out;
  }
  const discOf = p => fSub(fMul(pcoef(p, 1), pcoef(p, 1)), fMul(F(4), fMul(p[2], pcoef(p, 0))));
  const discCount = p => { const D = discOf(p); return D.n > 0 ? 2 : D.n === 0 ? 1 : 0; };

  // rt: a·x + b = q ± s·√rad, then q ± s√n (n = 1 a whole number, n < 0 means i√|n|)
  function rtSlots(e) {
    const out = [];
    if (!e.pm) { out.push(slot('pm7', ['R'], {})); return out; }
    if (e.rad !== null && e.rad < 0) out.push(slot('i7', ['R'], { rad: e.rad }));
    if (!fz(e.b)) out.push(mvSlot(e.b));
    else if (!fIs(e.a, 1)) out.push(dvSlot(e.a));
    if (e.rad === null && e.n === 1 && fz(e.b) && fIs(e.a, 1) && !fz(e.q)) out.push(slot('spl7', ['R'], {}));
    return out;
  }
  function qfSlots(e) {
    const p = PL([e.c, e.b, e.a]), v = discCount(p);
    return [slot('dsc7', ['Q'], { v }, c => c.v === v)];
  }
  function csSlots(e) {
    const i = e.cs.findIndex(c => !(fIs(c.a, 1) && fz(c.b)));
    if (i < 0) return [];
    const c = e.cs[i];
    if (!fz(c.b)) return [mvSlot(c.b)];
    return [dvSlot(c.a)];
  }
  // vf: y = x² + bx + c  →  y = (x² + bx + n) − n + c  →  y = (x + h)² − n + c  →  y = (x + h)² + k
  function vfSlots(e) {
    const h = fMul(e.b, F(1, 2)), n = fMul(h, h);
    if (e.st === 0) return [slot('as7', ['Vf'], { n }, c => c.n && fEq(c.n, n))];
    if (e.st === 1) return [slot('fold7', ['Vf'], { h }, c => c.h && fEq(c.h, h))];
    if (e.st === 2) return [slot('cmb7', ['Vk'], {})];
    if (e.findV && !e.vtx) { const vx = { x: fNeg(h), y: fSub(e.c, n) }; return [slot('vx7', ['Vf', 'Vk'], { x: vx.x, y: vx.y }, c => c.x && fEq(c.x, vx.x) && fEq(c.y, vx.y))]; }
    return [];
  }
  // cx: brackets { t: 'g', s, z: [re, im] }, products { t: 'pr', A, B }, terms { t: 't', c, e } (e = power of i)
  function cxSlots(e) {
    const out = [];
    e.items.forEach((it, i) => {
      const r = 'i' + i;
      if (it.t === 'g') out.push(slot(it.s < 0 ? 'neg7' : 'drop7', [r], {}));
      if (it.t === 'pr') out.push(slot('box7', [r], {}));
    });
    if (out.length) return out;
    e.items.forEach((it, i) => { if (it.t === 't' && it.e === 2) out.push(slot('i27', ['i' + i], {})); });
    const by = {};
    e.items.forEach((it, i) => { if (it.t === 't') (by[it.e] = by[it.e] || []).push('i' + i); });
    for (const k of [0, 1, 2]) if (by[k] && by[k].length >= 2) out.push(slot('cmb7', by[k], {}));
    if (!out.length && e.items.length === 2 && e.items[0].e === 1 && e.items[1].e === 0) out.push(slot('srt7', ['i0', 'i1'], {}));
    return out;
  }
  function grSlots(e) {
    const h = fDiv(fNeg(e.b), fMul(F(2), e.a));
    if (e.ask === 'roots') return [slot('y07', ['G'], {})];
    if (e.ask === 'max' && !e.dir) { const v = e.a.n < 0 ? 'downmax' : 'upmin'; return [slot('dir7', ['G'], { v }, c => c.v === v)]; }
    if (!e.h) return [slot('ax7', ['G'], { h }, c => c.h && fEq(c.h, h))];
    if (e.ask !== 'axis' && !e.k) return [slot('plg7', ['G'], {})];
    return [];
  }
  function fxSlots(e) {
    const out = [];
    facSlots(e.L, 'L', out);
    const L = e.L;
    if (!out.length && !e.prime && fIs(L.c, 1) && !L.m && L.fs.length === 1 && L.fs[0].t === 'p' && pdeg(L.fs[0].p) >= 2) out.push(slot('prime7', sideRefs(L, 'L'), {}));
    return out;
  }
  function movesOf(e) {
    switch (e.k7) {
      case 'fx': return fxSlots(e);
      case 'eq': return eqSlots(e);
      case 'rt': return rtSlots(e);
      case 'qf': return qfSlots(e);
      case 'cs': return csSlots(e);
      case 'vf': return vfSlots(e);
      case 'cx': return cxSlots(e);
      case 'gr': return grSlots(e);
      default: return [];
    }
  }
  const canon7 = e => { const s = movesOf(e)[0]; return s ? { ...s.card, ref: s.refs[0] } : null; };
  const slotFor = (e, c, ref) => movesOf(e).find(s => s.op === c.op && s.ok(c) && (s.refs[0] === '*' || s.refs.includes(ref)));
  const legalAnywhere = (e, c) => movesOf(e).some(s => s.op === c.op && s.ok(c));
  function correct7(e, c, target) {
    if (!c || !c.a7 || c.op === 'trap') return false;
    return !!slotFor(e, c, refOf(target));
  }

  // ================================================================ applying a move
  function applyFac(x, i, c) {
    const f = x.fs[i];
    switch (c.op) {
      case 'gcf7': {
        const g = c.g; x.c = fMul(x.c, g.c); x.m += g.e;
        x.fs[i] = { t: 'p', p: pscale(f.p.slice(g.e), F(1, 1)).map(v => fDiv(v, g.c)) };
        x.fs[i].p = ptrim(x.fs[i].p); break;
      }
      case 'tri7': x.fs.splice(i, 1, ...(pEq(c.A, c.B) ? [{ t: 'sq', p: c.A }] : [{ t: 'p', p: c.A }, { t: 'p', p: c.B }])); break;
      case 'split7': { const p = f.p; x.fs[i] = { t: 'g4', ts: [{ c: p[2], e: 2 }, { c: F(c.u), e: 1 }, { c: F(c.w), e: 1 }, { c: pcoef(p, 0), e: 0 }] }; break; }
      case 'grp7': {
        const [a, u, w, k] = f.ts.map(t => t.c.n), g1 = gcd(a, u), B = PL([u / g1, a / g1]), kk = w * g1 / a;
        x.fs[i] = { t: 'gp', A: { c: F(g1), e: 1 }, B, C: { c: F(kk), e: 0 }, D: PL([k / kk, w / kk]) }; break;
      }
      case 'out7': { const A = PL([f.C.c, f.A.c]); x.fs.splice(i, 1, ...(pEq(A, f.B) ? [{ t: 'sq', p: A }] : [{ t: 'p', p: A }, { t: 'p', p: f.B }])); break; }
      case 'dos7': { const a = isqrt(f.p[2].n), b = isqrt(f.p[0].n); x.fs.splice(i, 1, { t: 'p', p: PL([b, a]) }, { t: 'p', p: PL([-b, a]) }); break; }
      case 'psq7': x.fs[i] = { t: 'sq', p: psqBase(f.p) }; break;
    }
    return x;
  }
  // adding the same term to both sides of an equation
  function addTerm(x, t) {
    if (isPlain(x)) return Xp(padd(x.fs[0].p, mono(t.c, t.e)));
    if (!t.e) { x.k = fAdd(x.k, t.c); return x; }
    return Xp(padd(xPoly(x), mono(t.c, t.e)));
  }
  function divSide(x, n) {
    if (isPlain(x)) return Xp(pscale(x.fs[0].p, fDiv(F(1), n)));
    x.c = fDiv(x.c, n); x.k = fDiv(x.k, n); return x;
  }
  // the root of a number: √16 → { s: 4, n: 1 }, √7 → { s: 1, n: 7 }, √−9 waits for Pull out i
  function rootOf(rad) {
    if (rad >= 0 && isSq(rad)) return { s: F(isqrt(rad)), n: 1 };
    if (rad > 0) return { s: F(1), n: rad };
    return null;
  }
  function apply7(e, c, ref) {
    const r = clone(e);
    if (!c || c.op === 'trap') return r;
    const sl = slotFor(e, c, ref) || movesOf(e).find(s => s.op === c.op && s.ok(c));
    if (!sl) return r;
    const at = sl.refs[0] === '*' ? null : (sl.refs.includes(ref) ? ref : sl.refs[0]);
    switch (e.k7) {
      case 'fx': {
        if (c.op === 'prime7') { r.prime = true; return r; }
        applyFac(r.L, +at.slice(2), c); return r;
      }
      case 'eq': return applyEq(r, c, at);
      case 'rt': return applyRt(r, c);
      case 'qf': return applyQf(r, c);
      case 'cs': {
        const i = r.cs.findIndex(x => !(fIs(x.a, 1) && fz(x.b))), k = r.cs[i];
        if (c.op === 'mv7') { k.r = fAdd(k.r, c.t.c); k.b = F(0); }
        if (c.op === 'dv7') { k.r = fDiv(k.r, c.n); k.a = F(1); }
        return r;
      }
      case 'vf': {
        if (c.op === 'as7') r.st = 1;
        else if (c.op === 'fold7') r.st = 2;
        else if (c.op === 'cmb7') r.st = 3;
        else if (c.op === 'vx7') r.vtx = { x: c.x, y: c.y };
        return r;
      }
      case 'cx': return applyCx(r, c, sl);
      case 'gr': {
        if (c.op === 'dir7') r.dir = c.v;
        if (c.op === 'ax7') r.h = c.h;
        if (c.op === 'plg7') r.k = fAdd(fAdd(fMul(r.a, fMul(r.h, r.h)), fMul(r.b, r.h)), r.c);
        if (c.op === 'y07') return { ...eqState(Xp(PL([r.c, r.b, r.a])), Xn(0), 'factor', { skill: r.skill, gq: { a: r.a, b: r.b, c: r.c } }), qid: r.qid, fromGr: true };
        return r;
      }
    }
    return r;
  }
  function applyEq(r, c, at) {
    const keep = s => ({ ...s, qid: r.qid, gq: r.gq, skill: r.skill, cplx: r.cplx });
    switch (c.op) {
      case 'mv7': r.L = addTerm(r.L, c.t); r.R = addTerm(r.R, c.t); return r;
      case 'dv7': r.L = divSide(r.L, c.n); r.R = divSide(r.R, c.n); return r;
      case 'box7': { const k = r.L.k; r.L = Xp(prodPoly(r.L)); r.L.k = k; return r; }
      case 'cmb7': r.L = Xp(padd(r.L.fs[0].p, [r.L.k])); return r;
      case 'gcf7': case 'tri7': case 'split7': case 'grp7': case 'out7': case 'dos7': case 'psq7':
        applyFac(r.L, +at.slice(2), c); return r;
      case 'fold7': r.L = X([{ t: 'sq', p: PL([c.h, 1]) }]); return r;
      case 'zp7': {
        const seen = new Set(), cs = [];
        for (const p of zeroFactors(r.L)) { const k = pText(p); if (seen.has(k)) continue; seen.add(k); cs.push({ ...lin(p), r: F(0) }); }
        return keep(csState(cs, { qid: r.qid }));
      }
      case 'sqrt7': {
        const L = r.L, base = isSqSide(L) ? L.fs[0].p : PL([0, 1]);
        // the generators keep this side a whole number (b even, divisions exact), so .n is the whole radicand
        return keep({ k7: 'rt', ...lin(base), q: F(0), s: F(1), rad: constOf(r.R).n, n: null, pm: false });
      }
      case 'qf7': { const p = plainP(r.L); return keep({ k7: 'qf', a: p[2], b: pcoef(p, 1), c: pcoef(p, 0) }); }
      case 'dsc7': { const p = plainP(r.L); return keep({ k7: 'vd', from: eqText(r), D: discOf(p).n, say: c.v === 2 ? 'two' : c.v === 1 ? 'one' : 'none', kind: 'count' }); }
    }
    return r;
  }
  function applyRt(r, c) {
    switch (c.op) {
      case 'pm7': { r.pm = true; const rt = r.rad !== null ? rootOf(r.rad) : null; if (rt) { r.s = fMul(r.s, rt.s); r.n = rt.n; r.rad = null; } return r; }
      case 'i7': { const m = -r.rad; if (isSq(m)) { r.s = fMul(r.s, F(isqrt(m))); r.n = -1; } else r.n = -m; r.rad = null; return r; }
      case 'mv7': r.q = fAdd(r.q, c.t.c); r.b = F(0); return r;
      case 'dv7': r.q = fDiv(r.q, c.n); r.s = fDiv(r.s, c.n); r.a = F(1); return r;
      case 'spl7': return { ...csState([{ a: F(1), b: F(0), r: fAdd(r.q, r.s) }, { a: F(1), b: F(0), r: fSub(r.q, r.s) }], { qid: r.qid }), gq: r.gq, skill: r.skill };
    }
    return r;
  }
  function applyQf(r, c) {
    const D = discOf(PL([r.c, r.b, r.a])).n, den = fMul(F(2), r.a), q = fDiv(fNeg(r.b), den), s = fDiv(F(1), den);
    const base = { qid: r.qid, gq: r.gq, skill: r.skill, cplx: r.cplx };
    if (D === 0) return { ...csState([{ a: F(1), b: F(0), r: q, one: true }], { qid: r.qid }), ...base, k7: 'cs' };
    if (D < 0 && !r.cplx) return { ...base, k7: 'vd', from: qfText(r), D, say: 'nosol', kind: 'formula' };
    const rt = rootOf(D);
    return { ...base, k7: 'rt', a: F(1), b: F(0), q, s: rt ? fMul(s, rt.s) : s, rad: rt ? null : D, n: rt ? rt.n : null, pm: true, qf: true };
  }
  function applyCx(r, c, sl) {
    const i = +sl.refs[0].slice(1), it = r.items[i];
    const T = (cc, e) => ({ t: 't', c: FI(cc), e });
    switch (c.op) {
      case 'drop7': case 'neg7': { const s = it.s; r.items.splice(i, 1, ...[T(fMul(F(s), it.z[0]), 0), T(fMul(F(s), it.z[1]), 1)].filter(t => !fz(t.c))); break; }
      case 'box7': {
        const ts = [];
        it.A.forEach((a, j) => it.B.forEach((b, k) => { const v = fMul(a, b); if (!fz(v)) ts.push(T(fMul(F(it.s || 1), v), j + k)); }));
        r.items.splice(i, 1, ...ts); break;
      }
      case 'i27': r.items[i] = T(fNeg(it.c), 0); break;
      case 'cmb7': {
        const is = sl.refs.map(x => +x.slice(1)), sum = is.reduce((a, j) => fAdd(a, r.items[j].c), F(0));
        r.items[is[0]] = T(sum, r.items[is[0]].e);
        r.items = r.items.filter((x, j) => !is.slice(1).includes(j) && !(j === is[0] && fz(sum)));
        if (!r.items.length) r.items = [T(0, 0)];
        break;
      }
      case 'srt7': r.items = [r.items[1], r.items[0]]; break;
    }
    return r;
  }

  // ================================================================ text (for variety, answers and messages)
  function rhsText(e, html) {
    // q ± s·root, written over one denominator when they share one: (3 ± √41)/4
    const root = e.rad !== null && e.rad !== undefined ? (html ? `√<span class="rad7">${numText(e.rad)}</span>` : `√${e.rad < 0 ? '(' + numText(e.rad) + ')' : e.rad}`)
      : e.n === 1 ? '' : e.n === -1 ? (html ? XV('i') : 'i') : e.n < 0 ? (html ? XV('i') : 'i') + (html ? `√<span class="rad7">${-e.n}</span>` : `√${-e.n}`) : (html ? `√<span class="rad7">${e.n}</span>` : `√${e.n}`);
    const d = lcm(e.q.d, e.s.d), qn = e.q.n * (d / e.q.d), sn = e.s.n * (d / e.s.d);
    const sAbs = Math.abs(sn);
    const sPart = (root && sAbs === 1 ? '' : String(sAbs)) + root;
    let num;
    if (qn === 0) num = (e.pm ? '±' : sn < 0 ? MINUS : '') + (sPart || '1');
    else num = `${numText(qn)} ${e.pm ? '±' : sn < 0 ? MINUS : '+'} ${sPart || '1'}`;
    if (d === 1) return num;
    return html ? `<span class="frac f7"><span>${num}</span><span>${d}</span></span>` : `(${num})/${d}`;
  }
  const linText = (a, b, html) => pText(PL([b, a]), html);
  function eqText(e, html) { return `${xText(e.L, html)} = ${xText(e.R, html)}`; }
  function qfText(e, html) {
    const b2 = fMul(e.b, e.b), fac = fMul(F(-4), fMul(e.a, e.c));
    const inner = `${fNum(b2, html)} ${fac.n < 0 ? MINUS : '+'} ${fNum(fAbs(fac), html)}`;
    const num = `${fNum(fNeg(e.b), html)} ± √(${inner})`, den = fNum(fMul(F(2), e.a), html);
    return html ? `${XV()} = <span class="frac f7 big7"><span>${num}</span><span>${den}</span></span>` : `x = (${num})/${den}`;
  }
  const csText = (e, html) => e.cs.map(c => `${linText(c.a, c.b, html)} = ${fNum(c.r, html)}`).join(html ? ' <span class="or7">or</span> ' : ' or ');
  function cxText(e, html) {
    return e.items.map((it, j) => {
      const lead = s => (j ? (s < 0 ? MINUS + ' ' : '+ ') : s < 0 ? MINUS : '');
      if (it.t === 'g') return `${lead(it.s)}(${zText(it.z, html)})`;
      if (it.t === 'pr') return `${lead(it.s || 1)}(${zText(it.A, html)})(${zText(it.B, html)})`;
      return iTerm(it, j === 0, html);
    }).join(' ');
  }
  function iTerm(t, first, html) {
    const a = fAbs(t.c), I = html ? XV('i') : 'i', lit = t.e === 0 ? '' : t.e === 1 ? I : I + '²';
    const body = (lit && fIs(a, 1) ? '' : fNum(a, html)) + lit;
    return (t.c.n < 0 ? (first ? MINUS : MINUS + ' ') : first ? '' : '+ ') + body;
  }
  const zText = (z, html) => { const ts = [{ c: z[0], e: 0 }, { c: z[1], e: 1 }].filter(t => !fz(t.c)); return ts.length ? ts.map((t, j) => iTerm(t, j === 0, html)).join(' ') : '0'; };
  const grText = (e, html) => `${html ? XV('y') : 'y'} = ${pText(PL([e.c, e.b, e.a]), html)}`;
  function vfText(e, html) {
    const y = html ? XV('y') : 'y', h = fMul(e.b, F(1, 2)), n = fMul(h, h), p = PL([e.c, e.b, 1]);
    if (e.st === 0) return `${y} = ${pText(p, html)}`;
    if (e.st === 1) return `${y} = (${pText(PL([n, e.b, 1]), html)})${kText(fNeg(n), html)}${kText(e.c, html)}`;
    if (e.st === 2) return `${y} = (${pText(PL([h, 1]), html)})²${kText(fNeg(n), html)}${kText(e.c, html)}`;
    return `${y} = (${pText(PL([h, 1]), html)})²${kText(fSub(e.c, n), html)}`;
  }
  const ptT = (x, y) => `(${fracText(x)}, ${fracText(y)})`;
  function textOf7(e) {
    switch (e.k7) {
      case 'fx': return 'factor ' + xText(e.L);
      case 'eq': return (e.method || '') + ' ' + (e.ask === 'count' ? 'count ' : '') + eqText(e);
      case 'cx': return 'cx ' + cxText(e);
      case 'gr': return e.ask + ' ' + grText(e);
      case 'vf': return 'vf' + (e.findV ? 'v ' : ' ') + vfText(e);
      default: return JSON.stringify(e);
    }
  }
  function answerOf(e) {
    switch (e.k7) {
      case 'fx': return e.prime ? `${xText(e.L)} is prime` : xText(e.L);
      case 'rt': return `x = ${rhsText(e)}`;
      case 'cs': return e.cs.map(c => 'x = ' + fracText(c.r)).join(' or ');
      case 'vd': return vdSay(e);
      case 'vf': return vfText(e) + (e.vtx ? `, vertex ${ptT(e.vtx.x, e.vtx.y)}` : '');
      case 'cx': return cxText(e);
      case 'gr': return e.ask === 'axis' ? `axis x = ${fracText(e.h)}` : e.ask === 'max' ? `${e.a.n < 0 ? 'max' : 'min'} y = ${fracText(e.k)} at x = ${fracText(e.h)}` : `vertex ${ptT(e.h, e.k)}`;
      default: return '';
    }
  }
  const vdSay = e => (e.say === 'two' ? '2 real solutions' : e.say === 'one' ? '1 real solution' : e.say === 'none' ? 'no real solutions' : 'no real solution');

  // ================================================================ path, skills
  const HOME = { gcf7: 'gcf7', tri7: 'trinom', split7: 'trinom', grp7: 'trinom', out7: 'trinom', dos7: 'facpat', psq7: 'facpat', prime7: 'facpat',
    zp7: 'zprod', sqrt7: 'sqroot', pm7: 'sqroot', fold7: 'cmpsq', as7: 'cmpsq', vx7: 'cmpsq', qf7: 'qform', dsc7: 'qform',
    i7: 'cplx', i27: 'cplx', drop7: 'cplx', neg7: 'cplx', srt7: 'cplx', ax7: 'qgraph', plg7: 'qgraph', dir7: 'qgraph', y07: 'qgraph' };
  function skillFor(m, e, main) {
    let home = HOME[m.op] || main;
    if (e.k7 === 'cx') home = 'cplx';
    if (m.op === 'mv7' && e.k7 === 'eq' && e.method === 'square') home = 'cmpsq';
    if (m.op === 'spl7' && e.qf) home = 'qform';
    return home === main || (typeof isUnlocked === 'function' && isUnlocked(home)) ? home : main;
  }
  function pathOf7(e, main) {
    const path = []; let s = e;
    for (let i = 0; i < 40; i++) { const m = canon7(s); if (!m) break; path.push({ state: s, move: m, skill: skillFor(m, s, main) }); s = apply7(s, m, m.ref); }
    return { path, end: s };
  }
  function makeEquation7(state, enemy) {
    const main = state.skill || 'gcf7', { path, end } = pathOf7(state, main);
    return { start: state, end, path, main, skills: [...new Set([main, ...path.map(p => p.skill)])], enemy, act2: true, act7: true, answer: F(0), answerText: answerOf(end) };
  }
  function refreshPath(cur) {
    const { path: fresh, end } = pathOf7(cur.state, cur.main);
    cur.path = cur.path.slice(0, cur.step).concat(fresh);
    cur.answerText = answerOf(end);   // the answer the player is heading to, which can differ from the first plan (the other split, etc.)
  }
  const isSolved7 = e => !movesOf(e).length;

  // ================================================================ cards
  const pmT = (c, html) => (c.n < 0 ? MINUS + ' ' : '+ ') + fNum(fAbs(c), html);
  const linF = (p, html) => `(${pText(p, html)})`;
  const CARD = {
    gcf7:   c => ({ label: `GCF ${monoText(c.g, true)}`, text: `Factor out ${monoText(c.g, true)}`, kind: 'Factor out the GCF', icon: 'gcf7' }),
    tri7:   c => ({ label: linF(c.A, true) + linF(c.B, true), text: `Factor as ${linF(c.A, true)}${linF(c.B, true)}`, kind: 'Factor the trinomial', icon: 'tri7' }),
    split7: c => ({ label: `${tText({ c: F(c.u), e: 1 }, true)} ${pmT(F(c.w), true)}${XV()}`, text: `Split the middle term into ${tText({ c: F(c.u), e: 1 }, true)} ${mText({ c: F(c.w), e: 1 }, false, true)}`, kind: 'Split the middle term', icon: 'split7' }),
    grp7:   () => ({ label: 'Pairs', text: 'Factor the GCF out of each pair', kind: 'Group in pairs', icon: 'grp7' }),
    out7:   () => ({ label: 'Pull out ( )', text: 'Pull the shared bracket out front', kind: 'Pull out the bracket', icon: 'out7' }),
    dos7:   () => ({ label: 'a² − b²', text: 'a² − b² = (a + b)(a − b)', kind: 'Difference of squares', icon: 'dos7' }),
    psq7:   () => ({ label: '(a + b)²', text: 'a² + 2ab + b² = (a + b)²', kind: 'Perfect square', icon: 'psq7' }),
    prime7: () => ({ label: 'Prime', text: 'It can\'t be factored', kind: 'Prime', icon: 'prime7' }),
    zp7:    () => ({ label: 'Zero split', text: 'A·B = 0 means A = 0 or B = 0', kind: 'Zero-product split', icon: 'zp7' }),
    box7:   () => ({ label: 'Multiply out', text: 'Multiply the brackets out', kind: 'Multiply out', icon: 'box6' }),
    cmb7:   () => ({ label: 'Combine', text: 'Combine like terms', kind: 'Combine like terms', icon: 'comb' }),
    mv7:    c => ({ label: `${c.t.c.n < 0 ? MINUS : '+'} ${mBody({ c: c.t.c, e: c.t.e }, true)}`, text: `${c.t.c.n < 0 ? 'Subtract' : 'Add'} ${mBody({ c: c.t.c, e: c.t.e }, true)} ${c.t.c.n < 0 ? 'from' : 'to'} both sides`, kind: c.t.c.n < 0 ? 'Subtract' : 'Add', icon: c.t.c.n < 0 ? 'sub' : 'add' }),
    dv7:    c => ({ label: `${DIV} ${fracText(c.n).replace(/^−/, '(−') + (c.n.n < 0 ? ')' : '')}`, text: `Divide both sides by ${fracText(c.n)}`, kind: 'Divide', icon: 'div' }),
    sqrt7:  () => ({ label: '√ both', text: 'Take the square root of both sides', kind: 'Square root both sides', icon: 'sqrt7' }),
    pm7:    () => ({ label: '±', text: 'A root has two signs: + and −', kind: '± (plus or minus)', icon: 'pm7' }),
    i7:     c => ({ label: '√−1 = i', text: c.rad ? `Pull out i: √${numText(c.rad)} = ${isSq(-c.rad) ? isqrt(c.rad) : '√' + (-c.rad)}i` : 'Pull out i from the root of a negative', kind: 'Pull out i', icon: 'i7' }),
    spl7:   () => ({ label: 'Split ±', text: 'Work out the + answer and the − answer', kind: 'Split the ±', icon: 'spl7' }),
    fold7:  c => ({ label: `(${pText(PL([c.h, 1]), true)})²`, text: `Fold it into (${pText(PL([c.h, 1]), true)})²`, kind: 'Fold into a square', icon: 'psq7' }),
    as7:    c => ({ label: `± ${fNum(c.n, true)}`, text: `Add and subtract ${fNum(c.n, true)}`, kind: 'Add and subtract (b/2)²', icon: 'as7' }),
    qf7:    c => ({ label: `<span class="qfl7">${qfVariant(c.e7, c.v, true)}</span>`, text: 'Plug a, b and c into the quadratic formula', kind: 'Quadratic formula', icon: 'qf7' }),
    dsc7:   c => ({ label: c.v === 2 ? '2 answers' : c.v === 1 ? '1 answer' : 'No real', text: c.v === 2 ? 'b² − 4ac > 0: two real answers' : c.v === 1 ? 'b² − 4ac = 0: one real answer' : 'b² − 4ac < 0: no real answers', kind: 'Check the discriminant', icon: 'dsc7' }),
    i27:    () => ({ label: `${XV('i')}² = ${MINUS}1`, text: 'Replace i² with −1', kind: 'i² = −1', icon: 'i7' }),
    drop7:  () => ({ label: 'Drop ( )', text: 'A + in front: the brackets go away', kind: 'Drop the brackets', icon: 'drop6' }),
    neg7:   () => ({ label: 'Minus in', text: 'Flip the sign of both parts inside', kind: 'Distribute the minus', icon: 'neg' }),
    srt7:   () => ({ label: `a + b${XV('i')}`, text: 'Standard form: real part first', kind: 'Standard form a + bi', icon: 'sort6' }),
    ax7:    c => ({ label: `${XV()} = ${fNum(c.h, true)}`, text: `Axis of symmetry: x = ${fracText(c.h)}`, kind: 'Axis x = −b/(2a)', icon: 'ax7' }),
    plg7:   () => ({ label: 'Plug in', text: 'Put the axis x into the rule to get y', kind: 'Plug in for y', icon: 'plg7' }),
    dir7:   c => ({ label: { downmax: 'Down, max', upmin: 'Up, min', downmin: 'Down, min', upmax: 'Up, max' }[c.v], text: { downmax: 'Opens down: the vertex is a maximum', upmin: 'Opens up: the vertex is a minimum', downmin: 'Opens down: the vertex is a minimum', upmax: 'Opens up: the vertex is a maximum' }[c.v], kind: 'Opens up or down', icon: 'dir7' }),
    y07:    () => ({ label: `Set ${XV('y')} = 0`, text: 'x-intercepts are where y = 0', kind: 'Set y = 0', icon: 'y07' }),
    vx7:    c => ({ label: `(${fNum(c.x, true)}, ${fNum(c.y, true)})`, text: `The vertex is (${fracText(c.x)}, ${fracText(c.y)})`, kind: 'Read the vertex', icon: 'vx7' }),
  };
  // the formula with a, b, c plugged in, right (ok) or with a classic slip
  function qfVariant(e, v, html) {
    if (!e) return 'x = (−b ± √(b² − 4ac))/(2a)';
    const a = e.a, b = e.b, c = e.c, b2 = fMul(b, b), fac = fMul(F(-4), fMul(a, c));
    const facS = v === 'sign4ac' ? fNeg(fac) : fac, top = v === 'signb' ? b : fNeg(b), den = v === 'over a' ? a : fMul(F(2), a);
    const b2S = v === 'negb2' ? fNeg(b2) : b2;
    const inner = `${fNum(b2S, html)} ${facS.n < 0 ? MINUS : '+'} ${fNum(fAbs(facS), html)}`;
    const num = `${fNum(top, html)} ± √(${inner})`;
    return html ? `<span class="frac f7"><span>${num}</span><span>${fNum(den, html)}</span></span>` : `(${num})/${fracText(den)}`;
  }
  const info = c => (c && c.a7 && CARD[c.op] ? CARD[c.op](c) : null);
  const label = c => (c && c.op === 'trap' && c.a7 ? `<span class="clong l7">${c.label}</span>` : info(c) ? `<span class="clong l7">${info(c).label}</span>` : null);
  const text = c => (c && c.op === 'trap' && c.a7 ? c.text : info(c) ? info(c).text : null);
  const kind = c => (c && c.op === 'trap' && c.a7 ? 'Trap: ' + c.trap : info(c) ? info(c).kind : null);
  const icon = c => (c && c.op === 'trap' && c.a7 ? c.icon : info(c) ? info(c).icon : null);
  const SLOT = { gcf7: 0, tri7: 1, split7: 1, grp7: 2, out7: 3, dos7: 2, psq7: 3, prime7: 4, zp7: 4, box7: 0, cmb7: 1, sqrt7: 2, pm7: 3,
    fold7: 3, as7: 2, qf7: 1, dsc7: 2, i7: 4, i27: 4, spl7: 5, drop7: 0, neg7: 1, srt7: 5, y07: 0, dir7: 1, ax7: 2, plg7: 3, vx7: 5 };
  const slotOf7 = c => (c && c.a7 && c.op !== 'trap' ? SLOT[c.op] ?? null : null);
  const targetSel = c => (c && c.a7 && (c.scope || 'both') === 'part' ? '#equation .tok[data-ref]' : null);

  // Where a ◎ card can go: one place per legal move, or else the parts of its kind, so a wrong card still
  // has to be dropped somewhere.
  const refsNow = () => [...$('equation').querySelectorAll('.tok[data-ref]')].map(t => t.dataset.ref);
  function kindPlaces(e, op) {
    const all = refsNow();
    const fac = ['gcf7', 'tri7', 'split7', 'grp7', 'out7', 'dos7', 'psq7'];
    if (fac.includes(op)) return all.filter(r => /^Lf\d/.test(r));
    if (['pm7', 'i7', 'spl7'].includes(op)) return all.filter(r => r === 'R');
    if (['i27', 'drop7', 'neg7'].includes(op)) return all.filter(r => /^i\d/.test(r));
    return all.slice(0, 1);
  }
  function places(e, c) {
    const op = c.op === 'trap' ? c.like : c.op;
    if (!op) return [];
    const legal = movesOf(e).filter(s => s.op === op && s.refs[0] !== '*' && (c.op === 'trap' || s.ok(c)));
    if (legal.length) return [...new Set(legal.map(s => s.refs[0]))];
    const anyOp = movesOf(e).filter(s => s.op === op && s.refs[0] !== '*');
    if (anyOp.length) return [...new Set(anyOp.map(s => s.refs[0]))];
    return kindPlaces(e, op);
  }
  const refEl = ref => $('equation').querySelector(`.tok[data-ref="${ref}"]`);
  function autoTarget(c) {
    if (!cur || !cur.act7) return 'pass';
    if (!c.a7) return 'pass';
    const ps = places(cur.state, c);
    if (ps.length >= 2) return undefined;
    if (!ps.length) return null;
    return refEl(ps[0]) || ps[0];
  }
  function onDrag(c, on) {
    document.querySelectorAll('.ok7').forEach(el => el.classList.remove('ok7'));
    if (!on || !cur || !cur.act7) return;
    const hl = difficulty.highlight === 'on' || isTutorial() || (difficulty.highlight === 'afterWrong' && cur.wrong > 0);
    if (!hl || !targetSel(c)) return;
    for (const el of document.querySelectorAll('#equation .tok[data-ref]')) if (correct7(cur.state, c, el)) el.classList.add('ok7');
  }

  // ---------------------------------------------------------------- hands
  const DECOYS = [1, 1, 2, 2];
  function trap(name, like, lbl, txt, why, iconKey) { return { op: 'trap', a7: true, trap: name, like, scope: BOTH.has(like) ? 'both' : 'part', label: lbl, text: txt, why, icon: iconKey }; }
  const L1 = (k, a = 1) => PL([k, a]);
  // the factor the next factoring move works on
  const facTarget = e => { const x = e.L; const i = x.fs.findIndex(f => f.t !== 'p' || pdeg(f.p) >= 2); return i >= 0 ? { f: x.fs[i], i } : null; };
  // wrong factor pairs for a trinomial: signs swapped, a pair that multiplies right but adds wrong, and one that adds right
  function badPairs(p) {
    const [c0, b, a] = [0, 1, 2].map(j => pcoef(p, j).n), out = [];
    const pr = trinomPair(a, b, c0);
    if (pr) {
      out.push({ A: PL([-pr.A[0].n, pr.A[1].n]), B: PL([-pr.B[0].n, pr.B[1].n]) });   // both signs flipped
      out.push({ A: PL([pr.A[0].n, pr.B[1].n]), B: PL([pr.B[0].n, pr.A[1].n]) });                                     // numbers swapped between brackets
      out.push({ A: PL([-pr.A[0].n, pr.A[1].n]), B: pr.B });                                                          // one sign flipped
    }
    if (a === 1) {
      for (let r = 1; r <= Math.abs(c0); r++) if (c0 % r === 0) { const s = c0 / r; if (r + s !== b) out.push({ A: L1(r), B: L1(s) }); if (-r - s !== b) out.push({ A: L1(-r), B: L1(-s) }); }
      for (let r = -9; r <= 9; r++) { const s = b - r; if (r && s && r * s !== c0 && Math.abs(r) <= 12) out.push({ A: L1(r), B: L1(s) }); }
    } else if (!pr) {
      out.push({ A: L1(isqrt(Math.abs(c0)) || 1, isqrt(a) || 1), B: L1(isqrt(Math.abs(c0)) || 1, isqrt(a) || 1) });
      out.push({ A: L1(isqrt(Math.abs(c0)) || 1, isqrt(a) || 1), B: L1(-(isqrt(Math.abs(c0)) || 1), isqrt(a) || 1) });
    }
    const ok = q => q.A[1].n > 0 && q.B[1].n > 0 && !fz(q.A[0]) && !fz(q.B[0]) && !pEq(pmul(q.A, q.B), p);
    return shuffle(out.filter(ok)).slice(0, 4);
  }
  function badSplits(p) {
    const [c0, b, a] = [0, 1, 2].map(j => pcoef(p, j).n), ac = a * c0, out = [];
    for (let u = -Math.abs(ac); u <= Math.abs(ac); u++) if (u && ac % u === 0) { const w = ac / u; if (u + w !== b && Math.abs(u) >= Math.abs(w)) out.push({ u, w }); }
    out.push({ u: b - c0, w: c0 }, { u: a, w: b - a }, { u: -b + 1, w: -1 });
    return shuffle(out.filter(o => o.u && o.w && o.u + o.w !== b || (o.u && o.w && o.u * o.w !== ac))).slice(0, 4);
  }
  function family(e, want) {
    const out = [], add = c => out.push(c);
    const facs = () => {
      const ft = facTarget(e); if (!ft) return;
      const f = ft.f;
      if (f.t === 'g4') { add(C7('out7')); add(C7('cmb7')); add(C7('box7')); return; }
      if (f.t === 'gp') { add(C7('grp7')); add(C7('box7')); return; }
      if (f.t !== 'p') return;
      const { g, e: me } = pCont(f.p);
      if (g !== 1 || me > 0) {
        if (g > 1 && me > 0) { add(C7('gcf7', { g: { c: F(g), e: 0 } })); add(C7('gcf7', { g: { c: F(1), e: me } })); }
        if (g !== 1) add(C7('gcf7', { g: { c: F(g * 2), e: me } }));
        if (g < 0) add(C7('gcf7', { g: { c: F(-g), e: me } }));
        add(C7('gcf7', { g: { c: F(g), e: me + 1 } }));
        if (g > 2) { const d = [2, 3, 5].find(k => g % k === 0 && k < g); if (d) add(C7('gcf7', { g: { c: F(d), e: me } })); }
        if (pdeg(f.p) === 2) badPairs(f.p).slice(0, 1).forEach(q => add(C7('tri7', q)));
        add(C7('prime7'));
        return;
      }
      if (pdeg(f.p) === 2) {
        const a = f.p[2].n;
        badPairs(f.p).forEach(q => add(C7('tri7', q)));
        if (a !== 1) badSplits(f.p).forEach(q => add(C7('split7', q)));
        add(C7('dos7')); add(C7('psq7')); add(C7('prime7'));
        if (pCont(f.p).g === 1) add(C7('gcf7', { g: { c: F(Math.abs(a) > 1 ? Math.abs(a) : 2), e: 0 } }));
      }
    };
    const term = t => C7('mv7', { t });
    const mvFam = (t) => { add(term({ c: fNeg(t.c), e: t.e })); if (t.e === 0) add(term({ c: fMul(t.c, F(2)), e: 0 })); };
    switch (e.k7) {
      case 'fx': facs(); break;
      case 'eq': {
        const L = e.L, R0 = isZero(e.R);
        if (e.ask === 'count') { [2, 1, 0].forEach(v => add(C7('dsc7', { v }))); add(C7('qf7', { v: 'ok', e7: abcOf(L) })); break; }
        if (want && want.op === 'mv7') mvFam(want.t);
        if (want && want.op === 'dv7') { add(C7('dv7', { n: fMul(want.n, F(2)) })); const k = constOffL(e) || pcoef(xPoly(e.R), 0); if (!fz(k) && !fEq(fAbs(k), fAbs(want.n))) add(C7('dv7', { n: fAbs(k) })); add(term({ c: fNeg(want.n), e: 0 })); }
        if (e.method === 'factor') {
          if (R0 && fz(L.k)) facs();
          add(C7('zp7')); if (!R0) add(C7('box7'));
          if (R0 && !fz(L.k)) add(C7('zp7'));
        }
        if (e.method === 'root' || e.method === 'square') {
          add(C7('sqrt7')); add(C7('pm7'));
          const p = plainP(L);
          if (e.method === 'square' && p && pdeg(p) === 2) {
            const b = pcoef(p, 1), h = fMul(b, F(1, 2));
            if (fIs(p[2], 1) && fz(pcoef(p, 0)) && !fz(b)) [fAbs(b), fMul(b, b), fAbs(h), fMul(fAbs(b), F(2))].forEach(n => add(term({ c: n, e: 0 })));
            if (monicPsq(p)) [b, fMul(h, h), fNeg(h)].forEach(hh => add(C7('fold7', { h: hh })));
          }
        }
        if (e.method === 'formula') { const ab = abcOf(L); if (ab && R0) ['signb', 'over a', 'sign4ac', 'negb2'].forEach(v => add(C7('qf7', { v, e7: ab }))); add(C7('dsc7', { v: 2 })); }
        break;
      }
      case 'qf': [2, 1, 0].forEach(v => add(C7('dsc7', { v }))); add(C7('spl7')); add(C7('i7')); break;
      case 'rt': {
        add(C7('pm7')); add(C7('spl7')); add(C7('i7'));
        if (!fz(e.b)) mvFam({ c: e.b, e: 0 }); else add(term({ c: F(e.b.n || (e.q.n ? -e.q.n : 1)), e: 0 }));
        if (!fIs(e.a, 1)) add(C7('dv7', { n: fMul(e.a, F(2)) })); else add(C7('dv7', { n: F(2) }));
        break;
      }
      case 'cs': {
        const i = e.cs.findIndex(c => !(fIs(c.a, 1) && fz(c.b))), c = e.cs[i];
        if (!fz(c.b)) { mvFam({ c: c.b, e: 0 }); add(C7('dv7', { n: fAbs(c.b) })); } else { add(C7('dv7', { n: fNeg(c.a) })); add(term({ c: fNeg(c.a), e: 0 })); }
        e.cs.forEach((o, j) => { if (j !== i && !fz(o.b)) add(term({ c: fNeg(o.b), e: 0 })); });
        add(C7('zp7'));
        break;
      }
      case 'vf': {
        const b = e.b, h = fMul(b, F(1, 2)), n = fMul(h, h);
        if (e.st === 0) [fAbs(b), fMul(b, b), fAbs(h)].forEach(v => { if (!fEq(v, n)) add(C7('as7', { n: v })); });
        if (e.st === 1) [b, n, fNeg(h)].forEach(v => { if (!fEq(v, h)) add(C7('fold7', { h: v })); });
        if (e.st <= 2) { add(C7('cmb7')); add(C7('box7')); }
        if (e.st === 3) { const k = fSub(e.c, n); [{ x: h, y: k }, { x: fNeg(h), y: fNeg(k) }, { x: h, y: fNeg(k) }, { x: e.b, y: e.c }].forEach(v => add(C7('vx7', v))); }
        break;
      }
      case 'cx': {
        ['drop7', 'neg7', 'box7', 'i27', 'cmb7', 'srt7'].forEach(op => add(C7(op)));
        break;
      }
      case 'gr': {
        const a = e.a, b = e.b, h = fDiv(fNeg(b), fMul(F(2), a));
        [fNeg(h), fDiv(fNeg(b), a), fDiv(b, a), fDiv(fMul(F(2), a), b).n ? fDiv(fNeg(fMul(F(2), a)), b) : F(1), e.c].forEach(v => { if (!fEq(v, h)) add(C7('ax7', { h: v })); });
        ['downmax', 'upmin', 'downmin', 'upmax'].forEach(v => add(C7('dir7', { v })));
        add(C7('plg7')); add(C7('y07'));
        break;
      }
    }
    return out;
  }
  const abcOf = x => { const p = plainP(x); return p && pdeg(p) === 2 ? { a: p[2], b: pcoef(p, 1), c: pcoef(p, 0) } : null; };
  // Rule decoys (the classic mistakes, dealt at every level outside tutorials) and Expert traps.
  function specials(e) {
    const out = { rule: [], traps: [] };
    if (e.k7 === 'eq') {
      const Lp = plainP(e.L), Rp = plainP(e.R);
      if (Lp && Rp && e.method === 'factor' && pdeg(Rp) >= 1 && fz(pcoef(Rp, 0)) && fz(pcoef(Lp, 0)))
        out.rule.push(trap('divide by x', 'dv7', `${DIV} ${XV()}`, 'Divide both sides by x',
          P(`Dividing by ${XV()} throws away an answer. ${XV()} could be 0, and you can't divide by 0, so ${XV()} = 0 vanishes without a trace. Move everything to one side so it equals 0, then factor: ${XV()} = 0 stays as one of the answers.`), 'div'));
      if (e.method === 'factor' && !isZero(e.R) && !isPlain(e.L))
        out.rule.push(C7('zp7'));
      if ((e.method === 'root' || e.method === 'square') && movesOf(e)[0] && movesOf(e)[0].op !== 'sqrt7' && movesOf(e)[0].op !== 'fold7')
        out.rule.push(C7('sqrt7'));
      if (Lp && pdeg(Lp) === 2 && !isZero(e.R) && e.method !== 'factor')
        out.traps.push(trap('root of each term', 'sqrt7', '√ each term', 'Take the root of each term on its own',
          P(`A square root doesn't split over + or ${MINUS}: √(${XV()}² + 9) is not ${XV()} + 3 (try ${XV()} = 4: √25 = 5, but 4 + 3 = 7). Only take the root once the square is alone on its side.`), 'sqrt7'));
      if (e.method === 'factor' && Lp && pdeg(Lp) === 2 && isZero(e.R) && Lp[2].n > 1 && pCont(Lp).g === 1)
        out.traps.push(trap('divide out a', 'gcf7', `${DIV} ${Lp[2].n} all`, `Divide every term by ${Lp[2].n}`, P(`${Lp[2].n} isn't a factor of every term, so dividing it out changes the numbers you get. Factor by grouping instead.`), 'gcf7'));
    }
    if (e.k7 === 'fx') {
      const ft = facTarget(e);
      if (ft && ft.f.t === 'p' && pdeg(ft.f.p) === 2 && ft.f.p[2].n > 1 && pCont(ft.f.p).g === 1)
        out.traps.push(trap('divide out a', 'gcf7', `${DIV} ${ft.f.p[2].n} all`, `Divide every term by ${ft.f.p[2].n}`,
          P(`Factoring has to keep the expression equal to what it was. Dividing every term by ${ft.f.p[2].n} makes a different expression (and ${ft.f.p[2].n} doesn't go into every term anyway). Only a factor that divides every term can come out front.`), 'gcf7'));
      if (ft && ft.f.t === 'p' && isDos(ft.f.p)) out.rule.push(C7('psq7'));
      if (ft && ft.f.t === 'p' && pdeg(ft.f.p) === 2 && fz(pcoef(ft.f.p, 1)) && pcoef(ft.f.p, 0).n > 0) out.rule.push(C7('dos7'));
    }
    if (e.k7 === 'rt' && e.pm) out.traps.push(trap('only the + root', 'pm7', 'Only +', 'Keep only the + answer: roots are positive', P(`√16 means the positive root, 4, but ${XV()}² = 16 has two answers: 4² = 16 and (${MINUS}4)² = 16. Once you take the root of both sides, both signs stay.`), 'pm7'));
    if (e.k7 === 'cx') {
      if (e.items.some(it => it.t === 't' && it.e === 2)) out.rule.push(trap('i² = 1', 'i27', `${XV('i')}² = 1`, 'Replace i² with 1 (a square is never negative)',
        P(`${XV('i')} is defined as √${MINUS}1, so ${XV('i')}² = ${MINUS}1. That's the whole point of ${XV('i')}: it's the number whose square is negative.`), 'i7'));
      const by = new Set(e.items.filter(it => it.t === 't').map(it => it.e));
      if (by.has(0) && by.has(1) && e.items.every(it => it.t === 't')) out.traps.push(trap('real + imaginary', 'cmb7', `3 + 2${XV('i')} = 5${XV('i')}`, 'Add the real and the imaginary parts together',
        P(`A real number and an imaginary one are unlike terms, like 3 and 2${XV()}. They stay apart: a + b${XV('i')} is as simple as it gets.`), 'comb'));
    }
    if (e.k7 === 'gr' && !e.h) out.traps.push(trap('vertex at c', 'ax7', `${XV()} = 0`, 'The vertex is on the y-axis, at (0, c)', P(`c is where the graph crosses the y-axis, not the vertex. The vertex is on the axis of symmetry, ${XV()} = ${MINUS}b/(2a).`), 'ax7'));
    return out;
  }
  const alsoRight = (e, c) => legalAnywhere(e, c);
  function makeHand7(e, correct, size) {
    const tut = isTutorial(), L = lvl();
    const hand = [correct], seen = new Set([cardLabel(correct)]);
    const add = c => { if (hand.length >= size) return; const k = cardLabel(c); if (seen.has(k)) return; if (c.op !== 'trap' && alsoRight(e, c)) return; seen.add(k); hand.push(c); };
    const sp = specials(e);
    if (!tut && L >= 3) sp.traps.slice(0, 1).forEach(add);
    if (!tut) sp.rule.slice(0, DECOYS[L]).forEach(add);
    shuffle(family(e, correct)).forEach(add);
    // a short family: fill with other moves of this act so the hand is always full
    [C7('box7'), C7('cmb7'), C7('prime7'), C7('sqrt7'), C7('zp7'), C7('dv7', { n: F(2) }), C7('mv7', { t: { c: F(-1), e: 0 } })].forEach(add);
    return shuffle(hand);
  }

  // ================================================================ wrong moves
  const S = (long, short, more) => (long ? P(more || short) : short);
  function why7(e, card, target, long) {
    const ref = refOf(target), ms = movesOf(e), want = ms[0] && ms[0].card;
    if (card.op === 'trap') return long ? card.why : 'That\'s a trap: it isn\'t true. Tap Why? to see why.';
    if (!card.a7) return S(long, 'That card doesn\'t fit here.');
    if (e.k7 === 'rt' && !e.pm) return S(long, 'You owe the ± first: a square root has two answers.',
      `When you take the square root of both sides, the answer can be positive or negative: 4² = 16 and (${MINUS}4)² = 16. So right after √ both sides, drop ± on the root. Then carry on.`);
    if (legalAnywhere(e, card)) return S(long, 'Right card, wrong place: drop it on the part it changes.');
    const r = whyOp(e, card, ref, want);
    if (r) return S(long, r[0], r[1]);
    return S(long, 'That isn\'t a step that works here.', `That move doesn't make progress on this one. Look at what the problem asks for, and at what's in the way of it.`);
  }
  function whyOp(e, card, ref, want) {
    const op = card.op, ft = (e.k7 === 'fx' || e.k7 === 'eq') ? facTarget(e) : null, f = ft && ft.f;
    if (op === 'gcf7' && f && f.t === 'p') {
      const { g, e: me } = pCont(f.p), G = { c: F(g), e: me }, cg = card.g, P0 = pText(f.p, true);
      const divides = (g % cg.c.n === 0) && cg.e <= me;
      if (Math.abs(cg.c.n) === Math.abs(g) && cg.e === me && cg.c.n !== g) return ['Take the minus out too.', `The first term is negative, so factor out ${monoText(G, true)}: then the bracket starts with a positive term.`];
      if (g === 1 && me === 0) return ['Nothing divides every term here.', `The terms of ${P0} share no factor except 1, so there's no GCF to pull out. Look for another way to factor.`];
      if (divides) return [`${monoText(cg, true)} is common, but not the greatest.`, `${monoText(cg, true)} goes into every term, but so does ${monoText(G, true)}. The greatest common factor takes the biggest number that divides all of them${me ? ` and the lowest power of ${XV()} (here ${XV()}${sup(me)})` : ''}: ${monoText(G, true)}.`];
      return [`${monoText(cg, true)} doesn't go into every term.`, `A common factor has to divide every term of ${P0}. ${monoText(cg, true)} doesn't, so it can't come out front. The GCF here is ${monoText(G, true)}.`];
    }
    if (op === 'tri7' && f && f.t === 'p' && card.A) {
      const got = pmul(card.A, card.B), [c0, b] = [pcoef(f.p, 0), pcoef(f.p, 1)];
      return [`${linF(card.A, true)}${linF(card.B, true)} multiplies out to ${pText(got, true)}.`,
        `Check by multiplying out: ${linF(card.A, true)}${linF(card.B, true)} = ${pText(got, true)}, not ${pText(f.p, true)}. ${fIs(f.p[2], 1) ? `You need two numbers that multiply to ${fracText(c0)} and add to ${fracText(b)}.` : 'Try splitting the middle term and grouping instead.'}`];
    }
    if (op === 'split7' && f && f.t === 'p' && pdeg(f.p) === 2) {
      const [c0, b, a] = [0, 1, 2].map(j => pcoef(f.p, j).n);
      return [`${card.u} and ${card.w} don't work: you need × = ${a * c0} and + = ${b}.`, `To split the middle term, find two numbers that multiply to a·c = ${a} · ${numText(c0)} = ${numText(a * c0)} and add to b = ${numText(b)}. ${card.u} · ${numText(card.w)} = ${numText(card.u * card.w)} and ${card.u} + ${numText(card.w)} = ${numText(card.u + card.w)}.`];
    }
    if ((op === 'dos7' || op === 'psq7') && f && f.t === 'p') {
      if (op === 'dos7') return ['That isn\'t a difference of two squares.', `a² ${MINUS} b² needs exactly two terms, both perfect squares, with a minus between them. ${pText(f.p, true)} isn't that${pdeg(f.p) === 2 && fz(pcoef(f.p, 1)) && pcoef(f.p, 0).n > 0 ? `: it's a <b>sum</b> of squares, and a sum of squares can't be factored (with real numbers)` : ''}.`];
      return ['That isn\'t a perfect square trinomial.', `a² + 2ab + b² needs the first and last terms to be squares and the middle term to be 2 · a · b. Check ${pText(f.p, true)}: it doesn't fit.`];
    }
    if (op === 'prime7') return ['It can be factored.', `"Prime" means nothing at all factors out. Here something does: ${want ? info(want).text : 'look again'}.`];
    if (op === 'grp7' || op === 'out7') return [op === 'grp7' ? 'There are no four terms to pair up yet.' : 'There\'s no shared bracket to pull out yet.', 'Grouping goes: split the middle term into two, factor each pair, then pull out the bracket they share.'];
    if (op === 'zp7') {
      if (e.k7 === 'eq' && !isZero(e.R)) return ['The zero-product rule only works when one side is 0.', `If A · B = 0, one of them must be 0. But if A · B = ${xText(e.R, true)}, there are endless ways to get it (1 · ${xText(e.R, true)}, 2 · …), so you can't split. Move everything to one side first so it equals 0.`];
      return ['The left side isn\'t a product yet.', 'Factor the left side into brackets first. Then each bracket can be set to 0.'];
    }
    if (op === 'box7') return ['Multiplying out doesn\'t help here.', e.k7 === 'eq' && isZero(e.R) && fz(e.L.k) ? 'The left side is already factored and the right side is 0: that\'s exactly what the zero-product rule needs. Multiplying out would undo the factoring.' : 'There\'s nothing here that needs multiplying out.'];
    if (op === 'sqrt7') {
      if (e.k7 === 'eq' && !isConst(e.R)) return ['Get the square alone first.', 'Square-rooting both sides only works when one side is a single square and the other is a number.'];
      if (e.k7 === 'eq') return ['Get the square alone first.', `√ both sides only works once the square is alone, like (${XV()} + 3)² = 16. A root doesn't split over + or ${MINUS}: √(${XV()}² + 9) is not ${XV()} + 3. Undo the + and ${MINUS} parts, then any number multiplying the square, first.`];
      return ['The square roots are already taken.', ''];
    }
    if (op === 'pm7') return [e.k7 === 'rt' ? 'The ± is already there.' : 'There\'s no square root yet.', 'The ± comes right after taking the square root of both sides.'];
    if (op === 'i7') return [e.k7 === 'rt' && e.rad === null ? 'There\'s no root of a negative left.' : 'There\'s no root of a negative here.', `Pull out ${XV('i')} only under a square root of a negative number: √${MINUS}9 = √9 · √${MINUS}1 = 3${XV('i')}.`];
    if (op === 'spl7') return ['Nothing to split yet.', 'Split the ± into two answers once x is alone and the ± part is a plain number.'];
    if (op === 'mv7' && card.t) {
      const t = card.t;
      const sqP = e.k7 === 'eq' && e.method === 'square' ? plainP(e.L) : null, sqH = sqP ? fMul(pcoef(sqP, 1), F(1, 2)) : null;
      if (sqP && want && want.op === 'mv7' && !want.t.e && fEq(want.t.c, fMul(sqH, sqH)) && !t.e && t.c.n > 0) {
        const p = sqP, b = pcoef(p, 1), h = sqH;
        return [`To complete the square, add (b/2)² = ${fracText(fMul(h, h))}.`, `Half of ${fracText(b)} is ${fracText(h)}, and ${fracText(h)} squared is ${fracText(fMul(h, h))}. Adding that to both sides makes the left side ${XV()}² ${pmT(b)}${XV()} + ${fracText(fMul(h, h))} = (${XV()} ${pmT(h)})², a perfect square.`];
      }
      if (want && want.op === 'mv7') {
        const w = want.t, same = w.e === t.e && fEq(fAbs(w.c), fAbs(t.c));
        if (same) return ['Wrong direction: that doubles it instead of cancelling.', `To clear ${mText({ c: fNeg(w.c), e: w.e }, true, true)} from its side, do the opposite: ${w.c.n < 0 ? 'subtract' : 'add'} ${mBody(w, true)}.`];
      }
      if (e.k7 === 'rt' && !fz(e.b)) return ['That doesn\'t cancel the number next to x.', `Undo ${pmT(e.b, true)} with its opposite.`];
      return ['That doesn\'t clear anything.', 'Adding or subtracting should cancel a term that\'s in the way.'];
    }
    if (op === 'dv7' && card.n) {
      if (want && want.op === 'mv7') return [`Undo the + and ${MINUS} first, then divide.`, `Dividing now would turn every term into a fraction. Clear the added number first; then one division finishes it.`];
      if (want && want.op === 'dv7') return [`Divide by ${fracText(want.n)}, the number multiplying it.`, `Dividing by ${fracText(card.n)} doesn't leave a 1 in front. The number multiplying is ${fracText(want.n)}.`];
      return ['There\'s nothing to divide away here.', ''];
    }
    if (op === 'fold7' && card.h) {
      const want_h = want && want.h; if (want_h === undefined) return ['It isn\'t a perfect square yet.', 'Fold into a square once the third term (b/2)² is there.'];
      const sq = PL([fMul(card.h, card.h), fMul(F(2), card.h), 1]);
      return [`(${XV()} ${pmT(card.h, true)})² is ${pText(sq, true)}.`, `Squaring a bracket gives a middle term of 2 · ${fracText(card.h)}${XV()}: (${XV()} ${pmT(card.h, true)})² = ${pText(sq, true)}. The number in the bracket is half of b: (${XV()} ${pmT(want_h, true)})².`];
    }
    if (op === 'as7' && card.n && e.k7 === 'vf') { const h = fMul(e.b, F(1, 2)); return [`Add and subtract (b/2)² = ${fracText(fMul(h, h))}.`, `Half of ${fracText(e.b)} is ${fracText(h)}; squared, ${fracText(fMul(h, h))}. Adding and subtracting it changes nothing, but makes a perfect square inside the bracket.`]; }
    if (op === 'vx7' && card.x && e.k7 === 'vf') { const h = fMul(e.b, F(1, 2)), k = fSub(e.c, fMul(h, h)); return [`In y = (x ${pmT(h)})² ${pmT(k)}, the vertex is (${fracText(fNeg(h))}, ${fracText(k)}).`, `Vertex form y = (x ${MINUS} h)² + k has its vertex at (h, k). The sign inside the bracket flips: (x ${pmT(h)})² means h = ${fracText(fNeg(h))}. The k outside keeps its sign.`]; }
    if (op === 'qf7' && card.v) {
      const t = { signb: [`The formula starts with ${MINUS}b.`, `With b = ${fracText(card.e7.b)}, ${MINUS}b = ${fracText(fNeg(card.e7.b))}. This card has b instead.`],
        'over a': ['The whole top is over 2a.', `The denominator is 2a = 2 · ${fracText(card.e7.a)} = ${fracText(fMul(F(2), card.e7.a))}, not a.`],
        sign4ac: [`Inside the root it's b² ${MINUS} 4ac.`, `4ac = 4 · ${fracText(card.e7.a)} · ${paren(card.e7.c)} = ${fracText(fMul(F(4), fMul(card.e7.a, card.e7.c)))}, and you subtract it. This card flips that sign.`],
        negb2: ['b² is never negative.', `Squaring ${paren(card.e7.b)} gives ${fracText(fMul(card.e7.b, card.e7.b))}: a negative times a negative is positive. Write (${fracText(card.e7.b)})², not ${MINUS}${fracText(fAbs(card.e7.b))}².`] }[card.v];
      if (t) return t;
      if (e.k7 === 'eq' && e.ask === 'count') return ['The question only asks how many real solutions.', `No need to solve: work out b² ${MINUS} 4ac. Its sign tells how many: positive two, zero one, negative none.`];
      return ['Get it into standard form first: ax² + bx + c = 0.', 'The formula needs a, b and c from an equation equal to 0.'];
    }
    if (op === 'dsc7') {
      const p = e.k7 === 'qf' ? PL([e.c, e.b, e.a]) : e.k7 === 'eq' ? plainP(e.L) : null;
      if (p && pdeg(p) === 2 && (e.k7 === 'qf' || (e.ask !== 'count' && isZero(e.R)))) { const D = discOf(p); return ['This asks for the solutions, not how many.', `b² ${MINUS} 4ac = ${fracText(D)} tells how many real answers there are, but the question wants the values of ${XV()}. ${e.k7 === 'qf' ? 'Work out the formula' : 'Use the formula'} to find them.`]; }
      if (p && pdeg(p) === 2 && isZero(e.R)) { const D = discOf(p); return [`b² ${MINUS} 4ac = ${fracText(D)}.`, `b² ${MINUS} 4ac = ${paren(pcoef(p, 1))}² ${MINUS} 4 · ${paren(p[2])} · ${paren(pcoef(p, 0))} = ${fracText(D)}. ${D.n > 0 ? 'Positive: two real answers (± gives two different values).' : D.n === 0 ? 'Zero: one answer (± 0 changes nothing).' : 'Negative: no real answers (no real number squares to a negative).'}`]; }
      return ['Get it into standard form first.', 'The discriminant uses a, b and c from ax² + bx + c = 0.'];
    }
    if (op === 'i27') return ['There\'s no i² to replace yet.', 'Multiply out first; i² shows up when i meets i.'];
    if (op === 'cmb7') return ['Nothing to combine yet.', 'Combine like terms once the brackets are gone: real with real, i with i.'];
    if (op === 'drop7' || op === 'neg7') return [op === 'neg7' && e.k7 === 'cx' && e.items.some(it => it.t === 'g' && it.s > 0) ? 'That bracket has a + in front.' : 'There\'s no bracket like that here.', `A + in front of a bracket: drop it. A ${MINUS} in front: flip the sign of everything inside.`];
    if (op === 'srt7') return ['It\'s already in order.', 'Standard form puts the real part first: a + bi.'];
    if (op === 'ax7' && card.h && e.k7 === 'gr') { const h = fDiv(fNeg(e.b), fMul(F(2), e.a)); return [`x = ${MINUS}b/(2a) = ${fracText(h)}.`, `a = ${fracText(e.a)} and b = ${fracText(e.b)}, so ${MINUS}b/(2a) = ${fracText(fNeg(e.b))}/${fracText(fMul(F(2), e.a))} = ${fracText(h)}. Watch the minus in front of b.`]; }
    if (op === 'dir7' && e.k7 === 'gr') return [`a = ${fracText(e.a)}: it opens ${e.a.n < 0 ? 'down, so the vertex is the highest point (a max)' : 'up, so the vertex is the lowest point (a min)'}.`, `The sign of a decides: a > 0 is a cup that opens up (lowest point at the vertex), a < 0 is a cap that opens down (highest point at the vertex).`];
    if (op === 'plg7') return ['Find the axis first.', 'The vertex is on the axis of symmetry: find x = −b/(2a), then plug it in.'];
    if (op === 'y07') return ['This question isn\'t about where y = 0.', 'Setting y = 0 finds the x-intercepts. Read what the question asks for.'];
    return null;
  }
  const isCorrect = (cur, card, target) => correct7(cur.state, card, target);
  const whyWrong = (cur, card, target) => why7(cur.state, card, target, false);
  function explain7({ state: e, card, ref }) {
    if (!e || !e.k7 || !card) return null;
    return why7(e, card, ref, true);
  }
  if (typeof registerWhy === 'function') registerWhy(explain7);

  // ================================================================ rendering
  const sym = (html, cls = '') => { const d = document.createElement('div'); d.className = 'tok a4 s7 ' + cls; d.innerHTML = html; return d; };
  const W = h => `<span class="w7">${h}</span>`;
  const owesPulse = () => difficulty.level <= 1 || isTutorial();
  function factorHtml(f, solo) {
    if (f.t === 'g4') return f.ts.map((t, i) => `<span class="pr7 ${i < 2 ? 'pa7' : 'pb7'}">${mText(t, i === 0, true)}</span>`).join(' ');
    if (f.t === 'gp') {
      const pair = (m, b, first, cls) => `<span class="pr7 ${cls}">${first ? (m.c.n < 0 ? MINUS : '') : m.c.n < 0 ? MINUS + ' ' : '+ '}${mBody({ c: m.c, e: m.e }, true) || '1'}<span class="sh7">(${pText(b, true)})</span></span>`;
      const s = pair(f.A, f.B, true, 'pa7') + ' ' + pair(f.C, f.D, false, 'pb7');
      return solo ? s : `[${s}]`;
    }
    return facText(f, true, solo);
  }
  function renderX(x, S, el) {
    const solo = soloX(x);
    const lead = leadText(x, true);
    if (lead || (!x.fs.length)) el.appendChild(TOK(W(lead || fNum(x.c, true)), 'c7', S + 'c', 'c7'));
    x.fs.forEach((f, i) => el.appendChild(TOK(W(factorHtml(f, solo)), 'f7', S + 'f' + i, 'f7' + (f.t === 'g4' || f.t === 'gp' ? ' g7' : ''))));
    if (!fz(x.k)) el.appendChild(TOK(W(kText(x.k, true, false).trim()), 'k7', S + 'k', 'k7'));
  }
  function renderEq(e, el) { renderX(e.L, 'L', el); el.appendChild(EQTOK()); renderX(e.R, 'R', el); }
  function renderRt(e, el) {
    el.appendChild(TOK(W(linText(e.a, e.b, true)), 'la7', 'La', 'la7'));
    el.appendChild(EQTOK());
    const t = TOK(W(rhsText(e, true)), 'r7', 'R', 'r7' + (!e.pm && owesPulse() ? ' owe7' : ''));
    el.appendChild(t);
  }
  function renderCs(e, el) {
    const act = e.cs.findIndex(c => !(fIs(c.a, 1) && fz(c.b)));
    e.cs.forEach((c, i) => {
      if (i) el.appendChild(sym('or', 'or7'));
      const done = fIs(c.a, 1) && fz(c.b);
      el.appendChild(TOK(W(`${linText(c.a, c.b, true)} = ${fNum(c.r, true)}`), 'cs7', 'C' + i, 'cs7' + (i === act ? ' act7' : '') + (done ? ' done7' : '')));
    });
  }
  function renderVd(e, el) {
    const say = { two: `2 real solutions`, one: `1 real solution`, none: 'No real solutions', nosol: 'No real solution' }[e.say];
    const extra = e.kind === 'count' ? `<div class="dd7">b² ${MINUS} 4ac = ${numText(e.D)} ${e.D > 0 ? '&gt;' : e.D === 0 ? '=' : '&lt;'} 0</div>` : `<div class="dd7">b² ${MINUS} 4ac = ${numText(e.D)} &lt; 0</div>`;
    el.appendChild(TOK(`<div class="from7">${e.fromHtml || e.from}</div>${extra}<div class="say7">${say}</div>`, 'vd7', 'V', 'vd7'));
  }
  function renderVf(e, el) {
    el.appendChild(sym(`${XV('y')} =`, 'lhs7'));
    const h = fMul(e.b, F(1, 2)), n = fMul(h, h);
    if (e.st === 0) { el.appendChild(TOK(W(pText(PL([e.c, e.b, 1]), true)), 'vf7', 'Vf', 'vf7')); return; }
    const inside = e.st === 1 ? `(${pText(PL([n, e.b, 1]), true)})` : `(${pText(PL([h, 1]), true)})²`;
    el.appendChild(TOK(W(inside), 'vf7', 'Vf', 'vf7'));
    const k = e.st === 3 ? kText(fSub(e.c, n), true).trim() : (kText(fNeg(n), true) + kText(e.c, true)).trim();
    if (k) el.appendChild(TOK(W(k), 'vk7', 'Vk', 'vk7'));
    if (e.vtx) el.appendChild(sym(`vertex (${fNum(e.vtx.x, true)}, ${fNum(e.vtx.y, true)})`, 'vx7t'));
  }
  function renderCx(e, el) {
    e.items.forEach((it, j) => {
      const lead = s => (j ? (s < 0 ? MINUS + '&nbsp;' : '+&nbsp;') : s < 0 ? MINUS : '');
      let html;
      if (it.t === 'g') html = `${lead(it.s)}(${zText(it.z, true)})`;
      else if (it.t === 'pr') html = `${lead(it.s || 1)}(${zText(it.A, true)})(${zText(it.B, true)})`;
      else html = iTerm(it, j === 0, true);
      el.appendChild(TOK(W(html), 'cx7', 'i' + j, 'cx7'));
    });
  }
  function renderGr(e, el) {
    const lines = [];
    if (e.dir) lines.push(`opens ${e.dir.startsWith('down') ? 'down' : 'up'}: ${e.a.n < 0 ? 'max' : 'min'}`);
    if (e.h) lines.push(`axis: ${XV()} = ${fNum(e.h, true)}`);
    if (e.k) lines.push(`vertex (${fNum(e.h, true)}, ${fNum(e.k, true)})`);
    el.appendChild(TOK(`<div>${grText(e, true)}</div>${lines.map(l => `<div class="info7">${l}</div>`).join('')}`, 'gr7', 'G', 'gr7'));
  }
  function renderFx(e, el) {
    renderX(e.L, 'L', el);
    if (e.prime) el.appendChild(sym('is prime', 'prime7t'));
  }
  // ---------------------------------------------------------------- the graph panel (stage 35)
  function graphOf(e) {
    if (e.k7 === 'gr') return { a: e.a, b: e.b, c: e.c, h: e.h, k: e.k, show: !!e.k, axis: !!e.h };
    if (e.gq) { const solved = e.k7 === 'cs' && isSolved7(e); return { ...e.gq, roots: solved ? e.cs.map(c => c.r) : null, show: solved }; }
    return null;
  }
  function drawPara(g) {
    const a = fv(g.a), b = fv(g.b), c = fv(g.c), h = -b / (2 * a), k = a * h * h + b * h + c;
    const D = b * b - 4 * a * c, roots = D >= 0 ? [(-b + Math.sqrt(D)) / (2 * a), (-b - Math.sqrt(D)) / (2 * a)] : [];
    const win = K.windowFor([F(Math.round(h)), ...roots.map(r => F(Math.round(r))), F(Math.round(h) + 2), F(Math.round(h) - 2)], [F(Math.round(k)), F(Math.round(c))]);
    const marks = [], lines = [];
    if (g.axis) lines.push({ x: g.h, dash: true, cls: 'gAx7' });
    if (g.show && g.k) marks.push({ t: 'dot', x: g.h, y: g.k, lab: `(${fracText(g.h)}, ${fracText(g.k)})`, cls: 'gV7' });
    if (g.roots) g.roots.forEach(r => marks.push({ t: 'dot', x: r, y: F(0), lab: `(${fracText(r)}, 0)`, cls: 'gR7' }));
    // Easy and Normal sketch the curve from the start (a picture to check the algebra against);
    // Hard and Expert keep it hidden until the answer is found, so it can't be read off the grid.
    const sketch = !g.show && (isTutorial() || lvl() < 2);
    K.drawGraph({ win, pts: [], lines, marks, labels: false, targets: false, qid: 'p7' + JSON.stringify([g.a, g.b, g.c]), curve7: g.show ? 2 : sketch ? 1 : 0 });
    if (!g.show && !sketch) return;
    const svg = $('graph').querySelector('svg'); if (!svg || svg.querySelector('.gPara7')) return;
    const Wd = 260, pad = 12, { x0, x1, y0, y1 } = win, span = Math.max(x1 - x0, y1 - y0), s = (Wd - 2 * pad) / span;
    const cx = (x0 + x1) / 2, cy = (y0 + y1) / 2, vx0 = cx - span / 2, vx1 = cx + span / 2, vy0 = cy - span / 2, vy1 = cy + span / 2;
    const Xs = x => (Wd / 2 + (x - cx) * s).toFixed(2), Ys = y => (Wd / 2 - (y - cy) * s).toFixed(2);
    let d = '', pen = false;
    for (let i = 0; i <= 120; i++) {
      const x = vx0 + (vx1 - vx0) * i / 120, y = a * x * x + b * x + c;
      if (y < vy0 - 2 || y > vy1 + 2) { pen = false; continue; }
      d += (pen ? 'L' : 'M') + Xs(x) + ' ' + Ys(Math.max(vy0 - 2, Math.min(vy1 + 2, y))) + ' '; pen = true;
    }
    const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
    path.setAttribute('d', d); path.setAttribute('class', 'gPara7' + (g.show ? '' : ' sk7')); path.setAttribute('pathLength', '1');
    const firstDot = svg.querySelector('.gDot'); svg.insertBefore(path, firstDot || null);
  }
  function fit7() {
    const el = $('equation'); if (!el.classList.contains('e7')) return;
    el.style.removeProperty('--eqSize');
    const base = parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--eqSize')) || 56;
    let size = Math.round(base * 0.82);
    el.style.setProperty('--eqSize', size + 'px');
    const graph = $('arena').classList.contains('g4') && innerWidth > 640;
    el.classList.add('fitting');
    for (let i = 0; i < 14; i++) {
      const availW = ($('arena').clientWidth || innerWidth) * (graph ? 0.56 : 0.94), needW = Math.max(el.scrollWidth, el.getBoundingClientRect().width);
      const f = availW && needW > availW ? availW / needW : 1;
      if (f >= 0.99) break;
      size = Math.max(12, Math.floor(size * Math.min(0.97, f)));
      el.style.setProperty('--eqSize', size + 'px');
      if (size <= 12) break;
    }
    el.classList.remove('fitting');
  }
  function render(e) {
    const el = $('equation'); if (typeof clearNotes === 'function') clearNotes();
    el.innerHTML = ''; el.classList.add('a4', 'e7');
    switch (e.k7) {
      case 'fx': renderFx(e, el); break;
      case 'eq': renderEq(e, el); break;
      case 'rt': renderRt(e, el); break;
      case 'qf': el.appendChild(TOK(W(qfText(e, true)), 'qf7', 'Q', 'qf7')); break;
      case 'cs': renderCs(e, el); break;
      case 'vd': renderVd(e, el); break;
      case 'vf': renderVf(e, el); break;
      case 'cx': renderCx(e, el); break;
      case 'gr': renderGr(e, el); break;
    }
    const g = graphOf(e);
    if (g) drawPara(g);
    fit7();
  }
  function clear() {
    const el = $('equation'); if (el) el.classList.remove('e7');
    document.querySelectorAll('.fly7').forEach(n => n.remove());
  }
  const fontPx = () => parseFloat(getComputedStyle($('equation')).fontSize);
  function prefit(s, ns) {
    render(ns); const after = fontPx(); render(s); const before = fontPx();
    if (before > after + 0.5) { const el = $('equation'), c = parseFloat(el.style.getPropertyValue('--eqSize')) || 56; el.style.setProperty('--eqSize', Math.floor(c * after / before) + 'px'); }
  }
  addEventListener('resize', () => { if (!cur || !cur.act7 || (typeof animating !== 'undefined' && animating)) return; fit7(); });

  // ================================================================ prompts
  const PR = {
    gcf: ['Factor out the greatest common factor.', 'Factor completely.', 'Factor out the GCF.'],
    factor: ['Factor completely.', 'Factor.', 'Factor the expression completely.'],
    zfac: ['Solve by factoring.', 'Solve.', 'Find all solutions.', 'Solve the equation.'],
    root: ['Solve.', 'Solve by taking square roots.', 'Find all solutions.'],
    rootc: ['Solve. Write complex answers in a + bi form.', 'Find all solutions, real or complex.'],
    square: ['Solve by completing the square.', 'Complete the square to solve.'],
    formula: ['Use the quadratic formula to solve.', 'Solve using the quadratic formula.', 'Solve with the quadratic formula.'],
    formulac: ['Solve with the quadratic formula. Write complex answers in a + bi form.', 'Use the quadratic formula. Give answers in a + bi form.'],
    count: ['How many real solutions does it have?', 'Use the discriminant to find the number of real solutions.', 'Find the discriminant. How many real solutions?'],
    cx: ['Simplify. Write the answer in a + bi form.', 'Simplify.', 'Write in standard form a + bi.'],
    vertex: ['Find the vertex of the parabola.', 'Find the vertex.', 'What is the vertex of the graph?'],
    axis: ['Find the axis of symmetry.', 'Find the axis of symmetry of the parabola.'],
    max: ['Does it have a maximum or a minimum? Find it.', 'Find the maximum or minimum value.'],
    roots: ['Find the x-intercepts.', 'Find the zeros of the function.', 'Where does the graph cross the x-axis?'],
    vf: ['Write in vertex form.', 'Complete the square to write it in vertex form.'],
    vfv: ['Write in vertex form and give the vertex.', 'Complete the square. What is the vertex?'],
  };
  const lastPr = {};
  function promptKey(s) {
    switch (s.k7) {
      case 'fx': return s.skill === 'gcf7' ? 'gcf' : 'factor';
      case 'eq': return s.ask === 'count' ? 'count' : s.method === 'factor' ? 'zfac' : s.method === 'root' ? (s.cplx ? 'rootc' : 'root') : s.method === 'square' ? 'square' : s.cplx ? 'formulac' : 'formula';
      case 'cx': return 'cx';
      case 'gr': return s.ask;
      case 'vf': return s.findV ? 'vfv' : 'vf';
      default: return 'factor';
    }
  }
  function prompt(s) {
    const key = promptKey(s), all = PR[key];
    const fresh = all.filter(t => t !== lastPr[key]);
    return (lastPr[key] = pick(fresh.length ? fresh : all));
  }

  // ================================================================ animations
  // The game's timing: what's written fades in fast, hold() (scaled by the speed setting), the change
  // runs fast (quick()), the result shows, hold(). Each operation has its own motion.
  const tk = ref => $('equation').querySelector(`.tok[data-ref="${ref}"]`);
  const toks = refs => refs.map(tk).filter(Boolean);
  const allToks = pre => [...$('equation').querySelectorAll('.tok[data-ref]')].filter(t => !pre || t.dataset.ref.startsWith(pre));
  const popRefs = refs => refs.forEach(r => kickClass(tk(r), 'pop'));
  async function result(ns, refs, cap) { render(ns); (refs === '*' ? allToks() : toks(refs)).forEach(t => kickClass(t, 'pop')); if (cap) caption(cap); await quick(300); await hold(); }
  async function written(html, anchors, cap, cls = 'lift4', opts = {}) {
    if (cap) caption(cap);
    const n = note(html, anchors.filter(Boolean), opts); n.classList.add(...cls.split(' '), 'n7');
    await quick(150); await hold();
    return n;
  }
  function fly(html, from, toEl, ms = 480) {
    if (!from || !toEl) return quick(1);
    const a = from.getBoundingClientRect ? from.getBoundingClientRect() : from, dest = toEl.getBoundingClientRect();
    const chip = document.createElement('div'); chip.className = 'fly4 fly7'; chip.innerHTML = html;
    chip.style.left = (a.left + a.width / 2) + 'px'; chip.style.top = (a.top + a.height / 2) + 'px';
    document.body.appendChild(chip); void chip.offsetWidth;
    chip.style.transform = `translate(${dest.left + dest.width / 2 - a.left - a.width / 2}px, ${dest.top + dest.height / 2 - a.top - a.height / 2}px)`;
    return quick(ms).then(() => chip.remove());
  }
  const slotAt = (s, c, ref) => slotFor(s, c, ref) || movesOf(s).find(o => o.op === c.op && o.ok(c));
  const facAt = (s, c, ref) => { const sl = slotAt(s, c, ref); const r = sl.refs[0]; const x = s.L; return { r, i: +r.slice(2), f: x.fs[+r.slice(2)], x }; };

  // ---------------------------------------------------------------- stages 27 to 29: factoring
  async function animGcf(c, s, ns, ref) {
    const { r, f } = facAt(s, c, ref), t = tk(r), g = c.g, G = monoText(g, true);
    mark([t], 'hot7');
    const parts = pTerms(f.p).map(tm => `${mText(tm, true, true)} = ${G} · ${mText({ c: fDiv(tm.c, g.c), e: tm.e - g.e }, true, true) || '1'}`).join(', &nbsp;');
    const n = await written(parts, [t], `${G} goes into every term: write each term as ${G} times what's left`);
    await fly(G, t, tk('Lc') || t, 420);
    dropNote(n);
    await result(ns, ['Lc', r], `The GCF ${monoText(g)} lifts out in front of new brackets`);
  }
  async function animTri(c, s, ns, ref) {
    const { r, f } = facAt(s, c, ref), t = tk(r);
    mark([t], 'hot7');
    const [c0, b, a] = [0, 1, 2].map(j => pcoef(f.p, j));
    const p = fIs(a, 1) ? [c.A[0], c.B[0]] : null;
    const html = p ? `${fracText(p[0])} × ${paren(p[1])} = ${fracText(c0)} &nbsp; ${fracText(p[0])} + ${paren(p[1])} = ${fracText(b)}` : `${linF(c.A, true)}${linF(c.B, true)} → ${pText(pmul(c.A, c.B), true)}`;
    const n = await written(html, [t], p ? `Two numbers that multiply to ${fracText(c0)} and add to ${fracText(b)}: ${fracText(p[0])} and ${fracText(p[1])}` : 'Check: the brackets multiply back out to the trinomial');
    dropNote(n);
    t.classList.add('fold7'); await quick(380);
    await result(ns, [r, 'Lf' + (+r.slice(2) + 1)], `The terms fold into two brackets: ${xText(ns.L)}`);
  }
  async function animSplit(c, s, ns, ref) {
    const { r, f } = facAt(s, c, ref), t = tk(r), [c0, b, a] = [0, 1, 2].map(j => pcoef(f.p, j).n);
    mark([t], 'hot7');
    const n = await written(`${c.u} × ${paren(F(c.w))} = ${a * c0} = a·c &nbsp; ${c.u} + ${paren(F(c.w))} = ${b}`, [t], `Find two numbers that multiply to a·c = ${a * c0} and add to b = ${b}`);
    dropNote(n);
    await result(ns, [r], `Split the middle term: ${mText({ c: F(b), e: 1 }, true)} = ${mText({ c: F(c.u), e: 1 }, true)} ${mText({ c: F(c.w), e: 1 }, false)}`);
  }
  async function animGrp(c, s, ns, ref) {
    const { r, f } = facAt(s, c, ref), t = tk(r), ts = f.ts, nf = ns.L.fs[+r.slice(2)];
    const pa = t.querySelectorAll('.pa7'), pb = t.querySelectorAll('.pb7');
    pa.forEach(x => x.classList.add('hl7a')); caption(`First pair: ${mText(ts[0], true)} ${mText(ts[1], false)} → pull out ${monoText(nf.A)}`); await quick(150); await hold();
    pb.forEach(x => x.classList.add('hl7b')); caption(`Second pair: ${mText(ts[2], true)} ${mText(ts[3], false)} → pull out ${monoText(nf.C)}`); await quick(150); await hold();
    await result(ns, [r], `Both pairs now share the bracket (${pText(nf.B)})`);
  }
  async function animOut(c, s, ns, ref) {
    const { r, f } = facAt(s, c, ref), t = tk(r);
    t.querySelectorAll('.sh7').forEach(x => x.classList.add('hl7a'));
    caption(`Both parts have (${pText(f.B)}): pull it out, and what's left, ${monoText(f.A)} and ${monoText(f.C)}, goes in the other bracket`);
    await quick(150); await hold();
    const other = t.querySelectorAll('.sh7')[1]; if (other) { other.classList.add('gone7'); await quick(300); }
    await result(ns, [r, 'Lf' + (+r.slice(2) + 1)], `${facText(f, false, true)} = ${xText(ns.L)}`);
  }
  async function animDos(c, s, ns, ref) {
    const { r, f } = facAt(s, c, ref), t = tk(r), a = isqrt(f.p[2].n), b = isqrt(f.p[0].n);
    mark([t], 'hot7');
    const aT = a === 1 ? 'x' : a + 'x';
    const n = await written(`(${aT})² ${MINUS} (${b})² &nbsp;→&nbsp; a = ${aT}, b = ${b}`, [t], `Two squares with a minus between: ${pText(f.p)} = (${aT})² ${MINUS} ${b}²`);
    dropNote(n);
    t.classList.add('tiles7'); await quick(400);
    await result(ns, [r, 'Lf' + (+r.slice(2) + 1)], `a² ${MINUS} b² = (a + b)(a ${MINUS} b): ${xText(ns.L)}`);
  }
  async function animPsq(c, s, ns, ref) {
    const { r, f } = facAt(s, c, ref), t = tk(r), base = psqBase(f.p), a = base[1].n, b = base[0];
    mark([t], 'hot7');
    const aT = a === 1 ? 'x' : a + 'x';
    const n = await written(`a = ${aT}, b = ${fracText(fAbs(b))}: 2ab = ${mText({ c: fMul(F(2 * a), fAbs(b)), e: 1 }, true)} ✓`, [t], 'First and last terms are squares, and the middle term is 2 · a · b');
    dropNote(n);
    t.classList.add('tiles7'); await quick(400);
    await result(ns, [r], `${pText(f.p)} = (${pText(base)})²`);
  }
  async function animPrime(c, s, ns) {
    const t = allToks('L');
    mark(t, 'hot7');
    const p = s.L.fs[0].p, [c0, b] = [pcoef(p, 0), pcoef(p, 1)];
    caption(`No common factor${pdeg(p) === 2 ? fz(b) && c0.n > 0 ? ', and a sum of squares never factors' : `, and no two whole numbers multiply to ${fracText(fMul(c0, p[2]))} and add to ${fracText(b)}` : ''}`);
    await quick(150); await hold();
    await result(ns, '*', `${xText(s.L)} is prime: it can't be factored`);
  }
  // ---------------------------------------------------------------- stage 30
  async function animZp(c, s, ns) {
    const t = allToks('L');
    mark(t, 'hot7');
    caption('A product is 0 only when one of its factors is 0, so each factor gets its own equation');
    await quick(150); await hold();
    t.forEach(x => x.classList.add('clone7')); await quick(350);
    await result(ns, '*', `${zeroFactors(s.L).map(p => pText(p) + ' = 0').join(' or ')}`);
  }
  async function animBox(c, s, ns, ref) {
    if (s.k7 === 'cx') {
      const sl = slotAt(s, c, ref), it = s.items[+sl.refs[0].slice(1)], t = tk(sl.refs[0]);
      mark([t], 'hot7');
      const ts = [];
      it.A.forEach((a, j) => it.B.forEach((b, k) => { if (!fz(a) && !fz(b)) ts.push(`${zText(j ? [F(0), a] : [a, F(0)], true)} · ${zText(k ? [F(0), b] : [b, F(0)], true)}`); }));
      const n = await written(ts.join(', &nbsp;'), [t], 'Multiply every part by every part, like (a + b)(c + d)');
      dropNote(n);
      return result(ns, '*', `= ${cxText(ns)}`);
    }
    const t = allToks('L');
    mark(t, 'hot7');
    const n = await written(`${xText({ ...s.L, k: F(0) }, true)} = ${pText(prodPoly(s.L), true)}`, t, 'Multiply out: every term of one bracket times every term of the other');
    dropNote(n);
    await result(ns, ['Lf0'], `${xText(s.L)} = ${xText(ns.L)}`);
  }
  async function animCmb(c, s, ns, ref) {
    if (s.k7 === 'cx') {
      const sl = slotAt(s, c, ref), its = sl.refs.map(r => s.items[+r.slice(1)]), ts = toks(sl.refs);
      mark(ts, 'hot7');
      const sum = its.reduce((a, it) => fAdd(a, it.c), F(0));
      const n = await written(`${its.map((it, j) => iTerm(it, j === 0, true)).join(' ')} = ${fz(sum) ? '0' : iTerm({ c: sum, e: its[0].e }, true, true)}`, ts, its[0].e === 0 ? 'Real parts together' : its[0].e === 1 ? `${XV('i')} terms together` : `${XV('i')}² terms together`);
      dropNote(n);
      return result(ns, '*', `= ${cxText(ns)}`);
    }
    if (s.k7 === 'vf') {
      const h = fMul(s.b, F(1, 2)), n0 = fMul(h, h), t = tk('Vk');
      mark([t], 'hot7');
      const n = await written(`${fracText(fNeg(n0))} ${pmT(s.c)} = ${fracText(fSub(s.c, n0))}`, [t], 'Combine the numbers outside the square');
      dropNote(n);
      return result(ns, ['Vk'], vfText(ns));
    }
    const t = allToks('L');
    mark(t, 'hot7');
    const p = s.L.fs[0].p, k0 = pcoef(p, 0), sum = fAdd(k0, s.L.k);
    const n = await written(`${fracText(k0)} ${pmT(s.L.k)} = ${fracText(sum)}`, [tk('Lk'), tk('Lf0')], 'Combine the numbers');
    dropNote(n);
    await result(ns, ['Lf0'], `${xText(s.L)} = ${xText(ns.L)}`);
  }
  // ⇔ moves: written under both sides
  const sideToks = side => allToks(side);
  async function animMv(c, s, ns) {
    const t = c.t, html = `${t.c.n < 0 ? MINUS : '+'} ${mBody({ c: t.c, e: t.e }, true)}`;
    if (s.k7 === 'eq' && s.method === 'square' && plainP(s.L) && fz(pcoef(plainP(s.L), 0)) && t.c.n > 0 && !t.e) return animTiles(s, ns, t.c);
    const groups = s.k7 === 'eq' ? [sideToks('L'), sideToks('R')] : s.k7 === 'rt' ? [[tk('La')], [tk('R')]] : (() => { const i = s.cs.findIndex(x => !(fIs(x.a, 1) && fz(x.b))); return [[tk('C' + i)]]; })();
    const ns1 = groups.map(g => note(html, g));
    ns1.forEach(n => n.classList.add('lift4', 'n7'));
    caption(`${t.c.n < 0 ? 'Subtract' : 'Add'} ${mBody({ c: t.c, e: t.e })} ${t.c.n < 0 ? 'from' : 'to'} both sides`);
    await quick(150); await hold();
    ns1.forEach(dropNote);
    await result(ns, '*', ns.k7 === 'eq' ? eqText(ns) : ns.k7 === 'rt' ? `${linText(ns.a, ns.b)} = ${rhsText(ns)}` : csText(ns));
  }
  async function animDv(c, s, ns) {
    const groups = s.k7 === 'eq' ? [sideToks('L'), sideToks('R')] : s.k7 === 'rt' ? [[tk('La')], [tk('R')]] : (() => { const i = s.cs.findIndex(x => !(fIs(x.a, 1) && fz(x.b))); return [[tk('C' + i)]]; })();
    const ns1 = groups.map(g => note(fracText(c.n), g, { bar: true }));
    ns1.forEach(n => n.classList.add('lift4', 'n7'));
    caption(`Divide both sides by ${fracText(c.n)}`);
    await quick(150); await hold();
    ns1.forEach(dropNote);
    await result(ns, '*', ns.k7 === 'eq' ? eqText(ns) : ns.k7 === 'rt' ? `${linText(ns.a, ns.b)} = ${rhsText(ns)}` : csText(ns));
  }
  // ---------------------------------------------------------------- stage 31: roots and the owed ±
  async function animSqrt(c, s, ns) {
    const L = sideToks('L'), R = sideToks('R');
    [...L, ...R].forEach(t => t.classList.add('rooted7'));
    caption('√ both sides: the root undoes the square on the left');
    await quick(200); await hold();
    await result(ns, '*', `${linText(ns.a, ns.b)} = √${ns.rad}  …and a root always has two signs`);
  }
  async function animPm(c, s, ns) {
    const t = tk('R'); t.classList.remove('owe7');
    const chip = document.createElement('span'); chip.className = 'pm7c'; chip.textContent = '±';
    t.querySelector('.w7').prepend(chip); kickClass(chip, 'pop');
    const r = s.rad >= 0 && isSq(s.rad) ? String(isqrt(s.rad)) : s.rad >= 0 ? `√${s.rad}` : `√(${fNum(F(s.rad))})`;
    caption(s.rad >= 0 ? `Both ${r} and ${MINUS}${r} square to ${s.rad}: the answer splits into + and ${MINUS}`
      : `A square root has two signs, + and ${MINUS}: the answer splits into + ${r} and ${MINUS} ${r}`);
    await quick(200); await hold();
    if (s.rad >= 0 && isSq(s.rad)) { const n = await written(`√${s.rad} = ${isqrt(s.rad)}`, [t], `${isqrt(s.rad)}² = ${s.rad}`); dropNote(n); }
    await result(ns, ['R'], `${linText(ns.a, ns.b)} = ${rhsText(ns)}`);
  }
  async function animI(c, s, ns) {
    const t = tk('R'), m = -s.rad;
    mark([t], 'hot7');
    const n = await written(`√${MINUS}${m} = √${m} · √${MINUS}1 = ${isSq(m) ? isqrt(m) : '√' + m}${XV('i')}`, [t], `√${MINUS}1 is called ${XV('i')}: pull it out of the root`);
    const sp = document.createElement('span'); sp.className = 'spark7'; sp.innerHTML = XV('i'); t.appendChild(sp);
    await quick(500); sp.remove(); dropNote(n);
    await result(ns, ['R'], `${s.k7 === 'rt' ? linText(ns.a, ns.b) : 'x'} = ${rhsText(ns)}`);
  }
  async function animSpl(c, s, ns) {
    const t = tk('R');
    mark([t], 'hot7');
    const plus = fAdd(s.q, s.s), minus = fSub(s.q, s.s);
    const n = await written(`+ : ${fracText(s.q)} + ${fracText(s.s)} = ${fracText(plus)} &nbsp; ${MINUS} : ${fracText(s.q)} ${MINUS} ${fracText(s.s)} = ${fracText(minus)}`, [t], 'Work out the + answer and the − answer');
    dropNote(n);
    await result(ns, '*', csText(ns));
  }
  // ---------------------------------------------------------------- stage 32: completing the square with tiles
  function tileSvg(h, filled) {
    const hv = Math.abs(fv(h)), bw = 38, sw = Math.max(10, Math.min(30, 38 * hv / 4));
    const x = bw, w = bw + sw;
    return `<svg class="tile7" viewBox="-2 -2 ${w + 4} ${w + 4}" width="${(w + 4) * 1.6}" height="${(w + 4) * 1.6}">
      <rect x="0" y="0" width="${bw}" height="${bw}" class="tx7"/><text x="${bw / 2}" y="${bw / 2 + 4}">x²</text>
      <rect x="${x}" y="0" width="${sw}" height="${bw}" class="tb7"/><rect x="0" y="${x}" width="${bw}" height="${sw}" class="tb7"/>
      <rect x="${x}" y="${x}" width="${sw}" height="${sw}" class="${filled ? 'tc7 in' : 'tc7'}"/>
      ${filled ? `<text x="${x + sw / 2}" y="${x + sw / 2 + 3}" class="tct7">${fracText(fMul(h, h))}</text>` : ''}</svg>`;
  }
  async function animTiles(s, ns, n) {
    const p = plainP(s.L), b = pcoef(p, 1), h = fMul(b, F(1, 2));
    const L = sideToks('L');
    const nt = await written(tileSvg(h, false), L, `${XV()}² ${pmT(b)}${XV()} is a square with two strips of ${fracText(fAbs(h))}: the corner is missing`, 'lift4 tilen7');
    await quick(200);
    nt.innerHTML = tileSvg(h, true);
    caption(`The missing corner is (b/2)² = ${fracText(h)}² = ${fracText(n)}: add it to both sides`);
    await hold();
    dropNote(nt);
    const R = sideToks('R'), a = note(`+ ${fracText(n)}`, R); a.classList.add('lift4', 'n7');
    await quick(150); await hold(); dropNote(a);
    await result(ns, '*', eqText(ns));
  }
  async function animFold(c, s, ns) {
    const t = tk(s.k7 === 'vf' ? 'Vf' : 'Lf0'), h = c.h;
    mark([t], 'hot7');
    const n = await written(`(${XV()} ${pmT(h, true)})² = ${XV()}² ${pmT(fMul(F(2), h), true)}${XV()} + ${fNum(fMul(h, h), true)}`, [t], 'A perfect square: fold it into one squared bracket, with half of b inside');
    dropNote(n);
    await result(ns, [s.k7 === 'vf' ? 'Vf' : 'Lf0'], s.k7 === 'vf' ? vfText(ns) : eqText(ns));
  }
  async function animAs(c, s, ns) {
    const t = tk('Vf'), h = fMul(s.b, F(1, 2));
    const nt = await written(tileSvg(h, false), [t], `${XV()}² ${pmT(s.b)}${XV()}: a square missing its corner`, 'lift4 tilen7');
    await quick(200); nt.innerHTML = tileSvg(h, true);
    caption(`Add the corner, ${fracText(c.n)}, and subtract it again so nothing changes`);
    await hold(); dropNote(nt);
    await result(ns, ['Vf', 'Vk'], vfText(ns));
  }
  async function animVx(c, s, ns) {
    const t = tk('Vf'), h = fMul(s.b, F(1, 2));
    mark([t, tk('Vk')], 'hot7');
    const n = await written(`(${XV()} ${MINUS} h)² + k: h = ${fracText(fNeg(h))}, k = ${fracText(fSub(s.c, fMul(h, h)))}`, [t, tk('Vk')], 'Vertex form y = (x − h)² + k: the vertex is (h, k), and the sign in the bracket flips');
    dropNote(n);
    await result(ns, '*', `vertex (${fracText(c.x)}, ${fracText(c.y)})`);
  }
  // ---------------------------------------------------------------- stage 33: the formula and the discriminant
  async function animQf(c, s, ns) {
    const L = sideToks('L'), ab = c.e7;
    const n = await written(`a = ${fracText(ab.a)}, b = ${fracText(ab.b)}, c = ${fracText(ab.c)}`, L, `Read a, b and c from ${pText(plainP(s.L))} = 0`);
    render(ns);
    const q = tk('Q'); dropNote(n);
    await Promise.all([fly(`a = ${fracText(ab.a)}`, L[0] || q, q, 520), fly(`b = ${fracText(ab.b)}`, L[0] || q, q, 600), fly(`c = ${fracText(ab.c)}`, L[0] || q, q, 680)]);
    await result(ns, ['Q'], 'x = (−b ± √(b² − 4ac)) / (2a), with the numbers in');
  }
  async function animDsc(c, s, ns) {
    const p = s.k7 === 'qf' ? PL([s.c, s.b, s.a]) : plainP(s.L), D = discOf(p);
    const t = s.k7 === 'qf' ? [tk('Q')] : sideToks('L');
    mark(t, 'hot7');
    const n = await written(`b² ${MINUS} 4ac = ${paren(pcoef(p, 1))}² ${MINUS} 4 · ${paren(p[2])} · ${paren(pcoef(p, 0))} = ${fracText(D)}`, t, `The discriminant b² − 4ac: ${D.n > 0 ? 'positive, so 2 answers' : D.n === 0 ? 'zero, so 1 answer' : 'negative, so no real answers'}`);
    dropNote(n);
    await result(ns, '*', ns.k7 === 'rt' ? `x = ${rhsText(ns)}` : ns.k7 === 'cs' ? csText(ns) : vdSay(ns));
  }
  // ---------------------------------------------------------------- stage 34: i
  async function animI2(c, s, ns, ref) {
    const sl = slotAt(s, c, ref), t = tk(sl.refs[0]), it = s.items[+sl.refs[0].slice(1)];
    mark([t], 'hot7');
    const n = await written(`${XV('i')}² = ${MINUS}1`, [t], `${iTerm(it, true)} = ${fracText(it.c)} · (${MINUS}1) = ${fracText(fNeg(it.c))}`);
    t.querySelector('.w7').classList.add('flip7'); await quick(350); dropNote(n);
    await result(ns, [sl.refs[0]], `= ${cxText(ns)}`);
  }
  async function animDrop(c, s, ns, ref) {
    const sl = slotAt(s, c, ref), t = tk(sl.refs[0]);
    mark([t], 'hot7');
    caption(c.op === 'neg7' ? `A minus in front: ${MINUS}1 times both parts, so both signs flip` : 'A + in front: the brackets just go away');
    await quick(150); await hold();
    await result(ns, '*', `= ${cxText(ns)}`);
  }
  async function animSrt(c, s, ns) {
    const ts = allToks('i');
    caption('Standard form a + bi: real part first');
    const [a, b] = ts.map(x => x.getBoundingClientRect());
    if (a && b) { ts[0].style.transition = ts[1].style.transition = `transform calc(.45s * var(--k))`; ts[0].style.transform = `translateX(${b.left - a.left}px)`; ts[1].style.transform = `translateX(${a.left - b.left}px)`; }
    await quick(500); await hold();
    await result(ns, '*', `= ${cxText(ns)}`);
  }
  // ---------------------------------------------------------------- stage 35: graphs
  async function animAx(c, s, ns) {
    const t = tk('G');
    mark([t], 'hot7');
    const n = await written(`${XV()} = ${MINUS}b / (2a) = ${fracText(fNeg(s.b))} / ${fracText(fMul(F(2), s.a))} = ${fracText(c.h)}`, [t], 'The axis of symmetry runs through the vertex: x = −b/(2a)');
    dropNote(n);
    await result(ns, ['G'], `axis of symmetry: x = ${fracText(c.h)}`);
  }
  async function animPlg(c, s, ns) {
    const t = tk('G'), h = s.h;
    mark([t], 'hot7');
    const n = await written(`${XV('y')} = ${fracText(s.a)}(${fracText(h)})² ${pmT(s.b)}(${fracText(h)}) ${pmT(s.c)} = ${fracText(ns.k)}`, [t], 'Plug the axis x into the rule: that gives the vertex height');
    dropNote(n);
    await result(ns, ['G'], `vertex (${fracText(h)}, ${fracText(ns.k)}): the parabola draws through it, like an arrow's arc`);
  }
  async function animDir(c, s, ns) {
    const t = tk('G');
    mark([t], 'hot7');
    const n = await written(`a = ${fracText(s.a)} ${s.a.n < 0 ? '&lt;' : '&gt;'} 0`, [t], s.a.n < 0 ? 'a is negative: the parabola opens down like a cap, so the vertex is its highest point' : 'a is positive: the parabola opens up like a cup, so the vertex is its lowest point');
    dropNote(n);
    await result(ns, ['G'], s.a.n < 0 ? 'Opens down: a maximum' : 'Opens up: a minimum');
  }
  async function animY0(c, s, ns) {
    const t = tk('G');
    mark([t], 'hot7');
    const n = await written(`${XV('y')} → 0`, [t], 'On the x-axis, y = 0: set the rule equal to 0 and solve');
    dropNote(n);
    await result(ns, '*', eqText(ns));
  }
  function animFor(card) {
    return async (c, s, ns, ref) => {
      switch (c.op) {
        case 'gcf7': return animGcf(c, s, ns, ref);
        case 'tri7': return animTri(c, s, ns, ref);
        case 'split7': return animSplit(c, s, ns, ref);
        case 'grp7': return animGrp(c, s, ns, ref);
        case 'out7': return animOut(c, s, ns, ref);
        case 'dos7': return animDos(c, s, ns, ref);
        case 'psq7': return animPsq(c, s, ns, ref);
        case 'prime7': return animPrime(c, s, ns, ref);
        case 'zp7': return animZp(c, s, ns, ref);
        case 'box7': return animBox(c, s, ns, ref);
        case 'cmb7': return animCmb(c, s, ns, ref);
        case 'mv7': return animMv(c, s, ns, ref);
        case 'dv7': return animDv(c, s, ns, ref);
        case 'sqrt7': return animSqrt(c, s, ns, ref);
        case 'pm7': return animPm(c, s, ns, ref);
        case 'i7': return animI(c, s, ns, ref);
        case 'spl7': return animSpl(c, s, ns, ref);
        case 'fold7': return animFold(c, s, ns, ref);
        case 'as7': return animAs(c, s, ns, ref);
        case 'vx7': return animVx(c, s, ns, ref);
        case 'qf7': return animQf(c, s, ns, ref);
        case 'dsc7': return animDsc(c, s, ns, ref);
        case 'i27': return animI2(c, s, ns, ref);
        case 'drop7': case 'neg7': return animDrop(c, s, ns, ref);
        case 'srt7': return animSrt(c, s, ns, ref);
        case 'ax7': return animAx(c, s, ns, ref);
        case 'plg7': return animPlg(c, s, ns, ref);
        case 'dir7': return animDir(c, s, ns, ref);
        case 'y07': return animY0(c, s, ns, ref);
      }
    };
  }

  // ================================================================ generators
  // Every case comes up at every level; the level changes how hard it is to do: bigger numbers, a
  // number in front, an extra step (a GCF first, terms on the wrong side).
  const RMAX = [6, 9, 12, 15];
  const nz = (L, max = RMAX) => nonZero(-max[L], max[L]);
  const posR = (L, max = RMAX) => rand(1, max[L]);
  const expand = (...ps) => ps.reduce((a, p) => pmul(a, PL(p)), [F(1)]).map(c => c.n);   // ints, low→high
  const primeQuad = (L, o = {}) => {
    for (let n = 0; n < 300; n++) {
      const a = o.a || rand(1, L >= 2 ? 3 : 1), b = o.noB ? 0 : nonZero(-6 - L * 2, 6 + L * 2), c = nonZero(o.posC ? 1 : -9, 9 + L * 2);
      if (!trinomPair(a, b, c) && gcd(gcd(a, b), c) === 1 && (o.posC ? c > 0 : true)) return [c, b, a];
    }
    return [5, 1, 1];
  };
  const fxG = (p, skill, enemy) => ({ q7: fxState(p, { skill }), enemy });

  const GCF_CASES = ['num', 'x', 'numx', 'cube', 'neg', 'three'];
  function genGcf(cs, tut = isTutorial()) {
    const L = lvl(tut), G = [5, 8, 12, 15][L];
    for (let n = 0; n < 200; n++) {
      const g = rand(2, G), a = rand(1, L >= 2 ? 5 : 4), b = nonZero(-9 - L * 3, 9 + L * 3);
      if (gcd(a, b) !== 1) continue;
      let p;
      if (cs === 'num') p = expand([g], [b, a]);
      else if (cs === 'x') p = expand([0, 1], [b, a], L >= 3 && chance(0.4) ? [0, 1] : [1]);
      else if (cs === 'numx') p = expand([0, g], [Math.abs(b), a]);
      else if (cs === 'neg') p = expand([0, g], [-Math.abs(b), a], L >= 2 && chance(0.4) ? [0, 1] : [1]);
      else if (cs === 'cube') p = expand([0, g], primeQuad(L));
      else p = expand([g], primeQuad(L, { posC: true }));
      if (p.length < 2 || pTerms(PL(p)).length < 2 || p[p.length - 1] <= 0) continue;
      return fxG(p, 'gcf7', 'factorling');
    }
    return fxG([0, 9, 6], 'gcf7', 'factorling');
  }
  const TRI_CASES = ['pp', 'mm', 'pm', 'mp', 'a', 'aneg'];
  function genTri(cs, tut = isTutorial()) {
    const L = lvl(tut);
    for (let n = 0; n < 300; n++) {
      let A, B;
      const r = posR(L), s = posR(L);
      if (r === s) continue;
      if (cs === 'pp') { A = [r, 1]; B = [s, 1]; }
      else if (cs === 'mm') { A = [-r, 1]; B = [-s, 1]; }
      else if (cs === 'pm') { A = [Math.max(r, s), 1]; B = [-Math.min(r, s), 1]; }
      else if (cs === 'mp') { A = [-Math.max(r, s), 1]; B = [Math.min(r, s), 1]; }
      else {
        const p = rand(2, L >= 2 ? 5 : 3), q = rand(1, [5, 7, 9, 11][L]) * (cs === 'aneg' ? sgnR() : 1), s2 = rand(1, [5, 7, 9, 11][L]) * (cs === 'aneg' ? sgnR() : 1);
        if (cs === 'aneg' && q > 0 && s2 > 0) continue;
        if (gcd(p, q) !== 1) continue;
        A = [q, p]; B = [s2, rand(1, L >= 2 ? 2 : 1)];
        if (gcd(B[0], B[1]) !== 1) continue;
      }
      const p = expand(A, B);
      if (!p[1] || isDos(PL(p)) || isPsq(PL(p))) continue;
      const g = L >= 2 && chance(0.4) ? rand(2, 3) : 1;      // Hard and Expert: sometimes a GCF comes out first
      return fxG(p.map(c => c * g), 'trinom', 'pairling');
    }
    return fxG([6, 5, 1], 'trinom', 'pairling');
  }
  const PAT_CASES = ['dos', 'dosa', 'sqp', 'sqm', 'prime', 'gcfdos'];
  function genPat(cs, tut = isTutorial()) {
    const L = lvl(tut), BM = [9, 12, 15, 20][L];
    for (let n = 0; n < 200; n++) {
      const b = rand(1, BM), a = rand(2, L >= 2 ? 7 : 5);
      let p;
      if (cs === 'dos') p = [-b * b, 0, 1];
      else if (cs === 'dosa') { if (gcd(a, b) !== 1) continue; p = [-b * b, 0, a * a]; }
      else if (cs === 'sqp' || cs === 'sqm') { const aa = L >= 1 && chance(0.4) ? rand(2, 3) : 1; if (gcd(aa, b) !== 1) continue; p = expand([cs === 'sqp' ? b : -b, aa], [cs === 'sqp' ? b : -b, aa]); }
      else if (cs === 'prime') p = chance(0.6) ? [b * b, 0, 1] : primeQuad(L, { a: 1 });
      else { const g = rand(2, L >= 2 ? 7 : 5); p = chance(0.7) ? [-b * b * g, 0, g] : expand([g], [b, 1], [b, 1]); }
      if (b === 0 || (p[1] === 0 && p[0] === 0)) continue;
      return fxG(p, 'facpat', 'squarelet');
    }
    return fxG([-9, 0, 1], 'facpat', 'squarelet');
  }
  const eqG = (L, R, method, skill, enemy, o = {}) => ({ q7: eqState(L, R, method, { skill, ...o }), enemy });
  const ZP_CASES = ['fac', 'move', 'gcf', 'prod', 'a', 'given'];
  function genZp(cs, tut = isTutorial()) {
    const L = lvl(tut);
    for (let n = 0; n < 300; n++) {
      const r = nz(L), s = nz(L);
      if (r === s) continue;
      if (cs === 'fac') return eqG(Xp(PL(expand([-r, 1], [-s, 1]))), Xn(0), 'factor', 'zprod', 'zerotwin');
      if (cs === 'move') {
        const p = expand([-r, 1], [-s, 1]); if (!p[0] || !p[1]) continue;
        const keepX = L >= 2 && chance(0.5);   // Hard and up: the x-term starts on the other side too
        return keepX ? eqG(Xp(PL([0, 0, 1])), Xp(PL([-p[0], -p[1]])), 'factor', 'zprod', 'zerotwin') : eqG(Xp(PL([0, p[1], 1])), Xn(-p[0]), 'factor', 'zprod', 'zerotwin');
      }
      if (cs === 'gcf') { const a = L === 0 ? 1 : rand(1, 3), b = nz(L) * a; return eqG(Xp(PL([0, 0, a])), Xp(PL([0, b])), 'factor', 'zprod', 'zerotwin'); }
      if (cs === 'prod') {
        const d = nonZero(-3, 3), A = r + d, B = s - d, k = A * B - r * s;
        if (!k || A === 0 || B === 0 || A === B) continue;
        return eqG(X([{ t: 'p', p: PL([-A, 1]) }, { t: 'p', p: PL([-B, 1]) }]), Xn(k), 'factor', 'zprod', 'zerotwin');
      }
      if (cs === 'a') {
        const p = rand(2, L >= 2 ? 4 : 3), q = nonZero(-7, 7); if (gcd(p, q) !== 1) continue;
        const pp = expand([q, p], [-s, 1]); if (!pp[1] || isPsq(PL(pp)) || isDos(PL(pp))) continue;
        return eqG(Xp(PL(pp)), Xn(0), 'factor', 'zprod', 'zerotwin');
      }
      const p = rand(1, L >= 1 ? 3 : 2), q = nonZero(-8, 8); if (gcd(p, q) !== 1) continue;
      return eqG(X([{ t: 'p', p: PL([-r, 1]) }, { t: 'p', p: PL([q, p]) }]), Xn(0), 'factor', 'zprod', 'zerotwin');
    }
    return eqG(Xp(PL([6, -5, 1])), Xn(0), 'factor', 'zprod', 'zerotwin');
  }
  const SFREE = [2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 17, 19];
  const SQ_CASES = ['x2', 'sq', 'iso', 'irr', 'ax2', 'lin'];
  function genSq(cs, tut = isTutorial()) {
    const L = lvl(tut);
    for (let n = 0; n < 200; n++) {
      const m = rand(1, [6, 9, 12, 13][L]), h = nz(L, [5, 8, 10, 12]);
      if (cs === 'x2') return eqG(Xp(PL([0, 0, 1])), Xn(chance(0.75) ? m * m : pick(SFREE)), 'root', 'sqroot', 'rootsprite');
      if (cs === 'sq') return eqG(X([{ t: 'sq', p: PL([h, 1]) }]), Xn(m * m), 'root', 'sqroot', 'rootsprite');
      if (cs === 'irr') return eqG(X([{ t: 'sq', p: PL([h, 1]) }]), Xn(pick(SFREE.slice(0, 5 + L * 2))), 'root', 'sqroot', 'rootsprite');
      if (cs === 'iso') { const c = rand(2, L >= 2 ? 5 : 3), k = nz(L, [9, 12, 15, 20]), mm = rand(1, [4, 6, 8, 9][L]); return eqG(X([{ t: 'sq', p: PL([h, 1]) }], { c, k }), Xn(c * mm * mm + k), 'root', 'sqroot', 'rootsprite'); }
      if (cs === 'ax2') { const c = rand(2, L >= 2 ? 6 : 4), mm = rand(1, [5, 7, 9, 10][L]), toZero = chance(0.5); return toZero ? eqG(Xp(PL([-c * mm * mm, 0, c])), Xn(0), 'root', 'sqroot', 'rootsprite') : eqG(Xp(PL([0, 0, c])), Xn(c * mm * mm), 'root', 'sqroot', 'rootsprite'); }
      const a = rand(2, L >= 2 ? 5 : 3), b = nonZero(-7, 7); if (gcd(a, b) !== 1) continue;
      return eqG(X([{ t: 'sq', p: PL([b, a]) }]), Xn(m * m), 'root', 'sqroot', 'rootsprite');
    }
    return eqG(X([{ t: 'sq', p: PL([-3, 1]) }]), Xn(16), 'root', 'sqroot', 'rootsprite');
  }
  const CS_CASES = ['basic', 'move', 'lead', 'irr', 'vf', 'vfv'];
  function genCs(cs, tut = isTutorial()) {
    const L = lvl(tut);
    for (let n = 0; n < 200; n++) {
      const h = nz(L, [5, 7, 9, 12]), m = rand(1, [7, 9, 12, 14][L]), b = 2 * h;
      if (cs === 'vf' || cs === 'vfv') { const c = nz(L, [9, 12, 15, 20]); return { q7: { k7: 'vf', b: F(b), c: F(c), st: 0, findV: cs === 'vfv', vtx: null, skill: 'cmpsq', qid: qid() }, enemy: 'cornermason' }; }
      const rhs = cs === 'irr' ? pick(SFREE.slice(0, 5 + L * 2)) : m * m, c = rhs - h * h;   // (x + h)² = rhs
      if (!c || (cs !== 'irr' && m === Math.abs(h))) continue;
      if (cs === 'basic' || cs === 'irr') return eqG(Xp(PL([0, b, 1])), Xn(c), 'square', 'cmpsq', 'cornermason');
      if (cs === 'move') return eqG(Xp(PL([-c, b, 1])), Xn(0), 'square', 'cmpsq', 'cornermason');
      const a = rand(2, L >= 2 ? 4 : 3);
      return eqG(Xp(PL([0, a * b, a])), Xn(a * c), 'square', 'cmpsq', 'cornermason');
    }
    return eqG(Xp(PL([0, 6, 1])), Xn(7), 'square', 'cmpsq', 'cornermason');
  }
  const QF_CASES = ['two', 'irr', 'one', 'none', 'move', 'count'];
  function genQf(cs, tut = isTutorial()) {
    const L = lvl(tut);
    for (let n = 0; n < 400; n++) {
      let p;
      if (cs === 'two') { const a = rand(1, L >= 2 ? 3 : 2), q = nonZero(-7, 7), s = nz(L); if (gcd(a, q) !== 1) continue; p = expand([q, a], [s, 1]); }
      else if (cs === 'one') { const a = rand(1, L >= 2 ? 3 : 2), q = nonZero(-7, 7); if (gcd(a, q) !== 1) continue; p = expand([q, a], [q, a]); }
      else {
        const a = rand(1, [2, 3, 4, 5][L]), b = nonZero(-9, 9), c = nonZero(-9 - L * 3, 9 + L * 3);
        p = [c, b, a];
        const D = b * b - 4 * a * c;
        if (cs === 'none' && D >= 0) continue;
        if ((cs === 'irr' || cs === 'move') && (D <= 0 || isSq(D) || !sqfree(D))) continue;
        if (cs === 'count' && (D !== 0 && !okRad(D))) continue;
      }
      if (gcd(gcd(p[0], p[1]), p[2]) !== 1) continue;
      if (cs === 'move') { const sh = chance(0.5); return eqG(Xp(PL(sh ? [0, p[1], p[2]] : [0, 0, p[2]])), Xp(PL(sh ? [-p[0]] : [-p[0], -p[1]])), 'formula', 'qform', 'formulist'); }
      if (cs === 'count') return eqG(Xp(PL(p)), Xn(0), 'formula', 'qform', 'formulist', { ask: 'count' });
      return eqG(Xp(PL(p)), Xn(0), 'formula', 'qform', 'formulist');
    }
    return eqG(Xp(PL([-4, -3, 2])), Xn(0), 'formula', 'qform', 'formulist');
  }
  const CX_CASES = ['solve', 'add', 'sub', 'mul', 'conj', 'formula'];
  function genCx(cs, tut = isTutorial()) {
    const L = lvl(tut), M = [6, 9, 12, 15][L];
    const z = () => [F(nz(L, [M, M, M, M])), F(nz(L, [M, M, M, M]))];
    const cxG = items => ({ q7: { k7: 'cx', items, skill: 'cplx', qid: qid() }, enemy: 'imp' });
    if (cs === 'add') return cxG([{ t: 'g', s: 1, z: z() }, { t: 'g', s: 1, z: z() }]);
    if (cs === 'sub') return cxG([{ t: 'g', s: 1, z: z() }, { t: 'g', s: -1, z: z() }]);
    if (cs === 'mul') { const m = [3, 5, 7, 9][L], zz = () => [F(nonZero(-m, m)), F(nonZero(-m, m))]; return cxG([{ t: 'pr', s: 1, A: zz(), B: zz() }]); }
    if (cs === 'conj') { const a = F(nonZero(-[5, 7, 9, 9][L], [5, 7, 9, 9][L])), b = F(nonZero(-[5, 7, 9, 9][L], [5, 7, 9, 9][L])); return cxG([{ t: 'pr', s: 1, A: [a, b], B: [a, fNeg(b)] }]); }
    if (cs === 'solve') {
      const k = rand(1, [6, 8, 10, 12][L]), rad = chance(0.8) ? k * k : pick(SFREE.slice(0, 6));
      if (L >= 1 && chance(0.5)) { const h = nz(L, [5, 7, 9, 9]); return eqG(X([{ t: 'sq', p: PL([h, 1]) }]), Xn(-rad), 'root', 'cplx', 'imp', { cplx: true }); }
      return eqG(Xp(PL([rad, 0, 1])), Xn(0), 'root', 'cplx', 'imp', { cplx: true });
    }
    const h = nz(L, [5, 7, 9, 9]), k = rand(1, [5, 7, 9, 9][L]), a = L >= 2 && chance(0.4) ? 2 : 1;
    return eqG(Xp(PL([a * (h * h + k * k), -2 * a * h, a])), Xn(0), 'formula', 'cplx', 'imp', { cplx: true });
  }
  const GR_CASES = ['vertex', 'axis', 'max', 'roots', 'vneg', 'rootsa'];
  function genGr(cs, tut = isTutorial()) {
    const L = lvl(tut);
    const grG = (a, b, c, ask) => ({ q7: { k7: 'gr', a: F(a), b: F(b), c: F(c), ask, h: null, k: null, dir: null, skill: 'qgraph', qid: qid() }, enemy: 'arcer' });
    for (let n = 0; n < 200; n++) {
      if (cs === 'roots' || cs === 'rootsa') {
        const r = nz(L, [6, 7, 8, 9]), s = nz(L, [6, 7, 8, 9]); if (r === s || Math.abs(r - s) > 12) continue;
        const a = cs === 'rootsa' ? pick([-1, -1, 2, -2]) : 1, p = expand([a], [-r, 1], [-s, 1]);
        return grG(p[2], p[1], p[0], 'roots');
      }
      const a = cs === 'vneg' ? -rand(1, L >= 2 ? 3 : 2) : (cs === 'max' ? pick([1, -1, 2, -2]) : pick([1, 1, 2, -1].slice(0, L >= 1 ? 4 : 2))), h = nz(L, [5, 6, 7, 8]);
      const odd = L >= 2 && Math.abs(a) === 2 && chance(0.4);   // Hard and up: a half-step vertex
      const b = odd ? -2 * a * h + a : -2 * a * h, c = nz(L, [8, 10, 12, 15]);
      if (!b) continue;
      return grG(a, b, c, cs === 'vneg' ? 'vertex' : cs);
    }
    return grG(-1, 4, 0, 'vertex');
  }

  // ---------------------------------------------------------------- elite and boss
  function genStacked7(list) {
    const act7 = list.filter(id => (SKILL[id].act || 1) === 7), newest = act7[act7.length - 1];
    const el = g => ({ ...g, enemy: 'twinbow' });
    const L = lvl();
    switch (newest) {
      case 'qgraph': return el(genGr(pick(['max', 'rootsa', 'vneg'])));
      case 'cplx': return el(chance(0.5) ? genCx('formula') : (() => { const h = nz(L, [5, 7, 9, 9]), c = rand(2, 3), k = rand(1, 6); return eqG(X([{ t: 'sq', p: PL([h, 1]) }], { c, k: c * k * k + c }), Xn(c), 'root', 'cplx', 'twinbow', { cplx: true }); })());
      case 'qform': return el(genQf(pick(['move', 'irr'])));
      case 'cmpsq': { const g = genCs('lead'); return el(chance(0.5) ? g : genCs('irr')); }
      case 'sqroot': { const h = nz(L, [5, 8, 10, 12]), c = rand(2, 4), k = nz(L, [9, 12, 15, 20]); return el(eqG(X([{ t: 'sq', p: PL([h, 1]) }], { c, k }), Xn(c * pick(SFREE.slice(0, 6)) + k), 'root', 'sqroot', 'twinbow')); }
      case 'zprod': return el(pick([() => genZp('prod'), () => { const b = rand(1, 9), g = rand(2, 4); return eqG(Xp(PL([0, 0, g])), Xn(g * b * b), 'factor', 'zprod', 'twinbow'); }, () => genZp('gcf')])());
      case 'facpat': return el(chance(0.5) ? genPat('gcfdos') : fxG(expand([0, 1], [-(rand(1, 9) ** 2), 0, 1]), 'facpat', 'twinbow'));
      case 'trinom': { const g = rand(2, 4), r = genTri(pick(['pp', 'mm', 'pm', 'a'])); r.q7.L = Xp(pscale(plainP(r.q7.L) || xPoly(r.q7.L), F(g))); return el(r); }
      default: return el(genGcf(pick(['cube', 'three'])));
    }
  }
  const GROUPS = [['gcf7', 'trinom', 'facpat'], ['zprod', 'sqroot'], ['cmpsq', 'qform'], ['cplx'], ['qgraph']];
  function buildFight7(node, list) {
    const act7 = list.filter(id => (SKILL[id].act || 1) === 7);
    if (node.type === 'elite') return { phases: [() => genStacked7(list)], handSize: difficulty.hand, enemy: 'twinbow' };
    // Boss: one phase per group of Act 7 stages (factoring, solving, completing the square and the formula,
    // complex numbers, graphs), then a last phase that mixes the newest stages.
    const phases = GROUPS.map(g => g.filter(id => act7.includes(id))).filter(g => g.length).map(g => () => { const id = pick(g); return GENS[id](pick(SKILL[id].cases)); });
    phases.push(() => genStacked7(list));
    return { phases, handSize: difficulty.hand, enemy: 'grandarcher' };
  }
  const GENS = { gcf7: genGcf, trinom: genTri, facpat: genPat, zprod: genZp, sqroot: genSq, cmpsq: genCs, qform: genQf, cplx: genCx, qgraph: genGr };
  if (typeof ENGINES === 'object') ENGINES.q7 = { text: textOf7 };
  const applyDifficulty = g => g;   // generators read the difficulty themselves; tutorials stay on Easy

  // ================================================================ skills, enemies, act
  const ex = (...lines) => lines.join('<br>');
  SKILLS.push(
    { id: 'gcf7', stage: 27, act: 7, name: 'Greatest common factor', cases: GCF_CASES, gen: cycled('gcf7', c => genGcf(c)),
      title: 'Stage 27: Greatest common factor',
      intro: 'Factoring is multiplying out in reverse: write the expression as a product. First look for the greatest common factor (GCF): the biggest number that divides every term, and the lowest power of x they all have. Pick the GCF card and it lifts out in front of new brackets. If you pick a factor that isn\'t the greatest, there\'s still something left to pull out, so it doesn\'t count.',
      example: ex('6x² + 9x', 'Every term has a 3 and an x: GCF 3x', '→ 3x(2x + 3)'),
      tutorial: [() => genGcf('num', true), () => genGcf('numx', true)] },
    { id: 'trinom', stage: 28, act: 7, name: 'Factor trinomials', cases: TRI_CASES, gen: cycled('trinom', c => genTri(c)),
      title: 'Stage 28: Factoring trinomials',
      intro: 'x² + bx + c factors into (x + p)(x + q) when p × q = c and p + q = b. Pick the right pair: watch the signs. When there is a number in front (ax² + bx + c), factor by grouping: split the middle term into two terms whose numbers multiply to a·c and add to b, factor each pair, then pull out the bracket they share.',
      example: ex('x² + 5x + 6: 2 × 3 = 6 and 2 + 3 = 5 → (x + 2)(x + 3)', '', '2x² + 7x + 3: a·c = 6, split 7x = 6x + x', '→ 2x(x + 3) + 1(x + 3) → (2x + 1)(x + 3)'),
      tutorial: [() => genTri('pp', true), () => genTri('pm', true)] },
    { id: 'facpat', stage: 29, act: 7, name: 'Special patterns', cases: PAT_CASES, gen: cycled('facpat', c => genPat(c)),
      title: 'Stage 29: Special factoring patterns',
      intro: 'Two shapes factor on sight. Difference of squares: a² − b² = (a + b)(a − b), so x² − 9 = (x + 3)(x − 3). Perfect square: a² + 2ab + b² = (a + b)², so x² + 6x + 9 = (x + 3)². A sum of squares like x² + 9 doesn\'t factor at all: it\'s prime. Always pull out a GCF first.',
      example: ex('x² − 9 = x² − 3² → (x + 3)(x − 3)', 'x² + 6x + 9: 2 · x · 3 = 6x → (x + 3)²', 'x² + 16 → Prime'),
      tutorial: [() => genPat('dos', true), () => genPat('sqp', true)] },
    { id: 'zprod', stage: 30, act: 7, name: 'Solve by factoring', cases: ZP_CASES, gen: cycled('zprod', c => genZp(c)),
      title: 'Stage 30: Solving by factoring',
      intro: 'If two things multiply to 0, one of them must be 0. So: get everything on one side so the other side is 0, factor, then split into one small equation per factor (Zero split) and solve each. Two traps: the split only works when one side is 0, and never divide both sides by x, because that loses the answer x = 0.',
      example: ex('x² − 5x + 6 = 0', 'Factor → (x − 2)(x − 3) = 0', 'Zero split → x − 2 = 0 or x − 3 = 0', 'x = 2 or x = 3'),
      tutorial: [() => genZp('given', true), () => genZp('fac', true)] },
    { id: 'sqroot', stage: 31, act: 7, name: 'Square root both sides', cases: SQ_CASES, gen: cycled('sqroot', c => genSq(c)),
      title: 'Stage 31: Square roots of both sides',
      intro: 'When the square is alone, take the square root of both sides. Get it alone first: undo + and −, then the number in front. Rule: right after √ both sides you owe a ± on the root, because 4² and (−4)² are both 16. Then finish solving; with a whole number after the ±, split it into two answers.',
      example: ex('(x − 3)² = 16', '√ both sides → x − 3 = √16', '± → x − 3 = ±4', 'Add 3 → x = 3 ± 4', 'Split → x = 7 or x = −1'),
      tutorial: [() => genSq('x2', true), () => genSq('sq', true)] },
    { id: 'cmpsq', stage: 32, act: 7, name: 'Complete the square', cases: CS_CASES, gen: cycled('cmpsq', c => genCs(c)),
      title: 'Stage 32: Completing the square',
      intro: 'x² + 6x is a square with two strips of 3 and one corner missing. The corner is (b/2)² = 9: add it to both sides and the left side folds into (x + 3)². Then take square roots like before. First move the plain number to the right, and divide by the number in front of x². The same trick writes y = x² + 6x + 5 in vertex form: add and subtract 9 to get y = (x + 3)² − 4, vertex (−3, −4).',
      example: ex('x² + 6x = 7', 'Add (6/2)² = 9 → x² + 6x + 9 = 16', 'Fold → (x + 3)² = 16', '√, ± → x + 3 = ±4 → x = 1 or x = −7'),
      tutorial: [() => genCs('basic', true), () => genCs('vf', true)] },
    { id: 'qform', stage: 33, act: 7, name: 'Quadratic formula', cases: QF_CASES, gen: cycled('qform', c => genQf(c)),
      title: 'Stage 33: The quadratic formula',
      intro: 'Any ax² + bx + c = 0 can be solved with x = (−b ± √(b² − 4ac)) / (2a). Get it into standard form first (everything on one side, = 0), then pick the card with a, b and c plugged in right: watch −b, the 2a, and the sign of −4ac. The part under the root, b² − 4ac, is the discriminant: positive means 2 real answers, zero means 1, negative means none.',
      example: ex('2x² − 3x − 4 = 0: a = 2, b = −3, c = −4', 'x = (3 ± √(9 + 32)) / 4', 'b² − 4ac = 41 > 0: 2 answers', 'x = (3 ± √41) / 4'),
      tutorial: [() => genQf('two', true), () => genQf('irr', true)] },
    { id: 'cplx', stage: 34, act: 7, name: 'Complex numbers', cases: CX_CASES, gen: cycled('cplx', c => genCx(c)),
      title: 'Stage 34: Complex numbers',
      intro: 'No real number squares to a negative, so mathematicians named one: i = √−1, and i² = −1. Pull out i from a root of a negative: √−9 = 3i. A complex number a + bi has a real part and an imaginary part; add them like like terms. To multiply, multiply out every part, then replace i² with −1.',
      example: ex('x² + 4 = 0 → x² = −4 → x = ±√−4 → x = ±2i', '', '(3 + 2i)(1 − i) = 3 − 3i + 2i − 2i²', 'i² = −1 → 3 − 3i + 2i + 2 = 5 − i'),
      tutorial: [() => genCx('add', true), () => genCx('solve', true)] },
    { id: 'qgraph', stage: 35, act: 7, name: 'Quadratic graphs', cases: GR_CASES, gen: cycled('qgraph', c => genGr(c)),
      title: 'Stage 35: Graphs of quadratics',
      intro: 'The graph of y = ax² + bx + c is a parabola, the curve an arrow flies along. If a > 0 it opens up (a lowest point); if a < 0 it opens down (a highest point). That point is the vertex. It sits on the axis of symmetry x = −b/(2a); plug that x in to get its height. The x-intercepts are where y = 0: set y = 0 and solve.',
      example: ex('y = −x² + 4x', 'a = −1 < 0: opens down, a max', 'Axis x = −4/(2 · −1) = 2', 'y = −(2)² + 4(2) = 4 → vertex (2, 4)'),
      tutorial: [() => genGr('axis', true), () => genGr('vertex', true)] },
  );
  for (const s of SKILLS) SKILL[s.id] = s;
  progress = loadProgress();     // the save was first read before these skills existed

  Object.assign(ENEMIES, {
    factorling:  { name: 'Factorling',     rank: 'Normal', color: '#90be6d', size: 84 },
    pairling:    { name: 'Pairling',       rank: 'Normal', color: '#43aa8b', size: 84 },
    squarelet:   { name: 'Squarelet',      rank: 'Normal', color: '#f9c74f', size: 84 },
    zerotwin:    { name: 'Zero Twins',     rank: 'Normal', color: '#577590', size: 84 },
    rootsprite:  { name: 'Root Sprite',    rank: 'Normal', color: '#4d908e', size: 84 },
    cornermason: { name: 'Corner Mason',   rank: 'Normal', color: '#f8961e', size: 84 },
    formulist:   { name: 'Formulist',      rank: 'Normal', color: '#277da1', size: 84 },
    imp:         { name: 'Imp of i',       rank: 'Normal', color: '#b5179e', size: 84 },
    arcer:       { name: 'Arcer',          rank: 'Normal', color: '#f94144', size: 84 },
    twinbow:     { name: 'Twinbow',        rank: 'Elite',  color: '#9d4edd', size: 100, horns: true },
    grandarcher: { name: 'The Grand Archer', rank: 'Boss', color: '#e85d04', size: 120, crown: true },
  });
  ACTS[7] = { name: 'The Archery Gallery', sub: 'Factoring and quadratics', boss: 'The Grand Archer', firstSkill: 'gcf7',
    blurb: 'In the Archery Gallery every arrow flies on a parabola. Factor expressions, solve quadratics four ways (factoring, square roots, completing the square, the formula), meet i, and read the arcs. Defeat The Grand Archer.' };

  // svgI is the shared icon wrapper from index.html
  Object.assign(CARD_ICONS, {
    gcf7:   { name: 'Factor out the GCF', svg: svgI('<path d="M3 12h4M5 10v4" stroke-width="2"/><path d="M11 5c-3 4-3 10 0 14M21 5c3 4 3 10 0 14" transform="translate(-2 0)"/>') },
    tri7:   { name: 'Factor a trinomial into two brackets', svg: svgI('<path d="M4 5c-2 4-2 10 0 14M10 5c2 4 2 10 0 14M14 5c-2 4-2 10 0 14M20 5c2 4 2 10 0 14"/>') },
    split7: { name: 'Split the middle term (for grouping)', svg: svgI('<path d="M12 4v6M12 10l-6 10M12 10l6 10"/>') },
    grp7:   { name: 'Factor each pair', svg: svgI('<rect x="2" y="7" width="8" height="10" rx="2"/><rect x="14" y="7" width="8" height="10" rx="2"/>') },
    out7:   { name: 'Pull out the shared bracket', svg: svgI('<path d="M9 6c-3 4-3 8 0 12M15 6c3 4 3 8 0 12M12 3v4M10 5l2-2 2 2"/>') },
    dos7:   { name: 'Difference of squares', svg: svgI('<rect x="3" y="3" width="18" height="18" rx="1"/><rect x="13" y="13" width="8" height="8" stroke-dasharray="2 2"/>') },
    psq7:   { name: 'Perfect square / fold into a square', svg: svgI('<rect x="3" y="3" width="18" height="18" rx="1"/><path d="M10 3v18M3 10h18"/>') },
    prime7: { name: 'Prime: can\'t be factored', svg: svgI('<rect x="5" y="5" width="14" height="14" rx="2"/><path d="M9 12h6"/>') },
    zp7:    { name: 'Zero-product split', svg: svgI('<ellipse cx="12" cy="6" rx="3" ry="3.5"/><path d="M12 10v3M12 13l-6 7M12 13l6 7"/>') },
    sqrt7:  { name: 'Square root of both sides', svg: svgI('<path d="M2 13l3-1 3 8 4-16h10"/>') },
    pm7:    { name: '± (a root has two signs)', svg: svgI('<path d="M12 4v10M7 9h10M7 19h10"/>') },
    i7:     { name: 'i = √−1, i² = −1', svg: svgI('<circle cx="12" cy="5" r="1.6"/><path d="M12 10v10M9 20h6M9 10h3"/>') },
    spl7:   { name: 'Split ± into two answers', svg: svgI('<path d="M4 12h6M10 12l8-6M10 12l8 6"/>') },
    as7:    { name: 'Add and subtract (b/2)²', svg: svgI('<rect x="3" y="3" width="12" height="12"/><rect x="15" y="15" width="6" height="6" stroke-dasharray="2 2"/>') },
    qf7:    { name: 'Quadratic formula', svg: svgI('<path d="M3 12h18M6 8l2-4 2 4M14 4l2 4 3-6M9 18h6"/>') },
    dsc7:   { name: 'Discriminant b² − 4ac', svg: svgI('<path d="M3 8h8M7 4v8M13 18h8"/><circle cx="17" cy="9" r="3"/>') },
    ax7:    { name: 'Axis of symmetry x = −b/(2a)', svg: svgI('<path d="M4 20c2-12 14-12 16 0" /><path d="M12 3v18" stroke-dasharray="2 2"/>') },
    plg7:   { name: 'Plug in to find y', svg: svgI('<path d="M4 12h10M10 8l4 4-4 4M18 5v14"/>') },
    dir7:   { name: 'Opens up or down', svg: svgI('<path d="M4 6c2 12 14 12 16 0M12 21v-4"/>') },
    y07:    { name: 'Set y = 0 (x-intercepts)', svg: svgI('<path d="M2 14h20"/><path d="M5 4c2 16 12 16 14 0"/>') },
    vx7:    { name: 'Read the vertex', svg: svgI('<path d="M4 4c2 16 14 16 16 0"/><circle cx="12" cy="16" r="2.4"/>') },
  });

  const css = document.createElement('style');
  css.textContent = `
    #equation.e7 { flex-wrap:nowrap; gap:0; max-width:100%; align-items:center; }
    .tok.a4.f7, .tok.a4.c7, .tok.a4.k7, .tok.a4.la7, .tok.a4.r7, .tok.a4.cx7, .tok.a4.vf7, .tok.a4.vk7, .tok.a4.cs7 { padding:4px 4px; white-space:nowrap; }
    .tok.a4.c7 + .tok.a4.f7, .tok.a4.f7 + .tok.a4.f7 { margin-left:-3px; }
    .tok.a4.s7 { padding:4px 3px; min-width:0; color:var(--muted); border-color:transparent !important; background:none !important; }
    .tok.a4.s7.or7 { font-size:.55em; padding:0 6px; }
    .tok.a4.s7.prime7t, .tok.a4.s7.vx7t { font-size:.5em; color:var(--good); margin-left:.4em; }
    .w7 { display:inline-flex; align-items:center; gap:.18em; }
    .tok.a4 .xv { font-style:normal; color:var(--accent); }
    .frac.f7 { font-size:.82em; } .frac.f7 > span { padding:0 .2em; } .frac.big7 { font-size:.9em; }
    .rad7 { border-top:.07em solid currentColor; padding:0 .08em; margin-left:.02em; }
    .tok.a4.cs7.act7 { border-color:var(--accent); }
    .tok.a4.cs7.done7 { color:var(--good); }
    .tok.a4.gr7, .tok.a4.vd7 { flex-direction:column; align-items:flex-start; padding:6px 8px; white-space:nowrap; }
    .info7 { font-size:.55em; color:var(--good); line-height:1.3; }
    .from7 { font-size:.55em; color:var(--muted); } .dd7 { font-size:.5em; color:#7bdff2; } .say7 { color:var(--good); }
    .tok.ok7 { border-color: var(--good) !important; background:#06d6a022 !important; }
    .tok.a4.hot7 { background:#ffffff14; border-color:var(--accent); }
    .tok.owe7 { animation: owe7 1s ease-in-out infinite; border-color:var(--bad) !important; }
    @keyframes owe7 { 50% { box-shadow:0 0 0 4px #ef476f55; } }
    .pm7c { color:#ffd166; margin-right:.1em; display:inline-block; }
    .pr7.hl7a, .sh7.hl7a { color:#ffc46b; } .pr7.hl7b { color:#7bdff2; }
    .sh7.gone7 { opacity:.15; transition: opacity .3s; }
    .tok.fold7 { animation: fold7 .38s ease-in; } @keyframes fold7 { 50% { transform: scaleX(.85); } }
    .tok.tiles7 { animation: tiles7 .4s ease-out; } @keyframes tiles7 { 50% { transform: rotate(-4deg) scale(1.06); } }
    .tok.clone7 { animation: clone7 .35s ease-out; } @keyframes clone7 { 50% { transform: translateY(-.25em); opacity:.5; } }
    .tok.rooted7 { box-shadow: inset 0 .12em 0 #ffd166; }
    .flip7 { display:inline-block; animation: flip6x .35s ease-in-out; color:#ff9ad5; } @keyframes flip6x { 50% { transform: rotateX(90deg); } }
    .spark7 { position:absolute; right:-.2em; top:-.3em; font-size:.8em; animation: spark7 .5s ease-out forwards; pointer-events:none; }
    @keyframes spark7 { from { transform: scale(.4); opacity:1; } to { transform: translate(.6em, -.8em) scale(1.4); opacity:0; } }
    .tok.a4 { position:relative; }
    .unote.n7 { font-size:max(.42em, 14px); }
    .unote.tilen7 { font-size:max(.42em, 12px); }
    .tile7 rect { stroke:var(--muted); stroke-width:1; } .tile7 .tx7 { fill:#3a86ff55; } .tile7 .tb7 { fill:#06d6a055; }
    .tile7 .tc7 { fill:none; stroke-dasharray:3 2; } .tile7 .tc7.in { fill:#ffd16699; stroke-dasharray:none; animation: pop .3s; }
    .tile7 text { fill:var(--ink); font-size:9px; text-anchor:middle; } .tile7 .tct7 { font-size:7px; }
    .card .clong.l7 { white-space:normal; display:block; line-height:1.05; }
    .card .clong.l7 .frac.f7 { font-size:.8em; }
    .card .qfl7 { font-size:.62em; display:inline-block; }
    #graph .gPara7 { fill:none; stroke:#ffd166; stroke-width:2.5; stroke-dasharray:1; stroke-dashoffset:1; animation: para7 1s ease-out forwards; }
    #graph .gPara7.sk7 { stroke-opacity:.55; }
    .frac.f7 > span:last-child { align-self:stretch; text-align:center; }   /* the bar spans the whole numerator */
    .frac.big7 { font-size:.8em; }
    @keyframes para7 { to { stroke-dashoffset:0; } }
    #graph .gAx7 { stroke:#7bdff2; }
    @media (max-width: 640px) {
      .tok.a4.f7, .tok.a4.c7, .tok.a4.k7, .tok.a4.cx7, .tok.a4.cs7 { padding:2px 3px; }
    }
  `;
  document.head.appendChild(css);

  // Do the math: moves that only copy numbers into a new layout play as usual.
  if (typeof COPY_MOVES === 'object') ['zp7', 'y07', 'drop7', 'srt7', 'sqrt7', 'out7', 'vx7'].forEach(op => COPY_MOVES.add(op));

  window.ACT7 = { apply: apply7, isSolved: isSolved7, makeEquation: makeEquation7, refreshPath, render, prefit, clear, makeHand: makeHand7,
    isCorrect, whyWrong, animFor, applyDifficulty, label, text, kind, icon, slot: slotOf7, targetSel, onDrag, autoTarget, buildFight: buildFight7, prompt,
    gens: GENS, eqText: textOf7,
    // test hooks
    _canon: canon7, _correct: correct7, _moves: movesOf, _apply: apply7, _places: places, _answer: answerOf, _path: pathOf7, _hand: makeHand7 };
})();
