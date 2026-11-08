// =====================================================================
//  Act 8: The Root Garden (radicals and rational exponents)
// =====================================================================
// Stage 36  Simplify radicals      √50, 3√12, √(18x³), √6 · √15, √12 + √27, 3/√2, 4/(3 − √5)
// Stage 37  Rational exponents     8^(2/3), 16^(−3/4), x^(2/5) as a root, x^(1/2) · x^(1/3), x^(3/2) = 8
// Stage 38  Radical equations      √(x + 3) = x − 3, 2√(x − 1) + 3 = 9, √(x + 1) = −3, ∛(x − 2) = 3
//
// States have their own kind, `k8`:
//   rx  a radical expression: { top: [term], bot: [factor] }. A factor is k·x^xo·√(n·x^xi) with whole
//       numbers; a term is a product of factors (√6 · √15 before it is multiplied). bot is a sum of
//       factors (empty = no fraction): 3/√2 has bot [√2], 4/(3 − √5) has bot [3, −√5]. Stage 36.
//   re  a rational exponent question: ask 'eval' (a number to a fraction power, worked out one step at a
//       time: exp → root form → root → power → value), 'torad' / 'toexp' (rewrite), 'rules' (x^a · x^b,
//       (x^a)^n, x^a / x^b with fraction exponents). Stage 37.
//   eq  an equation: { L, R } sides that are nodes (lin a·x + b, rad k·ⁱ√(ax + b) + d, pw k·x^e + d, sq
//       (ax + b)², quad, fac (x − r1)(x − r2), ev a number being evaluated). Squaring both sides sets
//       `sq`, which makes the Check step owed: every answer must be checked in the original equation
//       (`orig`) and kept or rejected by the player. Stage 37 (x^(3/2) = 8) and stage 38.
// Every legal move counts; the path the game expects (par) is the canonical order. Cards that change a
// part (◎) apply by themselves when there is only one place for them.
//
// index.html switches to this engine for generators that return { rad8 } (cur.act8).
'use strict';
(function () {
  const A4 = window.ACT4;
  if (!A4 || !A4.kit) return;
  const K = A4.kit;
  const { TOK, refOf, P, kickClass, clone, fNeg, fSub, fDiv, fEq, fz, fv } = K;
  const isTutorial = K.isTutorial, lvl = K.lvl;
  const chance = p => Math.random() < p;
  const qid = () => Math.random().toString(36).slice(2, 8);
  const FN = v => (typeof v === 'number' ? F(v) : v);

  // ================================================================ numbers
  const isSq = n => n >= 0 && Math.round(Math.sqrt(n)) ** 2 === n;
  const isqrt = n => Math.round(Math.sqrt(n));
  const sqPart = n => { let best = 1; for (let s = 2; s * s <= n; s++) if (n % (s * s) === 0) best = s * s; return best; };
  function irootInt(n, q) {                       // the whole q-th root of n, or null
    if (n < 0) { if (q % 2 === 0) return null; const r = irootInt(-n, q); return r === null ? null : -r; }
    const r = Math.round(Math.pow(n, 1 / q));
    for (const c of [r - 1, r, r + 1]) if (c >= 0 && c ** q === n) return c;
    return null;
  }
  const rootF = (f, q) => { const a = irootInt(f.n, q), b = irootInt(f.d, q); return a === null || b === null ? null : F(a, b); };
  const powF = (f, p) => (p >= 0 ? F(f.n ** p, f.d ** p) : F(f.d ** -p, f.n ** -p));
  const ORD = q => (q === 2 ? 'square' : q === 3 ? 'cube' : q + 'th');
  const SUPD = '⁰¹²³⁴⁵⁶⁷⁸⁹';
  const supT = n => (n < 0 ? '⁻' : '') + String(Math.abs(n)).split('').map(d => SUPD[+d]).join('');
  const supFT = f => (f.d === 1 ? supT(f.n) : `^(${fracText(f)})`);
  // Exponents and root indexes are written in <sup class="nonum">, so "Do the math" doesn't ask for them.
  const supH = n => `<sup class="nonum e8">${numText(n)}</sup>`;
  const supFH = f => `<sup class="nonum e8">${f.d === 1 ? numText(f.n) : (f.n < 0 ? MINUS : '') + Math.abs(f.n) + '/' + f.d}</sup>`;
  const XV = v => `<i class="xv">${v}</i>`;
  const ROOTSYM = { 2: '√', 3: '∛', 4: '∜' };
  // A root: √ with a bar over what's inside. Text form: √50, √(18x³), ∛(x − 2), ⁵√32.
  function rootOf(idx, inner, html) {
    if (html) return `<span class="rt8">${idx > 2 ? `<sup class="nonum ri8">${idx}</sup>` : ''}<span class="rs8">√</span><span class="rr8">${inner}</span></span>`;
    const plain = /^\d+$/.test(inner) || /^x[²³⁴⁵⁶⁷⁸⁹]*$/.test(inner);
    return (ROOTSYM[idx] || supT(idx) + '√') + (plain ? inner : `(${inner})`);
  }
  const numH = (f, html) => (html ? fracHtml(f) : fracText(f));
  const parenF = (f, html) => (f.n < 0 || f.d > 1 ? `(${numH(f, html)})` : numH(f, html));

  // ================================================================ rx: radical expressions (stage 36)
  const Fc = (k, n = 1, xi = 0, xo = 0) => ({ k, n, xi, xo });
  const Tm = (...f) => ({ f });
  const hasRoot = f => f.n > 1 || f.xi > 0;
  const xPart = (e, html) => (e ? (html ? XV('x') : 'x') + (e === 1 ? '' : html ? supH(e) : supT(e)) : '');
  function fBody(f, html) {
    const a = Math.abs(f.k), xo = xPart(f.xo, html);
    const inner = hasRoot(f) ? (f.n > 1 ? String(f.n) : '') + xPart(f.xi, html) : '';
    const k = a === 1 && (xo || inner) ? '' : String(a);
    return k + xo + (inner ? rootOf(2, inner, html) : '');
  }
  const termSign = t => t.f.reduce((s, f) => s * Math.sign(f.k), 1);
  const lead = (sg, first, html) => (first ? (sg < 0 ? MINUS : '') : sg < 0 ? (html ? ` ${MINUS} ` : ` ${MINUS} `) : ' + ');
  const termText = (t, first, html) => lead(termSign(t), first, html) + t.f.map(f => fBody(f, html)).join(' · ');
  const sumText = (ts, html) => (ts.length ? ts.map((t, i) => termText(t, i === 0, html)).join('') : '0');
  const botTerms = e => e.bot.map(f => Tm(f));
  function rxText(e, html) {
    const top = sumText(e.top, html);
    if (!e.bot.length) return top;
    const bot = sumText(botTerms(e), html);
    if (html) return `<span class="frac f8"><span>${top}</span><span>${bot}</span></span>`;
    const wrap = (s, many) => (many || / /.test(s) ? `(${s})` : s);
    return `${wrap(top, e.top.length > 1 || e.top.some(t => t.f.length > 1))}/${wrap(bot, e.bot.length > 1)}`;
  }
  function tidyRx(e) {
    if (e.k8 !== 'rx') return e;
    e.top = e.top.filter(t => t.f.every(f => f.k !== 0));
    e.bot = e.bot.filter(f => f.k !== 0);
    if (e.bot.length === 1 && !hasRoot(e.bot[0]) && !e.bot[0].xo && e.bot[0].k < 0) {   // a minus on the bottom goes to the top
      e.bot[0].k = -e.bot[0].k; e.top.forEach(t => { t.f[0].k = -t.f[0].k; });
    }
    if (e.bot.length === 1 && !hasRoot(e.bot[0]) && !e.bot[0].xo && e.bot[0].k === 1) e.bot = [];
    if (!e.top.length) e.top = [Tm(Fc(0))];
    return e;
  }
  const rxState = (top, bot, o = {}) => tidyRx({ k8: 'rx', top, bot: bot || [], skill: o.skill || 'radsimp', qid: qid() });
  const fref = (i, j) => `t${i}f${j}`;
  function rxFactors(e) {
    const out = [];
    e.top.forEach((t, i) => t.f.forEach((f, j) => out.push({ f, ref: fref(i, j), i, j, top: true })));
    e.bot.forEach((f, i) => out.push({ f, ref: 'b' + i, i, top: false }));
    return out;
  }
  const factorAt = (e, ref) => { if (!ref) return null; const x = rxFactors(e).find(o => o.ref === ref); return x ? x.f : null; };
  function rxGcd(e) {
    let g = Math.abs(e.bot[0].k);
    for (const t of e.top) g = gcd(g, Math.abs(t.f.reduce((p, f) => p * f.k, 1)));
    return g;
  }
  const likeKey = f => f.n + ',' + f.xi + ',' + f.xo;
  function rxMoves(e) {
    const out = [];
    e.top.forEach((t, i) => { if (t.f.length > 1) out.push({ op: 'mul8', refs: t.f.map((_, j) => fref(i, j)), ti: i }); });
    for (const x of rxFactors(e)) {
      const q = sqPart(x.f.n), qx = x.f.xi - (x.f.xi % 2);
      if (q > 1 || qx > 0) out.push({ op: 'pull8', refs: [x.ref], q, qx });
    }
    const groups = {};
    e.top.forEach((t, i) => { if (t.f.length === 1) (groups[likeKey(t.f[0])] ||= []).push(i); });
    for (const g of Object.values(groups)) if (g.length > 1) out.push({ op: 'comb8', refs: g.map(i => fref(i, 0)), idx: g });
    const muls = e.top.some(t => t.f.length > 1);
    if (e.bot.length === 1 && hasRoot(e.bot[0]) && !muls) { const n = e.bot[0].n; out.push({ op: 'rat8', refs: ['b0'], m: n / sqPart(n) }); }
    if (e.bot.length === 2 && e.bot.some(hasRoot) && !muls) out.push({ op: 'conj8', refs: ['b0', 'b1'], f: conjOf(e.bot) });
    if (e.bot.length === 1 && !hasRoot(e.bot[0]) && !muls) { const g = rxGcd(e); if (g > 1) out.push({ op: 'red8', refs: ['bar'], d: g }); }
    return out;
  }
  const conjOf = bot => [Fc(bot[0].k, bot[0].n), Fc(-bot[1].k, bot[1].n)];
  const legalPull = (f, c) => !!f && Number.isInteger(c.q) && c.q >= 1 && isSq(c.q) && f.n % c.q === 0 && ((c.qx || 0) % 2 === 0) && (c.qx || 0) <= f.xi && (c.q > 1 || (c.qx || 0) > 0);
  function applyRx(r, m, c, ref) {
    switch (m.op) {
      case 'mul8': {
        const t = r.top[m.ti];
        t.f = [t.f.reduce((a, f) => Fc(a.k * f.k, a.n * f.n, a.xi + f.xi, a.xo + f.xo), Fc(1))];
        break;
      }
      case 'pull8': {
        const f = factorAt(r, ref || m.refs[0]), q = c.q, qx = c.qx || 0;
        f.k *= isqrt(q); f.n /= q; f.xi -= qx; f.xo += qx / 2;
        break;
      }
      case 'comb8': {
        const sum = m.idx.reduce((a, i) => a + r.top[i].f[0].k, 0);
        r.top[m.idx[0]].f[0].k = sum;
        r.top = r.top.filter((t, i) => !m.idx.slice(1).includes(i));
        if (sum === 0) r.top.splice(m.idx[0], 1);
        break;
      }
      case 'rat8': {
        const b = r.bot[0], mm = c.m;
        r.top.forEach(t => { t.f[0].n *= mm; });
        b.k *= isqrt(b.n * mm); b.n = 1;
        break;
      }
      case 'conj8': {
        const cj = conjOf(r.bot), out = [];
        for (const t of r.top) for (const x of cj) { const f = t.f[0]; out.push(Tm(Fc(f.k * x.k, f.n * x.n, f.xi, f.xo))); }
        const [A, B] = r.bot;
        r.top = out;
        r.bot = [Fc(A.k * A.k * A.n - B.k * B.k * B.n)];
        break;
      }
      case 'red8': {
        const d = c.d;
        r.top.forEach(t => { t.f[0].k /= d; });
        r.bot[0].k /= d;
        break;
      }
    }
    return tidyRx(r);
  }

  // ================================================================ re: rational exponents (stage 37)
  // eval forms:  exp  b^e      out  (ᵠ√b)^p      in  ᵠ√(b^p)      pv  r^p      root  ᵠ√c      val  v
  // (e = p/q; recip = the whole thing is under a 1, after a negative exponent is flipped)
  const evalState = (b, e, o = {}) => ({ k8: 're', ask: 'eval', b: FN(b), e: FN(e), recip: false, form: 'exp', c: null, r: null, v: null,
    skill: o.skill || 'ratexp', qid: qid() });
  const evValue = s => (s.form !== 'val' ? null : s.recip ? fDiv(F(1), s.v) : s.v);
  function evHtml(s, html = true) {
    const p = s.e ? Math.abs(s.e.n) : 1, q = s.e ? s.e.d : 1;
    const B = f => parenF(f, html);
    const pw = (x, n) => (n === 1 ? x : x + (html ? supH(n) : supT(n)));
    let body;
    switch (s.form) {
      case 'exp': body = B(s.b) + (html ? supFH(s.e) : supFT(s.e)); break;
      case 'out': body = pw(p === 1 ? rootOf(q, numH(s.b, html), html) : `(${rootOf(q, numH(s.b, html), html)})`, p); break;
      case 'in': body = rootOf(q, pw(B(s.b), p), html); break;
      case 'pv': body = pw(B(s.r), p); break;
      case 'root': body = rootOf(q, numH(s.c, html), html); break;
      default: return s.recip ? numH(fDiv(F(1), s.v), html) : numH(s.v, html);
    }
    if (!s.recip) return body;
    return html ? `<span class="frac f8"><span>1</span><span>${body}</span></span>` : `1/${body}`;
  }
  // rewrite and rules
  const rwState = (ask, e, o = {}) => ({ k8: 're', ask, e: FN(e), form: ask === 'torad' ? 'exp' : 'in', skill: o.skill || 'ratexp', qid: qid() });
  const rulesState = (num, den, g, o = {}) => ({ k8: 're', ask: 'rules', num: num.map(FN), den: (den || []).map(FN), g: g ? { e: FN(g.e), o: g.o } : null,
    skill: o.skill || 'ratexp', qid: qid() });
  const xPow = (e, html) => (fIs(e, 1) ? (html ? XV('x') : 'x') : (html ? XV('x') + supFH(e) : 'x' + supFT(e)));
  function rwHtml(s, html = true) {
    const p = s.e.n, q = s.e.d, X = html ? XV('x') : 'x';
    const pw = n => (n === 1 ? X : X + (html ? supH(n) : supT(n)));
    if (s.form === 'exp') return xPow(s.e, html);
    if (s.form === 'in') return rootOf(q, pw(p), html);
    return p === 1 ? rootOf(q, X, html) : `(${rootOf(q, X, html)})${html ? supH(p) : supT(p)}`;
  }
  function rulesHtml(s, html = true) {
    const row = (l, g) => {
      const parts = [];
      if (g) parts.push(`(${xPow(g.e, html)})${html ? supH(g.o) : supT(g.o)}`);
      l.forEach(e => parts.push(xPow(e, html)));
      return parts.join(' · ') || '1';
    };
    const top = row(s.num, s.g);
    if (!s.den.length) return top;
    return html ? `<span class="frac f8"><span>${top}</span><span>${row(s.den)}</span></span>` : `${top} / ${row(s.den)}`;
  }
  const reHtml = (s, html = true) => (s.ask === 'eval' ? evHtml(s, html) : s.ask === 'rules' ? rulesHtml(s, html) : rwHtml(s, html));
  function reMoves(s) {
    const V = ['V'];
    if (s.ask === 'eval') {
      switch (s.form) {
        case 'exp':
          if (s.e.n < 0) return [{ op: 'neg8', refs: V }];
          if (s.e.d > 1) return [{ op: 'rad8', refs: V, rf: 'out', b: s.b, p: s.e.n, q: s.e.d }];
          return [{ op: 'pw8', refs: V }];
        case 'out': case 'root': return [{ op: 'root8', refs: V }];
        case 'in': case 'pv': return [{ op: 'pw8', refs: V }];
      }
      return [];
    }
    if (s.ask === 'torad') return s.form === 'exp' ? [{ op: 'rw8', refs: V, rf: 'in', p: s.e.n, q: s.e.d }] : [];
    if (s.ask === 'toexp') return s.form === 'in' ? [{ op: 'rw8', refs: V, rf: 'exp', p: s.e.n, q: s.e.d }] : [];
    const out = [];
    if (s.g) out.push({ op: 'pow8', refs: V });
    else if (s.num.length > 1 || s.den.length > 1) out.push({ op: 'prod8', refs: V });
    else if (s.num.length && s.den.length) out.push({ op: 'quot8', refs: V });
    return out;
  }
  // Which rewrite forms are right: x^(p/q) = ᵠ√(xᵖ) = (ᵠ√x)ᵖ.
  const rwLegal = (s, c) => (s.ask === 'torad' ? c.rf === 'in' || c.rf === 'out' : c.rf === 'exp');
  function applyRe(r, m, c) {
    const p = r.e ? Math.abs(r.e.n) : 1, q = r.e ? r.e.d : 1;
    switch (m.op) {
      case 'neg8': r.recip = !r.recip; r.e = fNeg(r.e); break;
      case 'rad8': r.form = c.rf === 'in' && p > 1 ? 'in' : 'out'; break;
      case 'root8':
        if (r.form === 'out') { r.r = rootF(r.b, q); if (p === 1) { r.form = 'val'; r.v = r.r; } else r.form = 'pv'; }
        else { r.v = rootF(r.c, q); r.form = 'val'; }
        break;
      case 'pw8':
        if (r.form === 'in') { r.c = powF(r.b, p); r.form = 'root'; }
        else if (r.form === 'pv') { r.v = powF(r.r, p); r.form = 'val'; }
        else { r.v = powF(r.b, r.e.n); r.form = 'val'; }
        break;
      case 'rw8': r.form = c.rf; break;
      case 'pow8': r.num.unshift(fMul(r.g.e, F(r.g.o))); r.g = null; break;
      case 'prod8':
        if (r.num.length > 1) r.num = [r.num.reduce(fAdd)];
        if (r.den.length > 1) r.den = [r.den.reduce(fAdd)];
        break;
      case 'quot8': r.num = [fSub(r.num[0], r.den[0])]; r.den = []; break;
    }
    return r;
  }

  // ================================================================ eq: equations (stages 37 and 38)
  const Lin = (a, b) => ({ t: 'lin', a: FN(a), b: FN(b) });
  const Rad = (k, idx, a, b, d = 0) => ({ t: 'rad', k: FN(k), idx, u: Lin(a, b), d: FN(d) });
  const Pw = (k, e, d = 0) => ({ t: 'pw', k: FN(k), e: FN(e), d: FN(d) });
  const isConst = n => n.t === 'lin' && fz(n.a);
  const isX = n => n.t === 'lin' && fIs(n.a, 1) && fz(n.b);
  const eqState = (L, R, o = {}) => ({ k8: 'eq', L, R, sq: false, orig: clone({ L, R }), cands: null, pend: null, none: false,
    skill: o.skill || 'radeq', qid: qid() });
  // a·x + b written out; with coef false the number in front of x is shown even when it is 1
  function linText(n, html) {
    const X = html ? XV('x') : 'x';
    if (fz(n.a)) return numH(n.b, html);
    const a = fIs(n.a, 1) ? '' : fIs(n.a, -1) ? MINUS : numH(n.a, html);
    return a + X + (fz(n.b) ? '' : (n.b.n < 0 ? ` ${MINUS} ` : ' + ') + numH(fAbs(n.b), html));
  }
  const kPre = (k, html) => (fIs(k, 1) ? '' : fIs(k, -1) ? MINUS : numH(k, html));
  const dPost = (d, html) => (fz(d) ? '' : (d.n < 0 ? ` ${MINUS} ` : ' + ') + numH(fAbs(d), html));
  function nodeText(n, html) {
    const X = html ? XV('x') : 'x';
    switch (n.t) {
      case 'lin': return linText(n, html);
      case 'rad': return kPre(n.k, html) + rootOf(n.idx, linText(n.u, html), html) + dPost(n.d, html);
      case 'pw': return kPre(n.k, html) + xPow(n.e, html) + dPost(n.d, html);
      case 'sq': return `(${linText(n, html)})${html ? supH(2) : '²'}`;
      case 'quad': {
        const ts = [];
        const add = (c, body) => { if (fz(c)) return; const a = fAbs(c); ts.push({ neg: c.n < 0, s: (fIs(a, 1) && body ? '' : numH(a, html)) + body }); };
        add(n.c2, X + (html ? supH(2) : '²')); add(n.c1, X); add(n.c0, '');
        return ts.length ? ts.map((t, i) => (i ? (t.neg ? ` ${MINUS} ` : ' + ') : t.neg ? MINUS : '') + t.s).join('') : '0';
      }
      case 'fac': return [n.r1, n.r2].sort((a, b) => (fz(b) ? 1 : 0) - (fz(a) ? 1 : 0)).map(r => (fz(r) ? X : `(${X} ${r.n < 0 ? '+' : MINUS} ${numH(fAbs(r), html)})`)).join('');
      case 'ev': return reHtml(n.re, html);
    }
    return '';
  }
  const eqText = (e, html) => `${nodeText(e.L, html)} = ${nodeText(e.R, html)}`;
  const origText = (e, html) => `${nodeText(e.orig.L, html)} = ${nodeText(e.orig.R, html)}`;
  function quadRoots(n) {             // whole roots of c2·x² + c1·x + c0 (c2 = 1 here), or null
    const out = [];
    for (let r = -200; r <= 200 && out.length < 2; r++) if (fz(fAdd(fAdd(fMul(n.c2, F(r * r)), fMul(n.c1, F(r))), n.c0))) out.push(F(r));
    return out.length === 2 ? out : null;
  }
  const eqDone = e => e.none || (!!e.cands && !e.pend && e.cands.every(c => c.st !== 'open')) || (!e.sq && !e.cands && isX(e.L) && isConst(e.R));
  function eqMoves(e) {
    if (eqDone(e)) return [];
    if (e.cands) {
      if (e.pend) return [{ op: e.pend.ok ? 'keep8' : 'rej8', both: true, v: e.pend.v }];
      return e.cands.filter(c => c.st === 'open').map(c => ({ op: 'check8', refs: ['O'], v: c.v }));
    }
    const L = e.L, R = e.R;
    if (R.t === 'ev') return reMoves(R.re);
    if (L.t === 'rad') {
      if (!fz(L.d)) return [{ op: 'as8', both: true, n: fNeg(L.d) }];
      if (!fIs(L.k, 1)) return [{ op: 'dv8', both: true, n: L.k }];
      if (L.idx === 2 && isConst(R) && R.b.n < 0) return [{ op: 'none8', both: true }];
      return [{ op: 'sq8', both: true, p: L.idx }];
    }
    if (L.t === 'pw') {
      if (!fz(L.d)) return [{ op: 'as8', both: true, n: fNeg(L.d) }];
      if (!fIs(L.k, 1)) return [{ op: 'dv8', both: true, n: L.k }];
      return [{ op: 'raise8', both: true, e: F(L.e.d, L.e.n) }];
    }
    if (L.t === 'lin' && R.t === 'sq') return [{ op: 'expand8', refs: ['R'], a: R.a, b: R.b, form: 'right' }];
    if (L.t === 'lin' && R.t === 'quad') {
      if (!fz(L.a) || !fz(L.b)) return [{ op: 'zero8', both: true, a: L.a, b: L.b }];
      const rs = quadRoots(R);
      return rs ? [{ op: 'fac8', refs: ['R'], r1: rs[0], r2: rs[1] }] : [];
    }
    if (R.t === 'fac') return [{ op: 'zp8', both: true }];
    if (L.t === 'lin' && R.t === 'lin') {
      if (!fz(R.a)) return [{ op: 'as8x', both: true, n: fNeg(R.a) }];
      if (!fz(L.b)) return [{ op: 'as8', both: true, n: fNeg(L.b) }];
      if (!fIs(L.a, 1)) return [{ op: 'dv8', both: true, n: L.a }];
    }
    return [];
  }
  // A side worked out at x = v: { sub (the side with v written in), kind: num | irr | undef, val, f (float), out (html) }
  function evalSide(n, v, html = true) {
    const subLin = u => {
      if (fz(u.a)) return numH(u.b, html);
      const vt = v.n < 0 || v.d > 1 ? `(${numH(v, html)})` : numH(v, html);
      const a = fIs(u.a, 1) ? vt : fIs(u.a, -1) ? MINUS + `(${numH(v, html)})` : `${numH(u.a, html)}(${numH(v, html)})`;
      return a + (fz(u.b) ? '' : (u.b.n < 0 ? ` ${MINUS} ` : ' + ') + numH(fAbs(u.b), html));
    };
    const val = u => fAdd(fMul(u.a, v), u.b);
    if (n.t === 'lin') { const f = val(n); return { sub: subLin(n), kind: 'num', val: f, f: fv(f), out: numH(f, html) }; }
    if (n.t === 'pw') {   // only for completeness; stage 37 equations aren't checked
      const f = rootF(powF(v, n.e.n), n.e.d); const w = f ? fAdd(fMul(n.k, f), n.d) : null;
      return { sub: kPre(n.k, html) + parenF(v, html) + (html ? supFH(n.e) : supFT(n.e)) + dPost(n.d, html), kind: w ? 'num' : 'undef', val: w, f: w ? fv(w) : NaN, out: w ? numH(w, html) : '?' };
    }
    // rad
    const w = val(n.u), sub = kPre(n.k, html) + rootOf(n.idx, subLin(n.u), html) + dPost(n.d, html);
    if (w.n < 0 && n.idx % 2 === 0) return { sub, kind: 'undef', w, f: NaN, out: rootOf(n.idx, numH(w, html), html) };
    const r = rootF(w, n.idx);
    if (r) { const f = fAdd(fMul(n.k, r), n.d); return { sub, kind: 'num', w, val: f, f: fv(f), out: numH(f, html) }; }
    const fl = fv(n.k) * Math.sign(fv(w)) * Math.pow(Math.abs(fv(w)), 1 / n.idx) + fv(n.d);
    return { sub, kind: 'irr', w, f: fl, out: kPre(n.k, html) + rootOf(n.idx, numH(w, html), html) + dPost(n.d, html) };
  }
  function checkAt(e, v) {
    const l = evalSide(e.orig.L, v), r = evalSide(e.orig.R, v);
    const ok = l.kind !== 'undef' && r.kind !== 'undef' && Math.abs(l.f - r.f) < 1e-9;
    return { v, l, r, ok };
  }
  function applyEq(r, m, c) {
    const add = (n, k) => { if (n.t === 'lin') n.b = fAdd(n.b, k); else n.d = fAdd(n.d, k); };
    const div = (n, k) => { if (n.t === 'lin') { n.a = fDiv(n.a, k); n.b = fDiv(n.b, k); } else { n.k = fDiv(n.k, k); n.d = fDiv(n.d, k); } };
    switch (m.op) {
      case 'as8': add(r.L, c.n); add(r.R, c.n); break;
      case 'as8x': r.L.a = fAdd(r.L.a, c.n); r.R.a = fAdd(r.R.a, c.n); break;
      case 'dv8': div(r.L, c.n); div(r.R, c.n); break;
      case 'sq8': {
        const p = m.p, R = r.R;
        r.L = Lin(r.L.u.a, r.L.u.b);
        if (R.t === 'rad') r.R = Lin(R.u.a, R.u.b);
        else if (isConst(R)) r.R = Lin(0, powF(R.b, p));
        else r.R = { t: 'sq', a: R.a, b: R.b };
        if (p === 2) r.sq = true;
        break;
      }
      case 'none8': r.none = true; break;
      case 'raise8': r.L = Lin(1, 0); r.R = { t: 'ev', re: evalState(r.R.b, c.e, { skill: r.skill }) }; break;
      case 'expand8': { const R = r.R; r.R = { t: 'quad', c2: fMul(R.a, R.a), c1: fMul(F(2), fMul(R.a, R.b)), c0: fMul(R.b, R.b) }; break; }
      case 'zero8': r.R.c1 = fSub(r.R.c1, r.L.a); r.R.c0 = fSub(r.R.c0, r.L.b); r.L = Lin(0, 0); break;
      case 'fac8': r.R = { t: 'fac', r1: m.r1, r2: m.r2 }; break;
      case 'zp8': { const rs = [r.R.r1, r.R.r2].sort((a, b) => fv(a) - fv(b)); r.cands = rs.map(v => ({ v, st: 'open' })); break; }
      case 'check8': { const v = c.v; r.pend = checkAt(r, v); r.pend.i = r.cands.findIndex(o => fEq(o.v, v)); break; }
      case 'keep8': case 'rej8': r.cands[r.pend.i].st = m.op === 'keep8' ? 'keep' : 'rej'; r.pend = null; break;
      default:
        if (r.R.t === 'ev') applyRe(r.R.re, m, c);
    }
    return tidyEq(r);
  }
  function tidyEq(r) {
    if (r.k8 !== 'eq') return r;
    if (r.R.t === 'ev' && r.R.re.form === 'val') r.R = Lin(0, evValue(r.R.re));
    if (r.sq && !r.cands && isX(r.L) && isConst(r.R)) r.cands = [{ v: r.R.b, st: 'open' }];
    return r;
  }
  function eqAnswer(e, html) {
    const X = html ? XV('x') : 'x';
    if (e.none) return 'No solution';
    if (e.cands) {
      const kept = e.cands.filter(c => c.st === 'keep');
      return kept.length ? kept.map(c => `${X} = ${numH(c.v, html)}`).join(' or ') : 'No solution';
    }
    return `${X} = ${numH(e.R.b, html)}`;
  }

  // ================================================================ moves, legality, applying
  const movesOf = e => (e.k8 === 'rx' ? rxMoves(e) : e.k8 === 're' ? reMoves(e) : eqMoves(e));
  const C8 = (op, o = {}) => ({ op, a8: true, scope: BOTH.has(op) ? 'both' : 'part', ...o });
  const BOTH = new Set(['as8', 'as8x', 'dv8', 'sq8', 'raise8', 'zero8', 'zp8', 'none8', 'keep8', 'rej8']);
  const PARAMS = ['q', 'qx', 'm', 'd', 'f', 'rf', 'n', 'p', 'e', 'a', 'b', 'form', 'r1', 'r2', 'v'];
  const moveCard = m => { const c = C8(m.op); for (const k of PARAMS) if (m[k] !== undefined) c[k] = clone(m[k]); return c; };
  const isSolved8 = e => !movesOf(e).length;
  // Does card c do move m? Some moves accept a family of cards (any perfect square pulls out, either root form).
  function okParams(e, m, c, ref) {
    switch (c.op) {
      case 'pull8': return legalPull(factorAt(e, ref || m.refs[0]), c);
      case 'rat8': return Number.isInteger(c.m) && c.m > 1 && isSq(e.bot[0].n * c.m);
      case 'red8': return Number.isInteger(c.d) && c.d > 1 && m.d % c.d === 0;
      case 'conj8': return !!c.f && c.f.length === 2 && c.f.every((x, i) => x.k === m.f[i].k && x.n === m.f[i].n);
      case 'rad8': return c.rf === 'out' || c.rf === 'in';
      case 'rw8': return rwLegal(e, c);
      case 'sq8': return c.p === m.p;
      case 'as8': case 'as8x': case 'dv8': return !!c.n && fEq(c.n, m.n);
      case 'raise8': return !!c.e && fEq(c.e, m.e);
      case 'expand8': return c.form === 'right';
      case 'zero8': return !!c.a && fEq(c.a, m.a) && fEq(c.b, m.b);
      case 'fac8': return !!c.r1 && ((fEq(c.r1, m.r1) && fEq(c.r2, m.r2)) || (fEq(c.r1, m.r2) && fEq(c.r2, m.r1)));
      case 'check8': return !!c.v && fEq(c.v, m.v);
    }
    return true;
  }
  function legalMove(e, c, ref) {
    if (!c || !c.a8 || c.op === 'trap') return null;
    return movesOf(e).find(m => m.op === c.op && (m.both || !m.refs || m.refs.includes(ref)) && okParams(e, m, c, ref)) || null;
  }
  const correct8 = (e, c, target) => !!legalMove(e, c, refOf(target));
  function apply8(e, c, ref) {
    const r = clone(e);
    const m = legalMove(e, c, ref) || movesOf(e).find(o => o.op === (c && c.op));   // a replayed move always has its place
    if (!m || !c || c.op === 'trap') return r;
    const at = ref && m.refs && m.refs.includes(ref) ? ref : m.refs ? m.refs[0] : null;
    if (e.k8 === 'rx') return applyRx(r, m, c, at);
    if (e.k8 === 're') return applyRe(r, m, c);
    return applyEq(r, m, c);
  }
  function canon8(e) { const m = movesOf(e)[0]; return m ? { ...moveCard(m), ref: m.refs ? m.refs[0] : null } : null; }

  // ================================================================ path, skills, answers
  const HOME = { pull8: 'radsimp', mul8: 'radsimp', comb8: 'radsimp', rat8: 'radsimp', conj8: 'radsimp', red8: 'radsimp',
    neg8: 'ratexp', rad8: 'ratexp', root8: 'ratexp', pw8: 'ratexp', rw8: 'ratexp', prod8: 'ratexp', pow8: 'ratexp', quot8: 'ratexp', raise8: 'ratexp',
    sq8: 'radeq', none8: 'radeq', expand8: 'radeq', zero8: 'radeq', fac8: 'radeq', zp8: 'radeq', check8: 'radeq', keep8: 'radeq', rej8: 'radeq' };
  function skillFor(m, main) {
    const home = HOME[m.op] || main;
    return home === main || isUnlocked(home) ? home : main;
  }
  function pathOf8(e, main) {
    const path = []; let s = e;
    for (let i = 0; i < 60; i++) { const m = canon8(s); if (!m) break; path.push({ state: s, move: m, skill: skillFor(m, main) }); s = apply8(s, m, m.ref); }
    return { path, end: s };
  }
  function answerOf(e, html) {
    if (e.k8 === 'rx') return '= ' + rxText(e, html);
    if (e.k8 === 're') return '= ' + reHtml(e, html);
    return eqAnswer(e, html);
  }
  function makeEquation8(state, enemy) {
    const main = state.skill || 'radsimp', { path, end } = pathOf8(state, main);
    return { start: state, end, path, main, skills: [...new Set(path.map(p => p.skill))], enemy, act2: true, act8: true, answer: F(0), answerText: answerOf(end, false) };
  }
  function refreshPath(cur) {
    const fresh = pathOf8(cur.state, cur.main).path;
    cur.path = cur.path.slice(0, cur.step).concat(fresh);
  }

  // ================================================================ cards
  const signedN = (n, html) => (n.n < 0 ? MINUS + ' ' : '+ ') + numH(fAbs(n), html);
  const qLabel = c => (c.q > 1 || !c.qx ? String(c.q) : '') + xPart(c.qx || 0, true);
  function rwFormHtml(c) {
    const X = XV('x'), p = c.p, q = c.q;
    const pw = n => (n === 1 ? X : X + supH(n));
    switch (c.rf) {
      case 'in': return rootOf(q, pw(p), true);
      case 'out': return p === 1 ? rootOf(q, X, true) : `(${rootOf(q, X, true)})${supH(p)}`;
      case 'swap': return p === 1 ? pw(q) : rootOf(p, pw(q), true);
      case 'exp': return X + supFH(F(p, q));
      case 'expswap': return X + supFH(F(q, p));
      case 'expmul': return X + supH(p * q);
    }
    return '?';
  }
  function radFormHtml(c) {
    const b = numH(FN(c.b), true), p = c.p, q = c.q;
    switch (c.rf) {
      case 'out': return p === 1 ? rootOf(q, b, true) : `(${rootOf(q, b, true)})${supH(p)}`;
      case 'in': return rootOf(q, b + (p === 1 ? '' : supH(p)), true);
      case 'swap': return p === 1 ? (c.b < 0 ? `(${b})` : b) + supH(q) : q === 1 ? rootOf(p, b, true) : `(${rootOf(p, b, true)})${supH(q)}`;
      case 'mul': return `${b} ${TIMES} ${p}/${q}`;
    }
    return '?';
  }
  const expandHtml = c => {
    const a = FN(c.a), b = FN(c.b);
    const q = c.form === 'each' ? { t: 'quad', c2: fMul(a, a), c1: F(0), c0: fMul(b, b) }
      : c.form === 'flip' ? { t: 'quad', c2: fMul(a, a), c1: fNeg(fMul(F(2), fMul(a, b))), c0: fMul(b, b) }
      : c.form === 'half' ? { t: 'quad', c2: fMul(a, a), c1: fMul(a, b), c0: fMul(b, b) }
      : { t: 'quad', c2: fMul(a, a), c1: fMul(F(2), fMul(a, b)), c0: fMul(b, b) };
    return nodeText(q, true);
  };
  const CARD = {
    pull8:   c => ({ label: `Pull out ${qLabel(c)}`, text: 'Take a perfect square out of the root', kind: 'Pull out a square', icon: 'pull8' }),
    mul8:    () => ({ label: 'Multiply roots', text: '√a · √b = √(ab): one root', kind: 'Multiply radicals', icon: 'mul8' }),
    comb8:   () => ({ label: 'Combine', text: 'Same root: add the numbers in front', kind: 'Combine like radicals', icon: 'comb' }),
    rat8:    c => ({ label: `${TIMES} <span class="frac f8c"><span>${rootOf(2, String(c.m), true)}</span><span>${rootOf(2, String(c.m), true)}</span></span>`, text: `Rationalize: multiply top and bottom by √${c.m}`, kind: 'Rationalize', icon: 'rat8' }),
    conj8:   c => { const t = sumText(c.f.map(f => Tm(f)), true); return { label: `${TIMES} (${t})`, text: `Multiply top and bottom by ${sumText(c.f.map(f => Tm(f)), false)}`, kind: 'Multiply by the conjugate', icon: 'rat8' }; },
    red8:    c => ({ label: `${DIV} ${c.d}`, text: `Divide top and bottom by ${c.d}`, kind: 'Reduce the fraction', icon: 'div' }),
    neg8:    () => ({ label: 'Neg. power', text: 'b⁻ⁿ = 1/bⁿ: put it under 1', kind: 'Negative exponent', icon: 'negx6' }),
    rad8:    c => ({ label: radFormHtml(c), text: 'Rewrite the power as a root', kind: 'Rewrite as a root', icon: 'rad8' }),
    root8:   () => ({ label: 'Take root', text: 'Work out the root', kind: 'Take the root', icon: 'root8' }),
    pw8:     () => ({ label: 'Power', text: 'Work out the power', kind: 'Work out the power', icon: 'pow6' }),
    rw8:     c => ({ label: rwFormHtml(c), text: 'Rewrite it in this form', kind: 'Rewrite', icon: 'rad8' }),
    prod8:   () => ({ label: 'Product rule', text: 'xᵃ · xᵇ = xᵃ⁺ᵇ: add the exponents', kind: 'Product rule', icon: 'prod6' }),
    pow8:    () => ({ label: 'Power rule', text: '(xᵃ)ⁿ = xᵃⁿ: multiply the exponents', kind: 'Power rule', icon: 'pow6' }),
    quot8:   () => ({ label: 'Quotient rule', text: 'xᵃ / xᵇ = xᵃ⁻ᵇ: subtract the exponents', kind: 'Quotient rule', icon: 'quot6' }),
    as8:     c => ({ label: signedN(FN(c.n), true).replace('+ ', '+').replace(MINUS + ' ', MINUS), text: c.n.n < 0 ? `Subtract ${fracText(fAbs(c.n))} from both sides` : `Add ${fracText(c.n)} to both sides`, kind: c.n.n < 0 ? 'Subtract' : 'Add', icon: c.n.n < 0 ? 'sub' : 'add' }),
    as8x:    c => { const t = linText(Lin(fAbs(c.n), 0), true); return { label: (c.n.n < 0 ? MINUS : '+') + t, text: `${c.n.n < 0 ? 'Subtract' : 'Add'} ${linText(Lin(fAbs(c.n), 0), false)} ${c.n.n < 0 ? 'from' : 'to'} both sides`, kind: 'Move the x term', icon: c.n.n < 0 ? 'sub' : 'add' }; },
    dv8:     c => ({ label: `${DIV} ${parenF(FN(c.n), true)}`, text: `Divide both sides by ${fracText(c.n)}`, kind: 'Divide', icon: 'div' }),
    sq8:     c => ({ label: c.p === 3 ? 'Cube both' : 'Square both', text: c.p === 3 ? 'Cube both sides: (∛u)³ = u' : 'Square both sides: (√u)² = u', kind: c.p === 3 ? 'Cube both sides' : 'Square both sides', icon: 'sq8' }),
    raise8:  c => ({ label: `( )${supFH(c.e)}`, text: `Raise both sides to the ${fracText(c.e)} power`, kind: 'Raise to a power', icon: 'raise8' }),
    expand8: c => ({ label: expandHtml(c), text: `Expand ${nodeText({ t: 'sq', a: FN(c.a), b: FN(c.b) }, false)}`, kind: 'Expand the square', icon: 'sqb6' }),
    zero8:   c => { const t = linText(Lin(c.a, c.b), true), w = fz(FN(c.a)) || fz(FN(c.b)) ? t : `(${t})`; return { label: `${MINUS} ${w}`, text: `Subtract ${fz(FN(c.a)) || fz(FN(c.b)) ? linText(Lin(c.a, c.b), false) : '(' + linText(Lin(c.a, c.b), false) + ')'} from both sides`, kind: 'Get 0 on one side', icon: 'sub' }; },
    fac8:    c => ({ label: nodeText({ t: 'fac', r1: FN(c.r1), r2: FN(c.r2) }, true), text: 'Factor the quadratic', kind: 'Factor', icon: 'fac8' }),
    zp8:     () => ({ label: 'Zero product', text: 'Set each factor equal to 0', kind: 'Zero product', icon: 'zp8' }),
    check8:  c => ({ label: `Check ${XV('x')} = ${numH(FN(c.v), true)}`, text: 'Put it into the original equation', kind: 'Check an answer', icon: 'check8' }),
    keep8:   () => ({ label: '✓ True', text: 'The sides match: keep it', kind: 'Keep the answer', icon: 'keep8' }),
    rej8:    () => ({ label: '✗ False', text: 'The sides differ: reject it', kind: 'Reject the answer', icon: 'rej8' }),
    none8:   () => ({ label: 'No solution', text: 'Declare: no number works', kind: 'No solution', icon: 'none' }),
  };
  const info = c => (c && c.a8 && CARD[c.op] ? CARD[c.op](c) : null);
  const label = c => (c && c.a8 && c.op === 'trap' ? `<span class="clong l8">${c.label}</span>` : info(c) ? `<span class="clong l8">${info(c).label}</span>` : null);
  const text = c => (c && c.a8 && c.op === 'trap' ? c.text : info(c) ? info(c).text : null);
  const kind = c => (c && c.a8 && c.op === 'trap' ? 'Trap: ' + c.trap : info(c) ? info(c).kind : null);
  const icon = c => (c && c.a8 && c.op === 'trap' ? c.icon : info(c) ? info(c).icon : null);
  const slot = () => null;
  const targetSel = c => (c && c.a8 && (c.scope || 'both') === 'part' ? '#equation .tok[data-ref]' : null);

  // Where a ◎ card can go: its legal places, or else every place of its kind (so a wrong card still has
  // to be dropped somewhere, or goes nowhere at all when there is no such thing).
  function kindPlaces(e, op) {
    if (e.k8 === 'rx') {
      const fs = rxFactors(e);
      if (op === 'pull8' || op === 'mul8') return fs.map(x => x.ref);
      if (op === 'comb8') return fs.filter(x => x.top).map(x => x.ref);
      if (op === 'rat8' || op === 'conj8') return e.bot.length ? ['b0'] : [];
      if (op === 'red8') return e.bot.length ? ['bar'] : [];
      return [];
    }
    if (op === 'check8') return e.k8 === 'eq' && e.cands ? ['O'] : [];
    if (op === 'expand8' || op === 'fac8') return e.k8 === 'eq' && !e.cands ? ['R'] : [];
    if (['neg8', 'rad8', 'root8', 'pw8', 'rw8', 'prod8', 'pow8', 'quot8'].includes(op)) return e.k8 === 're' || (e.k8 === 'eq' && e.R.t === 'ev' && !e.cands) ? ['V'] : [];
    return [];
  }
  function places(e, c) {
    const op = c.op === 'trap' ? c.like : c.op;
    if (!op) return [];
    const legal = movesOf(e).filter(m => m.op === op && m.refs);
    if (legal.length && c.op !== 'trap') return [...new Set(legal.map(m => m.refs[0]))];
    return kindPlaces(e, op);
  }
  const refEl = ref => $('equation').querySelector(`.tok[data-ref="${ref}"]`);
  function autoTarget(c) {
    if (!cur || !cur.act8 || !c.a8) return 'pass';
    const ps = places(cur.state, c);
    if (ps.length >= 2) return undefined;
    if (!ps.length) return null;
    return refEl(ps[0]) || ps[0];
  }
  function onDrag(c, on) {
    document.querySelectorAll('.ok8').forEach(el => el.classList.remove('ok8'));
    if (!on || !cur || !cur.act8) return;
    const hl = difficulty.highlight === 'on' || isTutorial() || (difficulty.highlight === 'afterWrong' && cur.wrong > 0);
    if (!hl || !targetSel(c)) return;
    for (const el of document.querySelectorAll('#equation .tok[data-ref]')) if (correct8(cur.state, c, el)) el.classList.add('ok8');
  }

  // ---------------------------------------------------------------- hands
  const DECOYS = [1, 1, 2, 2];
  const trap = (name, like, lbl, txt, why, ic, scope = 'part') => ({ op: 'trap', a8: true, trap: name, like, scope, label: lbl, text: txt, why, icon: ic });
  const R2 = (n, html = true) => rootOf(2, String(n), html);
  // Rule decoys (the classic mistakes, dealt at every level outside tutorials) and Expert traps.
  function specials(e, want) {
    const out = { rule: [], traps: [] };
    const ms = movesOf(e), has = op => ms.some(m => m.op === op), mv = op => ms.find(m => m.op === op);
    if (e.k8 === 'rx') {
      if (has('pull8')) {
        const m = mv('pull8'), f = factorAt(e, m.refs[0]);
        if (m.q > 1) out.rule.push(trap('forgot the root', 'pull8', `Pull out ${m.q} as ${m.q}`, `${R2(f.n)} = ${m.q}${R2(f.n / m.q)}: the square comes out as it is`,
          P(`Only the <b>square root</b> of a perfect square comes out: ${R2(m.q)} = ${isqrt(m.q)}. So ${R2(f.n)} = ${R2(m.q)} · ${R2(f.n / m.q)} = <b>${isqrt(m.q)}</b>${R2(f.n / m.q)}, not ${m.q}${R2(f.n / m.q)}. Check: ${m.q}${R2(f.n / m.q)} squared is far more than ${f.n}.`), 'pull8'));
        if (f.n > 1 && !isSq(f.n)) {   // the non-square factor
          let d = 2; while (d < f.n && (f.n % d || isSq(d))) d++;
          if (d < f.n) out.traps.push(trap('not a square', 'pull8', `Pull out ${d}`, `${R2(f.n)}: ${d} is a factor, so it comes out`,
            P(`Only a <b>perfect square</b> factor can come out of a square root, because √(a²) = a. ${d} isn't a perfect square, so ${R2(d)} stays a root.`), 'pull8'));
        }
      }
      const roots = e.top.filter(t => t.f.length === 1 && hasRoot(t.f[0]));
      if (roots.length >= 2 && !e.bot.length) {
        const [a, b] = roots.map(t => t.f[0]);
        if (a.k === 1 && b.k === 1 && !a.xi && !b.xi) out.rule.push(trap('add under the root', 'comb8', 'Add roots', `${R2(a.n)} + ${R2(b.n)} = ${R2(a.n + b.n)}`,
          P(`Roots don't add like that: ${R2(a.n)} + ${R2(b.n)} is not ${R2(a.n + b.n)}. (Try √9 + √16 = 3 + 4 = 7, but √25 = 5.) Only <b>like radicals</b>, with the same number under the root, combine: 2√3 + 5√3 = 7√3. Simplify each root first and see if they match.`), 'comb'));
        else out.rule.push(trap('add under the root', 'comb8', 'Add roots', 'Add the numbers under the roots too',
          P('Combining like radicals adds the numbers <b>in front</b>, and the root stays the same: 2√3 + 5√3 = 7√3, not 7√6. Roots with different numbers inside don\'t combine at all.'), 'comb'));
      }
      if (has('mul8')) {
        const t = e.top[mv('mul8').ti];
        if (t.f.some(f => Math.abs(f.k) > 1)) out.rule.push(trap('add the outside numbers', 'mul8', 'Add fronts', 'Multiply the roots, add the numbers in front',
          P(`Everything here is multiplied, so the numbers in front multiply too: ${t.f.map(f => fBody(f, true)).join(' · ')} = (${t.f.map(f => Math.abs(f.k)).join(' · ')})${R2(t.f.reduce((p, f) => p * f.n, 1))}. Order doesn't matter in a product.`), 'mul8'));
        else out.rule.push(trap('add under the root', 'mul8', 'Add inside', `√a · √b = √(a + b)`,
          P(`Multiplying roots multiplies what's inside: √a · √b = √(a · b). So ${t.f.map(f => fBody(f, true)).join(' · ')} = ${R2(t.f.reduce((p, f) => p * f.n, 1))}, not ${R2(t.f.reduce((p, f) => p + f.n, 0))}.`), 'mul8'));
      }
      if (has('rat8')) {
        const m = mv('rat8');
        out.rule.push(trap('bottom only', 'rat8', `${TIMES} ${R2(m.m)} below`, `Multiply just the bottom by ${R2(m.m, false)}`,
          P(`Multiplying only the bottom changes the value of the fraction. Multiply the top <b>and</b> the bottom by ${R2(m.m)}: that's multiplying by ${R2(m.m)}/${R2(m.m)} = 1, so the value stays the same.`), 'rat8'));
      }
      if (has('conj8')) {
        const b = e.bot;
        out.rule.push(trap('root only', 'conj8', `${TIMES} ${R2(b[1].n)}/${R2(b[1].n)}`, `Multiply top and bottom by ${R2(b[1].n, false)}`,
          P(`With two terms on the bottom, multiplying by ${R2(b[1].n)} just moves the root to the other term: (${sumText(botTerms(e), true)}) · ${R2(b[1].n)} still has a root. Use the <b>conjugate</b> (the same two terms with the middle sign flipped): (a − b)(a + b) = a² − b², and the roots square away.`), 'rat8'));
      }
      if (has('red8')) {
        const t = e.top.find(x => x.f[0].n > 1 && x.f[0].n % mv('red8').d === 0) || (e.top.find(x => x.f[0].n > 1));
        if (t) out.rule.push(trap('cancel into the root', 'red8', 'Cancel root', `Cancel the ${R2(t.f[0].n)} with the ${e.bot[0].k} below`,
          P(`A number under a root isn't the same as a number outside it: ${R2(t.f[0].n)} is about ${Math.sqrt(t.f[0].n).toFixed(2)}, not ${t.f[0].n}. Reduce the fraction only with the numbers <b>outside</b> the roots, and only if every term on top shares the factor.`), 'div'));
      }
    } else if (e.k8 === 're' && e.ask === 'eval') {
      if (has('rad8')) {
        const p = e.e.n, q = e.e.d;
        out.rule.push(C8('rad8', { rf: 'swap', b: e.b, p, q }));
        if (p > 1) out.traps.push(C8('rad8', { rf: 'mul', b: e.b, p, q }));
      }
      if (has('neg8')) out.rule.push(trap('negative answer', 'neg8', 'Make it neg.', `${numH(e.b, true)}${supFH(e.e)} is negative`,
        P(`A negative exponent doesn't make the number negative. It means "1 over": b${supH(-2)} = 1/b${supH(2)}. So ${parenF(e.b, true)}${supFH(e.e)} = 1/${parenF(e.b, true)}${supFH(fNeg(e.e))}, which is positive.`), 'negx6'));
    } else if (e.k8 === 're' && (e.ask === 'torad' || e.ask === 'toexp')) {
      out.rule.push(C8('rw8', { rf: e.ask === 'torad' ? 'swap' : 'expswap', p: e.e.n, q: e.e.d }));
    } else if (e.k8 === 're' && e.ask === 'rules') {
      if (has('prod8') && e.num.length > 1) out.rule.push(trap('multiply exponents', 'prod8', `${TIMES} exponents`, 'Same base: multiply the exponents',
        P(`x${supFH(e.num[0])} · x${supFH(e.num[1])}: multiplying powers of the same base <b>adds</b> the exponents, fractions or not: ${fracText(e.num[0])} + ${fracText(e.num[1])} = ${fracText(fAdd(e.num[0], e.num[1]))}. You multiply exponents for a power of a power.`), 'prod6'));
      if (has('pow8')) out.rule.push(trap('add exponents', 'pow8', 'Add powers', 'Power of a power: add the exponents',
        P(`(x${supFH(e.g.e)})${supH(e.g.o)} is x${supFH(e.g.e)} multiplied ${e.g.o} times, so the exponents <b>multiply</b>: ${fracText(e.g.e)} · ${e.g.o} = ${fracText(fMul(e.g.e, F(e.g.o)))}.`), 'pow6'));
      if (has('quot8')) out.rule.push(trap('divide exponents', 'quot8', `${DIV} exponents`, 'Same base on top and bottom: divide the exponents',
        P(`Dividing powers of the same base <b>subtracts</b> the exponents (top minus bottom): ${fracText(e.num[0])} ${MINUS} ${fracText(e.den[0])} = ${fracText(fSub(e.num[0], e.den[0]))}.`), 'quot6'));
    } else if (e.k8 === 'eq') {
      if (e.cands && !e.pend) {
        const all = e.cands.filter(c => c.st !== 'rej').map(c => `${XV('x')} = ${numH(c.v, true)}`).join(' or ');
        out.rule.push(trap('skip the check', 'check8', 'Done!', `${all}: the algebra is right, no check needed`,
          P('Squaring both sides can make <b>fake answers</b> (extraneous solutions): numbers that solve the squared equation but not the original one, because squaring hides a minus sign (2² and (−2)² are both 4). Every answer has to be checked in the original equation before it counts.'), 'keep8', 'both'));
      }
      if (e.pend && !e.pend.ok) out.traps.push(trap('plus or minus root', 'keep8', 'Keep: √ is ±', `${e.pend.l.out} could be negative too, so keep x = ${numH(e.pend.v, true)}`,
        P('The √ sign means the <b>principal</b> (non-negative) square root: √4 = 2, never −2. So the sides really are different, and this answer is a fake.'), 'keep8', 'both'));
      const ms0 = ms[0];
      if (ms0 && ms0.op === 'expand8') out.rule.push(C8('expand8', { a: e.R.a, b: e.R.b, form: 'each' }));
      if (ms0 && ms0.op === 'zero8') out.rule.push(trap('divide by x', 'zero8', `${DIV} ${XV('x')} both`, 'Divide both sides by x',
        P('Dividing both sides by x throws away the answer x = 0 and doesn\'t get rid of x². With an x² term, move everything to one side so it equals 0, then factor.'), 'div', 'both'));
      if (ms0 && (ms0.op === 'as8' || ms0.op === 'dv8') && e.L.t === 'rad') out.rule.push(C8('sq8', { p: e.L.idx }));
      if (ms0 && ms0.op === 'none8') out.rule.push(C8('sq8', { p: 2 }));
    }
    return out;
  }
  // The other cards of the stage, from which the wrong ones are drawn.
  function family(e, want) {
    const f = [];
    if (e.k8 === 'rx') {
      const pm = movesOf(e).find(m => m.op === 'pull8');
      const facs = rxFactors(e).filter(x => hasRoot(x.f));
      const n = (pm ? factorAt(e, pm.refs[0]) : (facs[0] || {}).f || Fc(1, 12)).n;
      const qs = new Set();
      if (pm) { qs.add(pm.q === 1 ? 4 : isqrt(pm.q) > 2 ? (isqrt(pm.q) - 1) ** 2 : 9); qs.add(isqrt(pm.q) + 1 > 1 ? (isqrt(pm.q) + 1) ** 2 : 4); }
      for (const q of [4, 9, 16, 25, 36]) if (qs.size < 4 && n % q) qs.add(q);
      qs.forEach(q => f.push(C8('pull8', { q, qx: pm ? pm.qx : 0 })));
      if (pm && pm.qx) f.push(C8('pull8', { q: pm.q, qx: pm.qx + 2 }), C8('pull8', { q: pm.q, qx: Math.max(0, pm.qx - 1) || 1 }));
      f.push(C8('mul8'), C8('comb8'));
      if (e.bot.length === 1) {
        const b = e.bot[0].n > 1 ? e.bot[0].n : 2, m = b / sqPart(b);
        f.push(C8('rat8', { m: m + 1 }), C8('rat8', { m: m === 2 ? 3 : 2 }));
        if (b !== m) f.push(C8('rat8', { m: b }));
        const d = e.bot[0].k;
        if (Math.abs(d) > 1 && e.bot[0].n === 1) f.push(C8('red8', { d: Math.abs(d) }), C8('red8', { d: Math.abs(d) + 1 }));
      }
      if (e.bot.length === 2) { const [A, B] = e.bot; f.push(C8('conj8', { f: [Fc(A.k, A.n), Fc(B.k, B.n)] }), C8('conj8', { f: [Fc(-A.k, A.n), Fc(B.k, B.n)] })); }
      if (!e.bot.length) f.push(C8('rat8', { m: 2 }), C8('red8', { d: 2 }));
      return f;
    }
    if (e.k8 === 're') {
      if (e.ask === 'eval') {
        const p = e.e ? Math.abs(e.e.n) : 1, q = e.e ? e.e.d : 1;
        f.push(C8('neg8'), C8('root8'), C8('pw8'));
        if (e.form === 'exp' && q > 1) f.push(C8('rad8', { rf: 'swap', b: e.b, p, q }), C8('rad8', { rf: 'mul', b: e.b, p, q }));
        f.push(C8('prod8'));
        return f;
      }
      if (e.ask === 'torad') return ['in', 'out', 'swap'].map(rf => C8('rw8', { rf, p: e.e.n, q: e.e.d })).concat([C8('rw8', { rf: 'expmul', p: e.e.n, q: e.e.d }), C8('pow8'), C8('root8')]);
      if (e.ask === 'toexp') return ['exp', 'expswap', 'expmul'].map(rf => C8('rw8', { rf, p: e.e.n, q: e.e.d })).concat([C8('rw8', { rf: 'swap', p: e.e.n, q: e.e.d }), C8('prod8'), C8('root8')]);
      return [C8('prod8'), C8('pow8'), C8('quot8'), C8('neg8'), C8('root8')];
    }
    // eq
    if (e.cands) {
      const out = [];
      e.cands.forEach(c => out.push(C8('check8', { v: c.v })));
      out.push(C8('keep8'), C8('rej8'), C8('none8'));
      return out;
    }
    const L = e.L, R = e.R;
    if (R.t === 'ev') { f.push(C8('neg8'), C8('root8'), C8('pw8'), C8('sq8', { p: 2 })); const s = R.re; if (s.form === 'exp' && s.e.d > 1) f.push(C8('rad8', { rf: 'swap', b: s.b, p: Math.abs(s.e.n), q: s.e.d })); return f; }
    if (L.t === 'rad' || L.t === 'pw') {
      const d = L.d, k = L.k;
      if (!fz(d)) f.push(C8('as8', { n: d }), C8('dv8', { n: fIs(fAbs(k), 1) ? F(2) : k }));
      else f.push(C8('as8', { n: fz(R.b || F(0)) ? F(1) : fNeg(R.b) }));
      if (!fIs(k, 1)) f.push(C8('dv8', { n: fNeg(k) }), C8('as8', { n: fNeg(k) }));
      if (L.t === 'rad') f.push(C8('sq8', { p: L.idx }), C8('sq8', { p: L.idx === 2 ? 3 : 2 }), C8('none8'));
      else f.push(C8('raise8', { e: L.e }), C8('raise8', { e: F(L.e.d, L.e.n) }), C8('dv8', { n: L.e }), C8('raise8', { e: fNeg(F(L.e.d, L.e.n)) }));
      return f;
    }
    if (R.t === 'sq') return ['right', 'each', 'flip', 'half'].map(form => C8('expand8', { a: R.a, b: R.b, form })).concat([C8('sq8', { p: 2 })]);
    if (R.t === 'quad' && (!fz(L.a) || !fz(L.b))) return [C8('zero8', { a: L.a, b: L.b }), C8('zero8', { a: fNeg(L.a), b: fNeg(L.b) }), C8('zero8', { a: L.a, b: F(0) }), C8('sq8', { p: 2 }), C8('none8')];
    if (R.t === 'quad') {
      const rs = quadRoots(R) || [F(1), F(2)], [a, b] = rs;
      const alts = [[fNeg(a), fNeg(b)], [fNeg(a), b], [a, fNeg(b)], [fAdd(a, F(1)), fSub(b, F(1))]];
      return [C8('fac8', { r1: a, r2: b }), ...alts.map(([x, y]) => C8('fac8', { r1: x, r2: y })), C8('none8')];
    }
    if (R.t === 'fac') return [C8('zp8'), C8('none8'), C8('expand8', { a: F(1), b: fNeg(R.r1), form: 'right' })];
    // lin = lin
    const out = [];
    if (!fz(R.a)) out.push(C8('as8x', { n: fNeg(R.a) }), C8('as8x', { n: R.a }), C8('as8', { n: fNeg(R.b) }));
    if (!fz(L.b)) out.push(C8('as8', { n: fNeg(L.b) }), C8('as8', { n: L.b }), C8('dv8', { n: fIs(fAbs(L.a), 1) ? F(2) : L.a }));
    if (!fIs(L.a, 1)) out.push(C8('dv8', { n: L.a }), C8('dv8', { n: fNeg(L.a) }), C8('as8', { n: fNeg(L.a) }));
    out.push(C8('sq8', { p: 2 }), C8('none8'));
    return out;
  }
  const alsoRight = (e, c) => movesOf(e).some(m => m.op === c.op && okParams(e, m, c, m.refs ? m.refs[0] : null) && (!m.refs || m.refs.length));
  function makeHand8(e, correct, size) {
    const tut = isTutorial(), L = lvl();
    const hand = [correct], seen = new Set([cardLabel(correct)]);
    const add = c => {
      if (hand.length >= size) return;
      const k = cardLabel(c); if (seen.has(k)) return;
      if (c.op !== 'trap' && (alsoRight(e, c) || rxAlsoRight(e, c))) return;
      seen.add(k); hand.push(c);
    };
    const sp = specials(e, correct);
    if (!tut && L >= 3) sp.traps.slice(0, 1).forEach(add);
    if (!tut) sp.rule.slice(0, DECOYS[L]).forEach(add);
    shuffle(family(e, correct)).forEach(add);
    for (const n of [2, 3, 5, 7, 4, 6]) add(C8('as8', { n: F(n) }));   // never short of cards
    return shuffle(hand);
  }
  // A pull card that is right on some other factor of the expression is right too.
  const rxAlsoRight = (e, c) => e.k8 === 'rx' && c.op === 'pull8' && rxFactors(e).some(x => legalPull(x.f, c));

  // ================================================================ wrong moves
  const S = (long, short, more) => (long ? P(more || short) : short);
  const opName = op => (CARD[op] ? CARD[op]({ q: 4, qx: 0, m: 2, d: 2, f: [Fc(1), Fc(1, 2)], rf: 'out', b: F(8), p: 2, n: F(1), e: F(2), a: F(1), r1: F(1), r2: F(2), v: F(1), form: 'right' }).kind : op);
  function why8(e, card, target, long) {
    const ref = refOf(target), ms = movesOf(e), want = ms[0];
    if (card.op === 'trap') return long ? card.why : 'That\'s a trap: it isn\'t true. Tap Why? to see why.';
    if (!card.a8) return S(long, 'That card doesn\'t fit here.');
    const next = want ? ` Next: ${opName(want.op)}.` : '';
    const same = ms.filter(m => m.op === card.op);
    if (same.length && same.some(m => okParams(e, m, card, m.refs ? m.refs[0] : null)) && ref && same.every(m => !m.refs || !m.refs.includes(ref)))
      return S(long, 'Right card, wrong place.', `That card is right, but not there.${e.k8 === 'rx' ? ' Drop it on the part it changes.' : ''}`);
    if (e.k8 === 'rx') return whyRx(e, card, ref, want, long, next);
    if (e.k8 === 're') return whyRe(e, card, want, long, next);
    return whyEq(e, card, want, long, next);
  }
  function whyRx(e, card, ref, want, long, next) {
    const f = factorAt(e, ref), ms = movesOf(e);
    const muls = e.top.some(t => t.f.length > 1);
    switch (card.op) {
      case 'pull8': {
        const q = card.q, qx = card.qx || 0;
        if (!f) return S(long, 'Drop it on a root.');
        if (!hasRoot(f)) return S(long, 'That part has no root.');
        if (q > 1 && !isSq(q)) return S(long, `${q} isn't a perfect square.`, `Only a perfect square factor comes out of a square root, because √(a²) = a. ${q} isn't a perfect square (4, 9, 16, 25, 36, … are).`);
        if (f.n % q) return S(long, `${q} doesn't go into ${f.n}.`, `To pull ${q} out, ${f.n} has to be ${q} times something. ${f.n} ÷ ${q} isn't a whole number. Look for a perfect square that divides ${f.n}: ${sqPart(f.n) > 1 ? sqPart(f.n) + ' does.' : 'there isn\'t one, so this root is already simplest.'}`);
        if (qx > f.xi) return S(long, `There aren't that many x's inside.`, `${R2(f.n)}: you can only pull out x's that are under the root.`);
        if (qx % 2) return S(long, `${xPart(qx, true)} isn't a perfect square.`, `x's come out of a square root in pairs: √(x²) = x, √(x⁴) = x². An odd power like ${xPart(qx, true)} can't come out whole: split it as ${xPart(qx - 1, true)} · x.`);
        return S(long, 'There\'s no square left to pull out there.');
      }
      case 'mul8':
        return S(long, 'There are no roots multiplied together here.', `Multiply roots joins √a · √b into √(ab). Nothing here is a product of two roots.${next}`);
      case 'comb8': {
        if (muls) return S(long, 'Multiply the roots first.');
        const roots = e.top.filter(t => hasRoot(t.f[0]));
        if (roots.length >= 2 && ms.some(m => m.op === 'pull8')) return S(long, 'Simplify each root first: then see if they match.', `Only like radicals combine: same number under the root. ${roots.map(t => fBody(t.f[0], true)).join(' and ')} don't match yet, but simplifying a root can make them match (√12 = 2√3, √27 = 3√3).`);
        return S(long, 'There are no like radicals to combine.', `Like radicals have exactly the same root: 2√3 and 5√3. Different roots, like √2 and √3, can't be combined, the same way x and y can't.${next}`);
      }
      case 'rat8': {
        if (!e.bot.length) return S(long, 'There\'s no fraction here.');
        const b = e.bot[0];
        if (e.bot.length === 2) return S(long, 'Two terms on the bottom: use the conjugate.', `Multiplying by one root doesn't clear a root from a two-term bottom. Multiply by the conjugate: the same two terms with the middle sign flipped.`);
        if (!hasRoot(b)) return S(long, 'The bottom has no root left.');
        if (muls) return S(long, 'Multiply the roots on top first.');
        return S(long, `${R2(b.n)} ${TIMES} ${R2(card.m)} = ${R2(b.n * card.m)}: still a root.`, `Rationalizing works when the bottom becomes a perfect square: ${R2(b.n)} · ${R2(b.n / sqPart(b.n))} = ${R2(b.n * (b.n / sqPart(b.n)))} = ${isqrt(b.n * (b.n / sqPart(b.n)))}. With ${R2(card.m)}, the bottom would be ${R2(b.n * card.m)}, which isn't a whole number.`);
      }
      case 'conj8':
        if (e.bot.length !== 2) return S(long, 'The conjugate is for a bottom with two terms.');
        return S(long, 'That isn\'t the conjugate.', `The conjugate of ${sumText(botTerms(e), true)} is ${sumText(conjOf(e.bot).map(x => Tm(x)), true)}: the same two terms with the sign between them flipped. Then (a − b)(a + b) = a² − b² and the root squares away. Multiplying by the same expression would leave a middle term with a root.`);
      case 'red8': {
        if (!e.bot.length) return S(long, 'There\'s no fraction to reduce.');
        if (e.bot.some(hasRoot)) return S(long, 'Clear the root from the bottom first.');
        const g = rxGcd(e);
        if (g === 1) return S(long, 'The fraction is already in lowest terms.', `To reduce, every number in front on top <b>and</b> the bottom must share a factor. Here they don't.`);
        return S(long, `${card.d} doesn't go into every number.`, `Every term on top and the bottom must be divisible by it. The biggest number that works is ${g}.`);
      }
    }
    return S(long, 'That card doesn\'t fit here.', `That isn't a move for simplifying a radical.${next}`);
  }
  function whyRe(e, card, want, long, next) {
    if (e.ask === 'eval') {
      const q = e.e ? e.e.d : 1;
      switch (card.op) {
        case 'neg8': return e.form === 'exp' && e.e.n > 0 ? S(long, 'The exponent isn\'t negative.') : S(long, 'There\'s no negative exponent here.');
        case 'rad8':
          if (e.form !== 'exp') return S(long, 'It\'s already written as a root.');
          if (e.e.n < 0) return S(long, 'Deal with the negative exponent first: put it under 1.', `${parenF(e.b, true)}${supFH(e.e)} = 1/${parenF(e.b, true)}${supFH(fNeg(e.e))}. Flip it first, then the exponent is positive.`);
          if (card.rf === 'swap') return S(long, 'The bottom of the exponent is the root, the top is the power.', `b${supFH(F(2, 3))} = (∛b)², not (√b)³. The denominator says which root (3 → cube root), the numerator says which power. So ${parenF(e.b, true)}${supFH(e.e)} = ${radFormHtml({ rf: 'out', b: e.b, p: e.e.n, q })}.`);
          if (card.rf === 'mul') return S(long, 'An exponent isn\'t a multiplication.', `${parenF(e.b, true)}${supFH(e.e)} doesn't mean ${numH(e.b, true)} ${TIMES} ${fracText(e.e)}. A fraction exponent p/q means: take the q-th root, then raise to the p-th power.`);
          return S(long, 'Not like that.');
        case 'root8':
          if (e.form === 'exp') return S(long, 'Write it as a root first.', `${parenF(e.b, true)}${supFH(e.e)} has no root sign yet. Rewrite the fraction power as a root, then work it out.`);
          if (e.form === 'in' || e.form === 'pv') return S(long, e.form === 'pv' ? 'The root is done: now the power.' : 'Work out the power inside first.');
          return S(long, 'There\'s no root left.');
        case 'pw8':
          if (e.form === 'exp') return S(long, e.e.n < 0 ? 'Put the negative exponent under 1 first.' : 'Rewrite it as a root first.', `A fraction power is a root and a power together. Split it into a root and a power first, then work them out.`);
          if (e.form === 'out' || e.form === 'root') return S(long, 'Take the root first: it\'s on the outside.', `In ${evHtml(e, true)} the root is applied first. Roots first keeps the numbers small: ∛8 = 2, then 2² = 4.`);
          return S(long, 'There\'s no power left to work out.');
      }
      return S(long, 'That card doesn\'t fit here.', `Work out the number one step at a time.${next}`);
    }
    if (e.ask === 'torad' || e.ask === 'toexp') {
      if (card.op !== 'rw8') return S(long, 'Just rewrite it: nothing needs working out.');
      const p = e.e.n, q = e.e.d;
      if (card.rf === 'swap' || card.rf === 'expswap') return S(long, 'The root goes on the bottom of the exponent.', `x${supFH(F(p, q))} = ${rwFormHtml({ rf: 'in', p, q })}: the denominator (${q}) is the root, the numerator (${p}) is the power. Swapping them gives a different number.`);
      if (card.rf === 'expmul') return S(long, 'A root isn\'t multiplying the exponent.', `A ${ORD(q)} root is the power 1/${q}, so ${rwFormHtml({ rf: 'in', p, q })} = x${supFH(F(p, q))}: the exponent is divided by ${q}, not multiplied.`);
      return S(long, e.ask === 'torad' ? 'The question asks for a root.' : 'The question asks for an exponent.');
    }
    switch (card.op) {
      case 'prod8': return e.g ? S(long, 'Open the power of a power first.') : S(long, 'There\'s nothing left to multiply on one side.');
      case 'pow8': return S(long, 'There\'s no power of a power here.', `The Power rule is for (x${supH(2)})${supH(3)}: a power outside brackets. Nothing here has one.${next}`);
      case 'quot8': return e.g || e.num.length > 1 || e.den.length > 1 ? S(long, 'Combine each side first.') : S(long, 'There\'s nothing on the bottom.');
    }
    return S(long, 'That card doesn\'t fit here.', `Use the exponent rules: the same ones as whole-number exponents.${next}`);
  }
  function whyEq(e, card, want, long, next) {
    const L = e.L, R = e.R;
    if (e.cands) {
      if (e.pend) {
        const { l, r, ok, v } = e.pend;
        if (card.op === 'keep8') return S(long, `${l.out} and ${r.out} aren't equal.`, `With ${XV('x')} = ${numH(v, true)} the left side is ${l.out}${l.kind === 'undef' ? ' (not a real number: no square root of a negative)' : ''} and the right side is ${r.out}. They differ, so ${XV('x')} = ${numH(v, true)} is a <b>fake answer</b> (extraneous): it solves the squared equation, not the original.`);
        if (card.op === 'rej8') return S(long, `${l.out} = ${r.out}: it works.`, `With ${XV('x')} = ${numH(v, true)} both sides come to ${l.out}. It makes the original equation true, so it's a real answer: keep it.`);
        return S(long, 'Decide first: does it check out?');
      }
      if (card.op === 'check8') return S(long, 'That answer is already checked.');
      if (card.op === 'keep8' || card.op === 'rej8') return S(long, 'Check an answer first.');
      if (card.op === 'none8') return S(long, 'Check the answers before deciding.', 'There are answers to check. Only if every one of them fails is there no solution.');
      return S(long, 'Now check each answer in the original equation.');
    }
    if (card.op === 'check8') return S(long, 'There\'s no answer to check yet.');
    if (card.op === 'keep8' || card.op === 'rej8') return S(long, 'There\'s nothing to keep or reject yet.');
    if (R.t === 'ev') return whyRe(R.re, card, want, long, next);
    if (L.t === 'rad') {
      const iso = fz(L.d) && fIs(L.k, 1);
      if (card.op === 'sq8') {
        if (!iso) return S(long, 'Get the root alone first.', `Squaring only gets rid of the root when the root is <b>alone</b> on its side. (${nodeText(L, true)})² isn't just the inside: the other parts get multiplied in too. First undo ${fz(L.d) ? 'the number in front' : 'the + or − part'}.`);
        if (card.p !== L.idx) return S(long, L.idx === 3 ? 'It\'s a cube root: cube both sides.' : 'It\'s a square root: square both sides.', `(${rootOf(L.idx, 'u', true)})${supH(L.idx)} = u. Undo a ${ORD(L.idx)} root with the power ${L.idx}.`);
        return S(long, 'A square root can\'t equal a negative number.', `${rootOf(2, 'u', true)} is never negative, so ${nodeText(L, true)} = ${nodeText(R, true)} has no solution. (Squaring would hide the minus sign and give a fake answer.)`);
      }
      if (card.op === 'none8') {
        if (!iso) return S(long, 'Get the root alone first, then decide.');
        if (L.idx === 3) return S(long, 'A cube root can be negative.', `∛(−8) = −2, so a cube root can equal a negative number. Cube both sides.`);
        return S(long, `${nodeText(R, true)} isn't negative, so there may be a solution.`, `A square root can equal 0 or a positive number. Square both sides and solve.`);
      }
      if (card.op === 'as8' || card.op === 'dv8') {
        if (!fz(L.d) && card.op === 'dv8') return S(long, `Undo the ${L.d.n < 0 ? 'subtraction' : 'addition'} first.`, `Like any equation, undo + and − first, then × and ÷. Dividing now would make fractions.`);
        if (!fz(L.d)) return S(long, `That doesn't cancel the ${signedN(L.d, true)}.`, `To get the root alone, undo ${signedN(L.d, true)}: ${L.d.n < 0 ? 'add' : 'subtract'} ${numH(fAbs(L.d), true)} on both sides.`);
        if (!fIs(L.k, 1)) return S(long, `Divide by ${numH(L.k, true)}, the number in front of the root.`);
        return S(long, 'The root is already alone.');
      }
      return S(long, 'That card doesn\'t fit here.', `Get the root alone, then undo it.${next}`);
    }
    if (L.t === 'pw') {
      if (card.op === 'raise8') {
        if (!fz(L.d) || !fIs(L.k, 1)) return S(long, `Get ${xPow(L.e, true)} alone first.`);
        return S(long, `Use the reciprocal power: ${fracText(F(L.e.d, L.e.n))}.`, `(${xPow(L.e, true)})${supFH(card.e)} = x${supFH(fMul(L.e, card.e))}. To get x¹, multiply the exponent by its reciprocal: ${fracText(L.e)} · ${fracText(F(L.e.d, L.e.n))} = 1.`);
      }
      if (card.op === 'dv8' && !fz(L.d)) return S(long, 'Undo the + or − first.');
      if (card.op === 'dv8' && fEq(card.n, L.e)) return S(long, 'Dividing doesn\'t undo a power.', `Dividing by ${fracText(L.e)} changes the number in front, not the exponent. To undo the power ${fracText(L.e)}, raise both sides to ${fracText(F(L.e.d, L.e.n))}.`);
      if (card.op === 'as8' || card.op === 'dv8') return S(long, 'That doesn\'t get x alone.');
      return S(long, 'That card doesn\'t fit here.', `Get the power alone, then raise both sides to the reciprocal power.${next}`);
    }
    if (card.op === 'none8') return S(long, 'Keep solving: there may well be a solution.');
    if (card.op === 'sq8') return S(long, 'There\'s no root left to undo.');
    if (R.t === 'sq') return card.op === 'expand8' ? S(long, 'That isn\'t (a + b)².', `(a + b)² = a² + 2ab + b²: there are <b>three</b> terms, and the middle one is 2ab. ${nodeText(R, true)} = ${expandHtml({ a: R.a, b: R.b, form: 'right' })}.`) : S(long, `Expand ${nodeText(R, true)} first.`);
    if (R.t === 'quad' && (!fz(L.a) || !fz(L.b))) {
      if (card.op === 'zero8') return S(long, 'Subtract the whole left side.', `To get 0 on the left, subtract exactly ${linText(L, true)} from both sides.`);
      return S(long, 'Get 0 on one side first.', `With an x² term, solve by factoring: first move everything to one side so it equals 0.${next}`);
    }
    if (R.t === 'quad') {
      if (card.op === 'fac8') {
        const rs = quadRoots(R);
        return S(long, 'Those factors don\'t multiply back to it.', rs ? `Look for two numbers that multiply to ${fracText(R.c0)} and add to ${fracText(R.c1)}: ${fracText(fNeg(rs[0]))} and ${fracText(fNeg(rs[1]))}. So it's ${nodeText({ t: 'fac', r1: rs[0], r2: rs[1] }, true)}.` : '');
      }
      return S(long, 'Factor it.');
    }
    if (R.t === 'fac') return S(long, 'Use the zero product rule: each factor = 0.');
    if (card.op === 'as8' || card.op === 'as8x' || card.op === 'dv8') {
      if (!fz(R.a) && card.op !== 'as8x') return S(long, 'Get the x terms on one side first.');
      if (!fz(R.a)) return S(long, `Subtract ${linText(Lin(R.a, 0), true)} to clear x from the right.`);
      if (!fz(L.b) && card.op === 'dv8') return S(long, 'Undo the + or − first.');
      return S(long, 'That doesn\'t get x alone.', `Undo what's attached to x: + or − first, then × or ÷.${next}`);
    }
    return S(long, 'That card doesn\'t fit here.', `Solve for x.${next}`);
  }
  const isCorrect = (cur, card, target) => correct8(cur.state, card, target);
  const whyWrong = (cur, card, target) => why8(cur.state, card, target, false);
  function explain8({ state: e, card, ref }) {
    if (!e || !e.k8 || !card) return null;
    return why8(e, card, ref, true);
  }
  if (typeof registerWhy === 'function') registerWhy(explain8);

  // ================================================================ rendering
  const W = h => `<span class="w8">${h}</span>`;
  const sym = (html, cls = '') => { const d = document.createElement('div'); d.className = 'tok a4 s8 ' + cls; d.innerHTML = html; return d; };
  const rowEl = els => { const r = document.createElement('span'); r.className = 'row4'; els.forEach(x => r.appendChild(x)); return r; };
  function sumEls(terms, refFn) {
    const out = [];
    terms.forEach((t, i) => {
      const sg = termSign(t);
      if (i) out.push(sym(sg < 0 ? MINUS : '+')); else if (sg < 0) out.push(sym(MINUS, 'lead8'));
      t.f.forEach((f, j) => { if (j) out.push(sym('·')); out.push(TOK(W(fBody(f, true)), 'f8', refFn(i, j), 'f8')); });
    });
    return out;
  }
  function renderRx(e) {
    const el = $('equation');
    const top = sumEls(e.top, fref);
    if (!e.bot.length) { top.forEach(x => el.appendChild(x)); return; }
    const w = document.createElement('span'); w.className = 'n4 frac4 frac8';
    w.append(rowEl(top), TOK('<span class="bar4"></span>', 'bar', 'bar'), rowEl(sumEls(botTerms(e), i => 'b' + i)));
    el.appendChild(w);
  }
  function renderEq(e) {
    const el = $('equation');
    if (!e.cands) {
      el.appendChild(TOK(W(nodeText(e.L, true)), 'l8', 'L', 'side8'));
      el.appendChild(K.EQTOK());
      el.appendChild(TOK(W(nodeText(e.R, true)), 'r8', e.R.t === 'ev' ? 'V' : 'R', 'side8'));
      if (e.none) { const col = colWrap(el); col.appendChild(rowEl([sym('No solution', 'ns8')])); }
      return;
    }
    const col = document.createElement('div'); col.className = 'col8';
    col.appendChild(rowEl([sym('Check in the original:', 'lab8'), TOK(W(origText(e, true)), 'o8', 'O', 'o8')]));
    const cs = [];
    e.cands.forEach((c, i) => { if (i) cs.push(sym('or', 'or8')); cs.push(TOK(W(`${XV('x')} = ${numH(c.v, true)}`), 'c8', 'c' + i, 'c8 st8-' + c.st + (e.pend && e.pend.i === i ? ' now8' : ''))); });
    col.appendChild(rowEl(cs));
    if (e.pend) {
      const { l, r } = e.pend;
      col.appendChild(rowEl([TOK(`<div class="sub8 nonum">${l.sub} ≟ ${r.sub}</div><div class="val8">${l.out}${l.kind === 'undef' ? ' <small>(not real)</small>' : ''} ≟ ${r.out}</div>`, 'p8', 'C', 'p8')]));
    } else if (eqDone(e)) col.appendChild(rowEl([sym(eqAnswer(e, true), 'fin8')]));
    el.appendChild(col);
  }
  function colWrap(el) {   // puts what's in the equation in a column so a line can go under it
    const kids = [...el.childNodes], col = document.createElement('div'); col.className = 'col8';
    col.appendChild(rowEl(kids)); el.appendChild(col); return col;
  }
  function fit8() {
    const el = $('equation'); if (!el.classList.contains('ex8')) return;
    el.style.removeProperty('--eqSize');
    const base = parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--eqSize')) || 56;
    let size = Math.round(base * (el.querySelector('.col8') ? 0.7 : 0.9));
    el.style.setProperty('--eqSize', size + 'px');
    const maxH = Math.max(90, ($('arena').clientHeight || 400) * (innerWidth <= 640 ? 0.45 : 0.55));
    for (let i = 0; i < 14; i++) {
      const availW = ($('arena').clientWidth || innerWidth) * 0.92, needW = Math.max(el.scrollWidth, el.getBoundingClientRect().width);
      const needH = Math.max(0, ...[...el.children].map(k => k.offsetHeight || 0));
      const f = Math.min(availW && needW > availW ? availW / needW : 1, needH > maxH ? maxH / needH : 1);
      if (f >= 0.99) break;
      size = Math.max(12, Math.floor(size * Math.min(0.97, f)));
      el.style.setProperty('--eqSize', size + 'px');
      if (size <= 12) break;
    }
  }
  function render(e) {
    const el = $('equation'); if (typeof clearNotes === 'function') clearNotes();
    el.innerHTML = ''; el.classList.add('a4', 'ex8');
    if (e.k8 === 'rx') renderRx(e);
    else if (e.k8 === 're') el.appendChild(TOK(W(reHtml(e, true)), 'v8', 'V', 'v8'));
    else renderEq(e);
    fit8();
  }
  function clear() {
    const el = $('equation'); if (el) el.classList.remove('ex8');
    document.querySelectorAll('.fly8').forEach(n => n.remove());
  }
  const fontPx = () => parseFloat(getComputedStyle($('equation')).fontSize);
  function prefit(s, ns) {
    render(ns); const after = fontPx(); render(s); const before = fontPx();
    if (before > after + 0.5) {
      const el = $('equation'), c = parseFloat(el.style.getPropertyValue('--eqSize')) || 56;
      el.style.setProperty('--eqSize', Math.floor(c * after / before) + 'px');
    }
  }
  addEventListener('resize', () => { if (!cur || !cur.act8 || (typeof animating !== 'undefined' && animating)) return; fit8(); });

  // ================================================================ prompts
  const PR = {
    simp: ['Simplify.', 'Simplify the radical.', 'Write in simplest radical form.'],
    rat: ['Simplify. Rationalize the denominator.', 'Rationalize the denominator.', 'Write in simplest form with no root in the denominator.'],
    eval: ['Evaluate.', 'Find the value.', 'Evaluate without a calculator.'],
    torad: ['Write using a radical.', 'Rewrite in radical form.', 'Write the expression as a root.'],
    toexp: ['Write using a rational exponent.', 'Rewrite with a fraction exponent.', 'Write the root as a power of x.'],
    rules: ['Simplify. Write with a rational exponent.', 'Simplify using the exponent rules.', 'Simplify.'],
    solve: ['Solve for x.', 'Solve the equation.', 'Solve.'],
    check: ['Solve. Check for extraneous solutions.', 'Solve and check your answers.', 'Solve the radical equation. Check each answer.'],
  };
  const lastPr = {};
  function promptKey(s) {
    if (s.k8 === 'rx') return s.bot.length ? 'rat' : 'simp';
    if (s.k8 === 're') return s.ask;
    return s.L.t === 'rad' && s.L.idx === 2 ? 'check' : 'solve';
  }
  function prompt(s) {
    const key = promptKey(s), all = PR[key];
    const fresh = all.filter(t => t !== lastPr[key]);
    return (lastPr[key] = pick(fresh.length ? fresh : all));
  }

  // ================================================================ animations
  // The game's timing: the written operation fades in fast, hold() (scaled by the speed setting), the
  // calculation runs fast (quick()), the result shows, hold(). Each operation has its own motion.
  const tk = ref => $('equation').querySelector(`.tok[data-ref="${ref}"]`);
  async function result(ns, refs, cap) { render(ns); refs.forEach(r => kickClass(tk(r), 'pop')); if (cap) caption(cap); await quick(300); await hold(); }
  async function written(html, anchors, cap, cls = 'lift4') {
    if (cap) caption(cap);
    const n = note(html, anchors.filter(Boolean)); n.classList.add(cls, 'n8');
    await quick(150); await hold();
    return n;
  }
  async function both(html, cap) {   // the same operation written under both sides
    if (cap) caption(cap);
    const ns = [tk('L'), tk('R') || tk('V')].filter(Boolean).map(a => { const n = note(html, [a]); n.classList.add('lift4', 'n8'); return n; });
    await quick(150); await hold();
    ns.forEach(dropNote);
  }
  function flyRect(html, from, toEl, ms = 480) {
    if (!from || !toEl) return quick(1);
    const dest = toEl.getBoundingClientRect();
    const chip = document.createElement('div'); chip.className = 'fly4 fly8'; chip.innerHTML = html;
    chip.style.left = (from.left + from.width / 2) + 'px'; chip.style.top = (from.top + from.height / 2) + 'px';
    document.body.appendChild(chip); void chip.offsetWidth;
    chip.style.transform = `translate(${dest.left + dest.width / 2 - from.left - from.width / 2}px, ${dest.top + dest.height / 2 - from.top - from.height / 2}px)`;
    return quick(ms).then(() => chip.remove());
  }
  const moveAt = (s, c, ref) => legalMove(s, c, ref) || movesOf(s).find(m => m.op === c.op);
  // ---------------------------------------------------------------- stage 36
  async function animPull(c, s, ns, ref) {
    const m = moveAt(s, c, ref), r0 = ref && m.refs.includes(ref) ? ref : m.refs[0], f = factorAt(s, r0), t = tk(r0);
    const q = c.q, qx = c.qx || 0, rest = Fc(1, f.n / q, f.xi - qx);
    const qIn = (q > 1 ? String(q) : '') + xPart(qx, true), rIn = (rest.n > 1 ? String(rest.n) : '') + xPart(rest.xi, true);
    mark([t], 'hot8');
    const n = await written(rootOf(2, qIn + (rIn ? ' · ' + rIn : ''), true), [t], `${qIn.replace(/<[^>]+>/g, '')} is a perfect square, so split the root: √(a · b) = √a · √b`);
    dropNote(n);
    const out = (q > 1 ? String(isqrt(q)) : '') + xPart(qx / 2, true);
    const from = t.getBoundingClientRect();
    render(ns);
    const dest = tk(r0);
    if (dest) dest.style.opacity = '0.25';
    await flyRect(out, from, dest);
    if (dest) { dest.style.opacity = ''; kickClass(dest, 'pop'); }
    caption(`${rootOf(2, qIn, false).replace(/<[^>]+>/g, '')} = ${out.replace(/<[^>]+>/g, '')} comes out in front of the root`);
    await quick(250); await hold();
  }
  async function animMul(c, s, ns, ref) {
    const m = moveAt(s, c, ref), fs = s.top[m.ti].f, toks = m.refs.map(tk);
    mark(toks, 'hot8');
    const n = await written(`${fs.some(f => Math.abs(f.k) > 1) ? '(' + fs.map(f => Math.abs(f.k)).join(' · ') + ')' : ''}${rootOf(2, fs.map(f => (f.n > 1 ? f.n : '') + xPart(f.xi, true)).join(' · '), true)}`, toks,
      'Multiply roots: √a · √b = √(ab), and the numbers in front multiply too');
    dropNote(n);
    toks.slice(1).forEach(x => x && x.classList.add('slide8'));
    await removeTok(toks.slice(1));
    await result(ns, [m.refs[0]], `One root: ${fBody(ns.top[m.ti].f[0], false)}`);
  }
  async function animComb(c, s, ns, ref) {
    const m = moveAt(s, c, ref), toks = m.refs.map(tk), f0 = s.top[m.idx[0]].f[0];
    const ks = m.idx.map(i => s.top[i].f[0].k), sum = ks.reduce((a, b) => a + b, 0);
    mark(toks, 'hot8');
    const rootPart = fBody(Fc(1, f0.n, f0.xi, f0.xo), true);
    const n = await written(`(${ks.map((k, i) => (i ? (k < 0 ? ` ${MINUS} ` : ' + ') : k < 0 ? MINUS : '') + Math.abs(k)).join('')})${rootPart}`, toks, 'Like radicals: same root, so add the numbers in front (like 2x + 5x = 7x)');
    dropNote(n);
    await removeTok(toks.slice(1));
    await result(ns, sum ? [m.refs[0]] : [], sum ? `= ${sum === 1 ? '' : sum === -1 ? MINUS : numText(sum)}${fBody(Fc(1, f0.n, f0.xi, f0.xo), false)}` : 'They cancel out: 0');
  }
  const topToks = () => [...$('equation').querySelectorAll('.tok[data-ref^="t"]')];
  async function animRat(c, s, ns) {
    const b = s.bot[0], m = c.m;
    caption(`Multiply the top and the bottom by ${R2(m, false)}: that's multiplying by 1, so the value stays the same`);
    const n1 = note(`${TIMES} ${R2(m)}`, topToks()), n2 = note(`${TIMES} ${R2(m)}`, [tk('b0')]);
    [n1, n2].forEach(n => n.classList.add('lift4', 'n8'));
    await quick(150); await hold();
    dropNote(n1); dropNote(n2);
    mark([tk('b0')], 'hot8');
    await result(ns, ['b0'], `${fBody(b, false)} · ${R2(m, false)} = ${fBody(Fc(b.k, b.n * m), false)} = ${b.k * isqrt(b.n * m)}: no root on the bottom any more`);
  }
  async function animConj(c, s, ns) {
    const cj = sumText(conjOf(s.bot).map(x => Tm(x)), true);
    caption(`Multiply top and bottom by the conjugate, ${sumText(conjOf(s.bot).map(x => Tm(x)), false)}: same terms, middle sign flipped`);
    const n1 = note(`${TIMES} (${cj})`, topToks()), n2 = note(`${TIMES} (${cj})`, [tk('b0'), tk('b1')]);
    [n1, n2].forEach(n => n.classList.add('lift4', 'n8'));
    await quick(150); await hold();
    dropNote(n1); dropNote(n2);
    const [A, B] = s.bot;
    await result(ns, ['b0'], `(a ${MINUS} b)(a + b) = a² ${MINUS} b²: ${A.k * A.k * A.n} ${MINUS} ${B.k * B.k * B.n} = ${A.k * A.k * A.n - B.k * B.k * B.n}, and the roots are gone from the bottom`);
  }
  async function animRed(c, s, ns) {
    caption(`Every number on top and the bottom share ${c.d}: divide them all by ${c.d}`);
    const n1 = note(`${DIV} ${c.d}`, topToks()), n2 = note(`${DIV} ${c.d}`, [tk('b0')]);
    [n1, n2].forEach(n => n.classList.add('lift4', 'n8'));
    await quick(150); await hold();
    dropNote(n1); dropNote(n2);
    await result(ns, topToks().length ? [] : [], `Reduced: ${rxText(ns, false)}`);
    topToks().forEach(t => kickClass(t, 'pop'));
  }
  // ---------------------------------------------------------------- stage 37
  const evOf = s => (s.k8 === 'eq' ? s.R.re : s);
  const nsEv = ns => (ns.k8 === 'eq' ? (ns.R.t === 'ev' ? ns.R.re : null) : ns);
  const evTok = () => tk('V');
  async function animNeg(c, s, ns) {
    const e = evOf(s), t = evTok();
    mark([t], 'hot8'); t.classList.add('spin');
    const n = await written(`1 / ${parenF(e.b, true)}${supFH(fNeg(e.e))}`, [t], 'Negative exponent: b⁻ⁿ = 1/bⁿ. It goes under 1 and the exponent turns positive');
    dropNote(n); t.classList.remove('spin');
    await result(ns, ['V'], `${parenF(e.b, false)}${supFT(e.e)} = 1/${parenF(e.b, false)}${supFT(fNeg(e.e))}`);
  }
  async function animRad(c, s, ns) {
    const e = evOf(s), t = evTok(), p = e.e.n, q = e.e.d;
    mark([t], 'hot8');
    const sup = t.querySelector('sup.e8'); if (sup) sup.classList.add('lift8');
    const n = await written(`${q} → ${ORD(q)} root${p > 1 ? `, ${p} → power ${p}` : ''}`, [t], `A fraction exponent p/q: the bottom (${q}) is the root, the top (${p}) is the power`);
    dropNote(n);
    await result(ns, ['V'], `${evHtml(e, false)} = ${evHtml(nsEv(ns) || { ...e, form: 'out' }, false)}`);
  }
  async function animRoot(c, s, ns) {
    const e = evOf(s), t = evTok(), q = e.e.d;
    const inner = e.form === 'out' ? e.b : e.c, r = rootF(inner, q);
    mark([t], 'hot8');
    const n = await written(`${rootOf(q, numH(inner, true), true)} = ${numH(r, true)}`, [t], `The ${ORD(q)} root of ${fracText(inner)}: ${parenF(r, false)}${supT(q)} = ${fracText(inner)}, so it's ${fracText(r)}`);
    dropNote(n);
    t.classList.add('crack8'); await quick(300);
    await result(ns, ['V', 'R'], '');
  }
  async function animPw(c, s, ns) {
    const e = evOf(s), t = evTok(), p = e.e ? Math.abs(e.e.n) : 1;
    const base = e.form === 'pv' ? e.r : e.b, pp = e.form === 'exp' ? e.e.n : p, v = powF(base, pp);
    mark([t], 'hot8');
    const n = await written(`${parenF(base, true)}${supH(pp)} = ${numH(v, true)}`, [t], `${parenF(base, false)}${supT(pp)} = ${Array(pp).fill(parenF(base, false)).join(' · ')} = ${fracText(v)}`);
    dropNote(n);
    await result(ns, ['V', 'R'], '');
  }
  async function animRw(c, s, ns) {
    const t = evTok(), p = s.e.n, q = s.e.d;
    mark([t], 'hot8');
    const n = await written(`${XV('x')}${supFH(F(p, q))} = ${rwFormHtml({ rf: 'in', p, q })} = ${rwFormHtml({ rf: 'out', p, q })}`, [t], `The bottom of the exponent (${q}) is the root, the top (${p}) is the power`);
    dropNote(n);
    await result(ns, ['V'], `Rewritten: ${rwHtml(ns, false)}`);
  }
  async function animRule(c, s, ns) {
    const t = evTok(); mark([t], 'hot8');
    let html, cap;
    if (c.op === 'pow8') { html = `${fracText(s.g.e)} ${TIMES} ${s.g.o} = ${fracText(fMul(s.g.e, F(s.g.o)))}`; cap = 'Power rule: a power of a power multiplies the exponents'; }
    else if (c.op === 'prod8') { const l = s.num.length > 1 ? s.num : s.den; html = `${l.map(fracText).join(' + ')} = ${fracText(l.reduce(fAdd))}`; cap = 'Product rule: same base multiplied, so add the exponents (find a common denominator)'; }
    else { html = `${fracText(s.num[0])} ${MINUS} ${fracText(s.den[0])} = ${fracText(fSub(s.num[0], s.den[0]))}`; cap = 'Quotient rule: same base divided, so subtract the exponents (top minus bottom)'; }
    const n = await written(html, [t], cap); dropNote(n);
    await result(ns, ['V'], `= ${rulesHtml(ns, false)}`);
  }
  // ---------------------------------------------------------------- equations
  async function animAs(c, s, ns) {
    const t = c.op === 'as8x' ? (c.n.n < 0 ? MINUS : '+') + ' ' + linText(Lin(fAbs(c.n), 0), true) : signedN(c.n, true);
    await both(t, cardText(c));
    await result(ns, ['L', 'R'], c.op === 'as8x' ? 'The x terms are on one side now' : 'Both sides changed the same way, so they stay equal');
  }
  async function animDv(c, s, ns) {
    caption(cardText(c));
    const ns2 = [tk('L'), tk('R')].filter(Boolean).map(a => { const n = note(numH(c.n, true), [a], { bar: true }); n.classList.add('n8'); return n; });
    await quick(150); await hold();
    ns2.forEach(dropNote);
    await result(ns, ['L', 'R'], 'Each side divided by the same number');
  }
  async function animSq(c, s, ns) {
    const p = c.p, R = s.R;
    await both(`( )${supH(p)}`, p === 3 ? 'Cube both sides: a cube undoes a cube root' : 'Square both sides: a square undoes a square root');
    const rs = $('equation').querySelectorAll('.rs8, .ri8'); rs.forEach(x => x.classList.add('peel8'));
    await quick(420);
    await result(ns, ['L', 'R'], isConst(R) ? `(${rootOf(p, 'u', false)})${supT(p)} = u, and ${parenF(R.b, false)}${supT(p)} = ${fracText(powF(R.b, p))}` : `(${rootOf(p, 'u', false)})${supT(p)} = u: the root is gone${p === 2 ? '. Squaring can add fake answers, so every answer gets checked at the end' : ''}`);
  }
  async function animRaise(c, s, ns) {
    await both(`( )${supFH(c.e)}`, `Raise both sides to the ${fracText(c.e)} power: ${fracText(s.L.e)} · ${fracText(c.e)} = 1, so x is left alone`);
    await result(ns, ['L', 'V'], `x = ${fracText(s.R.b)} to the ${fracText(c.e)}: now work out that number`);
  }
  async function animExpand(c, s, ns) {
    const t = tk('R'), lin = linText(s.R, true);
    mark([t], 'hot8');
    const n = await written(`(${lin})(${lin})`, [t], `Squaring means times itself: (a + b)² = a² + 2ab + b², three terms`);
    dropNote(n);
    await result(ns, ['R'], `= ${nodeText(ns.R, false)}`);
  }
  async function animZero(c, s, ns) {
    const w = linText(Lin(c.a, c.b), true);
    await both(`${MINUS} ${fz(c.a) || fz(c.b) ? w : '(' + w + ')'}`, 'Move everything to one side so it equals 0: then the quadratic can be factored');
    await result(ns, ['L', 'R'], `0 = ${nodeText(ns.R, false)}`);
  }
  async function animFac(c, s, ns) {
    const t = tk('R'), R = s.R, a = fNeg(c.r1), b = fNeg(c.r2);
    mark([t], 'hot8');
    const n = await written(`${fracText(a)} · ${fracText(b)} = ${fracText(R.c0)}, ${fracText(a)} + ${fracText(b)} = ${fracText(R.c1)}`, [t], 'Find two numbers that multiply to the last number and add to the middle one');
    dropNote(n);
    await result(ns, ['R'], `= ${nodeText(ns.R, false)}`);
  }
  async function animZp(c, s, ns) {
    const t = tk('R'), R = s.R;
    mark([t], 'hot8');
    const f1 = linText(Lin(1, fNeg(R.r1)), true), f2 = linText(Lin(1, fNeg(R.r2)), true);
    const n = await written(`${f1} = 0 or ${f2} = 0`, [t], 'Zero product: if two factors multiply to 0, one of them is 0');
    dropNote(n);
    await result(ns, ['c0', 'c1'], 'Two possible answers. The equation was squared, so each must be checked in the original');
  }
  async function animCheck(c, s, ns) {
    const i = s.cands.findIndex(o => fEq(o.v, c.v)), from = tk('c' + i), to = tk('O');
    mark([from], 'hot8');
    if (from && to) await flyRect(`${XV('x')} = ${numH(c.v, true)}`, from.getBoundingClientRect(), to, 520);
    render(ns);
    const p = tk('C'), val = p && p.querySelector('.val8');
    if (val) val.style.visibility = 'hidden';
    caption(`Put ${'x'} = ${fracText(c.v)} into the original equation`);
    await quick(200); await hold();
    if (val) { val.style.visibility = ''; kickClass(val, 'pop'); }
    caption('Work out each side. Are they equal?');
    await quick(250); await hold();
  }
  async function animVerdict(c, s, ns) {
    const i = s.pend.i, t = tk('c' + i), keep = c.op === 'keep8';
    if (t) t.classList.add(keep ? 'keep8a' : 'crack8');
    caption(keep ? `It checks out: ${'x'} = ${fracText(s.pend.v)} is a real answer` : `${'x'} = ${fracText(s.pend.v)} is a fake answer (extraneous): it's crossed off`);
    await quick(keep ? 400 : 650);
    await result(ns, [], '');
  }
  async function animNone(c, s, ns) {
    const n = await written('No solution', [tk('L'), tk('R')], 'A square root is never negative, so nothing works', 'stamp4');
    dropNote(n);
    await result(ns, [], 'No solution');
  }
  function animFor() {
    return async (c, s, ns, ref) => {
      switch (c.op) {
        case 'pull8': return animPull(c, s, ns, ref);
        case 'mul8': return animMul(c, s, ns, ref);
        case 'comb8': return animComb(c, s, ns, ref);
        case 'rat8': return animRat(c, s, ns, ref);
        case 'conj8': return animConj(c, s, ns, ref);
        case 'red8': return animRed(c, s, ns, ref);
        case 'neg8': return animNeg(c, s, ns, ref);
        case 'rad8': return animRad(c, s, ns, ref);
        case 'root8': return animRoot(c, s, ns, ref);
        case 'pw8': return animPw(c, s, ns, ref);
        case 'rw8': return animRw(c, s, ns, ref);
        case 'prod8': case 'pow8': case 'quot8': return animRule(c, s, ns, ref);
        case 'as8': case 'as8x': return animAs(c, s, ns, ref);
        case 'dv8': return animDv(c, s, ns, ref);
        case 'sq8': return animSq(c, s, ns, ref);
        case 'raise8': return animRaise(c, s, ns, ref);
        case 'expand8': return animExpand(c, s, ns, ref);
        case 'zero8': return animZero(c, s, ns, ref);
        case 'fac8': return animFac(c, s, ns, ref);
        case 'zp8': return animZp(c, s, ns, ref);
        case 'check8': return animCheck(c, s, ns, ref);
        case 'keep8': case 'rej8': return animVerdict(c, s, ns, ref);
        case 'none8': return animNone(c, s, ns, ref);
      }
    };
  }

  // ================================================================ generators
  // Every case comes up at every level; the level changes how hard it is: bigger numbers, negatives,
  // coefficients, extra steps to isolate, longer sums.
  const SF = [2, 3, 5, 6, 7, 10, 11, 13, 15];
  const sgnP = p => (chance(p) ? -1 : 1);
  function okPath(st, maxLen) {
    if (isSolved8(st)) return false;
    const { path, end } = pathOf8(st, st.skill);
    if (path.length > maxLen) return false;
    const big = JSON.stringify(end).match(/"n":(-?\d+)/g) || [];
    return big.every(t => Math.abs(+t.split(':')[1]) <= 5000);
  }
  // ---------------------------------------------------------------- stage 36
  const RAD_CASES = ['pull', 'coef', 'var', 'mul', 'add', 'rat', 'conj'];
  function genRad(cs, tut = isTutorial()) {
    const L = lvl(tut), maxS = [5, 6, 8, 10][L], maxN = [80, 150, 300, 500][L];
    cs = cs || pick(RAD_CASES);
    for (let t = 0; t < 500; t++) {
      const sqN = () => { const s = rand(2, maxS), m = pick(L ? SF : SF.slice(0, 5)); return s * s * m; };
      let st = null;
      if (cs === 'pull') { const n = sqN(); if (n > maxN) continue; st = rxState([Tm(Fc(1, n))]); }
      else if (cs === 'coef') { const n = sqN(); if (n > maxN) continue; st = rxState([Tm(Fc(sgnP(L ? 0.35 : 0.15) * rand(2, [5, 6, 9, 12][L]), n))]); }
      else if (cs === 'var') {
        const xi = rand(2, [5, 7, 9, 11][L]), n = tut ? pick([1, 4, 9]) : chance(0.25) ? 1 : sqN();
        if (n > maxN || (n === 1 && xi < 3)) continue;
        st = rxState([Tm(Fc(L >= 2 && chance(0.4) ? rand(2, 5) : 1, n, xi))]);
      } else if (cs === 'mul') {
        const a = rand(2, [15, 20, 30, 30][L]), b = rand(2, [15, 20, 30, 30][L]);
        if (a === b || sqPart(a) > 1 || sqPart(b) > 1 || sqPart(a * b) === 1 || a * b > [60, 150, 300, 500][L]) continue;
        const k1 = L && chance(0.5) ? rand(2, 5) : 1, k2 = L && chance(0.5) ? rand(2, 5) * sgnP(L >= 2 ? 0.3 : 0) : 1;
        st = rxState([Tm(Fc(k1, a), Fc(k2, b))]);
      } else if (cs === 'add') {
        const m = pick(SF.slice(0, L ? 6 : 3)), nT = !tut && L >= 2 && chance(0.6) ? 3 : 2;
        const terms = [];
        for (let i = 0; i < nT; i++) { const s = rand(1, [4, 5, 5, 6][L]), k = (i && chance(0.35) ? -1 : 1) * (L && chance(0.4) ? rand(2, 4) : 1); terms.push(Tm(Fc(k, s * s * m))); }
        if (L === 3 && chance(0.4)) { const m2 = pick(SF.filter(x => x !== m).slice(0, 4)); terms.push(Tm(Fc(1, pick([1, 4, 9]) * m2))); }
        if (terms.every(x => sqPart(x.f[0].n) === 1) || terms.some(x => x.f[0].n > maxN)) continue;
        const tot = terms.filter(x => x.f[0].n % m === 0 && isSq(x.f[0].n / m)).reduce((a, x) => a + x.f[0].k * isqrt(x.f[0].n / m), 0);
        if (!tot) continue;
        st = rxState(terms);
      } else if (cs === 'rat') {
        const n = L >= 2 && chance(0.4) ? pick([8, 12, 18, 20, 27, 50]) : pick(SF.slice(0, L ? 7 : 4));
        const kb = L && chance(0.35) ? rand(2, 4) : 1, m = n / sqPart(n);
        const k = chance(0.45) ? m * rand(1, 4) * (kb > 1 ? kb : 1) : rand(1, [9, 12, 15, 20][L]);
        st = rxState([Tm(Fc(sgnP(L ? 0.2 : 0) * k))], [Fc(kb, n)]);
      } else {   // conj
        const m = pick(SF.slice(0, L ? 6 : 3)), a = rand(1, [4, 5, 6, 7][L]), b = L >= 2 && chance(0.35) ? 2 : 1, s = chance(0.5) ? 1 : -1;
        const D = a * a - b * b * m;
        if (!D || Math.abs(D) > [12, 20, 30, 40][L]) continue;
        const k = chance(0.55) ? Math.abs(D) * rand(1, 3) : rand(1, [6, 9, 12, 15][L]);
        st = rxState([Tm(Fc(k))], [Fc(a), Fc(s * b, m)]);
      }
      if (st && okPath(st, [6, 7, 8, 9][L] + 2)) return { rad8: st, enemy: 'rootling' };
    }
    return { rad8: rxState([Tm(Fc(1, 50))]), enemy: 'rootling' };
  }
  // ---------------------------------------------------------------- stage 37
  const EXP_CASES = ['unit', 'frac', 'neg', 'rewrite', 'rules', 'eqn'];
  const RMAX = { 2: [6, 9, 12, 12], 3: [3, 4, 5, 6], 4: [2, 3, 3, 3], 5: [2, 2, 3, 3] };
  const coprime = (p, q) => gcd(p, q) === 1;
  function genExp8(cs, tut = isTutorial()) {
    const L = lvl(tut), Qs = [[2, 3], [2, 3, 4], [2, 3, 4, 5], [2, 3, 4, 5]][L];
    cs = cs || pick(EXP_CASES);
    const base = q => { const r = rand(2, RMAX[q][L]); if (!tut && chance([0, 0.15, 0.25, 0.3][L]) && q <= 3) { const r2 = rand(2, RMAX[q][L] + 1); if (r2 !== r && coprime(r, r2)) return powF(F(r, r2), q); } return F(r ** q); };
    for (let t = 0; t < 500; t++) {
      let st = null;
      if (cs === 'unit') { const q = pick(Qs); st = evalState(base(q), F(1, q)); }
      else if (cs === 'frac' || cs === 'neg') {
        const q = pick(Qs), p = rand(cs === 'neg' ? 1 : 2, q === 2 ? 5 : 4);
        if (!coprime(p, q) || p === q) continue;
        const b = base(q), r = rootF(b, q);
        const big = [64, 300, 1000, 1500][L];
        if (!r || Math.abs(fv(powF(r, p))) > big || powF(r, p).d > big) continue;
        st = evalState(b, F(cs === 'neg' ? -p : p, q));
      } else if (cs === 'rewrite') {
        const toRad = chance(0.5), q = rand(2, [4, 5, 7, 7][L]), p = rand(toRad ? 2 : 1, [3, 5, 6, 7][L]);
        if (!coprime(p, q) || p === q) continue;
        st = rwState(toRad ? 'torad' : 'toexp', F(p, q));
      } else if (cs === 'rules') {
        const form = pick(L >= 2 ? ['prod', 'quot', 'pow', 'mix'] : ['prod', 'quot', 'pow']);
        const fr = () => { for (;;) { const q = rand(2, [4, 6, 6, 8][L]), f = F(rand(1, q + (L ? 3 : 1)), q); if (f.d > 1) return f; } };
        let num = [], den = [], g = null;
        if (form === 'prod') num = [fr(), fr()];
        if (form === 'quot') { num = [fr()]; den = [fr()]; }
        if (form === 'pow') g = { e: fr(), o: rand(2, [4, 6, 8, 8][L]) };
        if (form === 'mix') { num = [fr(), fr()]; den = [fr()]; }
        const s0 = rulesState(num, den, g);
        const end = pathOf8(s0, 'ratexp').end;
        const ee = end.num[0] || F(0);
        if (end.den.length || ee.n <= 0 || ee.d > 24 || (num.length > 1 && fEq(num[0], num[1])) || (form === 'quot' && fEq(num[0], den[0]))) continue;
        st = s0;
      } else {   // eqn: k·x^(p/q) + d = c
        const [p, q] = pick(L ? [[1, 2], [1, 3], [3, 2], [3, 4], [5, 3], [2, 1]] : [[1, 2], [1, 3], [3, 2]]).map(Number);
        if (p === 2) continue;
        const tt = rand(2, q >= 3 || p >= 3 ? 3 : [5, 6, 7, 8][L]) * (q % 2 && L && chance(0.35) ? -1 : 1);
        const m = tt ** p;
        if (Math.abs(m) > 400 || Math.abs(tt ** q) > 400) continue;
        const k = !tut && chance([0.25, 0.5, 0.6, 0.7][L]) ? rand(2, [3, 4, 5, 6][L]) : 1;
        const d = !tut && chance([0.3, 0.6, 0.7, 0.8][L]) ? nonZero(-12, 12) : 0;
        st = eqState(Pw(k, F(p, q), d), Lin(0, k * m + d), { skill: 'ratexp' });
      }
      if (st && okPath(st, 12)) return { rad8: st, enemy: 'fernling' };
    }
    return { rad8: evalState(F(8), F(2, 3)), enemy: 'fernling' };
  }
  // ---------------------------------------------------------------- stage 38
  const EQ_CASES = ['lin', 'iso', 'quad', 'quadiso', 'allfake', 'noneg', 'two', 'cube'];
  function genRadEq(cs, tut = isTutorial()) {
    const L = lvl(tut);
    cs = cs || pick(EQ_CASES);
    const kOf = p => (!tut && chance(p) ? rand(2, [3, 3, 4, 5][L]) : 1);
    for (let t = 0; t < 800; t++) {
      let st = null;
      if (cs === 'lin' || cs === 'iso') {
        const a = rand(1, [3, 5, 7, 9][L]), x0 = rand(L ? -6 : 1, [9, 12, 15, 20][L]), c = rand(1, [6, 8, 10, 12][L]), b = c * c - a * x0;
        if (Math.abs(b) > [40, 60, 90, 120][L] || (cs === 'lin' && b === 0)) continue;
        let k = 1, d = 0;
        if (cs === 'iso') {
          k = kOf([0.5, 0.6, 0.7, 0.8][L]); d = !tut && (k === 1 || chance([0, 0.5, 0.7, 0.8][L])) ? nonZero(-9, 9) : 0;
          if (tut) d = rand(2, 6);
          if (k === 1 && d === 0) continue;
        }
        st = eqState(Rad(k, 2, a, b, d), Lin(0, k * c + d));
      } else if (cs === 'quad' || cs === 'quadiso' || cs === 'allfake') {
        const d = rand(-5, 5), lo = -d;
        let r1, r2;
        if (cs === 'allfake') { r1 = rand(lo - 7, lo - 1); r2 = rand(lo - 7, lo - 1); }
        else if (chance(0.25) && !tut) { r1 = rand(lo, lo + 7); r2 = rand(lo, lo + 7); }
        else { r1 = rand(lo - 6, lo - 1); r2 = rand(lo, lo + 8); }
        if (r1 === r2) continue;
        const a = 2 * d + r1 + r2, b = d * d - r1 * r2;
        if (a === 0 || (cs !== 'allfake' && a < 1) || Math.abs(a) > [8, 10, 14, 16][L] || Math.abs(b) > [30, 50, 70, 90][L]) continue;
        if (cs === 'quadiso') {
          if (d === 0) continue;
          st = eqState(Rad(1, 2, a, b, -d), Lin(1, 0));
        } else st = eqState(Rad(1, 2, a, b), Lin(1, d));
      } else if (cs === 'noneg') {
        const a = rand(1, [3, 5, 7, 9][L]), b = nonZero(-12, 15), c = -rand(1, 9);
        let k = 1, d = 0;
        if (!tut && L && chance(0.7)) { k = kOf(0.5); d = nonZero(-9, 9); }
        st = eqState(Rad(k, 2, a, b, d), Lin(0, k * c + d));
      } else if (cs === 'two') {
        const a = rand(1, [4, 6, 8, 9][L]), c = rand(1, [4, 6, 8, 9][L]), x0 = rand(-6, 10);
        if (a === c) continue;
        const v = chance(tut ? 0 : 0.25) ? -rand(1, 12) : rand(0, [12, 20, 30, 40][L]);
        const b = v - a * x0, dd = v - c * x0;
        if (Math.abs(b) > 40 || Math.abs(dd) > 40) continue;
        st = eqState(Rad(1, 2, a, b), Rad(1, 2, c, dd));
      } else {   // cube
        const a = rand(1, [3, 5, 7, 9][L]), x0 = rand(-8, 12), c = rand(1, [3, 4, 5, 5][L]) * (L && chance(0.4) ? -1 : 1), b = c ** 3 - a * x0;
        if (Math.abs(b) > [40, 80, 130, 150][L]) continue;
        const d = !tut && L && chance(0.5) ? nonZero(-9, 9) : 0, k = !tut && L >= 2 && chance(0.4) ? rand(2, 3) : 1;
        st = eqState(Rad(k, 3, a, b, d), Lin(0, k * c + d));
      }
      if (st && okPath(st, 16)) return { rad8: st, enemy: 'phantom' };
    }
    return { rad8: eqState(Rad(1, 2, 1, 3), Lin(1, -3)), enemy: 'phantom' };
  }
  const GENS = { radsimp: genRad, ratexp: genExp8, radeq: genRadEq };
  const HARD = { radsimp: ['add', 'rat', 'conj', 'mul'], ratexp: ['neg', 'frac', 'eqn', 'rules'], radeq: ['quad', 'quadiso', 'iso', 'allfake'] };
  function buildFight8(node, list) {
    const act8 = list.filter(id => (SKILL[id].act || 1) === 8);
    if (!act8.length) act8.push('radsimp');
    if (node.type === 'elite') {
      const two = act8.slice(-2);
      const phases = (two.length > 1 ? two : [two[0], two[0]]).map(id => () => GENS[id](pick(HARD[id])));
      return { phases, handSize: difficulty.hand, enemy: 'thornback' };
    }
    // Boss: one phase per Act 8 stage, then a last one that needs several of them.
    const phases = act8.map(id => () => GENS[id](pick(SKILL[id].cases)));
    phases.push(() => (act8.includes('radeq') ? genRadEq(pick(['quadiso', 'quad', 'allfake'])) : act8.includes('ratexp') ? genExp8(pick(['eqn', 'neg'])) : genRad('conj')));
    return { phases, handSize: difficulty.hand, enemy: 'elderroot' };
  }

  // ---------------------------------------------------------------- variety
  function textOf8(e) {
    if (e.k8 === 'rx') return rxText(e, false);
    if (e.k8 === 're') return e.ask + ' ' + reHtml(e, false);
    return eqText(e, false);
  }
  if (typeof ENGINES === 'object') ENGINES.rad8 = { text: textOf8 };
  const applyDifficulty = g => g;   // generators read the difficulty themselves; tutorials stay on Easy

  // ================================================================ skills, enemies, act
  SKILLS.push(
    { id: 'radsimp', stage: 36, act: 8, name: 'Simplify radicals', cases: RAD_CASES, gen: cycled('radsimp', c => genRad(c)),
      title: 'Stage 36: Simplifying radicals',
      intro: 'A square root is simplest when no perfect square (4, 9, 16, 25, …) is left inside, no fraction has a root on the bottom, and like radicals are combined. Pull out a perfect square: √50 = √(25 · 2) = 5√2 (only its root, 5, comes out). Multiply roots into one: √6 · √15 = √90. Combine like radicals: 2√3 + 5√3 = 7√3. Rationalize: multiply top and bottom by the root on the bottom (or by the conjugate when the bottom has two terms).',
      example: '√50 → Pull out 25 → 5√2<br><br>3/√2 → × √2/√2 → 3√2/2<br><br>√12 + √27 → 2√3 + 3√3 → 5√3',
      tutorial: [() => genRad('pull', true), () => genRad('rat', true)] },
    { id: 'ratexp', stage: 37, act: 8, name: 'Rational exponents', cases: EXP_CASES, gen: cycled('ratexp', c => genExp8(c)),
      title: 'Stage 37: Rational exponents',
      intro: 'A fraction exponent is a root and a power: the bottom is the root, the top is the power. 8^(2/3) = (∛8)² = 2² = 4. Take the root first to keep numbers small. A negative exponent means 1 over: 16^(−3/4) = 1/16^(3/4). The exponent rules work the same with fractions. To solve x^(3/2) = 8, raise both sides to the reciprocal power, 2/3.',
      example: '8^(2/3) → (∛8)² → 2² → 4<br><br>x^(3/2) = 8<br>Raise to 2/3 → x = 8^(2/3) = 4',
      tutorial: [() => genExp8('unit', true), () => genExp8('frac', true)] },
    { id: 'radeq', stage: 38, act: 8, name: 'Radical equations', cases: EQ_CASES, gen: cycled('radeq', c => genRadEq(c)),
      title: 'Stage 38: Radical equations',
      intro: 'Get the root alone, then square both sides (cube for a cube root) and solve what\'s left. Squaring can create fake answers (extraneous solutions), so after squaring you must Check every answer in the original equation and keep or reject it. A square root is never negative: √(x + 1) = −3 has no solution.',
      example: '√(x + 3) = x − 3<br>Square both → x + 3 = x² − 6x + 9<br>→ 0 = x² − 7x + 6 = (x − 1)(x − 6)<br>Check 1: √4 = 2, 1 − 3 = −2 ✗<br>Check 6: √9 = 3, 6 − 3 = 3 ✓ → x = 6',
      tutorial: [() => genRadEq('lin', true), () => genRadEq('quad', true)] },
  );
  for (const s of SKILLS) SKILL[s.id] = s;
  progress = loadProgress();     // the save was first read before these skills existed

  Object.assign(ENEMIES, {
    rootling:  { name: 'Rootling',       rank: 'Normal', color: '#8ac926', size: 84 },
    fernling:  { name: 'Fernling',       rank: 'Normal', color: '#52b788', size: 84 },
    phantom:   { name: 'Phantom Bloom',  rank: 'Normal', color: '#c77dff', size: 84 },
    thornback: { name: 'Thornback',      rank: 'Elite',  color: '#6a994e', size: 100, horns: true },
    elderroot: { name: 'The Elder Root', rank: 'Boss',   color: '#a7c957', size: 120, crown: true },
  });
  ACTS[8] = { name: 'The Root Garden', sub: 'Radicals and rational exponents', boss: 'The Elder Root', firstSkill: 'radsimp',
    blurb: 'In the Root Garden everything grows under a radical sign. Simplify roots, turn fraction exponents into roots, and solve radical equations, checking every answer for fakes. Defeat The Elder Root.',
    cleared: () => 'The Elder Root is tamed and the garden grows straight again. Act 9 is still to be built, so run Act 8 again to keep your skills sharp.' };

  const svgI = body => `<svg viewBox="0 0 24 24" width="1em" height="1em" fill="none" stroke="currentColor" stroke-width="2.6" stroke-linecap="round" stroke-linejoin="round">${body}</svg>`;
  Object.assign(CARD_ICONS, {
    pull8:  { name: 'Pull a perfect square out of the root', svg: svgI('<path d="M2 14l3 6 4-16h13"/><path d="M15 12V6M12 9l3-3 3 3" stroke-width="2"/>') },
    mul8:   { name: 'Multiply roots into one', svg: svgI('<path d="M1 13l2 5 3-12h6M12 13l2 5 3-12h6"/>') },
    rat8:   { name: 'Rationalize (clear the root from the bottom)', svg: svgI('<path d="M3 12h18"/><path d="M6 19l2 2 2-6h6" stroke-dasharray="2 2"/><path d="M9 3h6M12 6v0"/>') },
    rad8:   { name: 'Rewrite as a root', svg: svgI('<path d="M2 14l3 6 4-16h13"/><path d="M15 9h4M17 11v5" stroke-width="2"/>') },
    root8:  { name: 'Take the root', svg: svgI('<path d="M2 14l3 6 4-16h13"/><path d="M13 11l5 5M18 11l-5 5" stroke-width="2"/>') },
    sq8:    { name: 'Square or cube both sides', svg: svgI('<path d="M3 9h7M3 15h7"/><path d="M14 6h5v4h-5v4h5" stroke-width="2"/>') },
    raise8: { name: 'Raise both sides to a power', svg: svgI('<path d="M5 20c-2-4-2-8 0-12M11 20c2-4 2-8 0-12"/><path d="M15 9l3-5 3 5" stroke-width="2"/>') },
    fac8:   { name: 'Factor', svg: svgI('<path d="M5 5c-2 4-2 10 0 14M10 5c2 4 2 10 0 14M14 5c-2 4-2 10 0 14M19 5c2 4 2 10 0 14"/>') },
    zp8:    { name: 'Zero product (each factor = 0)', svg: svgI('<ellipse cx="12" cy="12" rx="5" ry="7"/><path d="M4 4l4 4M20 4l-4 4"/>') },
    check8: { name: 'Check an answer in the original equation', svg: svgI('<circle cx="10" cy="10" r="6"/><path d="M15 15l6 6"/><path d="M7.5 10l2 2 3.5-4" stroke-width="2"/>') },
    keep8:  { name: 'Keep: the answer checks out', svg: svgI('<path d="M4 13l5 5L20 6"/>') },
    rej8:   { name: 'Reject: a fake (extraneous) answer', svg: svgI('<path d="M5 5l14 14M19 5L5 19"/>') },
  });

  const css = document.createElement('style');
  css.textContent = `
    #equation.ex8 { flex-wrap:nowrap; gap:0; max-width:100%; align-items:center; }
    .tok.a4.f8 { padding:4px 4px; min-width:0; white-space:nowrap; }
    .tok.a4.s8 { padding:4px 3px; min-width:0; color:var(--muted); border-color:transparent !important; background:none !important; }
    .tok.a4.side8, .tok.a4.v8, .tok.a4.o8, .tok.a4.c8, .tok.a4.p8 { padding:4px 6px; white-space:nowrap; }
    .w8 { display:inline-block; white-space:nowrap; }
    sup.e8 { font-size:.5em; vertical-align:.85em; line-height:0; margin-left:.05em; }
    .rt8 { display:inline-flex; align-items:flex-start; white-space:nowrap; margin:0 .04em; }
    .rt8 .rs8 { display:inline-block; transform-origin:bottom; transition: opacity .35s, transform .35s; }
    .rt8 .rr8 { border-top:.07em solid currentColor; padding:0 .08em; margin-left:-.02em; margin-top:.12em; line-height:1.1; display:inline-block; white-space:nowrap; }
    .rt8 sup.ri8 { font-size:.45em; margin-right:-.35em; margin-top:.25em; line-height:1; z-index:1; }
    .rt8 .peel8, .peel8 { opacity:0; transform: translateY(-.4em) rotate(-25deg); transition: opacity .4s, transform .4s; }
    .frac.f8 { font-size:.8em; }
    .frac.f8 > span { padding:0 .2em; white-space:nowrap; }
    .frac8 .tok.a4 { min-height:0; padding:2px 3px; }
    .col8 { display:flex; flex-direction:column; align-items:center; gap:.15em; }
    .col8 .row4 { flex-wrap:nowrap; justify-content:center; }
    .tok.a4.s8.lab8 { font-size:.45em; color:var(--muted); white-space:nowrap; }
    .tok.a4.o8 { font-size:.62em; color:var(--ink); min-height:0; }
    .tok.a4.s8.or8 { font-size:.5em; }
    .tok.a4.c8 { min-height:0; }
    .tok.a4.c8.now8 { color:var(--accent); }
    .tok.a4.c8.st8-keep { color:var(--good); }
    .tok.a4.c8.st8-keep::after { content:' ✓'; }
    .tok.a4.c8.st8-rej { color:var(--bad); text-decoration:line-through; opacity:.75; }
    .tok.a4.p8 { flex-direction:column; min-height:0; font-size:.7em; }
    .p8 .sub8 { font-size:.7em; color:var(--muted); }
    .p8 .val8 { color:#ffc46b; }
    .p8 small { font-size:.55em; color:var(--bad); }
    .tok.a4.s8.fin8 { font-size:.6em; color:var(--good) !important; }
    .tok.a4.s8.ns8 { font-size:.55em; color:var(--bad) !important; }
    .tok.a4.hot8 { background:#ffffff14; border-color:var(--accent); }
    .tok.a4.slide8 { transform: translateX(-.6em) scale(.7); opacity:.2; }
    .tok.a4.crack8 { animation: crack8 .6s ease-in forwards; color:var(--bad); }
    @keyframes crack8 { 30% { transform: rotate(-6deg) scale(1.08); } 60% { transform: rotate(5deg) scale(.95); opacity:.8; } 100% { transform: translateY(.3em) rotate(-8deg) scale(.8); opacity:.15; } }
    .tok.a4.keep8a { animation: pop .4s; color:var(--good); border-color:var(--good); }
    sup.lift8 { display:inline-block; animation: lift6 .6s ease-out forwards; }
    .tok.ok8 { border-color: var(--good) !important; background:#06d6a022 !important; }
    .unote.n8 { font-size:max(.42em, 14px); }
    .unote.n8 .rt8 .rr8 { border-top-width:.08em; }
    .card .clong.l8 { white-space:normal; display:block; line-height:1.1; }
    .card .clong.l8 sup { font-size:.75em; }
    .card .clong.l8 .frac.f8c { font-size:.75em; display:inline-flex; vertical-align:middle; }
    .card .clong.l8 .rt8 .rr8 { border-top-width:.08em; }
    @media (max-width: 640px) {
      .tok.a4.side8, .tok.a4.v8, .tok.a4.o8, .tok.a4.c8, .tok.a4.p8 { padding:2px 3px; }
    }
  `;
  document.head.appendChild(css);

  window.ACT8 = { apply: apply8, isSolved: isSolved8, makeEquation: makeEquation8, refreshPath, render, prefit, clear, makeHand: makeHand8,
    isCorrect, whyWrong, animFor, applyDifficulty, label, text, kind, icon, slot, targetSel, onDrag, autoTarget, buildFight: buildFight8, prompt,
    gens: GENS, eqText: textOf8,
    // test hooks
    _canon: canon8, _correct: correct8, _moves: movesOf, _apply: apply8, _places: places, _legal: legalMove, _hand: makeHand8, _family: family, _specials: specials };
})();
