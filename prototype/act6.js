// =====================================================================
//  Act 6: The Power Forge (exponents and polynomials)
// =====================================================================
// Stage 22  Exponent rules            x² · x³, (x²)³, x⁵/x², x⁰, x⁻²
// Stage 23  Scientific notation       (3 × 10⁴)(2 × 10³), 45 000 = 4.5 × 10⁴
// Stage 24  Add and subtract polys    (3x² + 2x) − (x² − 5x + 1)
// Stage 25  Multiply polynomials      (x + 3)(x − 2), (x + 2)², (x + 3)(x − 3)
// Stage 26  Divide polynomials        (x² + 5x + 6) ÷ (x + 2), long and synthetic division
//
// These problems are simplified, not solved, so states have their own kind, `k6`:
//   ex   a product of factors over a product of factors: { num: [f], den: [f], sci, grouped, ask }
//        A factor is a number { t: 'n', v }, a power { t: 'p', b: 'x' | 'y' | '10', e } or a bracket
//        raised to a power { t: 'g', items: [n | p], e }. `grp` says which written bracket a factor sits
//        in, so (2x³)(4x²) is written the way it was given. Stages 22 and 23 (sci: base 10, decimals).
//   pl   a row of polynomial pieces: { items: [ grp | prod | sq | term ] }. grp is ± (terms), prod is
//        (A)(B), sq is (A)², term is one monomial { c, x, y }. Stages 24 and 25 (and the elite and boss,
//        which mix them: (x + 3)(x − 2) − (x² − 5x)).
//   pd   a polynomial over a polynomial: { N, D, method, filled, mode, Q, R, rows, done }. N, D, Q and R
//        are dense coefficient lists (index = power of x). Stage 26.
// Every move that is legal counts (exponent rules can go in any order); the path the game expects (par)
// is the canonical order. Cards are ◎: a card with one place to go applies by itself.
//
// index.html switches to this engine for generators that return { ex6 } (cur.act6).
'use strict';
(function () {
  const A2 = window.ACT2, A4 = window.ACT4;
  if (!A2 || !A4 || !A4.kit) return;
  const K = A4.kit;
  const { TOK, EQTOK, banner, refOf, P, kickClass, clone, fNeg, fSub, fDiv, fEq, fz, fv } = K;
  const isTutorial = K.isTutorial, lvl = K.lvl;
  const sgn = () => (Math.random() < 0.5 ? -1 : 1);
  const chance = p => Math.random() < p;
  const qid = () => Math.random().toString(36).slice(2, 8);

  // ================================================================ numbers and powers
  const SUPD = '⁰¹²³⁴⁵⁶⁷⁸⁹';
  const supText = n => (n < 0 ? '⁻' : '') + String(Math.abs(n)).split('').map(d => SUPD[+d]).join('');
  const supHtml = n => `<sup class="e6">${numText(n)}</sup>`;
  const fPow = (f, e) => (e >= 0 ? F(f.n ** e, f.d ** e) : F(f.d ** -e, f.n ** -e));
  const pow10 = k => (k >= 0 ? F(10 ** k) : F(1, 10 ** -k));
  // Exact decimal for a fraction whose bottom is made of 2s and 5s (0.25, 4.5, 0.00072); else a fraction.
  function decText(f) {
    if (f.d === 1) return numText(f.n);
    let k = 1; while (k < 16 && (10 ** k) % f.d) k++;
    if ((10 ** k) % f.d) return fracText(f);
    const s = String(Math.abs(f.n) * (10 ** k / f.d)).padStart(k + 1, '0');
    const frac = s.slice(-k).replace(/0+$/, ''), int = s.slice(0, -k);
    return (f.n < 0 ? MINUS : '') + int + (frac ? '.' + frac : '');
  }
  // Long standard-form numbers get thin spaces every three digits (45 000, 0.000 72 stays as written).
  const groupDigits = t => t.replace(/^(−?)(\d+)/, (m, s, d) => s + (d.length > 4 ? d.replace(/\B(?=(\d{3})+(?!\d))/g, ' ') : d));
  const XV = b => (b === '10' ? '10' : `<i class="xv">${b}</i>`);

  // ================================================================ ex: factors
  const N = (v, grp = 0) => ({ t: 'n', v: typeof v === 'number' ? F(v) : v, grp });
  const Pw = (b, e, grp = 0) => ({ t: 'p', b, e, grp });
  const G = (items, e, grp = 0) => ({ t: 'g', items, e, grp });
  const exState = (num, den, o = {}) => tidy({ k6: 'ex', num, den: den || [], sci: !!o.sci, grouped: !!o.grouped, ask: o.ask || 'simp',
    skill: o.skill || (o.sci ? 'scinot' : 'exprules'), qid: qid() });
  const numOf = (e, f) => (e.sci ? decText(f.v) : fracText(f.v));
  function facText(f, sci, lead = true) {
    if (f.t === 'n') return sci ? decText(f.v) : fracText(f.v);
    if (f.t === 'p') return f.b + (f.e === 1 && f.b !== '10' ? '' : supText(f.e));
    return '(' + itemsText(f.items, sci) + ')' + supText(f.e);
    void lead;
  }
  const itemsText = (items, sci) => items.map(i => facText(i, sci)).join(sci ? ' × ' : '');
  function facHtml(f, sci) {
    if (f.t === 'n') return groupDigits(sci ? decText(f.v) : fracText(f.v));
    if (f.t === 'p') return XV(f.b) + (f.e === 1 && f.b !== '10' ? '' : supHtml(f.e));
    return `(${f.items.map(i => facHtml(i, sci)).join(sci ? ' × ' : '')})${supHtml(f.e)}`;
  }
  const grpsOf = list => [...new Set(list.map(f => f.grp))];
  const idx = (list, test) => list.map((f, i) => (test(f) ? i : -1)).filter(i => i >= 0);
  // After every move: a 1 times something is dropped, an empty top is 1, a bottom of 1 goes away.
  function tidy(e) {
    if (e.k6 !== 'ex') return e;
    for (const s of ['num', 'den']) {
      const l = e[s];
      // scientific notation keeps its number even when it is 1 (1 × 10⁸)
      if (l.length > 1) e[s] = l.filter((f, i) => !(f.t === 'n' && fIs(f.v, 1)) || (e.sci && s === 'num' && !l.some((o, j) => j !== i && o.t === 'n' && !(fIs(o.v, 1) && j > i))));
      if (e[s].length > 1 && e[s].every(f => f.t === 'n' && fIs(f.v, 1))) e[s] = [e[s][0]];
    }
    if (e.den.length === 1 && e.den[0].t === 'n' && fIs(e.den[0].v, 1)) e.den = [];
    if (!e.num.length) e.num = [N(1)];
    return e;
  }
  function layerText(list, sci, grouped) {
    if (grouped) {
      const ns = list.filter(f => f.t === 'n'), ps = list.filter(f => f.t !== 'n');
      const part = (l, j) => (l.length > 1 ? '(' + l.map(f => facText(f, sci)).join(j) + ')' : l.map(f => facText(f, sci)).join(j));
      return [ns.length ? part(ns, ' · ') : '', ps.length ? part(ps, ' · ') : ''].filter(Boolean).join(' × ');
    }
    const gs = grpsOf(list);
    const one = g => itemsText(list.filter(f => f.grp === g), sci);
    if (gs.length === 1) return one(gs[0]);
    if (!sci && gs.every(g => list.filter(f => f.grp === g).length === 1)) return gs.map(one).join(' · ');
    return gs.map(g => '(' + one(g) + ')').join('');
  }
  function exText(e) {
    const t = layerText(e.num, e.sci, e.sci && e.grouped);
    if (!e.den.length) return t;
    const b = layerText(e.den, e.sci, e.sci && e.grouped);
    const wrap = (s, l) => (l.length > 1 || l.some(f => f.t === 'g') ? (s.startsWith('(') && grpsOf(l).length === 1 && l.length === 1 ? s : `(${s})`) : s);
    return `${wrap(t, e.num)}/${wrap(b, e.den)}`;
  }

  // ================================================================ pl: polynomials as rows of pieces
  const M = (c, x = 0, y = 0) => ({ c: typeof c === 'number' ? F(c) : c, x, y });
  const mkey = m => m.x + ',' + m.y;
  const mdeg = m => m.x + m.y;
  const mMul = (a, b) => M(fMul(a.c, b.c), a.x + b.x, a.y + b.y);
  const mNeg = m => ({ ...m, c: fNeg(m.c) });
  const byDeg = (a, b) => mdeg(b) - mdeg(a) || b.x - a.x;
  function mBody(m, html) {
    const lit = (b, e) => (e ? (html ? XV(b) : b) + (e === 1 ? '' : html ? supHtml(e) : supText(e)) : '');
    const L = lit('x', m.x) + lit('y', m.y), a = fAbs(m.c);
    const k = L && fIs(a, 1) ? '' : html ? fracHtml(a) : fracText(a);
    return k + L;
  }
  const mText = (m, first, html) => (m.c.n < 0 ? (first ? MINUS : MINUS + ' ') : first ? '' : '+ ') + mBody(m, html);
  const polyText = (ts, html) => (ts.length ? ts.map((m, i) => mText(m, i === 0, html)).join(' ') : '0');
  const T = m => ({ t: 'term', m });
  const Grp = (s, terms) => ({ t: 'grp', s, terms });
  const Prod = (A, B, s = 1) => ({ t: 'prod', A, B, s });
  const Sq = (A, s = 1) => ({ t: 'sq', A, s });
  const plState = (items, o = {}) => ({ k6: 'pl', items, ask: o.ask || 'simp', skill: o.skill || 'polyadd', qid: qid() });
  const isMonoP = A => A.length === 1;
  // (a + b)(a − b): same first terms, opposite second terms
  const isConj = it => it.t === 'prod' && it.A.length === 2 && it.B.length === 2 && mkey(it.A[0]) === mkey(it.B[0]) && fEq(it.A[0].c, it.B[0].c)
    && mkey(it.A[1]) === mkey(it.B[1]) && fEq(it.A[1].c, fNeg(it.B[1].c));
  function itemText(it, first) {
    const lead = (s, f) => (f ? (s < 0 ? MINUS : '') : s < 0 ? MINUS + ' ' : '+ ');
    if (it.t === 'term') return mText(it.m, first, false);
    if (it.t === 'grp') return `${lead(it.s, first)}(${polyText(it.terms)})`;
    if (it.t === 'sq') return `${lead(it.s || 1, first)}(${polyText(it.A)})²`;
    const A = isMonoP(it.A) ? mText(it.A[0], true) : `(${polyText(it.A)})`;
    return `${lead(it.s || 1, first)}${A}(${polyText(it.B)})`;
  }
  const plText = e => (e.items.length ? e.items.map((it, i) => itemText(it, i === 0)).join(' ') : '0');
  const plTerms = e => e.items.filter(it => it.t === 'term').map(it => it.m);

  // ================================================================ pd: polynomial division (dense lists)
  const deg = a => { for (let i = a.length - 1; i >= 0; i--) if (!fz(a[i])) return i; return -1; };
  const dense = (cs, n) => { const a = []; for (let i = 0; i <= n; i++) a.push(F(cs[i] || 0)); return a; };   // cs[i] = coefficient of xⁱ
  const pMul = (a, b) => { const out = []; for (let i = 0; i < a.length + b.length - 1; i++) out.push(F(0)); a.forEach((p, i) => b.forEach((q, j) => { out[i + j] = fAdd(out[i + j], fMul(p, q)); })); return out; };
  const pSub = (a, b) => { const n = Math.max(a.length, b.length), out = []; for (let i = 0; i < n; i++) out.push(fSub(a[i] || F(0), b[i] || F(0))); return out; };
  const toTerms = (a, keep0 = false) => { const ts = []; for (let i = a.length - 1; i >= 0; i--) if (keep0 || !fz(a[i])) ts.push(M(a[i] || F(0), i)); return ts; };
  const dText = (a, html) => polyText(toTerms(a), html);
  const isMonoD = D => toTerms(D).length === 1;
  const monicLin = D => deg(D) === 1 && fIs(D[1], 1);
  // N has a missing power somewhere below its top (x³ − 8 has no x² and no x)
  const holes = N => { const out = []; for (let i = deg(N) - 1; i >= 0; i--) if (fz(N[i])) out.push(i); return out; };
  const pdState = (N, D, o = {}) => ({ k6: 'pd', N, D, method: o.method || 'any', filled: false, mode: null, Q: [], R: null, rows: [], done: false,
    skill: 'polydiv', qid: qid() });
  const nextTerm = e => { const r = deg(e.R), d = deg(e.D); return { c: fDiv(e.R[r], e.D[d]), e: r - d }; };
  function divide(N, D) {          // quotient and remainder, by long division
    const R = N.slice(), d = deg(D), Q = [];
    for (let i = 0; i <= Math.max(0, deg(N) - d); i++) Q.push(F(0));
    for (let g = 0; g < 20 && deg(R) >= d; g++) {
      const r = deg(R), c = fDiv(R[r], D[d]); Q[r - d] = c;
      D.forEach((q, i) => { R[i + r - d] = fSub(R[i + r - d], fMul(q, c)); });
      R[r] = F(0);
    }
    return { Q, R };
  }
  function pdAnswer(e, html) {
    const q = dText(e.Q, html), r = deg(e.R);
    if (r < 0) return q;
    const rt = dText(e.R, html), dt = dText(e.D, html);
    const neg = e.R[r].n < 0 && toTerms(e.R).length === 1;
    const one = toTerms(e.R).length === 1, top = neg ? dText(e.R.map(fNeg)) : rt;
    const frac = html ? `<span class="frac f6"><span>${neg ? dText(e.R.map(fNeg), true) : dText(e.R, true)}</span><span>${dt}</span></span>` : `${one ? top : `(${top})`}/(${dt})`;
    return `${q} ${neg ? MINUS : '+'} ${frac}`.replace(/^0 \+ /, '');
  }
  const pdText = e => `(${dText(e.N)}) ÷ (${dText(e.D)})`;

  // ================================================================ the moves that are legal
  // Each move: { op, key, refs } (refs = the tokens it can be dropped on; key = which thing it changes,
  // so two tokens of one pair count as one place). The list is in the canonical order.
  function exMoves(e) {
    const out = [];
    const lay = { n: e.num, d: e.den };
    if (e.ask === 'tostd') {
      const ni = e.num.findIndex(f => f.t === 'n'), pi = e.num.findIndex(f => f.t === 'p');
      if (pi >= 0) out.push({ op: 'std6', key: 'S', refs: ['n' + ni, 'n' + pi] });
      return out;
    }
    for (const s of ['n', 'd']) lay[s].forEach((f, i) => {
      const r = s + i;
      if ((f.t === 'g' || f.t === 'p') && f.e === 0) out.push({ op: 'zero6', key: r, refs: [r] });
      else if (f.t === 'g') out.push({ op: 'pow6', key: r, refs: [r] });
    });
    const hasG = [...e.num, ...e.den].some(f => f.t === 'g');
    const needG = e.sci && !e.grouped && (grpsOf(e.num).length > 1 || e.den.length > 0);
    if (needG && !hasG) out.push({ op: 'grp6', key: 'X', refs: ['X'] });
    if (!needG) {
      for (const s of ['n', 'd']) {
        const ns = idx(lay[s], f => f.t === 'n');
        if (ns.length >= 2) out.push({ op: 'muln6', key: 'm' + s, refs: ns.map(i => s + i) });
        const bases = {};
        lay[s].forEach((f, i) => { if (f.t === 'p') (bases[f.b] = bases[f.b] || []).push(s + i); });
        for (const b of Object.keys(bases)) if (bases[b].length >= 2) out.push({ op: 'prod6', key: 'p' + s + b, refs: bases[b] });
      }
      const nn = idx(e.num, f => f.t === 'n'), dn = idx(e.den, f => f.t === 'n');
      if (nn.length === 1 && dn.length === 1) {
        const a = e.num[nn[0]].v, b = e.den[dn[0]].v;
        if (e.sci || fDiv(a, b).d !== b.n) out.push({ op: 'divn6', key: 'q', refs: ['n' + nn[0], 'd' + dn[0]] });
      }
      for (const b of new Set(e.den.filter(f => f.t === 'p').map(f => f.b))) {
        const ti = idx(e.num, f => f.t === 'p' && f.b === b), bi = idx(e.den, f => f.t === 'p' && f.b === b);
        if (ti.length === 1 && bi.length === 1) out.push({ op: 'quot6', key: 'q' + b, refs: ['n' + ti[0], 'd' + bi[0]] });
      }
    }
    if (!e.sci) for (const s of ['n', 'd']) lay[s].forEach((f, i) => { if (f.t === 'p' && f.e < 0) out.push({ op: 'negx6', key: s + i, refs: [s + i] }); });
    if (e.sci && !out.length) {
      const ni = idx(e.num, f => f.t === 'n'), pi = idx(e.num, f => f.t === 'p');
      if (ni.length === 1 && pi.length <= 1 && !e.den.length) {
        const a = Math.abs(fv(e.num[ni[0]].v));
        if (a >= 10 || a < 1) out.push({ op: 'norm6', key: 'N', refs: ['n' + ni[0]].concat(pi.map(i => 'n' + i)) });
      }
    }
    return out;
  }
  function sortedOK(e) {
    const ts = plTerms(e);
    for (let i = 1; i < ts.length; i++) if (byDeg(ts[i - 1], ts[i]) > 0) return false;
    return true;
  }
  function plMoves(e) {
    const out = [];
    e.items.forEach((it, i) => {
      const r = 'i' + i;
      if (it.t === 'grp') out.push({ op: it.s < 0 ? 'dneg6' : 'drop6', key: r, refs: [r] });
      if (it.t === 'sq') { if (it.A.length === 2) out.push({ op: 'sqb6', key: r, refs: [r] }); out.push({ op: 'box6', key: r, refs: [r] }); }
      if (it.t === 'prod') { if (isConj(it)) out.push({ op: 'dos6', key: r, refs: [r] }); out.push({ op: 'box6', key: r, refs: [r] }); }
    });
    const byKey = {};
    e.items.forEach((it, i) => { if (it.t === 'term') (byKey[mkey(it.m)] = byKey[mkey(it.m)] || []).push('i' + i); });
    for (const k of Object.keys(byKey)) if (byKey[k].length >= 2) out.push({ op: 'comb6', key: 'c' + k, refs: byKey[k] });
    if (!out.length && !sortedOK(e)) out.push({ op: 'sort6', key: 'X', refs: ['X'] });
    return out;
  }
  function pdMoves(e) {
    if (e.done) return [];
    const F_ = (op, o = {}) => ({ op, key: 'F', refs: ['F'], ...o });
    if (isMonoD(e.D)) return [F_(e.mode === 'split' ? 'divt6' : 'split6')];
    if (!e.mode) {
      if (holes(e.N).length && !e.filled) return [F_('fill6')];
      const o = [];
      if (e.method !== 'long' && monicLin(e.D)) o.push(F_('syn6', { c: fNeg(e.D[0]) }));
      if (e.method !== 'syn') o.push(F_('long6'));
      return o;
    }
    if (e.mode === 'long') return [F_('qt6', { t: nextTerm(e) })];
    return [];
  }
  const movesOf = e => (e.k6 === 'ex' ? exMoves(e) : e.k6 === 'pl' ? plMoves(e) : pdMoves(e));
  const C6 = (op, o = {}) => ({ op, a6: true, scope: 'part', ...o });
  const moveCard = m => C6(m.op, m.c ? { c: m.c } : m.t ? { t: m.t } : {});
  function canon6(e) { const m = movesOf(e)[0]; return m ? { ...moveCard(m), ref: m.refs[0] } : null; }
  const isSolved6 = e => !movesOf(e).length;
  function matchCard(m, c) {
    if (m.op !== c.op) return false;
    if (c.op === 'syn6') return !!c.c && fEq(c.c, m.c);
    if (c.op === 'qt6') return !!c.t && fEq(c.t.c, m.t.c) && c.t.e === m.t.e;
    return true;
  }
  function correct6(e, c, target) {
    if (!c || !c.a6 || c.op === 'trap') return false;
    const ref = refOf(target);
    return movesOf(e).some(m => matchCard(m, c) && m.refs.includes(ref));
  }

  // ================================================================ applying a move
  function apply6(e, c, ref) {
    const r = clone(e);
    if (!c || c.op === 'trap') return r;
    const m = movesOf(e).find(o => matchCard(o, c) && (o.refs.includes(ref) || o.refs.length === 1));
    if (!m) return r;
    if (e.k6 === 'ex') return tidy(applyEx(r, m, ref));
    if (e.k6 === 'pl') return applyPl(r, m);
    return applyPd(r, m);
  }
  const at = (e, ref) => (ref[0] === 'n' ? e.num : e.den)[+ref.slice(1)];
  const layerOf = (e, ref) => (ref[0] === 'n' ? 'num' : 'den');
  function applyEx(r, m, ref) {
    const r0 = m.refs.includes(ref) ? ref : m.refs[0];
    switch (m.op) {
      case 'pow6': {
        const L = layerOf(r, r0), i = +r0.slice(1), g = r[L][i];
        const items = g.items.map(it => (it.t === 'n' ? N(fPow(it.v, g.e), g.grp) : Pw(it.b, it.e * g.e, g.grp)));
        r[L].splice(i, 1, ...items); break;
      }
      case 'zero6': { const L = layerOf(r, r0), i = +r0.slice(1); r[L][i] = N(1, r[L][i].grp); break; }
      case 'negx6': {
        const L = layerOf(r, r0), i = +r0.slice(1), f = r[L][i], O = L === 'num' ? 'den' : 'num';
        r[L].splice(i, 1);
        if (!r[L].length && L === 'num') r.num = [N(1)];
        r[O].push(Pw(f.b, -f.e, r[O].length ? r[O][r[O].length - 1].grp : 0)); break;
      }
      case 'muln6': case 'prod6': {
        const L = m.refs[0][0] === 'n' ? 'num' : 'den', is = m.refs.map(x => +x.slice(1)), first = r[L][is[0]];
        if (m.op === 'muln6') first.v = is.slice(1).reduce((a, j) => fMul(a, r[L][j].v), first.v);
        else first.e = is.slice(1).reduce((a, j) => a + r[L][j].e, first.e);
        r[L] = r[L].filter((f, j) => !is.slice(1).includes(j)); break;
      }
      case 'divn6': {
        const ti = +m.refs[0].slice(1), bi = +m.refs[1].slice(1), q = fDiv(r.num[ti].v, r.den[bi].v);
        if (r.sci || q.d === 1) { r.num[ti].v = q; r.den.splice(bi, 1); } else { r.num[ti].v = F(q.n); r.den[bi].v = F(q.d); }
        break;
      }
      case 'quot6': {
        const ti = +m.refs[0].slice(1), bi = +m.refs[1].slice(1);
        r.num[ti].e -= r.den[bi].e; r.den.splice(bi, 1); break;
      }
      case 'grp6': r.grouped = true; r.num.forEach(f => { f.grp = f.t === 'n' ? 0 : 1; }); r.den.forEach(f => { f.grp = f.t === 'n' ? 0 : 1; }); break;
      case 'norm6': {
        const ni = r.num.findIndex(f => f.t === 'n'), v = r.num[ni].v;
        let k = 0; let a = Math.abs(fv(v));
        while (a >= 10) { a /= 10; k++; } while (a < 1 && a > 0) { a *= 10; k--; }
        r.num[ni].v = fMul(v, pow10(-k));
        const pi = r.num.findIndex(f => f.t === 'p');
        if (pi >= 0) r.num[pi].e += k; else r.num.push(Pw('10', k, r.num[ni].grp));
        r.num.forEach(f => { f.grp = 0; }); r.grouped = false;
        break;
      }
      case 'std6': {
        const ni = r.num.findIndex(f => f.t === 'n'), pi = r.num.findIndex(f => f.t === 'p');
        r.num[ni].v = fMul(r.num[ni].v, pow10(r.num[pi].e)); r.num.splice(pi, 1); break;
      }
    }
    return r;
  }
  // the terms of A × B, row by row (each term of A times each term of B), as the box lays them out
  const boxTerms = (A, B) => A.flatMap(a => B.map(b => mMul(a, b)));
  function productOf(it, op) {
    const A = it.A, B = it.t === 'sq' ? it.A : it.B;
    if (op === 'sqb6') { const [a, b] = A; return [mMul(a, a), M(fMul(F(2), fMul(a.c, b.c)), a.x + b.x, a.y + b.y), mMul(b, b)]; }
    if (op === 'dos6') { const [a, b] = A; return [mMul(a, a), mNeg(mMul(b, b))]; }
    return boxTerms(A, B);
  }
  function applyPl(r, m) {
    const i = m.key[0] === 'i' ? +m.key.slice(1) : -1, it = r.items[i];
    switch (m.op) {
      case 'dneg6': r.items.splice(i, 1, ...it.terms.map(t => T(mNeg(t)))); break;
      case 'drop6': r.items.splice(i, 1, ...it.terms.map(t => T(t))); break;
      case 'box6': case 'sqb6': case 'dos6': {
        // a product with a minus in front keeps its minus outside a bracket: −(x² − 9), to be distributed next
        const res = productOf(it, m.op);
        r.items.splice(i, 1, ...((it.s || 1) < 0 ? [Grp(-1, res)] : res.map(T)));
        break;
      }
      case 'comb6': {
        const is = m.refs.map(x => +x.slice(1)), sum = is.reduce((a, j) => fAdd(a, r.items[j].m.c), F(0));
        r.items[is[0]] = T({ ...r.items[is[0]].m, c: sum });
        r.items = r.items.filter((x, j) => !is.slice(1).includes(j) && !(j === is[0] && fz(sum)));
        break;
      }
      case 'sort6': { const ts = plTerms(r).sort(byDeg); r.items = ts.map(T); break; }
    }
    return r;
  }
  function applyPd(r, m) {
    switch (m.op) {
      case 'fill6': r.filled = true; break;
      case 'split6': r.mode = 'split'; break;
      case 'divt6': { const { Q, R } = divide(r.N, r.D); r.Q = Q; r.R = R; r.done = true; break; }
      case 'long6': r.mode = 'long'; r.R = r.N.slice(); r.Q = r.N.map(() => F(0)); r.rows = []; break;
      case 'qt6': {
        const t = m.t, prod = [];
        for (let i = 0; i <= t.e + deg(r.D); i++) prod.push(F(0));
        r.D.forEach((q, i) => { prod[i + t.e] = fMul(q, t.c); });
        const top = deg(r.R);
        r.Q[t.e] = t.c;
        const R2 = pSub(r.R, prod); R2[top] = F(0);
        r.rows.push({ prod, rem: R2, lo: t.e });
        r.R = R2;
        if (deg(r.R) < deg(r.D)) r.done = true;
        break;
      }
      case 'syn6': { const { Q, R } = divide(r.N, r.D); r.mode = 'syn'; r.Q = Q; r.R = R; r.c = m.c; r.done = true; break; }
    }
    return r;
  }

  // ================================================================ path, skills, answers
  const HOME = { pow6: 'exprules', prod6: 'exprules', quot6: 'exprules', zero6: 'exprules', negx6: 'exprules', muln6: 'exprules', divn6: 'exprules',
    grp6: 'scinot', norm6: 'scinot', std6: 'scinot', dneg6: 'polyadd', drop6: 'polyadd', box6: 'polymul', sqb6: 'polymul', dos6: 'polymul',
    fill6: 'polydiv', long6: 'polydiv', syn6: 'polydiv', qt6: 'polydiv', split6: 'polydiv', divt6: 'polydiv' };
  function skillFor(m, e, main) {
    let home = HOME[m.op] || main;
    if (e.k6 === 'ex' && e.sci) home = 'scinot';
    if (m.op === 'comb6' || m.op === 'sort6') home = main;
    return home === main || isUnlocked(home) ? home : main;
  }
  function pathOf6(e, main) {
    const path = []; let s = e;
    for (let i = 0; i < 60; i++) { const m = canon6(s); if (!m) break; path.push({ state: s, move: m, skill: skillFor(m, s, main) }); s = apply6(s, m, m.ref); }
    return { path, end: s };
  }
  function answerOf(e, html) {
    if (e.k6 === 'pd') return pdAnswer(e, html);
    if (e.k6 === 'pl') return html ? plHtmlLine(e) : plText(e);
    return html ? exLine(e) : exText(e);
  }
  function makeEquation6(state, enemy) {
    const main = state.skill || 'exprules', { path, end } = pathOf6(state, main);
    return { start: state, end, path, main, skills: [...new Set(path.map(p => p.skill))], enemy, act2: true, act6: true, answer: F(0), answerText: '= ' + answerOf(end, false) };
  }
  function refreshPath(cur) {
    const fresh = pathOf6(cur.state, cur.main).path;
    cur.path = cur.path.slice(0, cur.step).concat(fresh);
  }

  // ================================================================ cards
  const tHtml = t => mText(M(t.c, t.e), true, false);
  const CARD = {
    pow6:   () => ({ label: 'Power rule', text: '(xᵃ)ⁿ = xᵃⁿ: raise every factor', kind: 'Power rule', icon: 'pow6' }),
    prod6:  () => ({ label: 'Product rule', text: 'xᵃ · xᵇ = xᵃ⁺ᵇ: add exponents', kind: 'Product rule', icon: 'prod6' }),
    quot6:  () => ({ label: 'Quotient rule', text: 'xᵃ / xᵇ = xᵃ⁻ᵇ: subtract exponents', kind: 'Quotient rule', icon: 'quot6' }),
    zero6:  () => ({ label: 'Zero power', text: 'x⁰ = 1 (any base except 0)', kind: 'Zero exponent', icon: 'zero6' }),
    negx6:  () => ({ label: 'Neg. power', text: 'x⁻ⁿ = 1/xⁿ: flip across the bar', kind: 'Negative exponent', icon: 'negx6' }),
    muln6:  () => ({ label: `${TIMES} numbers`, text: 'Multiply the numbers together', kind: 'Multiply the numbers', icon: 'mul' }),
    divn6:  () => ({ label: `${DIV} numbers`, text: 'Divide or reduce the numbers', kind: 'Divide the numbers', icon: 'div' }),
    grp6:   () => ({ label: 'Group tens', text: 'Numbers together, tens together', kind: 'Group the tens', icon: 'grp6' }),
    norm6:  () => ({ label: 'Normalize', text: 'Make the number 1 to 10', kind: 'Normalize', icon: 'norm6' }),
    std6:   () => ({ label: 'Standard', text: 'Move the point, drop the 10ⁿ', kind: 'Standard form', icon: 'std6' }),
    dneg6:  () => ({ label: 'Minus in', text: 'Flip the sign of every term inside', kind: 'Distribute the minus', icon: 'neg' }),
    drop6:  () => ({ label: 'Drop ( )', text: 'A + in front: brackets go away', kind: 'Drop the brackets', icon: 'drop6' }),
    comb6:  () => ({ label: 'Combine', text: 'Same power: add the numbers', kind: 'Combine by degree', icon: 'comb' }),
    sort6:  () => ({ label: 'Order', text: 'Highest power first', kind: 'Standard form order', icon: 'sort6' }),
    box6:   () => ({ label: 'Multiply out', text: 'Every term times every term', kind: 'Multiply out (box)', icon: 'box6' }),
    sqb6:   () => ({ label: '(a + b)²', text: '(a + b)² = a² + 2ab + b²', kind: 'Square a binomial', icon: 'sqb6' }),
    dos6:   () => ({ label: 'a² − b²', text: '(a + b)(a − b) = a² − b²', kind: 'Difference of squares', icon: 'dos6' }),
    fill6:  () => ({ label: '0 holders', text: 'Write 0 for each missing power', kind: 'Fill in 0 terms', icon: 'fill6' }),
    long6:  () => ({ label: 'Long div.', text: 'Set up long division', kind: 'Long division', icon: 'long6' }),
    syn6:   c => ({ label: `Synth. ${fracText(c.c)}`, text: `Synthetic division with c = ${fracText(c.c)}`, kind: 'Synthetic division', icon: 'syn6' }),
    qt6:    c => ({ label: `Top: ${tHtml(c.t)}`, text: `Next term on top: ${tHtml(c.t)}`, kind: 'Quotient term', icon: 'long6' }),
    split6: () => ({ label: 'Split', text: 'One fraction per term on top', kind: 'Split the fraction', icon: 'split6' }),
    divt6:  () => ({ label: 'Each term', text: 'Divide each term by the bottom', kind: 'Divide each term', icon: 'quot6' }),
  };
  const info = c => (c && c.a6 && CARD[c.op] ? CARD[c.op](c) : null);
  const label = c => (c && c.op === 'trap' && c.a6 ? `<span class="clong l6">${c.label}</span>` : info(c) ? `<span class="clong l6">${info(c).label}</span>` : null);
  const text = c => (c && c.op === 'trap' && c.a6 ? c.text : info(c) ? info(c).text : null);
  const kind = c => (c && c.op === 'trap' && c.a6 ? 'Trap: ' + c.trap : info(c) ? info(c).kind : null);
  const icon = c => (c && c.op === 'trap' && c.a6 ? c.icon : info(c) ? info(c).icon : null);
  const SLOT = { pow6: 0, muln6: 1, prod6: 2, divn6: 3, quot6: 4, zero6: 5, negx6: 6, grp6: 0, norm6: 5, std6: 6,
    dneg6: 0, drop6: 1, box6: 0, sqb6: 1, dos6: 2, comb6: 3, sort6: 4, fill6: 0, long6: 1, split6: 0, divt6: 1 };
  const slot = c => (c && c.a6 && c.op !== 'trap' ? SLOT[c.op] ?? null : null);
  const targetSel = c => (c && (c.a6 || (c.op === 'trap' && c.a6)) && (c.scope || 'both') === 'part' ? '#equation .tok[data-ref]' : null);

  // Where a ◎ card can go. Legal places, one per thing it changes (both x's of x² · x³ are one place),
  // or else every place of its kind, so a wrong card still has to be dropped somewhere.
  function kindPlaces(e, op) {
    const fac = test => [...e.num.map((f, i) => [f, 'n' + i]), ...e.den.map((f, i) => [f, 'd' + i])].filter(([f]) => test(f)).map(x => x[1]);
    const items = test => e.items.map((it, i) => [it, 'i' + i]).filter(([it]) => test(it)).map(x => x[1]);
    if (e.k6 === 'ex') {
      if (op === 'pow6') return fac(f => f.t === 'g');
      if (op === 'zero6') return fac(f => f.t !== 'n');
      if (['prod6', 'quot6', 'negx6'].includes(op)) return fac(f => f.t === 'p');
      if (['muln6', 'divn6', 'norm6', 'std6'].includes(op)) return fac(f => f.t === 'n');
      if (op === 'grp6') return ['X'];
      return [];
    }
    if (e.k6 === 'pl') {
      if (op === 'dneg6' || op === 'drop6') return items(it => it.t === 'grp');
      if (['box6', 'sqb6', 'dos6'].includes(op)) return items(it => it.t === 'prod' || it.t === 'sq');
      if (op === 'comb6') return items(it => it.t === 'term');
      if (op === 'sort6') return ['X'];
      return [];
    }
    return ['fill6', 'long6', 'syn6', 'qt6', 'split6', 'divt6'].includes(op) ? ['F'] : [];
  }
  function places(e, c) {
    const op = c.op === 'trap' ? c.like : c.op;
    if (!op) return [];
    const legal = movesOf(e).filter(m => m.op === op);
    if (legal.length) return [...new Set(legal.map(m => m.refs[0]))];
    return kindPlaces(e, op);
  }
  const refEl = ref => $('equation').querySelector(`.tok[data-ref="${ref}"]`);
  function autoTarget(c) {
    if (!cur || !cur.act6) return 'pass';
    if (!c.a6) return 'pass';
    const ps = places(cur.state, c);
    if (ps.length >= 2) return undefined;
    if (!ps.length) return null;
    return refEl(ps[0]) || ps[0];
  }
  // While a card is held, the places it can go glow (Easy and Normal, or Hard after a wrong move).
  function onDrag(c, on) {
    document.querySelectorAll('.ok6').forEach(el => el.classList.remove('ok6'));
    if (!on || !cur || !cur.act6) return;
    const hl = difficulty.highlight === 'on' || isTutorial() || (difficulty.highlight === 'afterWrong' && cur.wrong > 0);
    if (!hl || !targetSel(c)) return;
    for (const el of document.querySelectorAll('#equation .tok[data-ref]')) if (correct6(cur.state, c, el)) el.classList.add('ok6');
  }

  // ---------------------------------------------------------------- hands
  const DECOYS = [1, 1, 2, 2];
  function trap(name, like, lbl, txt, why, iconKey) { return { op: 'trap', a6: true, trap: name, like, scope: 'part', label: lbl, text: txt, why, icon: iconKey }; }
  const ex1 = (b = 'x') => b;
  // Rule decoys (the classic mistakes, dealt at every level outside tutorials) and Expert traps.
  function specials(e, want) {
    const out = { rule: [], traps: [] };
    const ms = movesOf(e), has = op => ms.some(m => m.op === op);
    if (e.k6 === 'ex') {
      const lay = [...e.num, ...e.den];
      if (has('prod6')) {
        const m = ms.find(o => o.op === 'prod6'), fs = m.refs.map(r => at(e, r)), b = fs[0].b;
        const es = fs.map(f => f.e), prodE = es.reduce((a, x) => a * x, 1), sumE = es.reduce((a, x) => a + x, 0);
        if (prodE !== sumE) out.rule.push(trap('multiply exponents', 'prod6', `${TIMES} exponents`, `${fs.map(f => facText(f)).join(' · ')} = ${b}${supText(prodE)}: multiply the powers`,
          P(`${fs.map(f => facText(f)).join(' · ')} means ${es.map(x => `${x} ${b}'s`).join(' times ')} multiplied together: that's ${sumE} ${b}'s in a row, so ${b}${supText(sumE)}. Multiplying same bases <b>adds</b> the exponents. You multiply exponents only for a power of a power, like (${b}${supText(es[0])})${supText(es[1] || 2)}.`), 'prod6'));
      }
      const g = lay.find(f => f.t === 'g' && f.e > 1);
      if (has('pow6') && g) {
        const p = g.items.find(i => i.t === 'p'), n = g.items.find(i => i.t === 'n');
        if (p && p.e > 1 && p.e + g.e !== p.e * g.e) out.rule.push(trap('add exponents', 'pow6', 'Add powers', `(${p.b}${supText(p.e)})${supText(g.e)} = ${p.b}${supText(p.e + g.e)}: add the powers`,
          P(`(${p.b}${supText(p.e)})${supText(g.e)} is ${p.b}${supText(p.e)} written ${g.e} times: ${Array(g.e).fill(p.b + supText(p.e)).join(' · ')} = ${p.b}${supText(p.e * g.e)}. A power of a power <b>multiplies</b> the exponents. Adding is for x² · x³, two powers multiplied side by side.`), 'pow6'));
        if (n && !fIs(fAbs(n.v), 1)) out.rule.push(trap('number left out', 'pow6', 'Power x only', `${facText(g)}: raise only the letters, keep ${facText(n)}`,
          P(`The power is on the whole bracket, so the number inside is raised too: (${facText(n)})${supText(g.e)} = ${fracText(fPow(n.v, g.e))}. ${facText(g)} = ${itemsText(g.items.map(it => (it.t === 'n' ? N(fPow(it.v, g.e)) : Pw(it.b, it.e * g.e))))}.`), 'pow6'));
      }
      if (has('zero6')) {
        const z = ms.find(o => o.op === 'zero6'), f = at(e, z.refs[0]);
        out.rule.push(trap('zero power is 0', 'zero6', `${f.t === 'g' ? '( )' : f.b}⁰ = 0`, `${facText(f)} = 0: a power of 0 leaves nothing`,
          P(`Anything (except 0) to the power 0 is <b>1</b>, not 0. Look at the pattern: x³/x³ = x³⁻³ = x⁰, and anything divided by itself is 1. So ${facText(f)} = 1${f.t === 'p' && e.num.some(o => o.t === 'n' && !fIs(o.v, 1)) ? '. The number in front stays: only the power is 1' : ''}.`), 'zero6'));
      }
      if (has('negx6')) {
        const z = ms.find(o => o.op === 'negx6'), f = at(e, z.refs[0]);
        out.rule.push(trap('negative means minus', 'negx6', `${MINUS}${f.b}${supText(-f.e)}`, `${facText(f)} = ${MINUS}${f.b}${supText(-f.e)}: a negative power makes it negative`,
          P(`A negative exponent doesn't make anything negative. It means "one over": ${facText(f)} = 1/${f.b}${supText(-f.e)}. The factor moves across the fraction bar and the exponent turns positive.`), 'negx6'));
      }
      if (has('quot6')) {
        const q = ms.find(o => o.op === 'quot6'), a = at(e, q.refs[0]), b = at(e, q.refs[1]);
        if (b.e && a.e % b.e === 0 && a.e / b.e !== a.e - b.e) out.traps.push(trap('divide exponents', 'quot6', `${DIV} exponents`, `${facText(a)}/${facText(b)} = ${a.b}${supText(a.e / b.e)}: divide the powers`,
          P(`${facText(a)}/${facText(b)}: ${b.e} of the ${a.e} ${a.b}'s on top cancel with the ${b.e} on the bottom, leaving ${a.e - b.e}. Dividing same bases <b>subtracts</b> the exponents: ${a.b}${supText(a.e - b.e)}.`), 'quot6'));
      }
      if (has('norm6')) {
        const ni = e.num.findIndex(f => f.t === 'n'), pi = e.num.findIndex(f => f.t === 'p'), v = e.num[ni].v, p = pi >= 0 ? e.num[pi].e : 0;
        const r = apply6(e, C6('norm6'), 'n' + ni), nv = r.num.find(f => f.t === 'n').v, ne = r.num.find(f => f.t === 'p').e, wrong = p - (ne - p);
        out.rule.push(trap('power the wrong way', 'norm6', `${decText(nv)} × 10${supText(wrong)}`, `${decText(v)}${pi >= 0 ? ' × 10' + supText(p) : ''} = ${decText(nv)} × 10${supText(wrong)}`,
          P(`Moving the decimal point changes the number, so the power of 10 has to make up for it. ${decText(v)} → ${decText(nv)} made the number ${Math.abs(fv(v)) >= 10 ? 'smaller' : 'bigger'}, so the power of 10 goes ${Math.abs(fv(v)) >= 10 ? '<b>up</b>' : '<b>down</b>'}: ${decText(nv)} × 10${supText(ne)}.`), 'norm6'));
      }
      if (has('std6')) {
        const n = e.num.find(f => f.t === 'n'), p = e.num.find(f => f.t === 'p');
        if (p.e > 0 && !isInt(n.v)) {
          const digits = String(Math.abs(n.v.n)) + '0'.repeat(p.e);
          out.rule.push(trap('add zeros', 'std6', `Add ${p.e} zero${p.e > 1 ? 's' : ''}`, `${decText(n.v)} × 10${supText(p.e)} = ${groupDigits(digits)}`,
            P(`10${supText(p.e)} moves the decimal point ${p.e} places to the right. ${decText(n.v)} already has digits after the point, so they use up some of the moves: ${decText(n.v)} × 10${supText(p.e)} = ${groupDigits(decText(fMul(n.v, pow10(p.e))))}.`), 'std6'));
        }
      }
      if (has('grp6')) out.traps.push(trap('multiply the tens', 'grp6', '10 · 10 = 100', `${e.num.filter(f => f.t === 'p').map(f => facText(f)).join(' · ')} = 100 to a power`,
        P('10⁴ · 10³ is still a power of <b>10</b>: the base stays 10 and the exponents add, 10⁷. Group the numbers and the tens first, then use the Product rule on the tens.'), 'grp6'));
      return out;
    }
    if (e.k6 === 'pl') {
      const gi = e.items.findIndex(it => it.t === 'grp' && it.s < 0);
      if (gi >= 0) {
        const g = e.items[gi], wrong = g.terms.map((t, j) => (j === 0 ? mNeg(t) : t)), right = g.terms.map(mNeg);
        out.rule.push(trap('first sign only', 'dneg6', 'Minus in<span class="ftag">1st only</span>', `${MINUS}(${polyText(g.terms)}) = ${polyText(wrong)}`,
          P(`The minus is in front of the <b>whole</b> bracket, so it changes every term inside, not just the first: ${MINUS}(${polyText(g.terms)}) = ${polyText(right)}. Think of it as ${MINUS}1 times each term.`), 'neg'));
      }
      const si = e.items.findIndex(it => it.t === 'sq' && it.A.length === 2);
      if (si >= 0) {
        const [a, b] = e.items[si].A, mid = M(fMul(F(2), fMul(a.c, b.c)), a.x + b.x, a.y + b.y);
        out.rule.push(trap('square each term', 'sqb6', 'Square each', `(${polyText([a, b])})² = ${polyText([mMul(a, a), mMul(b, b)])}`,
          P(`(${polyText([a, b])})² means (${polyText([a, b])})(${polyText([a, b])}). Multiplied out, that's four products, and the two middle ones make <b>${mText(mid, true)}</b>: (${polyText([a, b])})² = ${polyText([mMul(a, a), mid, mMul(b, b)])}. Squaring each term forgets the middle.`), 'sqb6'));
      }
      const pi = e.items.findIndex(it => it.t === 'prod' && it.A.length === 2 && it.B.length === 2 && !isConj(it));
      if (pi >= 0) {
        const { A, B } = e.items[pi];
        out.traps.push(trap('firsts and lasts', 'box6', 'Firsts, lasts', `(${polyText(A)})(${polyText(B)}) = ${polyText([mMul(A[0], B[0]), mMul(A[1], B[1])])}`,
          P(`Every term in the first bracket multiplies every term in the second: 2 × 2 = 4 products. Firsts and lasts leave out the outer and inner ones (${mText(mMul(A[0], B[1]), true)} and ${mText(mMul(A[1], B[0]), true)}).`), 'box6'));
      }
      const ts = plTerms(e);
      const unlike = ts.find((t, j) => ts.some((o, k) => k !== j && mkey(o) !== mkey(t) && (o.y === t.y) && o.x !== t.x && o.x && t.x));
      if (unlike && has('comb6') || (unlike && !e.items.some(it => it.t !== 'term'))) {
        const o = ts.find(q => mkey(q) !== mkey(unlike) && q.x && q.y === unlike.y);
        if (o) out.traps.push(trap('add unlike powers', 'comb6', 'Add powers', `${mText(unlike, true)} + ${mText(o, true).replace(/^−/, '(−') + (o.c.n < 0 ? ')' : '')} = ${mBody(M(fAdd(unlike.c, o.c), unlike.x + o.x, unlike.y), false)}`,
          P(`${mBody(unlike)} and ${mBody(o)} are <b>unlike</b> terms: different powers of x can't be added into one term. Only terms with exactly the same power combine (x² with x², x with x).`), 'comb'));
      }
      return out;
    }
    // pd
    if (want && want.op === 'syn6') out.rule.push(trap('wrong sign for c', 'syn6', `Synth. ${fracText(fNeg(want.c))}`, `Synthetic division with c = ${fracText(fNeg(want.c))}`,
      P(`Synthetic division uses the c in x ${MINUS} c. ${dText(e.D)} = x ${MINUS} (${fracText(want.c)}), so c = <b>${fracText(want.c)}</b>, the number that makes the divisor 0. The sign flips.`), 'syn6'));
    if (want && want.op === 'fill6') out.rule.push(trap('skip the 0 terms', 'fill6', 'Long div.', 'Set up long division as written',
      P(`${dText(e.N)} has no ${holes(e.N).map(k => (k === 0 ? 'constant' : k === 1 ? 'x' : 'x' + supText(k)) + ' term').join(' and no ')}. Without a 0 written in its place, the columns slip and like terms end up under unlike ones. Write ${toTerms(e.N, true).filter(t => fz(t.c)).map(t => '0' + mBody({ ...t, c: F(1) }).replace(/^1$/, '')).join(' and ')} first.`), 'long6'));
    if (want && want.op === 'qt6') {
      const r = deg(e.R), lead = M(e.R[r], r);
      out.traps.push(trap('forgot to divide', 'qt6', `Top: ${mText(lead, true)}`, `Next quotient term: ${mText(lead, true)} (copy the leading term)`,
        P(`The next term on top is the leading term divided by the divisor's leading term: ${mText(lead, true)} ${DIV} ${mText(M(e.D[deg(e.D)], deg(e.D)), true)} = ${tHtml(want.t)}.`), 'long6'));
    }
    return out;
  }
  function family(e, want) {
    if (e.k6 === 'ex') {
      if (e.sci) return ['grp6', 'muln6', 'prod6', 'divn6', 'quot6', 'norm6', e.ask === 'tostd' ? 'std6' : null, 'pow6'].filter(Boolean).map(op => C6(op));
      return ['pow6', 'prod6', 'quot6', 'zero6', 'negx6', 'muln6', 'divn6'].map(op => C6(op));
    }
    if (e.k6 === 'pl') {
      const f = ['comb6', 'sort6'];
      if (e.skill === 'polyadd' || e.items.some(it => it.t === 'grp')) f.push('dneg6', 'drop6');
      if (e.skill !== 'polyadd' || e.items.some(it => it.t === 'prod' || it.t === 'sq')) f.push('box6', 'sqb6', 'dos6');
      return f.map(op => C6(op));
    }
    const f = ['fill6', 'long6', 'split6', 'divt6'].map(op => C6(op));
    if (deg(e.D) === 1 && !isMonoD(e.D)) { const c = fDiv(fNeg(e.D[0]), e.D[1]); f.push(C6('syn6', { c }), C6('syn6', { c: fNeg(c) })); if (!isInt(c)) f.push(C6('syn6', { c: fNeg(e.D[0]) })); }
    if (e.mode === 'long' && !e.done) {
      const t = want && want.t ? want.t : nextTerm(e);
      const alts = [{ c: fNeg(t.c), e: t.e }, { c: t.c, e: t.e + 1 }, { c: t.c, e: Math.max(0, t.e - 1) }, { c: e.R[deg(e.R)], e: t.e }, { c: fMul(t.c, F(2)), e: t.e }];
      alts.forEach(a => f.push(C6('qt6', { t: a })));
    }
    return f;
  }
  const alsoRight = (e, c) => movesOf(e).some(m => matchCard(m, c));
  function makeHand6(e, correct, size) {
    const tut = isTutorial(), L = lvl();
    const hand = [correct], seen = new Set([cardLabel(correct)]);
    const add = c => { if (hand.length >= size) return; const k = cardLabel(c); if (seen.has(k)) return; if (c.op !== 'trap' && alsoRight(e, c)) return; seen.add(k); hand.push(c); };
    const sp = specials(e, correct);
    if (!tut && L >= 3) sp.traps.slice(0, 1).forEach(add);
    if (!tut) sp.rule.slice(0, DECOYS[L]).forEach(add);
    shuffle(family(e, correct)).forEach(add);
    return shuffle(hand);
  }
  void ex1;

  // ================================================================ wrong moves
  const S = (long, short, more) => (long ? P(more || short) : short);
  function why6(e, card, target, long) {
    const ref = refOf(target), ms = movesOf(e), want = ms[0];
    if (card.op === 'trap') return long ? card.why : 'That\'s a trap: it isn\'t true. Tap Why? to see why.';
    if (!card.a6) return S(long, 'That card doesn\'t fit here.');
    const legal = ms.filter(m => matchCard(m, card));
    if (legal.length) {   // the right card on the wrong part
      const where = legal[0].refs.map(r => (r === 'X' || r === 'F' ? 'the expression' : refText(e, r))).join(' and ');
      return S(long, `Right rule, wrong place: use it on ${where}.`);
    }
    if (e.k6 === 'ex') return whyEx(e, card, ref, want, long);
    if (e.k6 === 'pl') return whyPl(e, card, ref, want, long);
    return whyPd(e, card, ref, want, long);
  }
  function refText(e, r) {
    if (e.k6 === 'ex') { const f = at(e, r); return f ? facText(f, e.sci) : 'that'; }
    if (e.k6 === 'pl') { const it = e.items[+r.slice(1)]; return it ? itemText(it, true) : 'that'; }
    return 'the division';
  }
  const opName = op => (CARD[op] ? CARD[op]({ c: F(0), t: { c: F(1), e: 0 } }).kind : op);
  function whyEx(e, card, ref, want, long) {
    const f = ref && ref !== 'X' ? at(e, ref) : null, all = [...e.num, ...e.den];
    const hasG = all.some(x => x.t === 'g');
    const needG = e.sci && !e.grouped && (grpsOf(e.num).length > 1 || e.den.length > 0);
    const nextIs = want ? ` Next: ${opName(want.op)}.` : '';
    switch (card.op) {
      case 'pow6':
        return hasG ? S(long, 'Drop it on the bracket with the power outside.') : S(long, 'There\'s no bracket raised to a power here.', `The Power rule is for a bracket with a power outside, like (2x³)². Nothing here has one.${nextIs}`);
      case 'zero6':
        return S(long, 'Nothing here has a power of 0.', `The Zero power rule turns x⁰ (or (…)⁰) into 1. No exponent here is 0.${nextIs}`);
      case 'negx6':
        if (e.sci) return S(long, 'In scientific notation a negative power of 10 is fine.', 'Scientific notation is a number from 1 to 10 times a power of 10, and the power can be negative: 3.2 × 10⁻⁴ is finished. Don\'t move it.');
        return S(long, 'No exponent here is negative.', `The Negative power rule moves x⁻ⁿ across the fraction bar as xⁿ. Nothing here has a negative exponent.${nextIs}`);
      case 'prod6': {
        if (needG) return S(long, 'Group the numbers and the powers of 10 first.');
        if (hasG) return S(long, 'Deal with the bracket first: Power rule.', 'A power outside a bracket applies to everything inside it, so open the bracket with the Power rule before combining with what\'s outside.');
        if (f && f.t === 'p' && e.den.some(o => o.t === 'p' && o.b === f.b) && e.num.some(o => o.t === 'p' && o.b === f.b)) return S(long, `The other ${f.b} is across the fraction bar: that's the Quotient rule.`);
        return S(long, 'There\'s no base written twice in a product.', `The Product rule joins two powers of the same base that are multiplied, like x² · x³ = x⁵. Here every base appears only once on its side of the bar.${nextIs}`);
      }
      case 'quot6': {
        if (needG) return S(long, 'Group the numbers and the powers of 10 first.');
        if (hasG) return S(long, 'Open the bracket first: Power rule.');
        const b = e.den.find(o => o.t === 'p' && e.num.some(q => q.t === 'p' && q.b === o.b));
        if (b && e.num.filter(q => q.t === 'p' && q.b === b.b).length > 1) return S(long, `Join the ${b.b}'s on top first (Product rule).`);
        if (b && e.den.filter(q => q.t === 'p' && q.b === b.b).length > 1) return S(long, `Join the ${b.b}'s on the bottom first (Product rule).`);
        return S(long, 'No base is on both the top and the bottom.', `The Quotient rule is for the same base on top and bottom, like x⁵/x² = x³.${nextIs}`);
      }
      case 'muln6':
        if (needG) return S(long, 'Group the numbers together first.');
        return S(long, 'There aren\'t two numbers multiplied on one side.', `Multiply the numbers needs two numbers in a product (on the same side of the fraction bar).${nextIs}`);
      case 'divn6': {
        if (needG) return S(long, 'Group the numbers and the powers of 10 first.');
        const a = e.num.filter(o => o.t === 'n'), b = e.den.filter(o => o.t === 'n');
        if (!b.length) return S(long, 'There\'s no number on the bottom to divide by.');
        if (!a.length) return S(long, `There's no number on top to divide: the ${fracText(b[0].v)} stays on the bottom.`);
        if (a.length > 1 || b.length > 1) return S(long, 'Multiply the numbers on each side first.');
        return S(long, `${fracText(a[0].v)}/${fracText(b[0].v)} is already in lowest terms.`, `${fracText(a[0].v)} and ${fracText(b[0].v)} share no factor, so the numbers can't be reduced. Leave them as a fraction.${nextIs}`);
      }
      case 'grp6':
        if (!e.sci) return S(long, 'There are no powers of 10 here.');
        if (e.grouped || !needG) return S(long, 'It\'s already grouped.');
        return S(long, 'Open the bracket with the power first.');
      case 'norm6': {
        if (!e.sci) return S(long, 'That\'s for scientific notation.');
        if (e.ask === 'tostd') return S(long, 'The question asks for standard form, not scientific notation.', 'Standard form means the number written out in full (like 310 000), with no power of 10.');
        if (needG || e.num.filter(o => o.t === 'n').length > 1 || e.den.length || e.num.filter(o => o.t === 'p').length > 1) return S(long, 'Finish the multiplying and dividing first.', `Normalize at the end, once there is one number times one power of 10.${nextIs}`);
        const n = e.num.find(o => o.t === 'n');
        return S(long, `${decText(n.v)} is already from 1 to 10.`, `Scientific notation needs the number to be at least 1 and less than 10. ${decText(n.v)} already is, so it's done.`);
      }
      case 'std6':
        return S(long, 'The question asks for scientific notation.', 'Standard form writes the number out in full. Here the answer should be in scientific notation: a number from 1 to 10 times a power of 10.');
    }
    return S(long, 'That card doesn\'t fit here.');
  }
  function whyPl(e, card, ref, want, long) {
    const it = ref && ref[0] === 'i' ? e.items[+ref.slice(1)] : null, ms = movesOf(e);
    const structural = e.items.some(x => x.t !== 'term');
    switch (card.op) {
      case 'dneg6':
        if (it && it.t === 'grp' && it.s > 0) return S(long, 'That bracket has a + in front: just drop the brackets.', 'A + in front of brackets changes nothing: (x² − 5x) stays x² − 5x. Only a minus in front flips every sign.');
        return S(long, 'There\'s no minus in front of a bracket.');
      case 'drop6':
        if (it && it.t === 'grp' && it.s < 0) return S(long, 'A minus in front: it changes every sign inside.', `${MINUS}(${polyText(it.terms)}) = ${polyText(it.terms.map(mNeg))}. Dropping the brackets without flipping the signs changes the value.`);
        return S(long, 'There are no + brackets to drop.');
      case 'comb6': {
        if (structural && e.items.some(x => x.t !== 'term' && (x.terms || x.B || x.A))) {
          const keys = new Set(plTerms(e).map(mkey));
          const inside = e.items.filter(x => x.t === 'grp').flatMap(x => x.terms).some(t => keys.has(mkey(t)));
          if (inside || e.items.some(x => x.t !== 'term')) return S(long, 'Clear the brackets first.', 'Terms inside brackets can\'t be combined with terms outside until the brackets are gone (distribute the minus, drop a + bracket, or multiply out).');
        }
        return S(long, 'There are no like terms left.', 'Like terms have exactly the same power (3x² and −x²). Every power here appears once.');
      }
      case 'sort6':
        if (ms.length) return S(long, 'Not yet: clear the brackets and combine first.');
        return S(long, 'It\'s already in order, highest power first.');
      case 'box6':
        return S(long, 'There\'s nothing left to multiply.');
      case 'sqb6':
        if (it && it.t === 'prod') return S(long, 'That isn\'t a square: the two brackets are different.', `(a + b)² is one bracket times itself. ${itemText(it, true)} has two different brackets, so multiply it out.`);
        return S(long, 'There\'s no bracket squared here.');
      case 'dos6':
        if (it && (it.t === 'prod' || it.t === 'sq')) return S(long, 'That isn\'t (a + b)(a − b).', `The difference of squares pattern needs the same two terms with opposite signs in the middle, like (x + 3)(x − 3). ${itemText(it, true)} isn't that shape, so multiply it out.`);
        return S(long, 'There\'s no product here.');
    }
    return S(long, 'That card doesn\'t fit here.');
  }
  function whyPd(e, card, ref, want, long) {
    const dl = dText(e.D);
    switch (card.op) {
      case 'fill6': return holes(e.N).length ? S(long, 'Already filled in.') : S(long, 'No powers are missing.', `${dText(e.N)} has every power from x${supText(deg(e.N))} down, so nothing needs a 0.`);
      case 'split6': case 'divt6':
        if (!isMonoD(e.D)) return S(long, `${dl} has two terms: you can't split the fraction over it.`, `Splitting into one fraction per term only works when the bottom is a single term. (a + b)/c = a/c + b/c, but c/(a + b) is not c/a + c/b. Use long or synthetic division.`);
        return S(long, e.mode === 'split' ? 'It\'s split: now divide each term.' : 'Split the fraction first.');
      case 'long6':
        if (isMonoD(e.D)) return S(long, 'The bottom is one term: split the fraction instead.');
        if (holes(e.N).length && !e.filled) return S(long, 'Write 0 for the missing powers first.', `${dText(e.N)} is missing some powers. Write them as 0 terms first, or the columns won't line up.`);
        if (e.mode) return S(long, 'Long division is already set up.');
        if (e.method === 'syn') return S(long, 'The question asks for synthetic division.');
        return S(long, 'Not now.');
      case 'syn6':
        if (isMonoD(e.D)) return S(long, 'The bottom is one term: split the fraction instead.');
        if (!monicLin(e.D)) return S(long, `Synthetic division only works for x ${MINUS} c. ${dl} isn't that shape.`, `Synthetic division divides by x ${MINUS} c (x with no number in front). ${dl} has ${deg(e.D) > 1 ? 'a higher power' : 'a number in front of x'}, so use long division.`);
        if (holes(e.N).length && !e.filled) return S(long, 'Write 0 for the missing powers first.', 'Synthetic division uses every coefficient in a row, including the 0s for missing powers. Fill them in first.');
        if (e.mode) return S(long, 'Keep going with the long division.');
        if (e.method === 'long') return S(long, 'The question asks for long division.');
        return S(long, `${dl} = x ${MINUS} (${fracText(fNeg(e.D[0]))}), so c = ${fracText(fNeg(e.D[0]))}.`, `Synthetic division uses the c in x ${MINUS} c: the value that makes the divisor 0. For ${dl}, c = <b>${fracText(fNeg(e.D[0]))}</b>.`);
      case 'qt6': {
        if (e.mode !== 'long') return S(long, 'Set up the division first.');
        const t = nextTerm(e), r = deg(e.R);
        return S(long, `Divide the leading terms: ${mText(M(e.R[r], r), true)} ${DIV} ${mText(M(e.D[deg(e.D)], deg(e.D)), true)} = ${tHtml(t)}.`,
          `Each step of long division: divide the first term left (${mText(M(e.R[r], r), true)}) by the first term of the divisor (${mText(M(e.D[deg(e.D)], deg(e.D)), true)}). That's <b>${tHtml(t)}</b>: watch the sign and the power.`);
      }
    }
    return S(long, 'That card doesn\'t fit here.');
  }
  const isCorrect = (cur, card, target) => correct6(cur.state, card, target);
  const whyWrong = (cur, card, target) => why6(cur.state, card, target, false);
  function explain6({ state: e, card, ref }) {
    if (!e || !e.k6 || !card) return null;
    return why6(e, card, ref, true);
  }
  if (typeof registerWhy === 'function') registerWhy(explain6);

  // ================================================================ rendering
  const sym = (html, cls = '') => { const d = document.createElement('div'); d.className = 'tok a4 s6 ' + cls; d.innerHTML = html; return d; };
  // Token contents sit in a span: a <sup> straight inside the flex box would be laid out as a flex item and lose its raise.
  const W = h => `<span class="w6">${h}</span>`;
  function facTok(f, ref, e, cls = '') { const t = TOK(W(facHtml(f, e.sci)), 'f6', ref, 'f6 ' + cls); t.dataset.kind = f.t; return t; }
  function rowEl(els) { const r = document.createElement('span'); r.className = 'row4'; els.forEach(x => r.appendChild(x)); return r; }
  function fracEl(top, bot) {
    const w = document.createElement('span'); w.className = 'n4 frac4 frac6';
    w.append(rowEl(top), TOK('<span class="bar4"></span>', 'bar', null), rowEl(bot));
    return w;
  }
  function layerEls(list, L, e) {
    const out = [], pre = L === 'num' ? 'n' : 'd', ix = list.map((f, i) => [f, i]);
    if (e.sci && e.grouped) {
      const part = l => { const w = l.length > 1; if (w) out.push(sym('(')); l.forEach(([f, i], j) => { if (j) out.push(sym('·')); out.push(facTok(f, pre + i, e)); }); if (w) out.push(sym(')')); };
      const ns = ix.filter(([f]) => f.t === 'n'), ps = ix.filter(([f]) => f.t !== 'n');
      if (ns.length) part(ns);
      if (ns.length && ps.length) out.push(sym(TIMES));
      if (ps.length) part(ps);
      return out;
    }
    const gs = grpsOf(list);
    const single = !e.sci && gs.every(g => list.filter(f => f.grp === g).length === 1);
    const wrap = gs.length > 1 && !single;
    gs.forEach((g, gi) => {
      if (gi && single) out.push(sym('·'));
      if (wrap) out.push(sym('(', gi ? 'tightP' : ''));
      ix.filter(([f]) => f.grp === g).forEach(([f, i], j) => {
        if (j && e.sci) out.push(sym(TIMES));
        out.push(facTok(f, pre + i, e, j && !e.sci ? 'tightL' : ''));
      });
      if (wrap) out.push(sym(')', 'tightL'));
    });
    return out;
  }
  function renderEx(e) {
    const el = $('equation');
    if (e.sci && e.grouped && e.den.length) {
      [f => f.t === 'n', f => f.t !== 'n'].forEach((k, j) => {
        const top = e.num.map((f, i) => [f, 'n' + i]).filter(([f]) => k(f)), bot = e.den.map((f, i) => [f, 'd' + i]).filter(([f]) => k(f));
        if (!top.length && !bot.length) return;
        if (j && el.children.length) el.appendChild(sym(TIMES));
        const mk = l => (l.length ? l.flatMap(([f, r], q) => (q ? [sym('·'), facTok(f, r, e)] : [facTok(f, r, e)])) : [sym('1')]);
        if (bot.length) el.appendChild(fracEl(mk(top), mk(bot))); else mk(top).forEach(x => el.appendChild(x));
      });
      return;
    }
    const top = layerEls(e.num, 'num', e);
    if (!e.den.length) top.forEach(x => el.appendChild(x));
    else el.appendChild(fracEl(top, layerEls(e.den, 'den', e)));
  }
  const exLine = e => exText(e);

  const inner = (terms, cls = 'it6') => terms.map((m, j) => `<span class="${cls}">${mText(m, j === 0, true)}</span>`).join(' ');
  function itemTok(it, i, first) {
    const ref = 'i' + i;
    if (it.t === 'term') return TOK(W(mText(it.m, first, true)), 'pt6', ref, 'pt6');
    const ld = `<span class="gs6">${first ? ((it.s || 1) < 0 ? MINUS : '') : (it.s || 1) < 0 ? MINUS + '&nbsp;' : '+&nbsp;'}</span>`;
    let html;
    if (it.t === 'grp') html = `${ld}<span class="gp6">(</span>${inner(it.terms)}<span class="gp6">)</span>`;
    else if (it.t === 'sq') html = `${ld}<span class="gp6">(</span>${inner(it.A)}<span class="gp6">)</span>${supHtml(2)}`;
    else html = `${ld}<span class="ga6">${isMonoP(it.A) ? mText(it.A[0], true, true) : `(${inner(it.A, 'ia6')})`}</span><span class="gb6">(${inner(it.B, 'ib6')})</span>`;
    return TOK(W(html), 'pg6', ref, 'pg6');
  }
  function renderPl(e) {
    const el = $('equation');
    if (!e.items.length) { el.appendChild(TOK('0', 'pt6', null, 'pt6')); return; }
    e.items.forEach((it, i) => el.appendChild(itemTok(it, i, i === 0)));
  }
  const plHtmlLine = e => (e.items.length ? e.items.map((it, i) => (it.t === 'term' ? mText(it.m, i === 0, true) : itemText(it, i === 0))).join(' ') : '0');

  // Polynomial division: the fraction, the split pieces, the long division layout or the synthetic table,
  // all inside one token (data-ref F) so every division card has one place to go.
  const cellT = (m, first) => (m ? mText(m, first, true) : '');
  function longHtml(e) {
    const n = deg(e.N), cols = n + 1, dd = deg(e.D);
    const cell = (h, cls = '', st = '') => `<span class="c6 ${cls}"${st ? ` data-st="${st}"` : ''}>${h}</span>`;
    const rowOf = (fn, cls, st) => { let out = ''; let first = true; for (let k = n; k >= 0; k--) { const m = fn(k); out += cell(m ? cellT(m, first) : '', cls, st); if (m) first = false; } return out; };
    const last = e.rows.length - 1;
    let h = `<div class="long6" style="grid-template-columns:auto repeat(${cols}, auto)">`;
    const qTop = e.Q.length ? deg(e.Q) : -1;
    h += cell('') ;
    { let first = true; for (let k = n; k >= 0; k--) { const has = k <= qTop && e.Q[k] && !fz(e.Q[k]); const isNew = e.rows.length && k === e.rows[last].lo; h += cell(has ? cellT(M(e.Q[k], k), first) : '', 'q6', has && isNew ? 'q' : ''); if (has) first = false; } }
    h += cell(`${dText(e.D, true)}&thinsp;)`, 'dv6');
    h += rowOf(k => M(e.N[k] || F(0), k), 'nd6');
    e.rows.forEach((r, j) => {
      const top = r.lo + dd, st = j === last ? 'p' : '';
      h += cell(MINUS, 'mn6', st);
      h += rowOf(k => (k <= top && k >= r.lo ? M(fNeg(r.prod[k] || F(0)), k) : null), 'pr6', st);
      const lo = j === last && e.done ? 0 : Math.max(0, r.lo - 1), hi = top - 1;
      const allZero = (() => { for (let k = hi; k >= lo; k--) if (!fz(r.rem[k] || F(0))) return false; return true; })();
      h += cell('', '', j === last ? 'r' : '');
      h += rowOf(k => (k <= hi && k >= lo ? (allZero ? (k === lo ? M(F(0), 0) : null) : M(r.rem[k] || F(0), k)) : null), 'rm6', j === last ? 'r' : '');
    });
    return h + '</div>';
  }
  function synSums(e) { const cs = toTerms(e.N, true).map(t => t.c), out = []; cs.forEach((a, j) => out.push(j ? fAdd(a, fMul(e.c, out[j - 1])) : a)); return { cs, out }; }
  function synHtml(e) {
    const { cs, out } = synSums(e), n = cs.length;
    const cell = (h, cls = '', col = -1) => `<span class="c6 ${cls}"${col >= 0 ? ` data-col="${col}"` : ''}>${h}</span>`;
    let h = `<div class="syn6" style="grid-template-columns:auto repeat(${n}, auto)">`;
    h += cell(fracText(e.c), 'sc6') + cs.map(c => cell(fracText(c), 'sn6')).join('');
    h += cell('') + cs.map((c, j) => cell(j ? fracText(fMul(e.c, out[j - 1])) : '', 'sp6', j)).join('');
    h += cell('') + out.map((c, j) => cell(fracText(c), 'ss6' + (j === n - 1 ? ' rem6' : ''), j)).join('');
    return h + '</div>';
  }
  function renderPd(e) {
    const el = $('equation');
    const top = e.filled ? toTerms(e.N, true).map((m, j) => `<span class="${fz(m.c) ? 'ph6' : 'it6'}">${mText(m, j === 0, true)}</span>`).join(' ') : inner(toTerms(e.N));
    let html;
    if (e.mode === 'long') html = longHtml(e);
    else if (e.mode === 'syn') html = synHtml(e);
    else if (e.mode === 'split' && !e.done) html = toTerms(e.N).map((m, j) => `<span class="pc6">${j ? (m.c.n < 0 ? MINUS : '+') + ' ' : m.c.n < 0 ? MINUS : ''}<span class="frac f6"><span>${mBody(m, true)}</span><span>${dText(e.D, true)}</span></span></span>`).join(' ');
    else if (e.mode === 'split') html = `<span class="pc6">${dText(e.Q, true)}</span>`;
    else html = `<span class="frac f6 big6"><span>${top}</span><span>${dText(e.D, true)}</span></span>`;
    if (e.done && e.mode !== 'split') html += `<div class="res6" data-st="a">= ${pdAnswer(e, true)}</div>`;
    const t = TOK(html, 'pd6', 'F', 'pd6' + (e.mode === 'long' || e.mode === 'syn' ? ' lay6' : ''));
    el.appendChild(t);
  }
  // Shrinks the expression to fit the arena: the width, and for the division layouts the height too.
  function fit6() {
    const el = $('equation'); if (!el.classList.contains('ex6')) return;
    el.style.removeProperty('--eqSize');
    const base = parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--eqSize')) || 56;
    const lay = !!el.querySelector('.lay6');
    let size = Math.round(base * (lay ? 0.62 : 0.9));
    el.style.setProperty('--eqSize', size + 'px');
    const maxH = Math.max(90, ($('arena').clientHeight || 400) * (innerWidth <= 640 ? 0.4 : 0.5));
    el.classList.add('fitting');
    for (let i = 0; i < 12; i++) {
      const availW = ($('arena').clientWidth || innerWidth) * 0.92, needW = Math.max(el.scrollWidth, el.getBoundingClientRect().width), needH = Math.max(0, ...[...el.children].map(k => k.offsetHeight || 0));
      const f = Math.min(availW && needW > availW ? availW / needW : 1, needH > maxH ? maxH / needH : 1);
      if (f >= 0.99) break;
      size = Math.max(12, Math.floor(size * Math.min(0.97, f)));
      el.style.setProperty('--eqSize', size + 'px');
      if (size <= 12) break;
    }
    el.classList.remove('fitting');
  }
  function render(e) {
    const el = $('equation'); if (typeof clearNotes === 'function') clearNotes();
    el.innerHTML = ''; el.classList.add('a4', 'ex6');
    if (e.k6 === 'ex') renderEx(e); else if (e.k6 === 'pl') renderPl(e); else renderPd(e);
    fit6();
  }
  function clear() {
    const el = $('equation'); if (el) el.classList.remove('ex6');
    document.querySelectorAll('.fly6').forEach(n => n.remove());
  }
  const fontPx = () => parseFloat(getComputedStyle($('equation')).fontSize);
  function prefit(s, ns) {
    render(ns); const after = fontPx(); render(s); const before = fontPx();
    if (before > after + 0.5) {
      const el = $('equation'), c = parseFloat(el.style.getPropertyValue('--eqSize')) || 56;
      el.style.setProperty('--eqSize', Math.floor(c * after / before) + 'px');
    }
  }
  addEventListener('resize', () => { if (!cur || !cur.act6 || (typeof animating !== 'undefined' && animating)) return; fit6(); });

  // ================================================================ prompts
  const PR = {
    simp: ['Simplify.', 'Simplify the expression.', 'Simplify. Write your answer using only positive exponents.'],
    neg: ['Simplify. Write your answer using only positive exponents.', 'Rewrite with positive exponents.', 'Simplify. Use positive exponents only.'],
    scimul: ['Multiply. Write your answer in scientific notation.', 'Simplify. Write the answer in scientific notation.', 'Find the product in scientific notation.'],
    scidiv: ['Divide. Write your answer in scientific notation.', 'Simplify. Write the answer in scientific notation.', 'Find the quotient in scientific notation.'],
    tosci: ['Write the number in scientific notation.', 'Write in scientific notation.', 'Express in scientific notation.'],
    tostd: ['Write the number in standard form.', 'Write in standard form.', 'Write the number without exponents.'],
    add: ['Add.', 'Add the polynomials.', 'Simplify. Write the answer in standard form.'],
    sub: ['Subtract.', 'Subtract the polynomials.', 'Simplify. Write the answer in standard form.'],
    mix: ['Simplify.', 'Simplify. Write the answer in standard form.', 'Simplify the expression.'],
    mul: ['Multiply.', 'Find the product.', 'Multiply and simplify.', 'Expand and simplify.'],
    div: ['Divide.', 'Find the quotient.', 'Divide the polynomials.'],
    syn: ['Use synthetic division to divide.', 'Divide using synthetic division.'],
    long: ['Use long division to divide.', 'Divide using long division.'],
  };
  const lastPr = {};
  function promptKey(s) {
    if (s.k6 === 'ex') {
      if (s.sci) return s.ask === 'tosci' ? 'tosci' : s.ask === 'tostd' ? 'tostd' : s.den.length ? 'scidiv' : 'scimul';
      return [...s.num, ...s.den].some(f => (f.t === 'p' && f.e < 0) || (f.t === 'g' && f.items.some(i => i.t === 'p' && i.e < 0))) ? 'neg' : 'simp';
    }
    if (s.k6 === 'pl') {
      if (s.skill === 'polymul' && s.items.every(it => it.t !== 'grp')) return 'mul';
      if (s.items.some(it => it.t === 'prod' || it.t === 'sq')) return 'mix';
      return s.items.some(it => it.t === 'grp' && it.s < 0) ? 'sub' : 'add';
    }
    return s.method === 'syn' ? 'syn' : s.method === 'long' ? 'long' : 'div';
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
  const popRefs = refs => refs.forEach(r => kickClass(tk(r), 'pop'));
  const ORD = n => (n === 2 ? 'square' : n === 3 ? 'cube' : n + 'th power');
  const moveAt = (s, c, ref) => movesOf(s).find(o => matchCard(o, c) && (o.refs.includes(ref) || o.refs.length === 1));
  async function result(ns, refs, cap) { render(ns); popRefs(refs); if (cap) caption(cap); await quick(300); await hold(); }
  async function written(html, anchors, cap, cls = 'lift4') {
    if (cap) caption(cap);
    const n = note(html, anchors); n.classList.add(cls);
    await quick(150); await hold();
    return n;
  }
  function flyRect(html, from, toEl, ms = 480) {
    if (!from || !toEl) return quick(1);
    const dest = toEl.getBoundingClientRect();
    const chip = document.createElement('div'); chip.className = 'fly4 fly6'; chip.innerHTML = html;
    chip.style.left = (from.left + from.width / 2) + 'px'; chip.style.top = (from.top + from.height / 2) + 'px';
    document.body.appendChild(chip); void chip.offsetWidth;
    chip.style.transform = `translate(${dest.left + dest.width / 2 - from.left - from.width / 2}px, ${dest.top + dest.height / 2 - from.top - from.height / 2}px)`;
    return quick(ms).then(() => chip.remove());
  }
  // ---------------------------------------------------------------- stage 22 and 23
  async function animPow(c, s, ns, ref) {
    const mv = moveAt(s, c, ref), r0 = mv.refs[0], g = at(s, r0), t = tk(r0);
    const parts = g.items.map(it => (it.t === 'n' ? `(${facText(it, s.sci)})${supText(g.e)} = ${s.sci ? decText(fPow(it.v, g.e)) : fracText(fPow(it.v, g.e))}` : `(${facText(it)})${supText(g.e)} = ${it.b}${supText(it.e * g.e)}`));
    mark([t], 'hot6');
    const sup = t.querySelector('sup.e6:last-child'); if (sup) sup.classList.add('lift6');
    const n = await written(g.items.map(it => (it.t === 'n' ? `${facHtml(it, s.sci)}${supHtml(g.e)}` : `${XV(it.b)}<sup class="e6">${it.e}·${g.e}</sup>`)).join(s.sci ? ` ${TIMES} ` : ' · '), [t],
      `Power rule: the ${ORD(g.e)} goes to every factor inside the bracket, and a power of a power multiplies the exponents`);
    dropNote(n);
    const L = r0[0], i0 = +r0.slice(1);
    await result(ns, g.items.map((_, j) => L + (i0 + j)), parts.join(', '));
  }
  async function animProd(c, s, ns, ref) {
    const mv = moveAt(s, c, ref), fs = mv.refs.map(r => at(s, r)), toks = mv.refs.map(tk), b = fs[0].b, sum = fs.reduce((a, f) => a + f.e, 0);
    mark(toks, 'hot6');
    const n = await written(`${XV(b)}<sup class="e6">${fs.map(f => f.e).join(' + ')}</sup>`, toks, `Product rule: ${fs.map(f => facText(f)).join(' · ')} has the same base ${b}, so add the exponents`);
    toks.slice(1).forEach(x => x.classList.add('slide6'));
    await removeTok(toks.slice(1)); dropNote(n);
    toks[0].innerHTML = W(facHtml(Pw(b, sum))); kickClass(toks[0], 'pop');
    await quick(250);
    await result(ns, [mv.refs[0]], `${fs.map(f => facText(f)).join(' · ')} = ${b}${supText(sum)}`);
  }
  async function animMuln(c, s, ns, ref) {
    const mv = moveAt(s, c, ref), fs = mv.refs.map(r => at(s, r)), toks = mv.refs.map(tk);
    const prod = fs.reduce((a, f) => fMul(a, f.v), F(1)), nt = v => (s.sci ? decText(v) : fracText(v));
    mark(toks, 'hot6');
    const n = await written(`${fs.map(f => nt(f.v)).join(' · ')} = ${nt(prod)}`, toks, 'Multiply the numbers: multiplication can go in any order, so the numbers can be multiplied first');
    await removeTok(toks.slice(1)); dropNote(n);
    toks[0].innerHTML = groupDigits(nt(prod)); kickClass(toks[0], 'pop');
    await quick(250);
    await result(ns, [mv.refs[0]], `${fs.map(f => nt(f.v)).join(' × ')} = ${nt(prod)}`);
  }
  async function animQuot(c, s, ns, ref) {
    const mv = moveAt(s, c, ref), a = at(s, mv.refs[0]), b = at(s, mv.refs[1]), ta = tk(mv.refs[0]), tb = tk(mv.refs[1]);
    mark([ta, tb], 'hot6');
    const n = await written(`${XV(a.b)}<sup class="e6">${a.e} ${MINUS} ${b.e < 0 ? '(' + numText(b.e) + ')' : b.e}</sup>`, [tb],
      `Quotient rule: ${facText(a)} over ${facText(b)}, same base, so subtract the exponents (top minus bottom)`);
    dropNote(n);
    tb.classList.add('sink6'); await removeTok([tb]);
    ta.innerHTML = W(facHtml(Pw(a.b, a.e - b.e))); kickClass(ta, 'pop');
    await quick(250);
    const e2 = a.e - b.e;
    await result(ns, [mv.refs[0]], `${facText(a)}/${facText(b)} = ${a.b}${supText(e2)}${e2 === 0 ? ' (and that is 1)' : e2 < 0 ? ' (a negative power: move it under the bar)' : ''}`);
  }
  async function animDivn(c, s, ns, ref) {
    const mv = moveAt(s, c, ref), a = at(s, mv.refs[0]).v, b = at(s, mv.refs[1]).v, ta = tk(mv.refs[0]), tb = tk(mv.refs[1]), q = fDiv(a, b);
    const nt = v => (s.sci ? decText(v) : fracText(v));
    mark([ta, tb], 'hot6');
    const g = gcd(a.n, b.n);
    const n = await written(s.sci || q.d === 1 ? `${nt(a)} ${DIV} ${nt(b)} = ${nt(q)}` : `${DIV} ${g} top and bottom`, [tb],
      s.sci || q.d === 1 ? `Divide the numbers: ${nt(a)} ${DIV} ${nt(b)} = ${nt(q)}` : `Reduce the numbers: ${fracText(a)} and ${fracText(b)} share a factor of ${g}`);
    dropNote(n);
    await result(ns, [mv.refs[0], mv.refs[1]], s.sci || q.d === 1 ? `${nt(a)}/${nt(b)} = ${nt(q)}` : `${fracText(a)}/${fracText(b)} = ${q.n}/${q.d}`);
  }
  async function animZero(c, s, ns, ref) {
    const mv = moveAt(s, c, ref), f = at(s, mv.refs[0]), t = tk(mv.refs[0]);
    mark([t], 'hot6'); t.classList.add('spin');
    const n = await written('= 1', [t], `Zero power: ${facText(f, s.sci)} = 1 (anything except 0 to the power 0 is 1)`, 'stamp4');
    dropNote(n);
    t.classList.remove('spin'); t.innerHTML = '1'; kickClass(t, 'pop'); await quick(300);
    const coef = s.num.find(o => o.t === 'n' && !fIs(o.v, 1));
    await result(ns, [], coef && mv.refs[0][0] === 'n' && f.t === 'p' ? `${facText(f)} = 1, but the ${fracText(coef.v)} in front stays: ${fracText(coef.v)} ${TIMES} 1 = ${fracText(coef.v)}` : `${facText(f, s.sci)} = 1`);
  }
  async function animNeg(c, s, ns, ref) {
    const mv = moveAt(s, c, ref), r0 = mv.refs[0], f = at(s, r0), t = tk(r0), from = t.getBoundingClientRect();
    mark([t], 'hot6');
    const down = r0[0] === 'n';
    const n = await written(down ? `1 / ${XV(f.b)}${supHtml(-f.e)}` : `${XV(f.b)}${supHtml(-f.e)} on top`, [t],
      `Negative power: ${facText(f)} = ${down ? '1/' + f.b + supText(-f.e) : 'moves to the top as ' + f.b + supText(-f.e)}. It crosses the fraction bar and the exponent turns positive`);
    dropNote(n);
    render(ns);
    const O = down ? 'd' : 'n', list = down ? ns.den : ns.num, j = list.length - 1, dest = tk(O + j);
    if (dest) dest.style.opacity = '0';
    await flyRect(`${XV(f.b)}${supHtml(-f.e)}`, from, dest);
    if (dest) { dest.style.opacity = ''; kickClass(dest, 'pop'); }
    caption(`${facText(f)} ${down ? 'went under the bar' : 'came up to the top'} as ${f.b}${supText(-f.e)}: no negative exponents left there`);
    await quick(250); await hold();
  }
  async function animGrp(c, s, ns) {
    const toks = [...$('equation').querySelectorAll('.tok[data-ref]')];
    mark(toks.filter(x => x.dataset.kind === 'n'), 'hot6');
    caption('Multiplying can be done in any order: put the numbers together and the powers of 10 together');
    await quick(150); await hold();
    mark(toks, 'melt4'); await quick(320);
    render(ns); [...$('equation').querySelectorAll('.tok[data-ref]')].forEach(x => kickClass(x, 'drop4'));
    caption(ns.den.length ? 'Numbers over numbers, and tens over tens' : 'Numbers in one group, powers of 10 in the other');
    await quick(350); await hold();
  }
  // The decimal point hops one place at a time, and the power of 10 ticks to make up for each hop.
  async function hops(s, numRef, tenRef, v0, p0, k, cap) {
    const nt = tk(numRef); let tt = tenRef ? tk(tenRef) : null;
    caption(cap);
    const n = note(k > 0 ? `point ${Math.abs(k)} ${Math.abs(k) === 1 ? 'place' : 'places'} ←` : `point ${Math.abs(k)} ${Math.abs(k) === 1 ? 'place' : 'places'} →`, [nt]); n.classList.add('lift4');
    await quick(150); await hold(); dropNote(n);
    const step = k > 0 ? 1 : -1;
    for (let j = 1; j <= Math.abs(k); j++) {
      nt.innerHTML = groupDigits(decText(fMul(v0, pow10(-step * j)))); kickClass(nt, 'hop6');
      if (tt) { tt.innerHTML = W(`10${supHtml(p0 + step * j)}`); kickClass(tt, 'pop'); }
      await quick(Math.abs(k) > 5 ? 170 : 260);
    }
    return { nt, tt };
  }
  async function animNorm(c, s, ns) {
    const ni = s.num.findIndex(f => f.t === 'n'), pi = s.num.findIndex(f => f.t === 'p'), v = s.num[ni].v, p = pi >= 0 ? s.num[pi].e : 0;
    const k = ns.num.find(f => f.t === 'p').e - p;
    let tenRef = pi >= 0 ? 'n' + pi : null;
    if (pi < 0) { const tmp = clone(s); tmp.num.push(Pw('10', 0)); render(tmp); tenRef = 'n' + (tmp.num.length - 1); kickClass(tk(tenRef), 'drop4'); await quick(300); }
    mark([tk('n' + ni)], 'hot6');
    await hops(s, 'n' + ni, tenRef, v, p, k, `Normalize: the number has to be from 1 to 10. Move the decimal point ${Math.abs(k)} ${Math.abs(k) === 1 ? 'place' : 'places'} ${k > 0 ? 'left' : 'right'}; each place ${k > 0 ? 'adds 1 to' : 'takes 1 from'} the power of 10`);
    await result(ns, ns.num.map((_, i) => 'n' + i), `${decText(v)}${pi >= 0 ? ' × 10' + supText(p) : ''} = ${exText(ns)}`);
  }
  async function animStd(c, s, ns) {
    const ni = s.num.findIndex(f => f.t === 'n'), pi = s.num.findIndex(f => f.t === 'p'), v = s.num[ni].v, p = s.num[pi].e;
    mark([tk('n' + pi)], 'hot6');
    const { tt } = await hops(s, 'n' + ni, 'n' + pi, v, p, -p, `Standard form: 10${supText(p)} moves the point ${Math.abs(p)} ${Math.abs(p) === 1 ? 'place' : 'places'} ${p > 0 ? 'right (a bigger number)' : 'left (a smaller number)'}${p > 0 ? '' : ', with zeros filling in'}`);
    if (tt) await removeTok([tt]);
    await result(ns, ['n0'], `${exText(s)} = ${exText(ns)}`);
  }
  // ---------------------------------------------------------------- stages 24 and 25
  async function animDneg(c, s, ns, ref) {
    ref = moveAt(s, c, ref).refs[0];
    const i = +ref.slice(1), it = s.items[i], t = tk(ref);
    mark([t], 'hot6');
    const n = await written(`${TIMES} (${MINUS}1) each`, [t], `Distribute the minus: it means ${MINUS}1 times every term in the bracket, so every sign flips`);
    dropNote(n);
    const spans = [...t.querySelectorAll('.it6')];
    for (let j = 0; j < spans.length; j++) { spans[j].innerHTML = mText(mNeg(it.terms[j]), false, true); kickClass(spans[j], 'flip6'); await quick(170); }
    t.querySelectorAll('.gs6, .gp6').forEach(x => x.classList.add('gone6'));
    await quick(350);
    await result(ns, it.terms.map((_, j) => 'i' + (i + j)), `${MINUS}(${polyText(it.terms)}) = ${polyText(it.terms.map(mNeg))}`);
  }
  async function animDrop(c, s, ns, ref) {
    ref = moveAt(s, c, ref).refs[0];
    const i = +ref.slice(1), it = s.items[i], t = tk(ref);
    caption('A + in front of a bracket changes nothing: the brackets just go away');
    mark([t], 'hot6'); await quick(150); await hold();
    t.querySelectorAll('.gs6, .gp6').forEach(x => x.classList.add('gone6'));
    await quick(350);
    await result(ns, it.terms.map((_, j) => 'i' + (i + j)), `${i ? '+' : ''}(${polyText(it.terms)}) = ${i ? '+ ' : ''}${polyText(it.terms)}`);
  }
  async function animComb(c, s, ns, ref) {
    const mv = moveAt(s, c, ref), ms = mv.refs.map(r => s.items[+r.slice(1)].m), toks = mv.refs.map(tk);
    const sum = ms.reduce((a, m) => fAdd(a, m.c), F(0)), res = { ...ms[0], c: sum };
    mark(toks, 'hot6');
    const lhs = ms.map((m, j) => mText(m, j === 0, true)).join(' ');
    const n = await written(`${lhs} = ${fz(sum) ? '0' : mText(res, true, true)}`, toks, `Combine like terms: they have the same power, so add the numbers in front (${ms.map(m => fracText(m.c)).join(' + ').replace(/\+ −/g, MINUS + ' ')} = ${fracText(sum)})`);
    await removeTok(toks.slice(1)); dropNote(n);
    if (fz(sum)) await removeTok([toks[0]]); else { toks[0].innerHTML = W(mText(res, mv.refs[0] === 'i0', true)); kickClass(toks[0], 'pop'); }
    await quick(250);
    await result(ns, fz(sum) ? [] : [mv.refs[0]], fz(sum) ? `${lhs.replace(/<[^>]+>/g, '')} = 0: they cancel` : `${polyText(ms)} = ${mText(res, true)}`);
  }
  async function animSort(c, s, ns) {
    const old = {};
    [...$('equation').querySelectorAll('.tok[data-ref]')].forEach(x => { const m = s.items[+x.dataset.ref.slice(1)]; if (m && m.t === 'term') old[mkey(m.m)] = x.getBoundingClientRect(); });
    caption('Standard form: write the terms from the highest power down');
    await quick(150); await hold();
    render(ns);
    const moved = [];
    [...$('equation').querySelectorAll('.tok[data-ref]')].forEach(x => {
      const m = ns.items[+x.dataset.ref.slice(1)], o = m && old[mkey(m.m)];
      if (!o) return;
      const nr = x.getBoundingClientRect();
      x.style.transition = 'none'; x.style.transform = `translate(${o.left - nr.left}px, ${o.top - nr.top}px)`; moved.push(x);
    });
    void $('equation').offsetWidth;
    moved.forEach(x => { x.style.transition = `transform calc(.55s * var(--k)) ease-in-out`; x.style.transform = ''; });
    await quick(650);
    moved.forEach(x => { x.style.transition = ''; });
    caption(`In order: ${plText(ns)}`);
    await hold();
  }
  async function animBox(c, s, ns, ref) {
    ref = moveAt(s, c, ref).refs[0];
    const i = +ref.slice(1), it = s.items[i], t = tk(ref), A = it.A, B = it.t === 'sq' ? it.A : it.B;
    mark([t], 'hot6');
    const th = m => `<th>${mText(m, true, true)}</th>`;
    let html = `<table class="box6t"><tr><th class="corner6">${TIMES}</th>${B.map(th).join('')}</tr>`;
    A.forEach((a, r) => { html += `<tr>${th(a)}${B.map((b, q) => `<td data-k="${r * B.length + q}">${mText(mMul(a, b), true, true)}</td>`).join('')}</tr>`; });
    html += '</table>';
    const n = note(html, [t]); n.classList.add('box6n');
    caption(`Box method: ${A.length === 1 ? 'the term outside' : 'each term of the first bracket'} times each term of the ${A.length === 1 ? 'bracket' : 'second'}, one box at a time`);
    await quick(200); await hold();
    const cells = [...n.querySelectorAll('td')];
    for (const cell of cells) { cell.classList.add('in'); await quick(cells.length > 4 ? 220 : 320); }
    await hold();
    dropNote(n);
    const k = A.length * B.length;
    await result(ns, Array.from({ length: k }, (_, j) => 'i' + (i + j)), `${itemText(it, true)} = ${polyText(boxTerms(A, B))}${k > 1 ? ': now combine like terms' : ''}`);
  }
  async function animSqb(c, s, ns, ref) {
    ref = moveAt(s, c, ref).refs[0];
    const i = +ref.slice(1), [a, b] = s.items[i].A, t = tk(ref), w = m => `(${mText(m, true, true)})`;
    mark([t], 'hot6');
    const n = await written(`${w(a)}² + 2${w(a)}${w(b)} + ${w(b)}²`, [t], 'Square a binomial: (a + b)² = a² + 2ab + b², the first squared, twice the product, the last squared');
    dropNote(n);
    const mid = M(fMul(F(2), fMul(a.c, b.c)), a.x + b.x, a.y + b.y);
    await result(ns, [0, 1, 2].map(j => 'i' + (i + j)), `(${polyText([a, b])})² = ${polyText([mMul(a, a), mid, mMul(b, b)])}: don't forget the middle term ${mText(mid, true)}`);
  }
  async function animDos(c, s, ns, ref) {
    ref = moveAt(s, c, ref).refs[0];
    const i = +ref.slice(1), it = s.items[i], [a, b] = it.A, t = tk(ref), w = m => `(${mText(m, true, true)})`;
    mark([t], 'hot6');
    const n = await written(`${w(a)}² ${MINUS} ${w(fAbs(b.c) && b.c.n < 0 ? mNeg(b) : b)}²`, [t],
      `Difference of squares: (a + b)(a ${MINUS} b) = a² ${MINUS} b². The middle terms ${mText(mMul(a, it.B[1]), true)} and ${mText(mMul(it.A[1], it.B[0]), false)} cancel`);
    dropNote(n);
    await result(ns, [0, 1].map(j => 'i' + (i + j)), `${itemText(it, true)} = ${polyText([mMul(a, a), mNeg(mMul(b, b))])}`);
  }
  // ---------------------------------------------------------------- stage 26
  const ldText = a => mText(M(a[deg(a)], deg(a)), true);
  async function reveal(sel, cls = 'pop') { const els = [...$('equation').querySelectorAll(sel)]; els.forEach(x => { x.style.visibility = ''; kickClass(x, cls); }); return els; }
  const hideAll = sel => $('equation').querySelectorAll(sel).forEach(x => { x.style.visibility = 'hidden'; });
  async function animFill(c, s, ns) {
    render(ns);
    $('equation').querySelectorAll('.ph6').forEach(x => kickClass(x, 'drop4'));
    caption(`${dText(s.N)} is missing ${holes(s.N).map(k => (k === 0 ? 'a constant' : k === 1 ? 'an x term' : 'an x' + supText(k) + ' term')).join(' and ')}: write 0 in its place so every power has a column`);
    await quick(400); await hold();
  }
  async function animLong(c, s, ns) {
    const t = tk('F'); mark([t], 'hot6');
    caption('Long division: the divisor goes outside the bracket, the polynomial inside, highest power first');
    await quick(150); await hold();
    render(ns); kickClass(tk('F'), 'drop4');
    caption(`Now divide ${ldText(ns.R)} by ${ldText(ns.D)} to get the first term on top`);
    await quick(350); await hold();
  }
  async function animQt(c, s, ns) {
    const t = moveAt(s, c, 'F').t, r = ns.rows[ns.rows.length - 1];
    render(ns); hideAll('[data-st]');
    caption(`Divide the leading terms: ${ldText(s.R)} ${DIV} ${ldText(s.D)} = ${tHtml(t)}. Write it on top`);
    await reveal('[data-st="q"]', 'drop4'); await quick(300); await hold();
    const prodTerms = toTerms(r.prod);
    caption(`Multiply back: ${tHtml(t)} ${TIMES} (${dText(s.D)}) = ${polyText(prodTerms)}. Write it underneath`);
    await reveal('[data-st="p"]'); await quick(300); await hold();
    const remShown = toTerms(r.rem.map((x, k) => (k >= Math.max(0, r.lo - 1) || ns.done ? x : F(0))));
    caption(`Subtract: change the signs and add${ns.done ? '' : ', then bring down the next term'}. ${polyText(remShown) === '0' ? 'Nothing is left' : 'That leaves ' + polyText(remShown)}`);
    await reveal('[data-st="r"]'); await quick(300); await hold();
    if (ns.done) {
      await reveal('[data-st="a"]');
      caption(deg(ns.R) < 0 ? `Remainder 0: ${dText(ns.D)} goes in exactly ${dText(ns.Q)} times` : `The degree of what's left is less than the divisor's: the remainder is ${dText(ns.R)}, written over the divisor`);
      await quick(300); await hold();
    }
  }
  async function animSyn(c, s, ns) {
    const { cs, out } = synSums(ns);
    caption(`Synthetic division: c = ${fracText(ns.c)} (from x ${MINUS} c), then the coefficients of ${dText(s.N)} in a row`);
    render(ns); hideAll('[data-col], [data-st]');
    await quick(200); await hold();
    for (let j = 0; j < cs.length; j++) {
      if (j) {
        caption(`Multiply: ${fracText(ns.c)} ${TIMES} ${paren(out[j - 1])} = ${fracText(fMul(ns.c, out[j - 1]))}, written under the next coefficient`);
        await reveal(`.sp6[data-col="${j}"]`); await quick(cs.length > 4 ? 380 : 520);
        caption(`Add: ${fracText(cs[j])} + ${paren(fMul(ns.c, out[j - 1]))} = ${fracText(out[j])}`);
      } else caption(`Bring down the first coefficient: ${fracText(cs[0])}`);
      await reveal(`.ss6[data-col="${j}"]`); await quick(cs.length > 4 ? 380 : 520);
    }
    await reveal('[data-st="a"]');
    caption(`The bottom row is the answer: ${dText(ns.Q)}${deg(ns.R) < 0 ? ', remainder 0' : `, remainder ${dText(ns.R)}`}. The quotient is one power lower than ${dText(s.N)}`);
    await quick(300); await hold();
  }
  async function animSplit(c, s, ns) {
    const t = tk('F'); mark([t], 'hot6');
    caption(`The bottom is one term, so split the fraction: each term on top gets its own ${dText(s.D)} underneath`);
    await quick(150); await hold();
    render(ns); $('equation').querySelectorAll('.pc6').forEach((x, j) => { x.style.animationDelay = (j * 0.12) + 's'; kickClass(x, 'drop4'); });
    await quick(500); await hold();
  }
  async function animDivt(c, s, ns) {
    const pcs = [...$('equation').querySelectorAll('.pc6')], ts = toTerms(s.N), d = toTerms(s.D)[0];
    for (let j = 0; j < pcs.length; j++) {
      const m = ts[j], q = M(fDiv(m.c, d.c), m.x - d.x);
      pcs.forEach(x => x.classList.remove('hot6')); pcs[j].classList.add('hot6');
      caption(`${mBody(m)} ${DIV} ${mBody(d)}: ${fracText(fAbs(m.c))} ${DIV} ${fracText(d.c)} = ${fracText(fAbs(q.c))}, and x${supText(m.x)} ${DIV} x${supText(d.x)} = x${supText(m.x - d.x)} (subtract the exponents)`.replace(/x¹(?![\d⁰¹²³⁴⁵⁶⁷⁸⁹])/g, 'x').replace(/x⁰/g, '1'));
      await quick(200); await hold(); 
      pcs[j].innerHTML = mText(q, j === 0, true); kickClass(pcs[j], 'pop');
      await quick(250);
    }
    await result(ns, ['F'], `= ${dText(ns.Q)}`);
  }
  function animFor(card) {
    return async (c, s, ns, ref) => {
      switch (c.op) {
        case 'pow6': return animPow(c, s, ns, ref);
        case 'prod6': return animProd(c, s, ns, ref);
        case 'muln6': return animMuln(c, s, ns, ref);
        case 'quot6': return animQuot(c, s, ns, ref);
        case 'divn6': return animDivn(c, s, ns, ref);
        case 'zero6': return animZero(c, s, ns, ref);
        case 'negx6': return animNeg(c, s, ns, ref);
        case 'grp6': return animGrp(c, s, ns, ref);
        case 'norm6': return animNorm(c, s, ns, ref);
        case 'std6': return animStd(c, s, ns, ref);
        case 'dneg6': return animDneg(c, s, ns, ref);
        case 'drop6': return animDrop(c, s, ns, ref);
        case 'comb6': return animComb(c, s, ns, ref);
        case 'sort6': return animSort(c, s, ns, ref);
        case 'box6': return animBox(c, s, ns, ref);
        case 'sqb6': return animSqb(c, s, ns, ref);
        case 'dos6': return animDos(c, s, ns, ref);
        case 'fill6': return animFill(c, s, ns, ref);
        case 'long6': return animLong(c, s, ns, ref);
        case 'qt6': return animQt(c, s, ns, ref);
        case 'syn6': return animSyn(c, s, ns, ref);
        case 'split6': return animSplit(c, s, ns, ref);
        case 'divt6': return animDivt(c, s, ns, ref);
      }
    };
  }

  // ================================================================ generators
  // Every case comes up at every level; the level changes how hard it is to do: bigger numbers, negative
  // numbers, a second letter, extra factors and steps.
  const COEFP = [0.35, 0.6, 0.8, 0.9], NEGC = [0.1, 0.3, 0.4, 0.5], YP = [0.15, 0.35, 0.6, 0.7], EMAX = [5, 6, 8, 9];
  const okEx = (e, L) => {
    if (isSolved6(e)) return false;
    const { end, path } = pathOf6(e, e.skill);
    if (path.length > [5, 6, 8, 9][L] + 1) return false;
    return [...end.num, ...end.den].every(f => (f.t === 'n' ? Math.abs(f.v.n) <= 2000 && f.v.d <= 2000 : f.t === 'p' ? Math.abs(f.e) <= 40 : false));
  };
  function coefOr(L, tut, max = [6, 9, 12, 12]) {
    if (tut || !chance(COEFP[L])) return null;
    let k = rand(2, max[L]);
    if (chance(NEGC[L])) k = -k;
    return k;
  }
  function mono6(L, tut, grp, o = {}) {      // [k?] x^a [y^b]
    const out = [];
    const k = o.k !== undefined ? o.k : coefOr(L, tut, o.max);
    if (k !== null && k !== undefined) out.push(N(k, grp));
    out.push(Pw('x', o.a !== undefined ? o.a : rand(1, o.emax || EMAX[L]), grp));
    if (o.y || (o.y === undefined && !tut && chance(YP[L]))) out.push(Pw('y', o.b !== undefined ? o.b : rand(1, o.emax || EMAX[L]), grp));
    return out;
  }
  const EXP_CASES = ['prod', 'pow', 'quot', 'zero', 'neg', 'mixed'];
  function genExp(cs, tut = isTutorial()) {
    const L = lvl(tut);
    cs = cs || pick(EXP_CASES);
    for (let n = 0; n < 400; n++) {
      let num = [], den = [];
      if (cs === 'prod') {
        const parts = !tut && L >= 2 && chance(0.4) ? 3 : 2;
        const y = !tut && chance(YP[L]);
        for (let g = 0; g < parts; g++) num.push(...mono6(L, tut, g, { y: y && (g < 2 || chance(0.5)) }));
      } else if (cs === 'pow') {
        const e = rand(2, tut ? 3 : L >= 2 ? 4 : 3);
        const items = mono6(L, tut, 0, { max: [3, 3, 4, 5], emax: e > 3 ? 3 : 4 });
        num.push(G(items, e, 0));
        if (!tut && L >= 2 && chance(0.45)) num.push(...mono6(L, tut, 1, { k: null, y: items.some(i => i.b === 'y') && chance(0.5) }));
      } else if (cs === 'quot') {
        const y = !tut && chance(YP[L]);
        const a = rand(2, EMAX[L] + 2), c = !tut && L >= 1 && chance(0.3) ? rand(a + 1, a + 4) : rand(1, a - 1);
        let kn = null, kd = null;
        if (!tut && chance(COEFP[L])) {
          if (chance(0.6)) { kd = rand(2, [4, 6, 8, 9][L]); kn = kd * rand(1, [3, 4, 5, 6][L]); }
          else { const g2 = rand(2, 4), bb = rand(2, 5); let aa = rand(1, 7); while (gcd(aa, bb) !== 1) aa++; kn = g2 * aa; kd = g2 * bb; }
          if (chance(NEGC[L])) kn = -kn;
          num.push(N(kn, 0));
        }
        num.push(Pw('x', a, 0));
        if (y) num.push(Pw('y', rand(1, EMAX[L]), 0));
        if (kd !== null) den.push(N(kd, 0));
        den.push(Pw('x', c, 0));
        if (y && chance(0.6)) den.push(Pw('y', rand(1, EMAX[L]), 0));
      } else if (cs === 'zero') {
        const form = tut ? pick(['bare', 'coef']) : pick(['coef', 'group', 'mixed', L >= 2 ? 'prod' : 'coef']);
        if (form === 'bare') num.push(Pw('x', 0));
        if (form === 'coef') num.push(N(rand(2, [9, 9, 12, 15][L]) * (chance(NEGC[L]) ? -1 : 1)), Pw('x', 0));
        if (form === 'group') num.push(G(mono6(L, tut, 0, { k: rand(2, 9), y: chance(0.6) }), 0, 0));
        if (form === 'mixed') num.push(...(chance(COEFP[L]) ? [N(rand(2, 9))] : []), Pw('x', rand(1, EMAX[L])), Pw('y', 0));
        if (form === 'prod') num.push(N(rand(2, 6), 0), Pw('x', 0, 0), N(rand(2, 6), 1), Pw('x', rand(2, 5), 1));
      } else if (cs === 'neg') {
        const form = tut ? 'coef' : pick(['coef', 'mixed', 'under', L >= 2 ? 'two' : 'coef', L >= 1 ? 'under' : 'mixed']);
        if (form === 'coef') num.push(...(chance(tut ? 0.5 : COEFP[L]) ? [N(rand(2, 9) * (chance(NEGC[L]) ? -1 : 1))] : []), Pw('x', -rand(1, EMAX[L])));
        if (form === 'mixed') num.push(Pw('x', -rand(1, EMAX[L])), Pw('y', rand(1, EMAX[L])));
        if (form === 'under') { num.push(chance(0.5) ? N(rand(2, 9)) : Pw('y', rand(1, 5))); den.push(Pw('x', -rand(1, EMAX[L]))); }
        if (form === 'two') num.push(...(chance(0.5) ? [N(rand(2, 9))] : []), Pw('x', -rand(1, 5)), Pw('y', -rand(1, 5)));
      } else {   // mixed: two rules or more
        const form = pick(tut ? ['powprod'] : ['powprod', 'powquot', 'prodneg', L >= 1 ? 'quotneg' : 'powprod', L >= 2 ? 'all' : 'prodneg']);
        if (form === 'powprod') { const e = rand(2, 3); num.push(G([Pw('x', rand(2, 4))], e, 0), Pw('x', rand(1, EMAX[L]), 1)); }
        if (form === 'powquot') { const e = rand(2, 3), k = rand(2, 3); num.push(G([N(k), Pw('x', rand(2, 4))], e, 0)); den.push(N(k ** e / pick([1, k]) | 0 || k), Pw('x', rand(2, 6))); }
        if (form === 'prodneg') num.push(Pw('x', rand(2, EMAX[L])), Pw('x', -rand(EMAX[L] + 1, EMAX[L] + 4), 1));
        if (form === 'quotneg') { num.push(Pw('x', -rand(1, 4))); den.push(Pw('x', rand(1, 5))); if (chance(0.5)) { num.unshift(N(rand(2, 9) * 2)); den.unshift(N(2)); } }
        if (form === 'all') { const e = 2; num.push(G([N(rand(2, 3)), Pw('x', rand(1, 3)), Pw('y', -rand(1, 2))], e, 0)); den.push(N(pick([2, 4, 6])), Pw('x', rand(1, 5)), Pw('y', rand(1, 3))); }
      }
      if (!num.length) continue;
      const e = exState(num, den, { skill: 'exprules' });
      if (!okEx(e, L)) continue;
      return { ex6: e, enemy: 'powerling' };
    }
    return { ex6: exState([Pw('x', 2, 0), Pw('x', 3, 1)], [], { skill: 'exprules' }), enemy: 'powerling' };
  }

  // Stage 23. Mantissas are whole numbers on Easy, then one and two decimals; every level gets negative
  // powers of 10 sometimes.
  const SCI_CASES = ['mul', 'mulnorm', 'div', 'divnorm', 'tosci', 'tostd'];
  const NEGP = [0.3, 0.4, 0.5, 0.5];
  function mant(L, tut) {
    const dp = tut || L === 0 ? 0 : L === 1 ? (chance(0.5) ? 1 : 0) : L === 2 ? pick([0, 1, 1, 2]) : pick([1, 1, 2, 2]);
    const m = rand(10 ** dp, 10 ** (dp + 1) - 1);
    if (dp && m % 10 === 0) return F(m / 10, 10 ** (dp - 1));
    return F(m, 10 ** dp);
  }
  const dps = f => { const t = decText(f), i = t.indexOf('.'); return i < 0 ? 0 : t.length - i - 1; };
  const expo = (L, tut, lo = 1, hi = 8) => { const k = rand(lo, hi); return !tut && chance(NEGP[L]) ? -k : k; };
  function genSci(cs, tut = isTutorial()) {
    const L = lvl(tut), sci = { sci: true, skill: 'scinot' };
    cs = cs || pick(SCI_CASES);
    for (let n = 0; n < 600; n++) {
      if (cs === 'mul' || cs === 'mulnorm') {
        const a = mant(L, tut), b = mant(L, tut), p = fMul(a, b), big = fv(p) >= 10;
        if (big !== (cs === 'mulnorm') || dps(p) > 3 || fIs(a, 1) || fIs(b, 1)) continue;
        const m1 = expo(L, tut, 1, 9), m2 = expo(L, tut, 1, 9), fin = m1 + m2 + (big ? 1 : 0);
        if (m1 + m2 === 0 || fin === 0 || Math.abs(fin) > 18) continue;
        const num = [N(a, 0), Pw('10', m1, 0), N(b, 1), Pw('10', m2, 1)];
        if (!tut && L >= 3 && chance(0.3)) { const c = mant(0, true); if (fv(fMul(p, c)) >= 100 || dps(fMul(p, c)) > 3) continue; num.push(N(c, 2), Pw('10', expo(L, tut, 1, 4), 2)); }
        return { ex6: exState(num, [], sci), enemy: 'tenfold' };
      }
      if (cs === 'div' || cs === 'divnorm') {
        let q, b;
        if (cs === 'div') { q = mant(L, tut); b = mant(L, tut); } else { q = pick([F(1, 2), F(1, 4), F(3, 4), F(1, 5), F(2, 5), F(3, 5), F(4, 5), F(1, 8), F(3, 8), F(5, 8)]); b = F(rand(2, 9)); if (L >= 2 && chance(0.4)) b = fMul(b, F(1, 2)); }
        const a = fMul(q, b);
        if (fv(a) < 1 || fv(a) >= 10 || dps(a) > 2 || dps(q) > 3 || fIs(b, 1) || fIs(q, 1)) continue;
        const m1 = expo(L, tut, 2, 9), m2 = expo(L, tut, 1, 8), fin = m1 - m2 - (cs === 'divnorm' ? 1 : 0);
        if (m1 === m2 || fin === 0 || Math.abs(fin) > 16) continue;
        return { ex6: exState([N(a, 0), Pw('10', m1, 0)], [N(b, 0), Pw('10', m2, 0)], sci), enemy: 'tenfold' };
      }
      if (cs === 'tosci') {
        const m = mant(Math.max(L, 1), false); let k = rand(2, [5, 6, 7, 8][L]);
        if (chance(tut ? 0.3 : NEGP[L] + 0.1)) k = -rand(2, [4, 5, 6, 7][L]);
        if (fIs(m, 1)) continue;
        return { ex6: exState([N(fMul(m, pow10(k)))], [], { ...sci, ask: 'tosci' }), enemy: 'tenfold' };
      }
      // tostd
      const m = mant(Math.max(L, 1), false); let k = rand(1, [5, 6, 6, 7][L]);
      if (chance(tut ? 0.3 : NEGP[L] + 0.1)) k = -rand(1, [3, 4, 5, 5][L]);
      return { ex6: exState([N(m), Pw('10', k)], [], { ...sci, ask: 'tostd' }), enemy: 'tenfold' };
    }
    return { ex6: exState([N(3, 0), Pw('10', 4, 0), N(2, 1), Pw('10', 3, 1)], [], sci), enemy: 'tenfold' };
  }

  // Stage 24. Two or three polynomials added or subtracted.
  const ADD_CASES = ['add', 'sub', 'subneg', 'three', 'missing', 'twovar'];
  const CM = [6, 9, 12, 15];
  const coefP = (L, tut, neg = 0.35) => { const k = rand(1, tut ? 5 : CM[L]); return chance(tut ? 0.2 : neg) ? -k : k; };
  function polyOf(degs, L, tut, neg) { return degs.map(d => M(coefP(L, tut, neg), d)); }
  function degsFrom(top, count) { const all = []; for (let d = top; d >= 0; d--) all.push(d); const pickd = shuffle(all.slice()).slice(0, count).sort((a, b) => b - a); return pickd; }
  const VARS2 = [[2, 0], [1, 1], [0, 2], [1, 0], [0, 1]];
  function genAdd(cs, tut = isTutorial()) {
    const L = lvl(tut);
    cs = cs || pick(ADD_CASES);
    const nT = () => (tut ? rand(2, 3) : rand(2, [3, 3, 4, 4][L]));
    const top = () => (tut ? 2 : rand(2, [2, 3, 3, 4][L]));
    for (let n = 0; n < 400; n++) {
      let groups;
      if (cs === 'twovar') {
        const mk = () => shuffle(VARS2.slice(0, 3 + (L >= 2 ? 2 : 0))).slice(0, rand(2, 3)).sort((a, b) => b[0] + b[1] - a[0] - a[1] || b[0] - a[0]).map(([x, y]) => M(coefP(L, tut), x, y));
        groups = [Grp(1, mk()), Grp(sgn(), mk())];
      } else if (cs === 'missing') {
        const t = Math.max(3, top());
        const d1 = degsFrom(t, 2), d2 = degsFrom(t - 1, rand(2, 3));
        if (d1[0] !== t) continue;
        groups = [Grp(1, polyOf(d1, L, tut)), Grp(-1, polyOf(d2, L, tut))];
      } else {
        const t = top();
        const g = s => Grp(s, polyOf(degsFrom(t, Math.min(t + 1, nT())), L, tut, cs === 'subneg' && s < 0 ? 0.8 : 0.35));
        if (cs === 'add') groups = [g(1), g(1)];
        if (cs === 'sub' || cs === 'subneg') groups = [g(1), g(-1)];
        if (cs === 'three') { groups = [g(1), g(sgn()), g(sgn())]; if (!groups.some(x => x.s < 0)) groups[2].s = -1; }
      }
      const e = plState(groups, { skill: 'polyadd' });
      const { end, path } = pathOf6(e, 'polyadd');
      if (!path.some(p => p.move.op === 'comb6') || !end.items.length || path.length > 12) continue;
      if (cs === 'subneg' && groups[1].terms.filter(t => t.c.n < 0).length < 2) continue;
      if (cs === 'missing' && !path.some(p => p.move.op === 'sort6')) continue;
      return { ex6: e, enemy: 'collector' };
    }
    return { ex6: plState([Grp(1, [M(3, 2), M(2, 1)]), Grp(-1, [M(1, 2), M(-5, 1), M(1)])], { skill: 'polyadd' }), enemy: 'collector' };
  }

  // Stage 25. Binomial times binomial, squares, (a + b)(a − b), a monomial times a polynomial,
  // a binomial times a trinomial, and leading numbers.
  const MUL_CASES = ['binom', 'square', 'dos', 'mono', 'trinom', 'lead'];
  const nzc = (L, tut, max = [6, 8, 9, 12]) => (tut ? rand(1, 5) * (chance(0.3) ? -1 : 1) : nonZero(-max[L], max[L]));
  function genMul(cs, tut = isTutorial()) {
    const L = lvl(tut);
    cs = cs || pick(MUL_CASES);
    const X = (a = 1) => M(a, 1), C = k => M(k, 0);
    for (let n = 0; n < 400; n++) {
      let it;
      const a = () => (!tut && L >= 2 && chance(0.4) ? rand(2, 3) : 1);
      if (cs === 'binom') { const p = nzc(L, tut), q = nzc(L, tut); if (p === -q || p === q) continue; it = Prod([X(), C(p)], [X(), C(q)]); }
      if (cs === 'square') { const p = nzc(L, tut, [5, 7, 9, 10]); it = Sq(!tut && L >= 3 && chance(0.3) ? [X(a()), M(p, 0, 1)] : [X(a()), C(p)]); }
      if (cs === 'dos') { const p = rand(1, [6, 9, 10, 12][L]), k = a(); const A = [X(k), C(p)], B = [X(k), C(-p)]; it = chance(0.5) ? Prod(A, B) : Prod(B, A); }
      if (cs === 'mono') { const k = nzc(L, tut, [5, 6, 8, 9]), e = rand(1, L >= 2 ? 3 : 2); const B = polyOf(degsFrom(rand(1, 3), rand(2, 3)), L, tut); it = Prod([M(k, e)], B); }
      if (cs === 'trinom') { const p = nzc(L, tut, [5, 6, 7, 9]); it = Prod([X(), C(p)], [M(1, 2), M(nzc(L, tut, [5, 6, 7, 9]), 1), C(nzc(L, tut, [5, 6, 7, 9]))]); }
      if (cs === 'lead') { const A = [X(rand(2, [3, 4, 5, 6][L])), C(nzc(L, tut, [5, 6, 7, 9]))], B = [X(rand(1, [3, 4, 5, 6][L])), C(nzc(L, tut, [5, 6, 7, 9]))]; if (isConj({ t: 'prod', A, B })) continue; it = Prod(A, B); }
      if (!it) continue;
      if (it.t === 'prod' && it.A.length === 2 && !isConj(it) && cs === 'dos') continue;
      const e = plState([it], { skill: 'polymul' });
      const { end, path } = pathOf6(e, 'polymul');
      if (!end.items.length || path.length > 10 || plTerms(end).some(t => Math.abs(fv(t.c)) > 200)) continue;
      return { ex6: e, enemy: 'boxer' };
    }
    return { ex6: plState([Prod([X(), C(3)], [X(), C(-2)])], { skill: 'polymul' }), enemy: 'boxer' };
  }

  // Stage 26. Synthetic and long division by x − c, long division by ax + b, remainders, missing powers,
  // and dividing by a single term.
  const DIV_CASES = ['syn', 'long', 'lin2', 'rem', 'fill', 'mono'];
  const NMAX = [40, 60, 90, 120];
  function genDiv(cs, tut = isTutorial()) {
    const L = lvl(tut);
    cs = cs || pick(DIV_CASES);
    const qdeg = () => (tut ? 1 : rand(1, [1, 2, 2, 3][L]) + (L === 0 && chance(0.3) ? 1 : 0));
    for (let n = 0; n < 600; n++) {
      let N_, D, method = 'any';
      if (cs === 'mono') {
        const k = rand(1, tut ? 2 : [3, 4, 5, 6][L]), d = rand(1, L >= 2 ? 2 : 1);
        const terms = rand(2, tut ? 2 : 3), es = degsFrom(rand(terms - 1, 3), terms);
        const cs_ = []; es.forEach(e2 => { cs_[e2 + d] = k * nzc(L, tut, [5, 6, 8, 9]); });
        N_ = dense(cs_, es[0] + d); D = dense({ [d]: k }, d);
      } else {
        const c = tut ? rand(1, 4) * (chance(0.4) ? -1 : 1) : nonZero(-[5, 6, 7, 9][L], [5, 6, 7, 9][L]);
        const lin2 = cs === 'lin2';
        const qd = cs === 'fill' ? rand(1, 2) : qdeg();
        const Q = []; for (let i = 0; i <= qd; i++) Q.push(F(i === qd ? (lin2 || (!tut && L >= 2 && chance(0.25)) ? rand(1, 3) : 1) : nzc(L, tut, [5, 6, 8, 9])));
        D = lin2 ? dense({ 0: nonZero(-5, 5), 1: rand(2, 3) }, 1) : dense({ 0: -c, 1: 1 }, 1);
        N_ = pMul(Q, D);
        if (cs === 'fill') {   // a power missing in the middle: x² − 9, x³ − 8, x³ − 7x + 6 (and a remainder on Hard and up)
          const form = pick(['sq', 'cube', 'dep']), n3 = form !== 'sq' || chance(0.3) ? 3 : 2;
          const cs_ = { [n3]: 1 };
          if (form === 'dep' && n3 === 3) cs_[1] = nzc(L, tut, [6, 8, 9, 9]);
          cs_[0] = -(c ** n3) - (cs_[1] || 0) * c;
          if (!tut && L >= 2 && chance(0.35)) cs_[0] += nonZero(-6, 6);
          N_ = dense(cs_, n3);
          if (!holes(N_).some(k => k >= 1) || fz(N_[0])) continue;
        }
        if (cs === 'rem' || (lin2 && !tut && L >= 2 && chance(0.4))) N_[0] = fAdd(N_[0], F(nonZero(-[6, 8, 9, 9][L], [6, 8, 9, 9][L])));
        if (cs === 'fill' && !holes(N_).length) continue;
        if (cs !== 'fill' && holes(N_).length) continue;
        method = cs === 'syn' ? 'syn' : cs === 'long' || lin2 ? 'long' : 'any';
      }
      if (N_.some(f => Math.abs(fv(f)) > NMAX[L] || !isInt(f))) continue;
      const e = pdState(N_, D, { method });
      const { end } = pathOf6(e, 'polydiv');
      if (!end.Q || end.Q.some(f => !isInt(f))) continue;
      return { ex6: e, enemy: 'divider' };
    }
    return { ex6: pdState(dense({ 0: 6, 1: 5, 2: 1 }, 2), dense({ 0: 2, 1: 1 }, 1), { method: 'any' }), enemy: 'divider' };
  }

  // ---------------------------------------------------------------- elite and boss
  function comboPl(tut = false) {     // multiply, then subtract: (x + 3)(x − 2) − (x² − 5x), and friends
    const L = lvl(tut);
    for (let n = 0; n < 200; n++) {
      const p = nzc(L, tut), q = nzc(L, tut), r = nzc(L, tut, [5, 6, 7, 8]);
      const A = [M(1, 1), M(p)], B = [M(1, 1), M(q)];
      const form = pick(['prodsub', 'sqsubprod', 'sqsub', 'monoadd']);
      let items;
      if (form === 'prodsub') items = [Prod(A, B), Grp(-1, [M(1, 2), M(nzc(L, tut), 1)])];
      if (form === 'sqsubprod') items = [Sq(A), Prod([M(1, 1), M(r)], [M(1, 1), M(-r)], -1)];
      if (form === 'sqsub') items = [Sq(A), Grp(-1, [M(rand(1, 3), 2), M(nzc(L, tut), 1), M(nzc(L, tut))])];
      if (form === 'monoadd') items = [Prod([M(nzc(L, tut, [4, 5, 6, 6]), 1)], B), Grp(1, [M(nzc(L, tut), 2), M(r)])];
      const e = plState(items, { skill: 'polymul' });
      const { end, path } = pathOf6(e, 'polymul');
      if (!end.items.length || path.length > 12) continue;
      return { ex6: e, enemy: 'anvil' };
    }
    return { ex6: plState([Prod([M(1, 1), M(3)], [M(1, 1), M(-2)]), Grp(-1, [M(1, 2), M(-5, 1)])], { skill: 'polymul' }), enemy: 'anvil' };
  }
  function genStacked6(list) {
    const act6 = list.filter(id => (SKILL[id].act || 1) === 6), newest = act6[act6.length - 1];
    const el = g => ({ ...g, enemy: 'anvil' });
    if (newest === 'polydiv') return el(genDiv(pick(['fill', 'rem', 'lin2'])));
    if (newest === 'polymul') return comboPl();
    if (newest === 'polyadd') return el(genAdd(pick(['three', 'missing', 'twovar'])));
    if (newest === 'scinot') return el(genSci(pick(['mulnorm', 'divnorm'])));
    return el(genExp('mixed'));
  }
  function buildFight6(node, list) {
    const act6 = list.filter(id => (SKILL[id].act || 1) === 6);
    if (node.type === 'elite') return { phases: [() => genStacked6(list)], handSize: difficulty.hand, enemy: 'anvil' };
    // Boss: one phase per Act 6 stage, then an expression that mixes them.
    const phases = act6.map(id => () => GENS[id](pick(SKILL[id].cases)));
    phases.push(() => (act6.includes('polymul') ? comboPl() : act6.includes('scinot') ? genSci(pick(['mulnorm', 'divnorm'])) : genExp('mixed')));
    return { phases, handSize: difficulty.hand, enemy: 'forgemaster' };
  }
  const GENS = { exprules: genExp, scinot: genSci, polyadd: genAdd, polymul: genMul, polydiv: genDiv };

  // ---------------------------------------------------------------- variety
  function textOf6(e) {
    if (e.k6 === 'ex') return (e.ask === 'tostd' ? 'standard form of ' : e.ask === 'tosci' ? 'sci notation of ' : '') + exText(e);
    if (e.k6 === 'pl') return plText(e);
    return pdText(e) + (e.method !== 'any' ? ` (${e.method})` : '');
  }
  if (typeof ENGINES === 'object') ENGINES.ex6 = { text: textOf6 };
  const applyDifficulty = g => g;   // generators read the difficulty themselves; tutorials stay on Easy

  // ================================================================ skills, enemies, act
  SKILLS.push(
    { id: 'exprules', stage: 22, act: 6, name: 'Exponent rules', cases: EXP_CASES, gen: cycled('exprules', c => genExp(c)),
      title: 'Stage 22: Exponent rules',
      intro: 'An exponent counts how many times a base is multiplied: x³ = x · x · x. Five rules follow from that. Product: x² · x³ = x⁵ (add). Power: (x²)³ = x⁶ (multiply), and the power hits every factor in the bracket. Quotient: x⁵/x² = x³ (subtract). Zero: x⁰ = 1. Negative: x⁻² = 1/x² (move it across the bar). Drop the rule card on the part it changes.',
      example: '(2x³)(4x²)<br>× numbers → 8 · x³ · x²<br>Product rule → 8x⁵<br><br>x⁵/x² → Quotient rule → x³',
      tutorial: [() => genExp('prod', true), () => genExp('pow', true)] },
    { id: 'scinot', stage: 23, act: 6, name: 'Scientific notation', cases: SCI_CASES, gen: cycled('scinot', c => genSci(c)),
      title: 'Stage 23: Scientific notation',
      intro: 'Scientific notation writes a number as (a number from 1 to 10) × (a power of 10): 45 000 = 4.5 × 10⁴, 0.003 = 3 × 10⁻³. To multiply or divide, Group the tens (numbers together, powers of 10 together), work each part (the Product and Quotient rules work on the tens), then Normalize: if the number isn\'t from 1 to 10, move the point and change the power to make up for it.',
      example: '(3 × 10⁴)(2 × 10³)<br>Group tens → (3 · 2)(10⁴ · 10³)<br>× numbers → 6 · Product rule → 6 × 10⁷<br><br>24 × 10⁷ → Normalize → 2.4 × 10⁸',
      tutorial: [() => genSci('mul', true), () => genSci('mulnorm', true)] },
    { id: 'polyadd', stage: 24, act: 6, name: 'Add & subtract polynomials', cases: ADD_CASES, gen: cycled('polyadd', c => genAdd(c)),
      title: 'Stage 24: Adding and subtracting polynomials',
      intro: 'First clear the brackets. A + in front changes nothing: Drop ( ). A minus in front multiplies every term inside by −1: Minus in flips every sign, not just the first. Then Combine like terms, which have exactly the same power (3x² and −x²), by adding the numbers in front. Finish in standard form, highest power first.',
      example: '(3x² + 2x) − (x² − 5x + 1)<br>Drop ( ), Minus in → 3x² + 2x − x² + 5x − 1<br>Combine → 2x² + 7x − 1',
      tutorial: [() => genAdd('add', true), () => genAdd('sub', true)] },
    { id: 'polymul', stage: 25, act: 6, name: 'Multiply polynomials', cases: MUL_CASES, gen: cycled('polymul', c => genMul(c)),
      title: 'Stage 25: Multiplying polynomials',
      intro: 'Multiply out with the box method: every term of one bracket times every term of the other, one box each, then Combine like terms. Two shortcuts: (a + b)² = a² + 2ab + b² (Square a binomial: never forget the middle term), and (a + b)(a − b) = a² − b² (Difference of squares: the middle terms cancel).',
      example: '(x + 3)(x − 2)<br>Box → x² − 2x + 3x − 6<br>Combine → x² + x − 6<br><br>(x + 3)(x − 3) → x² − 9',
      tutorial: [() => genMul('binom', true), () => genMul('square', true)] },
    { id: 'polydiv', stage: 26, act: 6, name: 'Divide polynomials', cases: DIV_CASES, gen: cycled('polydiv', c => genDiv(c)),
      title: 'Stage 26: Dividing polynomials',
      intro: 'Long division works like it does with numbers: divide the leading terms to get the next term on top, multiply it back, subtract, bring down, repeat. Pick the right next term each time. Dividing by x − c? Synthetic division is a shortcut: use c (for x + 2, c = −2). Write 0 for any missing power first. Dividing by one term? Split the fraction and divide each term.',
      example: '(x² + 5x + 6) ÷ (x + 2)<br>x² ÷ x = x → x(x + 2) = x² + 2x → subtract → 3x + 6<br>3x ÷ x = 3 → 3(x + 2) → subtract → 0<br>Answer: x + 3',
      tutorial: [() => genDiv('long', true), () => genDiv('syn', true)] },
  );
  for (const s of SKILLS) SKILL[s.id] = s;
  progress = loadProgress();     // the save was first read before these skills existed

  Object.assign(ENEMIES, {
    powerling:   { name: 'Powerling',      rank: 'Normal', color: '#ff9f1c', size: 84 },
    tenfold:     { name: 'Tenfold',        rank: 'Normal', color: '#2ec4b6', size: 84 },
    collector:   { name: 'Collector',      rank: 'Normal', color: '#e71d36', size: 84 },
    boxer:       { name: 'Boxer',          rank: 'Normal', color: '#ff70a6', size: 84 },
    divider:     { name: 'Divider',        rank: 'Normal', color: '#70d6ff', size: 84 },
    anvil:       { name: 'Anvil Golem',    rank: 'Elite',  color: '#8d99ae', size: 100, horns: true },
    forgemaster: { name: 'The Forgemaster', rank: 'Boss',  color: '#f77f00', size: 120, crown: true },
  });
  ACTS[6] = { name: 'The Power Forge', sub: 'Exponents and polynomials', boss: 'The Forgemaster', firstSkill: 'exprules',
    blurb: 'In the Power Forge, expressions come in raw and you hammer them into their simplest form: exponent rules, scientific notation, and adding, multiplying and dividing polynomials. Defeat The Forgemaster.' };

  const svgI = body => `<svg viewBox="0 0 24 24" width="1em" height="1em" fill="none" stroke="currentColor" stroke-width="2.6" stroke-linecap="round" stroke-linejoin="round">${body}</svg>`;
  Object.assign(CARD_ICONS, {
    prod6:  { name: 'Product rule (add exponents)', svg: svgI('<path d="M3 17h5M5.5 14.5v5"/><path d="M11 8h4M13 6v4" stroke-width="2"/><path d="M17 8h4M19 6v4" stroke-width="2"/>') },
    pow6:   { name: 'Power rule (multiply exponents)', svg: svgI('<path d="M4 6c-2 4-2 8 0 12M12 6c2 4 2 8 0 12"/><path d="M16 4l4 4M20 4l-4 4" stroke-width="2"/>') },
    quot6:  { name: 'Quotient rule (subtract exponents)', svg: svgI('<path d="M4 12h12"/><path d="M8 5h4M8 19h4"/><path d="M17 5h4" stroke-width="2"/>') },
    zero6:  { name: 'Zero exponent (= 1)', svg: svgI('<path d="M4 18V8M2 10l2-2"/><ellipse cx="16" cy="7" rx="3" ry="4" stroke-width="2"/>') },
    negx6:  { name: 'Negative exponent (move across the bar)', svg: svgI('<path d="M3 12h12M9 4v5M7 7l2 2 2-2M9 20v-5"/><path d="M17 6h5" stroke-width="2"/>') },
    grp6:   { name: 'Group the numbers and the tens', svg: svgI('<path d="M5 5c-2 4-2 10 0 14M11 5c2 4 2 10 0 14M14 5c-2 4-2 10 0 14M20 5c2 4 2 10 0 14"/>') },
    norm6:  { name: 'Normalize (1 to 10 × a power of 10)', svg: svgI('<circle cx="6" cy="18" r="1.5"/><path d="M10 12c3-5 7-5 10 0M18 10l2 2 2-2"/>') },
    std6:   { name: 'Standard form (write it out)', svg: svgI('<path d="M3 16h18"/><circle cx="18" cy="12" r="1.5"/><path d="M14 8c-3-4-7-4-10 0M6 6L4 8l2 2"/>') },
    drop6:  { name: 'Drop + brackets', svg: svgI('<path d="M8 4c-3 5-3 11 0 16M16 4c3 5 3 11 0 16" stroke-dasharray="3 3"/><path d="M12 9v6M9 12h6"/>') },
    sort6:  { name: 'Standard form order (highest power first)', svg: svgI('<path d="M4 6h14M4 12h10M4 18h6M20 10v10M17 17l3 3 3-3"/>') },
    box6:   { name: 'Multiply out (box method)', svg: svgI('<rect x="3" y="3" width="18" height="18" rx="1"/><path d="M12 3v18M3 12h18"/>') },
    sqb6:   { name: 'Square a binomial', svg: svgI('<rect x="3" y="3" width="18" height="18" rx="1"/><path d="M10 3v18M3 10h18"/><path d="M3 3l7 7M10 10l11 11" stroke-width="1.6"/>') },
    dos6:   { name: 'Difference of squares', svg: svgI('<rect x="3" y="3" width="18" height="18" rx="1"/><rect x="13" y="13" width="8" height="8" stroke-dasharray="2 2"/>') },
    fill6:  { name: 'Fill in 0 for missing powers', svg: svgI('<ellipse cx="12" cy="12" rx="5" ry="7"/><path d="M3 21h18" stroke-dasharray="3 3"/>') },
    long6:  { name: 'Long division (next term on top)', svg: svgI('<path d="M7 20V7c3 0 3-3 3-3h11"/><path d="M12 12h8M12 17h6"/>') },
    syn6:   { name: 'Synthetic division', svg: svgI('<path d="M7 3v10H3M7 13h14"/><path d="M11 18h2M16 18h2M10 8l3 3M15 8l3 3"/>') },
    split6: { name: 'Split the fraction', svg: svgI('<path d="M3 12h7M14 12h7"/><path d="M5 7h3M5 17h3M16 7h3M16 17h3"/>') },
  });

  const css = document.createElement('style');
  css.textContent = `
    #equation.ex6 { flex-wrap:nowrap; gap:0; max-width:100%; align-items:center; }
    .tok.a4.f6 { padding:4px 3px; min-width:0; }
    .tok.a4.s6 { padding:4px 2px; min-width:0; color:var(--muted); border-color:transparent !important; background:none !important; }
    .tok.a4.f6.tightL { margin-left:-4px; }
    .tok.a4.s6.tightL { margin-left:-6px; } .tok.a4.s6.tightP { margin-left:-2px; }
    sup.e6 { font-size:.55em; vertical-align:.75em; line-height:0; margin-left:.04em; }
    .frac6 sup.e6, .frac sup.e6 { font-size:.6em; }
    .tok.a4 .xv, .unote .xv { font-style:normal; color:var(--accent); }
    .frac6 { font-size:.85em; }
    .frac6 .tok.a4 { min-height:0; padding:2px 3px; }
    .tok.a4.pt6, .tok.a4.pg6 { padding:4px 5px; white-space:nowrap; }
    .tok.a4.pg6 .gone6 { opacity:0; transition: opacity .3s; }
    .tok.a4.pg6 .ga6 { color:#ffc46b; } .tok.a4.pg6 .gb6 { color:var(--ink); }
    .flip6 { display:inline-block; animation: flip6 .35s ease-in-out; color:#ff9ad5; }
    @keyframes flip6 { 50% { transform: rotateX(90deg); } }
    .tok.a4.hop6 { animation: hop6 .22s ease-out; }
    @keyframes hop6 { 40% { transform: translateY(-.18em); } }
    .tok.a4.hot6 { background:#ffffff14; border-color:var(--accent); }
    .pc6.hot6 { color:var(--accent); }
    sup.lift6 { display:inline-block; animation: lift6 .6s ease-out forwards; }
    @keyframes lift6 { to { transform: translateY(-.6em); opacity:.25; } }
    .tok.a4.sink6 { transform: translateY(.4em) scale(.7); opacity:.2; }
    .tok.ok6 { border-color: var(--good) !important; background:#06d6a022 !important; }
    .unote.box6n { font-size:.42em; color:var(--ink); }
    .box6t { border-collapse:collapse; margin-top:.3em; background:#0005; }
    .box6t th, .box6t td { border:2px solid var(--muted); padding:.15em .45em; white-space:nowrap; }
    .box6t th { color:#ffc46b; font-weight:bold; }
    .box6t th.corner6 { color:var(--muted); }
    .box6t td { color:transparent; }
    .box6t td.in { color:var(--good); animation: pop .3s; }
    .tok.a4.pd6 { flex-direction:column; padding:6px 8px; white-space:nowrap; }
    .frac.f6 { font-size:.8em; } .frac.big6 { font-size:.9em; }
    .frac.f6 > span { padding:0 .2em; }
    .ph6 { color:#7bdff2; }
    .pc6 { display:inline-flex; align-items:center; gap:.15em; margin:0 .1em; }
    .long6, .syn6 { display:grid; column-gap:.55em; row-gap:.08em; align-items:center; font-size:.62em; line-height:1.3; }
    .long6 .c6, .syn6 .c6 { text-align:center; min-width:1.4em; }
    .long6 .nd6 { border-top:.08em solid var(--ink); }
    .long6 .dv6 { color:#ffc46b; text-align:right; padding-right:.15em; }
    .long6 .q6 { color:var(--good); }
    .long6 .pr6, .long6 .mn6 { color:#ff9ad5; border-bottom:.06em solid var(--muted); }
    .long6 .mn6 { border-bottom:none; text-align:right; }
    .long6 .rm6 { color:var(--ink); }
    .syn6 .sc6 { color:#ffc46b; border-right:.08em solid var(--ink); padding-right:.3em; }
    .syn6 .sp6 { color:#ff9ad5; border-bottom:.08em solid var(--ink); }
    .syn6 .ss6 { color:var(--good); }
    .syn6 .rem6 { outline:.06em solid var(--muted); outline-offset:.1em; border-radius:2px; }
    .res6 { margin-top:.25em; font-size:.62em; color:var(--good); align-self:center; }
    .card .clong.l6 { white-space:normal; display:block; line-height:1.05; }
    .card .clong.l6 sup { font-size:.6em; }
    @media (max-width: 640px) {
      .tok.a4.pt6, .tok.a4.pg6 { padding:2px 3px; }
      .long6, .syn6 { column-gap:.4em; }
    }
  `;
  document.head.appendChild(css);

  window.ACT6 = { apply: apply6, isSolved: isSolved6, makeEquation: makeEquation6, refreshPath, render, prefit, clear, makeHand: makeHand6,
    isCorrect, whyWrong, animFor, applyDifficulty, label, text, kind, icon, slot, targetSel, onDrag, autoTarget, buildFight: buildFight6, prompt,
    gens: GENS, eqText: textOf6,
    // test hooks
    _canon: canon6, _correct: correct6, _moves: movesOf, _apply: apply6, _places: places };
})();
