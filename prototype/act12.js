// =====================================================================
//  Act 12: The Orrery (the Algebra 2 endgame)
// =====================================================================
// Stage 53  Polynomial roots        possible roots, test a root, divide it out, factor the rest; grouping;
//                                   x⁴ − 13x² + 36 = 0; remainder theorem; build a polynomial from its roots
// Stage 54  Three-variable systems  eliminate one variable twice, then solve the 2×2 and back-substitute;
//                                   systems with no solution or infinitely many
// Stage 55  Sequences and series    arithmetic and geometric terms and sums, Σ notation, infinite geometric
//                                   series (and when there's no sum), recursive sequences
// Stage 56  Conics                  circles by completing the square, standard forms, ellipses, parabolas,
//                                   hyperbolas, classifying a conic from its equation
//
// Problems are scripted like Act 11 (kit9.js `scripted`): the generator works out each step and its classic
// mistakes, and the player picks the right card at every step.
'use strict';
(function () {
  const KT = window.KIT9;
  if (!KT || !KT.scripted) return;
  const { P, FN, chance, qid, isTutorial, lvl, supH, supT, XV, numH, frH, ptext, P1, pmul, padd, pscale, peval, pEq, fv, svgI, drawCurves, fNeg, fDiv, fEq } = KT;
  const X = XV(), Y = XV('y'), Z = XV('z'), U = XV('u'), Nv = XV('n');
  const pw = (b, e) => `${b}${supH(e)}`;
  const M_ = n => (n < 0 ? MINUS + Math.abs(n) : String(n));
  const trimDec = v => { const s = String(+(+v).toFixed(6)); return s.startsWith('-') ? MINUS + s.slice(1) : s; };
  const nh = f => numH(FN(f), true);
  const alt = (v, why, long, op) => ({ v, why, long, op });
  const st = (op, v, row, o = {}) => ({ op, v, row, ...o });
  const nz = (a, b) => nonZero(a, b);
  const xm = r => ptext(P1(1, -r), true);                 // x − r
  const pt = p => ptext(p, true);
  const S12 = (kind, skill, pk, top, row0, steps, ans, extra = {}) => ({ k12: kind, top, rows: [row0], i: 0, steps, ans, skill, pk, qid: qid(), ...extra });
  const uniqBy = (xs, f) => { const seen = new Set(); return xs.filter(x => { const k = f(x); if (seen.has(k)) return false; seen.add(k); return true; }); };

  const OPS = {
    cand12: { kind: 'List possible roots', text: 'Rational roots divide the constant term (over the leading coefficient)', icon: 'cand12' },
    test12: { kind: 'Test a root', text: 'A root makes the polynomial 0', icon: 'test12' },
    use12:  { kind: 'Pick the number to divide by', text: 'Dividing by (x − r) uses r', icon: 'syn12' },
    syn12:  { kind: 'Synthetic division', text: 'Divide out the factor', icon: 'syn12', fx: 'spin11' },
    rem12:  { kind: 'Remainder theorem', text: 'The remainder of f(x) ÷ (x − r) is f(r)', icon: 'test12' },
    ev12:   { kind: 'Work it out', text: 'Work out the value', icon: 'calc12', fx: 'spin11' },
    grp12:  { kind: 'Group', text: 'Factor each pair', icon: 'grp12' },
    fac12:  { kind: 'Factor', text: 'Factor it', icon: 'fac9' },
    sub12:  { kind: 'Substitute', text: 'Let u = x² to make a quadratic', icon: 'sub12' },
    back12: { kind: 'Back to x', text: 'Put x² back for u', icon: 'sub12' },
    zp12:   { kind: 'Each factor = 0', text: 'A product is 0 when a factor is 0', icon: 'zp9' },
    mul12:  { kind: 'Multiply out', text: 'Multiply the factors', icon: 'mul12' },
    el12:   { kind: 'Eliminate', text: 'Add or subtract equations to remove a variable', icon: 'el12' },
    sv12:   { kind: 'Solve', text: 'Get the variable alone', icon: 'sv12' },
    bs12:   { kind: 'Back-substitute', text: 'Put the value you know into an earlier equation', icon: 'bs12' },
    end12:  { kind: 'Read the result', text: 'What does the last equation say?', icon: 'chk11' },
    kind12: { kind: 'Arithmetic or geometric', text: 'Same difference: arithmetic. Same ratio: geometric.', icon: 'kind12' },
    d12:    { kind: 'Find d or r', text: 'The common difference or ratio', icon: 'd12' },
    form12: { kind: 'Write the formula', text: 'The formula for the nth term or the sum', icon: 'form12' },
    plug12: { kind: 'Plug in', text: 'Put the numbers into the formula', icon: 'plug9' },
    rec12:  { kind: 'Next term', text: 'Use the rule on the term before', icon: 'rec12' },
    grpc12: { kind: 'Group x and y', text: 'Group the x terms and the y terms; move the number over', icon: 'grp12' },
    cs12:   { kind: 'Complete the square', text: 'Add (half the coefficient)² to both sides', icon: 'cs12' },
    std12:  { kind: 'Standard form', text: 'Write it in standard form', icon: 'form12' },
    read12: { kind: 'Read it off', text: 'Read the center, radius, vertices or asymptotes', icon: 'read12' },
    cls12:  { kind: 'Classify', text: 'Look at the x² and y² terms', icon: 'kind12' },
    dv12:   { kind: 'Divide', text: 'Divide both sides so the right side is 1', icon: 'div11' },
  };
  const SC = KT.scripted({ OPS, keepRows: 4 });

  // ================================================================ stage 53: polynomial roots
  const synth = (p, r) => {   // p dense (index = power) ÷ (x − r) -> { q, rem }
    const co = p.slice().reverse().map(FN); const out = [co[0]];
    for (let i = 1; i < co.length; i++) out.push(fAdd(co[i], fMul(out[i - 1], F(r))));
    const rem = out.pop(); return { q: out.reverse(), rem };
  };
  const divisors = n => { n = Math.abs(n); const d = []; for (let i = 1; i <= n; i++) if (n % i === 0) d.push(i); return d; };
  const pm = ds => ds.map(d => `±${d}`).join(', ');
  const ROOT_CASES = ['rrt', 'synth', 'rem', 'group', 'biquad', 'build'];
  function genRoots(cs, tut = isTutorial()) {
    const L = lvl(tut);
    cs = cs || pick(ROOT_CASES);
    for (let tries = 0; tries < 200; tries++) {
      if (cs === 'rrt') {
        const R = [0, 0, 0].map(() => nz(-[3, 4, 5, 5][L], [3, 4, 5, 5][L]));
        if (new Set(R).size < 2) continue;
        const p = pmul(pmul(P1(1, -R[0]), P1(1, -R[1])), P1(1, -R[2]));
        const c0 = fv(p[0]); if (Math.abs(c0) > 60) continue;
        const ds = divisors(c0);
        const r1 = R[0], test = ds.map(d => [d, -d]).flat().find(q => !R.includes(q) && Math.abs(q) <= 6);
        if (test === undefined) continue;
        const fq = fv(peval(p, F(test)));
        const { q } = synth(p, r1), wrongQ = synth(p, -r1).q;
        const others = R.slice(1).sort((a, b) => b - a), fct = `(${xm(r1)})(${xm(others[0])})(${xm(others[1])}) = 0`;
        const roots = [...new Set(R)].sort((a, b) => a - b).map(M_).join(', ');
        const steps = [
          st('cand12', `Possible roots: ${pm(ds)}`, `${pt(p)} = 0`, { alts: [alt(`Possible roots: ${ds.join(', ')}`, 'A root can be negative too: use ± each divisor.'), alt(`Possible roots: ${pm(divisors(fv(p[2]) || 1))}`, `Rational roots divide the constant term (${M_(c0)}), not the x² coefficient.`)], rule: [alt(`Possible roots: ${ds.join(', ')}`, 'Include the negatives: ± each divisor of the constant term.')], why: [`Divisors of the constant ${M_(c0)}, with ±.`], cap: `Divisors of ${M_(c0)}, positive and negative`, note: false }),
          st('test12', `${X} = ${M_(r1)}: f(${M_(r1)}) = 0 ✓`, `f(${M_(r1)}) = 0, so (${xm(r1)}) is a factor`, { alts: [alt(`${X} = ${M_(test)}: f(${M_(test)}) = 0 ✓`, `f(${M_(test)}) = ${M_(fq)}, not 0: ${M_(test)} isn't a root.`)], why: ['A root makes f(x) = 0.'], cap: `f(${M_(r1)}) = 0: a root` }),
          st('syn12', `(${xm(r1)})(${pt(q)}) = 0`, `(${xm(r1)})(${pt(q)}) = 0`, { alts: [alt(`(${xm(r1)})(${pt(wrongQ)}) = 0`, `Divide using ${M_(r1)}, the root: (x − r) uses r.`)], rule: [alt(`(${xm(r1)})(${pt(wrongQ)}) = 0`, `Synthetic division by (${KT.strip(xm(r1))}) uses ${M_(r1)}, the number that makes it 0.`)], why: [`Synthetic division with ${M_(r1)}.`], cap: `Synthetic division with ${M_(r1)}` }),
          st('fac12', fct, fct, { alts: [alt(`(${xm(r1)})(${xm(-others[0])})(${xm(-others[1])}) = 0`, 'Check the signs: multiply back.')], why: ['Factor the quadratic.'], cap: 'Factor the quadratic' }),
          st('zp12', `${X} = ${roots}`, `${X} = ${roots}`, { alts: [alt(`${X} = ${[...new Set(R)].sort((a, b) => a - b).map(r => M_(-r)).join(', ')}`, 'x − 2 = 0 gives x = 2: the sign changes.')], why: ['Set each factor to 0.'], cap: 'Each factor = 0' }),
        ];
        return { r12: S12('pr', 'polyroots', 'roots', 'Find every root.', `${pt(p)} = 0`, steps, `${X} = ${roots}`), enemy: 'cogmoon' };
      }
      if (cs === 'synth' || cs === 'rem') {
        const r = nz(-4, 4), deg = L >= 2 ? 4 : 3;
        const p = [F(nz(-9, 9))]; for (let i = 1; i < deg; i++) p.push(F(rand(-6, 6))); p.push(F(1));
        const { q, rem } = synth(p, r), wr = synth(p, -r);
        if (cs === 'synth') {
          const v = fv(rem) ? `${pt(q)}, remainder ${nh(rem)}` : `${pt(q)}, remainder 0`;
          const vb = fv(wr.rem) ? `${pt(wr.q)}, remainder ${nh(wr.rem)}` : `${pt(wr.q)}, remainder 0`;
          const qBad = q.slice(); qBad[0] = fAdd(qBad[0], F(1));
          const steps = [
            st('use12', `Use ${M_(r)}`, `(${pt(p)}) ÷ (${xm(r)})`, { alts: [alt(`Use ${M_(-r)}`, `${KT.strip(xm(r))} = 0 at x = ${M_(r)}: divide with ${M_(r)}.`)], rule: [alt(`Use ${M_(-r)}`, `For (x − r) use r: here ${M_(r)}, the number that makes ${KT.strip(xm(r))} zero.`)], why: [`(${KT.strip(xm(r))}) is 0 at x = ${M_(r)}.`], cap: `${KT.strip(xm(r))} = 0 at x = ${M_(r)}`, note: false }),
            st('syn12', v, `${pt(q)}${fv(rem) ? `, remainder ${nh(rem)}` : ''}`, { alts: [alt(vb, `That divides with ${M_(-r)}.`), alt(`${pt(qBad)}, remainder ${nh(rem)}`, 'Bring down, multiply by r, add: check each column.')], why: ['Bring down, multiply, add.'], cap: 'Bring down, multiply by r, add' }),
          ];
          return { r12: S12('pr', 'polyroots', 'div', 'Divide with synthetic division.', `(${pt(p)}) ÷ (${xm(r)})`, steps, `${pt(q)}${fv(rem) ? `, remainder ${nh(rem)}` : ', remainder 0'}`), enemy: 'cogmoon' };
        }
        const sub = pt(p).replace(/<i class="xv">x<\/i>/g, `(${M_(r)})`);
        const steps = [
          st('rem12', `Remainder = f(${M_(r)})`, `f(${M_(r)}) = ${sub}`, { alts: [alt(`Remainder = f(0)`, 'Put in the r from (x − r).')], rule: [alt(`Remainder = f(${M_(-r)})`, `The remainder of f(x) ÷ (x − r) is f(r): here r = ${M_(r)}.`)], why: [`The remainder is f(${M_(r)}).`], cap: 'Remainder theorem: the remainder is f(r)' }),
          st('ev12', `f(${M_(r)}) = ${nh(rem)}`, `Remainder = ${nh(rem)}`, { alts: [alt(`f(${M_(r)}) = ${nh(wr.rem)}`, `That's f(${M_(-r)}).`), alt(`f(${M_(r)}) = ${nh(fAdd(rem, F(r)))}`, 'Work out each power carefully.')], why: ['Work it out.'], cap: 'Work it out' }),
        ];
        return { r12: S12('pr', 'polyroots', 'rem', `Find the remainder when f(${X}) = ${pt(p)} is divided by (${xm(r)}).`, `f(${X}) ÷ (${xm(r)})`, steps, `Remainder = ${nh(rem)}`), enemy: 'cogmoon' };
      }
      if (cs === 'group') {
        const a = nz(-6, 6), m = rand(1, [3, 4, 5, 6][L]), b = -m * m;
        const p = [F(a * b), F(b), F(a), F(1)];
        const g1 = `${pw(X, 2)}(${ptext(P1(1, a), true)}) ${MINUS} ${m * m}(${ptext(P1(1, a), true)})`;
        const roots = [-a, -m, m].sort((x, y) => x - y);
        if (new Set(roots).size < 3) continue;
        const steps = [
          st('grp12', `${g1} = 0`, `${g1} = 0`, { alts: [alt(`${pw(X, 2)}(${ptext(P1(1, a), true)}) + ${m * m}(${ptext(P1(1, a), true)}) = 0`, `Take out ${MINUS}${m * m}: it flips the sign of each term in the second pair.`)], rule: [alt(`${pw(X, 2)}(${ptext(P1(1, a), true)}) ${MINUS} ${m * m}(${ptext(P1(1, -a), true)}) = 0`, `Taking out ${MINUS}${m * m} flips both signs: ${MINUS}${m * m}x ${a * b < 0 ? MINUS : '+'} ${Math.abs(a * b)} = ${MINUS}${m * m}(x ${a < 0 ? MINUS : '+'} ${Math.abs(a)}).`)], why: ['Factor each pair: the brackets must match.'], cap: 'Factor each pair' }),
          st('fac12', `(${pw(X, 2)} ${MINUS} ${m * m})(${ptext(P1(1, a), true)}) = 0`, `(${pw(X, 2)} ${MINUS} ${m * m})(${ptext(P1(1, a), true)}) = 0`, { alts: [alt(`(${pw(X, 2)} + ${m * m})(${ptext(P1(1, a), true)}) = 0`, 'Check the sign of the second pair.')], why: ['Take out the common bracket.'], cap: 'The common bracket comes out' }),
          st('fac12', `(${xm(m)})(${xm(-m)})(${ptext(P1(1, a), true)}) = 0`, `(${xm(m)})(${xm(-m)})(${ptext(P1(1, a), true)}) = 0`, { alts: [alt(`(${xm(m)})(${xm(m)})(${ptext(P1(1, a), true)}) = 0`, 'a² − b² = (a − b)(a + b).')], why: ['A difference of squares.'], cap: 'Difference of squares' }),
          st('zp12', `${X} = ${roots.map(M_).join(', ')}`, `${X} = ${roots.map(M_).join(', ')}`, { alts: [alt(`${X} = ${roots.map(r => M_(-r)).join(', ')}`, 'Each factor = 0: the sign changes.')], why: ['Each factor = 0.'], cap: 'Each factor = 0' }),
        ];
        return { r12: S12('pr', 'polyroots', 'roots', 'Solve by grouping.', `${pt(p)} = 0`, steps, `${X} = ${roots.map(M_).join(', ')}`), enemy: 'cogmoon' };
      }
      if (cs === 'biquad') {
        const s = rand(1, [3, 4, 5, 6][L]), t = rand(1, [3, 4, 5, 6][L]);
        if (s >= t) continue;
        const pp = -(s * s + t * t), qq = s * s * t * t;
        const eq = `${pw(X, 4)} ${MINUS} ${-pp}${pw(X, 2)} + ${qq} = 0`;
        const steps = [
          st('sub12', `Let ${U} = ${pw(X, 2)}: ${pw(U, 2)} ${MINUS} ${-pp}${U} + ${qq} = 0`, `${pw(U, 2)} ${MINUS} ${-pp}${U} + ${qq} = 0`, { alts: [alt(`Let ${U} = ${X}: ${pw(U, 4)} ${MINUS} ${-pp}${pw(U, 2)} + ${qq} = 0`, 'That changes nothing. x⁴ = (x²)², so let u = x².'), alt(`Let ${U} = ${pw(X, 4)}: ${U} ${MINUS} ${-pp}${U} + ${qq} = 0`, 'x² isn\'t u either way: let u = x², then x⁴ = u².')], why: ['x⁴ = (x²)²: let u = x².'], cap: 'x⁴ = (x²)²: let u = x²' }),
          st('fac12', `(${U} ${MINUS} ${s * s})(${U} ${MINUS} ${t * t}) = 0`, `(${U} ${MINUS} ${s * s})(${U} ${MINUS} ${t * t}) = 0`, { alts: [alt(`(${U} + ${s * s})(${U} + ${t * t}) = 0`, `They multiply to ${qq} and add to ${pp}: both negative.`)], why: [`Two numbers that multiply to ${qq} and add to ${pp}.`], cap: 'Factor the quadratic in u' }),
          st('back12', `${pw(X, 2)} = ${s * s} or ${pw(X, 2)} = ${t * t}`, `${pw(X, 2)} = ${s * s} or ${pw(X, 2)} = ${t * t}`, { alts: [alt(`${X} = ${s * s} or ${X} = ${t * t}`, 'u is x², not x.')], why: ['Put x² back for u.'], cap: 'u = x²' }),
          st('zp12', `${X} = ±${s}, ±${t}`, `${X} = ±${s}, ±${t}`, { alts: [alt(`${X} = ${s * s}, ${t * t}`, 'Take square roots.')], rule: [alt(`${X} = ${s}, ${t}`, `x² = ${s * s} has two roots: ${s} and ${MINUS}${s}. A degree 4 polynomial can have 4 roots.`)], why: ['Square root both: ±.'], cap: 'Square roots: ± each' }),
        ];
        return { r12: S12('pr', 'polyroots', 'roots', 'Find every root.', eq, steps, `${X} = ±${s}, ±${t}`), enemy: 'cogmoon' };
      }
      // build: polynomial from its roots
      const n3 = L >= 1 && chance(0.6);
      const R = (n3 ? [0, 0, 0] : [0, 0]).map(() => nz(-5, 5));
      if (new Set(R).size < R.length) continue;
      const f1 = R.map(r => `(${xm(r)})`).join(''), fBad = R.map(r => `(${xm(-r)})`).join('');
      const p2 = pmul(P1(1, -R[0]), P1(1, -R[1])), pAll = n3 ? pmul(p2, P1(1, -R[2])) : p2;
      const pBad = n3 ? pmul(pmul(P1(1, R[0]), P1(1, R[1])), P1(1, R[2])) : pmul(P1(1, R[0]), P1(1, R[1]));
      const steps = [
        st('fac12', f1, f1, { alts: [alt(fBad, `A root r gives the factor (x − r): x = ${M_(R[0])} gives (${KT.strip(xm(R[0]))}).`)], rule: [alt(fBad, 'A root r makes (x − r) zero: the sign flips inside the bracket.')], why: ['A root r gives the factor (x − r).'], cap: 'Each root r gives a factor (x − r)' }),
      ];
      if (n3) steps.push(st('mul12', `(${pt(p2)})(${xm(R[2])})`, `(${pt(p2)})(${xm(R[2])})`, { alts: [alt(`(${pt(pmul(P1(1, R[0]), P1(1, -R[1])))})(${xm(R[2])})`, 'Multiply carefully: watch the signs.')], why: ['Multiply the first two.'], cap: 'Multiply the first two' }));
      steps.push(st('mul12', pt(pAll), pt(pAll), { alts: [alt(pt(pBad), 'That uses the wrong signs in the factors.'), alt(pt(padd(pAll, [F(2)])), 'Check the number on the end: it is the product of the −r values.')], why: ['Multiply it all out.'], cap: 'Multiply out' }));
      return { r12: S12('pr', 'polyroots', 'build', `Write a polynomial with roots ${R.map(M_).join(', ')} (leading coefficient 1).`, `roots: ${R.map(M_).join(', ')}`, steps, `${pt(pAll)}`), enemy: 'cogmoon' };
    }
    return genRoots('rrt', tut);
  }

  // ================================================================ stage 54: three-variable systems
  const eqT = (a, b, c, d) => { const ts = []; [[a, X], [b, Y], [c, Z]].forEach(([k, v]) => { if (!k) return; ts.push({ neg: k < 0, s: (Math.abs(k) === 1 ? '' : Math.abs(k)) + v }); }); return (ts.length ? KT.sgnJoin(ts, true) : '0') + ' = ' + M_(d); };
  const SYS_CASES = ['elim', 'elim2', 'tri', 'nosol', 'many'];
  function genSys(cs, tut = isTutorial()) {
    const L = lvl(tut);
    cs = cs || pick(SYS_CASES);
    for (let tries = 0; tries < 400; tries++) {
      const M = [3, 4, 5, 6][L];
      const sol = [rand(-M, M), rand(-M, M), rand(-M, M)];
      if (cs === 'tri') {
        // upper triangular: back-substitution only
        const a = [1, nz(-3, 3), nz(-3, 3)], b = [0, 1, nz(-3, 3)], c3 = rand(1, 3);
        const d1 = a[0] * sol[0] + a[1] * sol[1] + a[2] * sol[2], d2 = sol[1] + b[2] * sol[2], d3 = c3 * sol[2];
        const top = `(1) ${eqT(a[0], a[1], a[2], d1)}<br>(2) ${eqT(0, 1, b[2], d2)}<br>(3) ${eqT(0, 0, c3, d3)}`;
        const steps = [
          st('sv12', `${Z} = ${M_(sol[2])}`, `${Z} = ${M_(sol[2])}`, { push: true, alts: [alt(`${Z} = ${M_(d3 * c3)}`, `Divide by ${c3}.`), alt(`${Z} = ${M_(-sol[2])}`, 'Check the sign.')].filter(x => c3 > 1 || !x.v.endsWith(M_(d3 * c3))), why: ['(3) has only z: solve it first.'], cap: '(3) has only z' }),
          st('bs12', `Into (2): ${Y} = ${M_(sol[1])}`, `${Y} = ${M_(sol[1])}, ${Z} = ${M_(sol[2])}`, { alts: [alt(`Into (2): ${Y} = ${M_(d2 + b[2] * sol[2])}`, `Move ${b[2] * sol[2] < 0 ? MINUS : ''}${Math.abs(b[2] * sol[2])} with the opposite sign.`), alt(`Into (1): ${Y} = ${M_(sol[1] + 1)}`, '(1) still has x in it: use (2), which only has y and z.')], why: ['Put z into (2).'], cap: 'Put z into (2)' }),
          st('bs12', `Into (1): ${X} = ${M_(sol[0])}`, `(${X}, ${Y}, ${Z}) = (${sol.map(M_).join(', ')})`, { alts: [alt(`Into (1): ${X} = ${M_(d1 + a[1] * sol[1] + a[2] * sol[2])}`, 'Move the known terms with the opposite sign.')], why: ['Put y and z into (1).'], cap: 'Put y and z into (1)' }),
        ];
        return { r12: S12('sy', 'sys3', 'sys', 'Solve from the bottom up.', top, steps, `(${X}, ${Y}, ${Z}) = (${sol.map(M_).join(', ')})`), enemy: 'tripod' };
      }
      // y has coefficient 1 in (1); eliminate y from (2) and (3) using (1)
      const e1 = [nz(-3, 3), 1, nz(-3, 3)], e2 = [nz(-3, 3), pick([1, -1]), nz(-3, 3)], e3 = [nz(-3, 3), pick(cs === 'elim2' ? [2, -2, 1] : [1, -1]), nz(-3, 3)];
      const d = e => e[0] * sol[0] + e[1] * sol[1] + e[2] * sol[2];
      let E3 = e3, D3 = d(e3);
      if (cs === 'nosol' || cs === 'many') { // (3) = (1) + (2) on the left; same or different number on the right
        E3 = [e1[0] + e2[0], e1[1] + e2[1], e1[2] + e2[2]]; if (E3[1] === 0) continue;
        D3 = d(e1) + d(e2) + (cs === 'nosol' ? nz(-5, 5) : 0);
      }
      const D1 = d(e1), D2 = d(e2);
      const s2 = e2[1], s3 = E3[1];
      const comb = (e, D, s) => [e[0] - s * e1[0], 0, e[2] - s * e1[2], D - s * D1];
      const r4 = comb(e2, D2, s2), r5 = comb(E3, D3, s3);
      if (!r4[0] || !r4[2] || !r5[0] || !r5[2]) continue;
      const opT = (k, s) => (s === 1 ? `(${k}) − (1)` : s === -1 ? `(${k}) + (1)` : s > 0 ? `(${k}) − ${s}·(1)` : `(${k}) + ${-s}·(1)`);
      const badOp = (k, s) => (s === 1 ? `(${k}) + (1)` : s === -1 ? `(${k}) − (1)` : `(${k}) − (1)`);
      const badComb = (e, D, s) => { const t = s === 1 ? -1 : s === -1 ? 1 : 1; return [e[0] - t * e1[0], e[1] - t * e1[1], e[2] - t * e1[2], D - t * D1]; };
      const b4 = badComb(e2, D2, s2), b5 = badComb(E3, D3, s3);
      const top = `(1) ${eqT(...e1, D1)}<br>(2) ${eqT(...e2, D2)}<br>(3) ${eqT(...E3, D3)}`;
      const v4 = `${opT(2, s2)}: ${eqT(r4[0], 0, r4[2], r4[3])}`, v5 = `${opT(3, s3)}: ${eqT(r5[0], 0, r5[2], r5[3])}`;
      const steps = [
        st('el12', v4, `(4) ${eqT(r4[0], 0, r4[2], r4[3])}`, { push: true, alts: [alt(`${badOp(2, s2)}: ${eqT(...b4)}`, 'That doesn\'t remove y: the y terms must cancel.'), alt(`${opT(2, s2)}: ${eqT(r4[0], 0, r4[2], r4[3] + 2)}`, 'Do the same to the numbers on the right.')], rule: [alt(`${opT(2, s2)}: ${eqT(r4[0], 0, -r4[2], r4[3])}`, 'Subtracting an equation subtracts every term: watch the signs of z.')], why: ['Remove y from (2) using (1).'], cap: 'The y terms cancel' }),
        st('el12', v5, `(5) ${eqT(r5[0], 0, r5[2], r5[3])}`, { push: true, alts: [alt(`${badOp(3, s3)}: ${eqT(...b5)}`, 'That doesn\'t remove y.'), alt(`${opT(3, s3)}: ${eqT(r5[0], 0, r5[2], r5[3] + 3)}`, 'Do the same to the numbers on the right.')], why: ['Remove y from (3) using (1) too, so (4) and (5) have only x and z.'], cap: 'Remove y again' }),
      ];
      if (cs === 'nosol' || cs === 'many') {
        const k = r4[3] - r5[3];
        const v = cs === 'nosol' ? `(4) − (5): 0 = ${M_(k)}, so no solution` : '(4) − (5): 0 = 0, so infinitely many solutions';
        if ((cs === 'nosol') !== (k !== 0)) continue;
        if (r4[0] !== r5[0] || r4[2] !== r5[2]) continue;
        steps.push(st('end12', v, cs === 'nosol' ? `0 = ${M_(k)}` : '0 = 0', { push: true, alts: [alt(cs === 'nosol' ? '(4) − (5): 0 = 0, so infinitely many solutions' : `(4) − (5): 0 = 1, so no solution`, cs === 'nosol' ? `The numbers differ: ${M_(r4[3])} − ${M_(r5[3])} = ${M_(k)}.` : 'Both sides cancel completely: 0 = 0.'), alt(`(4) − (5): ${Z} = 0`, 'Everything cancels: there\'s no z left.')], rule: [alt(cs === 'nosol' ? `(4) − (5): ${X} = ${M_(k)}` : `(4) − (5): ${X} = 0`, 'Everything on the left cancels. What is left is a statement about numbers.')], why: ['Look at what is left.'], cap: cs === 'nosol' ? 'A false statement: the planes share no point' : 'Always true: the planes share a whole line' }));
        return { r12: S12('sy', 'sys3', 'sys', 'Eliminate y first.', top, steps, cs === 'nosol' ? 'No solution' : 'Infinitely many solutions'), enemy: 'tripod' };
      }
      // 2×2 in x and z: a5·(4) − a4·(5) removes x
      const a4 = r4[0], a5 = r5[0];
      const zc = a5 * r4[2] - a4 * r5[2], zd = a5 * r4[3] - a4 * r5[3];
      if (!zc || zd % zc) continue;
      if (Math.abs(a4) > 6 || Math.abs(a5) > 6) continue;
      const m4 = a5, m5 = a4;
      const mT = (m, k) => (m === 1 ? `(${k})` : m === -1 ? `−(${k})` : `${m}·(${k})`);
      const v6 = `${mT(m4, 4)} − ${mT(m5, 5)}: ${eqT(0, 0, zc, zd)}`;
      steps.push(st('el12', v6, `${eqT(0, 0, zc, zd)}`, { push: true, alts: [alt(`${mT(m4, 4)} + ${mT(m5, 5)}: ${eqT(2 * a4 * a5, 0, a5 * r4[2] + a4 * r5[2], a5 * r4[3] + a4 * r5[3])}`, 'That doesn\'t remove x: the x terms must cancel.'), alt(`${mT(m4, 4)} − ${mT(m5, 5)}: ${eqT(0, 0, zc, zd + 1)}`, 'Multiply every term, then subtract every term.')], why: ['Remove x from (4) and (5).', `Multiply (4) by ${a5} and (5) by ${a4}, then subtract: the x terms cancel.`], cap: 'Now remove x' }));
      steps.push(st('sv12', `${Z} = ${M_(sol[2])}`, `${Z} = ${M_(sol[2])}`, { alts: [alt(`${Z} = ${M_(-sol[2])}`, 'Check the sign.'), alt(`${Z} = ${M_(zd)}`, `Divide by ${zc}.`)].filter(x => Math.abs(zc) !== 1 || !x.v.endsWith(M_(zd)) || zc !== 1), why: [`Divide by ${zc}.`], cap: `÷ ${M_(zc)}` }));
      steps.push(st('bs12', `Into (4): ${X} = ${M_(sol[0])}`, `${X} = ${M_(sol[0])}, ${Z} = ${M_(sol[2])}`, { alts: [alt(`Into (4): ${X} = ${M_(sol[0] + 1)}`, 'Move the z term, then divide.'), alt(`Into (4): ${X} = ${M_(-sol[0])}`, 'Check the sign.')], why: ['Put z into (4).'], cap: 'Put z into (4)' }));
      steps.push(st('bs12', `Into (1): ${Y} = ${M_(sol[1])}`, `(${X}, ${Y}, ${Z}) = (${sol.map(M_).join(', ')})`, { alts: [alt(`Into (1): ${Y} = ${M_(sol[1] - 1)}`, 'Move the x and z terms with the opposite sign.'), alt(`Into (1): ${Y} = ${M_(-sol[1])}`, 'Check the sign.')], why: ['Put x and z into (1).'], cap: 'Put x and z into (1)' }));
      return { r12: S12('sy', 'sys3', 'sys', 'Eliminate y first.', top, steps, `(${X}, ${Y}, ${Z}) = (${sol.map(M_).join(', ')})`), enemy: 'tripod' };
    }
    return genSys('tri', tut);
  }

  // ================================================================ stage 55: sequences and series
  const SEQ_CASES = ['arith', 'geom', 'which', 'asum', 'gsum', 'inf', 'sigma', 'recur'];
  const fmtN = v => (Number.isInteger(v) ? M_(v) : trimDec(+v.toFixed(4)));
  function genSeq(cs, tut = isTutorial()) {
    const L = lvl(tut);
    cs = cs || pick(SEQ_CASES);
    for (let tries = 0; tries < 200; tries++) {
      if (cs === 'arith' || cs === 'asum' || cs === 'sigma') {
        const a1 = rand(-9, 15), d = nz(-6, 8), n = rand(8, [15, 20, 30, 40][L]), an = a1 + (n - 1) * d;
        const terms = [0, 1, 2, 3].map(i => a1 + i * d).map(M_).join(', ') + ', …';
        if (cs === 'arith') {
          const steps = [
            st('d12', `d = ${M_(d)}`, `d = ${M_(d)}`, { alts: [alt(`d = ${M_(-d)}`, 'Later term minus earlier term.'), alt(`r = ${fmtN((a1 + d) / (a1 || 1))}`, 'The differences are all the same: it\'s arithmetic, with a common difference.')].filter(x => a1), why: ['Subtract one term from the next.'], cap: 'Subtract: the same difference each time' }),
            st('form12', `a${'<sub>n</sub>'} = ${M_(a1)} + (${Nv} − 1)(${M_(d)})`, `a<sub>n</sub> = ${M_(a1)} + (${Nv} − 1)(${M_(d)})`, { alts: [alt(`a<sub>n</sub> = ${M_(a1)} + ${Nv}(${M_(d)})`, `The first term already counts once, so add d (n − 1) times.`), alt(`a<sub>n</sub> = ${M_(a1)}(${M_(d)})${supH('n − 1')}`, 'That is geometric: arithmetic adds d.')], rule: [alt(`a<sub>n</sub> = ${M_(a1)} + ${Nv}(${M_(d)})`, 'aₙ = a₁ + (n − 1)d: from a₁ to aₙ there are n − 1 steps.')], why: ['aₙ = a₁ + (n − 1)d.'], cap: 'aₙ = a₁ + (n − 1)d' }),
            st('ev12', `a<sub>${n}</sub> = ${M_(an)}`, `a<sub>${n}</sub> = ${M_(an)}`, { alts: [alt(`a<sub>${n}</sub> = ${M_(an + d)}`, `That is ${n} steps from a₁: use ${n} − 1 = ${n - 1}.`), alt(`a<sub>${n}</sub> = ${M_(a1 * d * (n - 1))}`, 'Add (n − 1)d to a₁; don\'t multiply.')], why: [`${M_(a1)} + ${n - 1}(${M_(d)}).`], cap: `${M_(a1)} + ${n - 1} × ${M_(d)}` }),
          ];
          return { r12: S12('sq', 'seqser', 'term', `Find the ${n}th term.`, terms, steps, `a<sub>${n}</sub> = ${M_(an)}`), enemy: 'starling' };
        }
        const S = n * (a1 + an) / 2;
        const pre = [];
        let top = `Find the sum of the first ${n} terms.`, row0 = terms;
        if (cs === 'sigma') {
          const c = d, k0 = a1 - d;   // term k = c·k + k0
          const gen = ptext(P1(c, k0), true, 'k');
          top = 'Find the sum.'; row0 = `Σ<sub>k=1</sub><sup class="nonum">${n}</sup> (${gen})`;
          pre.push(st('d12', `a<sub>1</sub> = ${M_(a1)}, a<sub>${n}</sub> = ${M_(an)}, ${n} terms`, `${M_(a1)} + ${M_(a1 + d)} + … + ${M_(an)}`, { alts: [alt(`a<sub>1</sub> = ${M_(k0)}, a<sub>${n}</sub> = ${M_(an)}, ${n} terms`, 'k starts at 1: put k = 1 in for the first term.'), alt(`a<sub>1</sub> = ${M_(a1)}, a<sub>${n}</sub> = ${M_(an)}, ${n - 1} terms`, `k = 1 to ${n} is ${n} terms.`)], why: ['Put k = 1 and k = n in.'], cap: 'First term k = 1, last term k = ' + n }));
        } else pre.push(st('ev12', `a<sub>${n}</sub> = ${M_(an)}`, `a<sub>${n}</sub> = ${M_(an)}`, { alts: [alt(`a<sub>${n}</sub> = ${M_(an + d)}`, `Use n − 1 = ${n - 1} steps.`)], why: ['Find the last term first: aₙ = a₁ + (n − 1)d.'], cap: 'The last term first' }));
        const steps = [...pre,
          st('form12', `S<sub>${n}</sub> = ${frH(`${n}(${M_(a1)} + ${M_(an)})`, 2)}`, `S<sub>${n}</sub> = ${frH(`${n}(${M_(a1)} + ${M_(an)})`, 2)}`, { alts: [alt(`S<sub>${n}</sub> = ${n}(${M_(a1)} + ${M_(an)})`, 'Average of first and last, times n: divide by 2.'), alt(`S<sub>${n}</sub> = ${frH(`${M_(a1)} + ${M_(an)}`, 2)}`, 'That is only the average term: multiply by the number of terms.')], rule: [alt(`S<sub>${n}</sub> = ${n}(${M_(a1)} + ${M_(an)})`, 'Sₙ = n(a₁ + aₙ)/2: n terms times the average of the first and last.')], why: ['Sₙ = n(a₁ + aₙ)/2.'], cap: 'n × the average of the first and last' }),
          st('ev12', `S<sub>${n}</sub> = ${fmtN(S)}`, `S<sub>${n}</sub> = ${fmtN(S)}`, { alts: [alt(`S<sub>${n}</sub> = ${fmtN(2 * S)}`, 'Divide by 2.'), alt(`S<sub>${n}</sub> = ${fmtN(S + an)}`, 'Check the arithmetic.')], why: ['Work it out.'], cap: 'Work it out' }),
        ];
        return { r12: S12('sq', 'seqser', 'sum', top, row0, steps, `S<sub>${n}</sub> = ${fmtN(S)}`), enemy: 'starling' };
      }
      if (cs === 'geom' || cs === 'gsum') {
        const a1 = nz(-5, 6), r = pick(L >= 2 ? [2, 3, -2, -3, 4] : [2, 3, -2]), n = rand(5, [6, 7, 8, 9][L]), an = a1 * r ** (n - 1);
        const terms = [0, 1, 2, 3].map(i => a1 * r ** i).map(M_).join(', ') + ', …';
        if (cs === 'geom') {
          const steps = [
            st('d12', `r = ${M_(r)}`, `r = ${M_(r)}`, { alts: [alt(`d = ${M_(a1 * r - a1)}`, 'The differences change; the ratio stays the same: geometric.'), alt(`r = ${M_(-r)}`, 'Divide a term by the one before it, signs included.')], why: ['Divide a term by the one before.'], cap: 'Divide: the same ratio each time' }),
            st('form12', `a<sub>n</sub> = ${M_(a1)}(${M_(r)})${supH('n − 1')}`, `a<sub>n</sub> = ${M_(a1)}(${M_(r)})${supH('n − 1')}`, { alts: [alt(`a<sub>n</sub> = ${M_(a1)} + (${Nv} − 1)(${M_(r)})`, 'That is arithmetic: geometric multiplies by r.'), alt(`a<sub>n</sub> = (${M_(a1 * r)})${supH('n − 1')}`, 'Only r is raised to the power.')], rule: [alt(`a<sub>n</sub> = ${M_(a1)}(${M_(r)})${supH('n')}`, 'aₙ = a₁·rⁿ⁻¹: from a₁ to aₙ there are n − 1 multiplications.')], why: ['aₙ = a₁·rⁿ⁻¹.'], cap: 'aₙ = a₁·rⁿ⁻¹' }),
            st('ev12', `a<sub>${n}</sub> = ${M_(an)}`, `a<sub>${n}</sub> = ${M_(an)}`, { alts: [alt(`a<sub>${n}</sub> = ${M_(an * r)}`, `Use the power n − 1 = ${n - 1}.`), alt(`a<sub>${n}</sub> = ${M_(a1 * r * (n - 1))}`, 'r is raised to the power; it isn\'t multiplied by it.')], why: [`${M_(a1)} × (${M_(r)})${supT(n - 1)}.`], cap: `${M_(a1)} × (${M_(r)})${supT(n - 1)}` }),
          ];
          return { r12: S12('sq', 'seqser', 'term', `Find the ${n}th term.`, terms, steps, `a<sub>${n}</sub> = ${M_(an)}`), enemy: 'starling' };
        }
        const S = a1 * (1 - r ** n) / (1 - r);
        const steps = [
          st('d12', `r = ${M_(r)}`, `r = ${M_(r)}`, { alts: [alt(`d = ${M_(a1 * r - a1)}`, 'The ratio is constant: geometric.')], why: ['Divide a term by the one before.'], cap: 'The common ratio' }),
          st('form12', `S<sub>${n}</sub> = ${frH(`${M_(a1)}(1 − (${M_(r)})${supH(n)})`, `1 − (${M_(r)})`)}`, `S<sub>${n}</sub> = ${frH(`${M_(a1)}(1 − (${M_(r)})${supH(n)})`, `1 − (${M_(r)})`)}`, { alts: [alt(`S<sub>${n}</sub> = ${frH(`${n}(${M_(a1)} + ${M_(an)})`, 2)}`, 'That is the arithmetic sum.'), alt(`S<sub>${n}</sub> = ${frH(M_(a1), `1 − (${M_(r)})`)}`, 'That is the infinite sum, only for |r| < 1.')], rule: [alt(`S<sub>${n}</sub> = ${frH(`${M_(a1)}(1 − (${M_(r)})${supH(n - 1)})`, `1 − (${M_(r)})`)}`, 'Sₙ uses rⁿ: n terms.')], why: ['Sₙ = a₁(1 − rⁿ)/(1 − r).'], cap: 'Sₙ = a₁(1 − rⁿ)/(1 − r)' }),
          st('ev12', `S<sub>${n}</sub> = ${fmtN(S)}`, `S<sub>${n}</sub> = ${fmtN(S)}`, { alts: [alt(`S<sub>${n}</sub> = ${fmtN(a1 * (1 - r ** (n - 1)) / (1 - r))}`, `That's ${n - 1} terms.`), alt(`S<sub>${n}</sub> = ${fmtN(-S)}`, 'Watch the signs: 1 − r on the bottom.')], why: ['Work it out.'], cap: 'Work it out' }),
        ];
        return { r12: S12('sq', 'seqser', 'sum', `Find the sum of the first ${n} terms.`, terms, steps, `S<sub>${n}</sub> = ${fmtN(S)}`), enemy: 'starling' };
      }
      if (cs === 'inf') {
        const div = chance(0.3);
        const a1 = pick([8, 9, 12, 16, 18, 24, 27, 32, 36, 48]), [rn, rd] = div ? pick([[3, 2], [5, 4], [-3, 2], [2, 1]]) : pick([[1, 2], [1, 3], [-1, 2], [2, 3], [1, 4], [-1, 3], [3, 4]]);
        if (!div && ((a1 * rn) % rd || (a1 * rn * rn) % (rd * rd))) continue;
        if (div && ((a1 * rn) % rd)) continue;
        const r = F(rn, rd), t2 = a1 * rn / rd, t3 = div ? a1 * rn * rn / (rd * rd) : a1 * rn * rn / (rd * rd);
        if (!Number.isInteger(t3)) continue;
        const terms = `${a1} + ${M_(t2).replace(MINUS, '(' + MINUS) + (t2 < 0 ? ')' : '')} + ${M_(t3)} + …`;
        const S = fDiv(F(a1), fAdd(F(1), fNeg(r)));
        const steps = [
          st('d12', `r = ${nh(r)}`, `r = ${nh(r)}`, { alts: [alt(`r = ${nh(fDiv(F(1), r))}`, 'Divide a term by the one before it, not the other way.'), alt(`r = ${M_(t2 - a1)}`, 'Divide, don\'t subtract.')], why: ['Divide a term by the one before.'], cap: 'The common ratio' }),
          div
            ? st('end12', `|r| ≥ 1: no sum (it diverges)`, '|r| ≥ 1: the terms don\'t shrink', { alts: [alt(`S = ${nh(S)}`, `a₁/(1 − r) only works when |r| < 1. Here |r| = ${nh(F(Math.abs(rn), rd))}, so the terms never shrink.`)], rule: [alt(`S = ${nh(S)}`, 'The infinite sum formula needs |r| < 1; otherwise the sum grows without end.')], why: ['Check |r| first.'], cap: '|r| ≥ 1: the terms never shrink' })
            : st('form12', `S = ${frH(a1, `1 − (${nh(r)})`)}`, `S = ${frH(a1, `1 − (${nh(r)})`)}`, { alts: [alt(`S = ${frH(a1, `1 + (${nh(r)})`)}`, 'S = a₁/(1 − r).'), alt('No sum: it goes on forever', `|r| = ${nh(F(Math.abs(rn), rd))} < 1: the terms shrink fast enough to add up to a number.`)], rule: [alt('No sum: it goes on forever', 'An infinite geometric series with |r| < 1 does have a sum: a₁/(1 − r).')], why: ['S = a₁/(1 − r) when |r| < 1.'], cap: '|r| < 1: S = a₁/(1 − r)' }),
        ];
        if (!div) steps.push(st('ev12', `S = ${nh(S)}`, `S = ${nh(S)}`, { alts: [alt(`S = ${nh(fDiv(F(a1), fAdd(F(1), r)))}`, '1 − r on the bottom.'), alt(`S = ${nh(fMul(F(a1), fAdd(F(1), fNeg(r))))}`, 'Divide by 1 − r.')], why: ['Work it out.'], cap: 'Work it out' }));
        return { r12: S12('sq', 'seqser', 'inf', 'Find the sum, if it exists.', terms, steps, div ? 'No sum: |r| ≥ 1' : `S = ${nh(S)}`), enemy: 'starling' };
      }
      if (cs === 'which') {
        const ar = chance(0.5), a1 = rand(1, 9), k = ar ? nz(-5, 7) : pick([2, 3, -2]);
        const ts = [0, 1, 2, 3].map(i => (ar ? a1 + i * k : a1 * k ** i));
        const nxt = ar ? a1 + 4 * k : a1 * k ** 4;
        const steps = [
          st('kind12', ar ? `Arithmetic: d = ${M_(k)}` : `Geometric: r = ${M_(k)}`, ar ? `Arithmetic: d = ${M_(k)}` : `Geometric: r = ${M_(k)}`, { alts: [alt(ar ? `Geometric: r = ${fmtN(ts[1] / ts[0])}` : `Arithmetic: d = ${M_(ts[1] - ts[0])}`, ar ? 'The ratios change, but the differences stay the same.' : 'The differences change, but the ratios stay the same.')], why: ['Check the differences and the ratios.'], cap: ar ? 'The same difference each time' : 'The same ratio each time', note: false }),
          st('ev12', `Next term: ${M_(nxt)}`, `${ts.map(M_).join(', ')}, ${M_(nxt)}`, { alts: [alt(`Next term: ${M_(ar ? ts[3] * 2 : ts[3] + (ts[3] - ts[2]))}`, 'Use the pattern you found.'), alt(`Next term: ${M_(ar ? ts[3] - k : ts[3] / k)}`, ar ? 'Add d.' : 'Multiply by r.')], why: [ar ? 'Add d.' : 'Multiply by r.'], cap: ar ? `+ ${M_(k)}` : `× ${M_(k)}` }),
        ];
        return { r12: S12('sq', 'seqser', 'term', 'Arithmetic or geometric? Find the next term.', ts.map(M_).join(', ') + ', …', steps, `${ar ? 'Arithmetic' : 'Geometric'}, next ${M_(nxt)}`), enemy: 'starling' };
      }
      // recur
      const a1 = rand(-3, 6), m = pick([2, 3, -1, 2]), c = nz(-4, 4);
      const seq = [a1]; for (let i = 1; i < 4; i++) seq.push(m * seq[i - 1] + c);
      if (seq.some(v => Math.abs(v) > 200)) continue;
      const rule = `a<sub>n</sub> = ${m === 1 ? '' : m === -1 ? MINUS : m}a<sub>n−1</sub>${c < 0 ? ` ${MINUS} ${-c}` : ` + ${c}`}`;
      const steps = [1, 2, 3].map(i => st('rec12', `a<sub>${i + 1}</sub> = ${M_(seq[i])}`, `${seq.slice(0, i + 1).map(M_).join(', ')}`, { alts: [alt(`a<sub>${i + 1}</sub> = ${M_(m * seq[i - 1] - c)}`, 'Check the sign of the number added.'), alt(`a<sub>${i + 1}</sub> = ${M_(m * (seq[i - 1] + c))}`, `Multiply first, then ${c < 0 ? 'subtract' : 'add'}.`), alt(`a<sub>${i + 1}</sub> = ${M_(seq[i - 1] + c)}`, `Multiply by ${m} first.`)], why: [`Use the term before: ${m} × ${M_(seq[i - 1])} ${c < 0 ? MINUS : '+'} ${Math.abs(c)}.`], cap: `${m} × ${M_(seq[i - 1])} ${c < 0 ? MINUS : '+'} ${Math.abs(c)}` }));
      return { r12: S12('sq', 'seqser', 'rec', `a<sub>1</sub> = ${M_(a1)}, ${rule}. Find a<sub>4</sub>.`, `${M_(a1)}`, steps, `a<sub>4</sub> = ${M_(seq[3])}`), enemy: 'starling' };
    }
    return genSeq('arith', tut);
  }

  // ================================================================ stage 56: conics
  const sq = (v, h) => (h === 0 ? pw(v, 2) : `(${ptext(P1(1, -h), true, v.replace(/<[^>]+>/g, ''))})${supH(2)}`);
  const sqT = (v, h) => sq(XV(v), h);
  const CON_CASES = ['circle', 'circstd', 'ellipse', 'parabola', 'hyper', 'classify'];
  function genCon(cs, tut = isTutorial()) {
    const L = lvl(tut);
    cs = cs || pick(CON_CASES);
    for (let tries = 0; tries < 200; tries++) {
      if (cs === 'circle' || cs === 'circstd') {
        const h = rand(-6, 6), k = rand(-6, 6), r = rand(2, [5, 6, 8, 9][L]);
        const std = `${sqT('x', h)} + ${sqT('y', k)} = ${r * r}`;
        const read = `Center (${M_(h)}, ${M_(k)}), radius ${r}`;
        const readAlts = [alt(`Center (${M_(-h)}, ${M_(-k)}), radius ${r}`, `(x − h)² means the center is at x = h: (x ${h < 0 ? '+' : MINUS} ${Math.abs(h)}) gives h = ${M_(h)}.`), alt(`Center (${M_(h)}, ${M_(k)}), radius ${r * r}`, `The right side is r²: r = √${r * r} = ${r}.`), alt(`Center (${M_(-h)}, ${M_(-k)}), radius ${r * r}`, `Both are off: the center's signs are the opposite of the brackets', and the radius is √${r * r} = ${r}.`), ...(h !== k ? [alt(`Center (${M_(k)}, ${M_(h)}), radius ${r}`, 'The x bracket gives the x of the center; the y bracket gives the y.')] : [])];
        const readRule = [alt(`Center (${M_(-h)}, ${M_(-k)}), radius ${r}`, 'The signs inside the brackets are the opposite of the center\'s coordinates.')];
        const gr = { t: 'circle', h, k, r };
        if (cs === 'circstd') {
          if (h === 0 || k === 0) continue;
          const steps = [st('read12', read, read, { alts: readAlts, rule: readRule, why: ['(x − h)² + (y − k)² = r².'], cap: 'Read the center and the radius', gr })];
          return { r12: S12('cn', 'conics', 'circ', 'Find the center and radius.', std, steps, read), enemy: 'cometling' };
        }
        const D = -2 * h, E = -2 * k, Fc = h * h + k * k - r * r;
        if (!D || !E) continue;
        const gen = `${pw(X, 2)} + ${pw(Y, 2)}${D < 0 ? ` ${MINUS} ${-D}` : ` + ${D}`}${X}${E < 0 ? ` ${MINUS} ${-E}` : ` + ${E}`}${Y}${Fc ? (Fc < 0 ? ` ${MINUS} ${-Fc}` : ` + ${Fc}`) : ''} = 0`;
        const gx = `(${pw(X, 2)}${D < 0 ? ` ${MINUS} ${-D}` : ` + ${D}`}${X})`, gy = `(${pw(Y, 2)}${E < 0 ? ` ${MINUS} ${-E}` : ` + ${E}`}${Y})`;
        const steps = [
          st('grpc12', `${gx} + ${gy} = ${M_(-Fc)}`, `${gx} + ${gy} = ${M_(-Fc)}`, { alts: [alt(`${gx} + ${gy} = ${M_(Fc)}`, 'Moving the number to the other side changes its sign.')], why: ['Group x with x, y with y, and move the number over.'], cap: 'Group, and move the number over' }),
          st('cs12', `+ ${h * h} for x: ${sqT('x', h)}`, `${sqT('x', h)} + ${gy} = ${M_(-Fc + h * h)}`, { alts: [alt(`+ ${D * D} for x: ${sqT('x', h)}`, `Half of ${M_(D)} is ${M_(-h)}, and (${M_(-h)})² = ${h * h}. Don't square ${M_(D)} itself.`), alt(`+ ${h * h} for x: ${sqT('x', -h)}`, `x² ${D < 0 ? MINUS : '+'} ${Math.abs(D)}x + ${h * h} = (x ${h > 0 ? MINUS : '+'} ${Math.abs(h)})².`)], rule: [alt(`+ ${Math.abs(D / 2)} for x: ${sqT('x', h)}`, `Add (half the coefficient)²: (${M_(D)}/2)² = ${h * h}, on both sides.`)], why: ['Add (half the x coefficient)² to both sides.'], cap: `(${M_(D)} ÷ 2)² = ${h * h}, added to both sides` }),
          st('cs12', `+ ${k * k} for y: ${sqT('y', k)}`, std, { alts: [alt(`+ ${E * E} for y: ${sqT('y', k)}`, `Half of ${M_(E)} is ${M_(-k)}; square that: ${k * k}.`), alt(`+ ${k * k} for y: ${sqT('y', -k)}`, 'Check the sign inside the bracket.')], why: ['Now the same for y.'], cap: `(${M_(E)} ÷ 2)² = ${k * k}, added to both sides` }),
          st('read12', read, read, { alts: readAlts, rule: readRule, why: ['(x − h)² + (y − k)² = r².'], cap: 'Read the center and the radius', gr }),
        ];
        return { r12: S12('cn', 'conics', 'circ', 'Find the center and radius.', gen, steps, read), enemy: 'cometling' };
      }
      if (cs === 'ellipse' || cs === 'hyper') {
        let a = rand(2, [4, 5, 6, 7][L]), b = rand(2, [4, 5, 6, 7][L]);
        if (a === b) continue;
        const hyp = cs === 'hyper';
        if (!hyp && a < b) [a, b] = [b, a];
        const A2 = a * a, B2 = b * b, R = A2 * B2;
        const fromGen = L >= 1 && chance(0.6);
        const std = `${frH(pw(X, 2), A2)} ${hyp ? MINUS : '+'} ${frH(pw(Y, 2), B2)} = 1`;
        const gen = `${B2}${pw(X, 2)} ${hyp ? MINUS : '+'} ${A2}${pw(Y, 2)} = ${R}`;
        const steps = [];
        if (fromGen) steps.push(st('dv12', `÷ ${R}: ${std}`, std, { alts: [alt(`÷ ${R}: ${frH(pw(X, 2), B2)} ${hyp ? MINUS : '+'} ${frH(pw(Y, 2), A2)} = 1`, `${B2}x² ÷ ${R} = x²/${A2}: the numbers swap places.`)], why: [`Divide everything by ${R} so the right side is 1.`], cap: `÷ ${R}: the right side becomes 1` }));
        const read = hyp ? `Vertices (±${a}, 0), asymptotes ${Y} = ±${nh(F(b, a))}${X}` : `Vertices (±${a}, 0), co-vertices (0, ±${b})`;
        const gr = { t: hyp ? 'hyper' : 'ellipse', a, b };
        steps.push(st('read12', read, read, { alts: hyp ? [alt(`Vertices (0, ±${a}), asymptotes ${Y} = ±${nh(F(b, a))}${X}`, 'The x² term is the positive one, so the vertices are on the x-axis.'), alt(`Vertices (±${a}, 0), asymptotes ${Y} = ±${nh(F(a, b))}${X}`, `The slopes are ±b/a = ±${b}/${a}.`)] : [alt(`Vertices (±${A2}, 0), co-vertices (0, ±${B2})`, `The denominators are a² and b²: a = ${a}, b = ${b}.`), alt(`Vertices (±${b}, 0), co-vertices (0, ±${a})`, `x² is over ${A2}, so x reaches ±${a}.`)], rule: hyp ? [alt(`Vertices (±${a}, 0), asymptotes ${Y} = ±${nh(F(a, b))}${X}`, 'The asymptote slopes are ±b/a: rise over run, b over a.')] : [alt(`Vertices (±${A2}, 0), co-vertices (0, ±${B2})`, 'Take square roots of the denominators.')], why: [hyp ? 'x²/a² − y²/b² = 1: vertices (±a, 0), asymptotes y = ±(b/a)x.' : 'x²/a² + y²/b² = 1: x reaches ±a, y reaches ±b.'], cap: 'Read it off', gr }));
        return { r12: S12('cn', 'conics', hyp ? 'hyp' : 'ell', hyp ? 'Find the vertices and asymptotes.' : 'Find the vertices and co-vertices.', fromGen ? gen : std, steps, read), enemy: 'cometling' };
      }
      if (cs === 'parabola') {
        const h = nz(-5, 5), k = rand(-9, 9), b = -2 * h, c = h * h + k;
        const gen = `${Y} = ${pt([F(c), F(b), F(1)])}`;
        const vf = `${Y} = ${sqT('x', h)}${k < 0 ? ` ${MINUS} ${-k}` : k ? ` + ${k}` : ''}`;
        const steps = [
          st('cs12', `+ ${h * h} − ${h * h}: ${Y} = (${pt([F(h * h), F(b), F(1)])}) ${M_(c - h * h) === '0' ? '' : (c - h * h < 0 ? MINUS + ' ' + (h * h - c) : '+ ' + (c - h * h))}`, vf, { alts: [alt(`+ ${b * b} − ${b * b}: ${Y} = (${pt([F(b * b), F(b), F(1)])}) ${c - b * b < 0 ? MINUS + ' ' + (b * b - c) : '+ ' + (c - b * b)}`, `Half of ${M_(b)} is ${M_(-h)}; square that: ${h * h}.`)], why: ['Complete the square: add and take away (half the coefficient)².'], cap: `(${M_(b)} ÷ 2)² = ${h * h}: add it and take it away` }),
          st('read12', `Vertex (${M_(h)}, ${M_(k)})`, `Vertex (${M_(h)}, ${M_(k)})`, { alts: [alt(`Vertex (${M_(-h)}, ${M_(k)})`, `(x − h)²: the vertex is at x = h = ${M_(h)}.`), alt(`Vertex (${M_(h)}, ${M_(-k)})`, 'The number added at the end is k as it is.')], rule: [alt(`Vertex (${M_(-h)}, ${M_(k)})`, 'In y = (x − h)² + k the sign inside the bracket is the opposite of h.')], why: ['y = (x − h)² + k: vertex (h, k).'], cap: 'Read the vertex', gr: { t: 'para', h, k } }),
        ];
        return { r12: S12('cn', 'conics', 'para', 'Write in vertex form and find the vertex.', gen, steps, `Vertex (${M_(h)}, ${M_(k)})`), enemy: 'cometling' };
      }
      // classify
      const kind = pick(['circle', 'ellipse', 'hyperbola', 'parabola']);
      const a = rand(1, 9), c = kind === 'circle' ? a : kind === 'ellipse' ? (() => { let v; do v = rand(1, 9); while (v === a); return v; })() : kind === 'hyperbola' ? -rand(1, 9) : 0;
      const D = nz(-8, 8), E = nz(-8, 8), Fc = nz(-20, 20);
      const t = [`${a === 1 ? '' : a}${pw(X, 2)}`];
      if (c) t.push(`${c < 0 ? ` ${MINUS} ` : ' + '}${Math.abs(c) === 1 ? '' : Math.abs(c)}${pw(Y, 2)}`);
      t.push(`${D < 0 ? ` ${MINUS} ` : ' + '}${Math.abs(D) === 1 ? '' : Math.abs(D)}${X}`, `${E < 0 ? ` ${MINUS} ` : ' + '}${Math.abs(E) === 1 ? '' : Math.abs(E)}${Y}`, `${Fc < 0 ? ` ${MINUS} ` : ' + '}${Math.abs(Fc)}`);
      const eq = t.join('') + ' = 0';
      const why = { circle: 'x² and y² have the same coefficient', ellipse: 'x² and y² have different coefficients with the same sign', hyperbola: 'x² and y² have opposite signs', parabola: 'only one of x² and y² appears' };
      const names = ['circle', 'ellipse', 'hyperbola', 'parabola'].filter(n => n !== kind);
      const steps = [st('cls12', `${kind[0].toUpperCase() + kind.slice(1)}: ${why[kind]}`, `${kind[0].toUpperCase() + kind.slice(1)}`, { alts: names.map(n => alt(`${n[0].toUpperCase() + n.slice(1)}: ${why[n]}`, `Here ${why[kind]}.`)), why: ['Compare the x² and y² terms.'], cap: why[kind] })];
      return { r12: S12('cn', 'conics', 'cls', 'Which conic is it?', eq, steps, kind[0].toUpperCase() + kind.slice(1)), enemy: 'cometling' };
    }
    return genCon('circstd', tut);
  }

  // ================================================================ graph (conics)
  function graph(e) {
    const g = e.gr; if (!g) return;
    const ring = (fx, fy, n = 160) => Array.from({ length: n + 1 }, (_, i) => { const t = 2 * Math.PI * i / n; return [fx(t), fy(t)]; });
    let win, curves;
    if (g.t === 'circle') { win = KT.square(g.h, g.k, g.r + 1.5); curves = [{ pts: ring(t => g.h + g.r * Math.cos(t), t => g.k + g.r * Math.sin(t)), key: 'c' }]; }
    else if (g.t === 'ellipse') { win = KT.square(0, 0, Math.max(g.a, g.b) + 1.5); curves = [{ pts: ring(t => g.a * Math.cos(t), t => g.b * Math.sin(t)), key: 'e' }]; }
    else if (g.t === 'hyper') {
      const R = Math.max(g.a, g.b) * 2 + 1; win = KT.square(0, 0, R);
      const br = s => Array.from({ length: 81 }, (_, i) => { const u = -2.5 + 5 * i / 80; return [s * g.a * Math.cosh(u), g.b * Math.sinh(u)]; });
      curves = [{ pts: br(1), key: 'h1' }, { pts: br(-1), key: 'h2' }, { f: x => g.b / g.a * x, cls: 'mir9', key: 'as1' }, { f: x => -g.b / g.a * x, cls: 'mir9', key: 'as2' }];
    } else { win = KT.square(g.h, g.k + 3, 6); curves = [{ f: x => (x - g.h) ** 2 + g.k, key: 'p' }]; }
    drawCurves({ win, qid: 'cn' + e.qid, curves });
  }

  const PR = {
    roots: ['Find every root.', 'Solve.', 'Find all the zeros.'],
    div: ['Divide.', 'Use synthetic division.', 'Find the quotient and remainder.'],
    rem: ['Find the remainder.', 'Use the remainder theorem.', 'What is the remainder?'],
    build: ['Build the polynomial.', 'Write the polynomial.', 'Multiply out the factors.'],
    sys: ['Solve the system.', 'Find x, y and z.', 'Solve by elimination.'],
    term: ['Find the term.', 'Find the nth term.', 'Use the formula.'],
    sum: ['Find the sum.', 'Add up the series.', 'Use the sum formula.'],
    inf: ['Find the sum, if it exists.', 'Does it have a sum?', 'Sum to infinity.'],
    rec: ['Use the rule.', 'Find the terms one by one.', 'Work out each term.'],
    circ: ['Find the center and radius.', 'Write it in standard form.', 'Read the circle.'],
    ell: ['Read the ellipse.', 'Find the vertices.', 'Standard form, then read it.'],
    hyp: ['Read the hyperbola.', 'Find the vertices and asymptotes.', 'Standard form, then read it.'],
    para: ['Find the vertex.', 'Complete the square.', 'Write in vertex form.'],
    cls: ['Classify the conic.', 'Which conic?', 'Name the curve.'],
  };
  const GENS = { polyroots: genRoots, sys3: genSys, seqser: genSeq, conics: genCon };
  const HARD = { polyroots: ['rrt', 'biquad', 'group'], sys3: ['elim', 'elim2', 'nosol'], seqser: ['gsum', 'inf', 'sigma'], conics: ['circle', 'hyper', 'ellipse'] };
  const bossLast = mine => (mine.includes('conics') ? genCon('circle') : mine.includes('seqser') ? genSeq('gsum') : mine.includes('sys3') ? genSys('elim') : genRoots('rrt'));

  const spec = {
    act: 12, sk: 'k12', key: 'r12', tag: 'a12', ...SC.spec, graph, PR, HOME: {}, gens: GENS, hard: HARD, elite: 'armillary', boss: 'grandorrery', bossLast,
    skills: [
      { id: 'polyroots', stage: 53, act: 12, name: 'Polynomial roots', cases: ROOT_CASES, gen: cycled('polyroots', c => genRoots(c)),
        title: 'Stage 53: Roots of polynomials',
        intro: 'A rational root of a polynomial (leading coefficient 1) divides the constant term. Test candidates: r is a root when f(r) = 0, and then (x − r) is a factor. Divide it out with synthetic division and factor what\'s left. The remainder of f(x) ÷ (x − r) is f(r). Some polynomials factor by grouping or by letting u = x².',
        example: 'x³ − 2x² − 5x + 6 = 0<br>Try 1: f(1) = 0 → (x − 1)(x² − x − 6)<br>(x − 1)(x − 3)(x + 2) → x = −2, 1, 3',
        tutorial: [() => genRoots('build', true), () => genRoots('rrt', true)] },
      { id: 'sys3', stage: 54, act: 12, name: 'Three-variable systems', cases: SYS_CASES, gen: cycled('sys3', c => genSys(c)),
        title: 'Stage 54: Systems in three variables',
        intro: 'Use one equation to eliminate the same variable from the other two. That leaves two equations in two variables: eliminate again, solve, then back-substitute. If everything cancels to a false statement (0 = 3) there is no solution; if it cancels to 0 = 0 there are infinitely many.',
        example: 'Remove y with (2) − (1) and (3) − (1) → two equations in x, z → solve → back-substitute',
        tutorial: [() => genSys('tri', true), () => genSys('elim', true)] },
      { id: 'seqser', stage: 55, act: 12, name: 'Sequences and series', cases: SEQ_CASES, gen: cycled('seqser', c => genSeq(c)),
        title: 'Stage 55: Sequences and series',
        intro: 'Arithmetic: add d each time, aₙ = a₁ + (n − 1)d, Sₙ = n(a₁ + aₙ)/2. Geometric: multiply by r, aₙ = a₁·rⁿ⁻¹, Sₙ = a₁(1 − rⁿ)/(1 − r). An infinite geometric series adds up to a₁/(1 − r) only when |r| < 1. Σ notation lists the terms to add; a recursive rule builds each term from the one before.',
        example: '3, 7, 11, …: d = 4, a₂₀ = 3 + 19·4 = 79',
        tutorial: [() => genSeq('arith', true), () => genSeq('geom', true)] },
      { id: 'conics', stage: 56, act: 12, name: 'Conics', cases: CON_CASES, gen: cycled('conics', c => genCon(c)),
        title: 'Stage 56: Conic sections',
        intro: 'Circle: (x − h)² + (y − k)² = r², center (h, k), radius r. Get there by completing the square in x and in y. Ellipse: x²/a² + y²/b² = 1. Hyperbola: x²/a² − y²/b² = 1, asymptotes y = ±(b/a)x. Parabola: y = (x − h)² + k, vertex (h, k). Classify by the x² and y² terms: same coefficient, circle; same sign, ellipse; opposite signs, hyperbola; only one, parabola.',
        example: 'x² + y² − 6x + 4y − 3 = 0<br>(x − 3)² + (y + 2)² = 16 → center (3, −2), r = 4',
        tutorial: [() => genCon('circstd', true), () => genCon('circle', true)] },
    ],
    enemies: {
      cogmoon:   { name: 'Cogmoon',   rank: 'Normal', color: '#b8c0ff', size: 84 },
      tripod:    { name: 'Tripod',    rank: 'Normal', color: '#ffd6a5', size: 84 },
      starling:  { name: 'Starling',  rank: 'Normal', color: '#fdffb6', size: 84 },
      cometling: { name: 'Cometling', rank: 'Normal', color: '#9bf6ff', size: 84 },
      armillary: { name: 'The Armillary', rank: 'Elite', color: '#bdb2ff', size: 100, horns: true },
      grandorrery: { name: 'The Grand Orrery', rank: 'Boss', color: '#ffc6ff', size: 120, crown: true },
    },
    actInfo: { name: 'The Orrery', sub: 'Polynomials, systems, series and conics', boss: 'The Grand Orrery', firstSkill: 'polyroots',
      blurb: 'At the top of the Library, the Orrery turns every orbit at once. Find every root, solve three equations together, add up endless series, and trace the conics. Defeat The Grand Orrery.',
      cleared: () => 'The Grand Orrery stops, every orbit in its place. You have mastered all of algebra. Run any act again to keep your skills sharp.' },
    icons: {
      cand12: { name: 'List the possible rational roots', svg: svgI('<path d="M5 6h3M5 12h3M5 18h3"/><path d="M11 6h8M11 12h8M11 18h8" stroke-width="1.6"/>') },
      test12: { name: 'Test a root (f(r) = 0)', svg: svgI('<path d="M4 12h16"/><circle cx="12" cy="12" r="3.5"/>') },
      syn12:  { name: 'Synthetic division', svg: svgI('<path d="M6 4v16M6 15h14"/><path d="M10 9h8" stroke-width="1.8"/>') },
      calc12: { name: 'Work it out', svg: svgI('<rect x="5" y="3" width="14" height="18" rx="2"/><path d="M8 7h8M8 12h2M14 12h2M8 16h2M14 16h2"/>') },
      grp12:  { name: 'Group terms', svg: svgI('<path d="M7 5c-3 3-3 11 0 14M17 5c3 3 3 11 0 14"/><path d="M10 12h4"/>') },
      sub12:  { name: 'Substitute', svg: svgI('<path d="M4 8h12l-3-3M20 16H8l3 3"/>') },
      mul12:  { name: 'Multiply out', svg: svgI('<path d="M6 6l12 12M18 6L6 18"/>') },
      el12:   { name: 'Eliminate a variable', svg: svgI('<path d="M4 8h16M4 16h16"/><path d="M9 4l6 16" stroke-width="2"/>') },
      sv12:   { name: 'Solve for the variable', svg: svgI('<path d="M5 5l6 6M11 5l-6 6"/><path d="M14 16h6M14 20h6"/>') },
      bs12:   { name: 'Back-substitute', svg: svgI('<path d="M19 6v6H6M10 8l-4 4 4 4"/>') },
      kind12: { name: 'Classify', svg: svgI('<rect x="4" y="4" width="7" height="7" rx="1"/><circle cx="16.5" cy="16.5" r="3.5"/>') },
      d12:    { name: 'Common difference or ratio', svg: svgI('<path d="M4 18l5-5 4 3 7-8"/>') },
      form12: { name: 'Write the formula', svg: svgI('<path d="M5 19l10-14 4 4L9 23"/><path d="M4 20h7" stroke-width="1.6"/>') },
      rec12:  { name: 'Next term from the one before', svg: svgI('<path d="M4 12h12M12 7l5 5-5 5"/><circle cx="4" cy="12" r="1.5"/>') },
      cs12:   { name: 'Complete the square', svg: svgI('<rect x="4" y="4" width="16" height="16" rx="1"/><path d="M12 4v16M4 12h16" stroke-dasharray="2 2"/>') },
      read12: { name: 'Read it off', svg: svgI('<circle cx="12" cy="12" r="7"/><circle cx="12" cy="12" r="1.5"/><path d="M12 12h7"/>') },
    },
    css: '',
  };
  const A = KT.makeAct(spec);
  SC.bind(A);
  KT.install(spec, A);
})();
