// =====================================================================
//  Act 11: The Hourglass Vault (exponentials and logarithms)
// =====================================================================
// Stage 48  Growth and decay        P = 2000(1.05)ᵗ, half-life, doubling, compound and continuous interest
// Stage 49  Same-base equations     2ˣ⁺¹ = 32, 4ˣ = 8ˣ⁻¹, 9ˣ = 1/27, 25ˣ = √5, 2^(x² − x) = 4
// Stage 50  Logarithms              log₂ 8 = 3 ⇔ 2³ = 8, evaluate log₃ 81, solve log₄ x = 3, log_x 49 = 2
// Stage 51  Log properties          expand log₂(8x), log(x³y/z); condense 2 log x + log y; change of base
// Stage 52  Solving with logs       3ˣ = 20, 5·2ˣ = 40, e²ˣ = 7, log₂(x + 3) = 4, log x + log(x − 3) = 1
//
// Every problem is scripted: its generator works out each step and the classic mistakes for it, and the
// player picks the right card at each step (kit9.js `scripted`). Log equations end with a Check card: a log
// of 0 or a negative number is undefined, so an answer that makes one is rejected.
'use strict';
(function () {
  const KT = window.KIT9;
  if (!KT || !KT.scripted) return;
  const { P, FN, chance, qid, isTutorial, lvl, supH, supT, XV, numH, frH, ptext, P1, pmul, fv, svgI, drawCurves, fNeg, fDiv, fEq } = KT;
  const X = XV(), Y = XV('y'), Z = XV('z');
  const LG = b => (b === 10 ? 'log' : b === 'e' ? 'ln' : `log<sub class="nonum">${b}</sub>`);
  const pw = (b, e) => `${b}${supH(e)}`;
  const M_ = n => (n < 0 ? MINUS + Math.abs(n) : String(n));
  const trimDec = v => { const s = String(+(+v).toFixed(6)); return s.startsWith('-') ? MINUS + s.slice(1) : s; };
  const D = (v, dp = 2) => { const s = (Math.round(v * 10 ** dp) / 10 ** dp).toFixed(dp); return s.startsWith('-') ? MINUS + s.slice(1) : s; };
  const money = v => '$' + D(v, 2);
  const lin = (a, c) => ptext(P1(a, c), true);
  const xm = r => lin(1, -r);                         // x − r
  const sgnT = (c, html = true) => (c < 0 ? ` ${MINUS} ${Math.abs(c)}` : ` + ${c}`);
  const alt = (v, why, long, op) => ({ v, why, long, op });
  const st = (op, v, row, o = {}) => ({ op, v, row, ...o });
  const nz = (a, b) => nonZero(a, b);

  // ================================================================ the cards
  const OPS = {
    mdl11:  { kind: 'Choose the model', text: 'Start × (growth factor) to the power of time', icon: 'mdl11' },
    plug11: { kind: 'Plug in', text: 'Put the numbers into the model', icon: 'plug9' },
    ev11:   { kind: 'Work it out', text: 'Work out the value', icon: 'calc11', fx: 'spin11' },
    cls11:  { kind: 'Growth or decay', text: 'Read the base: more than 1 grows, less than 1 decays', icon: 'mdl11' },
    rate11: { kind: 'Read the rate', text: 'The percent change each step', icon: 'pct11' },
    rw11:   { kind: 'Rewrite as a power', text: 'Write the number as a power of the base', icon: 'pow11', part: true, fx: 'spin11' },
    pr11:   { kind: 'Power rule', text: 'A power of a power multiplies the exponents', icon: 'pr11' },
    mt11:   { kind: 'Match the exponents', text: 'Same base on both sides, so the exponents are equal', icon: 'mt11' },
    sv11:   { kind: 'Solve for x', text: 'Get x alone', icon: 'sv11' },
    mv11:   { kind: 'Move to one side', text: 'Make one side 0', icon: 'mv11' },
    fac11:  { kind: 'Factor', text: 'Factor the quadratic', icon: 'fac9' },
    zp11:   { kind: 'Each factor = 0', text: 'A product is 0 when a factor is 0', icon: 'zp9' },
    toexp11: { kind: 'Exponential form', text: 'logᵦ N = k means bᵏ = N', icon: 'exp11' },
    tolog11: { kind: 'Log form', text: 'bᵏ = N means logᵦ N = k', icon: 'log11' },
    rt11:   { kind: 'Square root', text: 'Take the square root of both sides', icon: 'root11' },
    lp11:   { kind: 'Expand the log', text: 'log(MN) = log M + log N, log(M/N) = log M − log N', icon: 'lp11', part: true, fx: 'spin11' },
    prp11:  { kind: 'Power rule for logs', text: 'log(Mᵖ) = p·log M', icon: 'pr11', part: true, fx: 'spin11' },
    le11:   { kind: 'Evaluate the log', text: 'logᵦ N asks: b to what power is N?', icon: 'log11', part: true },
    lc11:   { kind: 'Condense', text: 'A sum of logs is the log of a product; a difference is the log of a quotient', icon: 'lc11' },
    cob11:  { kind: 'Change of base', text: 'logᵦ N = ln N ÷ ln b', icon: 'cob11', part: true },
    tl11:   { kind: 'Take the log of both sides', text: 'Take the log of both sides to bring the exponent down', icon: 'log11' },
    dvl11:  { kind: 'Divide', text: 'Divide both sides', icon: 'div11' },
    as11:   { kind: 'Add or subtract', text: 'Add or subtract on both sides', icon: 'as11' },
    ot11:   { kind: 'Drop the logs', text: 'ln A = ln B means A = B', icon: 'mt11' },
    inv11:  { kind: 'Inverse property', text: 'ln and e undo each other', icon: 'log11' },
    chk11:  { kind: 'Check', text: 'Put each answer into the original: a log needs a positive inside', icon: 'chk11' },
  };
  const SC = KT.scripted({ OPS, keepRows: 3,
    anim: {
      async chk11(c, s, ns, at, H, stp) {
        const t = H.tk(at); H.mark([at]);
        caption(stp.cap || 'Check each answer in the original equation');
        await quick(250); await hold();
        if (t) t.classList.add(/Reject/.test(stp.v) ? 'bad11' : 'good11');
        await quick(200);
        await H.result(ns, ['W'], stp.after || '');
      },
    } });

  // ================================================================ stage 48: growth and decay
  const S11 = (kind, skill, pk, top, row0, steps, ans, extra = {}) => ({ k11: kind, top, rows: [row0], i: 0, steps, ans, skill, pk, qid: qid(), ...extra });
  const GROW_CASES = ['grow', 'decay', 'half', 'double', 'compound', 'cont', 'identify'];
  function genGrow(cs, tut = isTutorial()) {
    const L = lvl(tut);
    cs = cs || pick(GROW_CASES);
    if (cs === 'grow' || cs === 'decay') {
      const grow = cs === 'grow';
      const r = L >= 2 && chance(0.5) ? pick([1.5, 2.5, 3.5, 4.5, 6.5]) : grow ? rand(2, 9) : pick([5, 8, 10, 12, 15, 20, 25]);
      const g = grow ? 1 + r / 100 : 1 - r / 100, gT = trimDec(g), rT = trimDec(r / 100), gBad = trimDec(grow ? 1 - r / 100 : 1 + r / 100);
      const P0 = grow ? pick([1200, 2000, 3500, 5000, 800, 15000]) : pick([18000, 24000, 9500, 32000]);
      const t = rand(2, [4, 5, 8, 10][L]);
      const V = grow ? 'P' : 'V', fmt = grow ? v => D(v, 0) : money;
      const top = grow ? `A town of ${P0} people grows by ${r}% each year. How many people after ${t} years?` : `A car bought for $${P0} loses ${r}% of its value each year. What is it worth after ${t} years?`;
      const model = `${V} = ${P0}(${gT})${supH('t')}`, plugged = `${V} = ${P0}(${gT})${supH(t)}`;
      const val = P0 * g ** t;
      const steps = [
        st('mdl11', model, model, {
          alts: [alt(`${V} = ${P0}(${rT})${supH('t')}`, `${rT} is the rate. Each year multiplies by 1 ${grow ? '+' : MINUS} ${rT} = ${gT}.`),
            alt(`${V} = ${P0}(${gBad})${supH('t')}`, grow ? 'That shrinks it: growth multiplies by more than 1.' : 'That grows it: losing value multiplies by less than 1.'),
            alt(`${V} = ${P0} ${grow ? '+' : MINUS} ${gT}t`, 'Adding the same amount each year is linear. A percent change multiplies, so t goes in the exponent.')],
          rule: [alt(`${V} = ${P0}(${r})${supH('t')}`, `Turn the percent into a decimal first: ${r}% = ${rT}, and the factor is 1 ${grow ? '+' : MINUS} ${rT} = ${gT}.`)],
          trap: { name: 'times t', v: `${V} = ${P0} · ${gT} · t`, txt: 'Multiply the start by the factor and by the time', why: `Multiplying by t isn't repeated growth. After ${t} years the factor ${gT} has been used ${t} times: ${P0}(${gT})${supT(t)}.` },
          why: ['Start × (growth factor)ᵗ.', `A percent change multiplies each year: ${V} = start × (1 ${grow ? '+' : MINUS} rate)ᵗ.`], cap: `Each year multiplies by ${gT}` }),
        st('plug11', plugged, plugged, {
          alts: [alt(`${V} = ${P0}(${gT}) · ${t}`, `t is the exponent: the factor is used ${t} times, not multiplied by ${t}.`), alt(`${V} = (${P0} · ${gT})${supH(t)}`, 'Only the factor is raised to the power, not the start.'), alt(`${V} = ${P0}(${gT})${supH(t + 1)}`, `t = ${t}, so the exponent is ${t}.`)],
          why: [`Put t = ${t} in the exponent.`], cap: `t = ${t}` }),
        st('ev11', `${V} ≈ ${fmt(val)}`, `${V} ≈ ${fmt(val)}`, {
          alts: [alt(`${V} ≈ ${fmt(P0 * g * t)}`, 'That multiplies by t instead of raising to the power t.'), alt(`${V} ≈ ${fmt(P0 * (1 + (grow ? 1 : -1) * r * t / 100))}`, `That adds ${r}% of the start every year (simple interest). Each year's change is ${r}% of the new amount.`), alt(`${V} ≈ ${fmt(P0 * g ** (t - 1))}`, `That's only ${t - 1} years.`)],
          why: [`${gT}${supT(t)} first, then × ${P0}.`], cap: 'Power first, then multiply' }),
      ];
      return { r11: S11('gr', 'expgrow', 'grow', top, `${V} = ?`, steps, `${V} ≈ ${fmt(val)}`), enemy: 'sandling' };
    }
    if (cs === 'half' || cs === 'double') {
      const half = cs === 'half';
      const A0 = half ? pick([80, 100, 200, 240, 400, 640]) : pick([50, 120, 300, 250, 75]);
      const h = half ? pick([3, 5, 8, 10, 20, 30]) : pick([2, 3, 4, 6, 20]);
      const k = rand(2, [3, 3, 4, 5][L]), t = h * k, f = half ? '½' : '2';
      const unit = half ? (h >= 20 ? 'years' : 'days') : (h >= 20 ? 'minutes' : 'hours');
      const top = half ? `A sample of ${A0} g has a half-life of ${h} ${unit}. How much is left after ${t} ${unit}?` : `A culture of ${A0} bacteria doubles every ${h} ${unit}. How many are there after ${t} ${unit}?`;
      const V = half ? 'A' : 'N';
      const model = `${V} = ${A0}(${f})${supH(`t/${h}`)}`, val = half ? A0 / 2 ** k : A0 * 2 ** k;
      const fmt = v => trimDec(+v.toFixed(3));
      const steps = [
        st('mdl11', model, model, {
          alts: [alt(`${V} = ${A0}(${f})${supH(`${h}t`)}`, `It ${half ? 'halves' : 'doubles'} once every ${h} ${unit}, so the number of ${half ? 'halvings' : 'doublings'} is t ÷ ${h}.`),
            alt(`${V} = ${A0}(${f})${supH('t')}`, `That ${half ? 'halves' : 'doubles'} every single ${unit.slice(0, -1)}. It only happens every ${h}.`),
            alt(`${V} = ${A0}(${half ? '2' : '½'})${supH(`t/${h}`)}`, half ? 'A half-life multiplies by ½, not 2.' : 'Doubling multiplies by 2, not ½.')],
          rule: [alt(`${V} = ${A0} ${half ? MINUS : '+'} ${half ? '½' : '2'}t`, `${half ? 'Halving' : 'Doubling'} multiplies, it doesn't subtract a fixed amount.`)],
          why: [`Start × (${f}) to the power t/${h}.`], cap: `One ${half ? 'halving' : 'doubling'} every ${h} ${unit}` }),
        st('plug11', `${V} = ${A0}(${f})${supH(k)}`, `${V} = ${A0}(${f})${supH(k)}`, {
          alts: [alt(`${V} = ${A0}(${f})${supH(t)}`, `The exponent is t/${h} = ${t}/${h} = ${k}.`), alt(`${V} = (${A0} · ${f})${supH(k)}`, `Only the ${f} is raised to the power.`), alt(`${V} = ${A0}(${f})${supH(k + 1)}`, `${t} ÷ ${h} = ${k}.`)],
          why: [`t/${h} = ${t}/${h} = ${k}.`], cap: `${t} ÷ ${h} = ${k} ${half ? 'halvings' : 'doublings'}` }),
        st('ev11', `${V} = ${fmt(val)}`, `${V} = ${fmt(val)}`, {
          alts: [alt(`${V} = ${fmt(half ? A0 / (2 * k) : A0 * 2 * k)}`, `That's ${half ? 'dividing by' : 'multiplying by'} 2 × ${k}. Use 2${supT(k)} = ${2 ** k}.`), alt(`${V} = ${fmt(half ? A0 / 2 ** (k - 1) : A0 * 2 ** (k - 1))}`, `That's ${k - 1} ${half ? 'halvings' : 'doublings'}, not ${k}.`), alt(`${V} = ${fmt(half ? A0 / 2 ** (k + 1) : A0 * 2 ** (k + 1))}`, `That's ${k + 1} ${half ? 'halvings' : 'doublings'}.`)],
          why: [`(${f})${supT(k)} = ${half ? '1/' + 2 ** k : 2 ** k}.`], cap: `${half ? 'Halve' : 'Double'} it ${k} times` }),
      ];
      return { r11: S11('gr', 'expgrow', 'grow', top, `${V} = ?`, steps, `${V} = ${fmt(val)}${half ? ' g' : ''}`), enemy: 'sandling' };
    }
    if (cs === 'compound') {
      const [r, n, name] = pick([[6, 12, 'monthly'], [12, 12, 'monthly'], [3, 12, 'monthly'], [9, 12, 'monthly'], [4, 4, 'quarterly'], [6, 4, 'quarterly'], [8, 4, 'quarterly'], [10, 4, 'quarterly'], [5, 2, 'twice a year'], [7, 2, 'twice a year'], [3, 2, 'twice a year']]);
      const Pp = pick([1000, 2500, 5000, 800, 1200]), t = rand(2, [3, 5, 8, 10][L]);
      const rd = r / 100, base = 1 + rd / n, rT = trimDec(rd), bT = trimDec(base);
      const top = `$${Pp} is invested at ${r}% a year, compounded ${name}. What is it worth after ${t} years?`;
      const model = `A = ${Pp}(1 + ${frH(rT, n)})${supH(`${n}·${t}`)}`, val = Pp * base ** (n * t);
      const steps = [
        st('mdl11', model, model, {
          alts: [alt(`A = ${Pp}(1 + ${rT})${supH(`${n}·${t}`)}`, `Compounding ${name} splits the yearly rate: each period gets ${rT} ÷ ${n}.`), alt(`A = ${Pp}(1 + ${frH(rT, n)})${supH(t)}`, `There are ${n} periods a year, so ${n}·${t} periods in all.`), alt(`A = ${Pp} + ${Pp}(${rT})(${t})`, 'That is simple interest. Compound interest earns interest on the interest.')],
          rule: [alt(`A = ${Pp}(1 + ${frH(r, n)})${supH(`${n}·${t}`)}`, `Write the rate as a decimal: ${r}% = ${rT}.`)],
          why: ['A = P(1 + r/n)ⁿᵗ.', `Compound interest: A = P(1 + r/n)ⁿᵗ with r = ${rT}, n = ${n}, t = ${t}.`], cap: `${n} periods a year, each earning ${rT} ÷ ${n}` }),
        st('plug11', `A = ${Pp}(${bT})${supH(n * t)}`, `A = ${Pp}(${bT})${supH(n * t)}`, {
          alts: [alt(`A = ${Pp}(${bT})${supH(n + t)}`, `${n}·${t} multiplies: ${n * t} periods.`), alt(`A = ${Pp}(${trimDec(1 + rd)})${supH(n * t)}`, `1 + ${rT}/${n} = ${bT}.`), alt(`A = ${Pp}(${bT})${supH(t)}`, `The exponent is ${n}·${t} = ${n * t}.`)],
          why: [`1 + ${rT}/${n} = ${bT}, and ${n}·${t} = ${n * t}.`], cap: `1 + ${rT} ÷ ${n} = ${bT}` }),
        st('ev11', `A ≈ ${money(val)}`, `A ≈ ${money(val)}`, {
          alts: [alt(`A ≈ ${money(Pp * (1 + rd) ** t)}`, 'That compounds once a year.'), alt(`A ≈ ${money(Pp * (1 + rd * t))}`, 'That is simple interest.'), alt(`A ≈ ${money(Pp * base * n * t)}`, 'The periods are an exponent, not a multiplier.')],
          why: [`${bT}${supT(n * t)} first, then × ${Pp}.`], cap: 'Power first, then multiply' }),
      ];
      return { r11: S11('gr', 'expgrow', 'grow', top, 'A = ?', steps, `A ≈ ${money(val)}`), enemy: 'sandling' };
    }
    if (cs === 'cont') {
      const Pp = pick([500, 1000, 2000, 750]), r = rand(2, 9), t = rand(2, [5, 6, 10, 12][L]), rd = r / 100, rT = trimDec(rd), rt = trimDec(rd * t);
      const top = `$${Pp} is invested at ${r}% a year, compounded continuously. What is it worth after ${t} years?`;
      const model = `A = ${Pp}e${supH(`${rT}·${t}`)}`, val = Pp * Math.exp(rd * t);
      const steps = [
        st('mdl11', model, model, {
          alts: [alt(`A = ${Pp}(1 + ${rT})${supH(t)}`, 'That compounds once a year. Continuously uses e: A = Peʳᵗ.'), alt(`A = ${Pp} · e · ${rT} · ${t}`, 'r·t is the exponent of e, not a multiplier.'), alt(`A = ${Pp}e${supH(`${rT} + ${t}`)}`, 'The exponent is r times t.')],
          rule: [alt(`A = ${Pp}e${supH(`${r}·${t}`)}`, `Write the rate as a decimal: ${r}% = ${rT}.`)],
          why: ['A = Peʳᵗ.', 'Continuous compounding: A = Peʳᵗ.'], cap: 'Continuous growth uses e' }),
        st('plug11', `A = ${Pp}e${supH(rt)}`, `A = ${Pp}e${supH(rt)}`, { alts: [alt(`A = ${Pp}e${supH(trimDec(rd + t))}`, `${rT} × ${t} = ${rt}.`), alt(`A = (${Pp}e)${supH(rt)}`, 'Only e is raised to the power.')], why: [`${rT} × ${t} = ${rt}.`], cap: `${rT} × ${t} = ${rt}` }),
        st('ev11', `A ≈ ${money(val)}`, `A ≈ ${money(val)}`, {
          alts: [alt(`A ≈ ${money(Pp * (1 + rd) ** t)}`, 'That compounds once a year.'), alt(`A ≈ ${money(Pp * Math.E * rd * t)}`, 'r·t is an exponent.'), alt(`A ≈ ${money(Pp * (1 + rd * t))}`, 'That is simple interest.')],
          why: [`e${supT(1)} ≈ 2.718; work out e to the ${rt}, then × ${Pp}.`], cap: `e to the ${rt}, then × ${Pp}` }),
      ];
      return { r11: S11('gr', 'expgrow', 'grow', top, 'A = ?', steps, `A ≈ ${money(val)}`), enemy: 'sandling' };
    }
    // identify
    const a = rand(1, 5), b = pick(L >= 2 ? [0.5, 0.8, 0.9, 0.75, 0.6, 1.2, 1.5, 2, 1.05, 0.95, 1.08] : [0.5, 0.8, 0.9, 1.5, 2, 1.2]);
    const decay = b < 1, pct = trimDec(Math.abs(b - 1) * 100), bT = trimDec(b), kind = decay ? 'decay' : 'growth', Kind = decay ? 'Decay' : 'Growth';
    const steps = [
      st('cls11', `${Kind}: ${bT} ${decay ? '<' : '>'} 1`, `${bT} ${decay ? '<' : '>'} 1, so ${kind}`, {
        alts: [alt(`${decay ? 'Growth' : 'Decay'}: ${bT} ${decay ? '<' : '>'} 1`, decay ? 'Multiplying by less than 1 shrinks it each step: decay.' : 'Multiplying by more than 1 grows it each step.'), ...(a > 1 && decay ? [alt(`Growth: ${a} > 1`, `${a} is the starting value. The base ${bT} decides: less than 1 means decay.`)] : []), alt(`${decay ? 'Growth' : 'Decay'}: ${bT} > 0`, 'Every base here is positive. Compare it with 1.')],
        why: [`Compare the base ${bT} with 1.`], cap: `The base ${bT} is ${decay ? 'less' : 'more'} than 1`, gr: { a, b } }),
      st('rate11', `${pct}% ${kind}`, `${pct}% ${kind} per step`, {
        alts: [alt(`${pct}% ${decay ? 'growth' : 'decay'}`, `The base is ${decay ? 'less' : 'more'} than 1: ${kind}.`), alt(`${trimDec(b * 100)}% ${kind}`, `${bT} is what's kept${decay ? '' : ' plus the gain'}: the change is |${bT} − 1| = ${trimDec(Math.abs(b - 1))}, or ${pct}%.`), alt(`${bT}% ${kind}`, `The change each step is |${bT} − 1| = ${trimDec(Math.abs(b - 1))} = ${pct}%.`)],
        rule: [alt(`${trimDec(b * 100)}% ${kind}`, `${bT} is the factor, not the rate. The rate is |${bT} − 1| = ${pct}%.`)],
        why: [`The rate is |${bT} − 1| = ${pct}%.`], cap: `|${bT} − 1| = ${trimDec(Math.abs(b - 1))} = ${pct}%` }),
    ];
    return { r11: S11('gr', 'expgrow', 'id', 'Growth or decay? By what percent per step?', `${Y} = ${a === 1 ? '' : a}(${bT})${supH('x')}`, steps, `${Kind}, ${pct}% per step`, { gr: { a, b } }), enemy: 'sandling' };
  }

  // ================================================================ stage 49: same-base equations
  const SAME_CASES = ['basic', 'both', 'frac', 'root', 'quad'];
  const powAlts = (N, B, k) => {   // wrong ways to write N as a power of B
    const out = [alt(`${N} = ${pw(B, k + 1)}`, `${B}${supT(k + 1)} = ${B ** (k + 1)}, not ${N}.`), alt(`${N} = ${pw(B, k - 1)}`, `${B}${supT(k - 1)} = ${B ** (k - 1)}, not ${N}.`)];
    if (k ** B !== N && B !== k) out.push(alt(`${N} = ${pw(k, B)}`, `${k}${supT(B)} = ${k ** B}. Keep the base ${B} and find its exponent.`));
    return out;
  };
  const powRule = (N, B, k) => (N / B !== k && Number.isInteger(N / B) ? [alt(`${N} = ${pw(B, N / B)}`, `The exponent counts how many ${B}s multiply to ${N}: ${Array(k).fill(B).join(' × ')}. It isn't ${N} ÷ ${B}.`)] : []);
  const linSol = (a, c, k) => fDiv(fAdd(FN(k), F(-c)), F(a));        // a·x + c = k
  function solveStep(a, c, k) {   // a·x + c = k (k a fraction) -> x
    const s = linSol(a, c, k);
    const bad = [fDiv(fAdd(FN(k), F(c)), F(a)), fAdd(FN(k), F(-c)), fNeg(s)].filter(v => !fEq(v, s));
    return st('sv11', `${X} = ${numH(s, true)}`, `${X} = ${numH(s, true)}`, { alts: bad.map(v => alt(`${X} = ${numH(v, true)}`, `Undo ${c ? `the ${c > 0 ? '+' : MINUS} ${Math.abs(c)} first, then ` : ''}${a !== 1 ? `÷ ${a}` : 'nothing else'}.`)), why: ['Get x alone.'], cap: 'Get x alone' });
  }
  function genSame(cs, tut = isTutorial()) {
    const L = lvl(tut);
    cs = cs || pick(SAME_CASES);
    for (let tries = 0; tries < 200; tries++) {
      if (cs === 'basic') {
        const [B, mx] = pick([[2, [5, 6, 7, 8][L]], [3, [4, 4, 5, 5][L]], [5, [3, 3, 4, 4][L]]]);
        const k = rand(2, mx), N = B ** k, m = L >= 1 && chance(0.5) ? rand(2, 3) : 1, c = nz(-4, 4);
        const s = linSol(m, c, k); if (L < 2 && s.d !== 1) continue;
        const e = lin(m, c);
        const R = { h: String(N), ref: 'R' }, Lh = { h: pw(B, e), ref: 'L' };
        const steps = [
          st('rw11', `${N} = ${pw(B, k)}`, [Lh, { h: '=' }, { h: pw(B, k), ref: 'R' }], { ref: 'R', alts: powAlts(N, B, k), rule: powRule(N, B, k), why: [`Write ${N} as a power of ${B}.`, `Make the bases match: ${N} = ${Array(k).fill(B).join(' × ')} = ${B}${supT(k)}.`], cap: `${N} = ${B}${supT(k)}` }),
          st('mt11', `${e} = ${k}`, `${e} = ${k}`, { alts: [alt(`${e} = ${N}`, `Match the exponents: ${N} isn't an exponent, ${k} is.`), alt(`${X} = ${k}`, `The whole exponent ${KT.strip(e)} equals ${k}.`)], why: ['Same base, so the exponents are equal.'], cap: 'Same base: the exponents are equal',
            trap: { name: 'drop the base', v: `${B}${supT(1)} = ${N}`, txt: 'The bases cancel', why: 'Nothing cancels: equal powers of the same base have equal exponents.' } }),
          solveStep(m, c, k),
        ];
        const ans = steps[2].v;
        return { r11: S11('sb', 'samebase', 'same', '', [Lh, { h: '=' }, R], steps, ans), enemy: 'tickling' };
      }
      if (cs === 'both' || cs === 'frac' || cs === 'root') {
        const [B, m, n] = cs === 'both' ? pick([[2, 2, 3], [2, 2, 4], [2, 3, 4], [2, 1, 2], [2, 1, 3], [3, 1, 2], [3, 2, 3], [5, 1, 2], [5, 2, 3]]) : pick([[2, 2], [2, 3], [3, 2], [5, 2], [2, 1], [3, 1], [10, 2], [7, 2]]);
        const b1 = B ** m;
        if (b1 > 125) continue;
        const a1 = L >= 2 && chance(0.4) ? 2 : 1, c1 = L >= 1 && chance(0.6) ? nz(-3, 3) : 0;
        const e1 = lin(a1, c1);
        let rhs, rhsB, eR, eRh, rEq;   // right side: its html, its rewrite as B^(…), the exponent polynomial
        if (cs === 'both') {
          const b2 = B ** n, a2 = 1, c2 = nz(-3, 3);
          rhs = pw(b2, lin(a2, c2)); rhsB = `(${pw(B, n)})${supH(lin(a2, c2))}`; eR = P1(n * a2, n * c2); rEq = { b: b2, n, a: a2, c: c2 };
        } else if (cs === 'frac') {
          const k = rand(1, B >= 5 ? 2 : 3); rhs = frH('1', String(B ** k)); rhsB = pw(B, M_(-k)); eR = [F(-k)]; rEq = { k };
        } else {
          const cube = L >= 1 && chance(0.4) && B <= 3;
          rhs = (cube ? '∛' : '√') + B; rhsB = pw(B, cube ? '⅓' : '½'); eR = [F(1, cube ? 3 : 2)]; rEq = { root: cube ? 3 : 2 };
        }
        const eL = P1(m * a1, m * c1);
        const den = fv(eL[1] || F(0)) - fv(eR[1] || F(0));
        if (Math.abs(den) < 1e-9) continue;
        const sol = fDiv(fAdd(FN(eR[0]), fNeg(FN(eL[0]))), fAdd(FN(eL[1] || F(0)), fNeg(FN(eR[1] || F(0)))));
        if (L < 2 && cs === 'both' && sol.d !== 1) continue;
        if (Math.abs(sol.n) > 30) continue;
        const Lh0 = { h: pw(b1, e1), ref: 'L' }, Rh0 = { h: rhs, ref: 'R' };
        const steps = [];
        let curL = Lh0, curR = Rh0;
        if (m > 1) {
          curL = { h: `(${pw(B, m)})${supH(e1)}`, ref: 'L' };
          const rr = powRule(b1, B, m);
          steps.push(st('rw11', `${b1} = ${pw(B, m)}`, [curL, { h: '=' }, curR], { ref: 'L', alts: powAlts(b1, B, m), rule: rr, why: [`Write ${b1} as a power of ${B}.`], cap: `${b1} = ${B}${supT(m)}` }));
        }
        if (cs === 'both' && rEq.n > 1 || cs !== 'both') {
          curR = { h: rhsB, ref: 'R' };
          const rwAlts = cs === 'both' ? powAlts(rEq.b, B, rEq.n) : cs === 'frac'
            ? [alt(`${rhs} = ${pw(B, rEq.k)}`, `1 over a power is a negative exponent: 1/${B}${supT(rEq.k)} = ${B}${supT(-rEq.k)}.`), alt(`${rhs} = ${pw(B, M_(-rEq.k - 1))}`, `${B}${supT(rEq.k)} = ${B ** rEq.k}, so the exponent is ${M_(-rEq.k)}.`)]
            : [alt(`${rhs} = ${pw(B, rEq.root)}`, `A ${rEq.root === 2 ? 'square' : 'cube'} root is the power 1/${rEq.root}, not ${rEq.root}.`), alt(`${rhs} = ${pw(B, M_(-rEq.root))}`, `A root is a fraction exponent: ${rEq.root === 2 ? '√' : '∛'}${B} = ${B} to the 1/${rEq.root}.`)];
          const rwRule = cs === 'frac' ? [alt(`${rhs} = ${MINUS}${pw(B, rEq.k)}`, 'A negative exponent makes a fraction, not a negative number.')] : cs === 'root' ? [alt(`${rhs} = ${pw(B, M_(-1) + '/' + rEq.root)}`, `A root is a positive fraction exponent: 1/${rEq.root}.`)] : powRule(rEq.b, B, rEq.n);
          const what = cs === 'both' ? `${rEq.b} = ${pw(B, rEq.n)}` : `${rhs} = ${rhsB}`;
          steps.push(st('rw11', what, [curL, { h: '=' }, curR], { ref: 'R', alts: rwAlts, rule: rwRule, why: [`Write the right side as a power of ${B}.`], cap: cs === 'frac' ? '1 over a power is a negative exponent' : cs === 'root' ? 'A root is a fraction exponent' : KT.strip(what) }));
        }
        const eLh = ptext(eL, true), eRh2 = ptext(eR, true);
        if (m > 1 || (cs === 'both' && rEq.n > 1)) {
          const v = `${pw(B, eLh)} = ${pw(B, eRh2)}`;
          const addL = m > 1 ? ptext(P1(a1, c1 + m), true) : eLh, addR = cs === 'both' && rEq.n > 1 ? ptext(P1(rEq.a, rEq.c + rEq.n), true) : eRh2;
          const forgotL = m > 1 && c1 ? ptext(P1(m * a1, c1), true) : eLh, forgotR = cs === 'both' && rEq.n > 1 ? ptext(P1(rEq.n * rEq.a, rEq.c), true) : eRh2;
          steps.push(st('pr11', v, [{ h: pw(B, eLh), ref: 'L' }, { h: '=' }, { h: pw(B, eRh2), ref: 'R' }], {
            alts: [alt(`${pw(B, addL)} = ${pw(B, addR)}`, 'A power of a power multiplies the exponents: (aᵐ)ⁿ = aᵐⁿ, not aᵐ⁺ⁿ.')],
            rule: forgotL !== eLh || forgotR !== eRh2 ? [alt(`${pw(B, forgotL)} = ${pw(B, forgotR)}`, 'Multiply the whole exponent: every term in the bracket.')] : [],
            why: ['Multiply the exponents: (aᵐ)ⁿ = aᵐⁿ.'], cap: '(aᵐ)ⁿ = aᵐⁿ: multiply the exponents' }));
        }
        steps.push(st('mt11', `${eLh} = ${eRh2}`, `${eLh} = ${eRh2}`, { alts: [alt(`${e1} = ${cs === 'both' ? lin(rEq.a, rEq.c) : numH(eR[0], true)}${cs === 'both' ? '' : ''}`, 'Rewrite with the same base first: the exponents only match once the bases do.')].filter(a => a.v !== `${eLh} = ${eRh2}`), why: ['Same base, so the exponents are equal.'], cap: 'Same base: the exponents are equal' }));
        const A_ = fAdd(FN(eL[1] || F(0)), fNeg(FN(eR[1] || F(0)))), C_ = fAdd(FN(eL[0]), fNeg(FN(eR[0])));
        const bad = [fDiv(C_, A_), fNeg(fDiv(fNeg(C_), F(1))), fAdd(sol, F(1))].filter(v => !fEq(v, sol));
        steps.push(st('sv11', `${X} = ${numH(sol, true)}`, `${X} = ${numH(sol, true)}`, { alts: bad.map(v => alt(`${X} = ${numH(v, true)}`, 'Collect the x terms on one side, then divide.')), why: ['Get x alone.'], cap: 'Get x alone' }));
        return { r11: S11('sb', 'samebase', 'same', '', [Lh0, { h: '=' }, Rh0], steps, `${X} = ${numH(sol, true)}`), enemy: 'tickling' };
      }
      // quad: B^(x² + px) = B^k
      const B = pick([2, 3]), r1 = rand(1, 3), r2 = -rand(1, 3), p = -(r1 + r2), k = -r1 * r2;
      if (B ** k > 300) continue;
      const N = B ** k, e = ptext([F(0), F(p), F(1)], true);
      const Lh = { h: pw(B, e), ref: 'L' };
      const fct = `(${xm(r1)})(${xm(r2)}) = 0`;
      const steps = [
        st('rw11', `${N} = ${pw(B, k)}`, [Lh, { h: '=' }, { h: pw(B, k), ref: 'R' }], { ref: 'R', alts: powAlts(N, B, k), rule: powRule(N, B, k), why: [`Write ${N} as a power of ${B}.`], cap: `${N} = ${B}${supT(k)}` }),
        st('mt11', `${e} = ${k}`, `${e} = ${k}`, { alts: [alt(`${e} = ${N}`, `Match exponents: ${k}, not ${N}.`)], why: ['Same base, so the exponents are equal.'], cap: 'Same base: the exponents are equal' }),
        st('mv11', `${ptext([F(-k), F(p), F(1)], true)} = 0`, `${ptext([F(-k), F(p), F(1)], true)} = 0`, { alts: [alt(`${ptext([F(k), F(p), F(1)], true)} = 0`, `Subtracting ${k} from both sides gives ${MINUS} ${k}.`)], why: ['Make one side 0 so you can factor.'], cap: `Subtract ${k}: one side is 0` }),
        st('fac11', fct, fct, { alts: [alt(`(${xm(-r1)})(${xm(-r2)}) = 0`, `Check: that multiplies out with the signs reversed.`)], rule: [alt(`(${xm(r1)})(${xm(-r2)}) = 0`, `The numbers must multiply to ${M_(-k)} and add to ${M_(p)}.`)], why: [`Two numbers that multiply to ${M_(-k)} and add to ${M_(p)}.`], cap: 'Factor' }),
        st('zp11', `${X} = ${M_(r1)} or ${X} = ${M_(r2)}`, `${X} = ${M_(r1)} or ${X} = ${M_(r2)}`, { alts: [alt(`${X} = ${M_(-r1)} or ${X} = ${M_(-r2)}`, `${KT.strip(xm(r1))} = 0 gives x = ${M_(r1)}: the sign changes.`)], rule: [alt(`${X} = ${M_(-r1)} or ${X} = ${M_(-r2)}`, 'Set each factor to 0 and solve: x − 2 = 0 gives x = 2.')], why: ['Set each factor to 0.'], cap: 'Each factor = 0' }),
      ];
      return { r11: S11('sb', 'samebase', 'same', '', [Lh, { h: '=' }, { h: String(N), ref: 'R' }], steps, `${X} = ${M_(r1)} or ${X} = ${M_(r2)}`), enemy: 'tickling' };
    }
    return genSame('basic', tut);
  }

  // ================================================================ stage 50: logarithms
  const LOG_CASES = ['toexp', 'tolog', 'eval', 'evalfrac', 'solve', 'solvebase', 'common', 'inverse'];
  function genLog(cs, tut = isTutorial()) {
    const L = lvl(tut);
    cs = cs || pick(LOG_CASES);
    const [b, mx] = pick([[2, [5, 6, 7, 8][L]], [3, [3, 4, 5, 5][L]], [4, [3, 3, 4, 4][L]], [5, [2, 3, 3, 4][L]], [6, [2, 2, 3, 3][L]]]);
    const k = rand(2, mx), N = b ** k;
    const def = `${LG(b)} N = k means ${b}ᵏ = N: the log is the exponent.`;
    if (cs === 'toexp' || cs === 'tolog') {
      const toexp = cs === 'toexp';
      const neg = L >= 2 && chance(0.4), kk = neg ? -k : k, NN = neg ? frH('1', String(N)) : String(N);
      const logF = `${LG(b)} ${NN} = ${M_(kk)}`, expF = `${pw(b, M_(kk))} = ${NN}`;
      const steps = toexp
        ? [st('toexp11', expF, expF, { alts: [alt(`${pw(M_(kk), b)} = ${NN}`, 'The base of the log is the base of the power.'), alt(`${pw(N, M_(kk))} = ${b}`, `The number inside the log (${N}) is the answer of the power.`), alt(`${pw(b, N)} = ${M_(kk)}`, 'The log is the exponent.')], rule: [alt(`${pw(M_(kk), b)} = ${NN}`, `logᵦ N = k means bᵏ = N: the base stays the base, the log becomes the exponent.`)], why: ['The log is the exponent.', def], cap: 'The base stays the base; the log is the exponent' })]
        : [st('tolog11', logF, logF, { alts: [alt(`${LG(M_(kk))} ${NN} = ${b}`, 'The base of the power is the base of the log.'), alt(`${LG(b)} ${M_(kk)} = ${NN}`, 'The log equals the exponent.'), alt(`${LG(N)} ${b} = ${M_(kk)}`, `The answer of the power (${N}) goes inside the log.`)], rule: [alt(`${LG(N)} ${b} = ${M_(kk)}`, 'bᵏ = N means logᵦ N = k: the result of the power goes inside the log.')], why: ['The exponent is the log.', def], cap: 'The exponent becomes the log' })];
      return { r11: S11('lg', 'logdef', toexp ? 'toexp' : 'tolog', '', toexp ? logF : expF, steps, steps[0].v), enemy: 'glassmite' };
    }
    if (cs === 'eval' || cs === 'evalfrac' || cs === 'common') {
      const bb = cs === 'common' ? 10 : b, kk0 = cs === 'common' ? rand(1, [3, 4, 5, 6][L]) : k, neg = cs === 'evalfrac' || (cs === 'common' && L >= 2 && chance(0.3));
      const NN = bb ** kk0, inside = neg ? (cs === 'common' ? '0.' + '0'.repeat(kk0 - 1) + '1' : frH('1', String(NN))) : String(NN), kk = neg ? -kk0 : kk0;
      const steps = [
        st('toexp11', `${pw(bb, '?')} = ${inside}`, [{ h: pw(bb, '?') }, { h: '=' }, { h: inside, ref: 'R' }], { alts: [alt(`${pw(inside, '?')} = ${bb}`, 'The base of the log is the base of the power.'), alt(`? = ${inside} ÷ ${bb}`, `A log asks for an exponent: ${bb} to what power is ${KT.strip(inside)}?`)], rule: [alt(`? = ${inside} ÷ ${bb}`, 'A log isn\'t a division: it asks which power of the base gives the number.')], why: ['Ask: the base to what power gives the number?'], cap: `${LG(bb).replace(/<[^>]+>/g, '')} asks: ${bb} to what power?` }),
        st('rw11', `${inside} = ${pw(bb, M_(kk))}`, [{ h: pw(bb, '?') }, { h: '=' }, { h: pw(bb, M_(kk)), ref: 'R' }], { ref: 'R', alts: neg ? [alt(`${inside} = ${pw(bb, kk0)}`, `1 over a power is a negative exponent: ${bb}${supT(-kk0)}.`), alt(`${inside} = ${MINUS}${pw(bb, kk0)}`, 'A negative exponent gives a fraction, not a negative number.')] : powAlts(NN, bb, kk0), rule: neg ? [] : powRule(NN, bb, kk0), why: [`Write it as a power of ${bb}.`], cap: `${KT.strip(inside)} = ${bb}${supT(kk)}` }),
        st('mt11', `? = ${M_(kk)}`, `? = ${M_(kk)}`, { alts: [alt(`? = ${neg ? frH('1', String(kk0)) : NN}`, `Match the exponents: ? = ${M_(kk)}.`), alt(`? = ${M_(-kk)}`, `Look at the sign of the exponent: ${M_(kk)}.`)], why: ['Match the exponents.'], cap: 'The exponents match' }),
      ];
      const q = `${LG(bb)} ${inside}`;
      return { r11: S11('lg', 'logdef', 'eval', '', `${q} = ?`, steps, `${q} = ${M_(kk)}`), enemy: 'glassmite' };
    }
    if (cs === 'solve') {
      const hard = L >= 2 && chance(0.6);
      const kk = Math.min(k, 4), NN = b ** kk;
      if (!hard) {
        const steps = [
          st('toexp11', `${X} = ${pw(b, kk)}`, `${X} = ${pw(b, kk)}`, { alts: [alt(`${X} = ${pw(kk, b)}`, 'The base of the log is the base of the power.'), alt(`${X} = ${frH(kk, b)}`, 'A log isn\'t a division.')], rule: [alt(`${X} = ${b} · ${kk}`, `${b}${supT(kk)} means ${kk} ${b}s multiplied, not ${b} × ${kk}.`)], why: ['Rewrite in exponential form.', def], cap: 'Exponential form' }),
          st('ev11', `${X} = ${NN}`, `${X} = ${NN}`, { alts: [alt(`${X} = ${b * kk}`, `${b}${supT(kk)} isn't ${b} × ${kk}.`), alt(`${X} = ${kk ** b}`, `${b}${supT(kk)}, not ${kk}${supT(b)}.`), alt(`${X} = ${b ** (kk - 1)}`, `That's ${b}${supT(kk - 1)}.`)], why: [`${b}${supT(kk)} = ${NN}.`], cap: `${b}${supT(kk)} = ${NN}` }),
        ];
        return { r11: S11('lg', 'logdef', 'solve', '', `${LG(b)} ${X} = ${kk}`, steps, `${X} = ${NN}`), enemy: 'glassmite' };
      }
      const a = rand(2, 4), c = nz(-9, 9);
      if ((NN - c) % a !== 0) return genLog('solve', tut);
      const sol = (NN - c) / a, e = lin(a, c);
      const steps = [
        st('toexp11', `${e} = ${pw(b, kk)}`, `${e} = ${NN}`, { alts: [alt(`${e} = ${pw(kk, b)}`, 'The base of the log is the base of the power.')], rule: [alt(`${e} = ${b * kk}`, `${b}${supT(kk)} means ${kk} ${b}s multiplied, not ${b} × ${kk}.`)], why: ['Rewrite in exponential form.', def], cap: `Exponential form: ${b}${supT(kk)} = ${NN}` }),
        st('sv11', `${X} = ${sol}`, `${X} = ${M_(sol)}`, { alts: [alt(`${X} = ${M_((NN + c) / a)}`, 'Undo the + or − with the opposite operation.'), alt(`${X} = ${M_(NN - c)}`, `Then divide by ${a}.`)], why: ['Get x alone.'], cap: 'Get x alone' }),
      ];
      return { r11: S11('lg', 'logdef', 'solve', '', `${LG(b)}(${e}) = ${kk}`, steps, `${X} = ${M_(sol)}`), enemy: 'glassmite' };
    }
    if (cs === 'solvebase') {
      const r = rand(2, [6, 9, 12, 15][L]), NN = r * r;
      const steps = [
        st('toexp11', `${pw(X, 2)} = ${NN}`, `${pw(X, 2)} = ${NN}`, { alts: [alt(`${pw(2, 'x')} = ${NN}`, 'x is the base, 2 is the exponent.'), alt(`${pw(NN, 2)} = ${X}`, `${NN} is the result of the power.`)], why: ['Rewrite in exponential form: the base is x.', def], cap: 'Exponential form: x is the base' }),
        st('rt11', `${X} = ±${r}`, `${X} = ±${r}`, { alts: [alt(`${X} = ${NN / 2}`, 'x² means x times x, so take the square root, not half.'), alt(`${X} = ${NN * NN}`, 'Undo a square with a square root.')], why: ['Take the square root of both sides.'], cap: 'Square root of both sides' }),
        st('chk11', `Keep ${r}, reject ${MINUS}${r}: a base must be positive`, `${X} = ${r}`, { alts: [alt(`Keep ${MINUS}${r}, reject ${r}`, 'A log base must be positive (and not 1).')], rule: [alt(`Keep both: (±${r})² = ${NN}`, `Both square to ${NN}, but a log base must be positive and not 1, so ${MINUS}${r} is out.`)], why: ['A base must be positive and not 1.'], cap: 'A log base must be positive' }),
      ];
      return { r11: S11('lg', 'logdef', 'solve', '', `${LG(X)} ${NN} = 2`, steps, `${X} = ${r}`), enemy: 'glassmite' };
    }
    // inverse: ln eᵏ = k, e^(ln N) = N, logᵦ bᵏ = k
    const v = pick(L >= 1 ? ['ln', 'eln', 'logb', 'eln2'] : ['ln', 'eln', 'logb']);
    const kk = rand(2, 9);
    if (v === 'eln2') {
      const a = rand(2, 5);
      const steps = [
        st('inv11', `${pw('e', `ln ${X}`)} = ${X}`, `${a}${X} = ${a * kk}`, { alts: [alt(`${pw('e', `ln ${X}`)} = ln ${X}`, 'e and ln undo each other: e to the ln x is just x.'), alt(`${pw('e', `ln ${X}`)} = e${X}`, 'They undo each other: nothing is left over.')], why: ['e and ln undo each other.'], cap: 'e and ln undo each other' }),
        st('dvl11', `${X} = ${kk}`, `${X} = ${kk}`, { alts: [alt(`${X} = ${a * kk - a}`, `${a}x means ${a} times x: divide by ${a}.`), alt(`${X} = ${a * kk * a}`, `Divide by ${a}.`)], why: [`Divide by ${a}.`], cap: `÷ ${a}` }),
      ];
      return { r11: S11('lg', 'logdef', 'inv', '', `${a}${pw('e', `ln ${X}`)} = ${a * kk}`, steps, `${X} = ${kk}`), enemy: 'glassmite' };
    }
    const q = v === 'ln' ? `ln ${pw('e', kk)}` : v === 'eln' ? pw('e', `ln ${kk}`) : `${LG(b)} ${pw(b, kk)}`;
    const steps = [st('inv11', `${q} = ${kk}`, `${q} = ${kk}`, { alts: [alt(`${q} = ${kk}e`, 'They undo each other: nothing is left over.'), alt(`${q} = ${v === 'logb' ? pw(b, kk) : pw('e', kk)}`, 'The log and the power undo each other.'), alt(`${q} = ${frH('1', kk)}`, 'Undoing isn\'t dividing.')], rule: [alt(`${q} = ${v === 'logb' ? b * kk : `${kk}e`}`, 'A log and a power of the same base cancel to just the exponent.')], why: ['A log and a power of the same base undo each other.'], cap: 'They undo each other' })];
    return { r11: S11('lg', 'logdef', 'inv', '', `${q} = ?`, steps, `${q} = ${kk}`), enemy: 'glassmite' };
  }

  // ================================================================ stage 51: log properties
  const PROP_CASES = ['product', 'quotient', 'power', 'expand', 'condense', 'condnum', 'cob'];
  function genProp(cs, tut = isTutorial()) {
    const L = lvl(tut);
    cs = cs || pick(PROP_CASES);
    const [b, mx] = pick([[2, [3, 5, 6, 6][L]], [3, [2, 3, 4, 4][L]], [5, [2, 2, 3, 3][L]], [10, [2, 3, 4, 4][L]]]);
    const k = rand(1, mx), N = b ** k, lg = LG(b);
    const sumWhy = 'The log of a product is a sum: log(MN) = log M + log N.', difWhy = 'The log of a quotient is a difference: log(M/N) = log M − log N.';
    const leStep = (ref, row) => st('le11', `${lg} ${N} = ${k}`, row, { ref, alts: [alt(`${lg} ${N} = ${k + 1}`, `${b}${supT(k + 1)} = ${b ** (k + 1)}, not ${N}.`), ...(N / b !== k && N / b > 1 ? [alt(`${lg} ${N} = ${N / b}`, `${lg.replace(/<[^>]+>/g, '')} ${N} asks: ${b} to what power is ${N}? Not ${N} ÷ ${b}.`)] : [])], rule: N / b !== k && N / b > 1 ? [alt(`${lg} ${N} = ${N / b}`, `A log asks for an exponent: ${b}${supT(k)} = ${N}, so it's ${k}. It isn't ${N} ÷ ${b}.`)] : [], why: [`${b} to what power is ${N}?`], cap: `${b}${supT(k)} = ${N}` });
    if (cs === 'product' || cs === 'quotient') {
      const prod = cs === 'product', p = L >= 1 && chance(0.5) ? rand(2, 4) : 1, xp = p > 1 ? pw(X, p) : X;
      const xTop = !prod && chance(0.5), inside = prod ? `${N}${xp}` : xTop ? frH(xp, N) : frH(N, xp), numFirst = !xTop;
      const t1 = `${lg} ${N}`, t2 = `${lg} ${xp}`, op = prod ? '+' : MINUS;
      const first = numFirst ? [t1, t2] : [t2, t1];
      const v = `${first[0]} ${op} ${first[1]}`;
      const steps = [st('lp11', v, numFirst ? [{ h: t1, ref: 'T1' }, { h: op }, { h: t2, ref: 'T2' }] : [{ h: t2, ref: 'T2' }, { h: op }, { h: t1, ref: 'T1' }], {
        ref: 'T0', alts: [alt(`${first[0]} ${prod ? MINUS : '+'} ${first[1]}`, prod ? 'Minus is for a quotient.' : 'Plus is for a product.'), alt(`${N} · ${lg} ${xp}`, `${N} ${prod ? 'multiplies inside the log' : 'divides inside the log'}; it isn't a power.`), ...(prod ? [] : [alt(`${first[1]} ${MINUS} ${first[0]}`, 'Top minus bottom: the log of the top comes first.')])],
        rule: [alt(prod ? `${t1} · ${t2}` : `${first[0]} ÷ ${first[1]}`, prod ? sumWhy : difWhy)],
        trap: prod ? { name: 'log of a sum', v: `${lg}(${N} + ${X}) = ${t1} + ${lg} ${X}`, txt: 'Split a log of a sum', why: 'There is no rule for the log of a sum. log M + log N is the log of a product, log(MN).' } : undefined,
        why: [prod ? sumWhy : difWhy], cap: prod ? 'log of a product: add the logs' : 'log of a quotient: subtract the logs' })];
      let row = steps[0].row;
      if (p > 1) {
        const nr = row.map(g => (g.ref === 'T2' ? { h: `${p} ${lg} ${X}`, ref: 'T2' } : g));
        steps.push(st('prp11', `${lg} ${xp} = ${p} ${lg} ${X}`, nr, { ref: 'T2', alts: [alt(`${lg} ${xp} = ${lg}(${p}${X})`, 'The exponent comes down in front: log(xᵖ) = p·log x.'), alt(`${lg} ${xp} = ${p} + ${lg} ${X}`, 'The exponent multiplies the log.')], rule: [alt(`${lg} ${xp} = (${lg} ${X})${supH(p)}`, 'log(xᵖ) = p·log x. (log x)ᵖ is something else.')], why: ['Bring the exponent down in front.'], cap: 'The exponent comes down in front' }));
        row = nr;
      }
      const fin = row.map(g => (g.ref === 'T1' ? { h: String(k) } : g.ref ? { h: g.h } : g));
      steps.push(leStep('T1', fin));
      const ans = fin.map(g => g.h).join(' ');
      return { r11: S11('lp', 'logprop', 'expand', '', [{ h: `${lg}${inside.startsWith('<') ? '' : ''}(${inside})`, ref: 'T0' }], steps, ans), enemy: 'quillwisp' };
    }
    if (cs === 'power') {
      const p = rand(2, 5), root = L >= 1 && chance(0.4);
      const inner = root ? `√${X}` : pw(X, p), coef = root ? '½' : String(p);
      const twoTerm = chance(0.5);
      const t0 = `${lg} ${inner}`;
      const steps = [];
      let row;
      if (twoTerm) {
        row = [{ h: `${lg}(${inner}${Y})`, ref: 'T0' }];
        const r1 = [{ h: t0, ref: 'T1' }, { h: '+' }, { h: `${lg} ${Y}`, ref: 'T2' }];
        steps.push(st('lp11', `${t0} + ${lg} ${Y}`, r1, { ref: 'T0', alts: [alt(`${t0} · ${lg} ${Y}`, sumWhy), alt(`${t0} ${MINUS} ${lg} ${Y}`, 'Minus is for a quotient.')], rule: [alt(`${t0} · ${lg} ${Y}`, sumWhy)], why: [sumWhy], cap: 'log of a product: add the logs' }));
      } else row = [{ h: t0, ref: 'T1' }];
      const pr = twoTerm ? [{ h: `${coef} ${lg} ${X}`, ref: 'T1' }, { h: '+' }, { h: `${lg} ${Y}`, ref: 'T2' }] : [{ h: `${coef} ${lg} ${X}`, ref: 'T1' }];
      steps.push(st('prp11', `${t0} = ${coef} ${lg} ${X}`, pr, { ref: 'T1', alts: [alt(`${t0} = ${lg}(${root ? '½' : p}${X})`, `The exponent comes down in front: log(xᵖ) = p·log x.${root ? ' √x is x to the ½.' : ''}`), alt(`${t0} = ${coef} + ${lg} ${X}`, 'The exponent multiplies the log.')], rule: [alt(`${t0} = (${lg} ${X})${supH(root ? '½' : p)}`, 'log(xᵖ) = p·log x. (log x)ᵖ is something else.')], why: [root ? '√x = x to the ½: the ½ comes down in front.' : 'Bring the exponent down in front.'], cap: root ? '√x is x to the ½: bring it down' : 'The exponent comes down in front',
        trap: { name: 'power of a log', v: `(${lg} ${X})${supH(2)} = 2 ${lg} ${X}`, txt: 'Bring a power of a log down', why: 'The power rule is for a power inside the log: log(x²) = 2 log x. (log x)² is the log squared.' } }));
      return { r11: S11('lp', 'logprop', 'expand', '', row, steps, pr.map(g => g.h).join(' ')), enemy: 'quillwisp' };
    }
    if (cs === 'expand') {
      const p = rand(2, 4), q = L >= 2 && chance(0.5) ? rand(2, 3) : 1, zq = q > 1 ? pw(Z, q) : Z;
      const t0 = `${lg}(${frH(`${pw(X, p)}${Y}`, zq)})`;
      const r1 = [{ h: `${lg}(${pw(X, p)}${Y})`, ref: 'T1' }, { h: MINUS }, { h: `${lg} ${zq}`, ref: 'T2' }];
      const r2 = [{ h: `${lg} ${pw(X, p)}`, ref: 'T3' }, { h: '+' }, { h: `${lg} ${Y}`, ref: 'T4' }, { h: MINUS }, { h: `${lg} ${zq}`, ref: 'T2' }];
      const r3 = r2.map(g => (g.ref === 'T3' ? { h: `${p} ${lg} ${X}`, ref: 'T3' } : g));
      const steps = [
        st('lp11', `${lg}(${pw(X, p)}${Y}) ${MINUS} ${lg} ${zq}`, r1, { ref: 'T0', alts: [alt(`${lg}(${pw(X, p)}${Y}) + ${lg} ${zq}`, 'Dividing becomes minus.'), alt(`${lg} ${zq} ${MINUS} ${lg}(${pw(X, p)}${Y})`, 'Top minus bottom.')], rule: [alt(`${lg}(${pw(X, p)}${Y}) ÷ ${lg} ${zq}`, difWhy)], why: [difWhy], cap: 'Quotient: top minus bottom' }),
        st('lp11', `${lg} ${pw(X, p)} + ${lg} ${Y}`, r2, { ref: 'T1', alts: [alt(`${lg} ${pw(X, p)} · ${lg} ${Y}`, sumWhy)], why: [sumWhy], cap: 'Product: add the logs' }),
        st('prp11', `${lg} ${pw(X, p)} = ${p} ${lg} ${X}`, r3, { ref: 'T3', alts: [alt(`${lg} ${pw(X, p)} = (${lg} ${X})${supH(p)}`, 'log(xᵖ) = p·log x.')], why: ['Bring the exponent down.'], cap: 'The exponent comes down' }),
      ];
      let fin = r3;
      if (q > 1) { fin = r3.map(g => (g.ref === 'T2' ? { h: `${q} ${lg} ${Z}`, ref: 'T2' } : g)); steps.push(st('prp11', `${lg} ${zq} = ${q} ${lg} ${Z}`, fin, { ref: 'T2', alts: [alt(`${lg} ${zq} = (${lg} ${Z})${supH(q)}`, 'log(zᵖ) = p·log z.')], why: ['Bring that exponent down too.'], cap: 'That exponent comes down too' })); }
      return { r11: S11('lp', 'logprop', 'expand', '', [{ h: t0, ref: 'T0' }], steps, fin.map(g => g.h).join(' ')), enemy: 'quillwisp' };
    }
    if (cs === 'condense') {
      const p = rand(2, 4), withZ = L >= 1 && chance(0.6);
      const row0 = [{ h: `${p} ${lg} ${X}`, ref: 'T0' }, { h: '+' }, { h: `${lg} ${Y}`, ref: 'T1' }, ...(withZ ? [{ h: MINUS }, { h: `${lg} ${Z}`, ref: 'T2' }] : [])];
      const r1 = row0.map(g => (g.ref === 'T0' ? { h: `${lg} ${pw(X, p)}`, ref: 'T0' } : g));
      const top = `${pw(X, p)}${Y}`, fin = withZ ? `${lg}(${frH(top, Z)})` : `${lg}(${top})`;
      const steps = [
        st('prp11', `${p} ${lg} ${X} = ${lg} ${pw(X, p)}`, r1, { ref: 'T0', alts: [alt(`${p} ${lg} ${X} = ${lg}(${p}${X})`, 'The number in front becomes an exponent: p·log x = log(xᵖ).'), alt(`${p} ${lg} ${X} = (${lg} ${X})${supH(p)}`, 'The number in front goes up as a power of x, inside the log.')], why: ['Move the number in front up as an exponent first.'], cap: 'The number in front becomes an exponent' }),
        st('lc11', fin, fin, { alts: [withZ ? alt(`${lg}(${pw(X, p)}${Y}${Z})`, 'A minus log divides.') : alt(`${lg} ${pw(X, p)} · ${lg} ${Y}`, 'The sum of the logs is the log of the product.'), alt(`${lg}(${frH(pw(X, p), Y)})${withZ ? '' : ''}`, 'Plus multiplies; minus divides.')], rule: [alt(`${lg}(${pw(X, p)} + ${Y}${withZ ? ` ${MINUS} ${Z}` : ''})`, 'log M + log N = log(MN): a sum of logs becomes a product inside, not a sum.')],
          trap: { name: 'log of a sum', v: `${lg} ${X} + ${lg} ${Y} = ${lg}(${X} + ${Y})`, txt: 'Add the insides', why: 'log x + log y = log(xy). Adding the insides isn\'t a log rule.' }, why: ['Plus multiplies inside, minus divides.'], cap: 'Plus multiplies, minus divides' }),
      ];
      return { r11: S11('lp', 'logprop', 'condense', '', row0, steps, fin), enemy: 'quillwisp' };
    }
    if (cs === 'condnum') {
      const [a, p, c, op, res, kk] = pick([[5, 2, 4, '+', 100, 2], [2, 3, 125, '+', 1000, 3], [5, 2, 40, '+', 1000, 3], [2, 2, 25, '+', 100, 2], [5, 3, 8, '+', 1000, 3], [10, 2, 10, '+', 1000, 3], [2, 4, 625, '+', 10000, 4]].concat([[10, 3, 10, MINUS, 100, 2], [20, 2, 4, MINUS, 100, 2], [30, 2, 9, MINUS, 100, 2]]));
      const ap = a ** p, row0 = [{ h: `${p} log ${a}`, ref: 'T0' }, { h: op }, { h: `log ${c}`, ref: 'T1' }];
      const r1 = [{ h: `log ${ap}`, ref: 'T0' }, { h: op }, { h: `log ${c}`, ref: 'T1' }];
      const steps = [
        st('prp11', `${p} log ${a} = log ${ap}`, r1, { ref: 'T0', alts: [alt(`${p} log ${a} = log ${p * a}`, `The ${p} becomes an exponent: ${a}${supT(p)} = ${ap}, not ${p} × ${a}.`), alt(`${p} log ${a} = log ${ap * p}`, `${a}${supT(p)} = ${ap}.`)], rule: [alt(`${p} log ${a} = log ${p * a}`, `p·log a = log(aᵖ): ${a}${supT(p)} = ${ap}.`)], why: ['The number in front becomes an exponent.'], cap: `${p} log ${a} = log ${a}${supT(p)} = log ${ap}` }),
        st('lc11', `log ${res}`, [{ h: `log ${res}`, ref: 'T0' }], { alts: [alt(`log ${op === '+' ? ap + +c : ap - +c}`, op === '+' ? 'A sum of logs is the log of a product.' : 'A difference of logs is the log of a quotient.'), alt(`log ${op === '+' ? ap / +c : ap * +c}`, op === '+' ? 'Plus multiplies.' : 'Minus divides.')].filter(x => !/NaN/.test(x.v)), rule: [alt(`log ${op === '+' ? ap + +c : ap - +c}`, op === '+' ? 'log M + log N = log(MN), not log(M + N).' : 'log M − log N = log(M/N), not log(M − N).')], why: [op === '+' ? 'Plus: multiply inside.' : 'Minus: divide inside.'], cap: op === '+' ? `${ap} × ${c} = ${res}` : `${ap} ÷ ${c} = ${res}` }),
        st('le11', `log ${res} = ${kk}`, String(kk), { ref: 'T0', alts: [alt(`log ${res} = ${res / 10}`, `log ${res} asks: 10 to what power is ${res}?`), alt(`log ${res} = ${kk + 1}`, `10${supT(kk + 1)} = ${10 ** (kk + 1)}.`)], why: [`10 to what power is ${res}?`], cap: `10${supT(kk)} = ${res}` }),
      ];
      if (!Number.isInteger(+c)) return genProp('condnum', tut);
      return { r11: S11('lp', 'logprop', 'condense', 'Write as a single log, then evaluate.', row0, steps, String(kk)), enemy: 'quillwisp' };
    }
    // cob: change of base
    const bb = pick([2, 3, 5, 7]), NN = pick([10, 20, 50, 7, 12, 30, 100, 6].filter(n => Math.abs(Math.log(n) / Math.log(bb) - Math.round(Math.log(n) / Math.log(bb))) > 0.05));
    const val = Math.log(NN) / Math.log(bb);
    const steps = [
      st('cob11', `${LG(bb)} ${NN} = ${frH(`ln ${NN}`, `ln ${bb}`)}`, [{ h: frH(`ln ${NN}`, `ln ${bb}`), ref: 'T0' }], { ref: 'T0', alts: [alt(`${LG(bb)} ${NN} = ln ${NN} ${MINUS} ln ${bb}`, `That's ln(${NN}/${bb}). Change of base divides the logs.`), alt(`${LG(bb)} ${NN} = ${frH(NN, bb)}`, 'Take the ln of each first.')], rule: [alt(`${LG(bb)} ${NN} = ${frH(`ln ${bb}`, `ln ${NN}`)}`, 'The number goes on top, the base on the bottom: logᵦ N = ln N ÷ ln b.')], why: ['logᵦ N = ln N ÷ ln b.'], cap: 'Number on top, base on the bottom' }),
      st('ev11', `≈ ${D(val)}`, `${LG(bb)} ${NN} ≈ ${D(val)}`, { alts: [alt(`≈ ${D(1 / val)}`, 'That has the logs upside down.'), alt(`≈ ${D(Math.log(NN / bb))}`, 'That is ln(N/b).'), alt(`≈ ${D(NN / bb)}`, 'Divide the logs, not the numbers.')], why: [`ln ${NN} ≈ ${D(Math.log(NN), 3)}, ln ${bb} ≈ ${D(Math.log(bb), 3)}.`], cap: `${D(Math.log(NN), 3)} ÷ ${D(Math.log(bb), 3)}` }),
    ];
    return { r11: S11('lp', 'logprop', 'cob', 'Use the change of base formula.', [{ h: `${LG(bb)} ${NN}`, ref: 'T0' }], steps, `${LG(bb)} ${NN} ≈ ${D(val)}`), enemy: 'quillwisp' };
  }

  // ================================================================ stage 52: solving with logs
  const SOLVE_CASES = ['exp', 'expco', 'e', 'logeq', 'logsum', 'lneq'];
  function genSolve(cs, tut = isTutorial()) {
    const L = lvl(tut);
    cs = cs || pick(SOLVE_CASES);
    for (let tries = 0; tries < 200; tries++) {
      if (cs === 'exp') {
        const b = pick([2, 3, 5, 7, 4]), N = rand(5, [30, 60, 100, 200][L]);
        { const q = Math.log(N) / Math.log(b) * 6; if (Math.abs(q - Math.round(q)) < 0.02) continue; }
        const c = L >= 2 && chance(0.5) ? nz(-4, 4) : 0, lg = chance(0.5) ? 'log' : 'ln';
        const e = c ? lin(1, c) : X, eP = c ? `(${e})` : X, frac = frH(`${lg} ${N}`, `${lg} ${b}`);
        const val = Math.log(N) / Math.log(b) - c;
        const steps = [
          st('tl11', `${lg} ${pw(b, e)} = ${lg} ${N}`, `${lg} ${pw(b, e)} = ${lg} ${N}`, { alts: [alt(`${e} = ${lg} ${N}`, `That only undoes a power of ${lg === 'log' ? 10 : 'e'}. Take the ${lg} of both sides, then use the power rule.`)], rule: [alt(`${e} = ${frH(N, b)}`, `You can't divide away a base: ${b}${supT(2)} isn't ${b} × 2. Take the log of both sides to bring the exponent down.`)], why: ['Take the log of both sides.', 'The unknown is in the exponent: take the log of both sides, then the power rule brings it down.'], cap: 'Take the log of both sides' }),
          st('pr11', `${eP} · ${lg} ${b} = ${lg} ${N}`, `${eP} · ${lg} ${b} = ${lg} ${N}`, { alts: [alt(`(${lg} ${b})${supH(e)} = ${lg} ${N}`, 'The exponent comes down in front as a multiplier: log(bˣ) = x·log b.'), alt(`${e} + ${lg} ${b} = ${lg} ${N}`, 'The exponent multiplies the log.')], why: ['Power rule: the exponent comes down.'], cap: 'Power rule: the exponent comes down in front' }),
          st('dvl11', `${e} = ${frac}`, `${e} = ${frac}`, { alts: [alt(`${e} = ${lg} ${N} ${MINUS} ${lg} ${b}`, `${eP} multiplies ${lg} ${b}: divide by it.`)], rule: [alt(`${e} = ${lg}(${frH(N, b)})`, `log ${N} ÷ log ${b} isn't log(${N}/${b}). Keep it as a fraction of two logs.`)], why: [`Divide both sides by ${lg} ${b}.`], cap: `÷ ${lg} ${b}` }),
        ];
        if (c) steps.push(st('as11', `${X} = ${frac}${sgnT(-c)}`, `${X} = ${frac}${sgnT(-c)}`, { alts: [alt(`${X} = ${frac}${sgnT(c)}`, `Undo ${c > 0 ? '+' : MINUS} ${Math.abs(c)} with the opposite.`)], why: [`${c > 0 ? 'Subtract' : 'Add'} ${Math.abs(c)}.`], cap: `${c > 0 ? MINUS : '+'} ${Math.abs(c)}` }));
        steps.push(st('ev11', `${X} ≈ ${D(val)}`, `${X} ≈ ${D(val)}`, { alts: [alt(`${X} ≈ ${D(Math.log(N / b) - c)}`, 'That is log(N/b): divide the logs instead.'), alt(`${X} ≈ ${D(N / b - c)}`, 'Divide the logs, not the numbers.'), alt(`${X} ≈ ${D(Math.log(b) / Math.log(N) - c)}`, 'The logs are upside down.')], why: ['Work out the logs, then divide.'], cap: 'Work it out' }));
        return { r11: S11('ls', 'logsolve', 'lsolve', 'Solve. Round to 2 decimal places.', `${pw(b, e)} = ${N}`, steps, `${X} ≈ ${D(val)}`), enemy: 'chronoth' };
      }
      if (cs === 'expco') {
        const a = rand(2, 5), b = pick([2, 3, 5]), k = rand(1, b === 2 ? 5 : 3), c = L >= 1 && chance(0.6) ? nz(-9, 9) : 0;
        const M = b ** k, N = a * M + c;
        const row0 = c ? `${a} · ${pw(b, X)}${sgnT(c)} = ${N}` : `${a} · ${pw(b, X)} = ${N}`;
        const steps = [];
        if (c) steps.push(st('as11', `${a} · ${pw(b, X)} = ${a * M}`, `${a} · ${pw(b, X)} = ${a * M}`, { alts: [alt(`${a} · ${pw(b, X)} = ${N + c}`, `Undo ${c > 0 ? '+' : MINUS} ${Math.abs(c)} with the opposite.`)], rule: [alt(`${pw(a * b, X)} = ${N - c}`, `${a} · ${b}ˣ isn't (${a * b})ˣ: the exponent belongs to ${b} only.`)], why: ['Get the power alone: undo the + or − first.'], cap: `${c > 0 ? MINUS : '+'} ${Math.abs(c)}`,
          trap: { name: 'log too soon', v: `log(${a} · ${pw(b, X)}) = ${X} · log ${a * b}`, txt: 'Bring the exponent down over the product', why: `The x belongs to ${b} only: log(${a} · ${b}ˣ) = log ${a} + x·log ${b}. Get ${b}ˣ alone first.` } }));
        steps.push(st('dvl11', `${pw(b, X)} = ${M}`, [{ h: pw(b, X) }, { h: '=' }, { h: String(M), ref: 'R' }], { alts: [alt(`${pw(b, X)} = ${a * M - a}`, `${a} multiplies, so divide by ${a}.`)], rule: [alt(`${pw(a * b, X)} = ${a * M}`, `${a} · ${b}ˣ isn't (${a * b})ˣ: the exponent belongs to ${b} only. Divide by ${a}.`)], why: [`Divide by ${a} to get the power alone.`], cap: `÷ ${a}` }));
        steps.push(st('rw11', `${M} = ${pw(b, k)}`, `${pw(b, X)} = ${pw(b, k)}`, { ref: 'R', alts: powAlts(M, b, k).filter(x => !/⁰|NaN/.test(x.v)), rule: powRule(M, b, k), why: [`Write ${M} as a power of ${b}.`], cap: `${M} = ${b}${supT(k)}` }));
        steps.push(st('mt11', `${X} = ${k}`, `${X} = ${k}`, { alts: [alt(`${X} = ${M}`, `Match the exponents: ${k}.`)], why: ['Same base: the exponents match.'], cap: 'Same base: the exponents are equal' }));
        return { r11: S11('ls', 'logsolve', 'lsolve', '', row0, steps, `${X} = ${k}`), enemy: 'chronoth' };
      }
      if (cs === 'e') {
        const a = L >= 1 && chance(0.6) ? rand(2, 5) : 1, kk = rand(1, [3, 4, 5, 5][L]), M = rand(2, 20), N = a * M;
        const ek = kk === 1 ? X : `${kk}${X}`;
        const row0 = `${a === 1 ? '' : a}${pw('e', ek)} = ${N}`;
        const val = Math.log(M) / kk;
        const steps = [];
        if (a > 1) steps.push(st('dvl11', `${pw('e', ek)} = ${M}`, `${pw('e', ek)} = ${M}`, { alts: [alt(`${pw('e', ek)} = ${N - a}`, `${a} multiplies: divide.`)], rule: [alt(`${pw(`${a}e`, ek)} = ${N}`, `The exponent belongs to e only. Divide by ${a} first.`)], why: [`Divide by ${a} first.`], cap: `÷ ${a}` }));
        steps.push(st('tl11', `${ek} = ln ${M}`, `${ek} = ln ${M}`, { alts: [alt(`${ek} = log ${M}`, 'ln undoes e. log is base 10.'), alt(`${ek} = ${frH(M, 'e')}`, 'You can\'t divide by e to undo a power of e.')], rule: [alt(`${ek} = ${frH(M, 'e')}`, 'Undo e with ln, its inverse.')], why: ['Take ln of both sides: ln and e undo each other.'], cap: 'ln of both sides: ln undoes e' }));
        if (kk > 1) steps.push(st('dvl11', `${X} = ${frH(`ln ${M}`, kk)}`, `${X} = ${frH(`ln ${M}`, kk)}`, { alts: [alt(`${X} = ln ${M} ${MINUS} ${kk}`, `${kk}x means ${kk} times x: divide.`)], rule: [alt(`${X} = ln(${frH(M, kk)})`, `(ln ${M}) ÷ ${kk} isn't ln(${M}/${kk}).`)], why: [`Divide by ${kk}.`], cap: `÷ ${kk}` }));
        steps.push(st('ev11', `${X} ≈ ${D(val)}`, `${X} ≈ ${D(val)}`, { alts: [alt(`${X} ≈ ${D(Math.log10(M) / kk)}`, 'That used log instead of ln.'), alt(`${X} ≈ ${D(Math.log(M / kk))}`, 'That is ln(M/k).'), alt(`${X} ≈ ${D(Math.log(M) - kk)}`, 'Divide, don\'t subtract.')], why: [`ln ${M} ≈ ${D(Math.log(M), 3)}.`], cap: 'Work it out' }));
        return { r11: S11('ls', 'logsolve', 'lsolve', 'Solve. Round to 2 decimal places.', row0, steps, `${X} ≈ ${D(val)}`), enemy: 'chronoth' };
      }
      if (cs === 'logeq') {
        const [b, kk] = pick([[2, rand(2, 5)], [3, rand(1, 3)], [10, rand(1, 2)], [5, rand(1, 2)]]), Bk = b ** kk;
        const a = L >= 1 && chance(0.5) ? rand(2, 4) : 1, c = nz(-9, 9);
        if ((Bk - c) % a !== 0) continue;
        const sol = (Bk - c) / a, e = lin(a, c);
        const steps = [
          st('toexp11', `${e} = ${pw(b, kk)}`, `${e} = ${Bk}`, { alts: [alt(`${e} = ${pw(kk, b)}`, 'The base of the log is the base of the power.')], rule: [alt(`${e} = ${b * kk}`, `${b}${supT(kk)} isn't ${b} × ${kk}.`)], why: ['Rewrite in exponential form.'], cap: `Exponential form: ${b}${supT(kk)} = ${Bk}` }),
          st('sv11', `${X} = ${M_(sol)}`, `${X} = ${M_(sol)}`, { alts: [alt(`${X} = ${M_((Bk + c) / a)}`, 'Undo the + or − with the opposite operation.'), alt(`${X} = ${M_(Bk - c)}`, `Then divide by ${a}.`)].filter(x => a > 1 || !x.v.endsWith(M_(Bk - c)) || true), why: ['Get x alone.'], cap: 'Get x alone' }),
          st('chk11', `Check: ${LG(b)} ${Bk} = ${kk} ✓ keep`, `${X} = ${M_(sol)}`, { alts: [alt(`Reject ${X} = ${M_(sol)}`, `${KT.strip(e)} = ${Bk} at x = ${M_(sol)}, which is positive, so the log is fine.`)], rule: [alt('Done: no check needed', 'A log equation needs a check: the inside of every log must be positive.')], why: ['Check the answer in the original.'], cap: `x = ${M_(sol)}: the inside is ${Bk}, positive` }),
        ];
        return { r11: S11('ls', 'logsolve', 'lsolve', 'Solve, then check.', `${LG(b)}(${e}) = ${kk}`, steps, `${X} = ${M_(sol)}`), enemy: 'chronoth' };
      }
      if (cs === 'logsum') {
        const [b, kk] = pick([[10, 1], [2, 3], [2, 4], [3, 2], [2, 2], [10, 2]]), B = b ** kk;
        const opts = [];
        for (let r = 1; r <= B; r++) if (B % r === 0) { const p = B / r - r; if (p && Math.abs(p) <= 15) opts.push([r, p]); }
        if (!opts.length) continue;
        const [r, p] = pick(opts), r2 = -(r + p), xp = lin(1, p);
        const row0 = `${LG(b)} ${X} + ${LG(b)}(${xp}) = ${kk}`;
        const q = `${ptext([F(-B), F(p), F(1)], true)} = 0`, fct = `(${xm(r)})(${xm(r2)}) = 0`;
        const steps = [
          st('lc11', `${LG(b)}(${X}(${xp})) = ${kk}`, `${LG(b)}(${X}(${xp})) = ${kk}`, { alts: [alt(`${LG(b)} ${X} · ${LG(b)}(${xp}) = ${kk}`, 'Adding logs multiplies the insides: log M + log N = log(MN).')], rule: [alt(`${LG(b)}(${X} + ${xp}) = ${kk}`, 'log M + log N = log(MN), not log(M + N).')], trap: { name: 'log of a sum', v: `${LG(b)} ${X} + ${LG(b)}(${xp}) = ${LG(b)}(${lin(2, p)})`, txt: 'Add the insides', why: 'A sum of logs is the log of a product, not of a sum.' }, why: ['Condense into one log.'], cap: 'Condense: plus multiplies' }),
          st('toexp11', `${X}(${xp}) = ${B}`, `${X}(${xp}) = ${B}`, { alts: [alt(`${X}(${xp}) = ${b * kk}`, `${b}${supT(kk)} = ${B}.`), alt(`${X}(${xp}) = ${kk}`, 'Rewrite in exponential form first.')], why: ['Rewrite in exponential form.'], cap: `${b}${supT(kk)} = ${B}` }),
          st('mv11', q, q, { alts: [alt(`${ptext([F(B), F(p), F(1)], true)} = 0`, `Subtracting ${B} gives ${MINUS} ${B}.`)], why: ['Distribute and make one side 0.'], cap: `Distribute, then ${MINUS} ${B}` }),
          st('fac11', fct, fct, { alts: [alt(`(${xm(-r)})(${xm(-r2)}) = 0`, 'The signs are reversed.')], why: [`Two numbers that multiply to ${M_(-B)} and add to ${M_(p)}.`], cap: 'Factor' }),
          st('zp11', `${X} = ${M_(r)} or ${X} = ${M_(r2)}`, `${X} = ${M_(r)} or ${X} = ${M_(r2)}`, { alts: [alt(`${X} = ${M_(-r)} or ${X} = ${M_(-r2)}`, 'Set each factor to 0: the sign changes.')], why: ['Set each factor to 0.'], cap: 'Each factor = 0' }),
          st('chk11', `Reject ${X} = ${M_(r2)}: ${LG(b)}(${M_(r2)}) is undefined`, `${X} = ${M_(r)}`, { alts: [alt(`Reject ${X} = ${M_(r)}: ${LG(b)}(${M_(r)}) is undefined`, `At x = ${r}, both insides are positive (${r} and ${B / r}).`)], rule: [alt('Keep both answers', `Check each one: at x = ${M_(r2)}, ${LG(b).replace(/<[^>]+>/g, '')}(${M_(r2)}) is the log of a negative, which is undefined.`)], why: ['Check each answer in the original equation.'], cap: `x = ${M_(r2)} makes a log of a negative: reject it` }),
        ];
        return { r11: S11('ls', 'logsolve', 'lsolve', 'Solve, then check.', row0, steps, `${X} = ${M_(r)}`), enemy: 'chronoth' };
      }
      // lneq: ln(ax + c) = ln(dx + f)
      const a = rand(2, 5), d = rand(1, 4), c = nz(-9, 9);
      if (a === d) continue;
      const s = rand(-6, 8), f = (a - d) * s + c;
      const bad = a * s + c <= 0;
      if (bad && !chance(0.6)) continue;
      const e1 = lin(a, c), e2 = lin(d, f), in1 = a * s + c, in2 = d * s + f;
      const steps = [
        st('ot11', `${e1} = ${e2}`, `${e1} = ${e2}`, { alts: [alt(`${e1} = ${pw('e', `(${e2})`)}`, 'Both sides are ln: same log means the insides are equal.'), alt(`${e1} ${MINUS} (${e2}) = 1`, 'ln A = ln B means A = B.')], rule: [alt(`ln(${e1} ${MINUS} (${e2})) = 0`, 'ln A − ln B is ln(A/B), not ln(A − B). Here ln A = ln B just means A = B.')], why: ['Same log on both sides: the insides are equal.'], cap: 'Same log: the insides are equal' }),
        st('sv11', `${X} = ${M_(s)}`, `${X} = ${M_(s)}`, { alts: [alt(`${X} = ${M_(-s)}`, 'Collect x on one side and the numbers on the other.'), alt(`${X} = ${M_(s + 1)}`, 'Check the arithmetic.')], why: ['Get x alone.'], cap: 'Get x alone' }),
        bad
          ? st('chk11', `Reject ${X} = ${M_(s)}: ln(${M_(in1)}) is undefined`, 'No solution', { alts: [alt(`Keep ${X} = ${M_(s)}`, `At x = ${M_(s)} the inside is ${M_(in1)}: a log of ${in1 === 0 ? '0' : 'a negative'} is undefined.`)], rule: [alt('Done: no check needed', 'A log equation needs a check: here the insides come out as ' + M_(in1) + '.')], why: ['Check it in the original.'], cap: `The inside is ${M_(in1)}: undefined` })
          : st('chk11', `Keep ${X} = ${M_(s)}: ln(${in1}) = ln(${in2}) ✓`, `${X} = ${M_(s)}`, { alts: [alt(`Reject ${X} = ${M_(s)}`, `Both insides are ${in1}, which is positive.`)], rule: [alt('Done: no check needed', 'A log equation needs a check: the insides must be positive.')], why: ['Check it in the original.'], cap: `Both insides are ${in1}: positive` }),
      ];
      return { r11: S11('ls', 'logsolve', 'lsolve', 'Solve, then check.', `ln(${e1}) = ln(${e2})`, steps, bad ? 'No solution' : `${X} = ${M_(s)}`), enemy: 'chronoth' };
    }
    return genSolve('exp', tut);
  }

  // ================================================================ graph (growth or decay)
  function graph(e) {
    if (!e.gr) return;
    const { a, b } = e.gr;
    drawCurves({ win: { x0: -4, x1: 4, y0: -1, y1: 7 }, qid: 'gr' + e.qid, curves: [{ f: x => a * b ** x, cls: '', key: 'c' }] });
  }

  const PR = {
    grow: ['Model it, then work it out.', 'Choose the model and evaluate.', 'Write the model and find the value.'],
    id: ['Growth or decay?', 'Read the base.', 'Classify the function.'],
    same: ['Solve by matching the bases.', 'Solve.', 'Write both sides with the same base, then solve.'],
    toexp: ['Rewrite in exponential form.', 'Write it as a power.', 'Rewrite as an exponential equation.'],
    tolog: ['Rewrite in log form.', 'Write it as a logarithm.', 'Rewrite as a log equation.'],
    eval: ['Evaluate the log.', 'Find the value.', 'Evaluate.'],
    solve: ['Solve for x.', 'Solve.', 'Find x.'],
    inv: ['Simplify.', 'Use the inverse property.', 'Evaluate.'],
    expand: ['Expand, then simplify.', 'Write as a sum and difference of logs.', 'Expand the log.'],
    condense: ['Write as a single log.', 'Condense.', 'Combine into one log.'],
    cob: ['Use the change of base formula.', 'Evaluate to 2 decimal places.', 'Change the base.'],
    lsolve: ['Solve.', 'Solve. Check your answer.', 'Find x.'],
  };
  const GENS = { expgrow: genGrow, samebase: genSame, logdef: genLog, logprop: genProp, logsolve: genSolve };
  const HARD = { expgrow: ['compound', 'cont', 'half'], samebase: ['both', 'root', 'quad'], logdef: ['evalfrac', 'solvebase', 'solve'], logprop: ['expand', 'condense', 'cob'], logsolve: ['logsum', 'lneq', 'exp'] };
  const bossLast = mine => (mine.includes('logsolve') ? genSolve('logsum') : mine.includes('logprop') ? genProp('expand') : mine.includes('logdef') ? genLog('solvebase') : mine.includes('samebase') ? genSame('both') : genGrow('compound'));
  const HOME = {};

  const spec = {
    act: 11, sk: 'k11', key: 'r11', tag: 'a11', ...SC.spec, graph, PR, HOME, gens: GENS, hard: HARD, elite: 'sandwraith', boss: 'timekeeper', bossLast,
    skills: [
      { id: 'expgrow', stage: 48, act: 11, name: 'Growth and decay', cases: GROW_CASES, gen: cycled('expgrow', c => genGrow(c)),
        title: 'Stage 48: Exponential growth and decay',
        intro: 'A quantity that changes by the same percent each step is exponential: amount = start × (growth factor)ᵗ. Growing by 5% multiplies by 1.05; losing 12% multiplies by 0.88. A half-life multiplies by ½ once per half-life. Compound interest: A = P(1 + r/n)ⁿᵗ. Continuous: A = Peʳᵗ.',
        example: '2000 people, +5% a year, 3 years<br>P = 2000(1.05)ᵗ → 2000(1.05)³ ≈ 2315',
        tutorial: [() => genGrow('grow', true), () => genGrow('identify', true)] },
      { id: 'samebase', stage: 49, act: 11, name: 'Same-base equations', cases: SAME_CASES, gen: cycled('samebase', c => genSame(c)),
        title: 'Stage 49: Exponential equations with the same base',
        intro: 'Write both sides as powers of the same base. Then the exponents must be equal, and you solve that equation. 32 = 2⁵, 1/27 = 3⁻³, √5 = 5^½. A power of a power multiplies the exponents: (2²)ˣ = 2²ˣ.',
        example: '2ˣ⁺¹ = 32<br>32 = 2⁵ → x + 1 = 5 → x = 4',
        tutorial: [() => genSame('basic', true), () => genSame('frac', true)] },
      { id: 'logdef', stage: 50, act: 11, name: 'Logarithms', cases: LOG_CASES, gen: cycled('logdef', c => genLog(c)),
        title: 'Stage 50: What a logarithm is',
        intro: 'A logarithm is an exponent. logᵦ N = k means bᵏ = N: "b to what power gives N?" log with no base is base 10; ln is base e. A log and a power of the same base undo each other: ln eᵏ = k. A log base must be positive and not 1.',
        example: 'log₂ 8 = ?<br>2^? = 8 → 8 = 2³ → log₂ 8 = 3',
        tutorial: [() => genLog('toexp', true), () => genLog('eval', true)] },
      { id: 'logprop', stage: 51, act: 11, name: 'Log properties', cases: PROP_CASES, gen: cycled('logprop', c => genProp(c)),
        title: 'Stage 51: Properties of logarithms',
        intro: 'Product: log(MN) = log M + log N. Quotient: log(M/N) = log M − log N. Power: log(Mᵖ) = p·log M. Use them to expand one log into several, or to condense several into one. There is no rule for log(M + N). Change of base: logᵦ N = ln N ÷ ln b.',
        example: 'log₂(8x) = log₂ 8 + log₂ x = 3 + log₂ x',
        tutorial: [() => genProp('product', true), () => genProp('condense', true)] },
      { id: 'logsolve', stage: 52, act: 11, name: 'Solving with logs', cases: SOLVE_CASES, gen: cycled('logsolve', c => genSolve(c)),
        title: 'Stage 52: Solving exponential and log equations',
        intro: 'Unknown in an exponent: get the power alone, take the log (or ln) of both sides, and the power rule brings x down. Unknown inside a log: rewrite in exponential form. Then check every answer: the inside of each log must be positive, so an answer that makes it 0 or negative is rejected.',
        example: '3ˣ = 20 → log 3ˣ = log 20 → x·log 3 = log 20 → x = log 20/log 3 ≈ 2.73',
        tutorial: [() => genSolve('exp', true), () => genSolve('logeq', true)] },
    ],
    enemies: {
      sandling:  { name: 'Sandling',     rank: 'Normal', color: '#f4d58d', size: 84 },
      tickling:  { name: 'Tickling',     rank: 'Normal', color: '#bf8b67', size: 84 },
      glassmite: { name: 'Glassmite',    rank: 'Normal', color: '#a8dadc', size: 84 },
      quillwisp: { name: 'Quillwisp',    rank: 'Normal', color: '#e9c46a', size: 84 },
      chronoth:  { name: 'Chronoth',     rank: 'Normal', color: '#90be6d', size: 84 },
      sandwraith: { name: 'The Sand Wraith', rank: 'Elite', color: '#d4a373', size: 100, horns: true },
      timekeeper: { name: 'The Timekeeper',  rank: 'Boss',  color: '#ffd166', size: 120, crown: true },
    },
    actInfo: { name: 'The Hourglass Vault', sub: 'Exponentials and logarithms', boss: 'The Timekeeper', firstSkill: 'expgrow',
      blurb: 'In the Hourglass Vault, sand falls by percents. Model growth and decay, match bases, read logs as exponents, and pull x down from the exponent. Defeat The Timekeeper.',
      cleared: () => `The Timekeeper's hourglass shatters and time runs forward again. ${KT.nextActText(11)}` },
    icons: {
      mdl11:  { name: 'Choose the model', svg: svgI('<path d="M4 20c4 0 8-2 10-8s4-8 6-8"/><path d="M4 4v16h16" stroke-width="1.8"/>') },
      calc11: { name: 'Work it out', svg: svgI('<rect x="5" y="3" width="14" height="18" rx="2"/><path d="M8 7h8M8 12h2M14 12h2M8 16h2M14 16h2"/>') },
      pct11:  { name: 'Read the rate (percent)', svg: svgI('<circle cx="7" cy="7" r="2.5"/><circle cx="17" cy="17" r="2.5"/><path d="M19 5L5 19"/>') },
      pow11:  { name: 'Rewrite as a power of the base', svg: svgI('<path d="M4 18l5-10 5 10"/><path d="M15 4h5l-5 6h5" stroke-width="2"/>') },
      pr11:   { name: 'Power rule (exponents multiply / come down)', svg: svgI('<path d="M6 6l12 12M18 6L6 18" stroke-width="2"/><path d="M15 3h5v5" stroke-width="1.8"/>') },
      mt11:   { name: 'Match the exponents', svg: svgI('<path d="M4 9h16M4 15h16"/><path d="M8 4l-2 3M18 4l-2 3" stroke-width="1.8"/>') },
      sv11:   { name: 'Solve for x', svg: svgI('<path d="M5 5l6 6M11 5l-6 6"/><path d="M14 16h6M14 20h6"/>') },
      mv11:   { name: 'Move everything to one side', svg: svgI('<path d="M4 12h12M12 7l5 5-5 5"/><path d="M20 6v12"/>') },
      exp11:  { name: 'Exponential form', svg: svgI('<path d="M5 18V8h6M5 13h5"/><path d="M14 4h6M17 4v7" stroke-width="1.8"/>') },
      log11:  { name: 'Logarithm', svg: svgI('<path d="M4 4v14h5"/><circle cx="14" cy="14" r="3.5"/><path d="M19 11v9c0 2-2 2-3 2" stroke-width="1.8"/>') },
      root11: { name: 'Square root of both sides', svg: svgI('<path d="M3 13l3 0 3 7 4-16h8"/>') },
      lp11:   { name: 'Expand the log', svg: svgI('<path d="M12 4v6M12 10l-6 8M12 10l6 8"/>') },
      lc11:   { name: 'Condense into one log', svg: svgI('<path d="M6 4l6 8 6-8M12 12v8"/>') },
      cob11:  { name: 'Change of base', svg: svgI('<path d="M4 12h16"/><path d="M8 8h8M8 16h8" stroke-width="1.8"/><path d="M4 5l3 3-3 3" stroke-width="1.6"/>') },
      div11:  { name: 'Divide both sides', svg: svgI('<path d="M5 12h14"/><circle cx="12" cy="6.5" r="1.6"/><circle cx="12" cy="17.5" r="1.6"/>') },
      as11:   { name: 'Add or subtract on both sides', svg: svgI('<path d="M4 8h8M8 4v8M13 17h7"/>') },
      chk11:  { name: 'Check the answer (a log needs a positive inside)', svg: svgI('<path d="M4 13l5 5L20 6"/>') },
    },
    css: KT.SCRIPT_CSS,
  };
  const A = KT.makeAct(spec);
  SC.bind(A);
  KT.install(spec, A);
})();
