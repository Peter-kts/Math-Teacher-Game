// Debug menu for testing: jump to any part of any act (a stage's tutorial, a fight of one stage, one exact
// problem type, any node on the run map, the elite, or one boss phase), auto-solve a fight, refill HP.
// Shown on the dev preview (/dev/), when opened as a local file, or with ?debug=1 in the URL.
// Kept in its own file so the game code doesn't depend on it. Everything is read from ACTS and SKILLS,
// so a new act (act5.js etc.) shows up here on its own once it registers its stages.
(function () {
  const on = location.protocol === 'file:' || /\/dev\//.test(location.pathname) || /[?&]debug=1/.test(location.search);
  if (!on) return;

  const css = document.createElement('style');
  css.textContent = `
    #dbgBtn { position:absolute; left:4px; top:4px; z-index:5; font-size:11px; line-height:1; padding:6px 8px; min-height:0; background:#ef476f; color:#000; border:2px solid #000; opacity:.85; touch-action:manipulation; }
    #dbgPanel { text-align:left; }
    #dbgPanel h1 { text-align:center; }
    #dbgPanel h2 { margin:8px 0 4px; font-size:15px; }
    #dbgPanel p { font-size:13px; }
    #dbgPanel details { border:2px solid #0006; border-radius:8px; margin:6px 0; padding:4px 8px; background:#0002; }
    #dbgPanel summary { cursor:pointer; font-weight:bold; padding:6px 0; font-size:15px; }
    #dbgPanel .grid { display:flex; flex-wrap:wrap; gap:6px; margin:2px 0 8px; }
    #dbgPanel .grid button { font-size:13px; padding:6px 10px; min-height:34px; }
    #dbgPanel .grid button.case { font-size:12px; padding:4px 8px; font-weight:normal; }
    #dbgPanel .stage { margin:4px 0 2px; font-size:13px; font-weight:bold; opacity:.9; }
    #dbgPanel .sub { font-size:12px; opacity:.75; margin:0 0 2px; }
  `;
  document.head.appendChild(css);
  const btn = document.createElement('button');
  btn.id = 'dbgBtn'; btn.textContent = 'Debug';
  ($('arena') || document.body).appendChild(btn);   // top-left corner of the arena, which is always empty

  const acts = () => (typeof ACTS !== 'undefined' ? Object.keys(ACTS).map(Number).sort((a, b) => a - b) : [1]);
  const actOfSkill = id => SKILL[id].act || 1;
  const layout = () => (typeof ACT1_LAYOUT !== 'undefined' ? ACT1_LAYOUT : ['fight', 'elite', 'boss']);
  const icon = t => (typeof NODE_ICON !== 'undefined' && NODE_ICON[t]) || '';
  const esc = s => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
  const allIds = () => SKILLS.map(s => s.id);

  function unlockAll() { progress.unlocked = allIds(); saveProgress(); renderSkills(); }
  function resetScreen() {
    if (typeof waiting !== 'undefined') waiting = false;
    $('next').classList.remove('show');
    if (typeof clearNotes === 'function') clearNotes();
    const c = $('celebrate'); if (c) c.innerHTML = '';
    hideOverlay();
  }

  // Runs fn as if a run of `act` were going with every stage unlocked, then puts everything back.
  // Used to count boss phases and to write sample problems without touching the player's save or run.
  function asIfRun(act, fn) {
    const saved = { run, unlocked: progress.unlocked, queues: { ...caseQueues } };
    run = { act, nodes: [], i: 0 };
    progress.unlocked = allIds();
    try { return fn(); } catch (e) { return undefined; }
    finally {
      run = saved.run; progress.unlocked = saved.unlocked;
      for (const k of Object.keys(caseQueues)) delete caseQueues[k];
      Object.assign(caseQueues, saved.queues);
    }
  }

  // A short readable sample of one problem type, e.g. "4x + 10 = 30". Numbers change in the real fight.
  function sampleOf(id, c) {
    return asIfRun(actOfSkill(id), () => {
      caseQueues[id] = [c];
      const g = SKILL[id].gen();
      const k = Object.keys(ENGINES).find(k => g[k]);
      if (!k) return c;
      let t = String(ENGINES[k].text(g[k])).replace(/<[^>]*>/g, '').replace(/\s+/g, ' ').trim();
      if (k === 'fn') {   // Act 4's text is a key for the variety check, so make it read like the problem
        t = t.replace(/^eval (.*) @(.+)$/, '$1, x = $2').replace(/^eval (.*) @$/, '$1')
          .replace(/^formula (.*) for (\w+)$/, '$1, for $2').replace(/^fin /, '')
          .replace(/^slope pts /, 'slope of ').replace(/^slope graph .*/, 'slope from a graph')
          .replace(/^slope \w+ /, 'slope of ').replace(/^line (\w+) .*/, 'line: ' + c).replace(/^icept /, 'intercepts of ');
      }
      return t.length > 34 ? t.slice(0, 32) + '…' : t;
    }) || c;
  }

  // How many phases this act's elite and boss have (they can depend on how many stages are unlocked: all, when jumping).
  const phaseCount = (act, type) => asIfRun(act, () => buildFight({ type }).phases.length) || 1;

  // Starts a fresh run of an act at one spot, with every stage unlocked.
  //   where.node  = index into the run map,   where.tutorial = a stage id,
  //   where.skill = a fight of that stage only (and where.case = one exact problem type),
  //   where.type  = 'elite' | 'boss' (where.phase = start at that phase).
  function jump(act, where) {
    unlockAll();
    resetScreen();
    startRun(act, typeof difficulty !== 'undefined' ? difficulty.level : undefined);
    resetScreen();
    run.nodes = layout().map(type => ({ type }));
    if (where.tutorial) { run.nodes.unshift({ type: 'tutorial', skill: where.tutorial }); run.i = 0; }
    else if (where.skill) {
      run.i = 0;
      run.nodes[0] = { type: 'fight', skill: where.skill };
      if (where.case) caseQueues[where.skill] = [where.case];   // the next equation of this stage is this type
    }
    else if (where.node != null) run.i = Math.min(where.node, run.nodes.length - 1);
    else {
      run.i = Math.max(0, run.nodes.findIndex(n => n.type === where.type));
      if (where.phase) run.nodes[run.i].startPhase = where.phase;
    }
    hp = MAX_HP; updateHud();
    startNode();
  }
  // Closing the debug menu goes back to the title if no run is going yet, so the screen isn't left empty.
  const close = () => { if (run) hideOverlay(); else showTitle(); };
  // Sets the difficulty for debug jumps and the next run (and unlocks it).
  function setLevel(lvl) {
    progress.levelUnlocked = Math.max(progress.levelUnlocked, lvl); saveProgress();
    difficulty = DIFFICULTIES[lvl];
    try { localStorage.setItem('algebraCards.difficulty', String(lvl)); } catch (e) {}
    open();
  }
  function autoSolve() {
    if (!cur || (typeof waiting !== 'undefined' && waiting)) return;
    hideOverlay(); busy = true; equationSolved();
  }

  let openAct = null;   // which act's section stays open between visits to the menu
  function actSection(a) {
    const info = typeof ACTS !== 'undefined' ? ACTS[a] : null;
    const b = (attrs, label, cls = '') => `<button class="${cls}" ${attrs}>${label}</button>`;
    const map = layout().map((t, i) => b(`data-a="${a}" data-node="${i}"`, `${icon(t)} ${i + 1}`)).join('');
    const stages = SKILLS.filter(s => actOfSkill(s.id) === a).map(s => {
      const cases = (s.cases || []).map(c => b(`data-a="${a}" data-skill="${s.id}" data-case="${esc(c)}" title="${esc(c)}"`, esc(sampleOf(s.id, c)), 'case ghost')).join('');
      return `<div class="stage">${s.stage}. ${esc(s.name)}</div><div class="grid">
        ${b(`data-a="${a}" data-tut="${s.id}"`, `${icon('tutorial')} Tutorial`)}
        ${b(`data-a="${a}" data-skill="${s.id}"`, `${icon('fight')} Fight`)}${cases}</div>`;
    }).join('');
    const phases = type => {
      const n = phaseCount(a, type);
      if (n < 2) return '';
      return Array.from({ length: n - 1 }, (_, i) => b(`data-a="${a}" data-type="${type}" data-phase="${i + 1}"`, `Phase ${i + 2}`, 'ghost')).join('');
    };
    return `<details data-act="${a}" ${openAct === a ? 'open' : ''}>
      <summary>Act ${a}${info ? ': ' + esc(info.name) : ''}</summary>
      <h2>Run map</h2><p class="sub">Start the run at any node; the run carries on from there.</p><div class="grid">${map}</div>
      <h2>Stages</h2><p class="sub">Tutorial, a fight of just that stage, or one exact problem type (numbers change each time).</p>${stages}
      <h2>Elite and boss</h2><div class="grid">
        ${b(`data-a="${a}" data-type="elite"`, `${icon('elite')} Elite`)}${phases('elite')}</div><div class="grid">
        ${b(`data-a="${a}" data-type="boss"`, `${icon('boss')} Boss${info && info.boss ? ': ' + esc(info.boss) : ''}`)}${phases('boss')}</div>
    </details>`;
  }

  function open() {
    if (openAct == null) openAct = run ? run.act : acts()[0];
    const diffRow = typeof DIFFICULTIES === 'undefined' ? '' : `<h2>Difficulty for jumps</h2><div class="grid">` +
      DIFFICULTIES.map(d => `<button data-lvl="${d.level}" class="${d.level === difficulty.level ? '' : 'ghost'}">${d.name}</button>`).join('') + '</div>';
    showOverlay(`<div id="dbgPanel"><h1>Debug</h1>
      <p>Jumping unlocks every stage and starts a new run at that spot, at the difficulty picked here (tutorials stay on Easy). Auto-solve counts as a clean solve, so it also raises mastery.</p>
      ${diffRow}${acts().map(actSection).join('')}</div>`, [
      ['Auto-solve this fight', autoSolve],
      ['Unlock all difficulties', () => { progress.levelUnlocked = 3; saveProgress(); close(); }, true],
      ['Refill HP', () => { hp = MAX_HP; updateHud(); close(); }, true],
      ['Close', close, true],
    ]);
    const panel = $('dbgPanel');
    panel.querySelectorAll('details').forEach(d => d.addEventListener('toggle', () => {
      if (!d.open) return;
      openAct = +d.dataset.act;
      panel.querySelectorAll('details').forEach(o => { if (o !== d) o.open = false; });   // one act open at a time keeps it short on phones
    }));
    panel.addEventListener('click', e => {
      const l = e.target.closest('button[data-lvl]'); if (l) return setLevel(+l.dataset.lvl);
      const t = e.target.closest('button[data-a]'); if (!t) return;
      const d = t.dataset, a = +d.a;
      openAct = a;
      if (d.tut) jump(a, { tutorial: d.tut });
      else if (d.skill) jump(a, { skill: d.skill, case: d.case });
      else if (d.node != null) jump(a, { node: +d.node });
      else jump(a, { type: d.type, phase: d.phase ? +d.phase : 0 });
    });
  }
  btn.addEventListener('click', e => { e.stopPropagation(); open(); });
  // The corner button sits under menus, so the title screen gets its own Debug button.
  const baseTitle = showTitle;
  showTitle = function () {
    baseTitle.apply(this, arguments);
    const row = document.querySelector('#overPanel .buttons'); if (!row) return;
    const b = document.createElement('button'); b.className = 'ghost'; b.textContent = 'Debug';
    b.addEventListener('click', open); row.appendChild(b);
  };
  if ($('over').classList.contains('show') && !run) showTitle();
})();
