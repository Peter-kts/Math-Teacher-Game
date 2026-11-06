// Debug menu for testing: jump to any act, stage, elite or boss, auto-solve a fight, refill HP.
// Shown on the dev preview (/dev/), when opened as a local file, or with ?debug=1 in the URL.
// Kept in its own file so the game code doesn't depend on it.
(function () {
  const on = location.protocol === 'file:' || /\/dev\//.test(location.pathname) || /[?&]debug=1/.test(location.search);
  if (!on) return;

  const css = document.createElement('style');
  css.textContent = `
    #dbgBtn { position:fixed; left:8px; bottom:8px; z-index:30; font-size:12px; padding:4px 8px; background:#ef476f; color:#000; border:2px solid #000; opacity:.85; }
    #dbgPanel h2 { margin:6px 0 0; }
    #dbgPanel .grid { display:flex; flex-wrap:wrap; gap:6px; }
    #dbgPanel .grid button { font-size:13px; padding:6px 10px; }
  `;
  document.head.appendChild(css);
  const btn = document.createElement('button');
  btn.id = 'dbgBtn'; btn.textContent = 'Debug';
  document.body.appendChild(btn);

  const acts = () => (typeof ACTS !== 'undefined' ? Object.keys(ACTS).map(Number) : [1]);
  const actOfSkill = id => SKILL[id].act || 1;
  const layout = () => (typeof ACT1_LAYOUT !== 'undefined' ? ACT1_LAYOUT : ['fight', 'elite', 'boss']);

  function unlockAll() { progress.unlocked = SKILLS.map(s => s.id); saveProgress(); renderSkills(); }
  function resetScreen() {
    if (typeof waiting !== 'undefined') waiting = false;
    $('next').classList.remove('show');
    if (typeof clearNotes === 'function') clearNotes();
    const c = $('celebrate'); if (c) c.innerHTML = '';
    hideOverlay();
  }
  // Starts a fresh run of an act and jumps straight to one node: a stage's tutorial, a normal fight, an elite or the boss.
  function jump(act, node) {
    unlockAll();
    resetScreen();
    (typeof startRun === "function" ? startRun : newRun)(act);
    resetScreen();
    run.nodes = layout().map(type => ({ type }));
    if (node.type === 'tutorial') { run.nodes.unshift(node); run.i = 0; }
    else run.i = Math.max(0, run.nodes.findIndex(n => n.type === node.type));
    hp = MAX_HP; updateHud();
    startNode();
  }
  function autoSolve() {
    if (!cur || (typeof waiting !== 'undefined' && waiting)) return;
    hideOverlay(); busy = true; equationSolved();
  }

  function open() {
    const rows = acts().map(a => {
      const stages = SKILLS.filter(s => actOfSkill(s.id) === a)
        .map(s => `<button data-a="${a}" data-t="tutorial" data-s="${s.id}">${s.stage}. ${s.name}</button>`).join('');
      return `<h2>Act ${a}${typeof ACTS !== 'undefined' ? ': ' + ACTS[a].name : ''}</h2>
        <div class="grid">${stages}
          <button data-a="${a}" data-t="fight">Normal fight</button>
          <button data-a="${a}" data-t="elite">Elite</button>
          <button data-a="${a}" data-t="boss">Boss</button></div>`;
    }).join('');
    showOverlay(`<div id="dbgPanel"><h1>Debug</h1>
      <p>Jumping unlocks every stage and starts a new run at that spot. Auto-solve counts as a clean solve, so it also raises mastery.</p>
      ${rows}</div>`, [
      ['Auto-solve this fight', autoSolve],
      ['Unlock all difficulties', () => { progress.levelUnlocked = 3; saveProgress(); hideOverlay(); }, true],
      ['Refill HP', () => { hp = MAX_HP; updateHud(); hideOverlay(); }, true],
      ['Close', hideOverlay, true],
    ]);
    $('dbgPanel').addEventListener('click', e => {
      const b = e.target.closest('button[data-t]'); if (!b) return;
      jump(+b.dataset.a, b.dataset.t === 'tutorial' ? { type: 'tutorial', skill: b.dataset.s } : { type: b.dataset.t });
    });
  }
  btn.addEventListener('click', e => { e.stopPropagation(); open(); });
})();
