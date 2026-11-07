// =====================================================================
//  Sound effects: small tones made with Web Audio (no sound files).
//  SFX.solved()  a solve; picks a chime, a bigger "enemy down" chord, or a boss fanfare
//  SFX.wrong()   a wrong move
//  SFX.lost()    out of HP
//  A speaker button in the header mutes everything; the choice is saved in localStorage.
// =====================================================================
window.SFX = (() => {
  const KEY = 'sfxMuted';
  let muted = false;
  try { muted = localStorage.getItem(KEY) === '1'; } catch (e) {}
  let ctx = null, master = null;

  // Browsers only allow audio after a user gesture, so the context is made (or resumed) on the first tap.
  function audio() {
    if (!ctx) {
      const AC = window.AudioContext || window.webkitAudioContext;
      if (!AC) return null;
      ctx = new AC();
      master = ctx.createGain(); master.gain.value = 0.35; master.connect(ctx.destination);
    }
    if (ctx.state === 'suspended') ctx.resume();
    return ctx;
  }
  window.addEventListener('pointerdown', audio, { capture: true });
  window.addEventListener('keydown', audio, { capture: true });

  const hz = n => 440 * Math.pow(2, (n - 69) / 12);   // MIDI note number to frequency

  // One note: a quick attack and a smooth fade, optionally sliding to another pitch.
  function tone(note, at, dur, { type = 'triangle', vol = 0.5, slide = null } = {}) {
    const t = ctx.currentTime + at;
    const o = ctx.createOscillator(), g = ctx.createGain();
    o.type = type; o.frequency.setValueAtTime(hz(note), t);
    if (slide !== null) o.frequency.exponentialRampToValueAtTime(hz(slide), t + dur);
    g.gain.setValueAtTime(0.0001, t);
    g.gain.exponentialRampToValueAtTime(vol, t + 0.012);
    g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    o.connect(g); g.connect(master);
    o.start(t); o.stop(t + dur + 0.05);
  }
  // A few high, quiet sparkles to go with the confetti.
  function sparkle(at, count = 5) {
    const notes = [96, 100, 103, 108, 105, 101];
    for (let i = 0; i < count; i++) tone(notes[i % notes.length], at + i * 0.05 + Math.random() * 0.02, 0.18, { type: 'sine', vol: 0.12 });
  }
  function play(fn) {
    if (muted || !audio()) return;
    try { fn(); } catch (e) {}
  }

  // C major: a rising three-note chime for a solved equation.
  const chime = () => {
    [72, 76, 79].forEach((n, i) => tone(n, i * 0.08, 0.32, { vol: 0.45 }));
    tone(84, 0.24, 0.5, { type: 'sine', vol: 0.3 });
    sparkle(0.2, 4);
  };
  // The last equation of a fight: a longer run that lands on a held chord.
  const enemyDown = () => {
    [72, 76, 79, 84].forEach((n, i) => tone(n, i * 0.075, 0.3, { vol: 0.42 }));
    [76, 79, 84, 88].forEach(n => tone(n, 0.32, 0.8, { vol: 0.2 }));
    tone(48, 0.32, 0.6, { type: 'sine', vol: 0.3 });
    sparkle(0.35, 6);
  };
  // A boss falls: a short fanfare.
  const fanfare = () => {
    const seq = [[67, 0, 0.14], [67, 0.15, 0.14], [67, 0.3, 0.14], [72, 0.45, 0.5], [70, 0.95, 0.16], [72, 1.12, 0.9]];
    seq.forEach(([n, t, d]) => { tone(n, t, d, { type: 'square', vol: 0.18 }); tone(n + 12, t, d, { vol: 0.2 }); });
    [60, 64, 67].forEach(n => tone(n, 1.12, 1.1, { vol: 0.22 }));
    tone(36, 1.12, 1.0, { type: 'sine', vol: 0.35 });
    sparkle(1.15, 6);
  };

  function solved() {
    play(() => {
      const dead = document.getElementById('enemyBox')?.classList.contains('dead');
      const boss = typeof fight !== 'undefined' && fight && fight.node && fight.node.type === 'boss';
      (dead ? (boss ? fanfare : enemyDown) : chime)();
    });
  }
  // A low, short "bonk" that slides down.
  function wrong() {
    play(() => {
      tone(50, 0, 0.22, { type: 'square', vol: 0.16, slide: 43 });
      tone(38, 0, 0.25, { type: 'sine', vol: 0.4, slide: 31 });
    });
  }
  function lost() {
    play(() => [67, 63, 60, 55].forEach((n, i) => tone(n, i * 0.22, i === 3 ? 0.9 : 0.24, { vol: 0.35 })));
  }

  // The mute button, put into the header next to Stats.
  function setMuted(v) {
    muted = v;
    try { localStorage.setItem(KEY, v ? '1' : '0'); } catch (e) {}
    const b = document.getElementById('sfxBtn'); if (!b) return;
    b.textContent = v ? '🔇' : '🔊';
    b.title = v ? 'Sound off (tap to turn on)' : 'Sound on (tap to mute)';
    b.setAttribute('aria-label', b.title);
    b.classList.remove('pop'); void b.offsetWidth; b.classList.add('pop');
  }
  function addButton() {
    const header = document.querySelector('#app header'); if (!header || document.getElementById('sfxBtn')) return;
    const st = document.createElement('style');
    st.textContent = `#sfxBtn { min-width:40px; } #sfxBtn.pop { animation: sfxPop .25s; }
      @keyframes sfxPop { 50% { transform: scale(1.18); } }`;
    document.head.appendChild(st);
    const b = document.createElement('button');
    b.id = 'sfxBtn'; b.className = 'topbtn ghost';
    b.addEventListener('click', () => { setMuted(!muted); if (!muted) play(() => tone(79, 0, 0.15, { vol: 0.35 })); });
    header.insertBefore(b, document.getElementById('statsBtn'));
    setMuted(muted);
    b.classList.remove('pop');
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', addButton); else addButton();

  return { solved, wrong, lost, isMuted: () => muted, setMuted };
})();
