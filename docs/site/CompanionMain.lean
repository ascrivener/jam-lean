import VersoManual
import Companion

open Verso.Genre Manual

/-- Layout fixes: code blocks and the chapters' tables keep their layout and scroll sideways inside
    their own box, with a visible scrollbar and a shadow at the edge that has more to see; display
    math scrolls inside its own box on narrow screens; and the header title keeps clear of the
    search box (which Verso places over the header): the title wrapper reserves the search bar's
    width, the search bar is narrower below 1200 px, and the title wraps and shrinks on narrow
    screens. The sidebar lists sections only: the entry Verso adds for each quoted declaration
    (`{mathdoc}`, `{docstring}`) is hidden. -/
def narrowCss : Verso.Genre.Manual.CSS := ⟨"
.semantics, pre, code.hl.lean.block { max-width: 100%; overflow-x: auto; white-space: pre;
  scrollbar-width: thin; scrollbar-color: #b0b0b0 transparent; }
main table { display: block; max-width: 100%; width: max-content; overflow-x: auto;
  scrollbar-width: thin; scrollbar-color: #b0b0b0 transparent; }
.semantics::-webkit-scrollbar, pre::-webkit-scrollbar, code.hl.lean.block::-webkit-scrollbar,
main table::-webkit-scrollbar { height: 8px; }
.semantics::-webkit-scrollbar-thumb, pre::-webkit-scrollbar-thumb, code.hl.lean.block::-webkit-scrollbar-thumb,
main table::-webkit-scrollbar-thumb { background: #b0b0b0; border-radius: 4px; }
code.hl.lean.block, .semantics, main table {
  background:
    linear-gradient(to right, #fff 30%, rgba(255,255,255,0)) left / 2em 100% no-repeat local,
    linear-gradient(to left, #fff 30%, rgba(255,255,255,0)) right / 2em 100% no-repeat local,
    radial-gradient(farthest-side at 0 50%, rgba(0,0,0,.22), transparent) left / 12px 100% no-repeat scroll,
    radial-gradient(farthest-side at 100% 50%, rgba(0,0,0,.22), transparent) right / 12px 100% no-repeat scroll; }
.katex-display { max-width: 100%; overflow-x: auto; overflow-y: hidden; }
.header-title-wrapper { box-sizing: border-box; min-width: 0;
  padding-right: calc(var(--search-bar-width, 24rem) + 1.5rem); }
.header-title { font-size: 1.5rem; }
.header-title h1 { text-wrap: wrap !important; white-space: normal !important; line-height: 1.1; }
@media (width <= 1200px) {
  :root { --search-bar-width: 12rem !important; }
  .header-title { font-size: 1.05rem; }
}
@media (width <= 700px) {
  .header-title { font-size: 0.72rem; }
}
@media (width <= 380px) {
  :root { --search-bar-width: 8rem !important; }
}
html, body { overflow-x: clip; }
code.hl.lean.block.collapsed-code { display: block; max-height: 18em; overflow-y: hidden;
  -webkit-mask-image: linear-gradient(to bottom, #000 70%, transparent);
  mask-image: linear-gradient(to bottom, #000 70%, transparent); }
button.show-code { display: block; margin: 0.25em 0 1em; padding: 0.3em 0.8em; font-family: system-ui, sans-serif;
  font-size: 0.9em; cursor: pointer; border: 1px solid #b0b0b0; border-radius: 4px; background: #f6f6f6; }
.lean-toggle { display: flex; flex-wrap: wrap; align-items: center; gap: 0.5em; margin: 0.5em 0 1em;
  font-family: system-ui, sans-serif; font-size: 0.9em; }
.lean-toggle button { min-height: 2.4em; padding: 0.3em 0.9em; font: inherit; cursor: pointer;
  border: 1px solid #b0b0b0; border-radius: 4px; background: #f6f6f6; color: inherit; }
.lean-toggle button[aria-pressed='true'] { background: #dde7f3; border-color: #5a7fa8; font-weight: 600; }
.lean-toggle button:focus-visible, button.show-code:focus-visible { outline: 2px solid #2a6ebb; outline-offset: 2px; }
.lean-toggle .lean-toggle-note { color: #666; }
body.lean-hidden .lean-source, body.lean-hidden code.hl.lean.block,
body.lean-hidden button.show-code { display: none; }
.split-toc li:has(> a[href*='/#JAM___']), .split-toc li:has(> a[href*='/#PVM___']),
.split-toc li:has(> a[href*='/#JamCrypto___']) { display: none; }
"⟩

/-- Long quoted definitions (`{leanSource}` blocks of more than 30 lines) start collapsed to their
    first 12 lines, with a button to show the whole definition; short ones stay open. A page with
    Lean code also gets, under its title, a "Show all Lean / Hide all Lean" switch (remembered in
    `localStorage`, when the browser allows it, for every page). -/
def collapseJs : Verso.Genre.Manual.JS := ⟨"
document.addEventListener('DOMContentLoaded', () => {
  for (const code of document.querySelectorAll('code.hl.lean.block')) {
    const lines = code.textContent.split('\\n').length;
    if (lines <= 30) continue;
    code.classList.add('collapsed-code');
    const btn = document.createElement('button');
    btn.className = 'show-code';
    btn.type = 'button';
    btn.textContent = 'Show the full definition (' + lines + ' lines)';
    btn.addEventListener('click', () => {
      const open = code.classList.toggle('collapsed-code');
      btn.textContent = open ? 'Show the full definition (' + lines + ' lines)' : 'Show less';
    });
    code.insertAdjacentElement('afterend', btn);
  }
  // The page-level switch: show every quoted definition in full, or hide them all. The choice
  // is remembered (per browser) for every page of the book.
  const blocks = document.querySelectorAll('code.hl.lean.block');
  const heading = document.querySelector('main section h1');
  if (!blocks.length || !heading) return;
  const KEY = 'jam-lean-book.lean';
  const load = () => { try { return localStorage.getItem(KEY); } catch (e) { return null; } };
  const save = (v) => { try { v ? localStorage.setItem(KEY, v) : localStorage.removeItem(KEY); } catch (e) {} };
  const bar = document.createElement('div');
  bar.className = 'lean-toggle';
  bar.setAttribute('role', 'group');
  bar.setAttribute('aria-label', 'Lean code on this page');
  const mk = (text, mode) => {
    const b = document.createElement('button');
    b.type = 'button'; b.textContent = text; b.dataset.mode = mode;
    b.setAttribute('aria-pressed', 'false');
    bar.appendChild(b); return b;
  };
  const showAll = mk('Show all Lean', 'all');
  const hideAll = mk('Hide all Lean', 'none');
  const note = document.createElement('span');
  note.className = 'lean-toggle-note';
  note.setAttribute('aria-live', 'polite');
  bar.appendChild(note);
  const apply = (mode) => {
    document.body.classList.toggle('lean-hidden', mode === 'none');
    if (mode === 'all') {
      for (const btn of document.querySelectorAll('button.show-code')) {
        const code = btn.previousElementSibling;
        if (code && code.classList.contains('collapsed-code')) btn.click();
      }
    }
    showAll.setAttribute('aria-pressed', String(mode === 'all'));
    hideAll.setAttribute('aria-pressed', String(mode === 'none'));
    note.textContent = mode === 'none' ? blocks.length + ' Lean block' + (blocks.length === 1 ? '' : 's') + ' hidden' : '';
  };
  for (const b of [showAll, hideAll]) b.addEventListener('click', () => {
    // Pressing the active button again returns to the default (long definitions collapsed).
    const mode = b.getAttribute('aria-pressed') === 'true' ? null : b.dataset.mode;
    if (mode === null && b === showAll) {
      for (const btn of document.querySelectorAll('button.show-code')) {
        const code = btn.previousElementSibling;
        if (code && !code.classList.contains('collapsed-code')) btn.click();
      }
    }
    save(mode); apply(mode);
  });
  heading.insertAdjacentElement('afterend', bar);
  const saved = load();
  if (saved === 'all' || saved === 'none') apply(saved);
});
"⟩

/-- Math in docstrings: `$…$` and `$$…$$` in the text of docstrings (the `.docs` blocks of
    `{docstring}` and `{leanSource}`, and hover tooltips) are rendered with the KaTeX that Verso
    already loads. As in doc-gen4's MathJax
    configuration, code (`code`, `pre`) is skipped, so a literal `$` belongs in backticks. -/
def docMathJs : Verso.Genre.Manual.JS := ⟨"
(() => {
  const re = /\\$\\$([\\s\\S]+?)\\$\\$|\\$([^$\\n]+?)\\$/g;
  const skip = (n) => n.parentElement && n.parentElement.closest('code, pre, .katex, .hl.lean');
  const render = (root) => {
    if (typeof katex === 'undefined') return;
    const walker = document.createTreeWalker(root, NodeFilter.SHOW_TEXT);
    const nodes = [];
    while (walker.nextNode()) {
      const n = walker.currentNode;
      if (!skip(n) && n.nodeValue.includes('$')) nodes.push(n);
    }
    for (const n of nodes) {
      const text = n.nodeValue; let last = 0; let m; const frag = document.createDocumentFragment();
      re.lastIndex = 0;
      while ((m = re.exec(text)) !== null) {
        frag.appendChild(document.createTextNode(text.slice(last, m.index)));
        const span = document.createElement('span');
        katex.render(m[1] !== undefined ? m[1] : m[2], span,
          { throwOnError: false, displayMode: m[1] !== undefined });
        frag.appendChild(span); last = re.lastIndex;
      }
      if (last === 0) continue;
      frag.appendChild(document.createTextNode(text.slice(last)));
      n.parentNode.replaceChild(frag, n);
    }
  };
  // Hover docstrings are Markdown rendered without math spans, so a `_` inside `$…$` may have become
  // <em>. Docstrings use \\ast rather than `*` in math, so inside a math span <em> can only be `_`.
  const renderHover = (root) => {
    if (typeof katex === 'undefined') return;
    const span = /\\$\\$([\\s\\S]+?)\\$\\$|\\$([^$]+?)\\$/g;
    const decode = (h) => { const t = document.createElement('textarea'); t.innerHTML = h; return t.value; };
    for (const el of root.querySelectorAll('.docstring p, .docstring li')) {
      el.innerHTML = el.innerHTML.replace(span, (whole, d, i) => {
        const body = d !== undefined ? d : i;
        if (body.includes('<code')) return whole;
        const tex = decode(body.replace(/<\\/?em>/g, '_').replace(/<[^>]+>/g, ''));
        return katex.renderToString(tex, { throwOnError: false, displayMode: d !== undefined });
      });
    }
  };
  document.addEventListener('DOMContentLoaded', () => {
    for (const root of document.querySelectorAll('.docs')) render(root);
    // Hover tooltips are created on demand: render their docstrings when they appear.
    new MutationObserver((records) => {
      for (const r of records) for (const n of r.addedNodes)
        if (n.nodeType === 1 && (n.matches('[data-tippy-root], .tippy-box') || n.querySelector('.tippy-box')))
          { renderHover(n); render(n); }
    }).observe(document.body, { childList: true, subtree: true });
  });
})();
"⟩

/-- HTML only, one page per chapter. -/
def config : Config where
  extraCss := ({} : Std.HashSet Verso.Genre.Manual.CSS).insert narrowCss
  extraJs := (({} : Std.HashSet Verso.Genre.Manual.JS).insert docMathJs).insert collapseJs
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1

def main := manualMain (%doc Companion) (config := { config with })
