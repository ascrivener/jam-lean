import VersoManual
import Companion

open Verso.Genre Manual

/-- Layout fixes: code blocks and the chapters' tables keep their layout and scroll sideways inside
    their own box, with a visible scrollbar and a shadow at the edge that has more to see; display
    math scrolls inside its own box on narrow screens; and the header title keeps clear of the
    search box (which Verso places over the header): the title wrapper reserves the search bar's
    width, the search bar is narrower below 1200 px, and the title wraps and shrinks on narrow
    screens. The sidebar lists sections only: the entry Verso adds for each quoted declaration
    (`{mathdoc}`, `{docstring}`) is hidden. The worked-example boxes (`{example}`,
    `Companion/Example.lean`) are styled here too; their tables scroll inside the box. -/
def narrowCss : Verso.Genre.Manual.CSS := ⟨"
:root { --jl-bg: #fff; --jl-bg-clear: rgba(255,255,255,0); --jl-edge-shadow: rgba(0,0,0,.22);
  --jl-scroll: #b0b0b0; --jl-button-bg: #f6f6f6; --jl-button-border: #b0b0b0; --jl-pressed-bg: #dde7f3;
  --jl-pressed-border: #5a7fa8; --jl-focus: #2a6ebb; --jl-muted: #666;
  --jl-example-bg: #f7f9fc; --jl-example-border: #c9d4e3; --jl-example-accent: #3b6ea8; --jl-example-rule: #dde3ec; }
.semantics, pre, code.hl.lean.block { max-width: 100%; overflow-x: auto; white-space: pre;
  scrollbar-width: thin; scrollbar-color: var(--jl-scroll) transparent; }
main table { display: block; max-width: 100%; width: max-content; overflow-x: auto;
  scrollbar-width: thin; scrollbar-color: var(--jl-scroll) transparent; }
.semantics::-webkit-scrollbar, pre::-webkit-scrollbar, code.hl.lean.block::-webkit-scrollbar,
main table::-webkit-scrollbar { height: 8px; }
.semantics::-webkit-scrollbar-thumb, pre::-webkit-scrollbar-thumb, code.hl.lean.block::-webkit-scrollbar-thumb,
main table::-webkit-scrollbar-thumb { background: var(--jl-scroll); border-radius: 4px; }
code.hl.lean.block, .semantics, main table, .katex-display {
  background:
    linear-gradient(to right, var(--jl-bg) 30%, var(--jl-bg-clear)) left / 2em 100% no-repeat local,
    linear-gradient(to left, var(--jl-bg) 30%, var(--jl-bg-clear)) right / 2em 100% no-repeat local,
    radial-gradient(farthest-side at 0 50%, var(--jl-edge-shadow), transparent) left / 12px 100% no-repeat scroll,
    radial-gradient(farthest-side at 100% 50%, var(--jl-edge-shadow), transparent) right / 12px 100% no-repeat scroll; }
.katex-display { max-width: 100%; overflow-x: auto; overflow-y: hidden; padding-bottom: 2px;
  scrollbar-width: thin; scrollbar-color: var(--jl-scroll) transparent; }
.katex-display::-webkit-scrollbar { height: 8px; }
.katex-display::-webkit-scrollbar-thumb { background: var(--jl-scroll); border-radius: 4px; }
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
  font-size: 0.9em; cursor: pointer; border: 1px solid var(--jl-button-border); border-radius: 4px; background: var(--jl-button-bg);
  color: inherit; }
.page-tools { display: flex; flex-wrap: wrap; align-items: center; gap: 0.5em 1.5em; margin: 0.5em 0 1em;
  font-family: system-ui, sans-serif; font-size: 0.9em; }
.lean-toggle { display: flex; flex-wrap: wrap; align-items: center; gap: 0.5em; }
.theme-switch { display: flex; align-items: center; gap: 0.4em; margin-left: auto; }
.theme-switch select { min-height: 2.4em; padding: 0.2em 0.5em; font: inherit; color: inherit;
  background: var(--jl-button-bg); border: 1px solid var(--jl-button-border); border-radius: 4px; }
.theme-switch select:focus-visible { outline: 2px solid var(--jl-focus); outline-offset: 2px; }
.lean-toggle button { min-height: 2.4em; padding: 0.3em 0.9em; font: inherit; cursor: pointer;
  border: 1px solid var(--jl-button-border); border-radius: 4px; background: var(--jl-button-bg); color: inherit; }
.lean-toggle button[aria-pressed='true'] { background: var(--jl-pressed-bg); border-color: var(--jl-pressed-border); font-weight: 600; }
.lean-toggle button:focus-visible, button.show-code:focus-visible { outline: 2px solid var(--jl-focus); outline-offset: 2px; }
.lean-toggle .lean-toggle-note { color: var(--jl-muted); }
body.lean-hidden .lean-source, body.lean-hidden code.hl.lean.block,
body.lean-hidden button.show-code { display: none; }
.split-toc li:has(> a[href*='/#JAM___']), .split-toc li:has(> a[href*='/#PVM___']),
.split-toc li:has(> a[href*='/#JamCrypto___']) { display: none; }
.model-line { margin: -0.3em 0 1.2em; font-family: system-ui, sans-serif; font-size: 0.85em; line-height: 1.45;
  color: var(--jl-muted); overflow-wrap: anywhere; }
.model-line p { margin: 0.1em 0; }
.model-line code { font-size: 0.95em; }
.model-line details > summary { cursor: pointer; list-style: none; }
.model-line details > summary::-webkit-details-marker { display: none; }
.model-line details > summary:focus-visible { outline: 2px solid var(--jl-focus); outline-offset: 2px; }
.model-line .model-show { display: inline-block; margin-left: 0.5em; padding: 0 0.45em; border: 1px solid var(--jl-button-border);
  border-radius: 3px; background: var(--jl-button-bg); white-space: nowrap; }
.model-line .model-show::before { content: '▸ '; }
.model-line details[open] .model-show::before { content: '▾ '; }
.model-line details > :not(summary) { margin-top: 0.4em; font-size: 1.15em; }
.model-line a.model-quoted[href] { cursor: pointer; }
body.lean-hidden .model-line .model-show, body.lean-hidden .model-line details > :not(summary) { display: none; }
/* Worked examples ({example}, Companion/Example.lean): a box with a table that scrolls inside itself. */
details.worked-example { margin: 1.2em 0 1.6em; border: 1px solid var(--jl-example-border);
  border-left: 4px solid var(--jl-example-accent); border-radius: 4px; background: var(--jl-example-bg);
  font-family: system-ui, sans-serif; font-size: 0.9em; line-height: 1.45; max-width: 100%; }
details.worked-example > summary { cursor: pointer; padding: 0.55em 0.8em; font-weight: 600; }
details.worked-example > summary:focus-visible { outline: 2px solid var(--jl-focus); outline-offset: 2px; }
details.worked-example .we-tag { display: inline-block; margin-right: 0.6em; padding: 0 0.45em; border-radius: 3px;
  background: var(--jl-example-accent); color: var(--jl-bg); font-size: 0.8em; font-weight: 600;
  text-transform: uppercase; letter-spacing: 0.04em; vertical-align: 0.1em; }
details.worked-example .we-body { padding: 0 0.8em 0.6em; overflow-wrap: break-word; }
details.worked-example .we-body > p { margin: 0.45em 0; }
details.worked-example .we-table-wrap { position: relative; max-width: 100%; overflow-x: auto; margin: 0.6em 0;
  scrollbar-width: thin; scrollbar-color: var(--jl-scroll) transparent;
  background:
    linear-gradient(to right, var(--jl-example-bg) 30%, transparent) left / 2em 100% no-repeat local,
    linear-gradient(to left, var(--jl-example-bg) 30%, transparent) right / 2em 100% no-repeat local,
    radial-gradient(farthest-side at 0 50%, var(--jl-edge-shadow), transparent) left / 12px 100% no-repeat scroll,
    radial-gradient(farthest-side at 100% 50%, var(--jl-edge-shadow), transparent) right / 12px 100% no-repeat scroll; }
details.worked-example .we-table-wrap::-webkit-scrollbar { height: 8px; }
details.worked-example .we-table-wrap::-webkit-scrollbar-thumb { background: var(--jl-scroll); border-radius: 4px; }
main details.worked-example table.we-table { display: table; width: 100%; max-width: none; overflow: visible;
  background: none; border-collapse: collapse; font-size: 0.95em; }
details.worked-example table.we-table th, details.worked-example table.we-table td { text-align: left;
  vertical-align: top; padding: 0.3em 0.55em; border-bottom: 1px solid var(--jl-example-rule);
  min-width: 3em; max-width: 22em; overflow-wrap: break-word; }
details.worked-example table.we-table thead th { border-bottom: 2px solid var(--jl-example-border); white-space: nowrap; }
details.worked-example table.we-table tbody th { font-weight: 500; }
details.worked-example table.we-table p { margin: 0; }
details.worked-example code { font-size: 0.92em; }
@media (max-width: 600px) {
  details.worked-example .we-body { padding: 0 0.5em 0.5em; }
  details.worked-example table.we-table th, details.worked-example table.we-table td { padding: 0.25em 0.35em; max-width: 14em; }
}
"⟩

/-- Dark mode: the book follows the reader's system setting (`prefers-color-scheme`), and the
    theme switch under each page's title (Auto / Light / Dark, remembered in `localStorage`) can
    override it by setting `data-theme` on the root element. One palette, applied in both cases:
    Verso's colour variables (text, tooltips and hovers, messages, the sidebar, search), the colours
    Verso's own styles hard-code (header, sidebar links, docstring boxes), this book's own
    variables, links, and KaTeX (which draws in the text colour). -/
def darkRules (root : String) : String := s!"
{root} \{ color-scheme: dark;
  --verso-text-color: #e2e4e8; --verso-code-color: #e2e4e8; --verso-structure-color: #e2e4e8;
  --verso-background-color: #16181d; --verso-surface-color: #22262d; --verso-border-color: #3d434c;
  --verso-muted-color: #a3a9b3; --verso-selected-color: #2b3d57; --selected-color: #2b3d57;
  --verso-link-color: #8ab4f8;
  --verso-tooltip-color: #e2e4e8; --verso-tooltip-bg-color: #2a2e36; --verso-tooltip-border-color: #6b7380;
  --verso-tooltip-separator-color: #444b55;
  --verso-code-hover-bg-color: #2f3540; --verso-code-info-hover-bg-color: #2d4a8a;
  --verso-code-warning-hover-bg-color: #6b5214; --verso-code-error-hover-bg-color: #6e2a2a;
  --verso-message-error-color: #ff8a80; --verso-tooltip-warning-border-color: #b08a2e;
  --verso-tooltip-error-border-color: #a85656;
  --verso-tactic-state-color: #e2e4e8; --verso-tactic-state-bg-color: #1d2026;
  --verso-tactic-state-border-color: #5a616c; --verso-tactic-toggle-color: #5a616c;
  --verso-tactic-toggle-checked-color: #7d8591;
  --verso-toc-text-color: #c9cdd3; --verso-toc-background-color: #1b1e24; --verso-toc-border-color: #3d434c;
  --verso-toc-resize-handle-color: #6b7380;
  --verso-burger-toc-visible-color: #e2e4e8; --verso-burger-toc-hidden-color: #e2e4e8;
  --jl-bg: #16181d; --jl-bg-clear: rgba(22,24,29,0); --jl-edge-shadow: rgba(0,0,0,.6);
  --jl-scroll: #5a616c; --jl-button-bg: #262a31; --jl-button-border: #5a616c; --jl-pressed-bg: #2b3d57;
  --jl-pressed-border: #7ea6d8; --jl-focus: #8ab4f8; --jl-muted: #a3a9b3;
  --jl-example-bg: #1c2027; --jl-example-border: #3d4a5c; --jl-example-accent: #8ab4f8; --jl-example-rule: #343b46; }
{root} body \{ background: #16181d; color: #e2e4e8; }
{root} header \{ background: #1b1e24; box-shadow: 0 0 6px #000; }
{root} .header-title, {root} .prev-next-buttons > *, {root} #toc a:hover \{ color: #e2e4e8; }
{root} #toc a \{ color: #c9cdd3; }
{root} #toc .split-toc label.toggle-split-toc::before \{ background-color: #c9cdd3; }
{root} body:has(#toggle-toc:checked) .toc-backdrop \{ background-color: #000a; }
{root} a:link, {root} a:visited \{ color: #8ab4f8; }
{root} .hl.lean a:link, {root} .hl.lean a:visited \{ color: inherit; }
{root} a.header-title:link, {root} a.header-title:visited, {root} .prev-next-buttons a:link,
{root} .prev-next-buttons a:visited \{ color: #e2e4e8; }
{root} #search-wrapper, {root} #search-wrapper .combobox .cb_edit \{ background-color: #1b1e24; }
{root} .namedocs, {root} .namedocs .text \{ border-color: #4f5a66; }
{root} .namedocs .label \{ background: #22262d; border-color: #4f5a66; color: #a3a9b3; }
{root} #search-wrapper .cb_edit:empty:before, {root} #search-wrapper .more-results \{ color: #8d939c; }
"

def darkCss : Verso.Genre.Manual.CSS := ⟨darkRules ":root[data-theme='dark']" ++
  "@media (prefers-color-scheme: dark) {" ++ darkRules ":root:not([data-theme='light'])" ++ "}"⟩

/-- The theme switch. Runs in the page head, so a remembered choice applies before the page is
    drawn; then adds "Theme: Auto / Light / Dark" to the page's tool bar (`companionTools`). -/
def themeJs : Verso.Genre.Manual.JS := ⟨"
(() => {
  const KEY = 'jam-lean-book.theme';
  const load = () => { try { return localStorage.getItem(KEY); } catch (e) { return null; } };
  const save = (v) => { try { v === 'auto' ? localStorage.removeItem(KEY) : localStorage.setItem(KEY, v); } catch (e) {} };
  const set = (v) => { if (v === 'light' || v === 'dark') document.documentElement.dataset.theme = v;
                       else delete document.documentElement.dataset.theme; };
  set(load());
  document.addEventListener('DOMContentLoaded', () => {
    const tools = companionTools();
    if (!tools) return;
    const label = document.createElement('label');
    label.className = 'theme-switch';
    label.append('Theme');
    const sel = document.createElement('select');
    for (const [v, t] of [['auto', 'Auto'], ['light', 'Light'], ['dark', 'Dark']]) {
      const o = document.createElement('option'); o.value = v; o.textContent = t; sel.appendChild(o);
    }
    const cur = load();
    sel.value = cur === 'light' || cur === 'dark' ? cur : 'auto';
    sel.addEventListener('change', () => { save(sel.value); set(sel.value); });
    label.appendChild(sel);
    tools.appendChild(label);
  });
})();
"⟩

/-- The bar of page tools under the page's title (the theme switch, and on pages with Lean code
    the Lean switch), made by whichever script asks first. -/
def toolsJs : Verso.Genre.Manual.JS := ⟨"
function companionTools() {
  let bar = document.querySelector('.page-tools');
  if (bar) return bar;
  const heading = document.querySelector('main section h1');
  if (!heading) return null;
  bar = document.createElement('div');
  bar.className = 'page-tools';
  heading.insertAdjacentElement('afterend', bar);
  return bar;
}
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
  if (!blocks.length) return;
  const KEY = 'jam-lean-book.lean';
  const load = () => { try { return localStorage.getItem(KEY); } catch (e) { return null; } };
  const save = (v) => { try { v ? localStorage.setItem(KEY, v) : localStorage.removeItem(KEY); } catch (e) {} };
  const tools = companionTools();
  if (!tools) return;
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
  tools.prepend(bar);
  const saved = load();
  if (saved === 'all' || saved === 'none') apply(saved);
});
"⟩

/-- The "In the model:" lines under the paper's equations (`Companion/ModelMap.lean`): a line made
    by a `{transcribed}` marker stands before its hand-written display and is moved after it; a
    "quoted in this chapter" pointer becomes a link to that quotation on this page (built here
    because the pages' `<base href>` would send a bare `#…` link to the book's root). -/
def modelJs : Verso.Genre.Manual.JS := ⟨"
document.addEventListener('DOMContentLoaded', () => {
  for (const line of document.querySelectorAll('.model-line-before')) {
    const display = line.nextElementSibling;
    if (display) display.insertAdjacentElement('afterend', line);
  }
  for (const a of document.querySelectorAll('a.model-quoted[data-target]')) {
    const box = [...document.querySelectorAll('.lean-source[data-decl]')].find(b => b.dataset.decl === a.dataset.target);
    if (!box) continue;
    if (!box.id) box.id = 'src-' + a.dataset.target;
    a.href = location.pathname + location.search + '#' + box.id;
  }
});
"⟩

/-- Wide displayed equations. A display at most 15% wider than the column is shrunk to fit, so its
    equation number shows without scrolling; a wider one keeps its size and scrolls inside its own
    box (`.katex-display`, which shows an edge shadow on the side with more to see, like code
    blocks). Runs after the page loads, once KaTeX has rendered and the fonts are in, and again when
    the window is resized. -/
def displayFitJs : Verso.Genre.Manual.JS := ⟨"
(() => {
  const MIN = 0.85;
  const fit = () => {
    for (const d of document.querySelectorAll('.katex-display')) {
      const k = d.querySelector(':scope > .katex');
      if (!k) continue;
      k.style.fontSize = '';
      const ratio = d.clientWidth / d.scrollWidth;
      if (ratio < 1 && ratio >= MIN)
        k.style.fontSize = (parseFloat(getComputedStyle(k).fontSize) * ratio * 0.995) + 'px';
    }
  };
  const run = () => requestAnimationFrame(() => { fit(); requestAnimationFrame(fit); });
  window.addEventListener('load', () => {
    run();
    if (document.fonts && document.fonts.ready) document.fonts.ready.then(run);
  });
  let t;
  window.addEventListener('resize', () => { clearTimeout(t); t = setTimeout(run, 100); });
})();
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
  extraCss := (({} : Std.HashSet Verso.Genre.Manual.CSS).insert narrowCss).insert darkCss
  extraJs := (((((({} : Std.HashSet Verso.Genre.Manual.JS).insert toolsJs).insert themeJs).insert docMathJs).insert collapseJs).insert modelJs).insert displayFitJs
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1

def main := manualMain (%doc Companion) (config := { config with })
