import VersoManual
import Companion

open Verso.Genre Manual

/-- Layout fixes: code blocks keep their layout and scroll sideways with a visible scrollbar and a
    shadow at the edge that has more to see; display
    math scrolls inside its own box on narrow screens; and the header title keeps clear of the
    search box (which Verso places over the header): the title wrapper reserves the search bar's
    width, the search bar is narrower below 1200 px, and the title wraps and shrinks on narrow
    screens. -/
def narrowCss : Verso.Genre.Manual.CSS := ⟨"
.semantics, pre, code.hl.lean.block { max-width: 100%; overflow-x: auto; white-space: pre;
  scrollbar-width: thin; scrollbar-color: #b0b0b0 transparent; }
.semantics::-webkit-scrollbar, pre::-webkit-scrollbar, code.hl.lean.block::-webkit-scrollbar { height: 8px; }
.semantics::-webkit-scrollbar-thumb, pre::-webkit-scrollbar-thumb, code.hl.lean.block::-webkit-scrollbar-thumb {
  background: #b0b0b0; border-radius: 4px; }
code.hl.lean.block, .semantics {
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
  extraJs := ({} : Std.HashSet Verso.Genre.Manual.JS).insert docMathJs
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1

def main := manualMain (%doc Companion) (config := { config with })
