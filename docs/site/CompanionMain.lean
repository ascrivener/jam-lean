import VersoManual
import Companion

open Verso.Genre Manual

/-- Layout fixes: code blocks keep their layout and scroll sideways with a visible scrollbar; display
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

/-- HTML only, one page per chapter. -/
def config : Config where
  extraCss := ({} : Std.HashSet Verso.Genre.Manual.CSS).insert narrowCss
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1

def main := manualMain (%doc Companion) (config := { config with })
