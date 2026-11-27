import VersoManual
import Companion

open Verso.Genre Manual

/-- Layout fixes: long code lines wrap (no hidden horizontal scrolling), display math scrolls inside
    its own box on narrow screens, and the header title shrinks to fit a phone. -/
def narrowCss : Verso.Genre.Manual.CSS := ⟨"
.semantics, pre, code.hl.lean.block { max-width: 100%; white-space: pre-wrap; overflow-wrap: anywhere; }
.katex-display { max-width: 100%; overflow-x: auto; overflow-y: hidden; }
.header-title { font-size: 1.5rem; }
@media (max-width: 700px) {
  .header-title { font-size: 0.72rem; }
  .header-title h1 { text-wrap: wrap !important; white-space: normal !important; line-height: 1.1; max-width: 30vw; }
}
"⟩

/-- HTML only, one page per chapter. -/
def config : Config where
  extraCss := ({} : Std.HashSet Verso.Genre.Manual.CSS).insert narrowCss
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1

def main := manualMain (%doc Companion) (config := { config with })
