import VersoManual
import Companion

open Verso.Genre Manual

/-- Narrow screens: wide code and display math scroll inside their own box instead of widening the
    page. -/
def narrowCss : Verso.Genre.Manual.CSS := ⟨"
.semantics, pre, .katex-display { max-width: 100%; overflow-x: auto; overflow-y: hidden; }
"⟩

/-- HTML only, one page per chapter. -/
def config : Config where
  extraCss := ({} : Std.HashSet Verso.Genre.Manual.CSS).insert narrowCss
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1

def main := manualMain (%doc Companion) (config := { config with })
