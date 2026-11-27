import VersoManual
import Companion

open Verso.Genre Manual

/-- HTML only, one page per chapter. -/
def config : Config where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1

def main := manualMain (%doc Companion) (config := { config with })
