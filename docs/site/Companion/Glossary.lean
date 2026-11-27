import VersoManual
import Companion.Source
import Companion.Paper
import Companion.Reader
import JAM.State
import JAM.Block
import JAM.BlockImport
import JAM.Safrole
import JAM.Disputes
import JAM.History
import JAM.Account
import JAM.Work
import JAM.Accumulate
import JAM.Accumulation
import JAM.Guarantee
import JAM.Refine
import JAM.Constants
import JAM.Params
import PVM.Basic
import PVM.Memory
import PVM.Exec
import PVM.Machine

open Verso.Genre Manual
open Companion

set_option pp.rawOnError true

#doc (Manual) "Glossary" =>
%%%
tag := "glossary"
shortTitle := "Glossary"
file := "glossary"
%%%

The symbols the book uses most, each with its meaning in plain words, the model's name for it
(linked to its API page; hover for its type) and the section that defines it. The paper's own,
complete index is {gpchapter}`sec:definitions`. For the big picture first, read
{ref "plain-english"}[JAM in plain English].

Two symbols are easy to confuse: the authorizer queue is $`\authqueue` (a circle with a straight
stroke through it) and the PVM registers are $`\registers` (an open loop). Both are the letter phi.

The entries are generated from `docs/site/glossary.json`; the build fails if a model name in it
no longer exists.

# The state
%%%
tag := "glossary-state"
%%%

{glossarySection "state"}

# The block
%%%
tag := "glossary-block"
%%%

{glossarySection "block"}

# Sets
%%%
tag := "glossary-sets"
%%%

{glossarySection "sets"}

# Functions
%%%
tag := "glossary-functions"
%%%

{glossarySection "functions"}

# The PVM
%%%
tag := "glossary-pvm"
%%%

{glossarySection "pvm"}

# Constants
%%%
tag := "glossary-constants"
%%%

{glossarySection "constants"}
