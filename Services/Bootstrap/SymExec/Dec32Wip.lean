import Services.Bootstrap.SymExec.ProgF
import PVM.SymExec.Trace
open PVM PVM.SymExec
def pairs : List Nat := (List.range 100).flatMap fun i => [48 + i / 10, 48 + i % 10]
def P1 : SVal := .alu2i .shloRImm64 (.const 0) (.mod (.alu3 .mulUpperUU (.alu2i .shloLImm64 (.const 0) (.var 0) 32) (.const 15111572745684516864) (.const 0)) 18446744073709551616) 45
def P2 : SVal := .alu3 .sub64 (.var 0) (.mod (.alu3 .mul64 (.var 7) (.const 10000) (.const 0)) 18446744073709551616) (.const 0)
def T64 : Nat := 18446744073709551616
def rws : List (SVal × SVal) := [(P1, .var 7), (P2, .var 8),
  (.alu2i .shloLImm64 (.const 0) (.var 8) 48, .var 13),
  (.alu2i .shloRImm64 (.const 0) (.var 13) 50, .var 14),
  (.alu3 .mul64 (.var 14) (.const 5243) (.const 0), .var 15),
  (.alu2i .shloRImm64 (.const 0) (.var 15) 16, .var 16),
  (.alu2i .andImm (.const 0) (.var 16) 2046, .var 9),
  (.alu2i .shloRImm64 (.const 0) (.var 15) 17, .var 17),
  (.alu2i .mulImm64 (.const 0) (.var 17) 100, .var 10),
  (.alu3 .sub64 (.var 8) (.var 10) (.const 0), .var 11),
  (.alu2i .shloLImm64 (.const 0) (.var 11) 49, .var 18),
  (.alu2i .shloRImm64 (.const 0) (.var 18) 48, .var 12)]
/-- ρ: 0 y (the u32), 1 sp, 2 v (its address), 3 F, 4 ret, 5 v5, 6 v6. Case 1000 ≤ y < 10000. -/
def st : Static :=
  { ub := [10000, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 1, 10000, 199, 9901, 100, 199, 2814749767106560000, 2500, 13107500, 201, 100, 56294995342131200, 1]
    lb := [1000, 2147484248, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := rws ++ [] }
def A : Spec :=
  { regs := [(0, .var 4), (1, .var 1), (5, .var 5), (6, .var 6), (7, .var 2), (8, .var 3)]
    cells := (⟨some 2, 0⟩, 4, .var 0) :: (List.range 200).map fun j => (⟨none, (70844 + j : Nat)⟩, 1, .const (pairs.getD j 0)) }























def s41 : SState := ((traceRun st Services.Bootstrap.SymExec.progF 41 68146 (init A)).2.map (·.2)).getD (init A)

partial def PVM.SymExec.SVal.sz : SVal → Nat
  | .mod v _ => v.sz + 1 | .sx _ v => v.sz + 1 | .alu2 _ a => a.sz + 1 | .tbl _ i => i.sz + 1
  | .alu2i _ a b _ => a.sz + b.sz + 1 | .alu3 _ a b d => a.sz + b.sz + d.sz + 1 | _ => 1
def showR (v : SVal) : String := if v.sz < 60 then toString (repr v) else s!"<size {v.sz}>"
def stepRegs (k : Nat) : String :=
  match (traceRun st Services.Bootstrap.SymExec.progF k 68146 (init A)).2 with
  | some (pc, σ) => s!"{k} pc {pc}: " ++ String.intercalate "; " ((List.range 13).filterMap fun r =>
      let v := σ.regs.getD r (.const 0); if v.sz > 1 then some s!"r{r}={showR v}" else none)
  | none => s!"{k} stuck"
def T : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, .addr ⟨some 1, -28⟩), (12, .const 4)]
    cells := [(⟨some 1, -28⟩, 1, .mem0 ⟨some 9, 70844⟩ 1), (⟨some 1, -27⟩, 1, .mem0 ⟨some 9, 70845⟩ 1),
      (⟨some 1, -26⟩, 1, .mem0 ⟨some 12, 70844⟩ 1), (⟨some 1, -25⟩, 1, .mem0 ⟨some 12, 70845⟩ 1)] }
def st_0 : Static := { st with ub := 10 :: st.ub.tail, lb := 0 :: st.lb.tail, rw := [] }
def rwsS : List (SVal × SVal) := [
  (.alu2i .shloLImm64 (.const 0) (.var 0) 48, .var 13),
  (.alu2i .shloRImm64 (.const 0) (.var 13) 50, .var 14),
  (.alu2i .mulImm64 (.const 0) (.var 14) 5243, .var 15),
  (.alu2i .shloRImm64 (.const 0) (.var 15) 17, .var 17),
  (.alu2i .mulImm64 (.const 0) (.var 17) 100, .var 10),
  (.alu3 .sub64 (.var 0) (.var 10) (.const 0), .var 11),
  (.alu2i .shloLImm64 (.const 0) (.var 11) 49, .var 18),
  (.alu2i .shloRImm64 (.const 0) (.var 18) 48, .var 12),
  (.alu2i .shloLImm32 (.const 0) (.var 0) 1, .var 19),
  (.alu2i .shloLImm32 (.const 0) (.var 17) 1, .var 19)]
def ubS (hi : Nat) : List Nat := [hi, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 1, 1, 1, 9901, 100, 199, 281474976710656000, 250, 1310750, 1, 10, 56294995342131200, 20]
def st_1 : Static := { st with ub := ubS 10, lb := 1 :: st.lb.tail, rw := rwsS }
def st_10 : Static := { st with ub := (ubS 100).set 17 1, lb := 10 :: st.lb.tail, rw := rwsS }
def st_100 : Static := { st with ub := ubS 1000, lb := (100 :: st.lb.tail).set 17 1, rw := rwsS }
def stepRegsS (st : Static) (k : Nat) : String :=
  match (traceRun st Services.Bootstrap.SymExec.progF k 68146 (init A)).2 with
  | some (pc, σ) => s!"{k} pc {pc}: " ++ String.intercalate "; " ((List.range 13).filterMap fun r =>
      let v := σ.regs.getD r (.const 0); if v.sz > 1 then some s!"r{r}={showR v}" else none)
  | none => s!"{k} stuck"
def r7at (st : Static) (k : Nat) : String :=
  match (traceRun st Services.Bootstrap.SymExec.progF k 68146 (init A)).2 with
  | some (pc, σ) => s!"{k} pc {pc}: r7={showR (σ.regs.getD 7 (.const 0))} r8={showR (σ.regs.getD 8 (.const 0))}"
  | none => s!"{k} stuck"
#eval (List.range 12).map fun j => (28+j*4, (traceRun st_1 Services.Bootstrap.SymExec.progF (28+j*4) 68146 (init A)).2.map (·.1))
#eval (List.range 12).map fun j => (28+j*4, (traceRun st_10 Services.Bootstrap.SymExec.progF (28+j*4) 68146 (init A)).2.map (·.1))
#eval (List.range 12).map fun j => (28+j*4, (traceRun st_100 Services.Bootstrap.SymExec.progF (28+j*4) 68146 (init A)).2.map (·.1))
