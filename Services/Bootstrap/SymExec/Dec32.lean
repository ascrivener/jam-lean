import Services.Bootstrap.SymExec.ProgF
import PVM.SymExec.Ops

namespace Services.Bootstrap.SymExec.Dec32

open PVM PVM.SymExec

def pairs : List Nat := (List.range 100).flatMap fun i => [48 + i / 10, 48 + i % 10]

def A : Spec :=
  { regs := [(0, .var 4), (1, .var 1), (5, .var 5), (6, .var 6), (7, .var 2), (8, .var 3)]
    cells := (⟨some 2, 0⟩, 4, .var 0) :: (List.range 200).map fun j => (⟨none, (70844 + j : Nat)⟩, 1, .const (pairs.getD j 0)) }

def st_0 : Static :=
  { ub := [1, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 1]
    lb := [0, 2147484248, 0, 0, 2, 0, 0, 0]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm32 (.const 0) (.var 0) 1, .var 7)] }

def T_0 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -25 }), (12, PVM.SymExec.SVal.const 1)]
    cells := [({ base := some 1, off := -25 }, 1, PVM.SymExec.SVal.tbl [48] (PVM.SymExec.SVal.var 7))] }

set_option maxRecDepth 100000 in
theorem ok_0 : check st_0 Services.Bootstrap.SymExec.progF A T_0 [(⟨some 1, -72⟩, 72)] 68146 61857 28 = true := by
  decide +kernel

/-- The named naturals of the range 0 ≤ y < 1. -/
def vals_0 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := 2 * v0
  [y, sp, v, F, ret, v5, v6, v7]

theorem bh_0 {y sp v F ret v5 v6 : Nat} (hy : 0 ≤ y ∧ y < 1) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_0 y sp v F ret v5 v6) st_0.ub ∧ LBHold (vals_0 y sp v F ret v5 v6) st_0.lb := by
  simp only [vals_0, st_0, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_0 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 0 ≤ y ∧ y < 1) :
    RwHold ⟨fun k => (vals_0 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_0.rw := by
  exact ⟨(op_shloL32 (by simp only [vals_0, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_0, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

def st_1 : Static :=
  { ub := [10, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 19]
    lb := [1, 2147484248, 0, 0, 2, 0, 0, 2]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm32 (.const 0) (.var 0) 1, .var 7)] }

def T_1 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -25 }), (12, PVM.SymExec.SVal.const 1)]
    cells := [({ base := some 1, off := -25 }, 1, PVM.SymExec.SVal.tbl [48, 48, 49, 48, 50, 48, 51, 48, 52, 48, 53, 48, 54, 48, 55, 48, 56, 48, 57] (PVM.SymExec.SVal.var 7))] }

set_option maxRecDepth 100000 in
theorem ok_1 : check st_1 Services.Bootstrap.SymExec.progF A T_1 [(⟨some 1, -72⟩, 72)] 68146 61857 29 = true := by
  decide +kernel

/-- The named naturals of the range 1 ≤ y < 10. -/
def vals_1 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := 2 * v0
  [y, sp, v, F, ret, v5, v6, v7]

theorem bh_1 {y sp v F ret v5 v6 : Nat} (hy : 1 ≤ y ∧ y < 10) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_1 y sp v F ret v5 v6) st_1.ub ∧ LBHold (vals_1 y sp v F ret v5 v6) st_1.lb := by
  simp only [vals_1, st_1, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_1 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 1 ≤ y ∧ y < 10) :
    RwHold ⟨fun k => (vals_1 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_1.rw := by
  exact ⟨(op_shloL32 (by simp only [vals_1, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

def st_10 : Static :=
  { ub := [100, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 27866022694354945, 25, 125833, 1, 1, 100, 56294995342131200, 199]
    lb := [10, 2147484248, 0, 0, 2, 0, 0, 2814749767106560, 2, 10486, 0, 0, 0, 0, 0]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm64 (.const 0) (.var 0) 48, .var 7),
    (.alu2i .shloRImm64 (.const 0) (.var 7) 50, .var 8),
    (.alu2i .mulImm64 (.const 0) (.var 8) 5243, .var 9),
    (.alu2i .shloRImm64 (.const 0) (.var 9) 17, .var 10),
    (.alu2i .mulImm64 (.const 0) (.var 10) 100, .var 11),
    (.alu3 .sub64 (.var 0) (.var 11) (.const 0), .var 12),
    (.alu2i .shloLImm64 (.const 0) (.var 12) 49, .var 13),
    (.alu2i .shloRImm64 (.const 0) (.var 13) 48, .var 14)] }

def T_10 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -26 }), (12, PVM.SymExec.SVal.const 2)]
    cells := [({ base := some 1, off := -26 }, 2, PVM.SymExec.SVal.mem0 { base := some 14, off := 70844 } 2)] }

set_option maxRecDepth 100000 in
theorem ok_10 : check st_10 Services.Bootstrap.SymExec.progF A T_10 [(⟨some 1, -72⟩, 72)] 68146 61857 37 = true := by
  decide +kernel

/-- The named naturals of the range 10 ≤ y < 100. -/
def vals_10 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := v0 * 281474976710656
  let v8 := v0 / 4
  let v9 := v0 / 4 * 5243
  let v10 := v0 / 100
  let v11 := v0 / 100 * 100
  let v12 := v0 % 100
  let v13 := v0 % 100 * 562949953421312
  let v14 := 2 * (v0 % 100)
  [y, sp, v, F, ret, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]

theorem bh_10 {y sp v F ret v5 v6 : Nat} (hy : 10 ≤ y ∧ y < 100) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_10 y sp v F ret v5 v6) st_10.ub ∧ LBHold (vals_10 y sp v F ret v5 v6) st_10.lb := by
  simp only [vals_10, st_10, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_10 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 10 ≤ y ∧ y < 100) :
    RwHold ⟨fun k => (vals_10 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_10.rw := by
  exact ⟨(op_shloLm (by decide) (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

def st_100 : Static :=
  { ub := [1000, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 281193501733945345, 250, 1305508, 10, 901, 100, 56294995342131200, 199, 19]
    lb := [100, 2147484248, 0, 0, 2, 0, 0, 28147497671065600, 25, 131075, 1, 100, 0, 0, 0, 2]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm64 (.const 0) (.var 0) 48, .var 7),
    (.alu2i .shloRImm64 (.const 0) (.var 7) 50, .var 8),
    (.alu2i .mulImm64 (.const 0) (.var 8) 5243, .var 9),
    (.alu2i .shloRImm64 (.const 0) (.var 9) 17, .var 10),
    (.alu2i .mulImm64 (.const 0) (.var 10) 100, .var 11),
    (.alu3 .sub64 (.var 0) (.var 11) (.const 0), .var 12),
    (.alu2i .shloLImm64 (.const 0) (.var 12) 49, .var 13),
    (.alu2i .shloRImm64 (.const 0) (.var 13) 48, .var 14),
    (.alu2i .shloLImm32 (.const 0) (.var 10) 1, .var 15)] }

def T_100 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -27 }), (12, PVM.SymExec.SVal.const 3)]
    cells := [({ base := some 1, off := -27 }, 1, PVM.SymExec.SVal.tbl [48, 48, 49, 48, 50, 48, 51, 48, 52, 48, 53, 48, 54, 48, 55, 48, 56, 48, 57] (PVM.SymExec.SVal.var 15)), ({ base := some 1, off := -26 }, 2, PVM.SymExec.SVal.mem0 { base := some 14, off := 70844 } 2)] }

set_option maxRecDepth 100000 in
theorem ok_100 : check st_100 Services.Bootstrap.SymExec.progF A T_100 [(⟨some 1, -72⟩, 72)] 68146 61857 46 = true := by
  decide +kernel

/-- The named naturals of the range 100 ≤ y < 1000. -/
def vals_100 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := v0 * 281474976710656
  let v8 := v0 / 4
  let v9 := v0 / 4 * 5243
  let v10 := v0 / 100
  let v11 := v0 / 100 * 100
  let v12 := v0 % 100
  let v13 := v0 % 100 * 562949953421312
  let v14 := 2 * (v0 % 100)
  let v15 := 2 * (v0 / 100)
  [y, sp, v, F, ret, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]

theorem bh_100 {y sp v F ret v5 v6 : Nat} (hy : 100 ≤ y ∧ y < 1000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_100 y sp v F ret v5 v6) st_100.ub ∧ LBHold (vals_100 y sp v F ret v5 v6) st_100.lb := by
  simp only [vals_100, st_100, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_100 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 100 ≤ y ∧ y < 1000) :
    RwHold ⟨fun k => (vals_100 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_100.rw := by
  exact ⟨(op_shloLm (by decide) (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloL32 (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

def st_1000 : Static :=
  { ub := [10000, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 42945377992705, 35180853652792, 1, 1, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199]
    lb := [1000, 2147484248, 0, 0, 2, 0, 0, 4294967296000, 3518437209000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm64 (.const 0) (.var 0) 32, .var 7),
    (.alu3 .mulUpperUU (.var 7) (.const 15111572745684516864) (.const 0), .var 8),
    (.alu2i .shloRImm64 (.const 0) (.var 8) 45, .var 9),
    (.alu3 .mul64 (.var 9) (.const 10000) (.const 0), .var 10),
    (.alu3 .sub64 (.var 0) (.var 10) (.const 0), .var 11),
    (.alu2i .shloLImm64 (.const 0) (.var 11) 48, .var 12),
    (.alu2i .shloRImm64 (.const 0) (.var 12) 50, .var 13),
    (.alu3 .mul64 (.var 13) (.const 5243) (.const 0), .var 14),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 16, .var 15),
    (.alu2i .andImm (.const 0) (.var 15) 2046, .var 16),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 17, .var 17),
    (.alu2i .mulImm64 (.const 0) (.var 17) 100, .var 18),
    (.alu3 .sub64 (.var 11) (.var 18) (.const 0), .var 19),
    (.alu2i .shloLImm64 (.const 0) (.var 19) 49, .var 20),
    (.alu2i .shloRImm64 (.const 0) (.var 20) 48, .var 21)] }

def T_1000 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -28 }), (12, PVM.SymExec.SVal.const 4)]
    cells := [({ base := some 1, off := -25 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70845 } 1), ({ base := some 1, off := -26 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70844 } 1), ({ base := some 1, off := -27 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70845 } 1), ({ base := some 1, off := -28 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70844 } 1)] }

set_option maxRecDepth 100000 in
theorem ok_1000 : check st_1000 Services.Bootstrap.SymExec.progF A T_1000 [(⟨some 1, -72⟩, 72)] 68146 61857 69 = true := by
  decide +kernel

/-- The named naturals of the range 1000 ≤ y < 10000. -/
def vals_1000 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := v0 * 4294967296
  let v8 := v7 * 15111572745684516864 / 18446744073709551616
  let v9 := v0 / 10000
  let v10 := v0 / 10000 * 10000
  let v11 := v0 % 10000
  let v12 := v0 % 10000 * 281474976710656
  let v13 := v0 % 10000 / 4
  let v14 := v0 % 10000 / 4 * 5243
  let v15 := v0 % 10000 / 4 * 5243 / 65536
  let v16 := 2 * (v0 % 10000 / 100)
  let v17 := v0 % 10000 / 100
  let v18 := v0 % 10000 / 100 * 100
  let v19 := v0 % 100
  let v20 := v0 % 100 * 562949953421312
  let v21 := 2 * (v0 % 100)
  [y, sp, v, F, ret, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21]

theorem bh_1000 {y sp v F ret v5 v6 : Nat} (hy : 1000 ≤ y ∧ y < 10000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_1000 y sp v F ret v5 v6) st_1000.ub ∧ LBHold (vals_1000 y sp v F ret v5 v6) st_1000.lb := by
  simp only [vals_1000, st_1000, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_1000 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 1000 ≤ y ∧ y < 10000) :
    RwHold ⟨fun k => (vals_1000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_1000.rw := by
  exact ⟨(op_shloLm (by decide) (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

def st_10000 : Static :=
  { ub := [100000, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 429492434632705, 351840202462792, 10, 90001, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199, 19]
    lb := [10000, 2147484248, 0, 0, 2, 0, 0, 42949672960000, 35184372090000, 1, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm64 (.const 0) (.var 0) 32, .var 7),
    (.alu3 .mulUpperUU (.var 7) (.const 15111572745684516864) (.const 0), .var 8),
    (.alu2i .shloRImm64 (.const 0) (.var 8) 45, .var 9),
    (.alu3 .mul64 (.var 9) (.const 10000) (.const 0), .var 10),
    (.alu3 .sub64 (.var 0) (.var 10) (.const 0), .var 11),
    (.alu2i .shloLImm64 (.const 0) (.var 11) 48, .var 12),
    (.alu2i .shloRImm64 (.const 0) (.var 12) 50, .var 13),
    (.alu3 .mul64 (.var 13) (.const 5243) (.const 0), .var 14),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 16, .var 15),
    (.alu2i .andImm (.const 0) (.var 15) 2046, .var 16),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 17, .var 17),
    (.alu2i .mulImm64 (.const 0) (.var 17) 100, .var 18),
    (.alu3 .sub64 (.var 11) (.var 18) (.const 0), .var 19),
    (.alu2i .shloLImm64 (.const 0) (.var 19) 49, .var 20),
    (.alu2i .shloRImm64 (.const 0) (.var 20) 48, .var 21),
    (.alu2i .shloLImm32 (.const 0) (.var 9) 1, .var 22)] }

def T_10000 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -29 }), (12, PVM.SymExec.SVal.const 5)]
    cells := [({ base := some 1, off := -29 }, 1, PVM.SymExec.SVal.tbl [48, 48, 49, 48, 50, 48, 51, 48, 52, 48, 53, 48, 54, 48, 55, 48, 56, 48, 57] (PVM.SymExec.SVal.var 22)), ({ base := some 1, off := -25 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70845 } 1), ({ base := some 1, off := -26 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70844 } 1), ({ base := some 1, off := -27 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70845 } 1), ({ base := some 1, off := -28 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70844 } 1)] }

set_option maxRecDepth 100000 in
theorem ok_10000 : check st_10000 Services.Bootstrap.SymExec.progF A T_10000 [(⟨some 1, -72⟩, 72)] 68146 61857 78 = true := by
  decide +kernel

/-- The named naturals of the range 10000 ≤ y < 100000. -/
def vals_10000 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := v0 * 4294967296
  let v8 := v7 * 15111572745684516864 / 18446744073709551616
  let v9 := v0 / 10000
  let v10 := v0 / 10000 * 10000
  let v11 := v0 % 10000
  let v12 := v0 % 10000 * 281474976710656
  let v13 := v0 % 10000 / 4
  let v14 := v0 % 10000 / 4 * 5243
  let v15 := v0 % 10000 / 4 * 5243 / 65536
  let v16 := 2 * (v0 % 10000 / 100)
  let v17 := v0 % 10000 / 100
  let v18 := v0 % 10000 / 100 * 100
  let v19 := v0 % 100
  let v20 := v0 % 100 * 562949953421312
  let v21 := 2 * (v0 % 100)
  let v22 := 2 * v9
  [y, sp, v, F, ret, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22]

theorem bh_10000 {y sp v F ret v5 v6 : Nat} (hy : 10000 ≤ y ∧ y < 100000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_10000 y sp v F ret v5 v6) st_10000.ub ∧ LBHold (vals_10000 y sp v F ret v5 v6) st_10000.lb := by
  simp only [vals_10000, st_10000, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_10000 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 10000 ≤ y ∧ y < 100000) :
    RwHold ⟨fun k => (vals_10000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_10000.rw := by
  exact ⟨(op_shloLm (by decide) (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloL32 (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

def st_100000 : Static :=
  { ub := [1000000, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 4294963001032705, 3518433690562792, 100, 990001, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199, 27866022694354945, 25, 125833, 1, 1, 100, 56294995342131200, 199]
    lb := [100000, 2147484248, 0, 0, 2, 0, 0, 429496729600000, 351843720900000, 10, 100000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2814749767106560, 2, 10486, 0, 0, 0, 0, 0]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm64 (.const 0) (.var 0) 32, .var 7),
    (.alu3 .mulUpperUU (.var 7) (.const 15111572745684516864) (.const 0), .var 8),
    (.alu2i .shloRImm64 (.const 0) (.var 8) 45, .var 9),
    (.alu3 .mul64 (.var 9) (.const 10000) (.const 0), .var 10),
    (.alu3 .sub64 (.var 0) (.var 10) (.const 0), .var 11),
    (.alu2i .shloLImm64 (.const 0) (.var 11) 48, .var 12),
    (.alu2i .shloRImm64 (.const 0) (.var 12) 50, .var 13),
    (.alu3 .mul64 (.var 13) (.const 5243) (.const 0), .var 14),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 16, .var 15),
    (.alu2i .andImm (.const 0) (.var 15) 2046, .var 16),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 17, .var 17),
    (.alu2i .mulImm64 (.const 0) (.var 17) 100, .var 18),
    (.alu3 .sub64 (.var 11) (.var 18) (.const 0), .var 19),
    (.alu2i .shloLImm64 (.const 0) (.var 19) 49, .var 20),
    (.alu2i .shloRImm64 (.const 0) (.var 20) 48, .var 21),
    (.alu2i .shloLImm64 (.const 0) (.var 9) 48, .var 22),
    (.alu2i .shloRImm64 (.const 0) (.var 22) 50, .var 23),
    (.alu2i .mulImm64 (.const 0) (.var 23) 5243, .var 24),
    (.alu2i .shloRImm64 (.const 0) (.var 24) 17, .var 25),
    (.alu2i .mulImm64 (.const 0) (.var 25) 100, .var 26),
    (.alu3 .sub64 (.var 9) (.var 26) (.const 0), .var 27),
    (.alu2i .shloLImm64 (.const 0) (.var 27) 49, .var 28),
    (.alu2i .shloRImm64 (.const 0) (.var 28) 48, .var 29)] }

def T_100000 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -30 }), (12, PVM.SymExec.SVal.const 6)]
    cells := [({ base := some 1, off := -30 }, 2, PVM.SymExec.SVal.mem0 { base := some 29, off := 70844 } 2), ({ base := some 1, off := -25 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70845 } 1), ({ base := some 1, off := -26 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70844 } 1), ({ base := some 1, off := -27 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70845 } 1), ({ base := some 1, off := -28 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70844 } 1)] }

set_option maxRecDepth 100000 in
theorem ok_100000 : check st_100000 Services.Bootstrap.SymExec.progF A T_100000 [(⟨some 1, -72⟩, 72)] 68146 61857 85 = true := by
  decide +kernel

/-- The named naturals of the range 100000 ≤ y < 1000000. -/
def vals_100000 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := v0 * 4294967296
  let v8 := v7 * 15111572745684516864 / 18446744073709551616
  let v9 := v0 / 10000
  let v10 := v0 / 10000 * 10000
  let v11 := v0 % 10000
  let v12 := v0 % 10000 * 281474976710656
  let v13 := v0 % 10000 / 4
  let v14 := v0 % 10000 / 4 * 5243
  let v15 := v0 % 10000 / 4 * 5243 / 65536
  let v16 := 2 * (v0 % 10000 / 100)
  let v17 := v0 % 10000 / 100
  let v18 := v0 % 10000 / 100 * 100
  let v19 := v0 % 100
  let v20 := v0 % 100 * 562949953421312
  let v21 := 2 * (v0 % 100)
  let v22 := v9 * 281474976710656
  let v23 := v9 / 4
  let v24 := v9 / 4 * 5243
  let v25 := v9 / 100
  let v26 := v9 / 100 * 100
  let v27 := v9 % 100
  let v28 := v9 % 100 * 562949953421312
  let v29 := 2 * (v9 % 100)
  [y, sp, v, F, ret, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29]

theorem bh_100000 {y sp v F ret v5 v6 : Nat} (hy : 100000 ≤ y ∧ y < 1000000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_100000 y sp v F ret v5 v6) st_100000.ub ∧ LBHold (vals_100000 y sp v F ret v5 v6) st_100000.lb := by
  simp only [vals_100000, st_100000, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_100000 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 100000 ≤ y ∧ y < 1000000) :
    RwHold ⟨fun k => (vals_100000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_100000.rw := by
  exact ⟨(op_shloLm (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

def st_1000000 : Static :=
  { ub := [10000000, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 42949668665032705, 35184368571562792, 1000, 9990001, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199, 281193501733945345, 250, 1305508, 10, 901, 100, 56294995342131200, 199, 19]
    lb := [1000000, 2147484248, 0, 0, 2, 0, 0, 4294967296000000, 3518437209000000, 100, 1000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28147497671065600, 25, 131075, 1, 100, 0, 0, 0, 2]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm64 (.const 0) (.var 0) 32, .var 7),
    (.alu3 .mulUpperUU (.var 7) (.const 15111572745684516864) (.const 0), .var 8),
    (.alu2i .shloRImm64 (.const 0) (.var 8) 45, .var 9),
    (.alu3 .mul64 (.var 9) (.const 10000) (.const 0), .var 10),
    (.alu3 .sub64 (.var 0) (.var 10) (.const 0), .var 11),
    (.alu2i .shloLImm64 (.const 0) (.var 11) 48, .var 12),
    (.alu2i .shloRImm64 (.const 0) (.var 12) 50, .var 13),
    (.alu3 .mul64 (.var 13) (.const 5243) (.const 0), .var 14),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 16, .var 15),
    (.alu2i .andImm (.const 0) (.var 15) 2046, .var 16),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 17, .var 17),
    (.alu2i .mulImm64 (.const 0) (.var 17) 100, .var 18),
    (.alu3 .sub64 (.var 11) (.var 18) (.const 0), .var 19),
    (.alu2i .shloLImm64 (.const 0) (.var 19) 49, .var 20),
    (.alu2i .shloRImm64 (.const 0) (.var 20) 48, .var 21),
    (.alu2i .shloLImm64 (.const 0) (.var 9) 48, .var 22),
    (.alu2i .shloRImm64 (.const 0) (.var 22) 50, .var 23),
    (.alu2i .mulImm64 (.const 0) (.var 23) 5243, .var 24),
    (.alu2i .shloRImm64 (.const 0) (.var 24) 17, .var 25),
    (.alu2i .mulImm64 (.const 0) (.var 25) 100, .var 26),
    (.alu3 .sub64 (.var 9) (.var 26) (.const 0), .var 27),
    (.alu2i .shloLImm64 (.const 0) (.var 27) 49, .var 28),
    (.alu2i .shloRImm64 (.const 0) (.var 28) 48, .var 29),
    (.alu2i .shloLImm32 (.const 0) (.var 25) 1, .var 30)] }

def T_1000000 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -31 }), (12, PVM.SymExec.SVal.const 7)]
    cells := [({ base := some 1, off := -31 }, 1, PVM.SymExec.SVal.tbl [48, 48, 49, 48, 50, 48, 51, 48, 52, 48, 53, 48, 54, 48, 55, 48, 56, 48, 57] (PVM.SymExec.SVal.var 30)), ({ base := some 1, off := -30 }, 2, PVM.SymExec.SVal.mem0 { base := some 29, off := 70844 } 2), ({ base := some 1, off := -25 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70845 } 1), ({ base := some 1, off := -26 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70844 } 1), ({ base := some 1, off := -27 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70845 } 1), ({ base := some 1, off := -28 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70844 } 1)] }

set_option maxRecDepth 100000 in
theorem ok_1000000 : check st_1000000 Services.Bootstrap.SymExec.progF A T_1000000 [(⟨some 1, -72⟩, 72)] 68146 61857 94 = true := by
  decide +kernel

/-- The named naturals of the range 1000000 ≤ y < 10000000. -/
def vals_1000000 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := v0 * 4294967296
  let v8 := v7 * 15111572745684516864 / 18446744073709551616
  let v9 := v0 / 10000
  let v10 := v0 / 10000 * 10000
  let v11 := v0 % 10000
  let v12 := v0 % 10000 * 281474976710656
  let v13 := v0 % 10000 / 4
  let v14 := v0 % 10000 / 4 * 5243
  let v15 := v0 % 10000 / 4 * 5243 / 65536
  let v16 := 2 * (v0 % 10000 / 100)
  let v17 := v0 % 10000 / 100
  let v18 := v0 % 10000 / 100 * 100
  let v19 := v0 % 100
  let v20 := v0 % 100 * 562949953421312
  let v21 := 2 * (v0 % 100)
  let v22 := v9 * 281474976710656
  let v23 := v9 / 4
  let v24 := v9 / 4 * 5243
  let v25 := v9 / 100
  let v26 := v9 / 100 * 100
  let v27 := v9 % 100
  let v28 := v9 % 100 * 562949953421312
  let v29 := 2 * (v9 % 100)
  let v30 := 2 * (v9 / 100)
  [y, sp, v, F, ret, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30]

theorem bh_1000000 {y sp v F ret v5 v6 : Nat} (hy : 1000000 ≤ y ∧ y < 10000000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_1000000 y sp v F ret v5 v6) st_1000000.ub ∧ LBHold (vals_1000000 y sp v F ret v5 v6) st_1000000.lb := by
  simp only [vals_1000000, st_1000000, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_1000000 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 1000000 ≤ y ∧ y < 10000000) :
    RwHold ⟨fun k => (vals_1000000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_1000000.rw := by
  exact ⟨(op_shloLm (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloL32 (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

def st_10000000 : Static :=
  { ub := [100000000, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 429496725305032705, 351843717381562792, 10000, 99990001, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199, 42945377992705, 35180853652792, 1, 1, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199]
    lb := [10000000, 2147484248, 0, 0, 2, 0, 0, 42949672960000000, 35184372090000000, 1000, 10000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4294967296000, 3518437209000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm64 (.const 0) (.var 0) 32, .var 7),
    (.alu3 .mulUpperUU (.var 7) (.const 15111572745684516864) (.const 0), .var 8),
    (.alu2i .shloRImm64 (.const 0) (.var 8) 45, .var 9),
    (.alu3 .mul64 (.var 9) (.const 10000) (.const 0), .var 10),
    (.alu3 .sub64 (.var 0) (.var 10) (.const 0), .var 11),
    (.alu2i .shloLImm64 (.const 0) (.var 11) 48, .var 12),
    (.alu2i .shloRImm64 (.const 0) (.var 12) 50, .var 13),
    (.alu3 .mul64 (.var 13) (.const 5243) (.const 0), .var 14),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 16, .var 15),
    (.alu2i .andImm (.const 0) (.var 15) 2046, .var 16),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 17, .var 17),
    (.alu2i .mulImm64 (.const 0) (.var 17) 100, .var 18),
    (.alu3 .sub64 (.var 11) (.var 18) (.const 0), .var 19),
    (.alu2i .shloLImm64 (.const 0) (.var 19) 49, .var 20),
    (.alu2i .shloRImm64 (.const 0) (.var 20) 48, .var 21),
    (.alu2i .shloLImm64 (.const 0) (.var 9) 32, .var 22),
    (.alu3 .mulUpperUU (.var 22) (.const 15111572745684516864) (.const 0), .var 23),
    (.alu2i .shloRImm64 (.const 0) (.var 23) 45, .var 24),
    (.alu3 .mul64 (.var 24) (.const 10000) (.const 0), .var 25),
    (.alu3 .sub64 (.var 9) (.var 25) (.const 0), .var 26),
    (.alu2i .shloLImm64 (.const 0) (.var 26) 48, .var 27),
    (.alu2i .shloRImm64 (.const 0) (.var 27) 50, .var 28),
    (.alu3 .mul64 (.var 28) (.const 5243) (.const 0), .var 29),
    (.alu2i .shloRImm64 (.const 0) (.var 29) 16, .var 30),
    (.alu2i .andImm (.const 0) (.var 30) 2046, .var 31),
    (.alu2i .shloRImm64 (.const 0) (.var 29) 17, .var 32),
    (.alu2i .mulImm64 (.const 0) (.var 32) 100, .var 33),
    (.alu3 .sub64 (.var 26) (.var 33) (.const 0), .var 34),
    (.alu2i .shloLImm64 (.const 0) (.var 34) 49, .var 35),
    (.alu2i .shloRImm64 (.const 0) (.var 35) 48, .var 36)] }

def T_10000000 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -32 }), (12, PVM.SymExec.SVal.const 8)]
    cells := [({ base := some 1, off := -29 }, 1, PVM.SymExec.SVal.mem0 { base := some 36, off := 70845 } 1), ({ base := some 1, off := -30 }, 1, PVM.SymExec.SVal.mem0 { base := some 36, off := 70844 } 1), ({ base := some 1, off := -31 }, 1, PVM.SymExec.SVal.mem0 { base := some 31, off := 70845 } 1), ({ base := some 1, off := -32 }, 1, PVM.SymExec.SVal.mem0 { base := some 31, off := 70844 } 1), ({ base := some 1, off := -25 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70845 } 1), ({ base := some 1, off := -26 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70844 } 1), ({ base := some 1, off := -27 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70845 } 1), ({ base := some 1, off := -28 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70844 } 1)] }

set_option maxRecDepth 100000 in
theorem ok_10000000 : check st_10000000 Services.Bootstrap.SymExec.progF A T_10000000 [(⟨some 1, -72⟩, 72)] 68146 61857 107 = true := by
  decide +kernel

/-- The named naturals of the range 10000000 ≤ y < 100000000. -/
def vals_10000000 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := v0 * 4294967296
  let v8 := v7 * 15111572745684516864 / 18446744073709551616
  let v9 := v0 / 10000
  let v10 := v0 / 10000 * 10000
  let v11 := v0 % 10000
  let v12 := v0 % 10000 * 281474976710656
  let v13 := v0 % 10000 / 4
  let v14 := v0 % 10000 / 4 * 5243
  let v15 := v0 % 10000 / 4 * 5243 / 65536
  let v16 := 2 * (v0 % 10000 / 100)
  let v17 := v0 % 10000 / 100
  let v18 := v0 % 10000 / 100 * 100
  let v19 := v0 % 100
  let v20 := v0 % 100 * 562949953421312
  let v21 := 2 * (v0 % 100)
  let v22 := v9 * 4294967296
  let v23 := v22 * 15111572745684516864 / 18446744073709551616
  let v24 := v9 / 10000
  let v25 := v9 / 10000 * 10000
  let v26 := v9 % 10000
  let v27 := v9 % 10000 * 281474976710656
  let v28 := v9 % 10000 / 4
  let v29 := v9 % 10000 / 4 * 5243
  let v30 := v9 % 10000 / 4 * 5243 / 65536
  let v31 := 2 * (v9 % 10000 / 100)
  let v32 := v9 % 10000 / 100
  let v33 := v9 % 10000 / 100 * 100
  let v34 := v9 % 100
  let v35 := v9 % 100 * 562949953421312
  let v36 := 2 * (v9 % 100)
  [y, sp, v, F, ret, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36]

theorem bh_10000000 {y sp v F ret v5 v6 : Nat} (hy : 10000000 ≤ y ∧ y < 100000000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_10000000 y sp v F ret v5 v6) st_10000000.ub ∧ LBHold (vals_10000000 y sp v F ret v5 v6) st_10000000.lb := by
  simp only [vals_10000000, st_10000000, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_10000000 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 10000000 ≤ y ∧ y < 100000000) :
    RwHold ⟨fun k => (vals_10000000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_10000000.rw := by
  exact ⟨(op_shloLm (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

def st_100000000 : Static :=
  { ub := [1000000000, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 4294967291705032705, 3518437205481562792, 100000, 999990001, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199, 429492434632705, 351840202462792, 10, 90001, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199, 19]
    lb := [100000000, 2147484248, 0, 0, 2, 0, 0, 429496729600000000, 351843720900000000, 10000, 100000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42949672960000, 35184372090000, 1, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm64 (.const 0) (.var 0) 32, .var 7),
    (.alu3 .mulUpperUU (.var 7) (.const 15111572745684516864) (.const 0), .var 8),
    (.alu2i .shloRImm64 (.const 0) (.var 8) 45, .var 9),
    (.alu3 .mul64 (.var 9) (.const 10000) (.const 0), .var 10),
    (.alu3 .sub64 (.var 0) (.var 10) (.const 0), .var 11),
    (.alu2i .shloLImm64 (.const 0) (.var 11) 48, .var 12),
    (.alu2i .shloRImm64 (.const 0) (.var 12) 50, .var 13),
    (.alu3 .mul64 (.var 13) (.const 5243) (.const 0), .var 14),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 16, .var 15),
    (.alu2i .andImm (.const 0) (.var 15) 2046, .var 16),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 17, .var 17),
    (.alu2i .mulImm64 (.const 0) (.var 17) 100, .var 18),
    (.alu3 .sub64 (.var 11) (.var 18) (.const 0), .var 19),
    (.alu2i .shloLImm64 (.const 0) (.var 19) 49, .var 20),
    (.alu2i .shloRImm64 (.const 0) (.var 20) 48, .var 21),
    (.alu2i .shloLImm64 (.const 0) (.var 9) 32, .var 22),
    (.alu3 .mulUpperUU (.var 22) (.const 15111572745684516864) (.const 0), .var 23),
    (.alu2i .shloRImm64 (.const 0) (.var 23) 45, .var 24),
    (.alu3 .mul64 (.var 24) (.const 10000) (.const 0), .var 25),
    (.alu3 .sub64 (.var 9) (.var 25) (.const 0), .var 26),
    (.alu2i .shloLImm64 (.const 0) (.var 26) 48, .var 27),
    (.alu2i .shloRImm64 (.const 0) (.var 27) 50, .var 28),
    (.alu3 .mul64 (.var 28) (.const 5243) (.const 0), .var 29),
    (.alu2i .shloRImm64 (.const 0) (.var 29) 16, .var 30),
    (.alu2i .andImm (.const 0) (.var 30) 2046, .var 31),
    (.alu2i .shloRImm64 (.const 0) (.var 29) 17, .var 32),
    (.alu2i .mulImm64 (.const 0) (.var 32) 100, .var 33),
    (.alu3 .sub64 (.var 26) (.var 33) (.const 0), .var 34),
    (.alu2i .shloLImm64 (.const 0) (.var 34) 49, .var 35),
    (.alu2i .shloRImm64 (.const 0) (.var 35) 48, .var 36),
    (.alu2i .shloLImm32 (.const 0) (.var 24) 1, .var 37)] }

def T_100000000 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -33 }), (12, PVM.SymExec.SVal.const 9)]
    cells := [({ base := some 1, off := -33 }, 1, PVM.SymExec.SVal.tbl [48, 48, 49, 48, 50, 48, 51, 48, 52, 48, 53, 48, 54, 48, 55, 48, 56, 48, 57] (PVM.SymExec.SVal.var 37)), ({ base := some 1, off := -29 }, 1, PVM.SymExec.SVal.mem0 { base := some 36, off := 70845 } 1), ({ base := some 1, off := -30 }, 1, PVM.SymExec.SVal.mem0 { base := some 36, off := 70844 } 1), ({ base := some 1, off := -31 }, 1, PVM.SymExec.SVal.mem0 { base := some 31, off := 70845 } 1), ({ base := some 1, off := -32 }, 1, PVM.SymExec.SVal.mem0 { base := some 31, off := 70844 } 1), ({ base := some 1, off := -25 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70845 } 1), ({ base := some 1, off := -26 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70844 } 1), ({ base := some 1, off := -27 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70845 } 1), ({ base := some 1, off := -28 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70844 } 1)] }

set_option maxRecDepth 100000 in
theorem ok_100000000 : check st_100000000 Services.Bootstrap.SymExec.progF A T_100000000 [(⟨some 1, -72⟩, 72)] 68146 61857 116 = true := by
  decide +kernel

/-- The named naturals of the range 100000000 ≤ y < 1000000000. -/
def vals_100000000 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := v0 * 4294967296
  let v8 := v7 * 15111572745684516864 / 18446744073709551616
  let v9 := v0 / 10000
  let v10 := v0 / 10000 * 10000
  let v11 := v0 % 10000
  let v12 := v0 % 10000 * 281474976710656
  let v13 := v0 % 10000 / 4
  let v14 := v0 % 10000 / 4 * 5243
  let v15 := v0 % 10000 / 4 * 5243 / 65536
  let v16 := 2 * (v0 % 10000 / 100)
  let v17 := v0 % 10000 / 100
  let v18 := v0 % 10000 / 100 * 100
  let v19 := v0 % 100
  let v20 := v0 % 100 * 562949953421312
  let v21 := 2 * (v0 % 100)
  let v22 := v9 * 4294967296
  let v23 := v22 * 15111572745684516864 / 18446744073709551616
  let v24 := v9 / 10000
  let v25 := v9 / 10000 * 10000
  let v26 := v9 % 10000
  let v27 := v9 % 10000 * 281474976710656
  let v28 := v9 % 10000 / 4
  let v29 := v9 % 10000 / 4 * 5243
  let v30 := v9 % 10000 / 4 * 5243 / 65536
  let v31 := 2 * (v9 % 10000 / 100)
  let v32 := v9 % 10000 / 100
  let v33 := v9 % 10000 / 100 * 100
  let v34 := v9 % 100
  let v35 := v9 % 100 * 562949953421312
  let v36 := 2 * (v9 % 100)
  let v37 := 2 * v24
  [y, sp, v, F, ret, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37]

theorem bh_100000000 {y sp v F ret v5 v6 : Nat} (hy : 100000000 ≤ y ∧ y < 1000000000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_100000000 y sp v F ret v5 v6) st_100000000.ub ∧ LBHold (vals_100000000 y sp v F ret v5 v6) st_100000000.lb := by
  simp only [vals_100000000, st_100000000, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_100000000 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 100000000 ≤ y ∧ y < 1000000000) :
    RwHold ⟨fun k => (vals_100000000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_100000000.rw := by
  exact ⟨(op_shloLm (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloL32 (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

def st_1000000000 : Static :=
  { ub := [2147483648, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 9223372032559808513, 7555786369323821224, 214749, 2147480001, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199, 922335636881409, 755577353758333, 22, 210001, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199, 5910974510923777, 6, 26216, 1, 1, 100, 56294995342131200, 199]
    lb := [1000000000, 2147484248, 0, 0, 2, 0, 0, 4294967296000000000, 3518437209000000000, 100000, 1000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 429496729600000, 351843720900000, 10, 100000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2814749767106560, 2, 10486, 0, 0, 0, 0, 0]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm64 (.const 0) (.var 0) 32, .var 7),
    (.alu3 .mulUpperUU (.var 7) (.const 15111572745684516864) (.const 0), .var 8),
    (.alu2i .shloRImm64 (.const 0) (.var 8) 45, .var 9),
    (.alu3 .mul64 (.var 9) (.const 10000) (.const 0), .var 10),
    (.alu3 .sub64 (.var 0) (.var 10) (.const 0), .var 11),
    (.alu2i .shloLImm64 (.const 0) (.var 11) 48, .var 12),
    (.alu2i .shloRImm64 (.const 0) (.var 12) 50, .var 13),
    (.alu3 .mul64 (.var 13) (.const 5243) (.const 0), .var 14),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 16, .var 15),
    (.alu2i .andImm (.const 0) (.var 15) 2046, .var 16),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 17, .var 17),
    (.alu2i .mulImm64 (.const 0) (.var 17) 100, .var 18),
    (.alu3 .sub64 (.var 11) (.var 18) (.const 0), .var 19),
    (.alu2i .shloLImm64 (.const 0) (.var 19) 49, .var 20),
    (.alu2i .shloRImm64 (.const 0) (.var 20) 48, .var 21),
    (.alu2i .shloLImm64 (.const 0) (.var 9) 32, .var 22),
    (.alu3 .mulUpperUU (.var 22) (.const 15111572745684516864) (.const 0), .var 23),
    (.alu2i .shloRImm64 (.const 0) (.var 23) 45, .var 24),
    (.alu3 .mul64 (.var 24) (.const 10000) (.const 0), .var 25),
    (.alu3 .sub64 (.var 9) (.var 25) (.const 0), .var 26),
    (.alu2i .shloLImm64 (.const 0) (.var 26) 48, .var 27),
    (.alu2i .shloRImm64 (.const 0) (.var 27) 50, .var 28),
    (.alu3 .mul64 (.var 28) (.const 5243) (.const 0), .var 29),
    (.alu2i .shloRImm64 (.const 0) (.var 29) 16, .var 30),
    (.alu2i .andImm (.const 0) (.var 30) 2046, .var 31),
    (.alu2i .shloRImm64 (.const 0) (.var 29) 17, .var 32),
    (.alu2i .mulImm64 (.const 0) (.var 32) 100, .var 33),
    (.alu3 .sub64 (.var 26) (.var 33) (.const 0), .var 34),
    (.alu2i .shloLImm64 (.const 0) (.var 34) 49, .var 35),
    (.alu2i .shloRImm64 (.const 0) (.var 35) 48, .var 36),
    (.alu2i .shloLImm64 (.const 0) (.var 24) 48, .var 37),
    (.alu2i .shloRImm64 (.const 0) (.var 37) 50, .var 38),
    (.alu2i .mulImm64 (.const 0) (.var 38) 5243, .var 39),
    (.alu2i .shloRImm64 (.const 0) (.var 39) 17, .var 40),
    (.alu2i .mulImm64 (.const 0) (.var 40) 100, .var 41),
    (.alu3 .sub64 (.var 24) (.var 41) (.const 0), .var 42),
    (.alu2i .shloLImm64 (.const 0) (.var 42) 49, .var 43),
    (.alu2i .shloRImm64 (.const 0) (.var 43) 48, .var 44)] }

def T_1000000000 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -34 }), (12, PVM.SymExec.SVal.const 10)]
    cells := [({ base := some 1, off := -34 }, 2, PVM.SymExec.SVal.mem0 { base := some 44, off := 70844 } 2), ({ base := some 1, off := -29 }, 1, PVM.SymExec.SVal.mem0 { base := some 36, off := 70845 } 1), ({ base := some 1, off := -30 }, 1, PVM.SymExec.SVal.mem0 { base := some 36, off := 70844 } 1), ({ base := some 1, off := -31 }, 1, PVM.SymExec.SVal.mem0 { base := some 31, off := 70845 } 1), ({ base := some 1, off := -32 }, 1, PVM.SymExec.SVal.mem0 { base := some 31, off := 70844 } 1), ({ base := some 1, off := -25 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70845 } 1), ({ base := some 1, off := -26 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70844 } 1), ({ base := some 1, off := -27 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70845 } 1), ({ base := some 1, off := -28 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70844 } 1)] }

set_option maxRecDepth 100000 in
theorem ok_1000000000 : check st_1000000000 Services.Bootstrap.SymExec.progF A T_1000000000 [(⟨some 1, -72⟩, 72)] 68146 61857 123 = true := by
  decide +kernel

/-- The named naturals of the range 1000000000 ≤ y < 2147483648. -/
def vals_1000000000 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := v0 * 4294967296
  let v8 := v7 * 15111572745684516864 / 18446744073709551616
  let v9 := v0 / 10000
  let v10 := v0 / 10000 * 10000
  let v11 := v0 % 10000
  let v12 := v0 % 10000 * 281474976710656
  let v13 := v0 % 10000 / 4
  let v14 := v0 % 10000 / 4 * 5243
  let v15 := v0 % 10000 / 4 * 5243 / 65536
  let v16 := 2 * (v0 % 10000 / 100)
  let v17 := v0 % 10000 / 100
  let v18 := v0 % 10000 / 100 * 100
  let v19 := v0 % 100
  let v20 := v0 % 100 * 562949953421312
  let v21 := 2 * (v0 % 100)
  let v22 := v9 * 4294967296
  let v23 := v22 * 15111572745684516864 / 18446744073709551616
  let v24 := v9 / 10000
  let v25 := v9 / 10000 * 10000
  let v26 := v9 % 10000
  let v27 := v9 % 10000 * 281474976710656
  let v28 := v9 % 10000 / 4
  let v29 := v9 % 10000 / 4 * 5243
  let v30 := v9 % 10000 / 4 * 5243 / 65536
  let v31 := 2 * (v9 % 10000 / 100)
  let v32 := v9 % 10000 / 100
  let v33 := v9 % 10000 / 100 * 100
  let v34 := v9 % 100
  let v35 := v9 % 100 * 562949953421312
  let v36 := 2 * (v9 % 100)
  let v37 := v24 * 281474976710656
  let v38 := v24 / 4
  let v39 := v24 / 4 * 5243
  let v40 := v24 / 100
  let v41 := v24 / 100 * 100
  let v42 := v24 % 100
  let v43 := v24 % 100 * 562949953421312
  let v44 := 2 * (v24 % 100)
  [y, sp, v, F, ret, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44]

theorem bh_1000000000 {y sp v F ret v5 v6 : Nat} (hy : 1000000000 ≤ y ∧ y < 2147483648) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_1000000000 y sp v F ret v5 v6) st_1000000000.ub ∧ LBHold (vals_1000000000 y sp v F ret v5 v6) st_1000000000.lb := by
  simp only [vals_1000000000, st_1000000000, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_1000000000 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 1000000000 ≤ y ∧ y < 2147483648) :
    RwHold ⟨fun k => (vals_1000000000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_1000000000.rw := by
  exact ⟨(op_shloLm (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

def st_2147483648 : Static :=
  { ub := [4294967296, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 18446744069414584321, 15111572742166079656, 429497, 4294960001, 18446744073709551616, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 18446744073709551616, 56294995342131200, 199, 1844671273762817, 1511154707516665, 43, 420001, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199, 11821949021847553, 11, 52431, 1, 1, 100, 56294995342131200, 199]
    lb := [2147483648, 2147484248, 0, 0, 2, 0, 0, 9223372036854775808, 7555786372842258432, 214748, 2147480000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 922335636881408, 755577353758332, 21, 210000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5910974510923776, 5, 26215, 0, 0, 0, 0, 0]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm64 (.const 0) (.sx 4 (.var 0)) 32, .var 7),
    (.alu3 .mulUpperUU (.var 7) (.const 15111572745684516864) (.const 0), .var 8),
    (.alu2i .shloRImm64 (.const 0) (.var 8) 45, .var 9),
    (.alu3 .mul64 (.var 9) (.const 10000) (.const 0), .var 10),
    (.alu3 .sub64 (.sx 4 (.var 0)) (.var 10) (.const 0), .var 11),
    (.alu2i .shloLImm64 (.const 0) (.var 11) 48, .var 12),
    (.alu2i .shloRImm64 (.const 0) (.var 12) 50, .var 13),
    (.alu3 .mul64 (.var 13) (.const 5243) (.const 0), .var 14),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 16, .var 15),
    (.alu2i .andImm (.const 0) (.var 15) 2046, .var 16),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 17, .var 17),
    (.alu2i .mulImm64 (.const 0) (.var 17) 100, .var 18),
    (.alu3 .sub64 (.var 11) (.var 18) (.const 0), .var 19),
    (.alu2i .shloLImm64 (.const 0) (.var 19) 49, .var 20),
    (.alu2i .shloRImm64 (.const 0) (.var 20) 48, .var 21),
    (.alu2i .shloLImm64 (.const 0) (.var 9) 32, .var 22),
    (.alu3 .mulUpperUU (.var 22) (.const 15111572745684516864) (.const 0), .var 23),
    (.alu2i .shloRImm64 (.const 0) (.var 23) 45, .var 24),
    (.alu3 .mul64 (.var 24) (.const 10000) (.const 0), .var 25),
    (.alu3 .sub64 (.var 9) (.var 25) (.const 0), .var 26),
    (.alu2i .shloLImm64 (.const 0) (.var 26) 48, .var 27),
    (.alu2i .shloRImm64 (.const 0) (.var 27) 50, .var 28),
    (.alu3 .mul64 (.var 28) (.const 5243) (.const 0), .var 29),
    (.alu2i .shloRImm64 (.const 0) (.var 29) 16, .var 30),
    (.alu2i .andImm (.const 0) (.var 30) 2046, .var 31),
    (.alu2i .shloRImm64 (.const 0) (.var 29) 17, .var 32),
    (.alu2i .mulImm64 (.const 0) (.var 32) 100, .var 33),
    (.alu3 .sub64 (.var 26) (.var 33) (.const 0), .var 34),
    (.alu2i .shloLImm64 (.const 0) (.var 34) 49, .var 35),
    (.alu2i .shloRImm64 (.const 0) (.var 35) 48, .var 36),
    (.alu2i .shloLImm64 (.const 0) (.var 24) 48, .var 37),
    (.alu2i .shloRImm64 (.const 0) (.var 37) 50, .var 38),
    (.alu2i .mulImm64 (.const 0) (.var 38) 5243, .var 39),
    (.alu2i .shloRImm64 (.const 0) (.var 39) 17, .var 40),
    (.alu2i .mulImm64 (.const 0) (.var 40) 100, .var 41),
    (.alu3 .sub64 (.var 24) (.var 41) (.const 0), .var 42),
    (.alu2i .shloLImm64 (.const 0) (.var 42) 49, .var 43),
    (.alu2i .shloRImm64 (.const 0) (.var 43) 48, .var 44)] }

def T_2147483648 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -34 }), (12, PVM.SymExec.SVal.const 10)]
    cells := [({ base := some 1, off := -34 }, 2, PVM.SymExec.SVal.mem0 { base := some 44, off := 70844 } 2), ({ base := some 1, off := -29 }, 1, PVM.SymExec.SVal.mem0 { base := some 36, off := 70845 } 1), ({ base := some 1, off := -30 }, 1, PVM.SymExec.SVal.mem0 { base := some 36, off := 70844 } 1), ({ base := some 1, off := -31 }, 1, PVM.SymExec.SVal.mem0 { base := some 31, off := 70845 } 1), ({ base := some 1, off := -32 }, 1, PVM.SymExec.SVal.mem0 { base := some 31, off := 70844 } 1), ({ base := some 1, off := -25 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70845 } 1), ({ base := some 1, off := -26 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70844 } 1), ({ base := some 1, off := -27 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70845 } 1), ({ base := some 1, off := -28 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70844 } 1)] }

set_option maxRecDepth 100000 in
theorem ok_2147483648 : check st_2147483648 Services.Bootstrap.SymExec.progF A T_2147483648 [(⟨some 1, -72⟩, 72)] 68146 61857 123 = true := by
  decide +kernel

/-- The named naturals of the range 2147483648 ≤ y < 4294967296. -/
def vals_2147483648 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := v0 * 4294967296
  let v8 := v7 * 15111572745684516864 / 18446744073709551616
  let v9 := v0 / 10000
  let v10 := v0 / 10000 * 10000
  let v11 := v0 + 18446744069414584320 - v0 / 10000 * 10000
  let v12 := v0 % 10000 * 281474976710656
  let v13 := v0 % 10000 / 4
  let v14 := v0 % 10000 / 4 * 5243
  let v15 := v0 % 10000 / 4 * 5243 / 65536
  let v16 := 2 * (v0 % 10000 / 100)
  let v17 := v0 % 10000 / 100
  let v18 := v0 % 10000 / 100 * 100
  let v19 := v0 + 18446744069414584320 - v0 / 10000 * 10000 - v0 % 10000 / 100 * 100
  let v20 := v0 % 100 * 562949953421312
  let v21 := 2 * (v0 % 100)
  let v22 := v9 * 4294967296
  let v23 := v22 * 15111572745684516864 / 18446744073709551616
  let v24 := v9 / 10000
  let v25 := v9 / 10000 * 10000
  let v26 := v9 % 10000
  let v27 := v9 % 10000 * 281474976710656
  let v28 := v9 % 10000 / 4
  let v29 := v9 % 10000 / 4 * 5243
  let v30 := v9 % 10000 / 4 * 5243 / 65536
  let v31 := 2 * (v9 % 10000 / 100)
  let v32 := v9 % 10000 / 100
  let v33 := v9 % 10000 / 100 * 100
  let v34 := v9 % 100
  let v35 := v9 % 100 * 562949953421312
  let v36 := 2 * (v9 % 100)
  let v37 := v24 * 281474976710656
  let v38 := v24 / 4
  let v39 := v24 / 4 * 5243
  let v40 := v24 / 100
  let v41 := v24 / 100 * 100
  let v42 := v24 % 100
  let v43 := v24 % 100 * 562949953421312
  let v44 := 2 * (v24 % 100)
  [y, sp, v, F, ret, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44]

theorem bh_2147483648 {y sp v F ret v5 v6 : Nat} (hy : 2147483648 ≤ y ∧ y < 4294967296) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_2147483648 y sp v F ret v5 v6) st_2147483648.ub ∧ LBHold (vals_2147483648 y sp v F ret v5 v6) st_2147483648.lb := by
  simp only [vals_2147483648, st_2147483648, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_2147483648 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 2147483648 ≤ y ∧ y < 4294967296) :
    RwHold ⟨fun k => (vals_2147483648 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_2147483648.rw := by
  exact ⟨(op_shloL_sx (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub_sx (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

end Services.Bootstrap.SymExec.Dec32
