import Services.Bootstrap.SymExec.Utf8Word

/-!
# `core::str::from_utf8` (60681): the outer loop 60738 (symexec, loops) — checks

EXPERIMENTAL, WORK IN PROGRESS (see `Services/Bootstrap/SymExec/README.md`). The forking checks of
the outer loop's body (GP v0.8.0 §A.5): from the header 60738 to the misaligned step 60731, the
aligned branch 60756, and the multi-octet arms at 60829 (after the table base 71078 is loaded);
from 60829 to the continuation 61079 (k = 1, 2, 3 continuation octets) or the error exit 61138
(error_len none, or some 1, 2, 3).

The table load at 60832 reads μ[71078 + b], b the first octet: the base is the named natural 13
(pinned to 71078 by the bounds) and b the named natural 14, with the fact ρ13 + ρ14 = ρ15, so
the address is affine; it is readable by the fact `rd 71078 71334`. Nothing is assumed about the
table's contents.

Named naturals as in `Utf8Byte` (0 p, 1 len, 2 i, 3 q, 4 sp, 5 align, 6 r4, 7 r11, 8 ret, 9/10
saved r5/r6, 11 r7, 12 e); at 60829 also 13 t = 71078, 14 b, 15 t + b; at 61079 13 is the index of
the last continuation octet.
-/

namespace Services.Bootstrap.SymExec.Utf8

open PVM PVM.SymExec Num Exec

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def ub1 : List Nat :=
  [2^32, 2^32, 2^32, 2^32, 2^32 - 32, 8, 2^32, 2^64, 2^64, 2^64, 2^64, 2^32, 2^32 + 1, 2^64, 2^64]
def lb1 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The registers at the header 60738 (r4 = m = max(len, 15) − 15). -/
def regs1 : List (Nat × SVal) :=
  [(0, vr 5), (1, vr 4), (3, .const 1), (4, vr 6), (5, vr 2), (7, vr 11), (8, vr 0), (9, vr 1),
    (11, vr 7)]
/-- The four saved stack words. -/
def cells1 : List (Aff × Nat × SVal) :=
  [(af 4 24, 8, vr 8), (af 4 16, 8, vr 9), (af 4 8, 8, vr 10), (af 4 0, 8, .const 71078)]

/-- The header cut at 60738. -/
def H1 : Cut := ⟨regs1, cells1, [], [], [(af 4 0, 32)]⟩

/-- q = p + i, i < len, e = p + len, [p, e), the table and the stack frame readable. -/
def asm1 : List Fact :=
  [.sum 0 2 3, .le (af 2 1) (af 1 0), .sum 0 1 12, .rd (af 0 0) (af 12 0),
    .rd ⟨none, 71078⟩ ⟨none, 71334⟩, .rd (af 4 0) (af 4 32)]

/-- The first octet masked to 8 bits (the value of r10 at 60829). -/
def bterm : SVal := .alu2i .andImm (.const 0) (.sx 1 (.mem0 (af 3 0) 1)) 255

/-- At 60829: r10 = b, r12 = t. -/
def H1b : Cut := ⟨regs1 ++ [(10, vr 14), (12, vr 13)], cells1, [], [], [(af 4 0, 32)]⟩

def sub1b : List SVal :=
  [vr 0, vr 1, vr 2, vr 3, vr 4, vr 5, vr 6, vr 7, vr 8, vr 9, vr 10, vr 11, vr 12, .const 71078,
    bterm, .const 0]

def leaves1 : List Leaf :=
  [⟨60731, [], H1, idsub15⟩, ⟨60756, [], H1, idsub15⟩, ⟨60829, [], H1b, sub1b⟩]

theorem check1 : forkCheckW progU ub1 lb1 [] H1 asm1 leaves1 60738 300 = true := by
  decide +kernel

def ub1b : List Nat :=
  [2^32, 2^32, 2^32, 2^32, 2^32 - 32, 8, 2^32, 2^64, 2^64, 2^64, 2^64, 2^32, 2^32 + 1, 71079, 256,
    71334]
def lb1b : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 71078, 0, 71078]
def asm1b : List Fact := asm1 ++ [.sum 13 14 15]

/-- The error exit 61138 with r2 = c2 (0: error_len none) and r3 = c3. -/
def HE (c2 c3 : Nat) : Cut :=
  ⟨[(0, vr 5), (1, vr 4), (2, .const c2), (3, .const c3), (4, vr 6), (5, vr 2), (7, vr 11),
    (8, vr 0), (9, vr 1), (11, vr 7)], cells1, [], [], [(af 4 0, 32)]⟩

/-- The continuation 61079: r6 = the index of the last continuation octet (named natural 13). -/
def H6 : Cut :=
  ⟨[(0, vr 5), (1, vr 4), (3, .const 1), (4, vr 6), (5, vr 2), (6, vr 13), (7, vr 11), (8, vr 0),
    (9, vr 1), (11, vr 7)], cells1, [], [], [(af 4 0, 32)]⟩

def sub6 (k : Int) : List SVal :=
  [vr 0, vr 1, vr 2, vr 3, vr 4, vr 5, vr 6, vr 7, vr 8, vr 9, vr 10, vr 11, vr 12, .addr (af 2 k),
    vr 14]

def leaves1b : List Leaf :=
  [⟨61138, [], HE 0 1, idsub15⟩, ⟨61138, [], HE 1 1, idsub15⟩, ⟨61138, [], HE 1 2, idsub15⟩,
   ⟨61138, [], HE 1 3, idsub15⟩, ⟨61079, [], H6, sub6 1⟩, ⟨61079, [], H6, sub6 2⟩,
   ⟨61079, [], H6, sub6 3⟩]

theorem check1b : forkCheckW progU ub1b lb1b [] H1b asm1b leaves1b 60829 300 = true := by
  decide +kernel

/-- The Ok exit 61086: what the epilogue reads (r1, r7, r8, r9 and the saved words). -/
def HOk : Cut := ⟨[(1, vr 4), (7, vr 11), (8, vr 0), (9, vr 1)], cells1, [], [], [(af 4 0, 32)]⟩

/-- idsub15 with i ↦ `i'` and q ↦ `q'`. -/
def nxtI (i' q' : SVal) : List SVal :=
  [vr 0, vr 1, i', q', vr 4, vr 5, vr 6, vr 7, vr 8, vr 9, vr 10, vr 11, vr 12, vr 13, vr 14]

/-- 61079 → 60738 (i := j + 1 < len) or 61086. -/
def ub6 : List Nat :=
  [2^32, 2^32, 2^32, 2^32, 2^32 - 32, 8, 2^32, 2^64, 2^64, 2^64, 2^64, 2^32, 2^32 + 1, 2^32 + 3, 2^64]
def leaves6 : List Leaf :=
  [⟨60738, [.le (af 13 2) (af 1 0)], H1, nxtI (.addr (af 13 1)) (.const 0)⟩,
   ⟨61086, [.le (af 1 0) (af 13 1)], HOk, idsub15⟩]
theorem check6 : forkCheck progU ub6 lb1 [] H6 asm1 leaves6 61079 100 = true := by
  decide +kernel

/-- 60731 (a misaligned octet < 0x80) → 60738 (i + 1 < len) or 61086. -/
def leaves7 : List Leaf :=
  [⟨61086, [.le (af 1 0) (af 2 1)], HOk, idsub15⟩,
   ⟨60738, [.le (af 2 2) (af 1 0)], H1, nxtI (.addr (af 2 1)) (.addr (af 3 1))⟩]
theorem check7 : forkCheck progU ub1 lb1 [] H1 asm1 leaves7 60731 100 = true := by
  decide +kernel

/-- 60756 (aligned) → 60793 (i ≥ m) or the word loop 60759 (i < m). -/
def leaves8 : List Leaf :=
  [⟨60793, [.le (af 6 0) (af 2 0)], H1, idsub15⟩, ⟨60759, [.le (af 2 1) (af 6 0)], H1, idsub15⟩]
theorem check8 : forkCheck progU ub1 lb1 [] H1 asm1 leaves8 60756 100 = true := by
  decide +kernel

/-- 60793 (i ≤ len) → 61086 (i = len) or the byte loop 60803 (r6 = 2^64 − i, r5 = i). -/
def ub4 : List Nat :=
  [2^32, 2^32, 2^32, 2^32 + 1, 2^32 - 32, 8, 2^32, 2^64, 2^64, 2^64, 2^64, 2^32, 2^32 + 1, 2^64, 2^64]
def asm4 : List Fact := [.sum 0 2 3, .le (af 2 0) (af 1 0), .sum 0 1 12, .rd (af 0 0) (af 12 0)]
def sub4 : List SVal :=
  [vr 0, vr 1, vr 2, vr 3, vr 4, vr 5, vr 6, vr 7, vr 8, vr 9, vr 10, vr 11, vr 12,
    .alu2i .negAddImm64 (.const 0) (vr 2) 0, vr 2]
def leaves4 : List Leaf :=
  [⟨61086, [.le (af 1 0) (af 2 0)], HOk, idsub15⟩, ⟨60803, [.le (af 2 1) (af 1 0)], H3, sub4⟩]
theorem check4 : forkCheck progU ub4 lb1 [] H1 asm4 leaves4 60793 100 = true := by
  decide +kernel

/-- 60943 (the byte loop found an octet ≥ 0x80) → 60946, r5 := 2^64 − r6 (= i). -/
def H5a : Cut :=
  ⟨[(0, vr 5), (1, vr 4), (3, .const 1), (4, vr 6), (5, .alu2i .negAddImm64 (.const 0) (vr 13) 0),
    (6, vr 13), (7, vr 11), (8, vr 0), (9, vr 1), (10, vr 3), (11, vr 7)], cells1, [], [],
   [(af 4 0, 32)]⟩
theorem check5a : forkCheckW progU ub3x lb3 [] H3 asm3 [⟨60946, [], H5a, idsub15⟩] 60943 100 = true := by
  decide +kernel

/-- 60946 (i < len) → 60738. -/
theorem check5b : forkCheck progU ub1 lb1 [] H1 asm1 [⟨60738, [], H1, idsub15⟩] 60946 100 = true := by
  decide +kernel

end Services.Bootstrap.SymExec.Utf8
