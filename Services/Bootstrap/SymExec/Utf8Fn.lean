import Services.Bootstrap.SymExec.Utf8Loop

/-!
# `core::str::from_utf8` (60681): pre-loop and epilogues (symexec)

EXPERIMENTAL, WORK IN PROGRESS (see `Services/Bootstrap/SymExec/README.md`). The forking checks
around the outer loop (GP v0.8.0 §A.5):
- `check0`: the entry 60681 (allocates the 32-octet frame, saves r0, r5, r6 and the table base)
  to 61086 when len = 0, or to the loop header 60738 with i = 0, align = ((p + 7) & ~7) − p,
  m = max(len, 15) − 15 and r11 = 2^64 − len.
- `checkOk`: 61086 → 61107: stores the result `Ok(&v[..len])` (0, p, len) at r7, restores r0, r5,
  r6, frees the frame; 61107 is `jump_ind r0`.
- `checkErr`: 61138 → 61164: stores `Err(Utf8Error { valid_up_to: i, error_len })` (1, i, r2, r3)
  at r7, restores, frees the frame; 61164 is `jump_ind r0`.

Named naturals at the entry: 0 p, 1 len, 4 sp (the frame base, r1 − 32 at entry), 8 the return
address, 9/10 the caller's r5/r6, 11 r7 (the result's address), 12 e = p + len. In `HEE`/`HEX`,
2 is valid_up_to, 13 the error_len tag and 14 its value.
-/

namespace Services.Bootstrap.SymExec.Utf8

open PVM PVM.SymExec Num Exec

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- The entry cut at 60681: the frame [sp, sp + 32) and the result [r7, r7 + 24) writable. -/
def H0 : Cut :=
  ⟨[(0, vr 8), (1, .addr (af 4 32)), (5, vr 9), (6, vr 10), (7, vr 11), (8, vr 0), (9, vr 1)], [], [],
   [(af 4 0, 32), (af 11 0, 24)], [(af 4 0, 32)]⟩

def ub0 : List Nat :=
  [2^32, 2^32, 2^32, 2^32, 2^32 - 32, 8, 2^32, 2^64, 2^64, 2^64, 2^64, 2^32 - 24, 2^32 + 1, 2^64, 2^64]

/-- e = p + len, the input and the table readable. -/
def asm0 : List Fact := [.sum 0 1 12, .rd (af 0 0) (af 12 0), .rd ⟨none, 71078⟩ ⟨none, 71334⟩]

/-- The three saved words. -/
def cells3 : List (Aff × Nat × SVal) := [(af 4 24, 8, vr 8), (af 4 16, 8, vr 9), (af 4 8, 8, vr 10)]

/-- The Ok exit 61086 as the epilogue needs it: the frame readable, the result writable. -/
def HOkE : Cut :=
  ⟨[(1, vr 4), (7, vr 11), (8, vr 0), (9, vr 1)], cells3, [(af 4 0, 32)], [(af 11 0, 24)],
   [(af 4 0, 32)]⟩

/-- align = ((p + 7) & ~7) − p. -/
def alignT : SVal :=
  .alu3 .sub64 (.alu2i .andImm (.const 0) (.addr (af 0 7)) (2^64 - 8)) (vr 0) (.const 0)
/-- m = max(len, 15) − 15. -/
def mT : SVal :=
  .alu2i .addImm64 (.const 0) (.mod (.alu3 .maxU (vr 1) (.const 15) (.const 0)) (2^64)) (2^64 - 15)
/-- r11 = 2^64 − len. -/
def r11T : SVal := .alu2i .negAddImm64 (.const 0) (vr 1) 0

/-- The loop's named naturals at its first entry. -/
def sub0 : List SVal :=
  [vr 0, vr 1, .const 0, .addr (af 0 0), vr 4, alignT, mT, r11T, vr 8, vr 9, vr 10, vr 11, vr 12,
    .const 0, .const 0]

def leaves0 : List Leaf :=
  [⟨61086, [.ge (vr 1) 0, .lt (vr 1) 1], HOkE, idsub15⟩, ⟨60738, [.ne (vr 1) 0], H1, sub0⟩]

theorem check0 : forkCheck progU ub0 lb1 [] H0 asm0 leaves0 60681 200 = true := by
  decide +kernel

/-- The result [r7, r7 + 24) apart from the frame. -/
def sepE : List ((Aff × Nat) × (Aff × Nat)) := [((af 11 0, 24), (af 4 0, 32))]

def ubE : List Nat :=
  [2^32, 2^32, 2^32, 2^32, 2^32 - 32, 8, 2^32, 2^64, 2^64, 2^64, 2^64, 2^32 - 24, 2^32 + 1, 2, 4]

/-- At the return 61107 / 61164: r0, r1, r5, r6 restored, the result written. -/
def HOkX : Cut :=
  ⟨[(0, vr 8), (1, .addr (af 4 32)), (5, vr 9), (6, vr 10)],
   [(af 11 0, 8, .const 0), (af 11 8, 8, vr 0), (af 11 16, 8, vr 1)], [], [],
   [(af 4 0, 32), (af 11 0, 24)]⟩

theorem checkOk : forkCheck progU ubE lb1 sepE HOkE [] [⟨61107, [], HOkX, idsub15⟩] 61086 100 = true := by
  decide +kernel

/-- The error exit 61138 as the epilogue needs it (r2 = ρ13, r3 = ρ14). -/
def HEE : Cut :=
  ⟨[(1, vr 4), (2, vr 13), (3, vr 14), (5, vr 2), (7, vr 11)], cells3, [(af 4 0, 32)],
   [(af 11 0, 24)], [(af 4 0, 32)]⟩

def HEX : Cut :=
  ⟨[(0, vr 8), (1, .addr (af 4 32)), (5, vr 9), (6, vr 10)],
   [(af 11 0, 8, .const 1), (af 11 8, 8, vr 2), (af 11 16, 1, vr 13), (af 11 17, 1, vr 14)], [], [],
   [(af 4 0, 32), (af 11 0, 24)]⟩

theorem checkErr : forkCheck progU ubE lb1 sepE HEE [] [⟨61164, [], HEX, idsub15⟩] 61138 100 = true := by
  decide +kernel

end Services.Bootstrap.SymExec.Utf8
