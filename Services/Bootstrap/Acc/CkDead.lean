import Services.Bootstrap.CodeAAll
import PVM.Logic.Dead7

/-!
# ω₇ is dead after bootstrap's `checkpoint` calls

After each `ecalli 18` (`checkpoint`, Ω_C, GP v0.8.0 eq. `accinvocation`), which reports the gas
left in ω₇, the code overwrites ω₇ before it reads it (`PVM.Dead7`):
- after 8490: `fallthrough`, a load into ω₈, then `ω₇ := ω₈ · 232` (8497);
- after 9944: `ω₇ := 13` (9946);
- after 11889 (`Benchmark`'s loop): a load into ω₈ and its increment, then a branch on ω₈. One
  way, `ω₇ := ω₁ + 1380` (11914), after two stores. The other way, a byte store, a load into ω₈
  and a branch on it, then `ω₇ := ω₁ + 1144` (14268) or a load into ω₇ (13890).
Every step on the way neither reads nor writes ω₇. The facts are proved from the code facts
(`CodeA`), one instruction at a time.
-/

namespace Services.Bootstrap.Acc.CkDead

open PVM Services.Bootstrap.CodeA

/-- Unfold one gas-free step at a decoded instruction. -/
macro "fs_simp" "[" xs:Lean.Parser.Tactic.simpLemma,* "]" hd:term : tactic => `(tactic| (
  simp [Program.freeStep_of_decode _ _ ($hd).2.1, Program.exec, Program.finalState, memoryException,
    Regs.get, Vector.set_set, Program.sjump, Program.branch,
    Program.isBlockStartInt, ($hd).2.2.1, $xs,*]))

/-- A step that passes ω₇ along to dead indices `js` (proved by `hjs`). -/
macro "dead_pass" "[" xs:Lean.Parser.Tactic.simpLemma,* "]" hd:term "to" js:term "by" hjs:term : tactic => `(tactic| (
  refine Dead7.pass_to $js ($hd).1 (fun ω μ v => ?_) (fun ω μ => ?_) (fun ω μ => ?_) $hjs
  · fs_simp [$xs,*] $hd
    try (split <;> simp_all [Vector.set_comm])
    try simp [Vector.set_comm]
  · fs_simp [$xs,*] $hd
    try (split <;> simp_all [Status.Quiet])
    try (repeat' split) <;> simp_all [Status.Quiet]
  · fs_simp [$xs,*] $hd
    try (split <;> simp_all)))

theorem k8497 {p : ByteArray} {P : Program} [HasCodeA p P] : Dead7 p 8497 := by
  have hd := d_8497 (p := p) (P := P)
  refine Dead7.kill_of' hd.1 (fun ω μ v => ?_) (fun ω μ => ?_)
  · fs_simp [Exec.twoRegImmAlu] hd
  · fs_simp [] hd

theorem p8493 {p : ByteArray} {P : Program} [HasCodeA p P] : Dead7 p 8493 := by
  have hd := d_8493 (p := p) (P := P)
  dead_pass [] hd to [8497] by (by simp; exact k8497 (P := P))

theorem p8492 {p : ByteArray} {P : Program} [HasCodeA p P] : Dead7 p 8492 := by
  have hd := d_8492 (p := p) (P := P)
  dead_pass [bs_8493] hd to [8493] by (by simp; exact p8493 (P := P))

theorem k9946 {p : ByteArray} {P : Program} [HasCodeA p P] : Dead7 p 9946 := by
  have hd := d_9946 (p := p) (P := P)
  refine Dead7.kill_of' hd.1 (fun ω μ v => ?_) (fun ω μ => ?_)
  · fs_simp [] hd
    try (split <;> simp_all)
  · fs_simp [] hd
    try (split <;> simp_all)

theorem k14268 {p : ByteArray} {P : Program} [HasCodeA p P] : Dead7 p 14268 := by
  have hd := d_14268 (p := p) (P := P)
  refine Dead7.kill_of' hd.1 (fun ω μ v => ?_) (fun ω μ => ?_)
  · fs_simp [Exec.twoRegImmAlu] hd
    try (split <;> simp_all)
  · fs_simp [] hd
    try (split <;> simp_all)

theorem k13890 {p : ByteArray} {P : Program} [HasCodeA p P] : Dead7 p 13890 := by
  have hd := d_13890 (p := p) (P := P)
  refine Dead7.kill_of' hd.1 (fun ω μ v => ?_) (fun ω μ => ?_)
  · fs_simp [] hd
    try (split <;> simp_all)
  · fs_simp [] hd
    try (split <;> simp_all)

theorem k11914 {p : ByteArray} {P : Program} [HasCodeA p P] : Dead7 p 11914 := by
  have hd := d_11914 (p := p) (P := P)
  refine Dead7.kill_of' hd.1 (fun ω μ v => ?_) (fun ω μ => ?_)
  · fs_simp [Exec.twoRegImmAlu] hd
    try (split <;> simp_all)
  · fs_simp [] hd
    try (split <;> simp_all)

theorem p13889 {p : ByteArray} {P : Program} [HasCodeA p P] : Dead7 p 13889 := by
  have hd := d_13889 (p := p) (P := P)
  dead_pass [] hd to [13890] by (by simp; exact k13890 (P := P))

theorem p13884 {p : ByteArray} {P : Program} [HasCodeA p P] : Dead7 p 13884 := by
  have hd := d_13884 (p := p) (P := P)
  dead_pass [bs_14268, bs_13889] hd to [14268, 13889] by (by simp; exact ⟨k14268 (P := P), p13889 (P := P)⟩)

theorem p13880 {p : ByteArray} {P : Program} [HasCodeA p P] : Dead7 p 13880 := by
  have hd := d_13880 (p := p) (P := P)
  dead_pass [] hd to [13884] by (by simp; exact p13884 (P := P))

theorem p13879 {p : ByteArray} {P : Program} [HasCodeA p P] : Dead7 p 13879 := by
  have hd := d_13879 (p := p) (P := P)
  dead_pass [] hd to [13880] by (by simp; exact p13880 (P := P))

theorem p13878 {p : ByteArray} {P : Program} [HasCodeA p P] : Dead7 p 13878 := by
  have hd := d_13878 (p := p) (P := P)
  dead_pass [bs_13879] hd to [13879] by (by simp; exact p13879 (P := P))

theorem p13874 {p : ByteArray} {P : Program} [HasCodeA p P] : Dead7 p 13874 := by
  have hd := d_13874 (p := p) (P := P)
  dead_pass [] hd to [13878] by (by simp; exact p13878 (P := P))

theorem p11910 {p : ByteArray} {P : Program} [HasCodeA p P] : Dead7 p 11910 := by
  have hd := d_11910 (p := p) (P := P)
  dead_pass [] hd to [11914] by (by simp; exact k11914 (P := P))

theorem p11906 {p : ByteArray} {P : Program} [HasCodeA p P] : Dead7 p 11906 := by
  have hd := d_11906 (p := p) (P := P)
  dead_pass [] hd to [11910] by (by simp; exact p11910 (P := P))

theorem p11905 {p : ByteArray} {P : Program} [HasCodeA p P] : Dead7 p 11905 := by
  have hd := d_11905 (p := p) (P := P)
  dead_pass [] hd to [11906] by (by simp; exact p11906 (P := P))

theorem p11899 {p : ByteArray} {P : Program} [HasCodeA p P] : Dead7 p 11899 := by
  have hd := d_11899 (p := p) (P := P)
  dead_pass [bs_13874, bs_11905] hd to [13874, 11905] by (by simp; exact ⟨p13874 (P := P), p11905 (P := P)⟩)

theorem p11896 {p : ByteArray} {P : Program} [HasCodeA p P] : Dead7 p 11896 := by
  have hd := d_11896 (p := p) (P := P)
  dead_pass [] hd to [11899] by (by simp; exact p11899 (P := P))

theorem p11892 {p : ByteArray} {P : Program} [HasCodeA p P] : Dead7 p 11892 := by
  have hd := d_11892 (p := p) (P := P)
  dead_pass [] hd to [11896] by (by simp; exact p11896 (P := P))

theorem p11891 {p : ByteArray} {P : Program} [HasCodeA p P] : Dead7 p 11891 := by
  have hd := d_11891 (p := p) (P := P)
  dead_pass [bs_11892] hd to [11892] by (by simp; exact p11892 (P := P))

end Services.Bootstrap.Acc.CkDead
