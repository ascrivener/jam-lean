import sys,re
sys.path.insert(0,'/tmp/claude-0/sp')
from dis import ins
# collect per-byte blocks
a=56356; starts=[56356]; 
while a<56921:
    t,nx=ins[a]
    if 'unlikely' in t and ins[nx][0].find('loadIndI8')>=0: starts.append(a)
    a=nx
assert len(starts)==32, len(starts)
ends=starts[1:]+[56921]
# which bytes have a store
stores={}
for k,(s,e) in enumerate(zip(starts,ends)):
    a=s; st=False
    while a!=e:
        t,nx=ins[a]
        if 'storeIndU64' in t: st=True
        a=nx
    stores[k]=st
hdr='''import Services.Bootstrap.Fmt.Tac

/-!
# `56340`: the per-octet checks (the steps)

56340 is the `Debug` of a 32-octet name at a (ω₇). After its prologue (frame sp = the caller's
sp − 280; ω₀, ω₅, ω₆ saved at sp + 272, sp + 264, sp + 256), it checks each octet b in turn: when b,
sign-extended, is above 31 (32 ≤ b < 128) or is 0, it goes on to the next check; otherwise it
jumps to the hex path (57346). The checks are unrolled; some keep the sign-extended octet in a
stack slot (sp + 16 … sp + 192).

- `sx8_signed`: the sign-extended octet read back as a signed integer;
- `n56_0` … `n56_31`: octet k's check, from its start to the next check's (56921 after the last),
  or to 57346. ω₁, ω₇, ω₈ are kept; only sp … sp + 200 is written.

The octets' values are not tracked further: what follows depends only on which are 0.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- An octet b, sign-extended to 64 bits and read back as a signed integer. -/
theorem sx8_signed (b : Nat) (hb : b < 256) :
    (if ((if b < 128 then (b : Int) else (b : Int) - 256) % 18446744073709551616).toNat < 9223372036854775808 then
        (((if b < 128 then (b : Int) else (b : Int) - 256) % 18446744073709551616).toNat : Int)
      else (((b : Int) - 256) % 18446744073709551616).toNat - 18446744073709551616) =
      (if b < 128 then (b : Int) else (b : Int) - 256) := by
  by_cases h : b < 128
  · simp only [h, if_true]
    have : ((b : Int) % 18446744073709551616) = b := Int.emod_eq_of_lt (by omega) (by omega)
    rw [this]; simp; omega
  · simp only [h, if_false]
    have : (((b : Int) - 256) % 18446744073709551616) = b - 256 + 18446744073709551616 := by omega
    rw [this]
    have : ((b : Int) - 256 + 18446744073709551616).toNat = b + 18446744073709551360 := by omega
    rw [this]; simp; omega
'''
def lemma(k):
    s,e=starts[k],ends[k]
    off = '' if k==0 else f' + {k}'
    addr = 'a' if k==0 else f'(a + {k})'
    st=stores[k]
    if st:
        tail='''    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]'''
        mem="μ'"
        ex="∃ ω' μ'"
        ref="refine ⟨?_, ?_, {OR} ?_, ?_⟩\n    rotate_left 2"
    else:
        tail='''    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]'''
        ref="refine ⟨?_, μ, {OR} ?_, ?_⟩\n    rotate_left"
    cases=[('Or.inl','32 ≤ b ∧ b < 128',e),('Or.inl','b = 0',e),('Or.inr','(0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)',57346)]
    body=''
    for i,(OR,cond,tgt) in enumerate(cases):
        r=ref.replace('{OR}',OR)
        body+=f'''  · have hc : {cond} := by omega
    {r}
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
{tail}
'''
    return f'''
/-- Octet {k} (at a + {k}): from {s} to {e}, or to 57346. -/
theorem n56_{k} {{p : ByteArray}} {{P : Program}} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R {s} ω μ x {e} ω' μ' x 7 ∨ FreeStepsH p R {s} ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ {addr} 1 < 256 := by have := rdN_lt μ {addr} 1; simpa using this
  generalize rb : rdN μ {addr} 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
''' + body.replace('  · have hc : ','  · clear hc; have hc : ' if False else '  · have hc : ')
out=hdr+''.join(lemma(k) for k in range(32))+'\nend Services.Bootstrap.Fmt\n'
open('/home/user/jam-lean/Services/Bootstrap/Fmt/N56Steps.lean','w').write(out)
print(starts, stores)
