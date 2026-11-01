/-
  GENERATED FILE: do not edit by hand.
  Produced by `scripts/gen_tables.py` from the Gray Paper v0.8.0, `text/pvm.tex`.
  CI regenerates it from the pinned paper and fails on any difference.
-/
import PVM.CostExpr

namespace PVM

/-- Opcodes of GP §A.5 "Instructions without Arguments". -/
inductive NoArgsOp where
  /-- `trap` (opcode 0). -/
  | trap
  /-- `fallthrough` (opcode 1). -/
  | fallthrough
  /-- `unlikely` (opcode 2). -/
  | unlikely
  deriving DecidableEq, Repr, Inhabited

/-- The opcode number of each `NoArgsOp`, as in GP §A.5. -/
def NoArgsOp.opcode : NoArgsOp → Nat
  | .trap => 0
  | .fallthrough => 1
  | .unlikely => 2

/-- The paper's name for each `NoArgsOp`. -/
def NoArgsOp.name : NoArgsOp → String
  | .trap => "trap"
  | .fallthrough => "fallthrough"
  | .unlikely => "unlikely"

/-- Inverse of `NoArgsOp.opcode`. -/
def NoArgsOp.ofOpcode? : Nat → Option NoArgsOp
  | 0 => some .trap
  | 1 => some .fallthrough
  | 2 => some .unlikely
  | _ => none

/-- Opcodes of GP §A.5 "Instructions with Arguments of One Immediate". -/
inductive OneImmOp where
  /-- `ecalli` (opcode 10). -/
  | ecalli
  deriving DecidableEq, Repr, Inhabited

/-- The opcode number of each `OneImmOp`, as in GP §A.5. -/
def OneImmOp.opcode : OneImmOp → Nat
  | .ecalli => 10

/-- The paper's name for each `OneImmOp`. -/
def OneImmOp.name : OneImmOp → String
  | .ecalli => "ecalli"

/-- Inverse of `OneImmOp.opcode`. -/
def OneImmOp.ofOpcode? : Nat → Option OneImmOp
  | 10 => some .ecalli
  | _ => none

/-- Opcodes of GP §A.5 "Instructions with Arguments of One Register and One Extended Width Immediate". -/
inductive RegExtImmOp where
  /-- `load_imm_64` (opcode 20). -/
  | loadImm64
  deriving DecidableEq, Repr, Inhabited

/-- The opcode number of each `RegExtImmOp`, as in GP §A.5. -/
def RegExtImmOp.opcode : RegExtImmOp → Nat
  | .loadImm64 => 20

/-- The paper's name for each `RegExtImmOp`. -/
def RegExtImmOp.name : RegExtImmOp → String
  | .loadImm64 => "load_imm_64"

/-- Inverse of `RegExtImmOp.opcode`. -/
def RegExtImmOp.ofOpcode? : Nat → Option RegExtImmOp
  | 20 => some .loadImm64
  | _ => none

/-- Opcodes of GP §A.5 "Instructions with Arguments of Two Immediates". -/
inductive TwoImmOp where
  /-- `store_imm_u8` (opcode 30). -/
  | storeImmU8
  /-- `store_imm_u16` (opcode 31). -/
  | storeImmU16
  /-- `store_imm_u32` (opcode 32). -/
  | storeImmU32
  /-- `store_imm_u64` (opcode 33). -/
  | storeImmU64
  deriving DecidableEq, Repr, Inhabited

/-- The opcode number of each `TwoImmOp`, as in GP §A.5. -/
def TwoImmOp.opcode : TwoImmOp → Nat
  | .storeImmU8 => 30
  | .storeImmU16 => 31
  | .storeImmU32 => 32
  | .storeImmU64 => 33

/-- The paper's name for each `TwoImmOp`. -/
def TwoImmOp.name : TwoImmOp → String
  | .storeImmU8 => "store_imm_u8"
  | .storeImmU16 => "store_imm_u16"
  | .storeImmU32 => "store_imm_u32"
  | .storeImmU64 => "store_imm_u64"

/-- Inverse of `TwoImmOp.opcode`. -/
def TwoImmOp.ofOpcode? : Nat → Option TwoImmOp
  | 30 => some .storeImmU8
  | 31 => some .storeImmU16
  | 32 => some .storeImmU32
  | 33 => some .storeImmU64
  | _ => none

/-- Opcodes of GP §A.5 "Instructions with Arguments of One Offset". -/
inductive OneOffsetOp where
  /-- `jump` (opcode 40). -/
  | jump
  deriving DecidableEq, Repr, Inhabited

/-- The opcode number of each `OneOffsetOp`, as in GP §A.5. -/
def OneOffsetOp.opcode : OneOffsetOp → Nat
  | .jump => 40

/-- The paper's name for each `OneOffsetOp`. -/
def OneOffsetOp.name : OneOffsetOp → String
  | .jump => "jump"

/-- Inverse of `OneOffsetOp.opcode`. -/
def OneOffsetOp.ofOpcode? : Nat → Option OneOffsetOp
  | 40 => some .jump
  | _ => none

/-- Opcodes of GP §A.5 "Instructions with Arguments of One Register & One Immediate". -/
inductive RegImmOp where
  /-- `jump_ind` (opcode 50). -/
  | jumpInd
  /-- `load_imm` (opcode 51). -/
  | loadImm
  /-- `load_u8` (opcode 52). -/
  | loadU8
  /-- `load_i8` (opcode 53). -/
  | loadI8
  /-- `load_u16` (opcode 54). -/
  | loadU16
  /-- `load_i16` (opcode 55). -/
  | loadI16
  /-- `load_u32` (opcode 56). -/
  | loadU32
  /-- `load_i32` (opcode 57). -/
  | loadI32
  /-- `load_u64` (opcode 58). -/
  | loadU64
  /-- `store_u8` (opcode 59). -/
  | storeU8
  /-- `store_u16` (opcode 60). -/
  | storeU16
  /-- `store_u32` (opcode 61). -/
  | storeU32
  /-- `store_u64` (opcode 62). -/
  | storeU64
  deriving DecidableEq, Repr, Inhabited

/-- The opcode number of each `RegImmOp`, as in GP §A.5. -/
def RegImmOp.opcode : RegImmOp → Nat
  | .jumpInd => 50
  | .loadImm => 51
  | .loadU8 => 52
  | .loadI8 => 53
  | .loadU16 => 54
  | .loadI16 => 55
  | .loadU32 => 56
  | .loadI32 => 57
  | .loadU64 => 58
  | .storeU8 => 59
  | .storeU16 => 60
  | .storeU32 => 61
  | .storeU64 => 62

/-- The paper's name for each `RegImmOp`. -/
def RegImmOp.name : RegImmOp → String
  | .jumpInd => "jump_ind"
  | .loadImm => "load_imm"
  | .loadU8 => "load_u8"
  | .loadI8 => "load_i8"
  | .loadU16 => "load_u16"
  | .loadI16 => "load_i16"
  | .loadU32 => "load_u32"
  | .loadI32 => "load_i32"
  | .loadU64 => "load_u64"
  | .storeU8 => "store_u8"
  | .storeU16 => "store_u16"
  | .storeU32 => "store_u32"
  | .storeU64 => "store_u64"

/-- Inverse of `RegImmOp.opcode`. -/
def RegImmOp.ofOpcode? : Nat → Option RegImmOp
  | 50 => some .jumpInd
  | 51 => some .loadImm
  | 52 => some .loadU8
  | 53 => some .loadI8
  | 54 => some .loadU16
  | 55 => some .loadI16
  | 56 => some .loadU32
  | 57 => some .loadI32
  | 58 => some .loadU64
  | 59 => some .storeU8
  | 60 => some .storeU16
  | 61 => some .storeU32
  | 62 => some .storeU64
  | _ => none

/-- Opcodes of GP §A.5 "Instructions with Arguments of One Register & Two Immediates". -/
inductive RegTwoImmOp where
  /-- `store_imm_ind_u8` (opcode 70). -/
  | storeImmIndU8
  /-- `store_imm_ind_u16` (opcode 71). -/
  | storeImmIndU16
  /-- `store_imm_ind_u32` (opcode 72). -/
  | storeImmIndU32
  /-- `store_imm_ind_u64` (opcode 73). -/
  | storeImmIndU64
  deriving DecidableEq, Repr, Inhabited

/-- The opcode number of each `RegTwoImmOp`, as in GP §A.5. -/
def RegTwoImmOp.opcode : RegTwoImmOp → Nat
  | .storeImmIndU8 => 70
  | .storeImmIndU16 => 71
  | .storeImmIndU32 => 72
  | .storeImmIndU64 => 73

/-- The paper's name for each `RegTwoImmOp`. -/
def RegTwoImmOp.name : RegTwoImmOp → String
  | .storeImmIndU8 => "store_imm_ind_u8"
  | .storeImmIndU16 => "store_imm_ind_u16"
  | .storeImmIndU32 => "store_imm_ind_u32"
  | .storeImmIndU64 => "store_imm_ind_u64"

/-- Inverse of `RegTwoImmOp.opcode`. -/
def RegTwoImmOp.ofOpcode? : Nat → Option RegTwoImmOp
  | 70 => some .storeImmIndU8
  | 71 => some .storeImmIndU16
  | 72 => some .storeImmIndU32
  | 73 => some .storeImmIndU64
  | _ => none

/-- Opcodes of GP §A.5 "Instructions with Arguments of One Register, One Immediate and One Offset". -/
inductive RegImmOffsetOp where
  /-- `load_imm_jump` (opcode 80). -/
  | loadImmJump
  /-- `branch_eq_imm` (opcode 81). -/
  | branchEqImm
  /-- `branch_ne_imm` (opcode 82). -/
  | branchNeImm
  /-- `branch_lt_u_imm` (opcode 83). -/
  | branchLtUImm
  /-- `branch_le_u_imm` (opcode 84). -/
  | branchLeUImm
  /-- `branch_ge_u_imm` (opcode 85). -/
  | branchGeUImm
  /-- `branch_gt_u_imm` (opcode 86). -/
  | branchGtUImm
  /-- `branch_lt_s_imm` (opcode 87). -/
  | branchLtSImm
  /-- `branch_le_s_imm` (opcode 88). -/
  | branchLeSImm
  /-- `branch_ge_s_imm` (opcode 89). -/
  | branchGeSImm
  /-- `branch_gt_s_imm` (opcode 90). -/
  | branchGtSImm
  deriving DecidableEq, Repr, Inhabited

/-- The opcode number of each `RegImmOffsetOp`, as in GP §A.5. -/
def RegImmOffsetOp.opcode : RegImmOffsetOp → Nat
  | .loadImmJump => 80
  | .branchEqImm => 81
  | .branchNeImm => 82
  | .branchLtUImm => 83
  | .branchLeUImm => 84
  | .branchGeUImm => 85
  | .branchGtUImm => 86
  | .branchLtSImm => 87
  | .branchLeSImm => 88
  | .branchGeSImm => 89
  | .branchGtSImm => 90

/-- The paper's name for each `RegImmOffsetOp`. -/
def RegImmOffsetOp.name : RegImmOffsetOp → String
  | .loadImmJump => "load_imm_jump"
  | .branchEqImm => "branch_eq_imm"
  | .branchNeImm => "branch_ne_imm"
  | .branchLtUImm => "branch_lt_u_imm"
  | .branchLeUImm => "branch_le_u_imm"
  | .branchGeUImm => "branch_ge_u_imm"
  | .branchGtUImm => "branch_gt_u_imm"
  | .branchLtSImm => "branch_lt_s_imm"
  | .branchLeSImm => "branch_le_s_imm"
  | .branchGeSImm => "branch_ge_s_imm"
  | .branchGtSImm => "branch_gt_s_imm"

/-- Inverse of `RegImmOffsetOp.opcode`. -/
def RegImmOffsetOp.ofOpcode? : Nat → Option RegImmOffsetOp
  | 80 => some .loadImmJump
  | 81 => some .branchEqImm
  | 82 => some .branchNeImm
  | 83 => some .branchLtUImm
  | 84 => some .branchLeUImm
  | 85 => some .branchGeUImm
  | 86 => some .branchGtUImm
  | 87 => some .branchLtSImm
  | 88 => some .branchLeSImm
  | 89 => some .branchGeSImm
  | 90 => some .branchGtSImm
  | _ => none

/-- Opcodes of GP §A.5 "Instructions with Arguments of Two Registers". -/
inductive TwoRegOp where
  /-- `move_reg` (opcode 100). -/
  | moveReg
  /-- `count_set_bits_64` (opcode 101). -/
  | countSetBits64
  /-- `count_set_bits_32` (opcode 102). -/
  | countSetBits32
  /-- `leading_zero_bits_64` (opcode 103). -/
  | leadingZeroBits64
  /-- `leading_zero_bits_32` (opcode 104). -/
  | leadingZeroBits32
  /-- `trailing_zero_bits_64` (opcode 105). -/
  | trailingZeroBits64
  /-- `trailing_zero_bits_32` (opcode 106). -/
  | trailingZeroBits32
  /-- `sign_extend_8` (opcode 107). -/
  | signExtend8
  /-- `sign_extend_16` (opcode 108). -/
  | signExtend16
  /-- `zero_extend_16` (opcode 109). -/
  | zeroExtend16
  /-- `reverse_bytes` (opcode 110). -/
  | reverseBytes
  deriving DecidableEq, Repr, Inhabited

/-- The opcode number of each `TwoRegOp`, as in GP §A.5. -/
def TwoRegOp.opcode : TwoRegOp → Nat
  | .moveReg => 100
  | .countSetBits64 => 101
  | .countSetBits32 => 102
  | .leadingZeroBits64 => 103
  | .leadingZeroBits32 => 104
  | .trailingZeroBits64 => 105
  | .trailingZeroBits32 => 106
  | .signExtend8 => 107
  | .signExtend16 => 108
  | .zeroExtend16 => 109
  | .reverseBytes => 110

/-- The paper's name for each `TwoRegOp`. -/
def TwoRegOp.name : TwoRegOp → String
  | .moveReg => "move_reg"
  | .countSetBits64 => "count_set_bits_64"
  | .countSetBits32 => "count_set_bits_32"
  | .leadingZeroBits64 => "leading_zero_bits_64"
  | .leadingZeroBits32 => "leading_zero_bits_32"
  | .trailingZeroBits64 => "trailing_zero_bits_64"
  | .trailingZeroBits32 => "trailing_zero_bits_32"
  | .signExtend8 => "sign_extend_8"
  | .signExtend16 => "sign_extend_16"
  | .zeroExtend16 => "zero_extend_16"
  | .reverseBytes => "reverse_bytes"

/-- Inverse of `TwoRegOp.opcode`. -/
def TwoRegOp.ofOpcode? : Nat → Option TwoRegOp
  | 100 => some .moveReg
  | 101 => some .countSetBits64
  | 102 => some .countSetBits32
  | 103 => some .leadingZeroBits64
  | 104 => some .leadingZeroBits32
  | 105 => some .trailingZeroBits64
  | 106 => some .trailingZeroBits32
  | 107 => some .signExtend8
  | 108 => some .signExtend16
  | 109 => some .zeroExtend16
  | 110 => some .reverseBytes
  | _ => none

/-- Opcodes of GP §A.5 "Instructions with Arguments of Two Registers & One Immediate". -/
inductive TwoRegImmOp where
  /-- `store_ind_u8` (opcode 120). -/
  | storeIndU8
  /-- `store_ind_u16` (opcode 121). -/
  | storeIndU16
  /-- `store_ind_u32` (opcode 122). -/
  | storeIndU32
  /-- `store_ind_u64` (opcode 123). -/
  | storeIndU64
  /-- `load_ind_u8` (opcode 124). -/
  | loadIndU8
  /-- `load_ind_i8` (opcode 125). -/
  | loadIndI8
  /-- `load_ind_u16` (opcode 126). -/
  | loadIndU16
  /-- `load_ind_i16` (opcode 127). -/
  | loadIndI16
  /-- `load_ind_u32` (opcode 128). -/
  | loadIndU32
  /-- `load_ind_i32` (opcode 129). -/
  | loadIndI32
  /-- `load_ind_u64` (opcode 130). -/
  | loadIndU64
  /-- `add_imm_32` (opcode 131). -/
  | addImm32
  /-- `and_imm` (opcode 132). -/
  | andImm
  /-- `xor_imm` (opcode 133). -/
  | xorImm
  /-- `or_imm` (opcode 134). -/
  | orImm
  /-- `mul_imm_32` (opcode 135). -/
  | mulImm32
  /-- `set_lt_u_imm` (opcode 136). -/
  | setLtUImm
  /-- `set_lt_s_imm` (opcode 137). -/
  | setLtSImm
  /-- `shlo_l_imm_32` (opcode 138). -/
  | shloLImm32
  /-- `shlo_r_imm_32` (opcode 139). -/
  | shloRImm32
  /-- `shar_r_imm_32` (opcode 140). -/
  | sharRImm32
  /-- `neg_add_imm_32` (opcode 141). -/
  | negAddImm32
  /-- `set_gt_u_imm` (opcode 142). -/
  | setGtUImm
  /-- `set_gt_s_imm` (opcode 143). -/
  | setGtSImm
  /-- `shlo_l_imm_alt_32` (opcode 144). -/
  | shloLImmAlt32
  /-- `shlo_r_imm_alt_32` (opcode 145). -/
  | shloRImmAlt32
  /-- `shar_r_imm_alt_32` (opcode 146). -/
  | sharRImmAlt32
  /-- `cmov_iz_imm` (opcode 147). -/
  | cmovIzImm
  /-- `cmov_nz_imm` (opcode 148). -/
  | cmovNzImm
  /-- `add_imm_64` (opcode 149). -/
  | addImm64
  /-- `mul_imm_64` (opcode 150). -/
  | mulImm64
  /-- `shlo_l_imm_64` (opcode 151). -/
  | shloLImm64
  /-- `shlo_r_imm_64` (opcode 152). -/
  | shloRImm64
  /-- `shar_r_imm_64` (opcode 153). -/
  | sharRImm64
  /-- `neg_add_imm_64` (opcode 154). -/
  | negAddImm64
  /-- `shlo_l_imm_alt_64` (opcode 155). -/
  | shloLImmAlt64
  /-- `shlo_r_imm_alt_64` (opcode 156). -/
  | shloRImmAlt64
  /-- `shar_r_imm_alt_64` (opcode 157). -/
  | sharRImmAlt64
  /-- `rot_r_64_imm` (opcode 158). -/
  | rotR64Imm
  /-- `rot_r_64_imm_alt` (opcode 159). -/
  | rotR64ImmAlt
  /-- `rot_r_32_imm` (opcode 160). -/
  | rotR32Imm
  /-- `rot_r_32_imm_alt` (opcode 161). -/
  | rotR32ImmAlt
  deriving DecidableEq, Repr, Inhabited

/-- The opcode number of each `TwoRegImmOp`, as in GP §A.5. -/
def TwoRegImmOp.opcode : TwoRegImmOp → Nat
  | .storeIndU8 => 120
  | .storeIndU16 => 121
  | .storeIndU32 => 122
  | .storeIndU64 => 123
  | .loadIndU8 => 124
  | .loadIndI8 => 125
  | .loadIndU16 => 126
  | .loadIndI16 => 127
  | .loadIndU32 => 128
  | .loadIndI32 => 129
  | .loadIndU64 => 130
  | .addImm32 => 131
  | .andImm => 132
  | .xorImm => 133
  | .orImm => 134
  | .mulImm32 => 135
  | .setLtUImm => 136
  | .setLtSImm => 137
  | .shloLImm32 => 138
  | .shloRImm32 => 139
  | .sharRImm32 => 140
  | .negAddImm32 => 141
  | .setGtUImm => 142
  | .setGtSImm => 143
  | .shloLImmAlt32 => 144
  | .shloRImmAlt32 => 145
  | .sharRImmAlt32 => 146
  | .cmovIzImm => 147
  | .cmovNzImm => 148
  | .addImm64 => 149
  | .mulImm64 => 150
  | .shloLImm64 => 151
  | .shloRImm64 => 152
  | .sharRImm64 => 153
  | .negAddImm64 => 154
  | .shloLImmAlt64 => 155
  | .shloRImmAlt64 => 156
  | .sharRImmAlt64 => 157
  | .rotR64Imm => 158
  | .rotR64ImmAlt => 159
  | .rotR32Imm => 160
  | .rotR32ImmAlt => 161

/-- The paper's name for each `TwoRegImmOp`. -/
def TwoRegImmOp.name : TwoRegImmOp → String
  | .storeIndU8 => "store_ind_u8"
  | .storeIndU16 => "store_ind_u16"
  | .storeIndU32 => "store_ind_u32"
  | .storeIndU64 => "store_ind_u64"
  | .loadIndU8 => "load_ind_u8"
  | .loadIndI8 => "load_ind_i8"
  | .loadIndU16 => "load_ind_u16"
  | .loadIndI16 => "load_ind_i16"
  | .loadIndU32 => "load_ind_u32"
  | .loadIndI32 => "load_ind_i32"
  | .loadIndU64 => "load_ind_u64"
  | .addImm32 => "add_imm_32"
  | .andImm => "and_imm"
  | .xorImm => "xor_imm"
  | .orImm => "or_imm"
  | .mulImm32 => "mul_imm_32"
  | .setLtUImm => "set_lt_u_imm"
  | .setLtSImm => "set_lt_s_imm"
  | .shloLImm32 => "shlo_l_imm_32"
  | .shloRImm32 => "shlo_r_imm_32"
  | .sharRImm32 => "shar_r_imm_32"
  | .negAddImm32 => "neg_add_imm_32"
  | .setGtUImm => "set_gt_u_imm"
  | .setGtSImm => "set_gt_s_imm"
  | .shloLImmAlt32 => "shlo_l_imm_alt_32"
  | .shloRImmAlt32 => "shlo_r_imm_alt_32"
  | .sharRImmAlt32 => "shar_r_imm_alt_32"
  | .cmovIzImm => "cmov_iz_imm"
  | .cmovNzImm => "cmov_nz_imm"
  | .addImm64 => "add_imm_64"
  | .mulImm64 => "mul_imm_64"
  | .shloLImm64 => "shlo_l_imm_64"
  | .shloRImm64 => "shlo_r_imm_64"
  | .sharRImm64 => "shar_r_imm_64"
  | .negAddImm64 => "neg_add_imm_64"
  | .shloLImmAlt64 => "shlo_l_imm_alt_64"
  | .shloRImmAlt64 => "shlo_r_imm_alt_64"
  | .sharRImmAlt64 => "shar_r_imm_alt_64"
  | .rotR64Imm => "rot_r_64_imm"
  | .rotR64ImmAlt => "rot_r_64_imm_alt"
  | .rotR32Imm => "rot_r_32_imm"
  | .rotR32ImmAlt => "rot_r_32_imm_alt"

/-- Inverse of `TwoRegImmOp.opcode`. -/
def TwoRegImmOp.ofOpcode? : Nat → Option TwoRegImmOp
  | 120 => some .storeIndU8
  | 121 => some .storeIndU16
  | 122 => some .storeIndU32
  | 123 => some .storeIndU64
  | 124 => some .loadIndU8
  | 125 => some .loadIndI8
  | 126 => some .loadIndU16
  | 127 => some .loadIndI16
  | 128 => some .loadIndU32
  | 129 => some .loadIndI32
  | 130 => some .loadIndU64
  | 131 => some .addImm32
  | 132 => some .andImm
  | 133 => some .xorImm
  | 134 => some .orImm
  | 135 => some .mulImm32
  | 136 => some .setLtUImm
  | 137 => some .setLtSImm
  | 138 => some .shloLImm32
  | 139 => some .shloRImm32
  | 140 => some .sharRImm32
  | 141 => some .negAddImm32
  | 142 => some .setGtUImm
  | 143 => some .setGtSImm
  | 144 => some .shloLImmAlt32
  | 145 => some .shloRImmAlt32
  | 146 => some .sharRImmAlt32
  | 147 => some .cmovIzImm
  | 148 => some .cmovNzImm
  | 149 => some .addImm64
  | 150 => some .mulImm64
  | 151 => some .shloLImm64
  | 152 => some .shloRImm64
  | 153 => some .sharRImm64
  | 154 => some .negAddImm64
  | 155 => some .shloLImmAlt64
  | 156 => some .shloRImmAlt64
  | 157 => some .sharRImmAlt64
  | 158 => some .rotR64Imm
  | 159 => some .rotR64ImmAlt
  | 160 => some .rotR32Imm
  | 161 => some .rotR32ImmAlt
  | _ => none

/-- Opcodes of GP §A.5 "Instructions with Arguments of Two Registers & One Offset". -/
inductive TwoRegOffsetOp where
  /-- `branch_eq` (opcode 170). -/
  | branchEq
  /-- `branch_ne` (opcode 171). -/
  | branchNe
  /-- `branch_lt_u` (opcode 172). -/
  | branchLtU
  /-- `branch_lt_s` (opcode 173). -/
  | branchLtS
  /-- `branch_ge_u` (opcode 174). -/
  | branchGeU
  /-- `branch_ge_s` (opcode 175). -/
  | branchGeS
  deriving DecidableEq, Repr, Inhabited

/-- The opcode number of each `TwoRegOffsetOp`, as in GP §A.5. -/
def TwoRegOffsetOp.opcode : TwoRegOffsetOp → Nat
  | .branchEq => 170
  | .branchNe => 171
  | .branchLtU => 172
  | .branchLtS => 173
  | .branchGeU => 174
  | .branchGeS => 175

/-- The paper's name for each `TwoRegOffsetOp`. -/
def TwoRegOffsetOp.name : TwoRegOffsetOp → String
  | .branchEq => "branch_eq"
  | .branchNe => "branch_ne"
  | .branchLtU => "branch_lt_u"
  | .branchLtS => "branch_lt_s"
  | .branchGeU => "branch_ge_u"
  | .branchGeS => "branch_ge_s"

/-- Inverse of `TwoRegOffsetOp.opcode`. -/
def TwoRegOffsetOp.ofOpcode? : Nat → Option TwoRegOffsetOp
  | 170 => some .branchEq
  | 171 => some .branchNe
  | 172 => some .branchLtU
  | 173 => some .branchLtS
  | 174 => some .branchGeU
  | 175 => some .branchGeS
  | _ => none

/-- Opcodes of GP §A.5 "Instruction with Arguments of Two Registers and Two Immediates". -/
inductive TwoRegTwoImmOp where
  /-- `load_imm_jump_ind` (opcode 180). -/
  | loadImmJumpInd
  deriving DecidableEq, Repr, Inhabited

/-- The opcode number of each `TwoRegTwoImmOp`, as in GP §A.5. -/
def TwoRegTwoImmOp.opcode : TwoRegTwoImmOp → Nat
  | .loadImmJumpInd => 180

/-- The paper's name for each `TwoRegTwoImmOp`. -/
def TwoRegTwoImmOp.name : TwoRegTwoImmOp → String
  | .loadImmJumpInd => "load_imm_jump_ind"

/-- Inverse of `TwoRegTwoImmOp.opcode`. -/
def TwoRegTwoImmOp.ofOpcode? : Nat → Option TwoRegTwoImmOp
  | 180 => some .loadImmJumpInd
  | _ => none

/-- Opcodes of GP §A.5 "Instructions with Arguments of Three Registers". -/
inductive ThreeRegOp where
  /-- `add_32` (opcode 190). -/
  | add32
  /-- `sub_32` (opcode 191). -/
  | sub32
  /-- `mul_32` (opcode 192). -/
  | mul32
  /-- `div_u_32` (opcode 193). -/
  | divU32
  /-- `div_s_32` (opcode 194). -/
  | divS32
  /-- `rem_u_32` (opcode 195). -/
  | remU32
  /-- `rem_s_32` (opcode 196). -/
  | remS32
  /-- `shlo_l_32` (opcode 197). -/
  | shloL32
  /-- `shlo_r_32` (opcode 198). -/
  | shloR32
  /-- `shar_r_32` (opcode 199). -/
  | sharR32
  /-- `add_64` (opcode 200). -/
  | add64
  /-- `sub_64` (opcode 201). -/
  | sub64
  /-- `mul_64` (opcode 202). -/
  | mul64
  /-- `div_u_64` (opcode 203). -/
  | divU64
  /-- `div_s_64` (opcode 204). -/
  | divS64
  /-- `rem_u_64` (opcode 205). -/
  | remU64
  /-- `rem_s_64` (opcode 206). -/
  | remS64
  /-- `shlo_l_64` (opcode 207). -/
  | shloL64
  /-- `shlo_r_64` (opcode 208). -/
  | shloR64
  /-- `shar_r_64` (opcode 209). -/
  | sharR64
  /-- `and` (opcode 210). -/
  | and
  /-- `xor` (opcode 211). -/
  | xor
  /-- `or` (opcode 212). -/
  | or
  /-- `mul_upper_s_s` (opcode 213). -/
  | mulUpperSS
  /-- `mul_upper_u_u` (opcode 214). -/
  | mulUpperUU
  /-- `mul_upper_s_u` (opcode 215). -/
  | mulUpperSU
  /-- `set_lt_u` (opcode 216). -/
  | setLtU
  /-- `set_lt_s` (opcode 217). -/
  | setLtS
  /-- `cmov_iz` (opcode 218). -/
  | cmovIz
  /-- `cmov_nz` (opcode 219). -/
  | cmovNz
  /-- `rot_l_64` (opcode 220). -/
  | rotL64
  /-- `rot_l_32` (opcode 221). -/
  | rotL32
  /-- `rot_r_64` (opcode 222). -/
  | rotR64
  /-- `rot_r_32` (opcode 223). -/
  | rotR32
  /-- `and_inv` (opcode 224). -/
  | andInv
  /-- `or_inv` (opcode 225). -/
  | orInv
  /-- `xnor` (opcode 226). -/
  | xnor
  /-- `max` (opcode 227). -/
  | max
  /-- `max_u` (opcode 228). -/
  | maxU
  /-- `min` (opcode 229). -/
  | min
  /-- `min_u` (opcode 230). -/
  | minU
  deriving DecidableEq, Repr, Inhabited

/-- The opcode number of each `ThreeRegOp`, as in GP §A.5. -/
def ThreeRegOp.opcode : ThreeRegOp → Nat
  | .add32 => 190
  | .sub32 => 191
  | .mul32 => 192
  | .divU32 => 193
  | .divS32 => 194
  | .remU32 => 195
  | .remS32 => 196
  | .shloL32 => 197
  | .shloR32 => 198
  | .sharR32 => 199
  | .add64 => 200
  | .sub64 => 201
  | .mul64 => 202
  | .divU64 => 203
  | .divS64 => 204
  | .remU64 => 205
  | .remS64 => 206
  | .shloL64 => 207
  | .shloR64 => 208
  | .sharR64 => 209
  | .and => 210
  | .xor => 211
  | .or => 212
  | .mulUpperSS => 213
  | .mulUpperUU => 214
  | .mulUpperSU => 215
  | .setLtU => 216
  | .setLtS => 217
  | .cmovIz => 218
  | .cmovNz => 219
  | .rotL64 => 220
  | .rotL32 => 221
  | .rotR64 => 222
  | .rotR32 => 223
  | .andInv => 224
  | .orInv => 225
  | .xnor => 226
  | .max => 227
  | .maxU => 228
  | .min => 229
  | .minU => 230

/-- The paper's name for each `ThreeRegOp`. -/
def ThreeRegOp.name : ThreeRegOp → String
  | .add32 => "add_32"
  | .sub32 => "sub_32"
  | .mul32 => "mul_32"
  | .divU32 => "div_u_32"
  | .divS32 => "div_s_32"
  | .remU32 => "rem_u_32"
  | .remS32 => "rem_s_32"
  | .shloL32 => "shlo_l_32"
  | .shloR32 => "shlo_r_32"
  | .sharR32 => "shar_r_32"
  | .add64 => "add_64"
  | .sub64 => "sub_64"
  | .mul64 => "mul_64"
  | .divU64 => "div_u_64"
  | .divS64 => "div_s_64"
  | .remU64 => "rem_u_64"
  | .remS64 => "rem_s_64"
  | .shloL64 => "shlo_l_64"
  | .shloR64 => "shlo_r_64"
  | .sharR64 => "shar_r_64"
  | .and => "and"
  | .xor => "xor"
  | .or => "or"
  | .mulUpperSS => "mul_upper_s_s"
  | .mulUpperUU => "mul_upper_u_u"
  | .mulUpperSU => "mul_upper_s_u"
  | .setLtU => "set_lt_u"
  | .setLtS => "set_lt_s"
  | .cmovIz => "cmov_iz"
  | .cmovNz => "cmov_nz"
  | .rotL64 => "rot_l_64"
  | .rotL32 => "rot_l_32"
  | .rotR64 => "rot_r_64"
  | .rotR32 => "rot_r_32"
  | .andInv => "and_inv"
  | .orInv => "or_inv"
  | .xnor => "xnor"
  | .max => "max"
  | .maxU => "max_u"
  | .min => "min"
  | .minU => "min_u"

/-- Inverse of `ThreeRegOp.opcode`. -/
def ThreeRegOp.ofOpcode? : Nat → Option ThreeRegOp
  | 190 => some .add32
  | 191 => some .sub32
  | 192 => some .mul32
  | 193 => some .divU32
  | 194 => some .divS32
  | 195 => some .remU32
  | 196 => some .remS32
  | 197 => some .shloL32
  | 198 => some .shloR32
  | 199 => some .sharR32
  | 200 => some .add64
  | 201 => some .sub64
  | 202 => some .mul64
  | 203 => some .divU64
  | 204 => some .divS64
  | 205 => some .remU64
  | 206 => some .remS64
  | 207 => some .shloL64
  | 208 => some .shloR64
  | 209 => some .sharR64
  | 210 => some .and
  | 211 => some .xor
  | 212 => some .or
  | 213 => some .mulUpperSS
  | 214 => some .mulUpperUU
  | 215 => some .mulUpperSU
  | 216 => some .setLtU
  | 217 => some .setLtS
  | 218 => some .cmovIz
  | 219 => some .cmovNz
  | 220 => some .rotL64
  | 221 => some .rotL32
  | 222 => some .rotR64
  | 223 => some .rotR32
  | 224 => some .andInv
  | 225 => some .orInv
  | 226 => some .xnor
  | 227 => some .max
  | 228 => some .maxU
  | 229 => some .min
  | 230 => some .minU
  | _ => none

/-- The argument formats of GP §A.5, one per subsubsection of the instruction tables. -/
inductive ArgFormat where
  | noArgs
  | oneImm
  | regExtImm
  | twoImm
  | oneOffset
  | regImm
  | regTwoImm
  | regImmOffset
  | twoReg
  | twoRegImm
  | twoRegOffset
  | twoRegTwoImm
  | threeReg
  deriving DecidableEq, Repr

/-- The argument format of each opcode in U (GP §A.5); `none` for octets not in U. -/
def formatOf? : Nat → Option ArgFormat
  | 0 => some .noArgs
  | 1 => some .noArgs
  | 2 => some .noArgs
  | 10 => some .oneImm
  | 20 => some .regExtImm
  | 30 => some .twoImm
  | 31 => some .twoImm
  | 32 => some .twoImm
  | 33 => some .twoImm
  | 40 => some .oneOffset
  | 50 => some .regImm
  | 51 => some .regImm
  | 52 => some .regImm
  | 53 => some .regImm
  | 54 => some .regImm
  | 55 => some .regImm
  | 56 => some .regImm
  | 57 => some .regImm
  | 58 => some .regImm
  | 59 => some .regImm
  | 60 => some .regImm
  | 61 => some .regImm
  | 62 => some .regImm
  | 70 => some .regTwoImm
  | 71 => some .regTwoImm
  | 72 => some .regTwoImm
  | 73 => some .regTwoImm
  | 80 => some .regImmOffset
  | 81 => some .regImmOffset
  | 82 => some .regImmOffset
  | 83 => some .regImmOffset
  | 84 => some .regImmOffset
  | 85 => some .regImmOffset
  | 86 => some .regImmOffset
  | 87 => some .regImmOffset
  | 88 => some .regImmOffset
  | 89 => some .regImmOffset
  | 90 => some .regImmOffset
  | 100 => some .twoReg
  | 101 => some .twoReg
  | 102 => some .twoReg
  | 103 => some .twoReg
  | 104 => some .twoReg
  | 105 => some .twoReg
  | 106 => some .twoReg
  | 107 => some .twoReg
  | 108 => some .twoReg
  | 109 => some .twoReg
  | 110 => some .twoReg
  | 120 => some .twoRegImm
  | 121 => some .twoRegImm
  | 122 => some .twoRegImm
  | 123 => some .twoRegImm
  | 124 => some .twoRegImm
  | 125 => some .twoRegImm
  | 126 => some .twoRegImm
  | 127 => some .twoRegImm
  | 128 => some .twoRegImm
  | 129 => some .twoRegImm
  | 130 => some .twoRegImm
  | 131 => some .twoRegImm
  | 132 => some .twoRegImm
  | 133 => some .twoRegImm
  | 134 => some .twoRegImm
  | 135 => some .twoRegImm
  | 136 => some .twoRegImm
  | 137 => some .twoRegImm
  | 138 => some .twoRegImm
  | 139 => some .twoRegImm
  | 140 => some .twoRegImm
  | 141 => some .twoRegImm
  | 142 => some .twoRegImm
  | 143 => some .twoRegImm
  | 144 => some .twoRegImm
  | 145 => some .twoRegImm
  | 146 => some .twoRegImm
  | 147 => some .twoRegImm
  | 148 => some .twoRegImm
  | 149 => some .twoRegImm
  | 150 => some .twoRegImm
  | 151 => some .twoRegImm
  | 152 => some .twoRegImm
  | 153 => some .twoRegImm
  | 154 => some .twoRegImm
  | 155 => some .twoRegImm
  | 156 => some .twoRegImm
  | 157 => some .twoRegImm
  | 158 => some .twoRegImm
  | 159 => some .twoRegImm
  | 160 => some .twoRegImm
  | 161 => some .twoRegImm
  | 170 => some .twoRegOffset
  | 171 => some .twoRegOffset
  | 172 => some .twoRegOffset
  | 173 => some .twoRegOffset
  | 174 => some .twoRegOffset
  | 175 => some .twoRegOffset
  | 180 => some .twoRegTwoImm
  | 190 => some .threeReg
  | 191 => some .threeReg
  | 192 => some .threeReg
  | 193 => some .threeReg
  | 194 => some .threeReg
  | 195 => some .threeReg
  | 196 => some .threeReg
  | 197 => some .threeReg
  | 198 => some .threeReg
  | 199 => some .threeReg
  | 200 => some .threeReg
  | 201 => some .threeReg
  | 202 => some .threeReg
  | 203 => some .threeReg
  | 204 => some .threeReg
  | 205 => some .threeReg
  | 206 => some .threeReg
  | 207 => some .threeReg
  | 208 => some .threeReg
  | 209 => some .threeReg
  | 210 => some .threeReg
  | 211 => some .threeReg
  | 212 => some .threeReg
  | 213 => some .threeReg
  | 214 => some .threeReg
  | 215 => some .threeReg
  | 216 => some .threeReg
  | 217 => some .threeReg
  | 218 => some .threeReg
  | 219 => some .threeReg
  | 220 => some .threeReg
  | 221 => some .threeReg
  | 222 => some .threeReg
  | 223 => some .threeReg
  | 224 => some .threeReg
  | 225 => some .threeReg
  | 226 => some .threeReg
  | 227 => some .threeReg
  | 228 => some .threeReg
  | 229 => some .threeReg
  | 230 => some .threeReg
  | _ => none

/-- The opcodes U of all valid instructions (GP §A.3), in increasing order. -/
def validOpcodes : List Nat :=
  [0, 1, 2, 10, 20, 30, 31, 32, 33, 40, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 70, 71, 72, 73, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 170, 171, 172, 173, 174, 175, 180, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230]

/-- The paper's name of each opcode in U. -/
def opcodeName? : Nat → Option String
  | 0 => some "trap"
  | 1 => some "fallthrough"
  | 2 => some "unlikely"
  | 10 => some "ecalli"
  | 20 => some "load_imm_64"
  | 30 => some "store_imm_u8"
  | 31 => some "store_imm_u16"
  | 32 => some "store_imm_u32"
  | 33 => some "store_imm_u64"
  | 40 => some "jump"
  | 50 => some "jump_ind"
  | 51 => some "load_imm"
  | 52 => some "load_u8"
  | 53 => some "load_i8"
  | 54 => some "load_u16"
  | 55 => some "load_i16"
  | 56 => some "load_u32"
  | 57 => some "load_i32"
  | 58 => some "load_u64"
  | 59 => some "store_u8"
  | 60 => some "store_u16"
  | 61 => some "store_u32"
  | 62 => some "store_u64"
  | 70 => some "store_imm_ind_u8"
  | 71 => some "store_imm_ind_u16"
  | 72 => some "store_imm_ind_u32"
  | 73 => some "store_imm_ind_u64"
  | 80 => some "load_imm_jump"
  | 81 => some "branch_eq_imm"
  | 82 => some "branch_ne_imm"
  | 83 => some "branch_lt_u_imm"
  | 84 => some "branch_le_u_imm"
  | 85 => some "branch_ge_u_imm"
  | 86 => some "branch_gt_u_imm"
  | 87 => some "branch_lt_s_imm"
  | 88 => some "branch_le_s_imm"
  | 89 => some "branch_ge_s_imm"
  | 90 => some "branch_gt_s_imm"
  | 100 => some "move_reg"
  | 101 => some "count_set_bits_64"
  | 102 => some "count_set_bits_32"
  | 103 => some "leading_zero_bits_64"
  | 104 => some "leading_zero_bits_32"
  | 105 => some "trailing_zero_bits_64"
  | 106 => some "trailing_zero_bits_32"
  | 107 => some "sign_extend_8"
  | 108 => some "sign_extend_16"
  | 109 => some "zero_extend_16"
  | 110 => some "reverse_bytes"
  | 120 => some "store_ind_u8"
  | 121 => some "store_ind_u16"
  | 122 => some "store_ind_u32"
  | 123 => some "store_ind_u64"
  | 124 => some "load_ind_u8"
  | 125 => some "load_ind_i8"
  | 126 => some "load_ind_u16"
  | 127 => some "load_ind_i16"
  | 128 => some "load_ind_u32"
  | 129 => some "load_ind_i32"
  | 130 => some "load_ind_u64"
  | 131 => some "add_imm_32"
  | 132 => some "and_imm"
  | 133 => some "xor_imm"
  | 134 => some "or_imm"
  | 135 => some "mul_imm_32"
  | 136 => some "set_lt_u_imm"
  | 137 => some "set_lt_s_imm"
  | 138 => some "shlo_l_imm_32"
  | 139 => some "shlo_r_imm_32"
  | 140 => some "shar_r_imm_32"
  | 141 => some "neg_add_imm_32"
  | 142 => some "set_gt_u_imm"
  | 143 => some "set_gt_s_imm"
  | 144 => some "shlo_l_imm_alt_32"
  | 145 => some "shlo_r_imm_alt_32"
  | 146 => some "shar_r_imm_alt_32"
  | 147 => some "cmov_iz_imm"
  | 148 => some "cmov_nz_imm"
  | 149 => some "add_imm_64"
  | 150 => some "mul_imm_64"
  | 151 => some "shlo_l_imm_64"
  | 152 => some "shlo_r_imm_64"
  | 153 => some "shar_r_imm_64"
  | 154 => some "neg_add_imm_64"
  | 155 => some "shlo_l_imm_alt_64"
  | 156 => some "shlo_r_imm_alt_64"
  | 157 => some "shar_r_imm_alt_64"
  | 158 => some "rot_r_64_imm"
  | 159 => some "rot_r_64_imm_alt"
  | 160 => some "rot_r_32_imm"
  | 161 => some "rot_r_32_imm_alt"
  | 170 => some "branch_eq"
  | 171 => some "branch_ne"
  | 172 => some "branch_lt_u"
  | 173 => some "branch_lt_s"
  | 174 => some "branch_ge_u"
  | 175 => some "branch_ge_s"
  | 180 => some "load_imm_jump_ind"
  | 190 => some "add_32"
  | 191 => some "sub_32"
  | 192 => some "mul_32"
  | 193 => some "div_u_32"
  | 194 => some "div_s_32"
  | 195 => some "rem_u_32"
  | 196 => some "rem_s_32"
  | 197 => some "shlo_l_32"
  | 198 => some "shlo_r_32"
  | 199 => some "shar_r_32"
  | 200 => some "add_64"
  | 201 => some "sub_64"
  | 202 => some "mul_64"
  | 203 => some "div_u_64"
  | 204 => some "div_s_64"
  | 205 => some "rem_u_64"
  | 206 => some "rem_s_64"
  | 207 => some "shlo_l_64"
  | 208 => some "shlo_r_64"
  | 209 => some "shar_r_64"
  | 210 => some "and"
  | 211 => some "xor"
  | 212 => some "or"
  | 213 => some "mul_upper_s_s"
  | 214 => some "mul_upper_u_u"
  | 215 => some "mul_upper_s_u"
  | 216 => some "set_lt_u"
  | 217 => some "set_lt_s"
  | 218 => some "cmov_iz"
  | 219 => some "cmov_nz"
  | 220 => some "rot_l_64"
  | 221 => some "rot_l_32"
  | 222 => some "rot_r_64"
  | 223 => some "rot_r_32"
  | 224 => some "and_inv"
  | 225 => some "or_inv"
  | 226 => some "xnor"
  | 227 => some "max"
  | 228 => some "max_u"
  | 229 => some "min"
  | 230 => some "min_u"
  | _ => none

/-- The block-termination opcodes T (GP §A.3, `sec:basicblocks`), in the paper's order:
    `trap`, `fallthrough`, `jump`, `jump_ind`, `load_imm_jump`, `load_imm_jump_ind`, `branch_eq`, `branch_ne`, `branch_ge_u`, `branch_ge_s`, `branch_lt_u`, `branch_lt_s`, `branch_eq_imm`, `branch_ne_imm`, `branch_lt_u_imm`, `branch_lt_s_imm`, `branch_le_u_imm`, `branch_le_s_imm`, `branch_ge_u_imm`, `branch_ge_s_imm`, `branch_gt_u_imm`, `branch_gt_s_imm`. -/
def terminatorOpcodes : List Nat :=
  [0, 1, 40, 50, 80, 180, 170, 171, 174, 175, 172, 173, 81, 82, 83, 87, 84, 88, 85, 89, 86, 90]

/-- The opcode of `trap`. -/
def trapOpcode : Nat := 0
/-- The opcode of `unlikely`. -/
def unlikelyOpcode : Nat := 2
/-- The opcode of `move_reg`. -/
def moveRegOpcode : Nat := 100

/-- The memory-access cost 𝔪 (GP §A.10). -/
def memoryCost : Nat := 25

/-- The gas cost table of GP §A.10 (`sec:gascosttables`), keyed by opcode:
    `(č, ď, x̌_A, x̌_L, x̌_S, x̌_M, x̌_D)` as written in the paper, before evaluation. -/
def costRow? : Nat → Option CostRow
  | 0 => some ⟨(.const 2), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- trap
  | 1 => some ⟨(.const 2), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- fallthrough
  | 2 => some ⟨(.const 40), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- unlikely
  | 10 => some ⟨(.const 100), (.const 4), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- ecalli
  | 20 => some ⟨(.const 1), (.const 2), (.const 0), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- load_imm_64
  | 30 => some ⟨(.const 25), (.const 1), (.const 1), (.const 0), (.const 1), (.const 0), (.const 0)⟩ -- store_imm_u8
  | 31 => some ⟨(.const 25), (.const 1), (.const 1), (.const 0), (.const 1), (.const 0), (.const 0)⟩ -- store_imm_u16
  | 32 => some ⟨(.const 25), (.const 1), (.const 1), (.const 0), (.const 1), (.const 0), (.const 0)⟩ -- store_imm_u32
  | 33 => some ⟨(.const 25), (.const 1), (.const 1), (.const 0), (.const 1), (.const 0), (.const 0)⟩ -- store_imm_u64
  | 40 => some ⟨(.const 15), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- jump
  | 50 => some ⟨(.const 22), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- jump_ind
  | 51 => some ⟨(.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- load_imm
  | 52 => some ⟨.memory, (.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0)⟩ -- load_u8
  | 53 => some ⟨.memory, (.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0)⟩ -- load_i8
  | 54 => some ⟨.memory, (.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0)⟩ -- load_u16
  | 55 => some ⟨.memory, (.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0)⟩ -- load_i16
  | 56 => some ⟨.memory, (.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0)⟩ -- load_u32
  | 57 => some ⟨.memory, (.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0)⟩ -- load_i32
  | 58 => some ⟨.memory, (.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0)⟩ -- load_u64
  | 59 => some ⟨(.const 25), (.const 1), (.const 1), (.const 0), (.const 1), (.const 0), (.const 0)⟩ -- store_u8
  | 60 => some ⟨(.const 25), (.const 1), (.const 1), (.const 0), (.const 1), (.const 0), (.const 0)⟩ -- store_u16
  | 61 => some ⟨(.const 25), (.const 1), (.const 1), (.const 0), (.const 1), (.const 0), (.const 0)⟩ -- store_u32
  | 62 => some ⟨(.const 25), (.const 1), (.const 1), (.const 0), (.const 1), (.const 0), (.const 0)⟩ -- store_u64
  | 70 => some ⟨(.const 25), (.const 1), (.const 1), (.const 0), (.const 1), (.const 0), (.const 0)⟩ -- store_imm_ind_u8
  | 71 => some ⟨(.const 25), (.const 1), (.const 1), (.const 0), (.const 1), (.const 0), (.const 0)⟩ -- store_imm_ind_u16
  | 72 => some ⟨(.const 25), (.const 1), (.const 1), (.const 0), (.const 1), (.const 0), (.const 0)⟩ -- store_imm_ind_u32
  | 73 => some ⟨(.const 25), (.const 1), (.const 1), (.const 0), (.const 1), (.const 0), (.const 0)⟩ -- store_imm_ind_u64
  | 80 => some ⟨(.const 15), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- load_imm_jump
  | 81 => some ⟨.branch, (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- branch_eq_imm
  | 82 => some ⟨.branch, (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- branch_ne_imm
  | 83 => some ⟨.branch, (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- branch_lt_u_imm
  | 84 => some ⟨.branch, (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- branch_le_u_imm
  | 85 => some ⟨.branch, (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- branch_ge_u_imm
  | 86 => some ⟨.branch, (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- branch_gt_u_imm
  | 87 => some ⟨.branch, (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- branch_lt_s_imm
  | 88 => some ⟨.branch, (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- branch_le_s_imm
  | 89 => some ⟨.branch, (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- branch_ge_s_imm
  | 90 => some ⟨.branch, (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- branch_gt_s_imm
  | 100 => some ⟨(.const 0), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- move_reg
  | 101 => some ⟨(.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- count_set_bits_64
  | 102 => some ⟨(.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- count_set_bits_32
  | 103 => some ⟨(.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- leading_zero_bits_64
  | 104 => some ⟨(.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- leading_zero_bits_32
  | 105 => some ⟨(.const 2), (.const 1), (.const 2), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- trailing_zero_bits_64
  | 106 => some ⟨(.const 2), (.const 1), (.const 2), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- trailing_zero_bits_32
  | 107 => some ⟨(.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- sign_extend_8
  | 108 => some ⟨(.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- sign_extend_16
  | 109 => some ⟨(.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- zero_extend_16
  | 110 => some ⟨(.const 1), (.overlap 1 2), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- reverse_bytes
  | 120 => some ⟨(.const 25), (.const 1), (.const 1), (.const 0), (.const 1), (.const 0), (.const 0)⟩ -- store_ind_u8
  | 121 => some ⟨(.const 25), (.const 1), (.const 1), (.const 0), (.const 1), (.const 0), (.const 0)⟩ -- store_ind_u16
  | 122 => some ⟨(.const 25), (.const 1), (.const 1), (.const 0), (.const 1), (.const 0), (.const 0)⟩ -- store_ind_u32
  | 123 => some ⟨(.const 25), (.const 1), (.const 1), (.const 0), (.const 1), (.const 0), (.const 0)⟩ -- store_ind_u64
  | 124 => some ⟨.memory, (.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0)⟩ -- load_ind_u8
  | 125 => some ⟨.memory, (.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0)⟩ -- load_ind_i8
  | 126 => some ⟨.memory, (.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0)⟩ -- load_ind_u16
  | 127 => some ⟨.memory, (.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0)⟩ -- load_ind_i16
  | 128 => some ⟨.memory, (.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0)⟩ -- load_ind_u32
  | 129 => some ⟨.memory, (.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0)⟩ -- load_ind_i32
  | 130 => some ⟨.memory, (.const 1), (.const 1), (.const 1), (.const 0), (.const 0), (.const 0)⟩ -- load_ind_u64
  | 131 => some ⟨(.const 2), (.overlap 2 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- add_imm_32
  | 132 => some ⟨(.const 1), (.overlap 1 2), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- and_imm
  | 133 => some ⟨(.const 1), (.overlap 1 2), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- xor_imm
  | 134 => some ⟨(.const 1), (.overlap 1 2), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- or_imm
  | 135 => some ⟨(.const 4), (.overlap 2 3), (.const 1), (.const 0), (.const 0), (.const 1), (.const 0)⟩ -- mul_imm_32
  | 136 => some ⟨(.const 3), (.const 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- set_lt_u_imm
  | 137 => some ⟨(.const 3), (.const 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- set_lt_s_imm
  | 138 => some ⟨(.const 2), (.overlap 2 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- shlo_l_imm_32
  | 139 => some ⟨(.const 2), (.overlap 2 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- shlo_r_imm_32
  | 140 => some ⟨(.const 2), (.overlap 2 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- shar_r_imm_32
  | 141 => some ⟨(.const 3), (.const 4), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- neg_add_imm_32
  | 142 => some ⟨(.const 3), (.const 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- set_gt_u_imm
  | 143 => some ⟨(.const 3), (.const 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- set_gt_s_imm
  | 144 => some ⟨(.const 2), (.const 4), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- shlo_l_imm_alt_32
  | 145 => some ⟨(.const 2), (.const 4), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- shlo_r_imm_alt_32
  | 146 => some ⟨(.const 2), (.const 4), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- shar_r_imm_alt_32
  | 147 => some ⟨(.const 2), (.const 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- cmov_iz_imm
  | 148 => some ⟨(.const 2), (.const 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- cmov_nz_imm
  | 149 => some ⟨(.const 1), (.overlap 1 2), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- add_imm_64
  | 150 => some ⟨(.const 3), (.overlap 1 2), (.const 1), (.const 0), (.const 0), (.const 1), (.const 0)⟩ -- mul_imm_64
  | 151 => some ⟨(.const 1), (.overlap 1 2), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- shlo_l_imm_64
  | 152 => some ⟨(.const 1), (.overlap 1 2), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- shlo_r_imm_64
  | 153 => some ⟨(.const 1), (.overlap 1 2), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- shar_r_imm_64
  | 154 => some ⟨(.const 2), (.const 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- neg_add_imm_64
  | 155 => some ⟨(.const 1), (.const 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- shlo_l_imm_alt_64
  | 156 => some ⟨(.const 1), (.const 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- shlo_r_imm_alt_64
  | 157 => some ⟨(.const 1), (.const 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- shar_r_imm_alt_64
  | 158 => some ⟨(.const 1), (.overlap 1 2), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- rot_r_64_imm
  | 159 => some ⟨(.const 1), (.const 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- rot_r_64_imm_alt
  | 160 => some ⟨(.const 2), (.overlap 2 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- rot_r_32_imm
  | 161 => some ⟨(.const 2), (.const 4), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- rot_r_32_imm_alt
  | 170 => some ⟨.branch, (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- branch_eq
  | 171 => some ⟨.branch, (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- branch_ne
  | 172 => some ⟨.branch, (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- branch_lt_u
  | 173 => some ⟨.branch, (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- branch_lt_s
  | 174 => some ⟨.branch, (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- branch_ge_u
  | 175 => some ⟨.branch, (.const 1), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- branch_ge_s
  | 180 => some ⟨(.const 22), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- load_imm_jump_ind
  | 190 => some ⟨(.const 2), (.overlap 2 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- add_32
  | 191 => some ⟨(.const 2), (.overlap 2 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- sub_32
  | 192 => some ⟨(.const 4), (.overlap 2 3), (.const 1), (.const 0), (.const 0), (.const 1), (.const 0)⟩ -- mul_32
  | 193 => some ⟨(.const 60), (.const 4), (.const 1), (.const 0), (.const 0), (.const 0), (.const 1)⟩ -- div_u_32
  | 194 => some ⟨(.const 60), (.const 4), (.const 1), (.const 0), (.const 0), (.const 0), (.const 1)⟩ -- div_s_32
  | 195 => some ⟨(.const 60), (.const 4), (.const 1), (.const 0), (.const 0), (.const 0), (.const 1)⟩ -- rem_u_32
  | 196 => some ⟨(.const 60), (.const 4), (.const 1), (.const 0), (.const 0), (.const 0), (.const 1)⟩ -- rem_s_32
  | 197 => some ⟨(.const 2), (.overlapShift 3 4), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- shlo_l_32
  | 198 => some ⟨(.const 2), (.overlapShift 3 4), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- shlo_r_32
  | 199 => some ⟨(.const 2), (.overlapShift 3 4), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- shar_r_32
  | 200 => some ⟨(.const 1), (.overlap 1 2), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- add_64
  | 201 => some ⟨(.const 1), (.overlap 1 2), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- sub_64
  | 202 => some ⟨(.const 3), (.overlap 1 2), (.const 1), (.const 0), (.const 0), (.const 1), (.const 0)⟩ -- mul_64
  | 203 => some ⟨(.const 60), (.const 4), (.const 1), (.const 0), (.const 0), (.const 0), (.const 1)⟩ -- div_u_64
  | 204 => some ⟨(.const 60), (.const 4), (.const 1), (.const 0), (.const 0), (.const 0), (.const 1)⟩ -- div_s_64
  | 205 => some ⟨(.const 60), (.const 4), (.const 1), (.const 0), (.const 0), (.const 0), (.const 1)⟩ -- rem_u_64
  | 206 => some ⟨(.const 60), (.const 4), (.const 1), (.const 0), (.const 0), (.const 0), (.const 1)⟩ -- rem_s_64
  | 207 => some ⟨(.const 1), (.overlapShift 2 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- shlo_l_64
  | 208 => some ⟨(.const 1), (.overlapShift 2 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- shlo_r_64
  | 209 => some ⟨(.const 1), (.overlapShift 2 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- shar_r_64
  | 210 => some ⟨(.const 1), (.overlap 1 2), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- and
  | 211 => some ⟨(.const 1), (.overlap 1 2), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- xor
  | 212 => some ⟨(.const 1), (.overlap 1 2), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- or
  | 213 => some ⟨(.const 4), (.const 4), (.const 1), (.const 0), (.const 0), (.const 1), (.const 0)⟩ -- mul_upper_s_s
  | 214 => some ⟨(.const 4), (.const 4), (.const 1), (.const 0), (.const 0), (.const 1), (.const 0)⟩ -- mul_upper_u_u
  | 215 => some ⟨(.const 6), (.const 4), (.const 1), (.const 0), (.const 0), (.const 1), (.const 0)⟩ -- mul_upper_s_u
  | 216 => some ⟨(.const 3), (.const 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- set_lt_u
  | 217 => some ⟨(.const 3), (.const 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- set_lt_s
  | 218 => some ⟨(.const 2), (.const 2), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- cmov_iz
  | 219 => some ⟨(.const 2), (.const 2), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- cmov_nz
  | 220 => some ⟨(.const 1), (.overlapShift 2 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- rot_l_64
  | 221 => some ⟨(.const 2), (.overlapShift 3 4), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- rot_l_32
  | 222 => some ⟨(.const 1), (.overlapShift 2 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- rot_r_64
  | 223 => some ⟨(.const 2), (.overlapShift 3 4), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- rot_r_32
  | 224 => some ⟨(.const 2), (.const 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- and_inv
  | 225 => some ⟨(.const 2), (.const 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- or_inv
  | 226 => some ⟨(.const 2), (.overlap 2 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- xnor
  | 227 => some ⟨(.const 3), (.overlap 2 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- max
  | 228 => some ⟨(.const 3), (.overlap 2 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- max_u
  | 229 => some ⟨(.const 3), (.overlap 2 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- min
  | 230 => some ⟨(.const 3), (.overlap 2 3), (.const 1), (.const 0), (.const 0), (.const 0), (.const 0)⟩ -- min_u
  | _ => none

end PVM
