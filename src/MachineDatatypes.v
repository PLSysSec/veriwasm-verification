Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
From X86 Require Export x86_InstructionMnemonics.

Inductive bit_mask :=
Eight | EightHigh | Sixteen | ThirtyTwo | SixtyFour | OneHundredTwentyEight | TwoHundredFiftySix | FiveHundredTwelve.

Inductive register_mnemonic :=
rax |  rbx |  rcx |  rdx |  rbp |  rsp |  rsi |  rdi | rip |
r8 |   r9 |  r10 |  r11 |  r12 |  r13 |  r14 |  r15 |
cs |  ds |  es |  fs |  gs |  ss |  
(* To be reomoved once migrated to SIMD register model *)
ymm0w3|  ymm0w2|  ymm0w1|  ymm0w0 |
ymm1w3|  ymm1w2|  ymm1w1|  ymm1w0 |
ymm2w3|  ymm2w2|  ymm2w1|  ymm2w0 |
ymm3w3|  ymm3w2|  ymm3w1|  ymm3w0 |
ymm4w3|  ymm4w2|  ymm4w1|  ymm4w0 |
ymm5w3|  ymm5w2|  ymm5w1|  ymm5w0 |
ymm6w3|  ymm6w2|  ymm6w1|  ymm6w0 |
ymm7w3|  ymm7w2|  ymm7w1|  ymm7w0 |
ymm8w3|  ymm8w2|  ymm8w1|  ymm8w0 |
ymm9w3|  ymm9w2|  ymm9w1|  ymm9w0 |
ymm10w3| ymm10w2| ymm10w1| ymm10w0 |
ymm11w3| ymm11w2| ymm11w1| ymm11w0 |
ymm12w3| ymm12w2| ymm12w1| ymm12w0 |
ymm13w3| ymm13w2| ymm13w1| ymm13w0 |
ymm14w3| ymm14w2| ymm14w1| ymm14w0 |
ymm15w3| ymm15w2| ymm15w1| ymm15w0.

(* To be reomoved once migrated to SIMD register model *)
(*
abbreviation ymm0 where "ymm0 ≡ (ymm0w3,ymm0w2,ymm0w1,ymm0w0)"
abbreviation ymm1 where "ymm1 ≡ (ymm1w3,ymm1w2,ymm1w1,ymm1w0)"
abbreviation ymm2 where "ymm2 ≡ (ymm2w3,ymm2w2,ymm2w1,ymm2w0)"
abbreviation ymm3 where "ymm3 ≡ (ymm3w3,ymm3w2,ymm3w1,ymm3w0)"
abbreviation ymm4 where "ymm4 ≡ (ymm4w3,ymm4w2,ymm4w1,ymm4w0)"
abbreviation ymm5 where "ymm5 ≡ (ymm5w3,ymm5w2,ymm5w1,ymm5w0)"
abbreviation ymm6 where "ymm6 ≡ (ymm6w3,ymm6w2,ymm6w1,ymm6w0)"
abbreviation ymm7 where "ymm7 ≡ (ymm7w3,ymm7w2,ymm7w1,ymm7w0)"
abbreviation ymm8 where "ymm8 ≡ (ymm8w3,ymm8w2,ymm8w1,ymm8w0)"
abbreviation ymm9 where "ymm9 ≡ (ymm9w3,ymm9w2,ymm9w1,ymm9w0)"
abbreviation ymm10 where "ymm10 ≡ (ymm10w3,ymm10w2,ymm10w1,ymm10w0)"
abbreviation ymm11 where "ymm11 ≡ (ymm11w3,ymm11w2,ymm11w1,ymm11w0)"
abbreviation ymm12 where "ymm12 ≡ (ymm12w3,ymm12w2,ymm12w1,ymm12w0)"
abbreviation ymm13 where "ymm13 ≡ (ymm13w3,ymm13w2,ymm13w1,ymm13w0)"
abbreviation ymm14 where "ymm14 ≡ (ymm14w3,ymm14w2,ymm14w1,ymm14w0)"
abbreviation ymm15 where "ymm15 ≡ (ymm15w3,ymm15w2,ymm15w1,ymm15w0)"
*)

Inductive register :=
| General : bit_mask -> register_mnemonic -> register
| SIMD : bit_mask -> register_mnemonic -> register_mnemonic -> register_mnemonic -> register_mnemonic -> register.

Inductive register_sig :=
| General_sig : bit_mask -> register_sig
| SIMD_sig : bit_mask -> register_sig.

Definition label := string.

Inductive immediate :=
| ImmVal : Z -> immediate
| ImmLabel : string -> immediate.

Inductive address :=
| A_FromReg : register -> address
| A_Label : string -> address
| A_Constant : Z -> address
| A_WordConstant : Z -> address (*64word -> address*)
| A_Plus : address -> address -> address
| A_Minus : address -> address -> address
| A_Mult : Z -> address -> address 
| A_SizeDirective : N -> address -> address.

Inductive operand_dest :=
| Reg : register -> operand_dest
| Memory : bit_mask -> address -> operand_dest.

Inductive operand_dest_sig :=
| Reg_sig : register_sig -> operand_dest_sig
| Memory_sig : bit_mask -> operand_dest_sig.

Inductive operand_src :=
| Storage : operand_dest -> operand_src
| Immediate : bit_mask -> immediate -> operand_src.

Inductive operand_src_sig :=
| Storage_sig : operand_dest_sig -> operand_src_sig
| Immediate_sig : operand_src_sig.

Definition instr_mnemonic := instr_mnemonic_set_skylake_sp.

Inductive instr :=
| Nullary : instr_mnemonic -> instr 
| Unary : instr_mnemonic -> operand_src -> instr
| Binary : instr_mnemonic -> operand_dest -> operand_src -> instr
| Ternary : instr_mnemonic -> operand_dest -> operand_src -> operand_src -> instr.

Inductive operand_sig := 
| Nullary_sig : operand_sig
| Unary_sig : operand_src_sig -> operand_sig
| Binary_sig : operand_dest_sig -> operand_src_sig -> operand_sig
| Ternary_sig : operand_dest_sig -> operand_src_sig -> operand_src_sig -> operand_sig.

Inductive instr_mnemonic_family := 
        IMF_8088 | IMF_8088_x87 | IMF_80188 | IMF_80286 | IMF_80286_x87 | IMF_80386 | IMF_80386_x87 
      | IMF_80486 | IMF_Pentium | IMF_PentiumMMX | IMF_PentiumMMX_MMX | IMF_PentiumPro | IMF_PentiumPro_x87 
      | IMF_PentiumII | IMF_SSE | IMF_SSE_x87 | IMF_SSE_SIMDMMX | IMF_SSE_SIMD | IMF_SSE2 | IMF_SSE2_SIMDMMX 
      | IMF_SSE2_SIMD | IMF_SSE3 | IMF_SSE3_x87 | IMF_SSE3_SIMD | IMF_X86_64 | IMF_SSSE3_SIMDMMX | IMF_SSE4_1_SIMD 
      | IMF_VT_X | IMF_SSE4_2 | IMF_SSE4_2_SIMD | IMF_AVX | IMF_AVX_2 | IMF_AVX2 | IMF_FMA | IMF_BM1_BM2 
      | IMF_AVX_512_F_CD | IMF_AVX_512_VL_DQ_BW.

(*
type_synonym instr_sig = "instr_mnemonic_family × instr_mnemonic × operand_sig"
*)

Inductive flag :=
  flag_of | flag_sf | flag_zf |  flag_pf |flag_cf .
(* | flag_af | flag_tf |flag_if |flag_df | flag_nt | flag_rf | flag_vm | flag_ac | flag_vif | flag_vip | flag_id *)


(*
  A \emph{data section} of a binary is a section with a name, a size (in bytes) and data.
  Examples:
    .byte 0
  This is a data constant with value 0 and size 1 (in bytes).
    .quad frame\_dummy
  This is a data variable with as value the 64 bit address ''frame\_dummy'' and size 8 (in bytes).
*)
Inductive data_value :=
| Data_Byte : Z -> data_value (*"8 word"*)
| Data_Quad : Z -> data_value (*"64 word"*)
| Data_Var : string -> data_value (* a label representing a 64 bit address *)
| Data_String : string -> N -> data_value.

(*
  The deep embedding of an assembly file consists of a list of text- and datasections.
*)
Record assembly :=
{  text_sections : "(nat × instr × nat) list"
   data_sections : "(nat × (data_value list))  list"  
   labels_to_offsets : "(string × nat) list"
   binary_offset : Z (* "64 word" *)
}.

record state =
  regs :: "register_mnemonic ⇒ 64 word"
(*  simd_regs :: "simd_register_mnemonic ⇒ 512 word" NEEDED TO EXPAND TO AVX-512 *)
  mem :: "64 word ⇒ 8 word"
  flags :: "flag ⇒ bool"



