(*

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
 
 *)

theory MachineDatatypes 
imports "HOL-Word.WordBitwise" x86_InstructionMnemonics
begin          

section "Semantics of X86 assembly"

subsection "Datastructures"
text {*
  The datastructures for a deep embedding of assembly into Isabelle.
*} 

datatype bit_mask = 
Eight | EightHigh | Sixteen | ThirtyTwo | SixtyFour | OneHundredTwentyEight | TwoHundredFiftySix | FiveHundredTwelve

datatype register_mnemonic =
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
ymm15w3| ymm15w2| ymm15w1| ymm15w0

(* To be reomoved once migrated to SIMD register model *)
abbreviation ymm0 where "ymm0 \<equiv> (ymm0w3,ymm0w2,ymm0w1,ymm0w0)"
abbreviation ymm1 where "ymm1 \<equiv> (ymm1w3,ymm1w2,ymm1w1,ymm1w0)"
abbreviation ymm2 where "ymm2 \<equiv> (ymm2w3,ymm2w2,ymm2w1,ymm2w0)"
abbreviation ymm3 where "ymm3 \<equiv> (ymm3w3,ymm3w2,ymm3w1,ymm3w0)"
abbreviation ymm4 where "ymm4 \<equiv> (ymm4w3,ymm4w2,ymm4w1,ymm4w0)"
abbreviation ymm5 where "ymm5 \<equiv> (ymm5w3,ymm5w2,ymm5w1,ymm5w0)"
abbreviation ymm6 where "ymm6 \<equiv> (ymm6w3,ymm6w2,ymm6w1,ymm6w0)"
abbreviation ymm7 where "ymm7 \<equiv> (ymm7w3,ymm7w2,ymm7w1,ymm7w0)"
abbreviation ymm8 where "ymm8 \<equiv> (ymm8w3,ymm8w2,ymm8w1,ymm8w0)"
abbreviation ymm9 where "ymm9 \<equiv> (ymm9w3,ymm9w2,ymm9w1,ymm9w0)"
abbreviation ymm10 where "ymm10 \<equiv> (ymm10w3,ymm10w2,ymm10w1,ymm10w0)"
abbreviation ymm11 where "ymm11 \<equiv> (ymm11w3,ymm11w2,ymm11w1,ymm11w0)"
abbreviation ymm12 where "ymm12 \<equiv> (ymm12w3,ymm12w2,ymm12w1,ymm12w0)"
abbreviation ymm13 where "ymm13 \<equiv> (ymm13w3,ymm13w2,ymm13w1,ymm13w0)"
abbreviation ymm14 where "ymm14 \<equiv> (ymm14w3,ymm14w2,ymm14w1,ymm14w0)"
abbreviation ymm15 where "ymm15 \<equiv> (ymm15w3,ymm15w2,ymm15w1,ymm15w0)"


(* Needed for AVX-512
datatype simd_register_mnemonic = 
zmm0 | zmm1 | zmm2 | zmm3 | zmm4 | zmm5 | zmm6 | zmm7 | 
zmm8 | zmm9 | zmm10 | zmm11 | zmm12 | zmm13 | zmm14 | zmm15 | zmm16 | zmm17 | zmm18 | zmm19 | 
zmm20 | zmm21 | zmm22 | zmm23 | zmm24 | zmm25 | zmm26 | zmm27 | zmm28 | zmm29 | 
zmm30 | zmm31 | zmm32
*)
datatype register =
  General bit_mask register_mnemonic |
  SIMD bit_mask register_mnemonic register_mnemonic register_mnemonic register_mnemonic 
(* | SIMD bit_mask simd_register_mnemonic NEEDED FOR AVX-512 *)

datatype register_sig =
  General_sig bit_mask 
  | SIMD_sig bit_mask

datatype label = string

datatype immediate =                         
    ImmVal   int 
  | ImmLabel string

datatype address =
    A_FromReg register
  | A_Label string
  | A_Constant int
  | A_WordConstant "64 word"
  | A_Plus address address
  | A_Minus address address
  | A_Mult int address 
  | A_SizeDirective nat address

datatype operand_dest =
    Reg register
    | Memory bit_mask address
datatype operand_dest_sig =
   Reg_sig register_sig
   | Memory_sig bit_mask

datatype operand_src =
    Storage operand_dest
    |Immediate bit_mask immediate

datatype operand_src_sig =
  Storage_sig operand_dest_sig
| Immediate_sig

type_synonym instr_mnemonic = instr_mnemonic_set_skylake_sp

datatype instr =
  Nullary instr_mnemonic 
| Unary instr_mnemonic operand_src
| Binary instr_mnemonic operand_dest operand_src
| Ternary instr_mnemonic operand_dest operand_src operand_src 

datatype operand_sig = 
  Nullary_sig  
| Unary_sig operand_src_sig
| Binary_sig operand_dest_sig operand_src_sig
| Ternary_sig operand_dest_sig operand_src_sig operand_src_sig 

datatype instr_mnemonic_family = 
        IMF_8088 | IMF_8088_x87 | IMF_80188 | IMF_80286 | IMF_80286_x87 | IMF_80386 | IMF_80386_x87 
      | IMF_80486 | IMF_Pentium | IMF_PentiumMMX | IMF_PentiumMMX_MMX | IMF_PentiumPro | IMF_PentiumPro_x87 
      | IMF_PentiumII | IMF_SSE | IMF_SSE_x87 | IMF_SSE_SIMDMMX | IMF_SSE_SIMD | IMF_SSE2 | IMF_SSE2_SIMDMMX 
      | IMF_SSE2_SIMD | IMF_SSE3 | IMF_SSE3_x87 | IMF_SSE3_SIMD | IMF_X86_64 | IMF_SSSE3_SIMDMMX | IMF_SSE4_1_SIMD 
      | IMF_VT_X | IMF_SSE4_2 | IMF_SSE4_2_SIMD | IMF_AVX | IMF_AVX_2 | IMF_AVX2 | IMF_FMA | IMF_BM1_BM2 
      | IMF_AVX_512_F_CD | IMF_AVX_512_VL_DQ_BW   

type_synonym instr_sig = "instr_mnemonic_family \<times> instr_mnemonic \<times> operand_sig"

datatype flag =
  flag_of | flag_sf | flag_zf |  flag_pf |flag_cf 
(* | flag_af | flag_tf |flag_if |flag_df | flag_nt | flag_rf | flag_vm | flag_ac | flag_vif | flag_vip | flag_id *)


text {*
  A \emph{data section} of a binary is a section with a name, a size (in bytes) and data.
  Examples:
    .byte 0
  This is a data constant with value 0 and size 1 (in bytes).
    .quad frame\_dummy
  This is a data variable with as value the 64 bit address ''frame\_dummy'' and size 8 (in bytes).
*}
datatype data_value =
    Data_Byte "8 word"
  | Data_Quad "64 word"
  | Data_Var string (* a label representing a 64 bit address *)
  | Data_String string nat 

text {*
  The deep embedding of an assembly file consists of a list of text- and datasections.
*}
record assembly =
  text_sections :: "(nat \<times> instr \<times> nat) list"
  data_sections :: "(nat \<times> (data_value list))  list"  
  labels_to_offsets :: "(string \<times> nat) list"
  binary_offset :: "64 word"

record state =
  regs :: "register_mnemonic \<Rightarrow> 64 word"
(*  simd_regs :: "simd_register_mnemonic \<Rightarrow> 512 word" NEEDED TO EXPAND TO AVX-512 *)
  mem :: "64 word \<Rightarrow> 8 word"
  flags :: "flag \<Rightarrow> bool"

end
  
