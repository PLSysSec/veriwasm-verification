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
 
theory TestLemma_Setup
  imports Main  
  TestInstructions
 "HOL-Library.Rewrite"
 "../../isabelle/Monads/Abstract_System"
 State_Rewriting

 
begin

fun flag_annotation 
  where "flag_annotation _ = {flag_cf, flag_zf, flag_sf, flag_of, flag_pf}" 

lemma separation_is_irreflexive[simp]:
  assumes "no_block_overflow a"
  shows "a \<bowtie> a \<longleftrightarrow> snd a = 0"
  using assms
  apply (cases a)
  apply (auto simp add: sep.simps no_block_overflow.simps)
  apply unat_arith
  by (auto simp add: unat_of_nat)


lemma master_block_implies_no_block_overflow_16_8[simp]:
  assumes "master blocks (a,16) i"
  shows "no_block_overflow (a+8,8)"
  using assms
  unfolding seps_def master_def
    apply (auto simp add: no_block_overflow.simps )
  by unat_arith

lemma master_block_implies_no_block_overflow_16_8_2[simp]:
  assumes "master blocks (a,16) i"
  shows "no_block_overflow (a,8)"
  using assms
  unfolding seps_def master_def
  by (auto simp add: no_block_overflow.simps )

declare length_word_to_bytes[simp]
declare take_bits_def[simp]
declare exec_BV_Plus_def[simp]
declare bv_cat.simps [simp]
declare bv_slice.simps [simp]
declare word_sless_def [simp]
declare word_sle_def [simp]
declare uint_word_ariths[simp]
declare parity_def [simp add]
declare parity_offset_def [simp add]
declare xor_def [simp add]

lemma nat_to_numeral_m16 [simp]:
  shows "(Suc (Suc 0)) = 2"
  by auto

(*
lemma length_word_to_bytes[simp]:
  shows" (length (word_to_bytes w i)) = i"
  apply (simp only: word_to_bytes.simps)
*)(*

 master blocks (addr, 16) MemoryBlockID \<Longrightarrow>
    dst = simd_dst \<Longrightarrow>
    (addr + 8, 8) \<sqsubseteq> (addr, 16) \<Longrightarrow>

lemma meh[simp]:

\<not> (addr + 8, 8) \<sqsubseteq> (addr, 16)


lemma master_block_implies_no_block_overflow_offset[simp]:
  assumes "master blocks (a,s) i"
  and "s \<ge> unat offset"
  shows "no_block_overflow (a+offset,s-(unat offset))"
  using assms
  unfolding seps_def master_def
    apply (auto simp add: no_block_overflow.simps )
  by unat_arith
*)
declare Machine.set_def    [simp]
declare fun_upd_twist [simp]

abbreviation general_regs :: "register_mnemonic set"
  where "general_regs  \<equiv> {rax, rbx, rcx, rdx,
r8,  r9, r10, r11, r12, r13, r14, r15 }"

(*
abbreviation simd_regs :: "(register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic)  set"  
  where "simd_regs \<equiv> {ymm0,ymm1,ymm2,ymm3,ymm4,ymm5,ymm6,ymm7,ymm8,ymm9,ymm10,ymm11,ymm12,ymm13,ymm14,ymm15}"
*)
abbreviation simd_regs :: "(register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic)  set"
  where "simd_regs \<equiv> {ymm8,ymm9,ymm10}"

fun simd_w3 :: "(register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic) => register_mnemonic"
  where "simd_w3 (a,b,c,d) = a"
fun simd_w2 :: "(register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic) => register_mnemonic"
  where "simd_w2 (a,b,c,d) = b"
fun simd_w1 :: "(register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic) => register_mnemonic"
  where "simd_w1 (a,b,c,d) = c"
fun simd_w0 :: "(register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic) => register_mnemonic"
  where "simd_w0 (a,b,c,d) = d"

abbreviation simd_dst where "simd_dst \<equiv> ymm9"
abbreviation simd_src where "simd_src \<equiv> ymm8"

fun tuple_to_list :: "('a \<times> 'a  \<times> 'a  \<times> 'a) \<Rightarrow> 'a list"
  where  "tuple_to_list (a,b,c,d) =  a # b # c # [d]"

fun State     :: "(register_mnemonic \<times> 64 word) list \<Rightarrow> 
                  (64 word \<times> 'a::len0 word \<times> nat) list \<Rightarrow>
                  (flag \<times> bool) list \<Rightarrow> state \<Rightarrow> state"
  where   "State []         []                  []          \<sigma> = \<sigma>"
  |       "State ((r,v)#rr) mm                  ff          \<sigma> = (let newreg = (set (regs (State rr mm ff \<sigma>)) (r) (v)) in (State rr mm ff \<sigma>)\<lparr>regs := newreg\<rparr>) "
  |       "State rr         mm                  ((f,v)#ff)  \<sigma> = (let newf = (set (flags (State rr mm ff \<sigma>)) (f) (v)) in (State rr mm ff \<sigma>)\<lparr>flags := newf\<rparr>) "
  |       "State rr         ((addr,w,msize)#mm) ff          \<sigma> = (let newmem =  write_blocks [addr \<rhd> (word_to_bytes w msize)] (mem (State rr mm ff \<sigma>)) in (State rr mm ff \<sigma>)\<lparr>mem := newmem\<rparr>) "


end

