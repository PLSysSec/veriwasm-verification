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

theory CaseStudy_IEEE_Div
  imports "reassembly_all_execution_debug.Leviathan_Setup"
          "HOL-Library.Rewrite"
          "../../../isabelle/Monads/Abstract_System"
begin



lemma merge_blocks_same_address[simp]: (* TODO generalize this for other offsets and move to Memory_Rewriting *)
  fixes x ::  "64 word"
    and y :: "'a::len0 word"
  assumes "h - l = 3"
      and "no_block_overflow (a - 48, 8)"
      and "h < LENGTH('a) div 8"
  shows "merge_blocks (a - 48, rev (\<lbrace>7,0\<rbrace>x)) (a - 44, rev (\<lbrace>h,l\<rbrace>y)) = (a - 48, rev (\<lbrace>3,0\<rbrace>x) @ rev (\<lbrace>h,l\<rbrace>y))"
proof-
  have 1: "a - 48 < a - 44"
    using assms(2)
    unfolding no_block_overflow.simps
    apply unat_arith
    by auto
  have 2: "44 \<le> unat a \<Longrightarrow> 48 \<le> unat a"
    using assms(2)
    unfolding no_block_overflow.simps
    apply unat_arith
    by auto
  have 11: "a - 48 \<le> a - 44"
    apply (rule dual_order.strict_implies_order)
    by (rule 1)
  hence 3: "min (a - 48) (a - 44) = a - 48"
    by (auto simp add: min_def)
  have 4: "unat (a - 44 - (a - 48)) = 4"
    using assms(2)
    unfolding no_block_overflow.simps
    by unat_arith
  have 5: "length (\<lbrace>h,l\<rbrace>y) = 4"
    using assms(1,3)
    apply (cases "h  \<ge> Suc l", auto simp add: min_def)
    by linarith
  show ?thesis
    using assms(1)
    unfolding merge_blocks.simps
    apply (subst 1)
    apply (subst 3)
    apply (subst 4)
    apply (auto simp only: length_rev 5)
    by (auto simp add: take_rev unat_sub_if' 2)
qed








(*
  ----------
  REMAINDER
  ----------
*)

definition (in execution_context) ieee_funcs where
  "ieee_funcs \<alpha> \<equiv> [
  ''__ieee754_fmod'' \<mapsto> \<lambda> \<sigma> .
      let' (x,_) = data_from_src \<alpha> \<sigma> (Storage (Reg (General SixtyFour ymm0w0)));
           (y,_) = data_from_src \<alpha> \<sigma> (Storage (Reg (General SixtyFour ymm1w0)));
           \<sigma> = put \<alpha> (Reg (General SixtyFour ymm0w0)) (x mod\<^sup>f y) \<sigma> 
       in
      \<sigma>
]"

type_synonym floyd_invar = \<open>64 word \<rightharpoonup> (state \<Rightarrow> bool)\<close>

(* Three flags generation SF,OF,ZF *)
instruction_semantics_parser "../InstructionSemantics/strata_rules_3flags"   
lemmas strata_rules_3flags.semantics_def [code]               


x86_64_parser "../examples/Remainder/fdlibm/remainder_little_e.s"

lemmas remainder_little_e.assembly_def [code]
 
locale assembly = remainder_little_e + execution_context + strata_rules_3flags +
  assumes funcs_def: "funcs \<equiv> ieee_funcs \<alpha>"
begin

abbreviation "\<alpha> \<equiv> assembly"

schematic_goal unfold_semantics:
  shows \<open>instr_semantics semantics instr_sig = ?x\<close>
  by (simp add: semantics_def simp_rules)

lemma binary_offset[simp]:
  shows "binary_offset assembly = boffset"
  by (simp add: assembly_def assembly.defs)
schematic_goal unfold_labels[simp]:
  shows "label_to_address assembly = ?x"
  apply (rule ext)
  apply (unfold label_to_address_def)
  apply (unfold binary_offset)
  by (auto simp add: label_to_address_def assembly_def assembly.defs)

fun ieee_flag_annotation :: "flag_annotation"
  where "ieee_flag_annotation loc =
    (if loc \<in> {boffset + 1243, boffset + 1318, boffset + 1429} then {flag_zf} else
   (*  if loc = boffset + 105 then {flag_zf, flag_sf, flag_of} else*)
     {})"

definition step :: \<open>(unit, state) se\<close> where
  \<open>step \<sigma> \<equiv>
    let' pc = get_rip \<sigma>;
         index = the (instr_index lookup_table boffset pc);
         (_,i,s) = (text_sections \<alpha>)!index;
         \<sigma> = exec_instr \<alpha> ieee_flag_annotation semantics i s \<sigma>
    in
      Some ((), \<sigma>)\<close>

lemma wps_stepI[wps_intros]:
  assumes \<open>let' pc = get_rip \<sigma>;
                index = the (instr_index lookup_table boffset pc);
                (_,i,s) = (text_sections \<alpha>)!index;
                \<sigma> = exec_instr \<alpha> ieee_flag_annotation semantics i s \<sigma>
           in
             Q () \<sigma>\<close>
  shows \<open>wps step Q \<sigma>\<close>
  using assms
  unfolding step_def
  by (auto simp add: Let'_def Let_def wps_def)

definition wf_state :: \<open>state \<Rightarrow> bool\<close> where
  \<open>wf_state _ = True\<close>

definition halted :: \<open>state \<Rightarrow> bool\<close> where
  \<open>halted \<sigma> \<equiv> get_rip \<sigma> = boffset + 1745\<close>

interpretation cfg_system step halted wf_state get_rip
  by standard (simp add: wf_state_def det_system.is_weak_invar_def)

declare halted_def[simp]
declare wf_state_def[simp]

method symbolic_execution uses masters add del =
  (rule wps_rls),
  rewrite_one_let' del: del,
  rewrite_one_let' add: lookup_table_def instr_index_def entry_size_def del: del,
  rewrite_one_let' add: assembly_def del: del,
  rewrite_one_let' del: del,
  rewrite_one_let' add: exec_instr.simps del: del,
  rewrite_one_let' add: unfold_semantics del: del,
  insert masters,
  (rewrite_one_let' add: add del: del)+,
  (thin_tac \<open>master _ _ _\<close>)+,
  rule linvar_unfoldI,
  simp (no_asm_simp) del: del

method restart_symbolic_execution uses add del =
  ((rewrite_one_let' add: add del: del)+,
  (thin_tac \<open>master _ _ _\<close>)+,
  rule linvar_unfoldI,
  simp (no_asm_simp) del: del)
|
  (((thin_tac "master _ _ _")+)?,
  rule linvar_unfoldI,
  simp (no_asm_simp) del: del)



definition xor_sign :: "'a::len word \<Rightarrow> bool \<Rightarrow> 'a::len word"
  where "xor_sign a b \<equiv> set_bit a (LENGTH('a) - 1) (msb a \<noteq> b)"


definition pp_\<Theta> :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> floyd_invar\<close> where
  \<open>pp_\<Theta> rsp\<^sub>0 ymm0w0\<^sub>0 ymm1w0\<^sub>0 x \<equiv> [
    (* precondition *)
    (boffset + 1164) \<mapsto> \<lambda>\<sigma>. regs \<sigma> rsp = rsp\<^sub>0 \<and>
                   regs \<sigma> ymm0w0 = ymm0w0\<^sub>0 \<and>
                   regs \<sigma> ymm1w0 = ymm1w0\<^sub>0 \<and>
                   \<sigma> \<turnstile> *[boffset + 1857,8] = (9223372036854775807::64 word) \<and>
                   \<sigma> \<turnstile> *[boffset + 1873,8] = (4602678819172646912::64 word),
    (* postcondition *)
    (boffset + 1745) \<mapsto> \<lambda>\<sigma>. regs \<sigma> ymm0w0 =
        (let x_lo :: 32 word = \<langle>31,0\<rangle>ymm0w0\<^sub>0;
             x_hi :: 32 word = \<langle>63,32\<rangle>ymm0w0\<^sub>0;
             p_lo :: 32 word = \<langle>31,0\<rangle>ymm1w0\<^sub>0;
             p_hi :: 32 word = \<langle>63,32\<rangle>ymm1w0\<^sub>0  in
        if ymm1w0\<^sub>0 \<in> {0\<^sup>-, 0\<^sup>+} \<or>
           \<bar>x_hi\<bar>\<^sup>f >s 2146435071 \<or>
            ((\<bar>p_hi\<bar>\<^sup>f >s 2146435071) \<and> (\<bar>p_hi\<bar>\<^sup>f + 2148532224 \<noteq> 0 \<or> p_lo \<noteq> 0)) then
          ymm1w0\<^sub>0 *\<^sup>f ymm0w0\<^sub>0 div\<^sup>f (ymm1w0\<^sub>0 *\<^sup>f ymm0w0\<^sub>0)
        else if x_lo = p_lo \<longrightarrow> \<bar>x_hi\<bar>\<^sup>f \<noteq> \<bar>p_hi\<bar>\<^sup>f then
          let x' = 
          if \<bar>p_hi\<bar>\<^sup>f >s 2097151 then
            if float_ucmp (\<bar>ymm1w0\<^sub>0\<bar>\<^sup>f *\<^sup>f 4602678819172646912) \<bar>x\<bar>\<^sup>f \<in> {Unordered, LT, EQ} then
              \<bar>x\<bar>\<^sup>f
            else if float_ucmp (\<bar>ymm1w0\<^sub>0\<bar>\<^sup>f *\<^sup>f 4602678819172646912) (\<bar>x\<bar>\<^sup>f -\<^sup>f \<bar>ymm1w0\<^sub>0\<bar>\<^sup>f) \<in> {Unordered, LT} then
              \<bar>x\<bar>\<^sup>f -\<^sup>f \<bar>ymm1w0\<^sub>0\<bar>\<^sup>f
            else
              \<bar>x\<bar>\<^sup>f -\<^sup>f \<bar>ymm1w0\<^sub>0\<bar>\<^sup>f -\<^sup>f \<bar>ymm1w0\<^sub>0\<bar>\<^sup>f
          else
            if float_ucmp \<bar>ymm1w0\<^sub>0\<bar>\<^sup>f (\<bar>x\<bar>\<^sup>f +\<^sup>f \<bar>x\<bar>\<^sup>f) \<in> {Unordered, LT, EQ} then
              \<bar>x\<bar>\<^sup>f
            else if float_ucmp \<bar>ymm1w0\<^sub>0\<bar>\<^sup>f (\<bar>x\<bar>\<^sup>f -\<^sup>f \<bar>ymm1w0\<^sub>0\<bar>\<^sup>f +\<^sup>f (\<bar>x\<bar>\<^sup>f -\<^sup>f \<bar>ymm1w0\<^sub>0\<bar>\<^sup>f)) \<in> {Unordered, LT} then
              \<bar>x\<bar>\<^sup>f -\<^sup>f \<bar>ymm1w0\<^sub>0\<bar>\<^sup>f
            else
              \<bar>x\<bar>\<^sup>f -\<^sup>f \<bar>ymm1w0\<^sub>0\<bar>\<^sup>f -\<^sup>f \<bar>ymm1w0\<^sub>0\<bar>\<^sup>f
          in
              xor_sign x' (msb ymm0w0\<^sub>0)
        else 0\<^sup>+ *\<^sup>f x)
  ]\<close>

schematic_goal pp_\<Theta>_zero[simp]:
  shows \<open>pp_\<Theta> rsp\<^sub>0 ymm0w0\<^sub>0 ymm1w0\<^sub>0 x boffset = ?x\<close>
  unfolding pp_\<Theta>_def
  by simp
schematic_goal pp_\<Theta>_numeral_l[simp]:
  shows \<open>pp_\<Theta> rsp\<^sub>0 ymm0w0\<^sub>0 ymm1w0\<^sub>0 x (n + boffset) = ?x\<close>
  unfolding pp_\<Theta>_def
  by simp
schematic_goal pp_\<Theta>_numeral_r[simp]:
  shows \<open>pp_\<Theta> rsp\<^sub>0 ymm0w0\<^sub>0 ymm1w0\<^sub>0 x (boffset + n) = ?x\<close>
  unfolding pp_\<Theta>_def
  by simp



text \<open>Rewrite rules for xor\_sign\<close>

lemma xor_sign_remove[simp]:
  fixes a :: "'a::len word"
  shows "xor_sign \<bar>a\<bar>\<^sup>f (msb a) = a"
proof-
  {
    fix i ::  nat
    assume "i < LENGTH('a)"
    hence "(xor_sign \<bar>a\<bar>\<^sup>f (msb a)) !! i = a !! i"
      by (auto simp add: xor_sign_def test_bit_set_gen float_abs_def msb_nth word_size)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed

lemma bit_XOR_AND_is_xor_sign_msb[simp]:
  fixes a b :: "32 word"
  shows "a XOR b AND 2147483648 = xor_sign a (msb b)"
  unfolding float_abs_def 
  apply (word_bitwise)
  by (auto simp add: test_bit_set_gen xor_sign_def word_size word_ops_nth_size msb_nth)

lemma bv_cat_is_xor_sign_bit32[simp]:
  fixes a :: "64 word"
  shows "bv_cat (\<langle>31,0\<rangle>xor_sign ((\<langle>63,32\<rangle>a)::32 word) b, 32) ((\<langle>31,0\<rangle>a)::64 word, 32) = (xor_sign a b, 64)"
proof-
  {
    fix i :: nat
    assume "i < 64"
    hence "fst (bv_cat (\<langle>31,0\<rangle>xor_sign ((\<langle>63,32\<rangle>a)::32 word) b, 32) ((\<langle>31,0\<rangle>a)::64 word, 32)) !! i = (xor_sign a b) !! i"
      by (auto simp add: xor_sign_def test_bit_set_gen word_size test_bit_of_take_bits test_bit_of_bv_cat msb_nth)
  }
  thus ?thesis
    apply (cases "bv_cat (\<langle>31,0\<rangle>xor_sign ((\<langle>63,32\<rangle>a)::32 word) b, 32) ((\<langle>31,0\<rangle>a)::64 word, 32)",auto)
    apply (intro word_eqI)
    apply (auto simp add: word_size)
    by (auto simp add: bv_cat.simps) 
qed

lemma bv_cat_is_xor_sign_bit32_v2[simp]:
  fixes a :: "64 word"
  shows "bv_cat (\<langle>31,0\<rangle>xor_sign ((\<langle>63,32\<rangle>\<bar>a\<bar>\<^sup>f)::32 word) b, 32) ((\<langle>31,0\<rangle>a)::64 word, 32) = (xor_sign \<bar>a\<bar>\<^sup>f b, 64)"
proof-
  {
    fix i :: nat
    assume "i < 64"
    hence "fst (bv_cat (\<langle>31,0\<rangle>xor_sign ((\<langle>63,32\<rangle>\<bar>a\<bar>\<^sup>f)::32 word) b, 32) ((\<langle>31,0\<rangle>a)::64 word, 32)) !! i = (xor_sign \<bar>a\<bar>\<^sup>f b) !! i"
      by (auto simp add: xor_sign_def test_bit_set_gen word_size test_bit_of_take_bits test_bit_of_bv_cat msb_nth float_abs_def)
  }
  thus ?thesis
    apply (cases "bv_cat (\<langle>31,0\<rangle>xor_sign ((\<langle>63,32\<rangle>\<bar>a\<bar>\<^sup>f)::32 word) b, 32) ((\<langle>31,0\<rangle>a)::64 word, 32)",auto)
    apply (intro word_eqI)
    apply (auto simp add: word_size)
    by (auto simp add: bv_cat.simps) 
qed


schematic_goal ieee754_fmod[simp]:
  shows "funcs ''__ieee754_fmod'' = ?x"
  apply (subst funcs_def)
  apply (subst ieee_funcs_def)
  by (auto simp add: funcs_def ieee_funcs_def)



lemma rewrite_remainder_label_52:
  assumes "seps blocks"
   and "(9, rsp\<^sub>0 - 48, 8) \<in> blocks"
   and "(10, rsp\<^sub>0 - 56, 8) \<in> blocks"
   and "master blocks (rsp\<^sub>0 - 8, 8) 2"
   and "master blocks (rsp\<^sub>0 - 16, 8) 3"
   and "master blocks (rsp\<^sub>0 - 20, 4) 4"
   and "master blocks (rsp\<^sub>0 - 24, 4) 5"
   and "master blocks (rsp\<^sub>0 - 28, 4) 6"
   and "master blocks (rsp\<^sub>0 - 32, 4) 7"
   and "master blocks (rsp\<^sub>0 - 36, 4) 8"
   and "master blocks (rsp\<^sub>0 - 44, 4) 9"
   and "master blocks (rsp\<^sub>0 - 48, 4) 9"
   and "master blocks (rsp\<^sub>0 - 48, 8) 9"
   and "master blocks (rsp\<^sub>0 - 52, 4) 10"
   and "master blocks (rsp\<^sub>0 - 56, 4) 10"
   and "master blocks (rsp\<^sub>0 - 56, 8) 10"
   and "master blocks (rsp\<^sub>0 - 64, 8) 11"
   and "master blocks (boffset + 1857, 8) 0"
   and "master blocks (boffset + 1873, 8) 1"
   and "72 \<le> rsp\<^sub>0"
      and "get_rip \<sigma> = boffset + 1413"
      and "\<sigma> \<turnstile> *[rsp\<^sub>0 - 20,4] = \<langle>63,32\<rangle>ymm0w0\<^sub>0 AND (2147483648 :: 32 word)"
      and "\<sigma> \<turnstile> *[rsp\<^sub>0 - 24,4] = ((\<langle>31,0\<rangle>ymm1w0\<^sub>0) :: 32 word)"
      and "\<sigma> \<turnstile> *[rsp\<^sub>0 - 28,4] = (\<bar>\<langle>63,32\<rangle>ymm1w0\<^sub>0\<bar>\<^sup>f::32 word)"
      and "\<sigma> \<turnstile> *[rsp\<^sub>0 - 32,4] = ((\<langle>31,0\<rangle>ymm0w0\<^sub>0) :: 32 word)"
      and "\<sigma> \<turnstile> *[rsp\<^sub>0 - 36,4] = (\<bar>\<langle>63,32\<rangle>ymm0w0\<^sub>0\<bar>\<^sup>f::32 word)"
      and "\<sigma> \<turnstile> *[rsp\<^sub>0 - 48,8] = x"
      and "\<sigma> \<turnstile> *[rsp\<^sub>0 - 56,8] = ymm1w0\<^sub>0"
      and "\<sigma> \<turnstile> *[boffset + 1857,8] = (9223372036854775807::64 word)"
      and "\<sigma> \<turnstile> *[boffset + 1873,8] = (4602678819172646912::64 word)"
      and "regs \<sigma> rbp = rsp\<^sub>0 - 8"
      and "ymm1w0\<^sub>0 \<notin> {0\<^sup>-, 0\<^sup>+}"
      and "\<not> \<bar>\<langle>63,32\<rangle>ymm0w0\<^sub>0\<bar>\<^sup>f >s (2146435071::32 word)"
      and "\<bar>\<langle>63,32\<rangle>ymm1w0\<^sub>0\<bar>\<^sup>f \<le>s (2146435071::32 word) \<or> (\<bar>\<langle>63,32\<rangle>ymm1w0\<^sub>0\<bar>\<^sup>f + 2148532224 = (0::32 word) \<and> \<langle>31,0\<rangle>ymm1w0\<^sub>0 = (0::32 word))"
    shows "wps step (\<lambda>_. floyd.invar (pp_\<Theta> rsp\<^sub>0 ymm0w0\<^sub>0 ymm1w0\<^sub>0 x)) \<sigma>"
proof-
  note masters = assms(4-19)
  note 1 = word_sub_le[OF order_trans[OF _ assms(20)]]
  note 2 = order_trans[OF _ assms(20)]

  show ?thesis
    apply (insert assms(1-3,20-31) 1 2)
    (* .label_52: *)
    subgoal premises prems
      apply (insert prems)    
      apply (symbolic_execution masters: masters) (* mov	eax, dword ptr [rbp - 0x1c] *)
      apply (symbolic_execution masters: masters) (* sub	eax, dword ptr [rbp - 0x14]  *)
      apply (symbolic_execution masters: masters) (* mov	edx, eax *)
      apply (symbolic_execution masters: masters) (* mov	eax, dword ptr [rbp - 0x18] *)
      apply (symbolic_execution masters: masters) (* sub	eax, dword ptr [rbp - 0x10] *)
      apply (symbolic_execution masters: masters) (* or 	eax, edx *)
      apply (symbolic_execution masters: masters) (* test	eax, eax *)
      apply (symbolic_execution masters: masters) (* jne	.label_56 *)

    (* .label_56: *)
    subgoal premises prems
      apply (insert prems)
      apply (symbolic_execution masters: masters) (* movsd	xmm1, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0,  qword ptr [word ptr [rip + label_61]] *)
      apply (symbolic_execution masters: masters) (* andpd	xmm1, xmm0 *)
      apply (symbolic_execution masters: masters) (* movq	rax, xmm1 *)
      apply (symbolic_execution masters: masters) (* mov	qword ptr [rbp - 0x28], rax *)
      apply (symbolic_execution masters: masters) (* movsd	xmm1, qword ptr [rbp - 0x30] *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0,  qword ptr [word ptr [rip + label_61]] *)
      apply (symbolic_execution masters: masters) (* andpd	xmm1, xmm0 *)
      apply (symbolic_execution masters: masters) (* movq	rax, xmm1 *)
      apply (symbolic_execution masters: masters) (* mov	qword ptr [rbp - 0x30], rax *)
      apply (symbolic_execution masters: masters) (* cmp	dword ptr [rbp - 0x14], 0x1fffff *)
      apply (symbolic_execution masters: masters) (* jg	.label_62 *)

    (* .label_62: *)
    subgoal premises prems
      apply (insert prems)
      apply (symbolic_execution masters: masters) (* movsd	xmm1, qword ptr [rbp - 0x30] *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [word ptr [rip + label_63]] *) 
      apply (symbolic_execution masters: masters) (* mulsd	xmm1, xmm0 *)
      apply (symbolic_execution masters: masters) (* movq	rax, xmm1 *)
      apply (symbolic_execution masters: masters) (* mov	qword ptr [rbp - 8], rax *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* ucomisd	xmm0, qword ptr [rbp - 8] *)
      apply (symbolic_execution masters: masters) (* jbe	.label_55 *)

    (* .label_55: *)
    subgoal premises prems
      apply (insert prems)
      apply (symbolic_execution masters: masters) (* lea	rax, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* add	rax, 4 *)
      apply (symbolic_execution masters: masters) (* lea	rdx, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* add	rdx, 4 *)
      apply (symbolic_execution masters: masters) (* mov	edx, dword ptr [rdx] *)
      apply (symbolic_execution masters: masters) (* xor	edx, dword ptr [rbp - 0xc] *)
      apply (symbolic_execution masters: masters add: master_blocks_implies_sep) (* mov	dword ptr [rax], edx *)
      apply (symbolic_execution masters: masters) (* mov	rax, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* mov	qword ptr [rbp - 0x38], rax *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x38] *)
      apply (symbolic_execution masters: masters del: pp_\<Theta>_numeral_l pp_\<Theta>_numeral_r) (* leave *)
      apply (subst pp_\<Theta>_numeral_l pp_\<Theta>_numeral_r)
      apply (insert assms(31-))
      by (auto simp add: Let_def signed_le_def signed_greater_than_def msb_nth simp del: signed_le_def[symmetric] signed_greater_than_def[symmetric])

    (* continue after jbe	.label_55 *)
    subgoal premises prems
      apply (insert prems)
      apply (restart_symbolic_execution)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* movsd	xmm1, qword ptr [rbp - 0x30] *)
      apply (symbolic_execution masters: masters) (* subsd	xmm0, xmm1 *)
      apply (symbolic_execution masters: masters) (* movq	rax, xmm0 *)
      apply (symbolic_execution masters: masters) (* mov	qword ptr [rbp - 0x28], rax *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* ucomisd	xmm0, qword ptr [rbp - 8] *)
      apply (symbolic_execution masters: masters) (* jb	.label_55 *)

    (* .label_55: *)
    subgoal premises prems
      apply (insert prems)
      apply (symbolic_execution masters: masters) (* lea	rax, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* add	rax, 4 *)
      apply (symbolic_execution masters: masters) (* lea	rdx, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* add	rdx, 4 *)
      apply (symbolic_execution masters: masters) (* mov	edx, dword ptr [rdx] *)
      apply (symbolic_execution masters: masters) (* xor	edx, dword ptr [rbp - 0xc] *)
      apply (symbolic_execution masters: masters add: master_blocks_implies_sep) (* mov	dword ptr [rax], edx *)
      apply (symbolic_execution masters: masters) (* mov	rax, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* mov	qword ptr [rbp - 0x38], rax *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x38] *)
      apply (symbolic_execution masters: masters del: pp_\<Theta>_numeral_l pp_\<Theta>_numeral_r) (* leave *)
      apply (subst pp_\<Theta>_numeral_l pp_\<Theta>_numeral_r)
      apply (insert assms(31-))
      by (auto simp add: Let_def signed_le_def signed_greater_than_def msb_nth simp del: signed_le_def[symmetric] signed_greater_than_def[symmetric])

    (* continue after jb	.label_55 *)
    subgoal premises prems
      apply (insert prems)
      apply (restart_symbolic_execution)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* movsd	xmm1, qword ptr [rbp - 0x30] *)
      apply (symbolic_execution masters: masters) (* subsd	xmm0, xmm1 *)
      apply (symbolic_execution masters: masters) (* movq	rax, xmm0 *)
      apply (symbolic_execution masters: masters) (* mov	qword ptr [rbp - 0x28], rax *)
      apply (symbolic_execution masters: masters) (* lea	rax, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* add	rax, 4 *)
      apply (symbolic_execution masters: masters) (* lea	rdx, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* add	rdx, 4 *)
      apply (symbolic_execution masters: masters) (* mov	edx, dword ptr [rdx] *)
      apply (symbolic_execution masters: masters) (* xor	edx, dword ptr [rbp - 0xc] *)
      apply (symbolic_execution masters: masters add: master_blocks_implies_sep) (* mov	dword ptr [rax], edx *)
      apply (symbolic_execution masters: masters) (* mov	rax, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* mov	qword ptr [rbp - 0x38], rax *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x38] *)
      apply (symbolic_execution masters: masters del: pp_\<Theta>_numeral_l pp_\<Theta>_numeral_r) (* leave *)
      apply (subst pp_\<Theta>_numeral_l pp_\<Theta>_numeral_r)
      apply (insert assms(32-))
      by (auto simp add: Let_def signed_le_def signed_greater_than_def msb_nth simp del: signed_le_def[symmetric] signed_greater_than_def[symmetric])
    done
    done

    (* continue after jg .label_62 *)
    subgoal premises prems
      apply (insert prems)
      apply (restart_symbolic_execution)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* addsd	xmm0, xmm0 *)
      apply (symbolic_execution masters: masters) (* movsd	xmm1, qword ptr [rbp - 0x30] *)
      apply (symbolic_execution masters: masters) (* ucomisd	xmm0, xmm1 *)
      apply (symbolic_execution masters: masters) (* ja	.label_54 *)


    (* .label_54: *)
    subgoal premises prems
      apply (insert prems)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* movsd	xmm1, qword ptr [rbp - 0x30] *)
      apply (symbolic_execution masters: masters) (* subsd	xmm0, xmm1 *)
      apply (symbolic_execution masters: masters) (* movq	rax, xmm0 *)
      apply (symbolic_execution masters: masters) (* mov	qword ptr [rbp - 0x28], rax *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* addsd	xmm0, xmm0 *)
      apply (symbolic_execution masters: masters) (* movsd	xmm1, qword ptr [rbp - 0x30] *)
      apply (symbolic_execution masters: masters) (* ucomisd	xmm0, xmm1  *)
      apply (symbolic_execution masters: masters) (* jae	.label_57 *)

    (* .label_57: *)
    subgoal premises prems
      apply (insert prems)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* movsd	xmm1, qword ptr [rbp - 0x30] *)
      apply (symbolic_execution masters: masters) (* subsd	xmm0, xmm1 *)
      apply (symbolic_execution masters: masters) (* movq	rax, xmm0 *)
      apply (symbolic_execution masters: masters) (* mov	qword ptr [rbp - 0x28], rax *)
      apply (symbolic_execution masters: masters) (* jmp	.label_55 *)
      apply (symbolic_execution masters: masters) (* lea	rax, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* add	rax, 4 *)
      apply (symbolic_execution masters: masters) (* lea	rdx, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* add	rdx, 4 *)
      apply (symbolic_execution masters: masters) (* mov	edx, dword ptr [rdx] *)
      apply (symbolic_execution masters: masters) (* xor	edx, dword ptr [rbp - 0xc] *)
      apply (symbolic_execution masters: masters add: master_blocks_implies_sep) (* mov	dword ptr [rax], edx *)
      apply (symbolic_execution masters: masters) (* mov	rax, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* mov	qword ptr [rbp - 0x38], rax *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x38] *)
      apply (symbolic_execution masters: masters del: pp_\<Theta>_numeral_l pp_\<Theta>_numeral_r) (* leave *)
      apply (subst pp_\<Theta>_numeral_l pp_\<Theta>_numeral_r)
      apply (insert assms(32-))
      by (auto simp add: Let_def signed_le_def signed_greater_than_def msb_nth simp del: signed_le_def[symmetric] signed_greater_than_def[symmetric])

    (* continue after jae	.label_57 *)
    subgoal premises prems
      apply (insert prems)
      apply (restart_symbolic_execution)
      apply (symbolic_execution masters: masters) (* jmp	.label_55 *)
      apply (symbolic_execution masters: masters) (* lea	rax, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* add	rax, 4 *)
      apply (symbolic_execution masters: masters) (* lea	rdx, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* add	rdx, 4 *)
      apply (symbolic_execution masters: masters) (* mov	edx, dword ptr [rdx] *)
      apply (symbolic_execution masters: masters) (* xor	edx, dword ptr [rbp - 0xc] *)
      apply (symbolic_execution masters: masters add: master_blocks_implies_sep) (* mov	dword ptr [rax], edx *)
      apply (symbolic_execution masters: masters) (* mov	rax, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* mov	qword ptr [rbp - 0x38], rax *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x38] *)
      apply (symbolic_execution masters: masters del: pp_\<Theta>_numeral_l pp_\<Theta>_numeral_r) (* leave *)
      apply (subst pp_\<Theta>_numeral_l pp_\<Theta>_numeral_r)
      apply (insert assms(32-))
      by (auto simp add: Let_def signed_le_def signed_greater_than_def msb_nth simp del: signed_le_def[symmetric] signed_greater_than_def[symmetric])
    done

    (* continue after ja	.label_54 *)
    subgoal premises prems
      apply (insert prems)
      apply (restart_symbolic_execution)
      apply (symbolic_execution masters: masters) (* jmp	.label_55 *)
      apply (symbolic_execution masters: masters) (* lea	rax, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* add	rax, 4 *)
      apply (symbolic_execution masters: masters) (* lea	rdx, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* add	rdx, 4 *)
      apply (symbolic_execution masters: masters) (* mov	edx, dword ptr [rdx] *)
      apply (symbolic_execution masters: masters) (* xor	edx, dword ptr [rbp - 0xc] *)
      apply (symbolic_execution masters: masters add: master_blocks_implies_sep) (* mov	dword ptr [rax], edx *)
      apply (symbolic_execution masters: masters) (* mov	rax, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* mov	qword ptr [rbp - 0x38], rax *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x38] *)
      apply (symbolic_execution masters: masters del: pp_\<Theta>_numeral_l pp_\<Theta>_numeral_r) (* leave *)
      apply (subst pp_\<Theta>_numeral_l pp_\<Theta>_numeral_r)
      apply (insert assms(32-))
      by (auto simp add: Let_def signed_le_def signed_greater_than_def msb_nth simp del: signed_le_def[symmetric] signed_greater_than_def[symmetric])
    done
    done

    (* continue after jne	.label_56 *)
    subgoal premises prems
      apply (insert prems)
      apply (restart_symbolic_execution)
      apply (symbolic_execution masters: masters) (* pxor	xmm1, xmm1 *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* mulsd	xmm1, xmm0 *) 
      apply (symbolic_execution masters: masters) (* movq	rax, xmm1 *)
      apply (symbolic_execution masters: masters) (* jmp	.label_53 *)
      apply (symbolic_execution masters: masters) (* mov	qword ptr [rbp - 0x38], rax *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x38] *)
      apply (symbolic_execution masters: masters del: pp_\<Theta>_numeral_l pp_\<Theta>_numeral_r) (* leave *)
      apply (subst pp_\<Theta>_numeral_l pp_\<Theta>_numeral_r)
      apply (insert assms(32-))
      by (auto simp add: Let_def signed_le_def signed_greater_than_def msb_nth simp del: signed_le_def[symmetric] signed_greater_than_def[symmetric])
    done
  done
qed







lemma rewrite_remainder_label_60:
  assumes "seps blocks"
   and "(9, rsp\<^sub>0 - 48, 8) \<in> blocks"
   and "(10, rsp\<^sub>0 - 56, 8) \<in> blocks"
   and "master blocks (rsp\<^sub>0 - 8, 8) 2"
   and "master blocks (rsp\<^sub>0 - 16, 8) 3"
   and "master blocks (rsp\<^sub>0 - 20, 4) 4"
   and "master blocks (rsp\<^sub>0 - 24, 4) 5"
   and "master blocks (rsp\<^sub>0 - 28, 4) 6"
   and "master blocks (rsp\<^sub>0 - 32, 4) 7"
   and "master blocks (rsp\<^sub>0 - 36, 4) 8"
   and "master blocks (rsp\<^sub>0 - 44, 4) 9"
   and "master blocks (rsp\<^sub>0 - 48, 4) 9"
   and "master blocks (rsp\<^sub>0 - 48, 8) 9"
   and "master blocks (rsp\<^sub>0 - 52, 4) 10"
   and "master blocks (rsp\<^sub>0 - 56, 4) 10"
   and "master blocks (rsp\<^sub>0 - 56, 8) 10"
   and "master blocks (rsp\<^sub>0 - 64, 8) 11"
   and "master blocks (boffset + 1857, 8) 0"
   and "master blocks (boffset + 1873, 8) 1"
   and "72 \<le> rsp\<^sub>0"
      and "get_rip \<sigma> = boffset + 1364"
      and "\<sigma> \<turnstile> *[rsp\<^sub>0 - 20,4] = \<langle>63,32\<rangle>ymm0w0\<^sub>0 AND (2147483648 :: 32 word)"
      and "\<sigma> \<turnstile> *[rsp\<^sub>0 - 24,4] = ((\<langle>31,0\<rangle>ymm1w0\<^sub>0) :: 32 word)"
      and "\<sigma> \<turnstile> *[rsp\<^sub>0 - 28,4] = (\<bar>\<langle>63,32\<rangle>ymm1w0\<^sub>0\<bar>\<^sup>f::32 word)"
      and "\<sigma> \<turnstile> *[rsp\<^sub>0 - 32,4] = ((\<langle>31,0\<rangle>ymm0w0\<^sub>0) :: 32 word)"
      and "\<sigma> \<turnstile> *[rsp\<^sub>0 - 36,4] = (\<bar>\<langle>63,32\<rangle>ymm0w0\<^sub>0\<bar>\<^sup>f::32 word)"
      and "\<sigma> \<turnstile> *[rsp\<^sub>0 - 48,8] = ymm0w0\<^sub>0"
      and "\<sigma> \<turnstile> *[rsp\<^sub>0 - 56,8] = ymm1w0\<^sub>0"
      and "\<sigma> \<turnstile> *[boffset + 1857,8] = (9223372036854775807::64 word)"
      and "\<sigma> \<turnstile> *[boffset + 1873,8] = (4602678819172646912::64 word)"
      and "regs \<sigma> rbp = rsp\<^sub>0 - 8"
      and "ymm1w0\<^sub>0 \<notin> {0\<^sup>-, 0\<^sup>+}"
      and "\<not> \<bar>\<langle>63,32\<rangle>ymm0w0\<^sub>0\<bar>\<^sup>f >s (2146435071::32 word)"
      and "\<bar>\<langle>63,32\<rangle>ymm1w0\<^sub>0\<bar>\<^sup>f \<le>s (2146435071::32 word) \<or> (\<bar>\<langle>63,32\<rangle>ymm1w0\<^sub>0\<bar>\<^sup>f + 2148532224 = (0::32 word) \<and> \<langle>31,0\<rangle>ymm1w0\<^sub>0 = (0::32 word))"
      and "x = (if \<bar>\<langle>63,32\<rangle>ymm1w0\<^sub>0\<bar>\<^sup>f >s (2145386495::32 word) then ymm0w0\<^sub>0 else ymm0w0\<^sub>0 mod\<^sup>f (ymm1w0\<^sub>0 +\<^sup>f ymm1w0\<^sub>0))"
    shows "wps step (\<lambda>_. floyd.invar (pp_\<Theta> rsp\<^sub>0 ymm0w0\<^sub>0 ymm1w0\<^sub>0 x)) \<sigma>"
proof-
  note masters = assms(4-19)
  note 1 = word_sub_le[OF order_trans[OF _ assms(20)]]
  note 2 = order_trans[OF _ assms(20)]

  show ?thesis
    apply (insert assms(1-3,20-34) 1 2)
    (* .label_60: *)
    subgoal premises prems
      apply (insert prems)
      apply (symbolic_execution masters: masters) (* cmp	dword ptr [rbp - 0x14], 0x7fefffff *)
      apply (symbolic_execution masters: masters) (* jg	.label_52 *)

    (* .label_52: *)
    subgoal premises prems
      apply (insert prems)
      apply (insert masters assms(35))
      apply (rule rewrite_remainder_label_52[OF assms(1-20)])
      by (auto)
    (* continue after jg	.label_52 *)
    subgoal premises prems
      apply (insert prems)
      apply (restart_symbolic_execution)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x30] *)
      apply (symbolic_execution masters: masters) (* addsd	xmm0, xmm0 *)
      apply (symbolic_execution masters: masters) (* mov	rax, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* movapd	xmm1, xmm0 *)
      apply (symbolic_execution masters: masters) (* mov	qword ptr [rbp - 0x38], rax  *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x38]  *)
      apply (symbolic_execution masters: masters) (* call	__ieee754_fmod *)
      apply (symbolic_execution masters: masters) (* movq	rax, xmm0 *)
      apply (symbolic_execution masters: masters) (* mov	qword ptr [rbp - 0x28], rax *)
      apply (rule rewrite_remainder_label_52[OF assms(1-20)])
      apply (insert masters assms(35))
      apply simp
      apply simp
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply simp
      apply simp
      done
    done
  done
qed

lemma rewrite_remainder:
  assumes "seps blocks"
   and "(9, rsp\<^sub>0 - 48, 8) \<in> blocks"
   and "(10, rsp\<^sub>0 - 56, 8) \<in> blocks"
   and "master blocks (rsp\<^sub>0 - 8, 8) 2"
   and "master blocks (rsp\<^sub>0 - 16, 8) 3"
   and "master blocks (rsp\<^sub>0 - 20, 4) 4"
   and "master blocks (rsp\<^sub>0 - 24, 4) 5"
   and "master blocks (rsp\<^sub>0 - 28, 4) 6"
   and "master blocks (rsp\<^sub>0 - 32, 4) 7"
   and "master blocks (rsp\<^sub>0 - 36, 4) 8"
   and "master blocks (rsp\<^sub>0 - 44, 4) 9"
   and "master blocks (rsp\<^sub>0 - 48, 4) 9"
   and "master blocks (rsp\<^sub>0 - 48, 8) 9"
   and "master blocks (rsp\<^sub>0 - 52, 4) 10"
   and "master blocks (rsp\<^sub>0 - 56, 4) 10"
   and "master blocks (rsp\<^sub>0 - 56, 8) 10"
   and "master blocks (rsp\<^sub>0 - 64, 8) 11"
   and "master blocks (boffset + 1857, 8) 0"
   and "master blocks (boffset + 1873, 8) 1"
   and "72 \<le> rsp\<^sub>0"
      and "x = (if \<bar>\<langle>63,32\<rangle>ymm1w0\<^sub>0\<bar>\<^sup>f >s (2145386495::32 word) then ymm0w0\<^sub>0 else ymm0w0\<^sub>0 mod\<^sup>f (ymm1w0\<^sub>0 +\<^sup>f ymm1w0\<^sub>0))"
    shows "is_std_invar (floyd.invar (pp_\<Theta> rsp\<^sub>0 ymm0w0\<^sub>0 ymm1w0\<^sub>0 x))"
proof-
  note masters = assms(4-19)
 
  note 1 = word_sub_le[OF order_trans[OF _ assms(20)]]
  note 2 = order_trans[OF _ assms(20)]

  {
    fix w :: "64 word"
    have 1: "\<bar>(\<langle>63,32\<rangle>w)::32 word\<bar>\<^sup>f = (\<langle>63,32\<rangle>w AND (2147483647::32 word))"
      by (auto simp add: float_abs_def)
    have "(\<bar>(\<langle>63,32\<rangle>w)::32 word\<bar>\<^sup>f = 0 \<and> ((\<langle>31,0\<rangle>w)::32 word) = 0) \<longleftrightarrow> (w \<in> {0\<^sup>-, 0\<^sup>+})"
      apply (subst 1)
      apply word_bitwise
      apply (auto simp add: test_bit_of_take_bits plus_zero_def minus_zero_def)
      apply word_bitwise
      by (auto simp add: numeral_2_eq_2)[1]
  }
  note bit_pattern_for_float_zero = this

  show ?thesis
    (* Boilerplate code from Peter to start the VCG *)
    apply (rule floyd_invarI)
    apply (rewrite at \<open>floyd_vcs \<hole> _\<close> pp_\<Theta>_def)
    apply (intro floyd_vcsI; clarsimp?)

    subgoal premises prems for \<sigma>
      thm prems
      apply (insert prems(2-4)[symmetric] assms(1-3,20) prems(1,5-) 1 2)
      (* Then, unfold instructions *)
      apply (symbolic_execution masters: masters) (* push rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00 *)
      apply (symbolic_execution masters: masters) (* mov	rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00 *)
      apply (symbolic_execution masters: masters) (* sub	rsp, 0x40 # Size:4, Opcode: 0x83,0x00,0x00,0x00 *)
      apply (symbolic_execution masters: masters) (* movsd	qword ptr [rbp - 0x28], xmm0 # Size:5, Opcode: 0x0f,0x11,0x00,0x00 *)
      apply (symbolic_execution masters: masters) (* movsd	qword ptr [rbp - 0x30], xmm1 # Size:5, Opcode: 0x0f,0x11,0x00,0x00 *)
      apply (symbolic_execution masters: masters) (* mov	eax, dword ptr [rbp - 0x24] *)
      apply (symbolic_execution masters: masters) (* mov	dword ptr [rbp - 0x1c], eax *)
      apply (symbolic_execution masters: masters) (* lea	rax, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* mov	eax, dword ptr [rax] *)
      apply (symbolic_execution masters: masters) (* mov	dword ptr [rbp - 0x18], eax *)
      apply (symbolic_execution masters: masters) (* mov	eax, dword ptr [rbp - 0x2c] *)
      apply (symbolic_execution masters: masters) (* mov	dword ptr [rbp - 0x14], eax *)
      apply (symbolic_execution masters: masters) (* lea	rax, qword ptr [rbp - 0x30] # Size:4, Opcode: 0x8d,0x00,0x00,0x00 *) 
      apply (symbolic_execution masters: masters) (* mov	eax, dword ptr [rax] # Size:2, Opcode: 0x8b,0x00,0x00,0x00 *)
      apply (symbolic_execution masters: masters) (* mov	dword ptr [rbp - 0x10], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00 *)
      apply (symbolic_execution masters: masters) (* mov	eax, dword ptr [rbp - 0x1c] *)
      apply (symbolic_execution masters: masters) (* and	eax, 0x80000000 # Size:5, Opcode: 0x25,0x00,0x00,0x00 *)
      apply (symbolic_execution masters: masters) (* mov	dword ptr [rbp - 0xc], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00 *)
      apply (symbolic_execution masters: masters) (* and	dword ptr [rbp - 0x14], 0x7fffffff # Size:7, Opcode: 0x81,0x00,0x00,0x00 *)
      apply (symbolic_execution masters: masters) (* and	dword ptr [rbp - 0x1c], 0x7fffffff # Size:7, Opcode: 0x81,0x00,0x00,0x00 *)
      apply (symbolic_execution masters: masters) (* mov	eax, dword ptr [rbp - 0x14] *)
      apply (symbolic_execution masters: masters) (* or	eax, dword ptr [rbp - 0x10] *)
      apply (symbolic_execution masters: masters) (* test	eax, eax *)
      apply (subst bit_pattern_for_float_zero)
      apply (symbolic_execution masters: masters) (* jne	.label_59 *)

    (* .label_59 *)
    subgoal premises prems
      apply (insert prems)
      apply (symbolic_execution masters: masters) (* cmp	dword ptr [rbp - 0x1c], 0x7fefffff *)
      apply (symbolic_execution masters: masters) (* jg	.label_58 *)

    (* .label_58 *)
    subgoal premises prems
      apply (insert prems)
      apply (symbolic_execution masters: masters) (* movsd	xmm1, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x30] *)
      apply (symbolic_execution masters: masters) (* mulsd	xmm0, xmm1 *)
      apply (symbolic_execution masters: masters) (* movsd	xmm2, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* movsd	xmm1, qword ptr [rbp - 0x30] *)
      apply (symbolic_execution masters: masters) (* mulsd	xmm1, xmm2 *)
      apply (symbolic_execution masters: masters) (* divsd	xmm0, xmm1 *)
      apply (symbolic_execution masters: masters) (* movq	rax, xmm0 *)
      apply (symbolic_execution masters: masters) (* jmp	.label_53 *)
      apply (symbolic_execution masters: masters) (* mov	qword ptr [rbp - 0x38], rax *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x38]  *)
      apply (symbolic_execution masters: masters) (* leave *)
      done

    (* continue after jg	.label_58 *)
    subgoal premises prems
      apply (insert prems)
      apply (restart_symbolic_execution)
      apply (symbolic_execution masters: masters) (* cmp	dword ptr [rbp - 0x14], 0x7fefffff *)
      apply (symbolic_execution masters: masters) (* jle	.label_60 *)

    (* .label_60: *)
    subgoal premises prems
      apply (insert prems)
      apply (insert masters assms(21))
      apply (rule rewrite_remainder_label_60[OF assms(1-20)])
      apply auto[1]
      apply auto[1]
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, ((rewrite_one_let')+,(simp add: simp_rules)?)?)
      apply ((simp add: simp_rules)?, ((rewrite_one_let')+,(simp add: simp_rules)?)?)
      apply ((simp add: simp_rules)?, ((rewrite_one_let')+,simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, ((rewrite_one_let')+,simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, ((rewrite_one_let')+,simp add: simp_rules)?)
      done

    (* continue after jle	.label_60 *)
    subgoal premises prems
      apply (insert prems)
      apply (restart_symbolic_execution)
      apply (symbolic_execution masters: masters) (* mov	eax, dword ptr [rbp - 0x14]  *)
      apply (symbolic_execution masters: masters) (* sub	eax, 0x7ff00000 *)
      apply (symbolic_execution masters: masters) (* or	eax, dword ptr [rbp - 0x10] *)
      apply (symbolic_execution masters: masters) (* test	eax, eax *)
      apply (symbolic_execution masters: masters) (* je	.label_60 *)

    (* .label_60: *)
    subgoal premises prems
      apply (insert prems)
      apply (insert masters assms(21))
      apply (rule rewrite_remainder_label_60[OF assms(1-20)])
      apply auto[1]
      apply auto[1]
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, (rewrite_one_let')+,(simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, ((rewrite_one_let')+,(simp add: simp_rules)?)?)
      apply ((simp add: simp_rules)?, ((rewrite_one_let')+,(simp add: simp_rules)?)?)
      apply ((simp add: simp_rules)?, ((rewrite_one_let')+,simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, ((rewrite_one_let')+,simp add: simp_rules)?)
      apply ((simp add: simp_rules)?, ((rewrite_one_let')+,simp add: simp_rules)?)
      done

    (* continue after je	.label_60 *)
    (* .label_58 *)
    subgoal premises prems
      apply (insert prems)
      apply (restart_symbolic_execution)
      apply (symbolic_execution masters: masters) (* movsd	xmm1, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x30] *)
      apply (symbolic_execution masters: masters) (* mulsd	xmm0, xmm1 *)
      apply (symbolic_execution masters: masters) (* movsd	xmm2, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* movsd	xmm1, qword ptr [rbp - 0x30] *)
      apply (symbolic_execution masters: masters) (* mulsd	xmm1, xmm2 *)
      apply (symbolic_execution masters: masters) (* divsd	xmm0, xmm1 *)
      apply (symbolic_execution masters: masters) (* movq	rax, xmm0 *)
      apply (symbolic_execution masters: masters) (* jmp	.label_53 *)
      apply (symbolic_execution masters: masters) (* mov	qword ptr [rbp - 0x38], rax *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x38]  *)
      apply (symbolic_execution masters: masters) (* leave *)
      done
    done
    done
    done

    (* continue after jne	.label_59 *)
    subgoal premises prems
      apply (insert prems)
      apply (restart_symbolic_execution)
      apply (symbolic_execution masters: masters) (* movsd	xmm1, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x30] *)
      apply (symbolic_execution masters: masters) (* mulsd	xmm0, xmm1 *)
      apply (symbolic_execution masters: masters) (* movsd	xmm2, qword ptr [rbp - 0x28] *)
      apply (symbolic_execution masters: masters) (* movsd	xmm1, qword ptr [rbp - 0x30] *)
      apply (symbolic_execution masters: masters) (* mulsd	xmm1, xmm2 *)
      apply (symbolic_execution masters: masters) (* divsd	xmm0, xmm1 *)
      apply (symbolic_execution masters: masters) (* movq	rax, xmm0 *)
      apply (symbolic_execution masters: masters) (* jmp	.label_53 *)
      apply (symbolic_execution masters: masters) (* mov	qword ptr [rbp - 0x38], rax *)
      apply (symbolic_execution masters: masters) (* movsd	xmm0, qword ptr [rbp - 0x38]  *)
      apply (symbolic_execution masters: masters) (* leave *)
      apply (auto)
      done
    done
  done
qed

thm rewrite_remainder
