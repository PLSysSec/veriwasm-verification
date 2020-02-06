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

theory Chum_Rewriting
  imports
      Memory_Rewriting
      Chum_Execution
      BitVector_Rewriting
begin

context execution_context
begin


lemmas sub_overflow_flag_simps[simp] = 
  sub_overflow_flag_def[of 0 0]
  sub_overflow_flag_def[of 0 1]
  sub_overflow_flag_def[of 0 "numeral m"]
  sub_overflow_flag_def[of 1 0]
  sub_overflow_flag_def[of 1 1]
  sub_overflow_flag_def[of 1 "numeral m"]
  sub_overflow_flag_def[of "numeral n" 0]
  sub_overflow_flag_def[of "numeral n" 1]
  sub_overflow_flag_def[of "numeral n" "numeral m"]
  for n m

lemmas sub_sign_flag_simps[simp] =
  sub_sign_flag_def[of 0 0]
  sub_sign_flag_def[of 0 1]
  sub_sign_flag_def[of 0 "numeral m"]
  sub_sign_flag_def[of 1 0]
  sub_sign_flag_def[of 1 1]
  sub_sign_flag_def[of 1 "numeral m"]
  sub_sign_flag_def[of "numeral n" 0]
  sub_sign_flag_def[of "numeral n" 1]
  sub_sign_flag_def[of "numeral n" "numeral m"]
  for n m



lemma sub_sign_flag_eq_sub_overflow_flag[simp]:
  shows "sub_sign_flag a b = sub_overflow_flag a b \<longleftrightarrow> \<not>(a <s b)"
  unfolding sub_overflow_flag_def sub_sign_flag_def
  by auto


lemma bytes_of_3_0_bit64[simp]: (* TODO: generalize *)
  fixes a :: "64 word"
  shows "\<lbrace>3,0\<rbrace>\<bar>a\<bar>\<^sup>f = \<lbrace>3,0\<rbrace>a"
proof-
  {
    fix i :: nat
    assume i: "i < 4"
    have "(\<lbrace>3,0\<rbrace>\<bar>a\<bar>\<^sup>f) ! i = (\<lbrace>3,0\<rbrace>a) ! i"
    proof-
      {
        fix j :: nat
        assume "j < 8"
        hence "(\<lbrace>3,0\<rbrace>\<bar>a\<bar>\<^sup>f) ! i !! j = (\<lbrace>3,0\<rbrace>a) ! i !! j"
          using i
          by (auto simp add: nth_bytes_of test_bit_of_take_bits float_abs_def test_bit_set_gen word_size)
      }
      thus ?thesis
        apply (intro word_eqI)
        by (auto simp add: word_size)
    qed
  }
  thus ?thesis
    apply (intro nth_equalityI)
    by (auto)
qed


lemma ucast_bitNOT:
  fixes a :: "'a ::len word"
assumes "LENGTH('b) = LENGTH('a) + 1"
  shows "((ucast (NOT a))::'b::len word) = NOT (2 ^ LENGTH('a) + ucast a)"
proof-
  have "uint a < 2^LENGTH('a)"
    by (auto)
  hence 0: "(2 ^ LENGTH('a) + ucast a :: 'b word) \<ge> 2 ^ LENGTH('a)"
    using assms
    apply uint_arith
    apply (auto simp add: is_up uint_up_ucast)
    apply (subst (asm) uint_2p)
    by (simp add: zero_le_2p)+
  {

    fix i :: nat
    assume i: "i < LENGTH('b)"
    have "(2 ^ LENGTH('a) + ucast a :: 'b word) !! LENGTH('a)"
      using 0 msb_is_gt_2p[unfolded msb_nth,where 'a='b] assms
      by auto
    moreover
    have "i < LENGTH('a) \<Longrightarrow> ((2 ^ LENGTH('a) + ucast a)::'b word) !! i = a !! i"
      using assms
      apply (subst test_bit_of_add_2p)
      by (auto simp add: nth_ucast)
    ultimately
    have "((ucast (NOT a))::'b word) !! i = (NOT (2 ^ LENGTH('a) + ucast a :: 'b word)) !! i"
      using assms
      by (cases "i = LENGTH('a)",auto simp add: bitNOT_nth word_size nth_ucast)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed

lemma bitNOT_plus[simp]:
  fixes a b :: "'a::len0 word"
  shows "NOT (a + b) = - a - b - 1"
proof-
  {
    fix a :: "'a::len0 word"
    have "NOT a = - a - 1"
      using twos_complement[of a]
      by (auto simp add: word_succ_p1)
  }
  thus ?thesis
    by simp
qed



lemma carry_sub_bit32[simp]:
  fixes a :: "32 word"
  shows "(1 + ucast (NOT a) :: 33 word) !! 32 \<longleftrightarrow> a \<le> 0"
  apply (subst msb_nth[symmetric,of "1 + ucast (NOT a) :: 33 word",simplified])
  apply (subst msb_is_gt_2p)
  apply (subst ucast_bitNOT)
  apply simp  
  apply simp  
  apply unat_arith
  by (auto simp add: unat_ucast is_up)


lemma overflow_sub_bit32[simp]:
  fixes a :: "'a::len0 word"
    and b :: "'b::len0 word"
  assumes "31 < LENGTH('a)"
      and "31 < LENGTH('b)"
  shows "((1::33 word) + (((\<langle>31,0\<rangle>a)::33 word) + ucast (NOT ((\<langle>31,0\<rangle>b):: 32 word)))) !! 32 = (((\<langle>31,0\<rangle>a)::32 word) \<ge> \<langle>31,0\<rangle>b)"
proof-
  have 3: "(((\<langle>31,0\<rangle>a)::33 word) \<ge> \<langle>31,0\<rangle>b) = (((\<langle>31,0\<rangle>a)::32 word) \<ge> \<langle>31,0\<rangle>b)"
    apply (subst take_bits_le_bit32)
    apply simp
    using assms apply simp
    using assms apply simp
    by simp

  have 1: "\<not> ((\<langle>31,0\<rangle>a)::33 word) !! 32"
   and 2: "\<not> ((\<langle>31,0\<rangle>b)::33 word) !! 32"
    using assms
    by (auto simp add: test_bit_of_take_bits)
  have "uint ((\<langle>31,0\<rangle>a)::33 word) < 4294967296"
   and "uint ((\<langle>31,0\<rangle>b)::33 word) < 4294967296"
    using msb_is_gt_2p[unfolded msb_nth,where 'a=33,simplified] 1
    apply (uint_arith)
    using msb_is_gt_2p[unfolded msb_nth,where 'a=33,simplified] 2
    by (uint_arith)
  hence "((1::33 word) + (((\<langle>31,0\<rangle>a)::33 word) + ucast (NOT ((\<langle>31,0\<rangle>b):: 32 word)))) !! 32 = (((\<langle>31,0\<rangle>a)::33 word) \<ge> \<langle>31,0\<rangle>b)"
    apply (subst ucast_bitNOT)
    apply simp
    apply (subst twos_complement_subtraction)
    apply simp
    apply (subst msb_is_gt_2p[unfolded msb_nth,where 'a=33,simplified])
    apply auto
    apply uint_arith
    using assms
    apply (auto simp add: is_up)
    apply uint_arith
    using assms
    by (auto simp add: is_up)
  thus ?thesis
    using 3
    by auto
qed

lemma overflow_sub_bit32_2[simp]:
  fixes a :: "'a :: len0 word"
    and b :: "32 word"
  assumes "31 < LENGTH('a)"
  shows "((1::33 word) + (ucast (NOT b) + ((\<langle>31,0\<rangle>a)::33 word))) !! 32 = (((\<langle>31,0\<rangle>a)::32 word) \<ge> b)"
  using overflow_sub_bit32[OF assms,of a b]
  by (auto simp add: field_simps)


lemma sign_sub_bit32[simp]:
  fixes a b:: "'a :: len0 word"
  assumes "31 < LENGTH('a)"
  shows "((1::33 word) + (((\<langle>31,0\<rangle>a)::33 word) + ucast (NOT ((\<langle>31,0\<rangle>b):: 32 word)))) !! 31 \<longleftrightarrow> sint (((\<langle>31,0\<rangle>a):: 32 word) - \<langle>31,0\<rangle>b) < 0"
proof-
  have 1: "\<And> a :: 33 word . a !! 31 = ((\<langle>31,0\<rangle>a):: 32 word) !! 31"
    using assms
    by (auto simp add: test_bit_of_take_bits nth_ucast)
  have 2: "\<langle>31,0\<rangle>((1::33 word) + (((\<langle>31,0\<rangle>a)::33 word) + ucast (NOT ((\<langle>31,0\<rangle>b):: 32 word)))) = (((\<langle>31,0\<rangle>a)::32 word) - \<langle>31,0\<rangle>b)"
    using assms
    apply (subst ucast_bitNOT)
    apply simp
    apply (subst twos_complement_subtraction)
    apply (subst take_bits_minus)
    apply (simp)
    apply (simp)
    by (simp)
  have 3: "... !! 31 \<longleftrightarrow> sint (((\<langle>31,0\<rangle>a):: 32 word) - \<langle>31,0\<rangle>b) < 0"
    using msb_nth[symmetric, where 'a=32]
    by (simp add: word_msb_sint)
  show ?thesis
    apply (subst 1)
    apply (subst 2)
    apply (subst 3)
    by simp
qed


end
end
