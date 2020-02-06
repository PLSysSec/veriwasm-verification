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

theory Word_Additions
  imports SymbolicRewriting
      "HOL-Word.WordBitwise"
begin

section "Extensions to the Word library"

text {*
  The word library models two's complement representation of ints.
  Some of the available operations:
*}
find_consts "_ word \<Rightarrow> _ word \<Rightarrow> _ word"
find_consts "_ word \<Rightarrow> _ word"
find_consts "_ word \<Rightarrow> bool list"
find_consts "nat \<Rightarrow> _ word"
find_consts "_ word \<Rightarrow> nat"
find_consts "int \<Rightarrow> _ word"
find_consts "_ word \<Rightarrow> int"
find_consts "bool list \<Rightarrow> _ word"



text {*
  Take the bits from $l$ to $h$ (both including) of the word.
*}
definition take_bits :: "nat \<Rightarrow> nat \<Rightarrow> 'a::len0 word \<Rightarrow> 'b::len0 word" ("\<langle>_,_\<rangle>_" [51,51,72] 72)
  where "take_bits h l w \<equiv> of_bl (take (h + 1 - l) (drop (LENGTH('a) - h - 1) (to_bl w)))"


fun bv_cat :: "'a::len0 word \<times> nat \<Rightarrow> 'a::len0 word \<times> nat \<Rightarrow> 'a::len0 word \<times> nat"
  where "bv_cat (w0,s0) (w1,s1) = (if s1 = 0 then (w0,s0) else ((w0 << s1) OR \<langle>s1-1,0\<rangle> w1, s0 + s1))"
declare bv_cat.simps[simp del]

fun sextend :: "'a::len word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a::len word"
  where "sextend w s s' = (if w!!(s - 1) then ((\<langle>s-1,0\<rangle>w) OR NOT mask s) AND mask s' else \<langle>s-1,0\<rangle>w)"



subsection "Words to bytes"

fun word_to_bytes :: "'a::len0 word \<Rightarrow> nat \<Rightarrow> 8 word list"
  where  "word_to_bytes w s = (if s \<le> 0 then [] else (\<langle>s*8-1,s*8-8\<rangle>w)#(word_to_bytes w (s-1)))"
declare word_to_bytes.simps[simp del]
lemmas word_to_bytes_simps[simp] =
  word_to_bytes.simps[of 0 s]
  word_to_bytes.simps[of 1 s]
  word_to_bytes.simps[of "(numeral n)::'a::len0 word" s]
  word_to_bytes.simps[of "- ((numeral n)::'a::len0 word)" s]
  for s n

definition sublist :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "sublist l h \<equiv> take (h + 1 - l) \<circ> (drop l)"

definition bytes_of :: "nat \<Rightarrow> nat \<Rightarrow> 'a::len0 word \<Rightarrow> 8 word list"   ("\<lbrace>_,_\<rbrace>_" [51,51,72] 72)
  where "bytes_of h l w = (if h < l \<or> LENGTH('a) div 8 \<le> h then [] else sublist (LENGTH('a) div 8 - 1 - h) (LENGTH('a) div 8 - 1 - l) (word_to_bytes w (LENGTH('a) div 8)))"

abbreviation byte_of :: "nat \<Rightarrow> 'a::len0 word \<Rightarrow> 8 word" ("\<lbrace>_\<rbrace> _" [51,72] 72)
  where "byte_of n w \<equiv> hd (\<lbrace>n,n\<rbrace> w)"

primrec cat_bytes :: "8 word list \<Rightarrow> 'a::len0 word"
  where "cat_bytes [] = 0"
  | "cat_bytes (b#bs) = ((ucast b) << (length bs * 8)) OR cat_bytes bs"

text {*
  Function @{term cat_bytes} takes a list of bytes (8 words) and converts them to a 64 word.
  This does essentially them same of @{term word_rcat}, but this version is tailored to bytes and
  makes proves/rewriting easier.
*}

value "(cat_bytes [1,2::8 word])::64 word"
value "(cat_bytes [0,0,0,21::8 word]) :: 64 word"
value "(word_rcat [1,2::8 word])::16 word"



  



subsection "Additional rewrite rules for words"

text {*
  Additional word rewriting.
*}
lemma le_numeral_zero[simp]:
  "((numeral bin0::'a::len word) \<le> (0::'a::len word)) = (uint (numeral bin0::'a::len word) = 0)"
  apply (simp add: word_le_def)
  by (smt bintr_ge0)
lemma le_numeral_one[simp]:
  "((numeral bin0::'a::len word) \<le> (1::'a::len word)) = (uint (numeral bin0::'a::len word) \<le> 1)"
  unfolding word_le_def word_le_def
  by simp

lemma le_minus_numeral[simp]:
  "(
    (word_sless::('a::len word \<Rightarrow> 'a::len word \<Rightarrow> bool))
     ((- (numeral bin0::'a::len word)))
      (numeral bin1::'a::len word)
   ) = (sint (- numeral bin0::'a::len word) < sint (numeral bin1::'a::len word))"
  unfolding word_sless_def word_sle_def
  by (smt word_sint.Rep_inject)

lemma le_zero_numeral[simp]:
  "(
    (word_sless::('a::len word \<Rightarrow> 'a::len word \<Rightarrow> bool))
     0 (numeral bin1::'a::len word)
   ) = (0 < sint (numeral bin1::'a::len word))"
  unfolding word_sless_def word_sle_def
  using word_sint.Rep_inject by fastforce

lemma rewrite_le_minus[simp]:
  shows "((a::'a::len word) - n \<le> a - m)  = (if a \<ge> m then m \<le> n \<and> a \<ge> n else (a-n \<le> (max_word::'a::len word) - m + a + 1))"
proof(cases "a\<ge>m")
  case True
  thus ?thesis
  apply (auto simp add: uint_minus_simple_alt)
    by (smt uint_sub_ge)+
next
  case False
  have 1: "(max_word::'a::len word) - m + a + 1 = (a - m)"
    apply auto
    by (metis add.left_inverse max_word_wrap)
  show ?thesis
    using False
    apply (auto)
    apply (subst 1,simp)
    by (simp add: "1")
qed

lemma rewrite_le_minus_0[simp]:
  shows "((a::'a::len word) \<le> a - m)  = (a \<ge> m \<longrightarrow> m = 0)" 
  using rewrite_le_minus[of a 0 m]
  apply auto
  by (meson less_imp_le not_le word_sub_le_iff)

lemma plus_less_left_cancel_nowrap: "x \<le> x + y' \<Longrightarrow> x \<le> x + y \<Longrightarrow> x + y' \<le> x + y \<longleftrightarrow> y' \<le> y"
  for x y y' :: "'a::len0 word"
  by uint_arith

lemma word_not_gr_zero[simp]:
  fixes w :: "'a::len0 word"
  shows "\<not> 0 < w \<longleftrightarrow> w = 0"
  apply unat_arith
  by (simp add: unat_eq_zero)


lemma mask_numeral[simp]:
  shows "mask (numeral n) = (1 << (numeral n)) - 1"
  by (auto simp add: mask_def)

lemma unfold_test_bit:
fixes w :: "'a::len word"
shows "w !! n = (if n < LENGTH('a) then to_bl w ! (LENGTH('a) - 1 - n) else False)"
  using to_bl_nth[of "LENGTH('a) - 1 - n" w,symmetric] test_bit_bin
  by (auto simp add: word_size)

lemma is_zero_bitOR[simp]:
  fixes a b :: "'a::len0 word"
  shows "((a OR b) = 0) = (a = 0 \<and> b = 0)"
  by (metis word_bw_lcs(2) word_bw_same(2) word_log_esimps(3))

lemma is_zero_all_bits:
  fixes a :: "'a::len0 word"
  shows "(a = 0) = (\<forall> n < LENGTH ('a) . \<not>a !! n)"
  by (auto simp add: word_eq_iff)

lemma is_zero_shiftl:
  fixes a :: "'a::len0 word"
  shows "((a << n) = 0) = (n \<ge> LENGTH('a) \<or> (\<forall> i < LENGTH('a) - n . \<not>a!!i))"
  using less_diff_conv 
  by (auto simp add: is_zero_all_bits nth_shiftl)

lemma twos_complement_subtraction[simp]:
  fixes a b :: "'a::len0 word"
  shows "1 + (a + NOT b) = a - b"
  by (auto simp add: word_succ_p1 twos_complement)

lemma twos_complement_subtraction_r[simp]:
  fixes a b :: "'a::len0 word"
  shows "1 + (NOT b + a) = a - b"
  by (auto simp add: word_succ_p1 twos_complement)


primrec enum_le :: "nat \<Rightarrow> nat list"
  where "enum_le 0 = []"
  | "enum_le (Suc n) = n#(enum_le n)"

lemma spec_of_enum_le:
  shows "x \<in> List.set (enum_le n) = (x < n)"
  by(induct n,auto)


lemma bitNOT_nth:
  "(NOT x) !! n \<longleftrightarrow> n < LENGTH('a) \<and> \<not>x !! n"
  for x :: "'a::len0 word"
  using test_bit_size[of "NOT x" n]
  by (auto simp add: word_size word_ops_nth_size)



declare plus_less_left_cancel_nowrap[simp add]
lemma x_less_x_plus_y[simp]:
  fixes x y :: "'a::len word"
  assumes "x \<le> max_word - y"
  shows "x \<le> x + y"
  apply (rule plus_minus_no_overflow_ab[of x "max_word::'a::len word" y,OF assms])
  by auto
lemma plus_minus_no_overflow_ab_l: "x \<le> ab - c \<Longrightarrow> c \<le> ab \<Longrightarrow> x \<le> c + x"
  for x ab c :: "'a::len0 word"
  by uint_arith
lemma x_less_x_plus_y_l[simp]:
  fixes x y :: "'a::len word"
  assumes "x \<le> max_word - y"
  shows "x \<le> y + x"
  apply (rule plus_minus_no_overflow_ab_l[of x "max_word::'a::len word" y,OF assms])
  by auto
lemma x_minus_le_plus_x[simp]:
  fixes x y w z :: "'a::len word"
  assumes "x \<ge> w"
      and "x \<le> max_word - z"
    shows "x - w \<le> z + x"
  using assms
proof-
  have "x - w \<le> x"
    using assms(1)
    by unat_arith
  also have "x \<le> z + x"
    using assms(2)
    by simp
  finally
  show ?thesis
    by simp
qed
lemma x_plus_y_less_x[simp]:
  fixes x y :: \<open>'a::len word\<close>
  assumes \<open>x \<le> max_word - y\<close>
    and \<open>y > 0\<close>
  shows \<open>x + y \<le> x \<longleftrightarrow> False\<close>
  using assms x_less_x_plus_y
  by fastforce
lemma less_max_word_minus[simp]:
  fixes x y z :: "'a::len word"
  assumes "x \<le> max_word - y"
     and "y \<ge> z"
   shows "x \<le> max_word - z"
  apply (rule order_trans[OF assms(1)])
  using assms
  by simp
lemma plus_lt_left_cancel_nowrap[simp]: "x \<le> x + y' \<Longrightarrow> x \<le> x + y \<Longrightarrow> x + y' < x + y \<longleftrightarrow> y' < y"
  for x y y' :: "'a::len0 word"
  by uint_arith
lemma plus_lt_right_cancel_nowrap[simp]: "x \<le> x + y' \<Longrightarrow> x \<le> x + y \<Longrightarrow> y' + x < y + x \<longleftrightarrow> y' < y"
  for x y y' :: "'a::len0 word"
  by uint_arith
lemma x_lt_x_plus_y[simp]:
  fixes x y :: "'a::len word"
  assumes "x \<le> max_word - y"
    shows "x < x + y \<longleftrightarrow> y > 0"
proof-
  have "x \<le> x + y"
    apply (rule plus_minus_no_overflow_ab[of x "max_word::'a::len word" y,OF assms(1)])
    by auto
  thus ?thesis
    apply (auto simp add: word_le_less_eq)
    by uint_arith
qed



lemma gt_zero_is_le_one:
  fixes w :: \<open>'a::len word\<close>
  assumes \<open>0 < w\<close>
  shows \<open>1 \<le> w\<close>
  using assms word_le_sub1
  by force

lemma a_minus_b_lt[simp]:
  fixes a :: "'a::len0 word"
  assumes "a \<ge> b"
    shows "(a - b < a) = (b > 0)"
  using assms
  by unat_arith

lemma a_minus_b_le[simp]:
  fixes a :: "'a::len0 word"
  assumes "a \<ge> b"
    shows "(a - b \<le> a)"
  using assms
  by unat_arith

lemma unat_ucast[OF refl]:
  assumes "uc = ucast"
      and "is_up uc"
    shows "unat (uc a) = unat a"
  using assms
  by (auto simp add: unat_def uint_up_ucast)

lemma ucast_minus:
  fixes a b :: "'a::len0 word"
  shows "ucast (a - b) = (if uint b \<le> uint a then ucast a - ucast b else ucast a - ucast b + word_of_int (2 ^ LENGTH('a)))"
  apply (auto simp add: ucast_def)
  apply (subst uint_sub_if')
  apply (auto simp add: wi_hom_syms(2))
  apply (subst uint_sub_if')
  by (auto simp add: wi_hom_syms ucast_def[symmetric])

lemma ucast_plus:
  fixes a b :: "'a::len0 word"
  shows "ucast (a + b) = (if uint a + uint b < 2 ^ LENGTH('a) then ucast a + ucast b else  ucast a + ucast b - word_of_int (2 ^ LENGTH('a)))"
  apply (auto simp add: ucast_def)
  apply (subst uint_plus_if_size)
  apply (auto simp add: word_size wi_hom_syms ucast_def[symmetric])
  apply (auto simp add: ucast_def)
  apply (subst uint_plus_if_size)
  by (auto simp add: word_size wi_hom_syms ucast_def[symmetric])

lemma msb_is_gt_2p:
  fixes a :: "'a::len word"
  shows "msb a \<longleftrightarrow> a \<ge> 2 ^ (LENGTH('a) - 1)"
proof-
  {
    assume 1: "a !! (LENGTH('a) - 1)"
    hence "a \<ge> 2 ^ (LENGTH('a) - 1)"
      using bang_is_le
      by (auto simp add: word_size)
  }
  moreover
  {
    assume 1: "\<not>a!! (LENGTH('a) - 1)"
    {
      fix i :: nat
      assume "i < LENGTH('a)"
      hence "(a AND mask (LENGTH('a) - 1)) !! i = a !! i"
        using 1
        by (cases "i=LENGTH('a) - 1",auto simp add: word_ao_nth word_size)
    }
    hence "a AND mask (LENGTH('a) - 1) = a"
      apply (intro word_eqI)
      by (auto simp add: word_size)
    hence "a < 2 ^ (LENGTH('a) - 1)"
      using mask_eq_iff_w2p[of "LENGTH('a) - 1" a]
      by (auto simp add: word_size)
  }
  ultimately
  show ?thesis
    unfolding msb_nth
    using linorder_not_le
    by blast
qed

lemma zero_le_2p:
  assumes "n < LENGTH('a)"
  shows "(0::'a::len word) < 2 ^ n"
  using assms
proof(induct n)
  case 0
  thus ?case
    by auto
next
  case (Suc n)
  thus ?case
    using shiftl_1[symmetric,of "n+1",where 'a='a]
    using is_zero_shiftl[of "1::'a word" "n+1"]
    apply (auto simp del: shiftl_1)
    by fastforce
qed



lemma of_nat_unat_is_ucast[simp]:
  fixes a :: "'a::len word"
  assumes "LENGTH('a) < LENGTH('b)"
  shows "of_nat (unat a) = (ucast a :: 'b::len word)"
  apply (rule word_unat.Rep_eqD)
  apply (subst unat_of_nat)
  apply (subst unat_ucast)
  apply (subst is_up)
  using assms apply simp
  using unat_lt2p[of a] assms
  by (metis assms int_ops(3) lt2p_lem mod_less of_nat_less_iff of_nat_power order_less_imp_le uint_nat)

lemma sextend_remove:
  fixes a :: "'a::len word"
  assumes "a < 2^(s-1)"
  shows "sextend a s s' = \<langle>s - Suc 0,0\<rangle>a"
  using assms
  unfolding sextend.simps
  apply auto
  apply (frule bang_is_le)
  by auto

end