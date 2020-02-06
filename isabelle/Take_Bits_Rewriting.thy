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

theory Take_Bits_Rewriting
  imports Machine
begin


lemmas take_bits_simps[simp] =
  take_bits_def[of h l 0]
  take_bits_def[of h l 1]
  take_bits_def[of h l "numeral bin::'a::len0 word"]
  take_bits_def[of h l "- (numeral bin::'a::len0 word)"]
  for h l bin

lemma to_bl_one[simp]: "to_bl (1::'a::len0 word) = bin_to_bl (len_of TYPE('a)) (uint (1::'a::len0 word))"
  unfolding to_bl_def
  by simp
lemma bin_to_bl_aux_negation_numeral[simp]:
  shows "bin_to_bl_aux s (- (numeral n)) bs = (if s = 0 then bs else bin_to_bl_aux (s-1) ((- numeral n) div 2) (bin_last (- numeral n) # bs))"
  by (cases s,auto simp add: bin_rest_def)

lemma take_bits_remove:
  assumes "h = LENGTH ('a) - 1"
  shows "((\<langle>h,0\<rangle>(w::'a::len0 word))::'b::len0 word) = ((ucast w)::'b::len0 word)"
  unfolding take_bits_def
  apply (auto)
  by (metis assms cancel_comm_monoid_add_class.diff_cancel diff_Suc_eq_diff_pred of_bl_def to_bl_bin trunc_bl2bin ucast_def word_bl_Rep' word_ubin.norm_Rep)

lemma take_all_bits64[simp]:
  shows "\<langle>63,0\<rangle> (w::64 word) = w"
  unfolding take_bits_def
  by (simp)    

lemma take_all_bits32[simp]:
  shows "\<langle>31,0\<rangle> (w::32 word) = w"
  unfolding take_bits_def
  by (simp)    

lemma take_all_bits8[simp]:
  shows "\<langle>7,0\<rangle> (w::8 word) = w"
  unfolding take_bits_def
  by (simp)    

lemma nth_of_take_bits:
  assumes "h < LENGTH('b)"
      and "n < LENGTH('a)"
      shows "to_bl (((\<langle>h,l\<rangle> (w::'b::len0 word))::'a::len0 word))!n =
          (if LENGTH('a) - Suc n < Suc h - l then (to_bl w)!(n + LENGTH('b) - (l + LENGTH('a))) else False)"
    using assms
    apply (auto simp add: take_bits_def test_bit_bin' bin_nth_uint word_size rev_nth word_rev_tf nth_takefill min_def algebra_simps split: if_split_asm)
    by (cases "l=0";auto)+

lemma test_bit_of_take_bits:
  assumes "h < LENGTH('b)"
      and "n < LENGTH('a)"
  shows "(((\<langle>h,l\<rangle> (w::'b::len0 word))::'a::len0 word))!!n = (if n < Suc h - l then w!!(l+n) else False)"
proof-
  let ?w = "(((\<langle>h,l\<rangle> (w::'b::len0 word))::'a::len0 word))"
  have "?w  !! n = to_bl ?w ! (LENGTH('a) - 1 - n)"
    using assms to_bl_nth[of "LENGTH('a) - 1 - n" ?w,symmetric]
    by (auto simp add: word_size)
  thus ?thesis
    using nth_of_take_bits[of h _ l w,where 'a='a] assms 
    using to_bl_nth[of "LENGTH('b) - Suc (l + n)" w]
    by (auto split: if_split_asm simp add: algebra_simps word_size)
qed

lemma if_test_bit_of_take_bits_is_set:
  fixes w :: "'a::len0 word"
  shows "((\<langle>h,l\<rangle>w)::'b::len word) !! i \<Longrightarrow> i \<le> Suc h - l \<and> i < LENGTH('b) \<and> i < LENGTH('a)"
  by (auto simp add: take_bits_def unfold_test_bit word_rep_drop nth_append word_size rev_nth min_def algebra_simps split: if_split_asm)

lemma take_bits_of_take_bits[simp]:
  fixes w :: "'a::len0 word"
  assumes "h < LENGTH('b)"
      and "h' < LENGTH('a)"
shows "((\<langle>h,l\<rangle>((\<langle>h',l'\<rangle>w)::'b::len0 word))::'c::len0 word) = (((\<langle>(if Suc h - l < Suc h' - (l + l') then h+l' else h'),l+l'\<rangle>w) :: 'c::len0 word) :: 'c::len0 word)"
proof-
  {
    fix n :: nat
    assume "n < size (((\<langle>h,l\<rangle>((\<langle>h',l'\<rangle>w)::'b::len0 word))::'c::len0 word))"
    hence "((\<langle>h,l\<rangle>((\<langle>h',l'\<rangle>w)::'b::len0 word))::'c::len0 word) !! n = (((\<langle>(if Suc h - l < Suc h' - (l + l') then h+l' else h'),l+l'\<rangle>w) :: 'c::len0 word) :: 'c::len0 word) !! n"
      using assms
      by (auto split: if_split_asm simp add: field_simps test_bit_of_take_bits word_size)
  }
  thus ?thesis
    apply (intro word_eqI)
    by auto
qed


lemma take_bits_max_word[simp]:
  assumes "LENGTH('a) = h + 1"
      and "LENGTH('b) > h"
    shows "(\<langle>h,0\<rangle>(max_word::'b::len word) :: 'a::len word) = -1"
proof-
  have "(\<langle>h,0\<rangle>(max_word::'b::len word)) = (max_word :: 'a::len word)"
  proof-
    {
      fix n
      assume "n < LENGTH('a)"
      hence "(\<langle>h,0\<rangle>(max_word::'b::len word) :: 'a::len word) !! n = (max_word :: 'a::len word) !! n"
        using assms
        by (auto simp add: test_bit_of_take_bits)
    }
    thus ?thesis
      apply (intro word_eqI)
      by (auto simp add: word_size)
  qed
  thus ?thesis
    using max_word_minus
    by auto
qed


subsection \<open>Take_Bits and logical operations\<close>


lemma take_bits_bitAND:
  fixes a b :: "'a::len0 word"
  assumes "h < LENGTH('a)"
    shows "((\<langle>h,l\<rangle>(a AND b)) :: 'b::len0 word) = ((\<langle>h,l\<rangle>a) :: 'b::len0 word) AND \<langle>h,l\<rangle>b"
proof-
  {
    fix n :: nat
    assume "n < LENGTH('b)"
    hence "((\<langle>h,l\<rangle>(a AND b)) :: 'b::len0 word) !! n = (((\<langle>h,l\<rangle>a) :: 'b::len0 word) AND \<langle>h,l\<rangle>b) !! n"
      using assms
      apply (subst test_bit_of_take_bits)
      by (auto simp add: test_bit_of_take_bits word_ao_nth)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed

lemma take_bits_bitOR:
  fixes a b :: "'a::len0 word"
  assumes "h < LENGTH('a)"
    shows "((\<langle>h,l\<rangle>(a OR b)) :: 'b::len0 word) = ((\<langle>h,l\<rangle>a) :: 'b::len0 word) OR \<langle>h,l\<rangle>b"
proof-
  {
    fix n :: nat
    assume "n < LENGTH('b)"
    hence "((\<langle>h,l\<rangle>(a OR b)) :: 'b::len0 word) !! n = (((\<langle>h,l\<rangle>a) :: 'b::len0 word) OR \<langle>h,l\<rangle>b) !! n"
      using assms
      apply (subst test_bit_of_take_bits)
      by (auto simp add: test_bit_of_take_bits word_ao_nth)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed


lemma take_bits_bitAND_bit32[simp]:
  fixes a b :: "'a::len0 word"
  assumes "LENGTH('b) > 32"
      and "LENGTH('a) \<ge> 32"
  shows "((\<langle>31,0\<rangle>(a AND b))::'b::len0 word) = ucast (((\<langle>31,0\<rangle>a)::32 word) AND ((\<langle>31,0\<rangle>b)::32 word))"
proof-
  {
    fix i :: nat
    assume "i < LENGTH('b)"
    hence "((\<langle>31,0\<rangle>(a AND b))::'b::len0 word) !! i = ((ucast (((\<langle>31,0\<rangle>a)::32 word) AND ((\<langle>31,0\<rangle>b)::32 word))) :: 'b::len0 word) !! i"
      using assms
      using if_test_bit_of_take_bits_is_set[of 31 0 a i,where 'b=32]
      by (auto simp add: nth_ucast word_ao_nth test_bit_of_take_bits )
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed


lemma take_bits_bitOR_bit32[simp]:
  fixes a b :: "'a::len0 word"
  assumes "LENGTH('b) > 32"
      and "LENGTH('a) \<ge> 32"
  shows "((\<langle>31,0\<rangle>(a OR b))::'b::len0 word) = ucast (((\<langle>31,0\<rangle>a)::32 word) OR ((\<langle>31,0\<rangle>b)::32 word))"
proof-
  {
    fix i :: nat
    assume "i < LENGTH('b)"
    hence "((\<langle>31,0\<rangle>(a OR b))::'b::len0 word) !! i = ((ucast (((\<langle>31,0\<rangle>a)::32 word) OR ((\<langle>31,0\<rangle>b)::32 word))) :: 'b::len0 word) !! i"
      using assms
      using if_test_bit_of_take_bits_is_set[of 31 0 a i,where 'b=32]
      apply (auto simp add: nth_ucast word_ao_nth test_bit_of_take_bits )
      using if_test_bit_of_take_bits_is_set[of 31 0 b i,where 'b=32]  
      by auto
    }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed

lemma take_bits_bitAND_bit64_high[simp]:
  fixes a b :: "'a::len0 word"
  assumes "LENGTH('b) > 128"
      and "LENGTH('a) \<ge> 128"
  shows "((\<langle>127,64\<rangle>(a AND b))::'b::len0 word) = ucast (((\<langle>127,64\<rangle>a)::64 word) AND ((\<langle>127,64\<rangle>b)::64 word))"
proof-
  {
    fix i :: nat
    assume "i < LENGTH('b)"
    hence "((\<langle>127,64\<rangle>(a AND b))::'b::len0 word) !! i = ((ucast (((\<langle>127,64\<rangle>a)::64 word) AND ((\<langle>127,64\<rangle>b)::64 word))) :: 'b::len0 word) !! i"
      using assms
      using if_test_bit_of_take_bits_is_set[of 127 64 a i,where 'b=64]
      by (auto simp add: nth_ucast word_ao_nth test_bit_of_take_bits )
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed

lemma take_bits_bitAND_bit64[simp]:
  fixes a b :: "'a::len0 word"
  assumes "LENGTH('b) > 64"
      and "LENGTH('a) \<ge> 64"
  shows "((\<langle>63,0\<rangle>(a AND b))::'b::len0 word) = ucast (((\<langle>63,0\<rangle>a)::64 word) AND ((\<langle>63,0\<rangle>b)::64 word))"
proof-
  {
    fix i :: nat
    assume "i < LENGTH('b)"
    hence "((\<langle>63,0\<rangle>(a AND b))::'b::len0 word) !! i = ((ucast (((\<langle>63,0\<rangle>a)::64 word) AND ((\<langle>63,0\<rangle>b)::64 word))) :: 'b::len0 word) !! i"
      using assms
      using if_test_bit_of_take_bits_is_set[of 63 0 a i,where 'b=64]
      by (auto simp add: nth_ucast word_ao_nth test_bit_of_take_bits )
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed




lemma take_bits_bitNOT_bit64[simp]:
  fixes a :: "'c::len0 word"
  assumes "64 \<le> LENGTH('c)"
  shows "((\<langle>63,0\<rangle>(NOT a))::'b::len0 word) = ucast (NOT ((\<langle>63,0\<rangle>a)::64 word))"
proof-
  {
    fix n
    assume "n < LENGTH('b)"
    hence "((\<langle>63,0\<rangle>(NOT a))::'b::len0 word) !! n = ((ucast (NOT ((\<langle>63,0\<rangle>a)::64 word)))::'b::len0 word) !! n"
      using assms
      apply (simp only: nth_ucast)
      apply (cases "n< 32",auto simp add: test_bit_of_take_bits word_ops_nth_size word_size nth_ucast )
      by (simp add: test_bit_bin)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed

lemma take_bits_bitNOT_bit32[simp]:
  fixes a :: "'c::len0 word"
  assumes "32 \<le> LENGTH('c)"
  shows "((\<langle>31,0\<rangle>(NOT a))::'b::len0 word) = ucast (NOT ((\<langle>31,0\<rangle>a)::32 word))"
proof-
  {
    fix n
    assume "n < LENGTH('b)"
    hence "((\<langle>31,0\<rangle>(NOT a))::'b::len0 word) !! n = ((ucast (NOT ((\<langle>31,0\<rangle>a)::32 word)))::'b::len0 word) !! n"
      using assms
      apply (simp only: nth_ucast)
      apply (cases "n< 32",auto simp add: test_bit_of_take_bits word_ops_nth_size word_size nth_ucast )
      by (simp add: test_bit_bin)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed



lemma bitXOR_nth:
  "(x XOR y) !! n \<longleftrightarrow> x !! n \<noteq> y !! n"
  for x :: "'a::len0 word"
  by (metis test_bit_size word_ops_nth_size wsst_TYs(3))


lemma take_bits_bitXOR_bit32[simp]:
  fixes a b :: "'a::len0 word"
  assumes "LENGTH('b) > 32"
      and "LENGTH('a) \<ge> 32"
  shows "((\<langle>31,0\<rangle>(a XOR b))::'b::len0 word) = ucast (((\<langle>31,0\<rangle>a)::32 word) XOR ((\<langle>31,0\<rangle>b)::32 word))"
proof-
  {
    fix i :: nat
    assume "i < LENGTH('b)"
    hence "((\<langle>31,0\<rangle>(a XOR b))::'b::len0 word) !! i = ((ucast (((\<langle>31,0\<rangle>a)::32 word) XOR ((\<langle>31,0\<rangle>b)::32 word))) :: 'b::len0 word) !! i"
      using assms(1-2)
      using if_test_bit_of_take_bits_is_set[of 31 0 a i,where 'b=32]
      apply (auto simp add: nth_ucast bitXOR_nth test_bit_of_take_bits word_size)
      using if_test_bit_of_take_bits_is_set[of 31 0 b i,where 'b=32]
      by auto
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed


subsection \<open>Take_Bits and ucast\<close>


lemma take_bits_ucast[simp]:
  fixes a :: "'c::len0 word"
  assumes "h < LENGTH('a)"
      and "LENGTH('c) - 1 \<le> h"
  shows "((\<langle>h,0\<rangle>((ucast a)::'a::len0 word))::'b::len0 word) = ucast a"
proof-
  {
    fix n :: nat
    assume "n < LENGTH('b)"
    hence "((\<langle>h,0\<rangle>((ucast a)::'a::len0 word))::'b::len0 word) !! n = ((ucast a)::'b::len0 word) !! n"
      using assms
      apply (auto simp add: test_bit_of_take_bits nth_ucast)
      by (smt Suc_le_eq Suc_pred' assms(2) le0 less_le_trans not_less test_bit_bin)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed


lemma ucast_take_bits[simp]:
  fixes a :: "'a::len0 word"
  assumes "h < LENGTH('a)"
      and "Suc h - l = LENGTH('c)"
  shows "((ucast ((\<langle>h,l\<rangle>a)::'c::len0 word))::'b::len0 word) = ((\<langle>h,l\<rangle>a)::'b::len0 word)"
proof-
  {
    fix n :: nat
    assume "n < LENGTH('b)"
    hence "((ucast ((\<langle>h,l\<rangle>a)::'c::len0 word))::'b::len0 word) !! n = ((\<langle>h,l\<rangle>a)::'b::len0 word) !! n"
      using assms
      apply (auto simp add: test_bit_of_take_bits nth_ucast)
      by (simp add: test_bit_bin)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed




lemma take_bits_ucast_bit64[simp]:
  fixes a :: "'c::len0 word"
  assumes "63 < LENGTH('a)"
      and "63 < LENGTH('c)"
  shows "((\<langle>63,0\<rangle>((ucast a)::'a::len0 word))::'b::len0 word) = ucast ((\<langle>63,0\<rangle>a)::64 word)"
proof-
  {
    fix i :: nat
    assume "i < LENGTH('b)"
    hence "((\<langle>63,0\<rangle>((ucast a)::'a::len0 word))::'b::len0 word) !! i = ((ucast ((\<langle>63,0\<rangle>a)::64 word))::'b::len0 word) !! i"
      using assms
      by (auto simp add: test_bit_of_take_bits nth_ucast)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed



lemma take_bits_ucast_bit32[simp]:
  fixes a :: "'c::len0 word"
  assumes "31 < LENGTH('a)"
      and "31 < LENGTH('c)"
  shows "((\<langle>31,0\<rangle>((ucast a)::'a::len0 word))::'b::len0 word) = ucast ((\<langle>31,0\<rangle>a)::32 word)"
proof-
  {
    fix i :: nat
    assume "i < LENGTH('b)"
    hence "((\<langle>31,0\<rangle>((ucast a)::'a::len0 word))::'b::len0 word) !! i = ((ucast ((\<langle>31,0\<rangle>a)::32 word))::'b::len0 word) !! i"
      using assms
      by (auto simp add: test_bit_of_take_bits nth_ucast)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed

lemma take_bits_ucast_bit8[simp]:
  fixes a :: "'c::len0 word"
  assumes "7 < LENGTH('a)"
      and "7 < LENGTH('c)"
  shows "((\<langle>7,0\<rangle>((ucast a)::'a::len0 word))::'b::len0 word) = ucast ((\<langle>7,0\<rangle>a)::8 word)"
proof-
  {
    fix i :: nat
    assume "i < LENGTH('b)"
    hence "((\<langle>7,0\<rangle>((ucast a)::'a::len0 word))::'b::len0 word) !! i = ((ucast ((\<langle>7,0\<rangle>a)::8 word))::'b::len0 word) !! i"
      using assms
      by (auto simp add: test_bit_of_take_bits nth_ucast)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed

lemma take_bits_ucast_bit16[simp]:
  fixes a :: "'c::len0 word"
  assumes "15 < LENGTH('a)"
      and "15 < LENGTH('c)"
    shows "((\<langle>15,0\<rangle>((ucast a)::'a::len0 word))::'b::len0 word) = ucast ((\<langle>15,0\<rangle>a)::16 word)"
proof-
  {
    fix i :: nat
    assume "i < LENGTH('b)"
    hence "((\<langle>15,0\<rangle>((ucast a)::'a::len0 word))::'b::len0 word) !! i = ((ucast ((\<langle>15,0\<rangle>a)::16 word))::'b::len0 word) !! i"
      using assms
      by (auto simp add: test_bit_of_take_bits nth_ucast)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed


lemma ucast_is_0[simp]:
  fixes a :: "'a::len0 word"
  assumes "LENGTH('b) \<ge> LENGTH('a)"
  shows "((ucast a)::'b::len0 word) = 0 \<longleftrightarrow> a = 0"
  using assms
  apply (auto)
  by (metis (mono_tags, hide_lams) is_zero_all_bits less_le_trans nth_ucast)

lemma ucast_is_1[simp]:
  fixes a :: "'a::len word"
  assumes "LENGTH('b) > LENGTH('a)"
  shows "((ucast a)::'b::len word) = 1 \<longleftrightarrow> a = 1"
proof-
  {
    assume "((ucast a)::'b::len word) = 1"
    hence "\<forall> i < LENGTH('b) . ((ucast a)::'b::len word) !! i = (i = 0)"
      by (auto simp add: nth_ucast)
    hence "\<forall> i < LENGTH('b) . a !! i = (i = 0)"
      by (auto simp add: nth_ucast)
    hence "a = 1"
      using assms
      by (auto simp add: word_eq_iff)
  }
  thus ?thesis
    by auto
qed



lemma test_bit_of_add_2p:
  fixes a :: "'a::len word"
  assumes "i < n"
      and "n < LENGTH('a)"
      and "\<langle>n-1,0\<rangle>a = a"
    shows "(2^n + a) !! i = a !! i"
proof-
  {
    fix j :: nat
    assume "j < LENGTH('a) - n"
    hence "take (LENGTH('a) - n) (to_bl a) ! j = replicate (LENGTH('a) - n) False ! j"
      apply (auto)
      apply (subst (asm) assms(3)[symmetric])
      apply (subst (asm) to_bl_nth)
      using assms
      by (auto simp add: word_size test_bit_of_take_bits split: if_split_asm)
  }
  hence "take (LENGTH('a) - n) (to_bl a) = replicate (LENGTH('a) - n) False"
    apply (intro nth_equalityI)
    by (auto)
  hence "rev (to_bl (2^n + a)) ! i = a !! i"
    using assms
    apply (subst aligned_bl_add_size[where n=n])
    apply (simp add: word_size)
    apply (subst shiftl_1[symmetric])+
    apply (simp only: word_size bl_shiftl)
    apply (simp del: to_bl_one)
    apply (subst shiftl_1[symmetric])+
    apply (simp only: word_size bl_shiftl) defer
    by (auto simp add: rev_nth nth_append word_size test_bit_bl)
  thus ?thesis
    by (auto simp add: test_bit_bl word_size)
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



lemma eliminate_ucast_8bit[simp]:
  fixes w :: \<open>'a::len word\<close>
  assumes \<open>LENGTH('a) > 8\<close>
      and \<open>LENGTH('b) > 8\<close>
  shows \<open>(ucast (\<langle>7,0\<rangle>w::'b::len0 word)::8 word) = (\<langle>7,0\<rangle>w::8 word)\<close>
proof -
  {
    fix n :: nat
    assume \<open>n < 8\<close>
    hence \<open>(ucast (\<langle>7,0\<rangle>w::'b::len0 word)::8 word) !! n = (\<langle>7,0\<rangle>w::8 word) !! n\<close>
      using assms
      by (auto simp add: nth_ucast test_bit_of_take_bits)
  }
  thus ?thesis
    by (intro word_eqI) (simp add: word_size)
qed

lemma nth_ucast_gt:
  fixes a :: "'a::len word"
  assumes "LENGTH('b) \<ge> LENGTH('a)"
  shows "((ucast a) :: 'b::len word) !! (LENGTH('a) - 1) \<longleftrightarrow> a \<ge> 2 ^ (LENGTH('a) - 1)"
 using msb_is_gt_2p[of a] assms
 apply (auto simp add: msb_nth nth_ucast)
 using less_le_trans test_bit_bin by blast


subsection \<open> Take_Bits and sign extension\<close>

lemma take_bits_sextend_bit64[simp]:
  fixes a :: "'c::len word"
  assumes "64 \<le> LENGTH('c)"
      and "s \<le> 64"
    shows "((\<langle>63,0\<rangle>(sextend a s s'))::'b::len word) = ucast (sextend ((\<langle>63,0\<rangle>a)::64 word) s (min 64 s'))"
proof-
  {
    fix n :: nat
    assume "n < LENGTH('b)"
    hence "((\<langle>63,0\<rangle>(sextend a s s'))::'b::len word) !! n = ((ucast (sextend ((\<langle>63,0\<rangle>a)::64 word) s (min 64 s')))::'b::len word) !! n"
      using assms
      apply (auto simp add: sextend.simps word_ops_nth_size word_size test_bit_of_take_bits nth_ucast word_ao_nth)
      by (simp add: test_bit_bin)+
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed

lemma take_bits_sextend_bit32[simp]:
  fixes a :: "'c::len word"
  assumes "32 \<le> LENGTH('c)"
      and "s \<le> 32"
    shows "((\<langle>31,0\<rangle>(sextend a s s'))::'b::len word) = ucast (sextend ((\<langle>31,0\<rangle>a)::32 word) s (min 32 s'))"
proof-
  {
    fix n :: nat
    assume "n < LENGTH('b)"
    hence "((\<langle>31,0\<rangle>(sextend a s s'))::'b::len word) !! n = ((ucast (sextend ((\<langle>31,0\<rangle>a)::32 word) s (min 32 s')))::'b::len word) !! n"
      using assms
      apply (auto simp add: word_ops_nth_size word_size test_bit_of_take_bits nth_ucast word_ao_nth)
      by (simp add: test_bit_bin)+
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed
declare sextend.simps[simp del]


lemma sextend_ucast_remove[simp]:
  fixes a :: "'a::len0 word"
  assumes "LENGTH('a) < s"
      and "s - Suc 0 < LENGTH(64)"
  shows "sextend (ucast a :: 64 word) s 64 = ucast a"
proof-
  {
    fix i :: nat
    assume "i < 64"
    have "\<not> a !! (s - 1)"
      apply (subst test_bit_bin)
      using assms
      by auto
    hence "(sextend (ucast a :: 64 word) s 64 !! i) = (ucast a :: 64 word) !! i"
      using assms
      by (auto simp add: sextend.simps nth_ucast test_bit_of_take_bits)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed



lemma msb_take_bits[simp]:
  fixes a :: "'a::len0 word"
  assumes "h < LENGTH('a)"
  shows "msb ((\<langle>h,l'\<rangle>a)::'b::len word) = (if LENGTH('b) \<le> Suc h - l' then a !! (l' + (LENGTH('b) - Suc 0)) else False)"
  using assms
  apply (cases "LENGTH('b) = 0",auto simp add: msb_nth test_bit_of_take_bits)
  by (metis diff_Suc_less le_neq_implies_less lens_gt_0(2) less_imp_diff_less)



subsection \<open> Take\_Bits and arithmetic\<close>

text \<open>This definition is based on @{thm to_bl_plus_carry}, which formulates addition as bitwise operations using @{term xor3} and @{term carry}.\<close>

definition bitwise_add :: "(bool \<times> bool) list \<Rightarrow> bool \<Rightarrow> bool list"
  where "bitwise_add x c \<equiv> foldr (\<lambda>(x, y) res car. xor3 x y car # res (carry x y car)) x (\<lambda>_. []) c"

lemma length_foldr_bitwise_add:
  shows "length (bitwise_add x c) = length x"
  unfolding bitwise_add_def
  by(induct x arbitrary: c) auto

text \<open>This is the "heart" of the proof: bitwise addition of two appended zipped lists can be expressed as
      two consecutive bitwise additions.
      Here, I need to make the assumption that the final carry is False.
 \<close>
lemma bitwise_add_append:
  assumes "x = [] \<or> \<not>carry (fst (last x)) (snd (last x)) True"
  shows "bitwise_add (x @ y) (x\<noteq>[] \<and> c) = bitwise_add x (x\<noteq>[] \<and> c) @ bitwise_add y False"
  using assms
  unfolding bitwise_add_def
  by(induct x arbitrary: c) (auto simp add: case_prod_unfold xor3_def carry_def split: if_split_asm)

lemma bitwise_add_take_append:
  shows "take (length x) (bitwise_add (x @ y) c) = bitwise_add x c"
  unfolding bitwise_add_def
  by(induct x arbitrary: c) (auto simp add: case_prod_unfold xor3_def carry_def split: if_split_asm)

lemma bitwise_add_zero:
  shows "bitwise_add (replicate n (False, False)) False = replicate n False "
  unfolding bitwise_add_def
  by(induct n) (auto simp add: xor3_def carry_def)

lemma bitwise_add_take:
  shows "take n (bitwise_add x c) = bitwise_add (take n x) c"
  unfolding bitwise_add_def
  apply(induct n arbitrary: x c,auto)
  by (metis append_take_drop_id bitwise_add_def bitwise_add_take_append diff_is_0_eq' length_foldr_bitwise_add length_take nat_le_linear rev_min_pm1 take_all)

lemma fst_hd_drop_zip:
  assumes "n < length x"
      and "length x = length y"
  shows "fst (hd (drop n (zip x y))) = hd (drop n x)"
  using assms
  apply(induct x arbitrary: n y,auto)
  by (metis (no_types, lifting) Cons_nth_drop_Suc drop_zip fst_conv length_Cons list.sel(1) zip_Cons_Cons)

lemma snd_hd_drop_zip:
  assumes "n < length x"
      and "length x = length y"
  shows "snd (hd (drop n (zip x y))) = hd (drop n y)"
  using assms
  apply(induct x arbitrary: n y,auto)
  by (metis (no_types, lifting) Cons_nth_drop_Suc drop_zip snd_conv length_Cons list.sel(1) zip_Cons_Cons)

text \<open>
  Taking bits of @{term "a+b"} can be rewritten to taking bits of @{term a} and @{term b}.
\<close>
lemma take_bits_plus:
  fixes a b :: "'a::len0 word"
  assumes "LENGTH('a) > LENGTH('b)"
      and "h = LENGTH('b) - 1"
  shows "((\<langle>h,0\<rangle>(a+b)) :: 'b ::len0 word) = \<langle>h,0\<rangle>a + \<langle>h,0\<rangle>b"
proof-
  have "to_bl ((\<langle>h,0\<rangle>(a+b)) :: 'b::len0 word) = to_bl (((\<langle>h,0\<rangle>a)::'b::len0 word) + \<langle>h,0\<rangle>b)"
    using assms
    unfolding take_bits_def
    apply (auto simp add: to_bl_plus_carry word_rep_drop length_foldr_bitwise_add drop_zip[symmetric] rev_drop bitwise_add_def simp del: foldr_replicate foldr_append)
    apply (simp only: bitwise_add_def[symmetric] length_foldr_bitwise_add)
    by (auto simp add: drop_take bitwise_add_take[symmetric] rev_take length_foldr_bitwise_add)
  thus ?thesis
    using word_bl.Rep_eqD
    by blast
qed

text \<open>
  Here, I need to make the assumptions that the most significant bits are not set.
  Otherwise, the rhs will possibly have an extra bit.
\<close>
lemma take_bits_plus_carry_false:
  fixes a b :: "'a::len0 word"
  assumes "\<not> a!!h"
      and "\<not> b!!h"
      and "LENGTH('a) \<ge> Suc h"
  shows "(\<langle>h,0\<rangle>(a+b) :: 'a::len0 word) = \<langle>h,0\<rangle>a + \<langle>h,0\<rangle>b"
proof-
  have "zip (to_bl a) (to_bl b) = [] \<or>
     \<not> carry (fst (last (take (Suc h) (rev (zip (to_bl a) (to_bl b))))))
         (snd (last (take (Suc h) (rev (zip (to_bl a) (to_bl b)))))) True"
    using assms
    by (auto simp add: take_rev last_rev fst_hd_drop_zip snd_hd_drop_zip carry_def hd_drop_conv_nth to_bl_nth word_size)
  hence "to_bl ((\<langle>h,0\<rangle>(a+b) :: 'a::len0 word)) = to_bl (((\<langle>h,0\<rangle>a)::'a::len0 word) + \<langle>h,0\<rangle>b)"
    using assms bitwise_add_take
    unfolding take_bits_def
    apply (auto simp add: to_bl_plus_carry word_rep_drop length_foldr_bitwise_add drop_zip[symmetric] rev_drop bitwise_add_def simp del: foldr_replicate foldr_append)
    using bitwise_add_append[of "take (Suc h) (rev (zip (to_bl a) (to_bl b)))" "replicate (LENGTH('a) - Suc h) (False, False)" False,unfolded bitwise_add_def]
     apply (auto simp add: drop_rev length_foldr_bitwise_add[unfolded bitwise_add_def] bitwise_add_zero[unfolded bitwise_add_def] simp del: foldr_replicate foldr_append)
    by (metis bitwise_add_def length_foldr_bitwise_add length_rev less_le_trans list.size(3) neq0_conv to_bl_plus_carry word_bl_Rep' zero_less_Suc)
  thus ?thesis
    using word_bl.Rep_eqD
    by blast
qed

lemmas take_bits_plus_64bit[simp] =
  take_bits_plus[of 63 a b, where 'b=64, simplified]
  take_bits_plus[of 63 1 b, where 'b=64, simplified]
  for a b

lemma take_bits_plus_32bit_generic:
  fixes a b :: "'c::len0 word"
  assumes "LENGTH('c) \<ge> LENGTH('b)"
      and "LENGTH('c) > 32"
  shows "((\<langle>31,0\<rangle>(a + b)) :: 'b ::len0 word) = ucast (((\<langle>31,0\<rangle>a)::32 word) + ((\<langle>31,0\<rangle>b)::32 word))"
proof-
  have "to_bl ((\<langle>31,0\<rangle>(a + b)) :: 'b ::len0 word) = to_bl ((ucast (((\<langle>31,0\<rangle>a)::32 word) + ((\<langle>31,0\<rangle>b)::32 word)) ::'b::len0 word))"
    using assms
    unfolding take_bits_def
    apply (auto simp add: to_bl_plus_carry word_rep_drop length_foldr_bitwise_add drop_zip[symmetric] rev_drop bitwise_add_def to_bl_ucast simp del: foldr_replicate foldr_append)
    apply (simp only: bitwise_add_def[symmetric] length_foldr_bitwise_add)
    by (auto simp add: drop_take rev_take  to_bl_ucast of_bl_drop' bitwise_add_def[symmetric] length_foldr_bitwise_add bitwise_add_take[symmetric] )
  thus ?thesis
    using word_bl.Rep_eqD
    by blast
qed

lemmas take_bits_plus_32bit[simp] =
  take_bits_plus_32bit_generic[of a b]
  take_bits_plus_32bit_generic[of 1 b]
  for a b


lemma take_bits_plus_16bit_generic:
  fixes a b :: "'c::len0 word"
  assumes "LENGTH('c) \<ge> LENGTH('b)"
      and "LENGTH('c) > 16"
  shows "((\<langle>15,0\<rangle>(a + b)) :: 'b ::len0 word) = ucast (((\<langle>15,0\<rangle>a)::16 word) + ((\<langle>15,0\<rangle>b)::16 word))"
proof-
  have "to_bl ((\<langle>15,0\<rangle>(a + b)) :: 'b ::len0 word) = to_bl ((ucast (((\<langle>15,0\<rangle>a)::16 word) + ((\<langle>15,0\<rangle>b)::16 word)) ::'b::len0 word))"
    using assms
    unfolding take_bits_def
    apply (auto simp add: to_bl_plus_carry word_rep_drop length_foldr_bitwise_add drop_zip[symmetric] rev_drop bitwise_add_def to_bl_ucast simp del: foldr_replicate foldr_append)
    apply (simp only: bitwise_add_def[symmetric] length_foldr_bitwise_add)
    by (auto simp add: drop_take rev_take  to_bl_ucast of_bl_drop' bitwise_add_def[symmetric] length_foldr_bitwise_add bitwise_add_take[symmetric] )
  thus ?thesis
    using word_bl.Rep_eqD
    by blast
qed

lemmas take_bits_plus_16bit[simp] = 
  take_bits_plus_16bit_generic[of a b]
  take_bits_plus_16bit_generic[of 1 b]
  for a b

lemma take_bits_plus_8bit_generic:
  fixes a b :: "'c::len0 word"
  assumes "LENGTH('c) \<ge> LENGTH('b)"
      and "LENGTH('c) > 8"
  shows "((\<langle>7,0\<rangle>(a + b)) :: 'b ::len0 word) = ucast (((\<langle>7,0\<rangle>a)::8 word) + ((\<langle>7,0\<rangle>b)::8 word))"
proof-
  have "to_bl ((\<langle>7,0\<rangle>(a + b)) :: 'b ::len0 word) = to_bl ((ucast (((\<langle>7,0\<rangle>a)::8 word) + ((\<langle>7,0\<rangle>b)::8 word)) ::'b::len0 word))"
    using assms
    unfolding take_bits_def
    apply (auto simp add: to_bl_plus_carry word_rep_drop length_foldr_bitwise_add drop_zip[symmetric] rev_drop bitwise_add_def to_bl_ucast simp del: foldr_replicate foldr_append)
    apply (simp only: bitwise_add_def[symmetric] length_foldr_bitwise_add)
    by (auto simp add: drop_take rev_take  to_bl_ucast of_bl_drop' bitwise_add_def[symmetric] length_foldr_bitwise_add bitwise_add_take[symmetric] )
  thus ?thesis
    using word_bl.Rep_eqD
    by blast
qed

lemmas take_bits_plus_8bit[simp] = 
  take_bits_plus_8bit_generic[of a b]
  take_bits_plus_8bit_generic[of 1 b]
  for a b



lemma take_bits_minus:
  fixes a b :: "'a::len word"
  assumes "LENGTH('a) > LENGTH('b)"
      and "h = LENGTH('b) - 1"
  shows "((\<langle>h,0\<rangle>(a - b)) :: 'b ::len word) = \<langle>h,0\<rangle>a - \<langle>h,0\<rangle>b"
proof-
  have "to_bl (word_succ (NOT ((of_bl (drop (LENGTH('a) - LENGTH('b)) (to_bl b)))::'b::len word))) = drop (LENGTH('a) - LENGTH('b)) (to_bl ((word_succ (NOT b))::'a::len word)  )"
    using assms
    apply (auto simp add: of_bl_drop' ucast_bl[symmetric] word_succ_p1 to_bl_plus_carry)
    by (auto simp add: bl_word_not drop_map assms(1) less_imp_le_nat to_bl_ucast Suc_leI drop_zip
           bitwise_add_def[symmetric] length_foldr_bitwise_add drop_rev len_bin_to_bl_aux bitwise_add_take take_rev bin_to_bl_zero_aux)
  hence "to_bl ((\<langle>h,0\<rangle>(a - b)) :: 'b::len word) = to_bl (((\<langle>h,0\<rangle>a)::'b::len word) - \<langle>h,0\<rangle>b)"
    using assms
    apply (simp only: take_bits_def bl_word_sub twos_complement)
    apply (auto simp add: take_bits_def to_bl_plus_carry word_rep_drop length_foldr_bitwise_add drop_zip[symmetric] rev_drop bitwise_add_def min_def)
    apply (auto simp add: bitwise_add_def[symmetric] length_foldr_bitwise_add )
    by (metis (no_types, lifting) bitwise_add_def bitwise_add_take length_rev rev_take to_bl_plus_carry word_bl_Rep')
  thus ?thesis
    using word_bl.Rep_eqD
    by blast
qed

lemmas take_bits_minus_64bit[simp] =
  take_bits_minus[of 63 a b, where 'b=64, simplified]
  take_bits_minus[of 63 1 b, where 'b=64, simplified]
for a b


lemma take_bits_minus_bit32_generic:
  fixes a b :: "'c::len word"
  assumes "LENGTH('c) \<ge> LENGTH('b)"
      and "LENGTH('c) > 32"
  shows "((\<langle>31,0\<rangle>(a - b)) :: 'b ::len word) = ucast (((\<langle>31,0\<rangle>a)::32 word) - ((\<langle>31,0\<rangle>b)::32 word))"
proof-
  {
    fix a :: "'x ::len word"
    and b :: "'y ::len word"
    assume "LENGTH('y) \<ge> LENGTH('x)"
    hence "to_bl (1 :: 'x::len word) = drop (LENGTH('y) - LENGTH('x)) (to_bl (1::'y::len word))"
      apply auto
      by (metis One_nat_def bin_to_bl_aux_one_minus_simp diff_diff_cancel drop_Nil drop_bin2bl_aux len_gt_0)
  }
  note 0 = this
  hence "to_bl (1:: 32 word) = drop (LENGTH('c) - 32) (to_bl (1::'c::len word))"
    using assms 0[where 'x=32 and 'y='c]
    by auto
  hence 1: "to_bl ((word_succ (NOT ((of_bl (to_bl b))::32 word)))::32 word) = drop (LENGTH('c) - 32) (to_bl (word_succ (NOT b)))"
    using assms            
    apply (auto simp add: of_bl_drop' ucast_bl[symmetric] word_succ_p1 to_bl_plus_carry simp del: to_bl_one)
    by (auto simp add: bitwise_add_def[symmetric] bl_word_not to_bl_ucast drop_map[symmetric] drop_zip[symmetric] rev_drop
              bitwise_add_take[symmetric] rev_take length_foldr_bitwise_add simp del: to_bl_one)
  hence "to_bl ((\<langle>31,0\<rangle>(a - b)) :: 'b ::len word) = to_bl ((ucast (((\<langle>31,0\<rangle>a)::32 word) - ((\<langle>31,0\<rangle>b)::32 word)) ::'b::len word))"
    using assms
    apply (auto simp add: take_bits_def bl_word_sub twos_complement to_bl_plus_carry word_rep_drop length_foldr_bitwise_add drop_zip[symmetric] rev_drop bitwise_add_def to_bl_ucast simp del: foldr_replicate foldr_append)
    by (simp add: bitwise_add_def[symmetric] length_foldr_bitwise_add of_bl_drop' drop_zip[symmetric] rev_drop bitwise_add_take[symmetric] rev_take)
  thus ?thesis
    using word_bl.Rep_eqD
    by blast
qed

lemmas take_bits_minus_32bit[simp] =
  take_bits_minus_bit32_generic[of a b]
  take_bits_minus_bit32_generic[of 1 b]
  for a b


lemma take_bits_minus_bit16_generic:
  fixes a b :: "'c::len word"
  assumes "LENGTH('c) \<ge> LENGTH('b)"
      and "LENGTH('c) > 16"
  shows "((\<langle>15,0\<rangle>(a - b))::'b::len word) = ucast (((\<langle>15,0\<rangle>a)::16 word) - ((\<langle>15,0\<rangle>b)::16 word))"
proof -
  {
    fix a :: "'x::len word"
    and b :: "'y::len word"
    assume "LENGTH('y) \<ge> LENGTH('x)"
    hence "to_bl (1::'x::len word) = drop (LENGTH('y) - LENGTH('x)) (to_bl (1::'y::len word))"
      apply auto
      by (metis One_nat_def bin_to_bl_aux_one_minus_simp diff_diff_cancel drop_Nil drop_bin2bl_aux len_gt_0)
  }
  note 0 = this
  hence "to_bl (1::16 word) = drop (LENGTH('c) - 16) (to_bl (1::'c::len word))"
    using assms 0[where 'x=16 and 'y='c]
    by auto
  hence 1: "to_bl ((word_succ (NOT ((of_bl (to_bl b))::16 word)))::16 word) = drop (LENGTH('c) - 16) (to_bl (word_succ (NOT b)))"
    using assms            
    apply (auto simp add: of_bl_drop' ucast_bl[symmetric] word_succ_p1 to_bl_plus_carry simp del: to_bl_one)
    by (auto simp add: bitwise_add_def[symmetric] bl_word_not to_bl_ucast drop_map[symmetric] drop_zip[symmetric] rev_drop
              bitwise_add_take[symmetric] rev_take length_foldr_bitwise_add simp del: to_bl_one)
  hence "to_bl ((\<langle>15,0\<rangle>(a - b))::'b::len word) = to_bl ((ucast (((\<langle>15,0\<rangle>a)::16 word) - ((\<langle>15,0\<rangle>b)::16 word))::'b::len word))"
    using assms
    apply (auto simp add: take_bits_def bl_word_sub twos_complement to_bl_plus_carry word_rep_drop length_foldr_bitwise_add drop_zip[symmetric] rev_drop bitwise_add_def to_bl_ucast simp del: foldr_replicate foldr_append)
    by (simp add: bitwise_add_def[symmetric] length_foldr_bitwise_add of_bl_drop' drop_zip[symmetric] rev_drop bitwise_add_take[symmetric] rev_take)
  thus ?thesis
    using word_bl.Rep_eqD
    by blast
qed


lemmas take_bits_minus_16bit[simp] =
  take_bits_minus_bit16_generic[of a b]
  take_bits_minus_bit16_generic[of 1 b]
  for a b

lemma take_bits_minus_bit8_generic:
  fixes a b :: "'c::len word"
  assumes "LENGTH('c) \<ge> LENGTH('b)"
      and "LENGTH('c) > 8"
  shows "((\<langle>7,0\<rangle>(a - b))::'b::len word) = ucast (((\<langle>7,0\<rangle>a)::8 word) - ((\<langle>7,0\<rangle>b)::8 word))"
proof -
  {
    fix a :: "'x::len word"
    and b :: "'y::len word"
    assume "LENGTH('y) \<ge> LENGTH('x)"
    hence "to_bl (1::'x::len word) = drop (LENGTH('y) - LENGTH('x)) (to_bl (1::'y::len word))"
      apply auto
      by (metis One_nat_def bin_to_bl_aux_one_minus_simp diff_diff_cancel drop_Nil drop_bin2bl_aux len_gt_0)
  }
  note 0 = this
  hence "to_bl (1::8 word) = drop (LENGTH('c) - 8) (to_bl (1::'c::len word))"
    using assms 0[where 'x=8 and 'y='c]
    by auto
  hence 1: "to_bl ((word_succ (NOT ((of_bl (to_bl b))::8 word)))::8 word) = drop (LENGTH('c) - 8) (to_bl (word_succ (NOT b)))"
    using assms            
    apply (auto simp add: of_bl_drop' ucast_bl[symmetric] word_succ_p1 to_bl_plus_carry simp del: to_bl_one)
    by (auto simp add: bitwise_add_def[symmetric] bl_word_not to_bl_ucast drop_map[symmetric] drop_zip[symmetric] rev_drop
              bitwise_add_take[symmetric] rev_take length_foldr_bitwise_add simp del: to_bl_one)
  hence "to_bl ((\<langle>7,0\<rangle>(a - b))::'b::len word) = to_bl ((ucast (((\<langle>7,0\<rangle>a)::8 word) - ((\<langle>7,0\<rangle>b)::8 word))::'b::len word))"
    using assms
    apply (auto simp add: take_bits_def bl_word_sub twos_complement to_bl_plus_carry word_rep_drop length_foldr_bitwise_add drop_zip[symmetric] rev_drop bitwise_add_def to_bl_ucast simp del: foldr_replicate foldr_append)
    by (simp add: bitwise_add_def[symmetric] length_foldr_bitwise_add of_bl_drop' drop_zip[symmetric] rev_drop bitwise_add_take[symmetric] rev_take)
  thus ?thesis
    using word_bl.Rep_eqD
    by blast
qed

lemmas take_bits_minus_8bit[simp] =
  take_bits_minus_bit8_generic[of a b]
  take_bits_minus_bit8_generic[of 1 b]
  for a b


subsection \<open>Take bits and comparison\<close>

lemma rev_bl_order_take:
  assumes "\<forall> i \<ge> n . i < length x \<longrightarrow> x ! i = False"
      and "\<forall> i \<ge> n . i < length y \<longrightarrow> y ! i = False"
      and "length x = length y"
    shows "rev_bl_order b x y = (if n = 0 then b else rev_bl_order b (take n x) (take n y))"
proof(cases "n=0")
  case True
  {
    fix i :: nat
    assume "i < length x"
    hence "x ! i = y ! i"
      using assms True
      by auto
  }
  hence "x = y"
    using assms
    apply (intro nth_equalityI)
    by auto
  thus ?thesis
    using assms
    unfolding rev_bl_order_def
    by auto
next
  case False
  have "length (take n x) = length (take n y)"
    using assms
    by (auto simp add: min_def)
  moreover
  {
    assume "x=y" and b
    hence "take n x = take n y \<and> b"
      by auto
  }
  moreover
  {
    assume "\<exists>n<length x. drop (Suc n) x = drop (Suc n) y \<and> \<not> x ! n \<and> y ! n"
    then obtain m where m: "m<length x \<and> drop (Suc m) x = drop (Suc m) y \<and> \<not> x ! m \<and> y ! m"
      by auto
    hence "m < n"
      using assms leI
      apply auto
      by blast
    hence "m<length (take n x) \<and> drop (Suc m) (take n x) = drop (Suc m) (take n y) \<and> \<not> take n x ! m \<and> take n y ! m"
      using m False
      by (auto simp add: drop_take)
    hence "\<exists>na<length (take n x). drop (Suc na) (take n x) = drop (Suc na) (take n y) \<and> \<not> take n x ! na \<and> take n y ! na"
      by auto
  }
  moreover
  {
    assume 1: "take n x = take n y"
       and 2: b
    {
      fix i :: nat
      assume "i < length x"
      hence "x ! i = y ! i"
        using assms 1
        apply (cases "i \<ge> n",auto)
        by (metis leI nth_take)+
    }
    hence "x = y"
      using assms
      apply (intro nth_equalityI)
      by auto
  }
  moreover
  {
    assume "(\<exists>na<length (take n x). drop (Suc na) (take n x) = drop (Suc na) (take n y) \<and> \<not> take n x ! na \<and> take n y ! na)"
    then obtain m where m: "m < length (take n x) \<and> drop (Suc m) (take n x) = drop (Suc m) (take n y) \<and> \<not> take n x ! m \<and> take n y ! m"
      by auto
    {
      fix i :: nat
      assume 1: "i < length (drop (Suc m) x)"
      have "Suc (m + i) < n \<Longrightarrow> x ! Suc (m + i) = drop (Suc m) (take n x) ! i"
        using 1 
        by auto        
      hence "(drop (Suc m) x) ! i = (drop (Suc m) y) ! i"
        using 1 m assms
        by (cases "Suc (m + i) < n",auto simp add: drop_take)
    }
    hence "(drop (Suc m) x) = (drop (Suc m) y)"
      using assms
      apply (intro nth_equalityI)
      by (auto)
    hence "m < length x \<and> drop (Suc m) x = drop (Suc m) y \<and> \<not> x ! m \<and> y ! m"
      using m
      by auto
    hence "\<exists>n<length x. drop (Suc n) x = drop (Suc n) y \<and> \<not> x ! n \<and> y ! n"
      by auto
  }
  ultimately
  show ?thesis
    using assms False
    unfolding rev_bl_order_def
    by auto
qed

lemma take_bits_lt_bit32:
  fixes a :: "'b::len0 word"
    and b :: "'c::len0 word"
  assumes "32 \<le> LENGTH('a)"
      and "32 \<le> LENGTH('b)"
      and "32 \<le> LENGTH('c)"
  shows "(((\<langle>31,0\<rangle>a)::'a::len0 word) < ((\<langle>31,0\<rangle>b)::'a::len0 word)) = (((\<langle>31,0\<rangle>a)::32 word) < ((\<langle>31,0\<rangle>b)::32 word))"
proof-
  have 1: "\<forall>i\<ge>32. i < length (rev (to_bl ((\<langle>31,0\<rangle>a)::'a::len0 word))) \<longrightarrow> \<not>rev (to_bl ((\<langle>31,0\<rangle>a)::'a::len0 word)) ! i"
    using assms
    by (auto simp add: rev_nth test_bit_of_take_bits to_bl_nth word_size)
  have 2: "\<forall>i\<ge>32. i < length (rev (to_bl ((\<langle>31,0\<rangle>b)::'a::len0 word))) \<longrightarrow> \<not>rev (to_bl ((\<langle>31,0\<rangle>b)::'a::len0 word)) ! i"
    using assms
    by (auto simp add: rev_nth test_bit_of_take_bits to_bl_nth word_size)
  have 3: "\<And> a ::'b::len0 word . take 32 (rev (to_bl ((\<langle>31,0\<rangle>a)::'a::len0 word))) = rev (to_bl ((\<langle>31,0\<rangle>a)::32 word))"
  proof-
    fix a :: "'b::len0 word"
    {
      fix i :: nat
      assume "i < 32"
      hence "take 32 (rev (to_bl ((\<langle>31,0\<rangle>a)::'a::len0 word))) ! i = rev (to_bl ((\<langle>31,0\<rangle>a)::32 word)) ! i"
        using assms
        by (auto simp add: rev_nth to_bl_nth word_size test_bit_of_take_bits)
    }
    thus "?thesis a"
      using assms
      apply (intro nth_equalityI)
      by (auto)
  qed
  have 4: "\<And> a ::'c::len0 word . take 32 (rev (to_bl ((\<langle>31,0\<rangle>a)::'a::len0 word))) = rev (to_bl ((\<langle>31,0\<rangle>a)::32 word))"
  proof-
    fix a :: "'c::len0 word"
    {
      fix i :: nat
      assume "i < 32"
      hence "take 32 (rev (to_bl ((\<langle>31,0\<rangle>a)::'a::len0 word))) ! i = rev (to_bl ((\<langle>31,0\<rangle>a)::32 word)) ! i"
        using assms
        by (auto simp add: rev_nth to_bl_nth word_size test_bit_of_take_bits)
    }
    thus "?thesis a"
      using assms
      apply (intro nth_equalityI)
      by (auto)
  qed

  show ?thesis
    apply (auto simp add: word_less_rbl)
    apply (subst (asm) rev_bl_order_take[of 32])
    using 1 2 3 4
    apply auto
    apply (subst rev_bl_order_take[of 32])
    using 1 2 3 4
    by auto
qed


lemma take_bits_le_bit32:
  fixes a :: "'b::len0 word"
    and b :: "'c::len0 word"
  assumes "32 \<le> LENGTH('a)"
      and "32 \<le> LENGTH('b)"
      and "32 \<le> LENGTH('c)"
  shows "(((\<langle>31,0\<rangle>a)::'a::len0 word) \<le> ((\<langle>31,0\<rangle>b)::'a::len0 word)) = (((\<langle>31,0\<rangle>a)::32 word) \<le> ((\<langle>31,0\<rangle>b)::32 word))"
proof-
  have "(((\<langle>31,0\<rangle>a)::'a::len0 word) = ((\<langle>31,0\<rangle>b)::'a::len0 word)) = (((\<langle>31,0\<rangle>a)::32 word) = ((\<langle>31,0\<rangle>b)::32 word))"
  proof-
    {
      assume "(((\<langle>31,0\<rangle>a)::'a::len0 word) = ((\<langle>31,0\<rangle>b)::'a::len0 word))"
      hence "\<forall> i < 32 . (((\<langle>31,0\<rangle>a)::'a::len0 word) !! i = (((\<langle>31,0\<rangle>b)::'a::len0 word)) !! i)"
        using assms
        by (auto simp add: test_bit_of_take_bits)
      hence "\<forall> i < 32 . (((\<langle>31,0\<rangle>a)::32 word) !! i = (((\<langle>31,0\<rangle>b)::32 word)) !! i)"
        using assms
        by (auto simp add: test_bit_of_take_bits)
      hence "(((\<langle>31,0\<rangle>a)::32 word) = ((\<langle>31,0\<rangle>b)::32 word))"
        apply (intro word_eqI)
        by (auto simp add: word_size)
    }
    moreover
    {
      assume "(((\<langle>31,0\<rangle>a)::32 word) = ((\<langle>31,0\<rangle>b)::32 word))"
      hence "\<forall> i < 32 . (((\<langle>31,0\<rangle>a)::32 word) !! i = (((\<langle>31,0\<rangle>b)::32 word)) !! i)"
        using assms
        by (auto simp add: test_bit_of_take_bits)
      hence "\<forall> i < LENGTH('a) . (((\<langle>31,0\<rangle>a)::'a::len0 word) !! i = (((\<langle>31,0\<rangle>b)::'a::len0 word)) !! i)"
        using assms
        by (auto simp add: test_bit_of_take_bits)
      hence "(((\<langle>31,0\<rangle>a)::'a::len0 word) = ((\<langle>31,0\<rangle>b)::'a::len0 word))"
        using assms
        apply (intro word_eqI)
        by (auto simp add: word_size)
    }
    ultimately
    show ?thesis
      by auto
  qed
  thus ?thesis
    using assms
    apply (cases "(((\<langle>31,0\<rangle>a)::'a::len0 word) = ((\<langle>31,0\<rangle>b)::'a::len0 word))"; cases "(((\<langle>31,0\<rangle>a)::32 word) = ((\<langle>31,0\<rangle>b)::32 word))";auto)
    by (meson less_imp_le_nat linorder_not_le take_bits_lt_bit32)+
qed



subsection \<open>unat\<close>


lemma unat_bitslice_to_16:
  fixes a :: "'b::len0 word"
  assumes "LENGTH('a) > 16"
      and "LENGTH('b) > 16"
  shows "unat (\<langle>15,0\<rangle>a :: 'a::len0 word) = unat (\<langle>15,0\<rangle>a :: 16 word)"
proof-
  have "unat ((\<langle>15,0\<rangle>a :: 'a::len0 word)) = unat (ucast (\<langle>15,0\<rangle>a :: 16 word) :: 'a::len0 word)"
    using assms
    by auto
  also have "... = unat (\<langle>15,0\<rangle>a :: 16 word)"
    apply (subst unat_ucast)
    using assms
    by (auto simp add: is_up)
  finally
  show ?thesis
    by auto
qed

lemma unat_bitslice_to_8:
  fixes a :: "'b::len0 word"
  assumes "LENGTH('a) > 8"
      and "LENGTH('b) > 8"
  shows "unat (\<langle>7,0\<rangle>a :: 'a::len0 word) = unat (\<langle>7,0\<rangle>a :: 8 word)"
proof-
  have "unat ((\<langle>7,0\<rangle>a :: 'a::len0 word)) = unat (ucast (\<langle>7,0\<rangle>a :: 8 word) :: 'a::len0 word)"
    using assms
    by auto
  also have "... = unat (\<langle>7,0\<rangle>a :: 8 word)"
    apply (subst unat_ucast)
    using assms
    by (auto simp add: is_up)
  finally
  show ?thesis
    by auto
qed

lemma rewrite_take_bits_is_0_bit16: (* Do not add to simplifier, can introduce infinite rewrite loop *)
  fixes a :: "'b::len0 word"
  assumes "LENGTH('b) > 16"
      and "LENGTH('a) \<ge> LENGTH('b)"
  shows "\<langle>15,0\<rangle>a = (0::'a::len0 word) \<longleftrightarrow> \<langle>15,0\<rangle>a = (0 :: 16 word)"
  apply unat_arith
  using assms
  apply (auto)
  apply (smt le_antisym le_trans less_or_eq_imp_le linorder_neqE_nat unat_0 unat_bitslice_to_16)
  by (smt less_le_trans unat_bitslice_to_16 unat_eq_0)

lemma rewrite_take_bits_is_0_bit8: (* Do not add to simplifier, can introduce infinite rewrite loop *)
  fixes a :: "'b::len0 word"
  assumes "LENGTH('b) > 8"
      and "LENGTH('a) \<ge> LENGTH('b)"
  shows "\<langle>7,0\<rangle>a = (0::'a::len0 word) \<longleftrightarrow> \<langle>7,0\<rangle>a = (0 :: 8 word)"
  apply unat_arith
  using assms
  apply (auto)
  apply (smt le_antisym le_trans less_or_eq_imp_le linorder_neqE_nat unat_0 unat_bitslice_to_8)
  by (smt less_le_trans unat_bitslice_to_8 unat_eq_0)

lemma unat_bit_slice_le_bit8:
  fixes a :: "'a::len0 word"
  assumes "8 < LENGTH('a)"
      and "LENGTH('b) \<ge> LENGTH('a)"
  shows "unat (\<langle>7,0\<rangle>a :: 'b::len0 word) < 2^(7+1)"
proof-
  have "unat (\<langle>7,0\<rangle>a :: 'b::len0 word) = unat (\<langle>7,0\<rangle>a ::8 word)"
    using unat_bitslice_to_8[of a,where 'a='b] assms
    by auto
  thus ?thesis
    apply unat_arith
    by auto
qed

end
