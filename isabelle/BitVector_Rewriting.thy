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

theory BitVector_Rewriting
  imports reassembly_rewriting.Take_Bits_Rewriting reassembly_manual_execution.BitVectors
begin


subsection \<open>Logical Operators\<close>

lemma bv_to_bool_bool_to_bv:
  shows "bv_to_bool (bool_to_bv b) = b"
  by (cases b,auto simp add: bv_to_bool_def)
      
lemma snd_bool_to_bv:
  shows "snd (bool_to_bv b) = 1"
  by (cases b,auto)

lemma bv_to_bool_True:
  shows "bv_to_bool (1, 1) = True"
  by (auto simp add: bv_to_bool_def)

lemma bv_to_bool_True_Suc0:
  shows "bv_to_bool (1, Suc 0) = True"
  by (auto simp add: bv_to_bool_def)

lemma bv_to_bool_False:
  shows "bv_to_bool (0, 1) = False"
  by (auto simp add: bv_to_bool_def)

lemma bv_to_bool_False_Suc0:
  shows "bv_to_bool (0, Suc 0) = False"
  by (auto simp add: bv_to_bool_def)


lemma bool_to_bv_eq:
  shows "bool_to_bv b = (x, Suc 0) \<longleftrightarrow> (x \<in> {0,1} \<and> ((x = 1) \<longleftrightarrow> b))"
  by (cases b,auto)

lemma bv_NOT_bool_to_bv:
  shows "bv_NOT (bool_to_bv b) = bool_to_bv (\<not>b)"
  by (cases b, auto simp add: max_word_def) 



subsection \<open>Concatenation and slicing\<close>



lemmas bv_slice_simps[simp] =
  bv_slice.simps[of "numeral h" "numeral l" "numeral w" "numeral s"]
  bv_slice.simps[of "numeral h" "numeral l" "numeral w" 0]
  bv_slice.simps[of "numeral h" "numeral l" "numeral w" 1]
  bv_slice.simps[of "numeral h" "numeral l" 0            "numeral s"]
  bv_slice.simps[of "numeral h" "numeral l" 0            0]
  bv_slice.simps[of "numeral h" "numeral l" 0            1]
  bv_slice.simps[of "numeral h" "numeral l" 1            "numeral s"]
  bv_slice.simps[of "numeral h" "numeral l" 1            0]
  bv_slice.simps[of "numeral h" "numeral l" 1            1]
  bv_slice.simps[of "numeral h" 0            "numeral w" "numeral s"]
  bv_slice.simps[of "numeral h" 0            "numeral w" 0]
  bv_slice.simps[of "numeral h" 0            "numeral w" 1]
  bv_slice.simps[of "numeral h" 0            0            "numeral s"]
  bv_slice.simps[of "numeral h" 0            0            0]
  bv_slice.simps[of "numeral h" 0            0            1]
  bv_slice.simps[of "numeral h" 0            1            "numeral s"]
  bv_slice.simps[of "numeral h" 0            1            0]
  bv_slice.simps[of "numeral h" 0            1            1]
  bv_slice.simps[of "numeral h" 1            "numeral w" "numeral s"]
  bv_slice.simps[of "numeral h" 1            "numeral w" 0]
  bv_slice.simps[of "numeral h" 1            "numeral w" 1]
  bv_slice.simps[of "numeral h" 1            0            "numeral s"]
  bv_slice.simps[of "numeral h" 1            0            0]
  bv_slice.simps[of "numeral h" 1            0            1]
  bv_slice.simps[of "numeral h" 1            1            "numeral s"]
  bv_slice.simps[of "numeral h" 1            1            0]
  bv_slice.simps[of "numeral h" 1            1            1]
  bv_slice.simps[of 0           "numeral l" "numeral w" "numeral s"]
  bv_slice.simps[of 0           "numeral l" "numeral w" 0]
  bv_slice.simps[of 0           "numeral l" "numeral w" 1]
  bv_slice.simps[of 0           "numeral l" 0            "numeral s"]
  bv_slice.simps[of 0           "numeral l" 0            0]
  bv_slice.simps[of 0           "numeral l" 0            1]
  bv_slice.simps[of 0           "numeral l" 1            "numeral s"]
  bv_slice.simps[of 0           "numeral l" 1            0]
  bv_slice.simps[of 0           "numeral l" 1            1]
  bv_slice.simps[of 0           0            "numeral w" "numeral s"]
  bv_slice.simps[of 0           0            "numeral w" 0]
  bv_slice.simps[of 0           0            "numeral w" 1]
  bv_slice.simps[of 0           0            0            "numeral s"]
  bv_slice.simps[of 0           0            0            0]
  bv_slice.simps[of 0           0            0            1]
  bv_slice.simps[of 0           0            1            "numeral s"]
  bv_slice.simps[of 0           0            1            0]
  bv_slice.simps[of 0           0            1            1]
  bv_slice.simps[of 0           1            "numeral w" "numeral s"]
  bv_slice.simps[of 0           1            "numeral w" 0]
  bv_slice.simps[of 0           1            "numeral w" 1]
  bv_slice.simps[of 0           1            0            "numeral s"]
  bv_slice.simps[of 0           1            0            0]
  bv_slice.simps[of 0           1            0            1]
  bv_slice.simps[of 0           1            1            "numeral s"]
  bv_slice.simps[of 0           1            1            0]
  bv_slice.simps[of 0           1            1            1]
  bv_slice.simps[of 1           "numeral l" "numeral w" "numeral s"]
  bv_slice.simps[of 1           "numeral l" "numeral w" 0]
  bv_slice.simps[of 1           "numeral l" "numeral w" 1]
  bv_slice.simps[of 1           "numeral l" 0            "numeral s"]
  bv_slice.simps[of 1           "numeral l" 0            0]
  bv_slice.simps[of 1           "numeral l" 0            1]
  bv_slice.simps[of 1           "numeral l" 1            "numeral s"]
  bv_slice.simps[of 1           "numeral l" 1            0]
  bv_slice.simps[of 1           "numeral l" 1            1]
  bv_slice.simps[of 1           0            "numeral w" "numeral s"]
  bv_slice.simps[of 1           0            "numeral w" 0]
  bv_slice.simps[of 1           0            "numeral w" 1]
  bv_slice.simps[of 1           0            0            "numeral s"]
  bv_slice.simps[of 1           0            0            0]
  bv_slice.simps[of 1           0            0            1]
  bv_slice.simps[of 1           0            1            "numeral s"]
  bv_slice.simps[of 1           0            1            0]
  bv_slice.simps[of 1           0            1            1]
  bv_slice.simps[of 1           1            "numeral w" "numeral s"]
  bv_slice.simps[of 1           1            "numeral w" 0]
  bv_slice.simps[of 1           1            "numeral w" 1]
  bv_slice.simps[of 1           1            0            "numeral s"]
  bv_slice.simps[of 1           1            0            0]
  bv_slice.simps[of 1           1            0            1]
  bv_slice.simps[of 1           1            1            "numeral s"]
  bv_slice.simps[of 1           1            1            0]
  bv_slice.simps[of 1           1            1            1]
  for h l w s

lemmas bv_cat_simps[simp] =
  bv_cat.simps[of "numeral w0" "numeral s0" "numeral w1" "numeral s1"]
  bv_cat.simps[of "numeral w0" "numeral s0" "numeral w1" 0]
  bv_cat.simps[of "numeral w0" "numeral s0" "numeral w1" 1]
  bv_cat.simps[of "numeral w0" "numeral s0" 0            "numeral s1"]
  bv_cat.simps[of "numeral w0" "numeral s0" 0            0]
  bv_cat.simps[of "numeral w0" "numeral s0" 0            1]
  bv_cat.simps[of "numeral w0" "numeral s0" 1            "numeral s1"]
  bv_cat.simps[of "numeral w0" "numeral s0" 1            0]
  bv_cat.simps[of "numeral w0" "numeral s0" 1            1]
  bv_cat.simps[of "numeral w0" 0            "numeral w1" "numeral s1"]
  bv_cat.simps[of "numeral w0" 0            "numeral w1" 0]
  bv_cat.simps[of "numeral w0" 0            "numeral w1" 1]
  bv_cat.simps[of "numeral w0" 0            0            "numeral s1"]
  bv_cat.simps[of "numeral w0" 0            0            0]
  bv_cat.simps[of "numeral w0" 0            0            1]
  bv_cat.simps[of "numeral w0" 0            1            "numeral s1"]
  bv_cat.simps[of "numeral w0" 0            1            0]
  bv_cat.simps[of "numeral w0" 0            1            1]
  bv_cat.simps[of "numeral w0" 1            "numeral w1" "numeral s1"]
  bv_cat.simps[of "numeral w0" 1            "numeral w1" 0]
  bv_cat.simps[of "numeral w0" 1            "numeral w1" 1]
  bv_cat.simps[of "numeral w0" 1            0            "numeral s1"]
  bv_cat.simps[of "numeral w0" 1            0            0]
  bv_cat.simps[of "numeral w0" 1            0            1]
  bv_cat.simps[of "numeral w0" 1            1            "numeral s1"]
  bv_cat.simps[of "numeral w0" 1            1            0]
  bv_cat.simps[of "numeral w0" 1            1            1]
  bv_cat.simps[of 0           "numeral s0" "numeral w1" "numeral s1"]
  bv_cat.simps[of 0           "numeral s0" "numeral w1" 0]
  bv_cat.simps[of 0           "numeral s0" "numeral w1" 1]
  bv_cat.simps[of 0           "numeral s0" 0            "numeral s1"]
  bv_cat.simps[of 0           "numeral s0" 0            0]
  bv_cat.simps[of 0           "numeral s0" 0            1]
  bv_cat.simps[of 0           "numeral s0" 1            "numeral s1"]
  bv_cat.simps[of 0           "numeral s0" 1            0]
  bv_cat.simps[of 0           "numeral s0" 1            1]
  bv_cat.simps[of 0           0            "numeral w1" "numeral s1"]
  bv_cat.simps[of 0           0            "numeral w1" 0]
  bv_cat.simps[of 0           0            "numeral w1" 1]
  bv_cat.simps[of 0           0            0            "numeral s1"]
  bv_cat.simps[of 0           0            0            0]
  bv_cat.simps[of 0           0            0            1]
  bv_cat.simps[of 0           0            1            "numeral s1"]
  bv_cat.simps[of 0           0            1            0]
  bv_cat.simps[of 0           0            1            1]
  bv_cat.simps[of 0           1            "numeral w1" "numeral s1"]
  bv_cat.simps[of 0           1            "numeral w1" 0]
  bv_cat.simps[of 0           1            "numeral w1" 1]
  bv_cat.simps[of 0           1            0            "numeral s1"]
  bv_cat.simps[of 0           1            0            0]
  bv_cat.simps[of 0           1            0            1]
  bv_cat.simps[of 0           1            1            "numeral s1"]
  bv_cat.simps[of 0           1            1            0]
  bv_cat.simps[of 0           1            1            1]
  bv_cat.simps[of 1           "numeral s0" "numeral w1" "numeral s1"]
  bv_cat.simps[of 1           "numeral s0" "numeral w1" 0]
  bv_cat.simps[of 1           "numeral s0" "numeral w1" 1]
  bv_cat.simps[of 1           "numeral s0" 0            "numeral s1"]
  bv_cat.simps[of 1           "numeral s0" 0            0]
  bv_cat.simps[of 1           "numeral s0" 0            1]
  bv_cat.simps[of 1           "numeral s0" 1            "numeral s1"]
  bv_cat.simps[of 1           "numeral s0" 1            0]
  bv_cat.simps[of 1           "numeral s0" 1            1]
  bv_cat.simps[of 1           0            "numeral w1" "numeral s1"]
  bv_cat.simps[of 1           0            "numeral w1" 0]
  bv_cat.simps[of 1           0            "numeral w1" 1]
  bv_cat.simps[of 1           0            0            "numeral s1"]
  bv_cat.simps[of 1           0            0            0]
  bv_cat.simps[of 1           0            0            1]
  bv_cat.simps[of 1           0            1            "numeral s1"]
  bv_cat.simps[of 1           0            1            0]
  bv_cat.simps[of 1           0            1            1]
  bv_cat.simps[of 1           1            "numeral w1" "numeral s1"]
  bv_cat.simps[of 1           1            "numeral w1" 0]
  bv_cat.simps[of 1           1            "numeral w1" 1]
  bv_cat.simps[of 1           1            0            "numeral s1"]
  bv_cat.simps[of 1           1            0            0]
  bv_cat.simps[of 1           1            0            1]
  bv_cat.simps[of 1           1            1            "numeral s1"]
  bv_cat.simps[of 1           1            1            0]
  bv_cat.simps[of 1           1            1            1]
  for w0 s0 w1 s1

lemma size_bv_cat:
  shows "snd (bv_cat a b) = snd a + snd b"
  by (cases a,cases b,auto simp add: bv_cat.simps)

lemma size_bv_slice:
  shows "snd (bv_slice h l a) = h + 1 - l"
  by (cases a,auto simp add: bv_slice.simps)

lemma bv_cat_prepend_0:
  fixes a :: "'a::len word"
  assumes "s < LENGTH('a)"
  shows "bv_cat (0, s') (a,s) = (if s = 0 then 0 else \<langle>s-1,0\<rangle>a,s + s')"
proof(cases "s = 0")
  case True
  thus ?thesis
    by (auto simp add: bv_cat.simps)
next
  case False
  {
    fix b :: "'a::len word"
    assume b: "b=0"
    {
      fix n::nat
      assume n: "n < LENGTH('a)"  
      {
        fix x h l :: nat
        {
          fix m :: nat
          assume m: "m < LENGTH('a)"
          hence "\<not> b !! (LENGTH('a) - 1 - m)"
            using b
            by auto
          hence "\<not> to_bl b ! m"
            using m
            by (auto simp add: unfold_test_bit split: if_split_asm)
        }
        hence "\<not>((\<langle>h,l\<rangle>b)::'a::len word) !! x"
          apply (cases "x < LENGTH('a)";cases "h < LENGTH('a)")
          apply (auto simp add: test_bit_of_take_bits)[1]
          using b apply simp
          by (auto simp add: take_bits_def test_bit_bl word_size rev_nth word_rep_drop min_def nth_append)
      }
      note 1 = this
      have "(fst (bv_cat (b, s') (a,s))) !! n= ((\<langle>s-1,0\<rangle>a):: 'a::len word)!!n"
        using assms n 1 False
        apply (auto split: if_split_asm simp add: test_bit_of_take_bits bv_cat.simps word_ao_nth nth_shiftl)
        using b nth_0 by blast
    }
    hence "(fst (bv_cat (b, s') (a,s))) = ((\<langle>s-1,0\<rangle>a):: 'a::len word)"
      and "(snd (bv_cat (b, s') (a,s))) = (s+s')"
      apply (intro word_eqI)
      by (auto simp add: word_size bv_cat.simps)+
  }
  thus ?thesis
    using False
    apply auto
    by (metis prod.exhaust_sel)
qed





lemma test_bit_of_bv_cat:
  fixes a b :: "'a ::len0 word \<times> nat"
  assumes "snd a \<le> LENGTH('a)"
      and "snd b \<le> LENGTH('a)"
      and "i < LENGTH('a)"
    shows "fst (bv_cat a b) !! i = (if i \<ge> snd b then (fst a) !! (i - snd b) else (fst b) !! i)"
  using assms
  by (cases a, cases b,auto simp add: bv_cat.simps test_bit_of_take_bits word_ao_nth nth_shiftl word_size split: if_split_asm)

lemma test_bit_of_bv_slice:
  assumes "h < \<M>"
  shows "fst (bv_slice h l a) !! n = (if n < Suc h - l then fst a!!(l+n) else False)"
  using assms
  apply (cases a, cases "n < \<M>",auto simp add: bv_slice.simps test_bit_of_take_bits)
  by (simp add: word_size test_bit_bin')



lemma bv_slice_bv_cat:
assumes "h < \<M>"
    and "snd a \<le> \<M>"
    and "snd b \<le> \<M>"
  shows "bv_slice h l (bv_cat a b) =
        (if h \<ge> snd b then
          (if l \<ge> snd b then
            bv_slice (h - snd b) (l - snd b) a
           else
            bv_cat (bv_slice (h - snd b) 0 a) (bv_slice (snd b - 1) l b))
        else
          (if l \<ge> snd b then
               (0,0)
           else
              bv_slice h l b))"
proof(cases "h \<ge> snd b")
  case True
  note h = this
  show ?thesis
  proof(cases "l \<ge> snd b")
    case True
    {
      fix i :: nat
      assume "i < \<M>"
      hence "fst (bv_slice h l (bv_cat a b)) !! i = fst (bv_slice (h - snd b) (l - snd b) a) !! i"
        using h True assms
        by (auto simp add: bv_cat.simps test_bit_of_bv_slice nth_ucast test_bit_of_bv_cat split: if_split_asm)
    }
    hence "fst (bv_slice h l (bv_cat a b)) = fst (bv_slice (h - snd b) (l - snd b) a)"
      apply (intro word_eqI)
      by (auto simp add: word_size)
    moreover
    have "snd (bv_slice h l (bv_cat a b)) = snd (bv_slice (h - snd b) (l - snd b) a)"
      using True h
      by (cases a, cases b,auto simp add: size_bv_slice)
    ultimately
    show ?thesis
      using True h
      apply (auto)
      by (metis prod.exhaust_sel)
  next
    case False
    {
      fix i :: nat
      assume "i < \<M>"
      hence "fst (bv_slice h l (bv_cat a b)) !! i = fst (bv_cat (bv_slice (h - snd b) 0 a) (bv_slice (snd b - 1) l b)) !! i"
        using h False assms
        apply (auto simp add: bv_cat.simps nth_ucast test_bit_of_bv_slice test_bit_of_bv_cat word_ao_nth nth_shiftl size_bv_slice split: if_split_asm)
        by (simp add: Groups.add_ac(2))+
    }
    hence "fst (bv_slice h l (bv_cat a b)) = fst (bv_cat (bv_slice (h - snd b) 0 a) (bv_slice (snd b - 1) l b))"
      apply (intro word_eqI)
      by (auto simp add: word_size)
    moreover
    have "snd (bv_slice h l (bv_cat a b)) = snd (bv_cat (bv_slice (h - snd b) 0 a) (bv_slice (snd b - 1) l b))"
      using False h
      by (cases a, cases b,auto simp add: size_bv_slice size_bv_cat)
    ultimately
    show ?thesis
      using False h
      apply (auto)
      by (metis prod.exhaust_sel)
  qed
next
  case False
  note h = this
  show ?thesis
  proof(cases "l \<ge> snd b")
    case True
    {
      fix i :: nat
      assume "i < \<M>"
      hence "fst (bv_slice h l (bv_cat a b)) !! i = (0::longword) !! i"
        using h True assms
        by (auto simp add: bv_cat.simps nth_ucast test_bit_of_bv_slice test_bit_of_bv_cat split: if_split_asm)
    }
    hence "fst (bv_slice h l (bv_cat a b)) = 0"
      apply (intro word_eqI)
      by (auto simp add: word_size)
    moreover
    have "snd (bv_slice h l (bv_cat a b)) = 0"
      using True h
      by (cases a, cases b,auto simp add: size_bv_slice size_bv_cat)
    ultimately
    show ?thesis
      using True h
      apply (auto)
      by (metis prod.exhaust_sel)
  next
    case False
    {
      fix i :: nat
      assume "i < \<M>"
      hence "fst (bv_slice h l (bv_cat a b)) !! i = fst (bv_slice h l b) !! i"
        using h False assms
        by (auto simp add: bv_cat.simps nth_ucast test_bit_of_bv_slice test_bit_of_bv_cat split: if_split_asm)
    }
    hence "fst (bv_slice h l (bv_cat a b)) = fst (bv_slice h l b)"
      apply (intro word_eqI)
      by (auto simp add: word_size)
    moreover
    have "snd (bv_slice h l (bv_cat a b)) = snd (bv_slice h l b)"
      using False h
      by (cases a, cases b,auto simp add: size_bv_slice size_bv_cat)
    ultimately
    show ?thesis
      using False h
      apply (auto)
      by (metis prod.exhaust_sel)
  qed
qed



definition "bv_cat' \<equiv> bv_cat"
lemma take_bits_bv_cat:
  fixes a b :: "'b ::len0 word \<times> nat"
  assumes "h < LENGTH('b)"
      and "snd a \<le> LENGTH('b)"
      and "snd b \<le> LENGTH('b)"
    shows "((\<langle>h,l\<rangle> (fst (bv_cat a b)))::'a::len0 word) =
        (if h \<ge> snd b then
          (if l \<ge> snd b then
            \<langle>h - snd b,l - snd b\<rangle>fst a
           else
            ((\<langle>h,l\<rangle> (fst (bv_cat' a b)))::'a::len0 word))
        else
          (if l \<ge> snd b then
               0
           else
              \<langle>h,l\<rangle> (fst b)))"
proof(cases "h \<ge> snd b")
  case True
  note h = this
  show ?thesis
  proof(cases "l \<ge> snd b")
    case True
    {
      fix i :: nat
      assume "i < LENGTH('a)"
      hence "((\<langle>h,l\<rangle> (fst (bv_cat a b)))::'a::len0 word) !! i = ((\<langle>h - snd b,l - snd b\<rangle>fst a)::'a::len0 word) !! i"
        using h True assms
        by (auto simp add: bv_cat.simps test_bit_of_take_bits nth_ucast test_bit_of_bv_cat split: if_split_asm)
    }
    hence "((\<langle>h,l\<rangle> (fst (bv_cat a b)))::'a::len0 word) = ((\<langle>h - snd b,l - snd b\<rangle>fst a)::'a::len0 word)"
      apply (intro word_eqI)
      by (auto simp add: word_size)
    thus ?thesis
      using True h
      by auto
  next
    case False
    thus ?thesis
      using h
      by (auto simp add: bv_cat'_def)
  qed
next
  case False
  note h = this
  show ?thesis
  proof(cases "l \<ge> snd b")
    case True
    {
      fix i :: nat
      assume "i < LENGTH('a)"
      hence "((\<langle>h,l\<rangle> (fst (bv_cat a b)))::'a::len0 word) !! i = (0::'a::len0 word) !! i"
        using h True assms
        by (auto simp add: bv_cat.simps nth_ucast test_bit_of_take_bits test_bit_of_bv_cat split: if_split_asm)
    }
    thus ?thesis
      using True h
      apply (auto)
      apply (intro word_eqI)
      by (auto simp add: word_size)
  next
    case False
    {
      fix i :: nat
      assume "i < LENGTH('a)"
      hence "((\<langle>h,l\<rangle> (fst (bv_cat a b)))::'a::len0 word) !! i = (\<langle>h,l\<rangle> (fst b)::'a::len0 word) !! i"
        using h False assms
        by (auto simp add: bv_cat.simps nth_ucast test_bit_of_take_bits test_bit_of_bv_cat split: if_split_asm)

    }
    thus ?thesis
      using False h
      apply (auto)
      apply (intro word_eqI)
      by (auto simp add: word_size)
  qed
qed


lemma take_bits_bv_slice:
  assumes "h < \<M>"
      and "h' < \<M>"
  shows "\<langle>h,l\<rangle>fst (bv_slice h' l' a) =  \<langle>(if Suc h - l < Suc h' - (l + l') then h + l' else h'),l + l'\<rangle>fst a"
  using assms
  by (cases a,auto simp add: bv_slice.simps)

lemma bv_slice_take_bits:
  assumes "h < \<M>"
      and "h' < LENGTH('a)"
  fixes a ::"'a::len0 word"
  shows "bv_slice h l (\<langle>h',l'\<rangle>a, s) = (\<langle>(if Suc h - l < Suc h' - (l + l') then h + l' else h'),l + l'\<rangle>a, h + 1 - l)"
  using assms
  by (auto simp add: bv_slice.simps)

lemma bv_slice_bit32:
  fixes a :: longword
  assumes "s \<ge> 32"
  shows "bv_slice 31 0 (a,s) = (ucast ((\<langle>31,0\<rangle>a)::32 word), 32)"
  using assms
  by (auto simp add: bv_slice.simps)


 
lemma bv_slice_nth_bit:
  assumes "h < \<M>"
  shows "bv_slice h h a = bool_to_bv (fst a !! h)"
proof-
  {
    fix i :: nat
    assume "i < \<M>"
    hence "((\<langle>h,h\<rangle>(fst a))::longword) !! i = (if fst a !! h then 1::longword else 0) !! i"
      using assms
      by (auto simp add: test_bit_of_take_bits)
  }
  hence "((\<langle>h,h\<rangle>(fst a))::longword) = (if fst a !! h then 1::longword else 0)"
    apply (intro word_eqI)
    by (auto simp add: word_size)
  thus ?thesis
    by (cases a;auto simp add: bv_slice.simps)
qed



subsection \<open>Arithmetic\<close>

lemma BV_Add_bit64:
  fixes a b :: longword
    shows "(a,64) +\<^sup>b\<^sup>v (b,64) = (ucast (((\<langle>63,0\<rangle>a)::64 word) + \<langle>63,0\<rangle>b), 64)"
proof-
  have "(a,64) +\<^sup>b\<^sup>v (b,64) = (\<langle>63,0\<rangle>(a + b), 64)"
    by (cases a;cases b;auto simp add: exec_BV_Plus_def case_prod_unfold)
  also have "... = (ucast ((\<langle>63,0\<rangle>(a + b))::64 word), 64)"
    by (subst ucast_take_bits,simp,simp,simp)
  also have "... = (ucast (((\<langle>63,0\<rangle>a)::64 word) + \<langle>63,0\<rangle>b), 64)"
    by (subst take_bits_plus,simp,simp,simp)
  finally
  show ?thesis
    by auto
qed

lemma BV_Add_bit33:
  fixes a b :: longword
    shows "(a,33) +\<^sup>b\<^sup>v (b,33) = (ucast (((\<langle>32,0\<rangle>a)::33 word) + \<langle>32,0\<rangle>b), 33)"
proof-
  have "(a,33) +\<^sup>b\<^sup>v (b,33) = (\<langle>32,0\<rangle>(a + b), 33)"
    by (cases a;cases b;auto simp add: exec_BV_Plus_def case_prod_unfold)
  also have "... = (ucast ((\<langle>32,0\<rangle>(a + b))::33 word), 33)"
    by (subst ucast_take_bits,simp,simp,simp)
  also have "... = (ucast (((\<langle>32,0\<rangle>a)::33 word) + \<langle>32,0\<rangle>b), 33)"
    by (subst take_bits_plus,simp,simp,simp)
  finally
  show ?thesis
    by auto
qed

lemma BV_Add_bit65:
  fixes a b :: longword
    shows "(a,65) +\<^sup>b\<^sup>v (b,65) = (ucast (((\<langle>64,0\<rangle>a)::65 word) + \<langle>64,0\<rangle>b), 65)"
proof-
  have "(a,65) +\<^sup>b\<^sup>v (b,65) = (\<langle>64,0\<rangle>(a + b), 65)"
    by (cases a;cases b;auto simp add: exec_BV_Plus_def case_prod_unfold)
  also have "... = (ucast ((\<langle>64,0\<rangle>(a + b))::65 word), 65)"
    by (subst ucast_take_bits,simp,simp,simp)
  also have "... = (ucast (((\<langle>64,0\<rangle>a)::65 word) + \<langle>64,0\<rangle>b), 65)"
    by (subst take_bits_plus,simp,simp,simp)
  finally
  show ?thesis
    by auto
qed

subsection \<open>Floating Point operations\<close>

context abstract_float
begin


lemma BV_Plus_bit64:
  fixes a b :: "64 word"
  shows "(\<langle>63,0\<rangle>a, 64) fplus\<^sup>b\<^sup>v (\<langle>63,0\<rangle>b, 64) = (\<langle>63,0\<rangle>(a +\<^sup>f b), 64)"
  by (auto simp add: exec_BV_Plus_Double_def)

lemma BV_Plus_bit64_numeral:
  fixes a :: "64 word"
  shows "(\<langle>63,0\<rangle>a, 64) fplus\<^sup>b\<^sup>v (numeral n, 64) = (\<langle>63,0\<rangle>(a +\<^sup>f \<langle>63,0\<rangle>((numeral n)::longword)), 64)"
  by (auto simp add: exec_BV_Plus_Double_def)

lemma BV_Sub_bit64:
  fixes a b :: "64 word"
  shows "(\<langle>63,0\<rangle>a, 64) fsub\<^sup>b\<^sup>v (\<langle>63,0\<rangle>b, 64) = (\<langle>63,0\<rangle>(a -\<^sup>f b), 64)"
  by (auto simp add: exec_BV_Sub_Double_def)

lemma BV_Sub_bit64_numeral:
  fixes a :: "64 word"
  shows "(\<langle>63,0\<rangle>a, 64) fsub\<^sup>b\<^sup>v (numeral n, 64) = (\<langle>63,0\<rangle>(a -\<^sup>f \<langle>63,0\<rangle>((numeral n)::longword)), 64)"
  by (auto simp add: exec_BV_Sub_Double_def)

lemma BV_Mult_bit64:
  fixes a b :: "64 word"
  shows "(\<langle>63,0\<rangle>a, 64) fmult\<^sup>b\<^sup>v (\<langle>63,0\<rangle>b, 64) = (\<langle>63,0\<rangle>(a *\<^sup>f b), 64)"
  by (auto simp add: exec_BV_Mul_Double_def)

lemma BV_Mult_bit64_numeral_r:
  fixes a :: "64 word"
  shows "(\<langle>63,0\<rangle>a, 64) fmult\<^sup>b\<^sup>v (numeral n, 64) = (\<langle>63,0\<rangle>(a *\<^sup>f \<langle>63,0\<rangle>((numeral n)::longword)), 64)"
  by (auto simp add: exec_BV_Mul_Double_def)
lemma BV_Mult_bit64_numeral_l:
  fixes a :: "64 word"
  shows "(numeral n, 64) fmult\<^sup>b\<^sup>v (\<langle>63,0\<rangle>a, 64) = (\<langle>63,0\<rangle>(\<langle>63,0\<rangle>((numeral n)::longword) *\<^sup>f a), 64)"
  by (auto simp add: exec_BV_Mul_Double_def)
lemma BV_Mult_bit64_0_l:
  fixes a :: "64 word"
  shows "(0, 64) fmult\<^sup>b\<^sup>v (\<langle>63,0\<rangle>a, 64) = (\<langle>63,0\<rangle>(0\<^sup>+ *\<^sup>f a), 64)"
  by (auto simp add: exec_BV_Mul_Double_def plus_zero_def)
lemma BV_Mult_bit64_0_r:
  fixes a :: "64 word"
  shows "(\<langle>63,0\<rangle>a, 64) fmult\<^sup>b\<^sup>v (0, 64) = (\<langle>63,0\<rangle>(a *\<^sup>f 0\<^sup>+), 64)"
  by (auto simp add: exec_BV_Mul_Double_def plus_zero_def)


lemma BV_Div_bit64:
  fixes a b :: "64 word"
  shows "(\<langle>63,0\<rangle>a, 64) fdiv\<^sup>b\<^sup>v (\<langle>63,0\<rangle>b, 64) = (\<langle>63,0\<rangle>(a div\<^sup>f b), 64)"
  by (auto simp add: exec_BV_Div_Double_def)

lemma BV_Div_bit64_numeral: 
  fixes a :: "64 word"
  shows "(\<langle>63,0\<rangle>a, 64) fdiv\<^sup>b\<^sup>v (numeral n, 64) = (\<langle>63,0\<rangle>(a div\<^sup>f \<langle>63,0\<rangle>((numeral n)::longword)), 64)"
  by (auto simp add: exec_BV_Div_Double_def)

end



subsection \<open>Simplification rules\<close>


lemmas (in abstract_float) bit_vector_simps =
    bv_slice_bv_cat take_bits_bv_slice bv_slice_take_bits take_bits_bv_cat bv_slice_bit32
    bv_cat_prepend_0 size_bv_cat size_bv_slice
    bv_to_bool_bool_to_bv snd_bool_to_bv
    bv_to_bool_True bv_to_bool_True_Suc0
    bv_to_bool_False bv_to_bool_False_Suc0
    BV_Add_bit65 BV_Add_bit64 BV_Add_bit33
    BV_Plus_bit64 BV_Plus_bit64_numeral
    BV_Sub_bit64 BV_Sub_bit64_numeral
    BV_Mult_bit64 BV_Mult_bit64_numeral_r BV_Mult_bit64_numeral_l BV_Mult_bit64_0_l BV_Mult_bit64_0_r
    BV_Div_bit64 BV_Div_bit64_numeral
    bv_slice_bit32
    bv_NOT.simps
    bv_NOT_bool_to_bv bool_to_bv_eq bv_slice_nth_bit
end
