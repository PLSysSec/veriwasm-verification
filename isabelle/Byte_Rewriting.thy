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

theory Byte_Rewriting
  imports Take_Bits_Rewriting
begin


declare take_bits_bitAND[simp del]
declare take_bits_bitOR[simp del]
declare take_bits_of_take_bits[simp del]

section "Bytes"

subsection "Byte-level operations"

text {*
  Function @{term cat_bytes} is used to concatenate a list of bytes.
  Function @{term bytes_of} is used to split a word into a list of bytes.
*}




subsection "Bytes of a word"

lemma length_sublist:
  shows "length (sublist l h x) = min (length x - l) (Suc h - l)"
  unfolding sublist_def
  by (auto)

lemma nth_sublist:
  assumes "n < length x - l"
      and "n < Suc h - l"
shows "(sublist l h x) ! n = x!(l + n)"
  using assms
  by (auto simp add: sublist_def)

lemma length_word_to_bytes:
  shows "length (word_to_bytes w s) = s"
proof(induct w s rule: word_to_bytes.induct)
  case (1 w s)
  then show ?case
    by (auto simp add: word_to_bytes.simps[of w s] word_to_bytes.simps[of w 0] split: if_split_asm)
qed

lemma length_bytes_of[simp]:
  fixes w :: "'a::len0 word"
  shows "length (\<lbrace>h,l\<rbrace>w) = (if h < l \<or> LENGTH('a) div 8 \<le> h then 0 else min (LENGTH('a) div 8 - (LENGTH('a) div 8 - Suc h)) (Suc (LENGTH('a) div 8 - Suc l) - (LENGTH('a) div 8 - Suc h)))"
  by (auto simp add: bytes_of_def length_sublist length_word_to_bytes)

lemma bytes_of_is_empty[simp]:
  fixes w :: "'a::len0 word"
  shows "(\<lbrace>h,l\<rbrace>w = []) = (if h < l \<or> LENGTH('a) div 8 \<le> h then True else Suc (LENGTH('a) div 8 - Suc l) \<le> LENGTH('a) div 8 - Suc h \<or> LENGTH('a) div 8 = 0)"
  unfolding bytes_of_def sublist_def
  by (auto simp add: length_word_to_bytes)


lemma take_bytes_of[simp]:
  fixes w :: "'a::len0 word"
  shows "take n (\<lbrace>h,l\<rbrace>w) = (if h < l \<or> LENGTH('a) div 8 \<le> h then take n [] else if h + 2 \<le> n + LENGTH('a) div 8 then (if LENGTH('a) div 8 = Suc 0 \<and> h = 0 then \<lbrace>h,l\<rbrace>w else if n \<le> Suc (Suc (h + (LENGTH('a) div 8 - Suc l))) - LENGTH('a) div 8 then \<lbrace>h,h+1-n\<rbrace>w else \<lbrace>h,l\<rbrace>w) else [])"
proof(cases "h + 2 > n + LENGTH('a) div 8")
  case True
  thus ?thesis
    by (cases "n=0",auto simp add: bytes_of_def sublist_def min_def field_simps)
next
  case False
  show ?thesis
  proof(cases "\<not>(LENGTH('a) div 8 = Suc 0 \<and> h = 0)")
    case False
    thus ?thesis
      by (auto simp add: bytes_of_def sublist_def min_def field_simps)
  next
    case True
    hence 0: "LENGTH('a) div 8 > h \<Longrightarrow> 2 \<le> LENGTH('a) div 8"
      by (auto)
    hence "LENGTH('a) div 8 > h \<Longrightarrow> Suc (Suc (n + LENGTH('a) div 8 - 2)) = n + LENGTH('a) div 8"
      by auto
    hence 1: "LENGTH('a) div 8 > h \<Longrightarrow> (Suc (Suc (n + LENGTH('a) div 8 - 2)) - LENGTH('a) div 8) = n"
      by auto
    show ?thesis
      using False True
      apply (auto simp add: bytes_of_def sublist_def min_def field_simps length_word_to_bytes)
      apply linarith
      apply (subst 1,simp,simp)
      apply linarith
      by (subst 1,simp,simp)
  qed
qed


lemma drop_bytes_of[simp]:
  fixes w :: "'a::len0 word"
  shows "drop n (\<lbrace>h,l\<rbrace>w) = (if h < l \<or> LENGTH('a) div 8 \<le> h then drop n [] else if n > h then [] else \<lbrace>h - n,l\<rbrace>w)"
  by (auto simp add: bytes_of_def sublist_def min_def field_simps drop_take)


lemma tl_bytes_of[simp]:
  fixes w :: "'a::len0 word"
  shows "tl (\<lbrace>h,l\<rbrace>w) = (if h < l \<or> LENGTH('a) div 8 \<le> h then tl [] else if Suc (LENGTH('a) div 8 - Suc l) \<le> LENGTH('a) div 8 - Suc h \<or> h = l then [] else (\<lbrace>h-1,l\<rbrace>w))"
  apply (auto simp add: bytes_of_def sublist_def min_def field_simps)
  apply (metis take_0 take_tl)
  apply (metis take_0 take_tl)
  by (smt Suc_diff_Suc Suc_eq_plus1 add_diff_cancel_right' diff_right_commute drop_Suc drop_tl le_add1 less_le_trans linorder_neqE_nat linorder_not_less tl_take)

  
lemma hd_bytes_of:
  fixes w :: "'a::len0 word"
  assumes "l \<noteq> h"
  shows "hd (\<lbrace>h,l\<rbrace>w) = (if h < l \<or> LENGTH('a) div 8 \<le> h then hd [] else \<lbrace>h\<rbrace>w)"
  by (auto simp add: bytes_of_def sublist_def take_drop drop_Suc field_simps length_word_to_bytes hd_drop_conv_nth)

lemma nth_word_to_bytes:
  shows "s < n \<Longrightarrow> (word_to_bytes w n)!s = (\<langle>(n-s) * 8 - 1,(n-s) * 8 - 8\<rangle>w)"
proof(induct w n arbitrary: s rule: word_to_bytes.induct)
  case (1 w n)
  show ?case
    using 1(2) 1(1)[of "s-1"] 1
    by (cases s;auto split: if_split_asm simp add: word_to_bytes.simps[of w n] nth_Cons)
qed

lemma hd_take:
  shows "hd (take n x) = (if x=[] \<or> n = 0 then hd [] else hd x)"
  by (cases x;cases n;auto)

lemma hd_sublist:
  shows "hd (sublist l h x) = (if l \<le> h \<and> l < length x then x!l else hd [])"
  by (cases "Suc h - l";cases x;auto simp add: sublist_def hd_take hd_drop_conv_nth)

lemma nth_bytes_of:
  fixes w :: "'a::len0 word"
  assumes "n < Suc (Suc (LENGTH('a) div 8 + h - Suc l)) - LENGTH('a) div 8"
  shows "(\<lbrace>h,l\<rbrace>w) ! n = (if h < l \<or> LENGTH('a) div 8 \<le> h then []!n else \<lbrace>h-n\<rbrace>w)"
  using assms
  by (auto simp add: length_word_to_bytes bytes_of_def nth_sublist hd_sublist)


(*
lemma to_bl_byte_of:
  fixes a :: "64 word"
  assumes "i < 8"
  shows "to_bl (\<lbrace>i\<rbrace> a) = take 8 (drop (56 - i*8) (to_bl a))"
proof-
  {
    fix j :: nat
    assume "j < 8"
    hence "to_bl ((\<langle>7 + i * 8,i * 8\<rangle>a):: 8 word) ! j = (take 8 (drop (56 - i * 8) (to_bl a))) ! j"
      using assms
      by (auto simp add: nth_of_take_bits)
  }
  hence "to_bl ((\<langle>7 + i * 8,i * 8\<rangle>a):: 8 word) = (take 8 (drop (56 - i * 8) (to_bl a)))"
    using assms
    apply (intro nth_equalityI)
    by (auto simp add: min_def)
  thus ?thesis
    using assms
    using nth_word_to_bytes[of "7-i" 8 a] hd_drop_conv_nth[of i "word_to_bytes a 8"]
    by (cases "drop i (word_to_bytes a 8)",auto simp add: bytes_of_def sublist_def length_word_to_bytes hd_take hd_drop_conv_nth)
qed*)

lemma test_bit_of_byte_of:
  fixes a :: "'a::len0 word"
  assumes "i < LENGTH('a) div 8"
  shows "(\<lbrace>i\<rbrace> a) !! n = (if n \<ge> 8 then False else a !! (i*8 + n))"
proof-
  show ?thesis
    using assms
    apply (auto simp add: bytes_of_def hd_sublist length_word_to_bytes nth_word_to_bytes test_bit_of_take_bits )
    by (auto simp add: test_bit_bin)
qed

lemmas bytes_of_simps[simp] =
  bytes_of_def[of h l 0]
  bytes_of_def[of h l 1]
  bytes_of_def[of h l "numeral n"]
  bytes_of_def[of h l "- ((numeral n)::'a::len0 word)"]
  for h l n


lemma byte_of_bitAND:
  fixes a b :: "'a::len0 word"
  assumes "n < LENGTH('a) div 8"
  shows "\<lbrace>n\<rbrace> (a AND b) = \<lbrace>n\<rbrace> a AND \<lbrace>n\<rbrace> b"
proof-
  {
    fix i :: nat
    assume "i < 8"
    hence "(\<lbrace>n\<rbrace> (a AND b)) !! i = (\<lbrace>n\<rbrace> a AND \<lbrace>n\<rbrace> b) !! i"
      using assms
      by (auto simp add: test_bit_of_byte_of word_ao_nth)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed

lemma byte_of_bitOR:
  fixes a b :: "'a::len0 word"
  assumes "n < LENGTH('a) div 8"
  shows "\<lbrace>n\<rbrace> (a OR b) = \<lbrace>n\<rbrace> a OR \<lbrace>n\<rbrace> b"
proof-
  {
    fix i :: nat
    assume "i < 8"
    hence "(\<lbrace>n\<rbrace> (a OR b)) !! i = (\<lbrace>n\<rbrace> a OR \<lbrace>n\<rbrace> b) !! i"
      using assms
      by (auto simp add: test_bit_of_byte_of word_ao_nth)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed



subsection "Byte Concatenation"

lemmas cat_bytes_simps[simp] =
  cat_bytes.simps(2)[of "numeral n" bs]
  cat_bytes.simps(2)[of 0 bs]
  cat_bytes.simps(2)[of 1 bs]
  for n bs


lemma test_bit_of_cat_bytes:
  shows "((cat_bytes ws)::'a::len0 word)!!n = (if n < length ws * 8 \<and> n < LENGTH('a) then (rev ws!(n div 8)) !! (7 - ((length ws * 8 - n - 1) mod 8)) else False)"
proof(induct ws arbitrary: n)
  case Nil
  thus ?case
    by auto
next
  case (Cons w ws)
  let ?w = "(ucast w)::'a::len0 word"
  let ?w' = "?w << (length ws * 8)"

  have "(length ws * 8 - Suc n) mod 8 = ((length ws * 8 - Suc n) + 8) mod 8"
    by simp
  hence "n < length ws * 8 \<Longrightarrow> (length ws * 8 - Suc n) mod 8 = (7 + length ws * 8 - n) mod 8"
    by auto
  thus ?case
    using Cons(1)[of n]
    apply (auto simp add: word_size nth_append nth_shiftl' word_ao_nth rev_nth nth_ucast to_bl_nth)
    by (auto simp add: test_bit_bl rev_nth word_size)
qed

declare cat_bytes.simps(2)[simp del]


lemma take_Suc0:
  shows "take (Suc 0) x = (if x = [] then [] else [hd x])"
  by (cases x,auto)

lemma cat_bytes_byte_of[simp]:
  fixes w :: "'a::len0 word"
  shows "cat_bytes [\<lbrace>l\<rbrace>w] = (if LENGTH('a) div 8 \<le> l then cat_bytes [hd []] else cat_bytes (\<lbrace>l,l\<rbrace> w))"
  unfolding bytes_of_def sublist_def
  by (cases "drop l (word_to_bytes w (LENGTH('a) div 8))",auto simp add: length_word_to_bytes hd_take take_Suc0)


lemma is_zero_cat_bytes[simp]:
  assumes "length bs * 8 < LENGTH('a)"
  shows "(((cat_bytes bs)::'a::len0 word) = 0) = (\<forall> b \<in> List.set bs . b = 0)"
proof-
  {
    fix b
    assume "((cat_bytes bs)::'a::len0 word) = 0"
       and "b \<in> List.set bs"
    from this have b: "b = 0"
      using assms
    proof(induct bs)
      case Nil
      thus ?thesis
        by auto
    next
      case (Cons b' bs)
      thus ?thesis
        using Cons
        apply (auto simp add: cat_bytes.simps(2) nth_ucast is_zero_shiftl is_zero_all_bits[of b'])        
        by (smt add_lessD1 less_diff_conv less_imp_add_positive)
    qed
  }
  moreover
  {
    assume "\<forall>b\<in>List.set bs. b = 0"
    hence "cat_bytes bs = 0"
      by(induct bs,auto simp add: cat_bytes.simps(2))
  }
  ultimately
  show ?thesis
    by auto
qed


lemma unfold_enum_le:
  shows "enum_le n = (if n=0 then [] else (n-1) # enum_le (n-1))"
  by (cases n,auto)

lemma take_eight_bits_of_cat_bytes:
  assumes "n * 8 - Suc 0 < LENGTH('a)"
      and "n > 0"
   shows "((\<langle>n * 8 - Suc 0,n * 8 - 8\<rangle>((cat_bytes bs)::'a::len0 word)):: 8 word) = (if n \<le> length bs then bs ! (length bs - n) else 0)"
proof-
  {
    fix i :: nat
    assume 2: "i < 8"
    have 1: "i < Suc (n * 8 - Suc 0) - (n * 8 - 8) \<Longrightarrow> n \<le> length bs \<Longrightarrow> (length bs - Suc ((n * 8 + i - 8) div 8)) = (length bs - n)"
      using assms
      by (cases "n=0",auto)

    have 4: "i + n * 8 \<le> length bs * 8 \<Longrightarrow> (7 + length bs * 8 - (i + n * 8)) mod 8 = (7 + length bs * 8 - n * 8 - i) mod 8"
      by (auto simp add: field_simps)
    have 5: "n \<le> length bs \<Longrightarrow> 7 + length bs * 8 - n * 8 - i = 7 + (length bs - n) * 8 - i"
      by (auto simp add: field_simps)
    have 6: "7 + (length bs - n) * 8 - i = 7 - i + (length bs - n) * 8"
      using assms 2
      by (auto simp add: field_simps)      
    have 4: "i + n * 8 \<le> length bs * 8 \<Longrightarrow> n \<le> length bs \<Longrightarrow> (7 + length bs * 8 - (i + n * 8)) mod 8 = 7 - i"
      apply (subst 4,simp)
      apply (subst 5,simp)
      apply (subst 6)
      by (auto simp add: mod_mult_self1)
    have "n \<le> length bs \<Longrightarrow> length bs - Suc ((n * 8 + i - 8) div 8) = length bs - n \<Longrightarrow> Suc ((n * 8 + i - 8) div 8) = n"
      using assms 2
      by auto
    hence 3: "length bs - Suc ((n * 8 + i - 8) div 8) = length bs - n \<Longrightarrow>
             n \<le> length bs \<Longrightarrow>
             n * 8 + i - 8 < length bs * 8 \<Longrightarrow>
              n * 8 + i - 8 < LENGTH('a) \<Longrightarrow> (7 - (7 + length bs * 8 - (n * 8 + i)) mod 8) = i"
      using assms
      apply (cases "length bs * 8 \<ge> (i + n * 8)", auto simp add: field_simps)
      apply (cases "length bs * 8 = (i + n * 8)", auto simp add: field_simps)
      apply (metis (no_types, lifting) "2" add_diff_cancel_left' arith_extra_simps(6) div_eq_0_iff div_mult_self1 gr_implies_not_zero minus_eq nonzero_mult_div_cancel_right)      
      using 4
      by (auto)
    have "((\<langle>n * 8 - Suc 0,n * 8 - 8\<rangle>((cat_bytes bs)::'a::len0 word))::8 word) !! i = (if n \<le> length bs then bs ! (length bs - n) else 0) !! i"
      using assms 2 1
      apply (auto simp add: test_bit_of_take_bits)
      by (auto simp add: test_bit_of_cat_bytes rev_nth 3 split: if_split_asm)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed



lemma word_to_bytes_cat_bytes:
  assumes "n \<ge> length bs"
      and "n * 8 - Suc 0 < LENGTH('a)"
  shows "word_to_bytes ((cat_bytes bs)::'a::len0 word) n = (replicate (n - length bs) 0) @ bs"
proof-
  {
    fix i::nat
    assume 1: "i<n"
    {
      fix j::nat
      have "((\<langle>(n - i) * 8 - Suc 0,(n - i) * 8 - 8\<rangle>((cat_bytes bs)::'a::len0 word))::8 word) !! j = (replicate (n - length bs) 0 @ bs) ! i !! j"
        using 1 assms
        by (auto simp add: take_eight_bits_of_cat_bytes nth_append add.commute)
    }
    note 2 = this
    have "(word_to_bytes ((cat_bytes bs)::'a::len0 word) n)!i = ((replicate (n - length bs) 0) @ bs)!i"
      using nth_word_to_bytes[of i n "((cat_bytes bs)::'a::len0 word)"] 1
      apply (auto simp add:)
      apply (intro word_eqI)
      apply (rule impI)
      apply (subst 2)
      by (auto simp add: word_size)
  }
  thus ?thesis
    using assms
    apply (intro nth_equalityI)
    by (auto simp add: length_word_to_bytes)
qed

lemma sublist_Cons[simp]:
  shows "sublist l h (x#y) = (if l=0 then [x] else [])@(if h=0 then [] else sublist (l-1) (h-1) y)"
  unfolding sublist_def
  by (cases l;auto simp add: field_simps Suc_diff_le)

lemma sublist_append[simp]:
  shows "sublist l h (x@y) = (if l > h then [] else if Suc h \<le> length x then sublist l h x
          else (sublist l h x) @ (sublist (l - length x) (h - length x) y))"
  unfolding sublist_def
  by (cases "l \<le> length x";cases "l\<le>h";cases "Suc h \<le> length x";auto simp add: field_simps Suc_diff_le)

lemma sublist_sublist:
  shows "sublist l h (sublist l' h' x) = (if Suc h - l \<le> Suc h' - (l + l') then sublist (l + l') (h+l') x else sublist (l + l') h' x)"
  unfolding sublist_def
  by (auto simp add: drop_take min_def field_simps)

lemma sublist_replicate:
  shows "sublist l h (replicate n w) = replicate (min (Suc h - l) (n - l)) w"
  unfolding sublist_def
  by auto

lemma sublist_empty:
  shows "sublist l h [] = []"
  unfolding sublist_def
  by auto

lemma sublist_empty_out_of_bounds:
  assumes \<open>n \<ge> length xs\<close>
    and \<open>m \<ge> length xs\<close>
  shows \<open>sublist n m xs = []\<close>
  using assms unfolding sublist_def
  by simp


lemma sublist_bytes_of[simp]:
  fixes w :: "'a::len0 word"
  assumes "l \<le> h' - l'"
      and "l \<le> h"
    shows  "sublist l h (\<lbrace>h',l'\<rbrace>w) = (if h' < l' \<or> LENGTH('a) div 8 \<le> h' then [] else
                if Suc h - l \<le> Suc (Suc (LENGTH('a) div 8 + h' - Suc l')) - (l + LENGTH('a) div 8) then
                   \<lbrace>h'-l,h'-h\<rbrace>w else \<lbrace>h'-l,l'\<rbrace>w)"
  using assms
  by (cases "h \<le> h'";auto simp add: bytes_of_def sublist_empty sublist_sublist field_simps)

lemma bytes_of_cat_bytes[simp]:
  assumes "length bs \<le> LENGTH('a) div 8"
  shows "\<lbrace>h,l\<rbrace>((cat_bytes bs)::'a::len0 word) =
          (if h < l \<or> (LENGTH('a) div 8 \<le> h \<and> \<not> h < l) then []
           else if Suc (LENGTH('a) div 8 - Suc l) \<le> LENGTH('a) div 8 - length bs then 
              replicate (min (Suc (Suc (LENGTH('a) div 8 + h - Suc l)) - LENGTH('a) div 8) (Suc h - length bs)) 0
           else replicate (min (Suc (Suc (LENGTH('a) div 8 + h - Suc l)) - LENGTH('a) div 8) (Suc h - length bs)) 0 @
    sublist (length bs - Suc h) (length bs - Suc l) bs)"
proof-
  have "sublist (LENGTH('a) div 8 - Suc h) (LENGTH('a) div 8 - Suc l) (replicate (LENGTH('a) div 8 - length bs) 0) =
        replicate (min (Suc (LENGTH('a) div 8 - Suc l) - (LENGTH('a) div 8 - Suc h)) (LENGTH('a) div 8 - (length bs + (LENGTH('a) div 8 - Suc h)))) 0"
    by (auto simp add: sublist_def min_def)
  thus ?thesis
    using assms
    by (auto simp add: bytes_of_def word_to_bytes_cat_bytes)
qed

lemma cat_bytes_append[simp]:
  assumes "length a + length b \<le> LENGTH('a) div 8"
  shows "((cat_bytes (a @ b))::'a::len word) = fst (bv_cat (cat_bytes a, 8 * length a) (cat_bytes b, 8 * length b))"
  using assms
proof (induct a)
  case Nil
  have "\<langle>8 * length b - Suc 0,0\<rangle>((cat_bytes b)::'a::len word) = ((cat_bytes b)::'a::len word)"
  proof-
    {
      fix i :: nat
      assume "i < LENGTH('a)"
      hence "((\<langle>8 * length b - Suc 0,0\<rangle>((cat_bytes b)::'a::len word))::'a::len word) !! i = ((cat_bytes b)::'a::len word) !! i"
        using Nil
        by (cases "length b = 0",auto simp add: test_bit_of_take_bits sublist_def test_bit_of_cat_bytes)
    }
    thus ?thesis
      apply (intro word_eqI)
      by (auto simp add: word_size)
  qed
  thus ?case
    by (auto simp add: sublist_def bv_cat.simps test_bit_of_cat_bytes)
next
  case (Cons a as)
  {
    fix i :: nat
    assume "i < LENGTH('a)"
    hence "(cat_bytes ((a # as) @ b) ::'a::len word) !! i = (fst (bv_cat (cat_bytes (a # as) ::'a::len word, 8 * length (a # as)) (cat_bytes b ::'a::len word, 8 * length b))) !! i"
      using Cons
      apply (auto simp add: cat_bytes.simps(2))
      by (auto simp add: bv_cat.simps word_ao_nth nth_ucast nth_shiftl test_bit_of_cat_bytes field_simps split: if_split_asm)
  }  
  thus ?case
    apply (intro word_eqI)
    by (auto simp add: word_size)      
qed






lemma length_read_bytes:
  shows "length (read_bytes m b) = snd b"
  by (induct m b rule: read_bytes.induct,auto simp add: Let'_def)


lemma take_bits_dereference_bit8:
  assumes "8 \<le> LENGTH('a)"
      and "8 \<le> LENGTH('b)"
    shows "((\<langle>7,0\<rangle>((\<sigma> \<turnstile> *[a,s])::'b::len0 word))::'a::len0 word) = ucast ((\<sigma> \<turnstile> *[a,s])::8 word)"
proof-
  {
    fix n :: nat and m r
    assume "n < LENGTH('a)"
    hence "((\<langle>7,0\<rangle>((\<sigma> \<turnstile> *[a,s])::'b::len0 word))::'a::len0 word) !! n = ((ucast ((\<sigma> \<turnstile> *[a,s])::8 word))::'a::len0 word) !! n"
      using assms
      unfolding read_region_def
      by (auto simp add: min_def test_bit_of_take_bits test_bit_of_cat_bytes length_read_bytes nth_ucast)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed

lemma take_bits_dereference_bit16[simp]:
  assumes "16 \<le> LENGTH('a)"
      and "16 \<le> LENGTH('b)"
    shows "((\<langle>15,0\<rangle>((\<sigma> \<turnstile> *[a,s])::'b::len0 word))::'a::len0 word) = ucast ((\<sigma> \<turnstile> *[a,s])::16 word)"
proof-
  {
    fix n :: nat and m r
    assume "n < LENGTH('a)"
    hence "((\<langle>15,0\<rangle>((\<sigma> \<turnstile> *[a,s])::'b::len0 word))::'a::len0 word) !! n = ((ucast ((\<sigma> \<turnstile> *[a,s])::16 word))::'a::len0 word) !! n"
      using assms
      unfolding read_region_def
      by (auto simp add: min_def test_bit_of_take_bits test_bit_of_cat_bytes length_read_bytes nth_ucast)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed


lemma take_bits_dereference_bit32:
  assumes "32 \<le> LENGTH('a)"
      and "32 \<le> LENGTH('b)"
    shows "((\<langle>31,0\<rangle>((\<sigma> \<turnstile> *[a,s])::'b::len0 word))::'a::len0 word) = ucast ((\<sigma> \<turnstile> *[a,s])::32 word)"
proof-
  {
    fix n :: nat and m r
    assume "n < LENGTH('a)"
    hence "((\<langle>31,0\<rangle>((\<sigma> \<turnstile> *[a,s])::'b::len0 word))::'a::len0 word) !! n = ((ucast ((\<sigma> \<turnstile> *[a,s])::32 word))::'a::len0 word) !! n"
      using assms
      unfolding read_region_def
      by (auto simp add: min_def take_bits_of_take_bits test_bit_of_take_bits test_bit_of_cat_bytes length_read_bytes nth_ucast)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed

lemma take_bits_lt_bit32_deref:
  fixes a :: "'b::len0 word"
  assumes "32 \<le> LENGTH('a)"   
      and "32 \<le> LENGTH('b)"
      and "s \<le> 4"
      and "no_block_overflow (b,s)"
  shows "(((\<langle>31,0\<rangle>a)::'a::len0 word) < ((\<sigma> \<turnstile> *[b,s])::'a::len0 word)) = (((\<langle>31,0\<rangle>a)::32 word) < ((\<sigma> \<turnstile> *[b,s])::32 word))"
proof-
  have 1: "((\<sigma> \<turnstile> *[b,s])::'a::len0 word) = \<langle>31,0\<rangle>((\<sigma> \<turnstile> *[b,s])::'b::len0 word)"
  proof-
    {
      fix i :: nat
      assume "i < LENGTH('a)"
      hence "((\<sigma> \<turnstile> *[b,s])::'a::len0 word) !! i = ((\<langle>31,0\<rangle>((\<sigma> \<turnstile> *[b,s])::'b::len0 word))::'a::len0 word) !! i"
        using assms
        unfolding read_region_def
        by (auto simp add: Abs_region_inverse min_def test_bit_of_take_bits test_bit_of_cat_bytes length_read_bytes nth_ucast)
    }
    thus ?thesis
      apply (intro word_eqI)
      by (auto simp add: word_size)
  qed
  have 2: "((\<sigma> \<turnstile> *[b,s])::32 word) = \<langle>31,0\<rangle>((\<sigma> \<turnstile> *[b,s])::'b::len0 word)"
  proof-
    {
      fix i :: nat
      assume "i < 32"
      hence "((\<sigma> \<turnstile> *[b,s])::32 word) !! i = ((\<langle>31,0\<rangle>((\<sigma> \<turnstile> *[b,s])::'b::len0 word)) :: 32 word) !! i"
        using assms
        by (auto simp add: test_bit_of_take_bits nth_ucast take_bits_dereference_bit32)
    }
    thus ?thesis
      apply (intro word_eqI)
      by (auto simp add: word_size)
  qed

  show ?thesis
    using assms
    apply (subst 1)
    apply (subst 2)
    apply (subst take_bits_lt_bit32)
    by auto
qed


lemma rewrite_byte_of_to_take_bits[simp]:
  fixes w :: "64 word"
  assumes "l < 8"
  shows "\<lbrace>l\<rbrace>w = ((\<langle>(l+1)*8-1,l*8\<rangle> w)::8 word)"
proof-
  {
    fix n :: nat
    assume "n < 8"
    hence "(\<lbrace>l\<rbrace>w) !! n = ((\<langle>(l+1)*8-1,l*8\<rangle> w)::8 word) !! n"
      using assms
      by (auto simp add: test_bit_of_byte_of test_bit_of_take_bits)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed


lemma take_equal_implies_nth_equal:
  assumes "take n x = take n y"
      and "i < n"
      and "n < length x"
      and "n < length y"
    shows "x ! i = y ! i"
  using assms
proof(induct n arbitrary: x y i)
  case 0
  thus ?case
    by auto
next
  case (Suc n)
  show ?case
    using Suc(2-) Suc(1)[of "tl x" "tl y" "i-1"]
    by (cases x;cases y;cases i;auto simp add: nth_Cons)
qed




lemma mod_mult_sub:
  fixes x y z :: nat
  shows "x * m \<ge> z \<Longrightarrow> y * m \<ge> z \<Longrightarrow> (x * m - z) mod m = (y * m - z) mod m"
proof(induct x arbitrary: y z)
  case 0
  thus ?case
    by (auto)
next
  case (Suc x)
  show ?case
    using Suc(2-)
    apply (auto simp add: field_simps simp del: mod_add_self1 split: if_split_asm)
    apply (cases "x*m \<le> z")
    using Suc(1)[of z y]
    apply (metis le_add_diff_inverse2 mod_add_self1 mod_mult_self1_is_0 mod_plus_right)
    by (metis linorder_linear local.Suc(1) mult.commute mult_Suc)
qed

lemma take_bits_cat_bytes:
  assumes "l mod 8 = 0"
      and "(h + 1) mod 8 = 0"
      and "(h + 1) div 8 \<le> length bs"
      and "h < LENGTH('a)"
    shows "\<langle>h,l\<rangle>((cat_bytes bs) :: 'a::len0 word) =
          (if l \<le> h then cat_bytes (sublist (length bs - ((h+1) div 8)) (length bs - 1 - (l div 8)) bs) else 0)"
proof(cases "l \<le> h")
  case False
  thus ?thesis
    using False
    unfolding take_bits_def
    by auto
next
  case True
  {
    fix n :: nat
    assume n: "n < LENGTH('b)"
    have 0: "Suc (l div 8) \<le> length bs"
      using assms True
      by auto
    hence 1: "sublist (length bs - Suc h div 8) (length bs - Suc (l div 8)) bs !
            (length (sublist (length bs - Suc h div 8) (length bs - Suc (l div 8)) bs) - Suc (n div 8)) = bs ! (length bs - Suc h div 8 +
          (min (length bs - (length bs - Suc h div 8)) (length bs - (l div 8 + (length bs - Suc h div 8))) - Suc (n div 8)))"
      apply (auto simp add: length_sublist )
      apply (subst  nth_sublist)
      using True assms
      by (auto simp add: min_def)
    have 2: "n < length (sublist (length bs - Suc h div 8) (length bs - Suc (l div 8)) bs) * 8 \<Longrightarrow>
              n div 8 < length (sublist (length bs - Suc h div 8) (length bs - Suc (l div 8)) bs)"
      using assms(3) 0
      by (auto simp add: length_sublist)
    have 3: "l + n < length bs * 8 \<Longrightarrow> (l + n) div 8 < length bs"
      using assms(3) 0 zero_less_numeral
      by (auto simp add: length_sublist)
    have 4: "n < Suc h - l \<Longrightarrow>
      (length bs - Suc h div 8 + (min (length bs - (length bs - Suc h div 8)) (length bs - (l div 8 + (length bs - Suc h div 8))) - Suc (n div 8))) =
      (length bs - Suc ((l + n) div 8))"
      using assms(3-)
      apply (cases "Suc h div 8 \<ge> Suc (l div 8 + n div 8)",auto simp add: length_sublist)
      using assms
      by (auto)

    have 8: "Suc h div 8 * 8 = Suc h"
      using assms
      by auto
    have 10: "\<And> a b c :: nat . b + c \<le> a \<Longrightarrow> a - (b + c) = a - b - c"
      by auto
    have 6: "n < Suc h - l \<Longrightarrow>
    (length bs + (Suc h div 8 - Suc (l div 8 + n div 8)) - Suc h div 8) = (length bs - Suc ((l + n) div 8))"
      using assms(3,4)
      by simp (smt 4 Groups.add_ac(2) Nat.add_diff_assoc2 add_Suc_right add_diff_cancel_left' diff_diff_left min_minus)
    have 7: "(Suc h div 8 - l div 8) * 8 = Suc h - l"
      using assms
      by (simp add: Groups.mult_ac(2) mod_0_imp_dvd right_diff_distrib')

    have 88: "l div 8 \<le> length bs \<Longrightarrow> (length bs * 8 - Suc (l + n)) mod 8 = ((length bs - l div 8) * 8 - Suc n) mod 8"
      using assms(1)
      by (auto simp add: field_simps diff_mult_distrib)
    have 11: "n < length (sublist (length bs - Suc h div 8) (length bs - Suc (l div 8)) bs) * 8 \<Longrightarrow>
              (7 - (length (sublist (length bs - Suc h div 8) (length bs - Suc (l div 8)) bs) * 8 - Suc n) mod 8) = (7 - (length bs * 8 - Suc (l + n)) mod 8)"
      using assms(3-) True
      apply (auto simp add: length_sublist)
      apply (subst 88)
      using assms apply auto[1]
      apply (subst mod_mult_sub[of _ _ _ "length bs - l div 8"])
      apply auto[1]
      using assms apply auto[1]
      by auto[1]
    have "((\<langle>h,l\<rangle>((cat_bytes bs) :: 'a::len0 word)):: 'b::len0 word) !! n =
          ((cat_bytes (sublist (length bs - ((h+1) div 8)) (length bs - 1 - (l div 8)) bs))::'b::len0 word) !! n"
      using assms(3,4) n 2 3
      using [[linarith_split_limit = 13]]
      apply (auto simp add: 1 6 7 8 test_bit_of_take_bits test_bit_of_cat_bytes rev_nth nth_sublist)
      apply(auto simp add: 4 11 6)[1]
      apply(auto simp add: 4 11 6)[1]
      apply(auto simp add: test_bit_of_take_bits length_sublist min_def 7 8 split: if_split_asm)[1]
      apply(auto simp add: test_bit_of_take_bits length_sublist min_def 7 8 split: if_split_asm)[1]
      using assms apply (auto)[1]
      using assms apply (auto)[1]
      using [[linarith_split_limit = 20]]
      apply(auto simp add: test_bit_of_take_bits length_sublist min_def 7 8 split: if_split_asm)[1]
      using [[linarith_split_limit = 9]]
      using assms 0 apply (auto)[1]
      using [[linarith_split_limit = 13]]
      using assms 0 apply (auto)[1]
      using [[linarith_split_limit = 20]]
      apply(auto simp add: test_bit_of_take_bits length_sublist min_def 7 8 split: if_split_asm)[1]
      using [[linarith_split_limit = 9]]
      using assms 0 apply (auto)[1]
      using assms 0 apply (auto)[1]
      done
  }
  thus ?thesis
    using True
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed



text \<open>
  @{term cat_bytes} when the lower bound is larger than the upper bound.
\<close>
lemma bytes_of_large_lowerbound:
  fixes w :: "64 word"
  assumes "l > h"
  shows "(\<lbrace>h,l\<rbrace>w) = []"
  using assms
  by (auto simp add:  bytes_of_def)


text \<open>
  This lemma rewrites taking bytes and then concatenating them to taking a set of bits.
\<close>
lemma rewrite_cat_bytes_to_take_bits:
  fixes w :: "'a::len0 word"
  assumes "7 + h * 8 < LENGTH('a)"
  shows "((cat_bytes (\<lbrace>h,l\<rbrace>w))::'b::len0 word) = (if l > h then 0 else \<langle>(h+1)*8-1,l*8\<rangle> w)"
proof(cases "l > h")
  case True
  thus ?thesis
    by (auto simp add: bytes_of_def)
next
  case False
  {
    fix i :: nat
    assume 1: "i < LENGTH ('b)"
    have 3: "h \<noteq> l \<Longrightarrow> h \<ge> Suc l"
      using False assms
      by (auto)
    hence 2: "min (Suc h) (Suc h - l) = Suc h - l"
      by (auto)
    have 4: "i < 8 + h * 8 - l * 8 \<Longrightarrow> i div 8 < Suc h - l"
      by (auto)
    have 5: "Suc (Suc (LENGTH('a) div 8 + h - Suc l)) - LENGTH('a) div 8 = Suc h - l"
    proof(cases "h=l")
      case True
      thus ?thesis
        using assms False
        by (cases "LENGTH('a) div 8 = 0";auto simp add: min_def field_simps)
    next
      case False
      thus ?thesis
        using assms 3
        by (auto simp add: min_def field_simps)
    qed


    {
      fix i h::nat
      have "i \<le> 7 + h * 8 \<Longrightarrow> 7 - (7 + h * 8 - i) mod 8 = i mod 8"
      proof(induct h arbitrary: i)
        case 0
        thus ?case
          by auto
      next
        case (Suc h)
        show ?case
          using Suc(2-)
          using Suc(1)[of "i-8"]
          apply (cases "i\<le> 8",auto simp add: le_mod_geq)
          apply (cases "i=0",auto)[1]
          apply (cases "i=1",auto)[1]
          apply (cases "i=2",auto)[1]
          apply (cases "i=3",auto)[1]
          apply (cases "i=4",auto)[1]
          apply (cases "i=5",auto)[1]
          apply (cases "i=6",auto)[1]
          apply (cases "i=7",auto)[1]
          by (cases "i=8",auto)[1]
      qed
    }
    note 9 = this
    have 99: "i < h * 8 \<Longrightarrow> 7 - (h * 8 - Suc i) mod 8 = i mod 8"
    proof(induct h arbitrary: i)
      case 0
      thus ?case
        by auto
    next
      case (Suc h)
      show ?case
        using Suc(2-) Suc(1)[of "i-8"] 
        by (cases "i\<le> 8";cases "h=0";auto simp add: 9)
    qed
    have 10: "i < 8 + h * 8 \<Longrightarrow> i div 8 * 8 + 7 - (7 + h * 8 - i) mod 8 = i"
      using assms 9[of i h]
      using mod_div_mult_eq[of i 8]
      apply (auto)
      by (smt Groups.add_ac(2) Nat.diff_add_assoc Suc_numeral \<open>i mod 8 + i div 8 * 8 = i\<close> cancel_comm_monoid_add_class.diff_cancel leI le_mod_geq less_trans_Suc mod_if mod_less_divisor order_refl pl_pl_mm semiring_norm(2) semiring_norm(8) zero_less_numeral zero_neq_numeral)

    have 11: "i < (Suc h - l) * 8 \<Longrightarrow> i < 8 + h * 8 - l * 8 \<Longrightarrow> \<not> Suc h \<le> Suc h - l \<Longrightarrow> i div 8 * 8 + (7 - ((Suc h - l) * 8 - Suc i) mod 8) = i"
      using assms False
      apply (subst mod_mult_sub[of _ _ _ h])
      using Suc_leI apply blast
      apply (meson Suc_leI leI less_le_trans rel_simps(51) td_gal_lt)
      by (auto simp add: 99)

    have "((cat_bytes (\<lbrace>h,l\<rbrace>w))::'b::len0 word) !! i = ((\<langle>(h+1)*8-1,l*8\<rangle> w) :: 'b::len0 word) !! i"
      using assms 1
      apply (auto simp add: 2 5 10 test_bit_of_cat_bytes test_bit_of_take_bits)
      apply (subst (asm) rev_nth)
      using False apply auto[1]
      apply (auto simp add: nth_bytes_of)[1]
      apply (subst(asm) nth_bytes_of)
      using False apply (auto simp add: 5 min_def)[1]
      using False apply (auto simp add: 5 min_def test_bit_of_byte_of split: if_split_asm)[1]
      apply (cases "l=0",auto simp add: 10)[1]
      using 11 apply (smt Groups.add_ac(2) Groups.add_ac(3))

      apply (subst rev_nth)
      using False apply auto[1]
      apply (auto simp add: nth_bytes_of)[1]
      apply (subst nth_bytes_of)
      using False apply (auto simp add: 5 min_def)[1]
      using False apply (auto simp add: 5 min_def test_bit_of_byte_of split: if_split_asm)[1]
      apply (cases "l=0",auto simp add: 10)[1]
      using 11 apply (smt Groups.add_ac(2) Groups.add_ac(3))
      done
  }
  thus ?thesis
    apply (intro word_eqI)
    using False
    by (auto simp add: word_size)
qed

lemma cat_bytes_singleton[simp]:
  shows "((cat_bytes [b])::'a::len0 word) = \<langle>7,0\<rangle>b"
proof-
  {
    fix i :: nat
    assume "i < LENGTH('a)"
    hence "((cat_bytes [b])::'a::len0 word) !! i = ((\<langle>7,0\<rangle>b)::'a::len0 word) !! i"
      apply (simp add: cat_bytes.simps(2))
      using test_bit_size[of b i]
      by (auto simp add: test_bit_of_take_bits nth_ucast nth_shiftl' word_size )
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed


lemma rewrite_bytes_3_0_of_bits_31_0[simp]: (* TODO generalise?*)
  fixes w :: "'a::len0 word"
  assumes "3 < LENGTH('a) div 8"
      and "3 < LENGTH('b) div 8"
  shows "\<lbrace>3,0\<rbrace>((\<langle>31,0\<rangle>w)::'b::len0 word) = \<lbrace>3,0\<rbrace>w"
proof-
  let ?w = "((\<langle>31,0\<rangle>w)::'b::len0 word)"
  {
    fix n :: nat
    assume n: "n < 4"
    have "(\<lbrace>3,0\<rbrace>?w) ! n = (\<lbrace>3,0\<rbrace>w) ! n"
    proof-
      {
        fix m :: nat
        assume "m < 8"
        hence "((\<lbrace>3,0\<rbrace>?w) ! n) !! m = ((\<lbrace>3,0\<rbrace>w) ! n) !! m"
          using n assms
          by (auto simp add: nth_bytes_of test_bit_of_take_bits test_bit_of_byte_of)
      }
      thus ?thesis
        apply (intro word_eqI)
        by (auto simp add: word_size)
    qed
  }
  thus ?thesis
    using assms
    apply (intro nth_equalityI)
    by auto
qed

lemma rewrite_bytes_7_4_of_bits_31_0[simp]:
  fixes w :: "'a::len0 word"
  assumes "3 < LENGTH('a) div 8"
      and "7 < LENGTH('b) div 8"
  shows "\<lbrace>7,4\<rbrace>((\<langle>31,0\<rangle>w)::'b::len0 word) = [0,0,0,0]"
proof-
  let ?w = "((\<langle>31,0\<rangle>w)::'b::len0 word)"
  {
    fix n :: nat
    assume n: "n < 4"
    have "(\<lbrace>7,4\<rbrace>?w) ! n = 0"
    proof-
      {
        fix m :: nat
        assume "m < 8"
        hence "((\<lbrace>7,4\<rbrace>?w) ! n) !! m = (0::8 word) !! m"
          using n assms
          by (auto simp add: nth_bytes_of test_bit_of_take_bits test_bit_of_byte_of)
      }
      thus ?thesis
        apply (intro word_eqI)
        by (auto simp add: word_size)
    qed
  }
  thus ?thesis
    using assms
    apply (intro nth_equalityI)
    by (auto simp add: nth_Cons')
qed


lemma rewrite_bytes_3_0_of_bits_63_32[simp]:
  fixes w :: "'a::len0 word"
  assumes "7 < LENGTH('a) div 8"
      and "3 < LENGTH('b) div 8"
  shows "\<lbrace>3,0\<rbrace>((\<langle>63,32\<rangle>w)::'b::len0 word) = \<lbrace>7,4\<rbrace>w"
proof-
  let ?w = "((\<langle>63,32\<rangle>w)::'b::len0 word)"
  {
    fix n :: nat
    assume n: "n < 4"
    have "(\<lbrace>3,0\<rbrace>?w) ! n = (\<lbrace>7,4\<rbrace>w) ! n"
    proof-
      {
        fix m :: nat
        assume "m < 8"
        have 1: "32 + ((3 - n) * 8 + m) = (7 - n) * 8 + m"
          using n
          by auto
        have "((\<lbrace>3,0\<rbrace>?w) ! n) !! m = ((\<lbrace>7,4\<rbrace>w) ! n) !! m"
          using n assms
          apply (auto simp add: nth_bytes_of test_bit_of_take_bits test_bit_of_byte_of)
          apply (subst (asm) 1,simp)
          by (subst 1,simp)
      }
      thus ?thesis
        apply (intro word_eqI)
        by (auto simp add: word_size)
    qed
  }
  thus ?thesis
    using assms
    apply (intro nth_equalityI)
    by auto
qed

lemma rewrite_bytes_7_4_of_bits_63_32[simp]:
  fixes w :: "'a::len0 word"
  assumes "7 < LENGTH('a) div 8"
      and "7 < LENGTH('b) div 8"
  shows "\<lbrace>7,4\<rbrace>((\<langle>63,32\<rangle>w)::'b::len0 word) = [0,0,0,0]"
proof-
  let ?w = "((\<langle>63,32\<rangle>w)::'b::len0 word)"
  {
    fix n :: nat
    assume n: "n < 4"
    have "(\<lbrace>7,4\<rbrace>?w) ! n = 0"
    proof-
      {
        fix m :: nat
        assume "m < 8"
        hence "((\<lbrace>7,4\<rbrace>?w) ! n) !! m = (0::8 word) !! m"
          using n assms
          by (auto simp add: nth_bytes_of test_bit_of_take_bits test_bit_of_byte_of)
      }
      thus ?thesis
        apply (intro word_eqI)
        by (auto simp add: word_size)
    qed
  }
  thus ?thesis
    using assms
    apply (intro nth_equalityI)
    by (auto simp add: nth_Cons')
qed




lemma bytes_ucast_bit32[simp]:
  fixes a :: "32 word"
  assumes "LENGTH('a) \<ge> 32"
  shows "\<lbrace>3,0\<rbrace>((ucast a)::'a::len0 word) = \<lbrace>3,0\<rbrace>a"
proof-
  {
    fix i :: nat
    assume i: "i < 4"
    have "(\<lbrace>3,0\<rbrace>((ucast a)::'a::len0 word)) ! i = (\<lbrace>3,0\<rbrace>a) ! i"
    proof-
      {
        fix j :: nat
        assume "j < 8"
        hence "((\<lbrace>3,0\<rbrace>((ucast a)::'a::len0 word)) ! i) !! j = ((\<lbrace>3,0\<rbrace>a) ! i) !! j"
          using i assms
          by (auto simp add: nth_bytes_of nth_ucast test_bit_of_byte_of)
      }
      thus ?thesis
        apply (intro word_eqI)
        by (auto simp add: word_size)
    qed
  }  
  thus ?thesis
    using assms
    apply (intro nth_equalityI)
     apply (auto)
qed



end
