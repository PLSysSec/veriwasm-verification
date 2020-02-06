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

theory Memory_Rewriting
  imports
      Byte_Rewriting
      "~~/src/HOL/Eisbach/Eisbach"
begin

section "Rewrite rules for reading and writing memory"

subsection "Get and set"

definition "get' \<equiv> get"
lemma get_rewrite:
  shows "get (f(k := v)) a = (if a = k then v else let' ret = get' f a in ret)"
  by (auto simp add: get_def Let'_def get'_def)
lemma get_simp_reg:
  shows "get (regs \<sigma>) r = regs \<sigma> r"
  unfolding get_def
  by auto
lemma get_simp_flg:
  shows "get (flags \<sigma>) r = flags \<sigma> r"
  unfolding get_def
  by auto
lemma get_simp_mem:
  shows "get (mem \<sigma>) r = mem \<sigma> r"
  unfolding get_def
  by auto

definition "set' \<equiv> set"
lemma set_simp:
  shows "set (f(k := v)) a b = (if a = k then f(k := b) else let' f' = set' f a b in f'(k := v))"
  unfolding set_def
  by (auto simp add: Let'_def set'_def set_def)
lemma set_simp_reg:
  shows "set (regs \<sigma>) r v = (regs \<sigma>)(r := v)"
  unfolding set_def
  by auto
lemma set_simp_flg:
  shows "set (flags \<sigma>) r v = (flags \<sigma>)(r := v)"
  unfolding set_def
  by auto
lemma set_simp_mem:
  shows "set (mem \<sigma>) r v = (mem \<sigma>)(r := v)"
  unfolding set_def
  by auto

text {*
  Use these rewrite rules:
*}
lemmas get_set_rewrite_rules =
    write_flg_def read_flg_def set_simp_flg get_simp_flg
    get_rewrite get_simp_reg get_simp_mem set_simp set_simp_reg set_simp_mem



subsection "Separation and enclosure of blocks"

text {*
  Two blocks in memory are \emph{separated} iff they have no shared address.
  Note this definition works only if the blocks do not overflow.
*}
fun sep :: "64 word \<times> nat \<Rightarrow> 64 word \<times> nat \<Rightarrow> bool" (infixl "\<bowtie>" 65)
  where "(a,s) \<bowtie> (a',s') = (s = 0 \<or> s' = 0 \<or> a + of_nat s \<le> a' \<or> a' + of_nat s' \<le> a)"

text {*
  Two blocks are \emph{enclosed} if all addresses in the first block are within the second block.
  Note this definition works only if the blocks do not overflow.
*}
fun enclosed :: "(64 word \<times> nat) \<Rightarrow> (64 word \<times> nat) \<Rightarrow> bool" (infixl "\<sqsubseteq>" 65)
  where "(a0,s0) \<sqsubseteq> (a1,s1) = (a0 \<ge> a1 \<and> a0 + of_nat s0 \<le> a1 + of_nat s1)"
definition "enclosed'' \<equiv> enclosed"

text {*
  Rewrite rules are based on the \emph{master} of the blocks used in the assembly code.
  If a block @{term a} has master @{term b}, then @{term "a \<sqsubseteq> b"} and block @{term b} is a member of a set of
  predefined blocks. Function \emph{seps} can be used to formulate an assumption stating that
  that set of blocks does not overflow, and is mutually separate.

  Reasoning is set up as follows: to check @{term "a \<bowtie> b"}, find the masters of @{term a} and @{term b},
  and check whether they are different. Different masters implies separate blocks.
  Two easily identify whether blocks are different, we use IDs.
  Similarly, @{term "\<not>a \<sqsubseteq> b"} can be checked: different masters implies non-enclosure.

  We have set up a method find\_master which can be used to find the master of a given block.
*}
definition master :: "(nat \<times> 64 word \<times> nat) set \<Rightarrow> 64 word \<times> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "master blocks a i \<equiv> no_block_overflow a \<and> (\<exists> b \<in> blocks . fst b = i \<and> a \<sqsubseteq> snd b)"

definition seps :: "(nat \<times> 64 word \<times> nat) set \<Rightarrow> bool"
  where "seps x \<equiv>
          (\<forall> (i,b) \<in> x . \<forall> (i',b') \<in> x . i = i' \<longrightarrow> b = b') \<and>
          (\<forall> (i,a,s) \<in> x . no_block_overflow (a,s) \<and> (\<forall> (i',a',s') \<in> x . (i \<noteq> i' \<longrightarrow> (a,s) \<bowtie> (a',s'))))"


lemma enclosed_reflexive[simp]:
  shows "b \<sqsubseteq> b"
  by (cases b,auto)

lemma sep_enclosed:
  assumes "no_block_overflow a"
      and "a \<sqsubseteq> a'"
      and "a' \<bowtie> b"
    shows "a \<bowtie> b"
  using assms
  apply (cases a, cases a',cases b,auto simp add: no_block_overflow.simps)
  apply unat_arith
  by (auto simp add: unat_of_nat)

lemma master_if_in_blocks:
  assumes "seps blocks"
      and "(i,a) \<in> blocks"
    shows "master blocks a i"
proof-
  have "no_block_overflow a"
    using assms
    unfolding seps_def
    by auto
  moreover
  have "(i,a) \<in> blocks \<and> fst (i,a) = i \<and> a \<sqsubseteq> snd (i,a)"
    using assms(2)
    by (auto)
  ultimately
  show ?thesis
    unfolding master_def
    by metis
qed

lemma seps_implies_no_block_overflow:
  assumes "seps blocks"
      and "(i,a) \<in> blocks"
    shows "no_block_overflow a"
  using assms
  unfolding seps_def
  by auto

lemma master_of_enclosed:
  assumes "seps blocks"
      and "no_block_overflow a"
      and "(i,b) \<in> blocks"
      and "a \<sqsubseteq> b"
    shows "master blocks a i"
    using assms
    unfolding master_def
    by force

lemma sep_implies_not_enclosed:
  assumes "a \<bowtie> b"
      and "no_block_overflow a"
      and "snd a > 0"
      and "snd b > 0"
    shows "\<not>a \<sqsubseteq> b"
  using assms
  apply (cases a, cases b,auto simp add: no_block_overflow.simps)
  apply unat_arith
  apply (auto simp add: unat_of_nat)
  apply unat_arith
  by (auto simp add: unat_of_nat)


lemma block_right_implies_not_enclosed:
assumes "a \<ge> a' + of_nat s'"
    and "no_block_overflow (a,s)"
    and "s \<noteq> 0"
  shows "\<not>(a,s) \<sqsubseteq> (a',s')"
proof-
  have "a \<le> a + of_nat s"
    using assms
    unfolding enclosed.simps no_block_overflow.simps
    apply (auto)
    apply unat_arith
    by (auto simp add: unat_of_nat)
  thus ?thesis
    using assms
    unfolding enclosed.simps no_block_overflow.simps
    apply (cases "a = a' + of_nat s'",auto)
    apply unat_arith
    by (auto simp add: unat_of_nat)
qed

lemma not_enclosed_right_block_negative_offset[simp]:
  assumes "no_block_overflow (a,s)"
      and "a \<ge> offset + 1"
      and "offset \<noteq> 2^64 - 1"
      and "s' \<le> unat offset"
      and "s \<noteq> 0"
    shows "\<not>(a, s) \<sqsubseteq> (a - offset, s')"
proof-
  have 1: "a - offset + of_nat s' = a - (offset - of_nat s')"
    using assms
    unfolding enclosed.simps no_block_overflow.simps
    by (auto simp add: unat_sub)
  have "offset < a"
    using assms(2,3)
    apply unat_arith
    by (auto)
  hence "a \<ge> a - offset + of_nat s'"
    using assms(1,4-)
    unfolding enclosed.simps no_block_overflow.simps
    apply (auto)
    apply (subst 1)
    apply (subst a_minus_b_le)
    apply unat_arith
    by (auto simp add: unat_of_nat)
  thus ?thesis
    apply (rule block_right_implies_not_enclosed)
    using assms(1,5)
    by simp+
qed


lemma no_block_overflow_smaller_block_negative_offset:
assumes "no_block_overflow (a - offset, s)"
    and "a \<ge> offset"
    and "a \<ge> offset'"
    and "s' - unat offset' \<le> s - unat offset"
  shows "no_block_overflow (a - offset',s')"
proof-
  have "unat a + s' - unat offset' < 18446744073709551616"
    using assms(1,2,4)
    apply (auto simp add: no_block_overflow.simps unat_sub_if' word_le_nat_alt split: if_split_asm)
    apply unat_arith
    by auto
  moreover
  have "unat offset' \<le> unat a"
    using assms(3)
    by unat_arith
  ultimately
  show ?thesis
    by (auto simp add: no_block_overflow.simps unat_sub_if')
qed

lemma sep_symmetric[symmetric]:
    shows "a \<bowtie> b = b \<bowtie> a"
  by (cases a, cases b,auto simp add:)


lemma no_block_overflow_smaller_block_positive_offset:
assumes "no_block_overflow (a, s)"
    and "unat offset + s' \<le> s"
  shows "no_block_overflow (offset + a ,s')"
proof-
  show ?thesis
    using assms
    apply (auto simp add: no_block_overflow.simps )
    by unat_arith
qed

lemma no_block_overflow_smaller_block_positive_offset_r:
assumes "no_block_overflow (a, s)"
    and "unat offset + s' \<le> s"
  shows "no_block_overflow (a + offset ,s')"
proof-
  show ?thesis
    using assms
    apply (auto simp add: no_block_overflow.simps )
    by unat_arith
qed

lemma no_block_overflow_smaller_block:
  assumes \<open>no_block_overflow (a, s)\<close>
      and \<open>s' \<le> s\<close>
    shows \<open>no_block_overflow (a, s')\<close>
  using assms
  by (simp add: no_block_overflow.simps)

lemma no_block_overflow_contained_block_negative_offset:
  assumes \<open>no_block_overflow (a - offset, s)\<close>
      and \<open>offset' \<le> a'\<close>
      and \<open>unat a' - unat offset' + s' \<le> unat a - unat offset + s\<close>
    shows \<open>no_block_overflow (a' - offset', s')\<close>
proof -
  have \<open>unat a' - unat offset' + s' < 18446744073709551616\<close> \<comment> \<open>2^64\<close>
    using assms
    by (auto simp add: no_block_overflow.simps unat_sub_if' split: if_split_asm)
  moreover have \<open>unat offset' \<le> unat a'\<close>
    using assms
    by unat_arith
  ultimately show ?thesis
    by (auto simp add: no_block_overflow.simps unat_sub_if')
qed


lemma master_blocks_implies_sep:
  assumes "seps blocks"
      and "master blocks a i"
      and "master blocks a' i'"
  shows "a \<bowtie> a' = (i\<noteq>i' \<or> snd a = 0 \<or> snd a' = 0 \<or> (fst a + of_nat (snd a) \<le> fst a' \<or> fst a' + of_nat (snd a') \<le> fst a))"
proof-
  obtain b b' where b : "(i,b) \<in> blocks \<and> a \<sqsubseteq> b"
                and b': "(i',b') \<in> blocks \<and> a' \<sqsubseteq> b'"
    using assms
    by (auto simp add: master_def)
  show ?thesis
  proof(cases "i=i'")
    case False
    have "\<forall> (i', b') \<in> blocks . i \<noteq> i' \<longrightarrow> b \<bowtie> b'"
      using assms(1)[unfolded seps_def Ball_def, THEN conjunct2,THEN spec, of "(i,b)"]
            b b'
      by (cases b,auto simp add: seps_def case_prod_unfold)
    hence "b \<bowtie> b'"
      using False b'
      by auto
    thus ?thesis
      using sep_enclosed[of a b a'] sep_enclosed[of a' b' b]
      using sep_symmetric[of a' b]  sep_symmetric[of b' b] b b'
      using assms False
      by (auto simp add: master_def)
  next
    case True
    thus ?thesis
      using b b'
      by (cases a, cases a',auto)
  qed
qed

lemma master_block_implies_no_block_overflow:
  assumes "master blocks a i"
    shows "no_block_overflow a"
  using assms
  unfolding seps_def master_def
  by (auto simp add: case_prod_unfold)

lemma no_overflow_explicit[simp]:
  assumes \<open>master blocks (a, unat s) i\<close>
   and \<open>a = a'\<close>
 shows \<open>a' \<le> max_word - s\<close>
proof -
  have \<open>no_block_overflow (a', unat s)\<close>
    using assms
    by (simp add: master_block_implies_no_block_overflow)
  then show ?thesis
    using assms
    by (simp add: no_block_overflow.simps max_word_eq) unat_arith
qed

lemma master_blocks_implies_enclosed:
  assumes "seps blocks"
      and "(i,b) \<in> blocks"
      and "master blocks a i"
    shows "a \<sqsubseteq> b"
proof-
  obtain b' where b': "(i,b') \<in> blocks \<and> a \<sqsubseteq> b'"
    using assms
    by (auto simp add: master_def)
  hence "b = b'"
    using assms(1)[unfolded seps_def,THEN conjunct1] assms(2)
    by (auto simp add: case_prod_unfold)
  thus ?thesis
    using b'
    by auto
qed

lemma master_blocks_implies_not_enclosed:
  assumes "seps blocks"
      and "master blocks a i"
      and "master blocks b i'"
      and "snd a > 0"
      and "snd b > 0"
      and "i \<noteq> i'"
    shows "\<not>a \<sqsubseteq> b"
proof-
  have "a \<bowtie> b"
    using assms master_blocks_implies_sep[OF assms(1),of a i b i']
    by (auto)
  thus ?thesis
    using sep_implies_not_enclosed[of a b] assms
    unfolding master_def
    by auto
qed

lemma enclosed_minus:
  shows "(a - offset,s) \<sqsubseteq> (a - offset',s') =
            (if offset \<le> a \<and> offset' \<le> a then
              (offset' \<ge> offset \<and> a - offset + of_nat s \<le> a - offset' + of_nat s')
             else
              enclosed'' (a - offset,s) (a - offset',s'))"
  by (auto simp add: enclosed''_def)

lemma enclosed_minus_numeral:
  shows "(a - ((numeral x)::64 word),s) \<sqsubseteq> (a - ((numeral x')::64 word),s') =
            (if ((numeral x)::64 word) \<le> a \<and> ((numeral x')::64 word) \<le> a then
              (((numeral x')::64 word) \<ge> ((numeral x)::64 word) \<and> a - ((numeral x)::64 word) + of_nat s \<le> a - ((numeral x')::64 word) + of_nat s')
             else
              enclosed'' (a - ((numeral x)::64 word),s) (a - ((numeral x')::64 word),s'))"
  using enclosed_minus
  by force

lemma enclosed_plus:
  shows "(n + a,s) \<sqsubseteq> (a,s') =
            (if unat n + unat a + s < 2^64 \<and> unat a + s' < 2 ^64 then n + of_nat s \<le> of_nat s' else enclosed'' (n + a, s) (a,s'))"
proof-
  have "unat n + unat a + s < 2^64 \<Longrightarrow> unat a + unat (n + of_nat s) = unat n + unat a + s"
    apply unat_arith
    by (auto simp add: unat_of_nat)
  hence 1: "unat n + unat a + s < 2^64 \<Longrightarrow> a \<le> a + (n + of_nat s)"
    by (auto simp add: no_olen_add_nat)
  have 2: "unat a + s' < 2 ^64 \<Longrightarrow> a \<le> a + of_nat s'"
    apply unat_arith
    by (auto simp add: unat_of_nat)
  have 3: "a + (n + of_nat s) = n + a + of_nat s"
    by auto
  have 4: "unat n + unat a + s < 2^64 \<Longrightarrow> a \<le> n + a"
    apply unat_arith
    by (auto simp add: unat_of_nat)
  show ?thesis
    using plus_less_left_cancel_nowrap[of a "n + of_nat s" "of_nat s'"] 1 2 3 4
    by (auto simp add: enclosed''_def)
qed

lemma enclosed_plus_r:
  shows "(a + n,s) \<sqsubseteq> (a,s') =
            (if unat n + unat a + s < 2^64 \<and> unat a + s' < 2 ^64 then n + of_nat s \<le> of_nat s' else enclosed'' (n + a, s) (a,s'))"
  using enclosed_plus[of n a s s'] add.commute[of n a]
  by metis


lemma enclosed_plus_numeral:
  shows "(((numeral x)::64 word) + a,s) \<sqsubseteq> (a,s') =
            (if unat ((numeral x)::64 word) + unat a + s < 2^64 \<and> unat a + s' < 2 ^64 then ((numeral x)::64 word) + of_nat s \<le> of_nat s' else enclosed'' (((numeral x)::64 word) + a, s) (a,s'))"
  using enclosed_plus
  by force

lemma enclosed_plus_numeral_r:
  shows "(a + ((numeral x)::64 word),s) \<sqsubseteq> (a,s') =
            (if unat ((numeral x)::64 word) + unat a + s < 2^64 \<and> unat a + s' < 2 ^64 then ((numeral x)::64 word) + of_nat s \<le> of_nat s' else enclosed'' (((numeral x)::64 word) + a, s) (a,s'))"
  using enclosed_plus_r
  by force


lemma unfold_enclosed_same_block:
  \<open>(a + offset, s) \<sqsubseteq> (a + offset', s') \<longleftrightarrow> a + offset' \<le> a + offset \<and> a + offset + of_nat s \<le> a + offset' + of_nat s'\<close>
  by (auto simp add: enclosed.simps)
lemmas unfold_enclosed_same_block_0l[simp] = unfold_enclosed_same_block[where offset=0,simplified]
lemmas unfold_enclosed_same_block_0r[simp] = unfold_enclosed_same_block[where offset'=0,simplified]


declare sep.simps[simp del]
declare enclosed.simps(1)[simp del]
lemmas sep_enclosed_simps =
  master_blocks_implies_sep
  master_block_implies_no_block_overflow
  master_blocks_implies_not_enclosed
  master_blocks_implies_enclosed
  enclosed_plus_numeral enclosed_plus_numeral_r enclosed_minus_numeral
  unfold_enclosed_same_block unfold_enclosed_same_block_0l unfold_enclosed_same_block_0r

method find_master_same_block uses assms =
  match conclusion in "master blocks b i" for blocks b i \<Rightarrow> \<open>
      match assms in A: "(i, b) \<in> blocks" \<Rightarrow> \<open>
        match assms in B: "seps blocks" \<Rightarrow> \<open>
          rule master_if_in_blocks[OF B A]
        \<close>
      \<close>
    \<close>

method find_master_larger_block_negative_offset uses assms add =
  match conclusion in "master blocks (a - offset,s) i" for blocks a offset s i \<Rightarrow> \<open>
      match assms in A: "(i, a - offset',s') \<in> blocks" for offset' s' \<Rightarrow> \<open>
        match assms in B: "seps blocks" \<Rightarrow> \<open>
          rule master_of_enclosed[OF B _ A],
          rule no_block_overflow_smaller_block_negative_offset[of _ offset' s'],
          rule seps_implies_no_block_overflow[OF B A],
          simp add: add,
          simp add: add,
          simp add: add,
          simp add: add enclosed_minus enclosed_plus enclosed_plus_r sep_enclosed_simps
        \<close>
      \<close>
    \<close>

method find_master_larger_block_positive_offset uses assms add =
  match conclusion in "master blocks (offset + a,s) i" for blocks a offset s i \<Rightarrow> \<open>
      match assms in A: "(i, a ,s') \<in> blocks" for s' \<Rightarrow> \<open>
        match assms in B: "seps blocks" \<Rightarrow> \<open>
          rule master_of_enclosed[OF B _ A],
          rule no_block_overflow_smaller_block_positive_offset[of a s'],
          rule seps_implies_no_block_overflow[OF B A],
          simp add: add,
          insert enclosed_plus enclosed_plus_r seps_implies_no_block_overflow[OF B A],
          simp add: add enclosed_minus enclosed_plus enclosed_plus_r sep_enclosed_simps no_block_overflow.simps
        \<close>
      \<close>
    \<close>
method find_master_larger_block_positive_offset_r uses assms add =
  match conclusion in "master blocks (a + offset,s) i" for blocks a offset s i \<Rightarrow> \<open>
      match assms in A: "(i, a ,s') \<in> blocks" for s' \<Rightarrow> \<open>
        match assms in B: "seps blocks" \<Rightarrow> \<open>
          rule master_of_enclosed[OF B _ A],
          rule no_block_overflow_smaller_block_positive_offset_r[of a s'],
          rule seps_implies_no_block_overflow[OF B A],
          simp add: add,
          insert enclosed_plus enclosed_plus_r seps_implies_no_block_overflow[OF B A],
          simp add: add enclosed_minus enclosed_plus enclosed_plus_r sep_enclosed_simps no_block_overflow.simps
        \<close>
      \<close>
    \<close>

method find_master_larger_block_positive_offset_r' uses assms add =
  match conclusion in \<open>master blocks (a + offset, s) i\<close> for blocks a offset s i \<Rightarrow> \<open>
    match assms in A: \<open>(i, a, s') \<in> blocks\<close> for s' \<Rightarrow> \<open>
      match assms in B: \<open>seps blocks\<close> \<Rightarrow> \<open>
        rule master_of_enclosed[OF B _ A],
        rule no_block_overflow_smaller_block_positive_offset_r[of a s'],
        rule seps_implies_no_block_overflow[OF B A],
        simp add: add,
        insert seps_implies_no_block_overflow[OF B A],
        simp add: add enclosed.simps no_block_overflow.simps,
        unat_arith,
        auto
      \<close>
    \<close>
  \<close>


method find_master_larger_block uses assms add =
  match conclusion in \<open>master blocks (a, s) i\<close> for blocks a s i \<Rightarrow> \<open>
    match assms in A: \<open>(i, a, s') \<in> blocks\<close> for s' \<Rightarrow> \<open>
      match assms in B: \<open>seps blocks\<close> \<Rightarrow> \<open>
        rule master_of_enclosed[OF B _ A],
        rule no_block_overflow_smaller_block[of a s'],
        rule seps_implies_no_block_overflow[OF B A],
        simp add: add,
        insert seps_implies_no_block_overflow[OF B A],
        simp add: add enclosed.simps no_block_overflow.simps,
        unat_arith,
        auto
      \<close>
    \<close>
  \<close>


method find_master_contained_block_negative_offset uses assms add =
  match conclusion in \<open>master blocks (a - offset, s) i\<close> for blocks a offset s i \<Rightarrow> \<open>
    match assms in A: \<open>(i, a' - offset', s') \<in> blocks\<close> for a' offset' s' \<Rightarrow> \<open>
      match assms in B: \<open>seps blocks\<close> \<Rightarrow> \<open>
        match assms in C: \<open>unat a = unat a' - offset_step\<close> for offset_step \<Rightarrow> \<open>
          rule master_of_enclosed[OF B _ A],
          rule no_block_overflow_contained_block_negative_offset[of a' offset' s'],
          rule seps_implies_no_block_overflow[OF B A],
          simp add: add,
          simp add: add unat_word_ariths unat_of_nat,
          (auto simp add: add enclosed.simps)[1],
          (insert assms)[1],
          unat_arith, (* takes a while but works *)
          (auto simp add: add unat_word_ariths unat_of_nat)[1],
          (insert assms)[1],
          unat_arith
        \<close>
      \<close>
    \<close>
  \<close>


method find_master uses assms add =
    find_master_same_block assms: assms
  | find_master_larger_block assms: assms
  | find_master_larger_block_negative_offset    assms: assms add: add
  | find_master_larger_block_positive_offset    assms: assms add: add
  | find_master_larger_block_positive_offset_r  assms: assms add: add
  | find_master_larger_block_positive_offset_r' assms: assms add: add
  | find_master_contained_block_negative_offset assms: assms add: add


subsection "Write blocks into memory"

text {*
  When a block is written into the memory and there exists a non-separate block, then these two blocks have to be \emph{merged}.
  Mergin means: overwrite block $b_0$ with block $b_1$ wherever possible.
*}
fun merge_blocks :: "(64 word \<times> 8 word list) \<Rightarrow> (64 word \<times> 8 word list) \<Rightarrow> (64 word \<times> 8 word list)"
  where "merge_blocks (a0,bs0) (a1,bs1) =
        (min a0 a1 ,
          (take (if a0 < a1 then unat (a1 - a0) else 0) bs0)
          @ bs1
          @ drop (if unat a1 + length bs1 < unat a0 + length bs0 then unat a1 + length bs1 - unat a0 else length bs0) bs0)"


value "merge_blocks (10, [0,1,2,3,4,5,6]) (5,[10,11,12,13,14,15,16,17])"
value "merge_blocks (10, [0,1,2,3,4,5,6]) (15,[10,11,12,13,14,15,16,17])"
value "merge_blocks (10, [0,1,2,3,4,5,6]) (9,[9,10,11,12,13,14,15,16,17])"
value "merge_blocks (10, [0,1,2,3,4,5,6]) (9,[9,10,11,12])"
value "merge_blocks (7, [0,1,2,3,4,5,6,7,8,9]) (9,[10,11,12])"



text {*
  This theorem characterizes @{term write_bytes}: that function will update the memory with all
  addresses within the block. Outside the block, the memory is unchanged.
*}
lemma spec_of_write_bytes:
  assumes "no_block_overflow (fst block, length (snd block))"
  shows "write_bytes block m x =
            (if fst block \<le> x \<and> x < fst block + of_nat (length (snd block)) then
                (snd block)!(unat (x - (fst block)))
             else
                m x)"
  using assms
proof(induct block m rule: write_bytes.induct)
  case (1 a m)
  then show ?case
    by auto
next
  case (2 a b bs m)
  have 0: "1 + a \<noteq> 0"
    using max_word_wrap[of a] 2
    by (auto simp add: max_word_def no_block_overflow.simps algebra_simps)
  hence 1: "unat a < 2 ^ 64 - 1"
    using max_word_max[of a]
    apply (cases "a=2^64-1",auto simp add: max_word_def)
    apply (subst word_less_nat_alt[of a "2^64-1",simplified,symmetric])
    by auto
  moreover
  hence 3: "a < a + 1"
    using 0
    by (cases "a = 2^64-1",auto simp add: word_less_nat_alt unat_plus_if' unat_of_nat split: if_split_asm)
  moreover
  have "(1::64 word) + of_nat (length bs) \<noteq> 0"
   and "length bs < 2 ^ 64"
   and "unat a + unat ((1::64 word) + of_nat (length bs)) < 2^64"
    using max_word_wrap[of "(of_nat (length bs))::64 word"] 1 2
    apply (auto simp add: max_word_def algebra_simps no_block_overflow.simps)
    by (auto simp add: of_nat_eq unat_plus_if' unat_of_nat)
  hence 4: "a < a + (1 + of_nat (length bs))"
    by (cases "length bs = 2^64-1",auto simp add: word_less_nat_alt unat_plus_if' unat_of_nat split: if_split_asm)
  moreover
  have 5: "no_block_overflow (a + 1, length bs)"
    using 2 unat_plus_simple[of a 1] 3
    by (auto simp add: algebra_simps no_block_overflow.simps)
  moreover
  have 6: "(x < a + 1 + of_nat (length bs)) = (x < a + (1 + of_nat (length bs)))"
    using max_word_wrap[of "(of_nat (length bs))::64 word"]
    by (auto simp add: max_word_def algebra_simps)
  ultimately
  show ?case
    using 2(1)[of "m(a := b)"]
    apply (auto simp add: Let'_def Let_def set_def fun_upd_def nth_Cons unat_sub word_le_nat_alt split: if_split_asm nat.splits)
    apply (auto simp add: unat_plus_if' split: if_split_asm )
    by (metis Suc_eq_plus1 diff_Suc_1 diff_diff_add)
qed

text {*
  Writing two separate blocks is commutative.
*}
lemma write_bytes_commute:
  assumes "(fst block0,length (snd block0)) \<bowtie> (fst block1, length (snd block1))"
      and "no_block_overflow (fst block0, length (snd block0))"
      and "no_block_overflow (fst block1, length (snd block1))"
    shows "write_bytes block0 (write_bytes block1 m) = write_bytes block1 (write_bytes block0 m)"
proof-
  {
    fix x
    have "write_bytes block0 (write_bytes block1 m) x = write_bytes block1 (write_bytes block0 m) x"
      using assms(1)
      using spec_of_write_bytes[of block0 "(write_bytes block1 m)" x,OF assms(2)]
      using spec_of_write_bytes[of block1 "(write_bytes block0 m)" x,OF assms(3)]
      using spec_of_write_bytes[of block0 m x,OF assms(2)]
      using spec_of_write_bytes[of block1 m x,OF assms(3)]
      by (auto simp add: sep.simps)
  }
  thus ?thesis
    by auto
qed

text {*
  Writing two non-separate blocks is equal to writing the merge of those blocks.
*}
lemma no_block_overflow_after_merge:
  assumes "no_block_overflow (fst block0, length (snd block0))"
      and "no_block_overflow (fst block1, length (snd block1))"
  shows "no_block_overflow (fst (merge_blocks block0 block1), length (snd (merge_blocks block0 block1)))"
  using assms
  apply (cases block0,cases block1,auto simp add: min_def no_block_overflow.simps)
  by unat_arith+

lemma write_bytes_nonseparate_is_merge:
  assumes "\<not>(fst block1, length (snd block1)) \<bowtie> (fst block0, length (snd block0))"
      and "no_block_overflow (fst block0, length (snd block0))"
      and "no_block_overflow (fst block1, length (snd block1))"
    shows "write_bytes block1 (write_bytes block0 m) = write_bytes (merge_blocks block0 block1) m"
proof-
  obtain a bs a' bs' s s'
    where 2: "block0 = (a,bs)"
      and 3: "block1 = (a',bs')"
      and 4: "length bs = s"
      and 5: "length bs' = s'"
    by (cases block0;cases block1;auto)
  hence 1: "no_block_overflow (fst (merge_blocks block0 block1), length (snd (merge_blocks block0 block1)))"
    using no_block_overflow_after_merge[OF assms(2-3)]
    by (auto)
  {
    fix x
    note unfold_write_bytes =
      spec_of_write_bytes[of block1 "(write_bytes block0 m)" x,OF assms(3)]
      spec_of_write_bytes[of "merge_blocks block0 block1" m x,OF 1]
      spec_of_write_bytes[of block1 m x,OF assms(3)]
      spec_of_write_bytes[of block0 m x,OF assms(2)]

    consider
        (A) "x < min a a'"
      | (B) "a \<le> x \<and> a < a' \<and> x < a'"
      | (C) "a' \<le> x \<and> x < a' + of_nat s'"
      | (D) "a' + of_nat s' \<le> x \<and> x < a + of_nat s"
      | (E) "max (a + of_nat s) (a' + of_nat s') \<le> x"
      using 2 3 4 5
      apply (cases "x < min a a'",auto split: if_split_asm)
      apply (cases "a < a' \<and> x < a'",auto split: if_split_asm)
      apply (cases "a' \<le> x \<and> x < a' + of_nat s'",auto split: if_split_asm)
      apply (cases "a' + of_nat s' \<le> x \<and> x < a + of_nat s",auto split: if_split_asm)
      apply (cases "max (a + of_nat s) (a' + of_nat s') \<le> x",auto)
      apply (cases "a < a' \<and> x < a'",auto split: if_split_asm)
      apply (cases "a' \<le> x \<and> x < a' + of_nat s'",auto split: if_split_asm)
      apply (cases "a' + of_nat s' \<le> x \<and> x < a + of_nat s",auto split: if_split_asm)
      apply (cases "max (a + of_nat s) (a' + of_nat s') \<le> x",auto)
      apply (cases "a < a' \<and> x < a'",auto split: if_split_asm)
      apply (cases "a' \<le> x \<and> x < a' + of_nat s'",auto split: if_split_asm)
      apply (cases "a' + of_nat s' \<le> x \<and> x < a + of_nat s",auto split: if_split_asm)
      by (cases "max (a + of_nat s) (a' + of_nat s') \<le> x",auto)

    hence "write_bytes block1 (write_bytes block0 m) x = write_bytes (merge_blocks block0 block1) m x"
    proof(cases)
      case A
      thus ?thesis
        apply (auto simp add: unfold_write_bytes)
        using 2 3 4 5
        by (auto split: if_split_asm simp add: min_def)
    next
      case B
      moreover
      hence 6: "x < a + of_nat (length bs)"
        using assms(1) 2 3 4 5
        by (auto simp add: sep.simps)
      moreover
      hence "unat x - unat a < length bs"
        using B
        apply unat_arith
        by (auto simp add: unat_of_nat)
      moreover
      have 6: "unat x - unat a < unat a' - unat a"
        using B
        by unat_arith
      moreover
      have "of_nat (unat a' - unat a) = a' - a"
        using B
        apply unat_arith
        by (auto simp add: unat_of_nat)
      moreover
      have "a' < a + of_nat s"
        using assms(1) 2 3 4 5
        by (auto simp add: sep.simps)
      moreover
      have "length bs > unat a' - unat a"
        using assms(1-3) 2 3 4 5 6
        apply (auto simp add: unat_of_nat sep.simps no_block_overflow.simps)
        apply unat_arith
        by (auto simp add: unat_of_nat sep.simps no_block_overflow.simps)
      moreover
      hence "x < a' + (of_nat (length bs') + of_nat (length bs + unat a - (unat a' + length bs')))"
        using B 2 3 4 5 assms(2-3)
        unfolding no_block_overflow.simps
        apply (auto split: if_split_asm simp add: min_def)
        apply unat_arith
        by (auto simp add: unat_of_nat)
      ultimately
        show ?thesis
        using unfold_write_bytes
        apply (auto simp add: unfold_write_bytes)
        using 2 3 4 5
        apply (auto split: if_split_asm simp add: nth_append)
        by (auto split: if_split_asm simp add: unat_sub min_def)
    next
      case C
      moreover
      hence "x \<ge> min a a'"
        by (auto simp add: min_def)
      hence "a' > a \<Longrightarrow> length bs > unat a' - unat a"
        using C assms(1) 2 3 4 5
        apply (auto simp add: min_def sep.simps split: if_split_asm)
        apply unat_arith
        apply (auto simp add: unat_of_nat)
        done
      moreover
      have "unat x - unat a \<ge> unat a' - unat a"
        using C
        by unat_arith
      moreover
      have "a' > a \<Longrightarrow> unat a + (unat a' - unat a) = unat a'"
        using C
        by unat_arith
      moreover
      have "a' > a \<Longrightarrow> of_nat (unat a' - unat a) = a' - a"
        apply unat_arith
        by (auto simp add: unat_of_nat)
      moreover
      have "unat x - unat a' < length bs'"
        using C 2 3 4 5
        apply unat_arith
        by (auto simp add: unat_of_nat)
      moreover
      have "x < a' + (of_nat (length bs') + of_nat (length bs + unat a - (unat a' + length bs')))"
        using C assms(2-3) 2 3 4 5
        unfolding no_block_overflow.simps
        apply unat_arith
        by (auto simp add: unat_of_nat)
      moreover
      have "x < a' + (of_nat (length bs') + of_nat (length bs - (unat a' + length bs' - unat a)))"
        using C assms(2-3) 2 3 4 5
        unfolding no_block_overflow.simps
        apply unat_arith
        by (auto simp add: unat_of_nat)
      ultimately
        show ?thesis
        apply (auto simp add: unfold_write_bytes)
        using 2 3 4 5
        apply (auto split: if_split_asm simp add: nth_append)
        by (auto split: if_split_asm simp add: unat_sub min_def)
    next
      case D
      moreover
      have 6: "a \<le> x"
        using D assms(1) 2 3 4 5
        apply (simp add: no_block_overflow.simps sep.simps)
        by unat_arith
      moreover
      have "a' \<le> x"
        using D[THEN conjunct1] assms(3) 2 3 4 5
        unfolding no_block_overflow.simps
        apply unat_arith
        by (auto simp add: unat_of_nat)
      moreover
      have "unat x - unat a < length bs"
        using D[THEN conjunct2] assms(2) 2 3 4 5 6
        unfolding no_block_overflow.simps
        apply unat_arith
        by (auto simp add: unat_of_nat)
      moreover
      have "unat x - unat a' \<ge> length bs'"
        using D[THEN conjunct1] assms(3) 2 3 4 5
        unfolding no_block_overflow.simps
        apply unat_arith
        by (auto simp add: unat_of_nat)
      moreover
      have 7: "unat a \<le> unat a' + length bs'"
        using D assms(1) 2 3 4 5
        apply (simp add: no_block_overflow.simps sep.simps)
        apply unat_arith
        by (auto simp add: unat_of_nat)
      have "unat a' + length bs' - unat a + (unat x - (unat a' + length bs')) = unat x - unat a"
        using D assms(2-3) 2 3 4 5 7
        unfolding no_block_overflow.simps
        apply unat_arith
        by (auto simp add: unat_of_nat)
      moreover
      have "a < a' \<Longrightarrow> unat a + (unat a' - unat a) = unat a'"
        by unat_arith
      moreover
      have "a' + of_nat (length bs' + length bs - (unat a' + length bs' - unat a)) = of_nat (length bs) + a"
        using D assms(2-3) 2 3 4 5 7
        unfolding no_block_overflow.simps
        apply unat_arith
        by (auto simp add: unat_of_nat)
      ultimately
      show ?thesis
        apply (auto simp add: unfold_write_bytes)
        using 2 3 4 5
        apply (auto split: if_split_asm simp add: nth_append)
        apply (auto split: if_split_asm simp add: unat_sub min_def comm_semiring_1_class.semiring_normalization_rules(24))
        by (simp add: Groups.add_ac(2) Nat.diff_add_assoc2)
    next
      case E
      moreover
      have "a  \<le> x"
       and "a' \<le> x"
        using E assms(1) 2 3 4 5
        by (auto split: if_split_asm simp add: no_block_overflow.simps sep.simps max_def)
      moreover
      have "unat x - unat a \<ge> length bs"
        using E assms(2) 2 3 4 5
        apply (simp add: no_block_overflow.simps sep.simps max_def)
        apply unat_arith
        by (auto simp add: unat_of_nat)
      moreover
      have "x \<ge> of_nat (length bs) + a"
        using E assms(2) 2 3 4 5
        apply (simp add: no_block_overflow.simps sep.simps max_def)
        by unat_arith
      moreover
      have "unat x - unat a' \<ge> length bs'"
        using E assms(3) 2 3 4 5
        apply (simp add: no_block_overflow.simps sep.simps max_def)
        apply unat_arith
        by (auto simp add: unat_of_nat)
      moreover
      have "a' > a \<Longrightarrow> unat a + (unat a' - unat a) = unat a'"
        by unat_arith
      moreover
      have "length bs' + unat a' \<ge> unat a"
        using E assms(1-3) 2 3 4 5
        apply (auto simp add: algebra_simps no_block_overflow.simps sep.simps max_def split: if_split_asm)
        apply unat_arith
        apply (auto simp add: unat_of_nat)[1]
        apply (auto simp add: unat_of_nat)[1]
        apply unat_arith
        by (auto simp add: unat_of_nat)
      moreover
      have "a' \<ge> a \<Longrightarrow> length bs > unat a' - unat a"
        using E assms(1) 2 3 4 5
        apply (auto simp add: algebra_simps no_block_overflow.simps sep.simps max_def split: if_split_asm)
        apply unat_arith
        apply (auto simp add: unat_of_nat)[1]
        apply unat_arith
        by (auto simp add: unat_of_nat)
      ultimately
      show ?thesis
        apply (auto simp add: unfold_write_bytes)
        using 2 3 4 5
        apply (auto split: if_split_asm simp add: nth_append)
        by (auto split: if_split_asm simp add: unat_sub of_nat_diff min_def)
    qed
  }
  thus ?thesis
    by auto
qed


definition "write_block' \<equiv> write_block"
text {*
  Now, we can set up the rewriter for writing blocks of memory instead of bytes.
  Consider the case where a block called @{term block0} is written into memory.
  Lemma write\_block\_Cons will be applied once for each block @{term block1} that has
  already been written into memory.

  First, separation of the two blocks is checked. If they are separate, then lemma
  @{thm write_bytes_commute} is used to show that the rewriter can proceed to the next block in memory.
  If not, then lemma @{thm write_bytes_nonseparate_is_merge} is used to merge the two blocks,
  and then proceed.

  This rewrite rule introduces a term @{term write_block'}.
  This prevents the rewriter to apply this rule to all blocks at once, since this rule only applies
  to term @{term write_block}. The rewriter will be set up in such a way that this rule will be
  applied once, and then after rewriting term @{term write_block'} will be substituted by term
  @{term write_block}. This allows us to control the rewriting, i.e., to apply this rewrite rule
  \emph{once}, see what happened (how many new subgoals have arisen), and then proceed.
*}
lemma write_block_Cons:
  shows "write_block block0 (write_blocks (block1#blocks) m) =
          (let' rblock0  = Rep_block block0;
                rblock1  = Rep_block block1;
                b = (fst rblock0, length (snd rblock0)) \<bowtie> (fst rblock1, length (snd rblock1)) in
           if b then
                 let' m' = write_blocks [block1] (write_block' block0 (write_blocks blocks m)) in m'
             else
                 let' m' = write_block' (Abs_block (merge_blocks rblock1 rblock0)) (write_blocks blocks m) in m')"
  unfolding Let'_def
  using Rep_block[of block0] Rep_block[of block1]
  apply (cases "Rep_block block0";cases "Rep_block block1")
  apply (simp add: case_prod_unfold Let_def write_block'_def Let'_def del: merge_blocks.simps)
  apply (rule conjI)
  apply (rule impI, subst write_bytes_commute,simp,simp,simp,simp)
  apply (rule impI,subst write_bytes_nonseparate_is_merge,simp,simp,simp)
  using no_block_overflow_after_merge
  apply (subst Abs_block_inverse,simp add: case_prod_unfold,simp)
  done

lemma write_block'_Nil:
  shows "write_block' block0 (mem \<sigma>) = write_blocks [block0] (mem \<sigma>)"
  by (auto simp add: write_block'_def case_prod_unfold)

lemma write_block_Nil:
  shows "write_block block0 (mem \<sigma>) = write_blocks [block0] (mem \<sigma>)"
  by (auto simp add: write_block'_def case_prod_unfold)

lemma write_blocks_append:
  shows "write_blocks blocks0 (write_blocks blocks1 m) = write_blocks (blocks0@blocks1) m"
proof(induct blocks1 m arbitrary: blocks0 rule: write_blocks.induct)
case (1 m)
  thus ?case
    by auto
next
  case (2 b bs m)
  {
    fix blocks m
    have "write_blocks (blocks @ [b]) m = write_blocks blocks (write_block b m)"
      by(induct blocks m rule: write_blocks.induct,auto)
  }
  thus ?case
    using 2[of "blocks0@[b]"]
    by auto
qed

text {*
  Merging of blocks starting with the same address.
*}
lemma merge_blocks_same_start:
  shows "merge_blocks (a,b0) (a,b1) = (a,b1 @ (if length b1 \<ge> length b0 then [] else drop (length b1) b0))"
  by (auto)


text {*
  Use these rewrite rules, and never use the actually definition of the following functions:
*}
lemmas memory_write_rewrite_rules =
    merge_blocks_same_start write_blocks_append write_block_Nil write_block_Cons
declare write_block.simps[simp del]
declare write_bytes.simps[simp del]
declare write_blocks.simps(2)[simp del]
declare merge_blocks.simps[simp del]



subsection "Reading blocks from memory"


fun read_bytes_in_block :: "64 word \<times> nat \<Rightarrow> block \<Rightarrow> 8 word list"
  where "read_bytes_in_block (a,s) block = (let (a',bs) = Rep_block block in take s (drop (unat (a - a')) bs))"

lemma no_block_overflow_is_inductive:
assumes "no_block_overflow (a, Suc n)"
  shows "no_block_overflow (a + 1, n)"
proof-
  have 0: "1 + a \<noteq> 0"
    using max_word_wrap[of a] assms
    by (auto simp add: max_word_def no_block_overflow.simps algebra_simps)
  hence 1: "unat a < 2 ^ 64 - 1"
    using max_word_max[of a]
    apply (cases "a=2^64-1",auto simp add: max_word_def)
    apply (subst word_less_nat_alt[of a "2^64-1",simplified,symmetric])
    by auto
  hence 3: "a < a + 1"
    using 0
    by (cases "a = 2^64-1",auto simp add: word_less_nat_alt unat_plus_if' unat_of_nat split: if_split_asm)
  thus ?thesis
    using assms unat_plus_simple[of a 1]
    by (auto simp add: algebra_simps no_block_overflow.simps)
qed

lemma read_bytes_focus:
  assumes "\<forall> a' . fst b \<le> a' \<and> a' < fst b + of_nat (snd b) \<longrightarrow> m a' = m' a'"
      and "no_block_overflow b"
    shows "read_bytes m b = read_bytes m' b"
  using assms
proof(induct m b rule: read_bytes.induct)
  case (1 m b)
  thus ?case
    by auto
next
  case (2 m a n)
  moreover
  have "no_block_overflow (a + 1, n)"
    using 2 no_block_overflow_is_inductive
    by auto
  moreover
  have "unat a + n < 18446744073709551615 \<Longrightarrow> \<not> a < a + (1 + of_nat n) \<Longrightarrow> False"
    apply unat_arith
    by (auto simp add: unat_of_nat)
  hence "a \<le> a \<and> a < a + (1 + of_nat n)"
    using 2(3) 2(2)[THEN spec, of a]
    by (auto simp add: no_block_overflow.simps unat_plus_if' split: if_split_asm)
  moreover
  have "\<forall>a'. a + 1 \<le> a' \<and> a' < a + 1 + of_nat n \<longrightarrow> m a' = m' a'"
  proof-
    {
      fix a'
      assume "a+1\<le> a' \<and> a' < a + 1 + of_nat n"
      hence "a \<le> a' \<and> a' < a + of_nat (Suc n)"
        using 2(3)
        apply (auto simp add: no_block_overflow.simps)
        apply unat_arith
        apply (auto simp add: unat_of_nat)
        by unat_arith
      hence "m a' = m' a'"
        using 2(2)[THEN spec,of a']
        by auto
    }
    thus ?thesis
      by auto
  qed
  ultimately
  show ?case
    by (auto simp add: Let'_def)
qed

lemma read_bytes_separate:
  assumes "\<forall> a' . fst b > a' \<or> a' \<ge> fst b + of_nat (snd b) \<longrightarrow> m a' = m' a'"
      and "a \<bowtie> b"
      and "no_block_overflow a"
    shows "read_bytes m a = read_bytes m' a"
    using assms
proof(induct m a rule: read_bytes.induct)
  case (1 m a)
  thus ?case
    by auto
next
  case (2 m a n)
  moreover
  have "no_block_overflow (a + 1, n)"
    using 2 no_block_overflow_is_inductive
    by auto
  moreover
  have "a < fst b \<or> fst b + of_nat (snd b) \<le> a"
    using 2(3,4)
    apply (cases a;cases b; auto simp add: sep.simps no_block_overflow.simps)
    apply unat_arith
    by (auto simp add: unat_of_nat)
  moreover
  have "(a + 1, n) \<bowtie> b"
    using 2(3,4)
    apply (cases b; auto simp add: sep.simps no_block_overflow.simps algebra_simps)
    apply unat_arith
    by (auto simp add: unat_of_nat)
  ultimately
  show ?case
    by (auto simp add: Let'_def Let_def)
qed


lemma read_bytes_write_block_separate:
  assumes "a \<bowtie> (fst (Rep_block block), length (snd (Rep_block block)))"
      and "no_block_overflow a"
    shows "read_bytes (write_block block m) a = read_bytes m a"
  apply (subst read_bytes_separate[of "(fst (Rep_block block), length (snd (Rep_block block)))" "write_block block m" m a])
  using assms Rep_block[of block]
  by (auto simp add: write_block.simps spec_of_write_bytes)

lemma read_bytes_write_blocks_Cons:
  assumes "a \<sqsubseteq> (fst (Rep_block block), length (snd (Rep_block block)))"
      and "no_block_overflow a"
    shows "read_bytes (write_blocks (block#blocks) m) a = read_bytes (write_bytes (Rep_block block) m) a"
proof-
  have 0: "no_block_overflow (fst (Rep_block block), length (snd (Rep_block block)))"
    using Rep_block[of block]
    by auto
  {
    fix a'
    assume "fst a \<le> a' \<and> a' < fst a + of_nat (snd a)"
    hence "fst (Rep_block block) \<le> a' \<and> a' < fst (Rep_block block) + of_nat (length (snd (Rep_block block)))"
      using assms(1)
      by (cases a, auto simp add: enclosed.simps)
    hence "write_bytes (Rep_block block) (write_blocks blocks m) a' = write_bytes (Rep_block block) m a'"
      by (auto simp add: spec_of_write_bytes[OF 0])
  }
  thus ?thesis
    apply (auto simp add: write_blocks.simps(2) write_block.simps)
    using read_bytes_focus[of a "write_bytes (Rep_block block) (write_blocks blocks m)" "write_bytes (Rep_block block) m"] assms(2)
    by auto
qed

lemma spec_of_read_bytes:
  assumes "no_block_overflow (fst region, snd region)"
      and "x < snd region"
    shows "(read_bytes m region) ! x = m (fst region + of_nat x)"
  using assms
proof(induct m region arbitrary: x rule: read_bytes.induct)
case (1 m region)
  thus ?case
    by auto
next
  case (2 m a n)
  have "no_block_overflow (a + 1, n)"
    using 2 no_block_overflow_is_inductive
    by auto
  moreover
  have 1: "\<And> x' . x = Suc x' \<Longrightarrow> a + 1 + of_nat x' = a + (1 + of_nat x')"
    using 2(2-)
    by (auto simp add: no_block_overflow.simps)
  ultimately
  show ?case
    using 2(1)[of "x-1"] 2(2-)
    by (cases x, auto simp add: Let'_def Let_def nth_Cons)
qed


lemma read_bytes_write_bytes:
  assumes "b \<sqsubseteq> (fst (Rep_block block), length (snd (Rep_block block)))"
      and "no_block_overflow b"
    shows "read_bytes (write_bytes (Rep_block block) m) b = read_bytes_in_block b block"
proof-
  have 1: "(length (snd (Rep_block block)) - unat (fst b - fst (Rep_block block))) \<ge> snd b"
    using assms(1-2)
    apply (cases b,auto simp add: no_block_overflow.simps enclosed.simps)
    apply unat_arith
    by (auto simp add: unat_of_nat)
  hence "length (read_bytes (write_bytes (Rep_block block) m) b) = length (read_bytes_in_block b block)"
    by (cases b, auto simp add: case_prod_unfold Let_def length_read_bytes)
  moreover
  {
    fix x
    assume 0: "x < snd b"
    moreover
    have "fst (Rep_block block) \<le> fst b + of_nat x"
      using 0 assms(1-2)
      apply (cases b,auto simp add: no_block_overflow.simps enclosed.simps)
      apply unat_arith
      by (auto simp add: unat_of_nat)
    moreover
      have "fst b + of_nat x < fst (Rep_block block) + of_nat (length (snd (Rep_block block)))"
      using 0 assms(1-2)
      apply (cases b,auto simp add: no_block_overflow.simps enclosed.simps)
      apply unat_arith
      by (auto simp add: unat_of_nat)
    moreover
    have "unat (fst b + of_nat x - fst (Rep_block block)) = (unat (fst b - fst (Rep_block block)) + x)"
      using 0 assms(1-2)
      apply (cases b,auto simp add: no_block_overflow.simps enclosed.simps unat_sub_if' unat_plus_if')
      apply unat_arith
      apply (auto simp add: unat_of_nat)
      by unat_arith+
    ultimately
    have "(read_bytes (write_bytes (Rep_block block) m) b) ! x = (read_bytes_in_block b block) ! x"
      apply (subst spec_of_read_bytes)
      apply (auto simp add: assms(2))
      apply (subst spec_of_write_bytes)
      using 1 Rep_block[of block]
      apply auto
      by (cases b, auto)
  }
  ultimately
  show ?thesis
    apply (intro nth_equalityI)
    by (auto simp add: length_read_bytes)
qed

declare write_block.simps[simp del]
declare write_bytes.simps[simp del]
declare write_blocks.simps(2)[simp del]
declare merge_blocks.simps[simp del]


lemma length_read_bytes_in_block:
  assumes "Rep_region b \<sqsubseteq> (fst (Rep_block block), length (snd (Rep_block block)))"
      and "no_block_overflow (Rep_region b)"
    shows "length (read_bytes_in_block (Rep_region b) block) = snd (Rep_region b)"
  using assms Rep_block[of block]
  apply (cases b,auto simp add: case_prod_unfold Let_def Abs_region_inverse min_def enclosed.simps no_block_overflow.simps unat_sub)
  apply unat_arith
  by (auto simp add: unat_of_nat)

definition "read_region'  \<equiv> read_region"
definition "read_region'' \<equiv> read_region"
lemma read_region_write_blocks:
  shows "((read_region (write_blocks (block#blocks) m) b)::'a::len0 word) =
      (let' (a',s') = (fst (Rep_block block), length (snd (Rep_block block))) ;
           (a,s)   = (fst (Rep_region b), snd (Rep_region b)) in
       let' found = (a,s) \<sqsubseteq> (a',s') in
        if found then
          cat_bytes (rev (read_bytes_in_block (a,s) block))
        else let' sep = (a,s) \<bowtie> (a',s') in
          if sep then
            read_region' (write_blocks blocks m) b
          else
            read_region'' (write_blocks (block#blocks) m) b
      )"
  unfolding Let'_def
  using Rep_region
  apply (auto simp add: Let_def Let'_def case_prod_unfold read_region_def read_region''_def read_region'_def min_def)
  apply (auto simp add: read_bytes_write_blocks_Cons length_read_bytes length_read_bytes_in_block min_def sublist_def take_bits_cat_bytes read_bytes_write_bytes)[1]
  apply (simp add: write_blocks.simps(2),subst read_bytes_write_block_separate,simp,simp,simp)
  by (auto simp add: take_bits_cat_bytes read_bytes_write_bytes read_bytes_write_blocks_Cons length_read_bytes length_read_bytes_in_block min_def sublist_def)[1]






definition "BLOCK_OVERFLOW b \<equiv> Rep_block (Abs_block b)"
lemma Abs_block_inverse_unconditional:
  shows "Rep_block (Abs_block b) = (let' no_overflow = no_block_overflow (fst b,length (snd b)) in if no_overflow then b else BLOCK_OVERFLOW b)"
  using Abs_block_inverse
  by (cases b,auto simp add: Let'_def BLOCK_OVERFLOW_def)
definition "REGION_OVERFLOW b \<equiv> Rep_region (Abs_region b)"
lemma Abs_region_inverse_unconditional:
  shows "Rep_region (Abs_region b) = (let' no_overflow = no_block_overflow (fst b,snd b) in if no_overflow then b else REGION_OVERFLOW b)"
  using Abs_region_inverse
  by (cases b,auto simp add: Let'_def REGION_OVERFLOW_def)


text {*
  Use these rewrite rules, and never use the actually definition of the following functions:
*}
lemmas memory_read_rewrite_rules =
    read_region_write_blocks length_read_bytes
    Abs_block_inverse_unconditional Abs_region_inverse_unconditional
declare read_bytes.simps(2)[simp del]



end
