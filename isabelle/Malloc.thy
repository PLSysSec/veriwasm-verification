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

theory Malloc
  imports "Det_Step"
          "Calls"
begin

record malloc_caller_state =
  ptr\<^sub>v :: "64 word option"

context execution_context
begin


definition abstract_malloc :: "(nat \<times> 64 word \<times> nat) set \<Rightarrow> 64 word \<Rightarrow> unit \<times> 'a malloc_caller_state_scheme \<Rightarrow> unit \<times> 'a malloc_caller_state_scheme \<Rightarrow> bool"
  where "abstract_malloc blocks siz \<sigma> \<sigma>' \<equiv> \<C> \<sigma>' =
        (if \<exists> a i. a \<noteq> 0 \<and> i \<notin> fst ` blocks \<and> seps ({(i,a,unat siz)} \<union> blocks) then 
            (\<C> \<sigma>)\<lparr> ptr\<^sub>v := Some (SOME a . a \<noteq> 0 \<and> (\<exists> i. i \<notin> fst ` blocks \<and> seps ({(i,a,unat siz)} \<union> blocks)))\<rparr>
         else
            (\<C> \<sigma>)\<lparr> ptr\<^sub>v := None\<rparr>)"

definition malloc :: "(nat \<times> 64 word \<times> nat) set \<Rightarrow> state \<Rightarrow> state"
  where "malloc blocks s \<equiv> let
         siz = RDI s;
         ret = if \<exists> a i . a \<noteq> 0 \<and> i \<notin> fst ` blocks \<and> seps ({(i,a,unat siz)} \<union> blocks) then 
            SOME a . a \<noteq> 0 \<and> (\<exists> i. i \<notin> fst ` blocks \<and> seps ({(i,a,unat siz)} \<union> blocks))
         else
            0
          in s\<lparr> regs := (regs s)(rax := ret)\<rparr>"


lemma malloc_abstract_malloc:
  fixes S :: "state \<Rightarrow> 'a malloc_caller_state_scheme"
  assumes "call\<^sub>c (malloc blocks) s s'"
    and "\<And> x . S (s\<lparr>regs := (regs s)(rax := x, rip := RIP s + 5)\<rparr>) = S s\<lparr>ptr\<^sub>v := if x = 0 then None else Some x\<rparr>"
    and "RDI s = n"
shows "abstract_malloc blocks n ((), S s) ((), S s')"
  using assms(1,3-)
  apply (auto simp add: abstract_malloc_def call\<^sub>c_def malloc_def Let_def)
  apply (subst assms(2))
  using someI_ex[of "\<lambda> a . a \<noteq> 0 \<and> (\<exists>i. i \<notin> fst ` blocks \<and> seps (insert (i, a, unat (RDI s)) blocks))"]
  apply auto
  apply (subst assms(2))
  using someI_ex[of "\<lambda> a . a \<noteq> 0 \<and> (\<exists>i. i \<notin> fst ` blocks \<and> seps (insert (i, a, unat (RDI s)) blocks))"]
  by auto


definition del_block :: "nat \<Rightarrow> (nat \<times> 64 word \<times> nat) set \<Rightarrow> (nat \<times> 64 word \<times> nat) set"
  where "del_block i blocks \<equiv> {(i',a,s) \<in> blocks . i' \<noteq> i}"

definition abstract_realloc :: "(nat \<times> 64 word \<times> nat) set \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> unit \<times> 'a malloc_caller_state_scheme \<Rightarrow> unit \<times> 'a malloc_caller_state_scheme \<Rightarrow> bool"
  where "abstract_realloc blocks a siz \<sigma> \<sigma>' \<equiv> \<C> \<sigma>' =
        (if \<exists> i si . a \<noteq> 0 \<and> si > 0 \<and>(i,a,si) \<in> blocks \<and> seps ({(i,a,unat siz)} \<union> del_block i blocks) then 
            (\<C> \<sigma>)\<lparr> ptr\<^sub>v := Some a\<rparr>
         else
            (\<C> \<sigma>)\<lparr> ptr\<^sub>v := None\<rparr>)"

definition realloc :: "(nat \<times> 64 word \<times> nat) set \<Rightarrow> state \<Rightarrow> state"
  where "realloc blocks s \<equiv> let
         a   = RDI s;
         siz = RSI s;
         ret = if \<exists> i si . a \<noteq> 0 \<and> si > 0 \<and> (i,a,si) \<in> blocks \<and> seps ({(i,a,unat siz)} \<union> del_block i blocks) then 
            a
         else
            0
          in s\<lparr> regs := (regs s)(rax := ret)\<rparr>"

lemma realloc_abstract_realloc:
  fixes S :: "state \<Rightarrow> 'a malloc_caller_state_scheme"
  assumes "call\<^sub>c (realloc blocks) s s'"
    and "\<And> x . S (s\<lparr>regs := (regs s)(rax := x, rip := RIP s + 5)\<rparr>) = S s\<lparr>ptr\<^sub>v := if x = 0 then None else Some x\<rparr>"
    and "RDI s = a"
    and "RSI s = n"
shows "abstract_realloc blocks a n ((), S s) ((), S s')"
  using assms
  by (auto simp add: abstract_realloc_def call\<^sub>c_def realloc_def Let_def)

lemma seps_implies_unique_blocks:
  assumes "seps blocks"
      and "(i,a,si) \<in> blocks"
      and "(i',a,si') \<in> blocks"
      and "si > 0"
      and "si' > 0"
    shows "i = i' \<and> si = si'"
proof-
  have "i = i' \<longrightarrow> si = si'"
    using assms
    unfolding seps_def
    by auto
  moreover
  have "i \<noteq> i' \<longrightarrow> no_block_overflow (a,si) \<and> no_block_overflow (a,si') \<and> (a,si) \<bowtie> (a,si')"
    using assms
    unfolding seps_def
    by auto
  hence "i \<noteq> i' \<longrightarrow> si = 0 \<or> si' = 0"
    apply (auto simp add: sep.simps no_block_overflow.simps)
    apply unat_arith
    apply (auto simp add: unat_of_nat)
    apply unat_arith
    by (auto simp add: unat_of_nat)
  ultimately
  show ?thesis
    using assms
    by auto
qed

definition malloced
  where "malloced P a si  \<equiv> (a = (0::64 word) \<or> (\<exists> i blocks' . seps (insert (i, a, si) blocks') \<and> i \<notin> fst ` blocks' \<and> P blocks'))"

lemma malloced_realloced_block:
  assumes "seps blocks"
      and "a = 0 \<or> 
            ((\<exists> i si . si > 0 \<and> (i,a,si) \<in> blocks \<and> seps ({(i,a,si')} \<union> del_block i blocks)) \<and> (i, a, si) \<in> blocks)"
      and "si > 0"
      and "P (del_block i blocks)"
    shows "malloced P a si'"
proof(cases "a=0")
  case True
  thus ?thesis
    unfolding malloced_def
    by auto
next
  case False
  then obtain i' si'' where 1: "a \<noteq> 0 \<and> si'' > 0 \<and> (i',a,si'') \<in> blocks \<and> seps ({(i',a,si')} \<union> del_block i' blocks)"
    using assms(2)
    by auto
  hence 2: "i=i' \<and> si'' = si"
    using seps_implies_unique_blocks[of blocks i' a si'' i si] assms
    by auto
  hence "seps (insert (i, a, si') (del_block i blocks)) \<and> i \<notin> fst ` (del_block i blocks) \<and> P (del_block i blocks)"
    using 1 assms
    by (auto simp add: del_block_def)
  thus ?thesis
    unfolding malloced_def
    using 1 2
    by auto
qed

lemma malloced_malloced_block:
  assumes "seps blocks"
      and "a = (if \<exists> a i . a \<noteq> 0 \<and> i \<notin> fst ` blocks \<and> seps ({(i,a,si)} \<union> blocks) then 
                  SOME a . a \<noteq> 0 \<and> (\<exists> i. i \<notin> fst ` blocks \<and> seps ({(i,a,si)} \<union> blocks))
                else 0)"
      and "P blocks"
    shows "malloced P a si"
    unfolding malloced_def
    using assms someI_ex[of "\<lambda> a . a \<noteq> 0 \<and> (\<exists>i. i \<notin> fst ` blocks \<and> seps (insert (i, a, si) blocks))"] 
    by (auto split: if_split_asm)

lemma master_implies_id_in_blocks:
  assumes "master blocks b i"
  shows "i \<in> fst ` blocks"
  using assms
  by (auto simp add: master_def)

lemma master_del_block:
  shows "master (del_block i' blocks) b i = (i \<noteq> i' \<and> master blocks b i)"
  apply (auto simp add: del_block_def)
  apply (frule master_implies_id_in_blocks)
  apply auto
  apply (auto simp add: master_def)[1]
  apply (metis fst_conv snd_eqD)
  apply (auto simp add: master_def)[1]
  by metis

lemma master_insert:
  shows "master (insert (i',a,s) blocks) b i =
      (if i = i' then 
          if i' \<in> fst ` blocks then (no_block_overflow b \<and> b \<sqsubseteq> (a, s)) \<or> master blocks b i 
          else b \<sqsubseteq> (a,s) \<and> no_block_overflow b
       else master blocks b i)"
  unfolding master_def
  by auto

lemma in_del_blocks:
  shows "x \<in> del_block i blocks \<longleftrightarrow> fst x \<noteq> i \<and> x \<in> blocks"
  unfolding del_block_def
  by auto


end
end