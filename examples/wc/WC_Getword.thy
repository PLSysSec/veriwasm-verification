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

theory WC_Getword
  imports "WC"
begin



locale wc_context' = wc_context +
  fixes feof :: "state \<Rightarrow> state"
    and getc :: "state \<Rightarrow> state"
    and isword :: "state \<Rightarrow> state"
    and rsp\<^sub>0 :: "64 word"
    and ret_address :: "64 word"
    and \<sigma>\<^sub>C :: '\<sigma>\<^sub>C
  assumes [simp]: "funcs ''feof'' = Some feof"
      and [simp]: "RSP (feof s) = RSP s"
      and [simp]: "RBP (feof s) = RBP s"
      and [simp]: "feof s \<turnstile> *[rsp\<^sub>0,8] = (s \<turnstile> *[rsp\<^sub>0,8] :: 64 word)"
      and [simp]: "feof s \<turnstile> *[rsp\<^sub>0 - 32,8] = (s \<turnstile> *[rsp\<^sub>0 - 32,8] ::64 word)"
      and [simp]: "feof s \<turnstile> *[boffset + 1345,8] = (s \<turnstile> *[boffset + 1345,8] ::64 word)"
      and [simp]: "feof s \<turnstile> *[boffset + 1353,8] = (s \<turnstile> *[boffset + 1353,8] ::64 word)"
      and [simp]: "feof s \<turnstile> *[boffset + 1361,8] = (s \<turnstile> *[boffset + 1361,8] ::64 word)"

      and [simp]: "funcs ''_IO_getc'' = Some getc"
      and [simp]: "RSP (getc s) = RSP s"
      and [simp]: "RBP (getc s) = RBP s"
      and [simp]: "getc s \<turnstile> *[rsp\<^sub>0,8] = (s \<turnstile> *[rsp\<^sub>0,8] :: 64 word)"
      and [simp]: "getc s \<turnstile> *[rsp\<^sub>0 - 32,8] = (s \<turnstile> *[rsp\<^sub>0 - 32,8] ::64 word)"
      and [simp]: "getc s \<turnstile> *[boffset + 1345,8] = (s \<turnstile> *[boffset + 1345,8] ::64 word)"
      and [simp]: "getc s \<turnstile> *[boffset + 1353,8] = (s \<turnstile> *[boffset + 1353,8] ::64 word)"
      and [simp]: "getc s \<turnstile> *[boffset + 1361,8] = (s \<turnstile> *[boffset + 1361,8] ::64 word)"

      and [simp]: "funcs ''isword'' = Some isword"
      and [simp]: "RSP (isword s) = RSP s"
      and [simp]: "RBP (isword s) = RBP s"
      and [simp]: "isword s \<turnstile> *[rsp\<^sub>0,8] = (s \<turnstile> *[rsp\<^sub>0,8] :: 64 word)"
      and [simp]: "isword s \<turnstile> *[rsp\<^sub>0 - 32,8] = (s \<turnstile> *[rsp\<^sub>0 - 32,8] ::64 word)"
      and [simp]: "isword s \<turnstile> *[boffset + 1345,8] = (s \<turnstile> *[boffset + 1345,8] ::64 word)"
      and [simp]: "isword s \<turnstile> *[boffset + 1353,8] = (s \<turnstile> *[boffset + 1353,8] ::64 word)"
      and [simp]: "isword s \<turnstile> *[boffset + 1361,8] = (s \<turnstile> *[boffset + 1361,8] ::64 word)"
begin

definition S :: "state \<Rightarrow> getword_state \<times> '\<sigma>\<^sub>C getword_caller_state_scheme"
  where "S s =
            (\<lparr> feof_ret\<^sub>v = (if RIP s = boffset + 639 then EAX s else undefined),
               getc_ret\<^sub>v = (if RIP s \<in> {boffset + 746,boffset + 830} then EAX s else undefined),
               isword_ret\<^sub>v = (if RIP s \<in> { boffset + 668, boffset + 812} then EAX s else undefined),
               breaked\<^sub>v\<^sub>1 = (RIP s = boffset + 833),
               breaked\<^sub>v\<^sub>2 = (RIP s = boffset + 839),
               c\<^sub>v = (if RIP s \<in> {boffset + 608, boffset + 634} then undefined else s \<turnstile> *[RBP s - 8,4])
                 \<rparr>,
              \<lparr> ret\<^sub>v = (if RIP s = boffset + ret_address then EAX s else undefined) ,
               wcount\<^sub>v = s \<turnstile> *[boffset + 1345,8],
               ccount\<^sub>v = s \<turnstile> *[boffset + 1353,8],
               lcount\<^sub>v = s \<turnstile> *[boffset + 1361,8],
                \<dots> = \<sigma>\<^sub>C\<rparr>)"
               

definition call_feof :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "call_feof s s' \<equiv> s' = (let s'' = feof s in s''\<lparr>regs := (regs s'')(rip := get_rip s + 5)\<rparr>)"

definition abstract_feof :: "file_t \<Rightarrow> unit \<times> getword_state \<Rightarrow> unit \<times> getword_state \<Rightarrow> bool"
  where "abstract_feof fp \<sigma> \<sigma>' \<equiv> \<exists> s s' . RDI s = address fp \<and> call_feof s s' \<and> snd \<sigma> = fst (S s) \<and> snd \<sigma>' = fst (S s')"

definition call_getc :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "call_getc s s' \<equiv> s' = (let s'' = getc s in s''\<lparr>regs := (regs s'')(rip := get_rip s + 5)\<rparr>)"

definition abstract_getc :: "file_t \<Rightarrow> unit \<times> getword_state \<Rightarrow> unit \<times> getword_state \<Rightarrow> bool"
  where "abstract_getc fp \<sigma> \<sigma>' \<equiv> \<exists> s s' . RDI s = address fp \<and> call_getc s s' \<and> snd \<sigma> = fst (S s) \<and> snd \<sigma>' = fst (S s')"

definition call_isword :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "call_isword s s' \<equiv> s' = (let s'' = isword s in s''\<lparr>regs := (regs s'')(rip := get_rip s + 5)\<rparr>)"

definition abstract_isword :: "8 word \<Rightarrow> unit \<times> getword_state \<Rightarrow> unit \<times> getword_state \<Rightarrow> bool"
  where "abstract_isword c \<sigma> \<sigma>' \<equiv> \<exists> s s' . DL s = c \<and> call_isword s s' \<and> snd \<sigma> = fst (S s) \<and> snd \<sigma>' = fst (S s')"



definition P_608
  where "P_608 blocks fp s \<equiv> 
      seps blocks
    \<and> RSP s = rsp\<^sub>0
    \<and> master blocks (rsp\<^sub>0, 8) 1
    \<and> master blocks (rsp\<^sub>0 - 8, 8) 2
    \<and> master blocks (rsp\<^sub>0 - 12, 4) 3
    \<and> master blocks (rsp\<^sub>0 - 16, 4) 4
    \<and> master blocks (rsp\<^sub>0 - 32, 8) 5
    \<and> master blocks (boffset + 1345, 8) 10
    \<and> master blocks (boffset + 1353, 8) 11
    \<and> master blocks (boffset + 1361, 8) 12
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address
    \<and> RIP s = boffset + 608
    \<and> ret_address > 1200 (* TODO *)
    \<and> RDI s = address fp"

definition P_def
  where "P_def l blocks fp s \<equiv>
      seps blocks
    \<and> RSP s = rsp\<^sub>0 - 40
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> master blocks (rsp\<^sub>0, 8) 1
    \<and> master blocks (rsp\<^sub>0 - 8, 8) 2
    \<and> master blocks (rsp\<^sub>0 - 12, 4) 3
    \<and> master blocks (rsp\<^sub>0 - 16, 4) 4
    \<and> master blocks (rsp\<^sub>0 - 32, 8) 5
    \<and> master blocks (boffset + 1345, 8) 10
    \<and> master blocks (boffset + 1353, 8) 11
    \<and> master blocks (boffset + 1361, 8) 12
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address
    \<and> RIP s = boffset + l
    \<and> ret_address > 1200" (* TODO *)

definition P_634
  where "P_634 blocks fp s \<equiv> 
      P_def 634 blocks fp s
    \<and> RDI s = address fp
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"

definition P_639
  where "P_639 blocks fp s \<equiv> 
      P_def 639 blocks fp s
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"

definition P_753
  where "P_753 blocks fp s \<equiv> 
      P_def 753 blocks fp s
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp
    \<and> flags s flag_zf = (s \<turnstile> *[RBP s - 8,4] = (-1::32 word))"

definition P_663
  where "P_663 blocks fp s \<equiv> 
      P_def 663 blocks fp s
    \<and> DL s = ucast (s \<turnstile> *[rsp\<^sub>0 - 16,4]::32 word)
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"

definition P_668
  where "P_668 blocks fp s \<equiv> 
      P_def 668 blocks fp s
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"

definition P_741
  where "P_741 blocks fp s \<equiv> 
      P_def 741 blocks fp s
    \<and> RDI s = address fp
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"

definition P_746
  where "P_746 blocks fp s \<equiv> 
      P_def 746 blocks fp s
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"

definition P_833
  where "P_833 blocks fp s \<equiv> 
      P_def 833 blocks fp s
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"

definition P_807
  where "P_807 blocks fp s \<equiv> 
      P_def 807 blocks fp s
    \<and> DL s = ucast (s \<turnstile> *[rsp\<^sub>0 - 16,4]::32 word)
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"

definition P_812
  where "P_812 blocks fp s \<equiv> 
      P_def 812 blocks fp s
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"

definition P_825
  where "P_825 blocks fp s \<equiv> 
      P_def 825 blocks fp s
    \<and> RDI s = address fp
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"

definition P_830
  where "P_830 blocks fp s \<equiv> 
      P_def 830 blocks fp s
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"

definition P_839
  where "P_839 blocks fp s \<equiv> 
      P_def 839 blocks fp s
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"

definition P_ret
  where "P_ret s \<equiv>
      RSP s = rsp\<^sub>0 + 8 \<and> 
      RIP s = boffset + ret_address"

lemma getword_608_634:
  assumes "P_608 blocks fp s"
  shows "((\<lambda> s s' . S s' = S s) s && P_634 blocks fp) (The (run_until_pred (lines {ret_address, 634, 639}) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (boffset + 1345, 8) 10\<close>
   and \<open>master blocks (boffset + 1353, 8) 11\<close>
   and \<open>master blocks (boffset + 1361, 8) 12\<close>
    using assms[unfolded P_608_def P_def_def]
    by auto
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0"
    
   and "RIP s = boffset + 608"
   and "ret_address > 1200"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "RDI s = address fp"
    using assms[unfolded P_608_def P_def_def]
    by auto
  note assms = this

  show ?thesis
    apply (insert assms)
    apply (symbolic_execution masters: masters) (* push *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* sub *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: S_def)[1]
    apply (insert masters)
    apply (rewrite_one_let')+
    apply simp
    apply (auto)[1]
    apply (rewrite_one_let')+
    apply simp
    apply (auto)[1]
    apply (rewrite_one_let')+
    apply simp
    apply (simp (no_asm_simp) add: P_634_def P_def_def)
    apply (rewrite_one_let')+
    apply simp
    done
qed




lemma getword_634_639:
  assumes "P_634 blocks fp s"
  shows "(call_feof s && P_639 blocks fp) (The (run_until_pred (lines {639, ret_address}) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (boffset + 1345, 8) 10\<close>
   and \<open>master blocks (boffset + 1353, 8) 11\<close>
   and \<open>master blocks (boffset + 1361, 8) 12\<close>
    using assms[unfolded P_634_def P_def_def]
    by auto
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 634"
   and "ret_address > 1200"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"
    using assms[unfolded P_634_def P_def_def]
    by auto
  note assms = this

  show ?thesis
    apply (insert assms)
    apply (symbolic_execution masters: masters) (* call feof *)
    apply (finish_symbolic_execution)
    apply (simp add: call_feof_def Let_def field_simps)
    using masters
    apply (simp add: P_639_def P_def_def)[1]
    done
qed

definition block1 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block1 s s' \<equiv> RIP s' = boffset + 741"

lemma getword_639_741_if_0:
  assumes "(P_639 blocks fp && (\<lambda>s. EAX s = 0)) s"
  shows "(block1 s && P_741 blocks fp) (The (run_until_pred (lines {741, 746, 753, 833, 839,ret_address}) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (boffset + 1345, 8) 10\<close>
   and \<open>master blocks (boffset + 1353, 8) 11\<close>
   and \<open>master blocks (boffset + 1361, 8) 12\<close>
    using assms[unfolded P_639_def P_def_def pred_logic]
    by auto
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"    
   and "RBP s = rsp\<^sub>0 - 8"    
   and "RIP s = boffset + 639"
   and "ret_address > 1200"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"
   and "EAX s = 0"
    using assms[unfolded P_639_def P_def_def pred_logic]
    by auto
  note assms = this

  show ?thesis
    apply (insert assms)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je .label_25 *)
    apply (symbolic_execution masters: masters) (* jmp .label_16 *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (auto simp add: block1_def)[1]
    apply (insert masters)
    apply (simp add: P_741_def P_def_def)
    done
qed

lemma getword_741_746:
  assumes "P_741 blocks fp s"
  shows "(call_getc s && P_746 blocks fp) (The (run_until_pred (lines {746, 753, 833, 839, ret_address}) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (boffset + 1345, 8) 10\<close>
   and \<open>master blocks (boffset + 1353, 8) 11\<close>
   and \<open>master blocks (boffset + 1361, 8) 12\<close>
    using assms[unfolded P_741_def P_def_def]
    by auto
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 741"
   and "ret_address > 1200"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"
    using assms[unfolded P_741_def P_def_def]
    by auto
  note assms = this

  show ?thesis
    apply (insert assms)
    apply (symbolic_execution masters: masters) (* call getc *)
    apply (finish_symbolic_execution)
    apply (simp add: call_getc_def Let_def field_simps)
    using masters
    apply (simp add: P_746_def P_def_def)[1]
    done
qed


definition block2 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block2 s s' \<equiv> RIP s' = boffset + 753 \<and> (s' \<turnstile> *[rsp\<^sub>0 - 16,4] = EAX s)"

lemma minus_one_bit32:
  shows "\<langle>31,0\<rangle>- (1::64 word) = (-1:: 32 word)"
proof-
  {
    fix i :: nat
    assume "i < 32"
    hence "(\<langle>31,0\<rangle>- (1::64 word)::32 word) !! i = (-1:: 32 word) !! i"
      by (auto simp add: test_bit_of_take_bits)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed


lemma getword_746_753:
  assumes "P_746 blocks fp s"
  shows "(block2 s && (P_753 blocks fp || P_833 blocks fp)) (The (run_until_pred (lines {753, 833, 839, ret_address}) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (boffset + 1345, 8) 10\<close>
   and \<open>master blocks (boffset + 1353, 8) 11\<close>
   and \<open>master blocks (boffset + 1361, 8) 12\<close>
    using assms[unfolded P_746_def P_def_def]
    by auto
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 746"
   and "ret_address > 1200"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"
    using assms[unfolded P_746_def P_def_def]
    by auto
  note assms = this

  show ?thesis
    apply (insert assms minus_one_bit32)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (finish_symbolic_execution)
    apply (simp add: block2_def)
    using masters
    apply (rewrite_one_let')+
    apply (simp add: P_753_def P_def_def simp_rules)
    using masters
    apply (simp add: P_753_def P_def_def simp_rules)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)
    done
qed



definition block3 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block3 s s' \<equiv> EAX s' = 0 \<and> RIP s' = boffset + ret_address"

lemma getword_639_ret_if_not_0:
  assumes "(P_639 blocks fp && (\<lambda>s. EAX s \<noteq> 0)) s"
  shows "(block3 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (boffset + 1345, 8) 10\<close>
   and \<open>master blocks (boffset + 1353, 8) 11\<close>
   and \<open>master blocks (boffset + 1361, 8) 12\<close>
    using assms[unfolded P_639_def P_def_def]
    by (auto simp add: pred_logic)
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 639"
   and "ret_address > 1200"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "EAX s \<noteq> 0"
    using assms[unfolded P_639_def P_def_def pred_logic]
    by auto
  note assms = this

  show ?thesis
    apply (insert assms)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (simp add: block3_def)
    apply (simp add: P_ret_def P_def_def)
    done
qed

definition block4 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block4 s s' \<equiv> RIP s' = boffset + 833"

lemma getword_753_833_to_833:
assumes "((P_753 blocks fp || P_833 blocks fp) && ! ((\<lambda>s. \<not> flags s flag_zf) && ! lines {833, 839, ret_address})) s"
shows "(block4 s && P_833 blocks fp) (The (run_until_pred (lines {833, 839, ret_address}) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (boffset + 1345, 8) 10\<close>
   and \<open>master blocks (boffset + 1353, 8) 11\<close>
   and \<open>master blocks (boffset + 1361, 8) 12\<close>
    using assms[unfolded P_753_def P_833_def P_def_def]
    by (auto simp add: pred_logic)
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "ret_address > 1200"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
    using assms[unfolded P_753_def P_833_def P_def_def pred_logic]
    by (auto simp add: line_def lines_def)
  note assms' = this

  consider (zf) "RIP s = boffset + 753 \<and> flags s flag_zf" 
         | (breaked) "RIP s = boffset + 833"
    using assms[unfolded P_753_def P_833_def P_def_def pred_logic]
    by (auto simp add: line_def lines_def)
  thus ?thesis
  proof(cases)
    case zf
    thus ?thesis
      apply (insert assms' zf)
      apply (symbolic_execution masters: masters) (* jmp *)
      apply (symbolic_execution masters: masters) (* jmp *)
      apply (finish_symbolic_execution)
      apply (simp add: block4_def)
      using masters
      apply (simp add: P_833_def P_def_def)
      done
  next
    case breaked
    thus ?thesis
      apply (insert assms' breaked)
      apply (finish_symbolic_execution)
      apply (simp add: block4_def)
      using masters
      apply (simp add: P_833_def P_def_def)
      done
  qed
qed

lemma getword_753_663:
assumes "((P_753 blocks fp || P_833 blocks fp) && (\<lambda>s. \<not> flags s flag_zf) && ! lines {ret_address, 833, 839}) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_663 blocks fp) (The (((\<lambda>s. (=) (step s)) ; run_until_pred (lines {663, 668, 833, 839, 753, ret_address})) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (boffset + 1345, 8) 10\<close>
   and \<open>master blocks (boffset + 1353, 8) 11\<close>
   and \<open>master blocks (boffset + 1361, 8) 12\<close>
    using assms[unfolded P_753_def P_833_def P_def_def]
    by (auto simp add: pred_logic)
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 753"
   and "ret_address > 1200"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"
   and "\<not>flags s flag_zf"
    using assms[unfolded P_753_def P_833_def P_def_def pred_logic]
    by (auto simp add: line_def lines_def)
  note assms = this

  have 1: "(s \<turnstile> *[rsp\<^sub>0 - 16,4] :: 8 word) = ucast (s \<turnstile> *[rsp\<^sub>0 - 16,4] :: 32 word)"
  proof-
    {
      fix i :: nat
      assume "i < 8"
      hence "(s \<turnstile> *[rsp\<^sub>0 - 16,4] :: 8 word) !! i = (ucast (s \<turnstile> *[rsp\<^sub>0 - 16,4] :: 32 word) :: 8 word) !! i"
        by (auto simp add: nth_ucast read_region_def test_bit_of_cat_bytes)
    }
    thus ?thesis
      apply (intro word_eqI)
      by (auto simp add: word_size)
  qed

  show ?thesis
    apply (insert assms)
    apply (rewrite_one_step)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (auto simp add: S_def)[1]
    using masters
    apply (auto simp add: P_663_def P_def_def ucast_id 1)[1]
    done
qed


lemma getword_663_668:
  assumes "P_663 blocks fp s"
  shows "(call_isword s && P_668 blocks fp) (The (run_until_pred (lines {668, 833, 839, 753, ret_address}) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (boffset + 1345, 8) 10\<close>
   and \<open>master blocks (boffset + 1353, 8) 11\<close>
   and \<open>master blocks (boffset + 1361, 8) 12\<close>
    using assms[unfolded P_663_def P_def_def]
    by auto
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 663"
   and "ret_address > 1200"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"
    using assms[unfolded P_663_def P_def_def]
    by auto
  note assms = this

  show ?thesis
    apply (insert assms)
    apply (symbolic_execution masters: masters) (* call isword *)
    apply (finish_symbolic_execution)
    apply (simp add: call_isword_def Let_def field_simps)
    using masters
    apply (simp add: P_668_def P_def_def)[1]
    done
qed


definition block5 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block5 s s' \<equiv> RIP s' = boffset + 741 
                      \<and> (s' \<turnstile> *[boffset + 1353,8]::64 word) = (s \<turnstile> *[boffset + 1353,8]) + 1
                      \<and> (s' \<turnstile> *[boffset + 1361,8]::64 word) = (if (s \<turnstile> *[RBP s - 8,4]) = (10::32 word) then (s \<turnstile> *[boffset + 1361,8]) + 1 else (s \<turnstile> *[boffset + 1361,8]))"

lemma getword_668_741_if_0:
assumes "((P_668 blocks fp) && (\<lambda> s . EAX s = 0)) s"
shows "(block5 s && P_741 blocks fp) (The (run_until_pred (lines {741, 746, 753, 833, 839, ret_address}) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (boffset + 1345, 8) 10\<close>
   and \<open>master blocks (boffset + 1353, 8) 11\<close>
   and \<open>master blocks (boffset + 1361, 8) 12\<close>
    using assms[unfolded P_668_def P_def_def]
    by (auto simp add: pred_logic)
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 668"
   and "ret_address > 1200"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"
   and "EAX s = 0"
    using assms[unfolded P_668_def P_def_def pred_logic]
    by auto
  note assms = this

  show ?thesis
    apply (insert assms)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je .label_17 *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jne .label_16 *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp add: block5_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (auto simp add: P_741_def P_def_def)[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (rewrite_one_let')+
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp add: block5_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    using masters
    apply (auto simp add: P_741_def P_def_def)[1]
    apply (rewrite_one_let')+
    apply simp
    apply (rewrite_one_let')+
    apply simp
    done
qed

definition block6 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block6 s s' \<equiv> RIP s' = boffset + 833 \<and>
                       (s' \<turnstile> *[boffset + 1345,8]::64 word) = (s \<turnstile> *[boffset + 1345,8]) + 1"

lemma getword_668_833_if_not_0:
assumes "((P_668 blocks fp) && ! (\<lambda> s . EAX s = 0)) s"
  shows "(block6 s && (P_753 blocks fp || P_833 blocks fp)) (The (run_until_pred (lines {ret_address, 753, 833, 839}) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (boffset + 1345, 8) 10\<close>
   and \<open>master blocks (boffset + 1353, 8) 11\<close>
   and \<open>master blocks (boffset + 1361, 8) 12\<close>
    using assms[unfolded P_668_def P_def_def]
    by (auto simp add: pred_logic)
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 668"
   and "ret_address > 1200"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "EAX s \<noteq> 0"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"
    using assms[unfolded P_668_def P_def_def pred_logic]
    by auto
  note assms = this

  show ?thesis
    apply (insert assms)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je .label_17 *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp .label_18 *)
    apply (symbolic_execution masters: masters) (* jmp .label_23 *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block6_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply simp
    using masters
    apply (simp add: P_833_def P_def_def)
    apply (rewrite_one_let')+
    apply simp
    done
qed

definition block7 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block7 s s' \<equiv> RIP s' = boffset + 839"

lemma getword_833_to_839:
assumes "((P_833 blocks fp || P_839 blocks fp) && ! ((\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 16,4] \<noteq> (- 1::32 word)) && ! lines {839, ret_address})) s"
shows "(block7 s && P_839 blocks fp) (The (run_until_pred (lines {839, ret_address}) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (boffset + 1345, 8) 10\<close>
   and \<open>master blocks (boffset + 1353, 8) 11\<close>
   and \<open>master blocks (boffset + 1361, 8) 12\<close>
    using assms[unfolded P_833_def P_839_def P_def_def]
    by (auto simp add: pred_logic)
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "ret_address > 1200"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
    using assms[unfolded P_833_def P_839_def P_def_def pred_logic]
    by (auto simp add: line_def lines_def)
  note assms' = this

  consider (eof) "RIP s = boffset + 833 \<and> s \<turnstile> *[rsp\<^sub>0 - 16,4] = (- 1::32 word)" 
         | (breaked) "RIP s = boffset + 839"
    using assms[unfolded P_833_def P_839_def P_def_def pred_logic]
    by (auto simp add: line_def lines_def)
  thus ?thesis
  proof(cases)
    case eof
    thus ?thesis
      apply (insert assms' eof minus_one_bit32)
      apply (symbolic_execution masters: masters) (* cmp *)
      apply (symbolic_execution masters: masters) (* jne .label_21 *)
      apply (finish_symbolic_execution)
      apply (simp add: block7_def)
      using masters
      apply (simp add: P_839_def P_def_def)
      done
  next
    case breaked
    thus ?thesis
      apply (insert assms' breaked)
      apply (finish_symbolic_execution)
      apply (simp add: block7_def)
      using masters
      apply (simp add: P_839_def P_def_def)
      done
  qed
qed

definition block8 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block8 s s' \<equiv> RIP s' = boffset + 807
                      \<and> (s' \<turnstile> *[boffset + 1353,8]::64 word) = (s \<turnstile> *[boffset + 1353,8]) + 1
                      \<and> (s' \<turnstile> *[boffset + 1361,8]::64 word) = (if (s \<turnstile> *[RBP s - 8,4]) = (10::32 word) then (s \<turnstile> *[boffset + 1361,8]) + 1 else (s \<turnstile> *[boffset + 1361,8]))"

lemma getword_833_807:
assumes "((P_833 blocks fp || P_839 blocks fp) && (\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 16,4] \<noteq> (- 1::32 word)) && ! lines {ret_address, 839}) s"
  shows "(block8 s && P_807 blocks fp) (The (((\<lambda>s. (=) (step s)) ; run_until_pred (lines {807, 812, 825, 833, 839, ret_address})) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (boffset + 1345, 8) 10\<close>
   and \<open>master blocks (boffset + 1353, 8) 11\<close>
   and \<open>master blocks (boffset + 1361, 8) 12\<close>
    using assms[unfolded P_833_def P_839_def P_def_def]
    by (auto simp add: pred_logic)
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "ret_address > 1200"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "RIP s = boffset + 833"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,4] \<noteq> (- 1::32 word)"
    using assms[unfolded P_833_def P_839_def P_def_def pred_logic]
    by (auto simp add: line_def lines_def)
  note assms' = this

  have 1: "(s \<turnstile> *[rsp\<^sub>0 - 16,4] :: 8 word) = ucast (s \<turnstile> *[rsp\<^sub>0 - 16,4] :: 32 word)"
  proof-
    {
      fix i :: nat
      assume "i < 8"
      hence "(s \<turnstile> *[rsp\<^sub>0 - 16,4] :: 8 word) !! i = (ucast (s \<turnstile> *[rsp\<^sub>0 - 16,4] :: 32 word) :: 8 word) !! i"
        by (auto simp add: nth_ucast read_region_def test_bit_of_cat_bytes)
    }
    thus ?thesis
      apply (intro word_eqI)
      by (auto simp add: word_size)
  qed

  show ?thesis
    apply (insert assms' minus_one_bit32)
    apply (rewrite_one_step)
    apply (symbolic_execution masters: masters) (* jne .label_21 *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jne .label_24 *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block8_def)
    apply (insert masters)[1]
    apply (rewrite_one_let')+
    apply simp    
    apply (insert masters)[1]
    apply (simp add: P_807_def P_def_def)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules 1)
    apply (rewrite_one_let')+

    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block8_def)
    apply (insert masters)[1]
    apply (rewrite_one_let')+
    apply simp
    apply (insert masters)[1]
    apply (simp add: P_807_def P_def_def)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules 1)
    done
qed



lemma getword_807_812:
  assumes "P_807 blocks fp s"
  shows "(call_isword s && P_812 blocks fp) (The (run_until_pred (lines {812, 825, 833, 839, ret_address}) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (boffset + 1345, 8) 10\<close>
   and \<open>master blocks (boffset + 1353, 8) 11\<close>
   and \<open>master blocks (boffset + 1361, 8) 12\<close>
    using assms[unfolded P_807_def P_def_def]
    by auto
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 807"
   and "ret_address > 1200"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"
    using assms[unfolded P_807_def P_def_def]
    by auto
  note assms = this

  show ?thesis
    apply (insert assms)
    apply (symbolic_execution masters: masters) (* call isword *)
    apply (finish_symbolic_execution)
    apply (simp add: call_isword_def Let_def field_simps)
    using masters
    apply (simp add: P_812_def P_def_def)[1]
    done
qed

definition block9 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block9 s s' \<equiv> if EAX s = 0 then RIP s' = boffset + 839 else RIP s' = boffset + 825"

lemma getword_812_to_825_or_839:
  assumes "P_812 blocks fp s"
  shows "(block9 s && (P_825 blocks fp || P_839 blocks fp)) (The (run_until_pred (lines {825, 833, 839, ret_address}) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (boffset + 1345, 8) 10\<close>
   and \<open>master blocks (boffset + 1353, 8) 11\<close>
   and \<open>master blocks (boffset + 1361, 8) 12\<close>
    using assms[unfolded P_812_def P_def_def]
    by auto
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 812"
   and "ret_address > 1200"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"
    using assms[unfolded P_812_def P_def_def]
    by auto
  note assms = this

  show ?thesis
    apply (insert assms)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* jne .label_19 *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp add: block9_def)
    using masters
    apply (simp add: P_825_def P_def_def)[1]

    apply (rewrite_one_let')+
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (finish_symbolic_execution)
    apply (simp add: block9_def)
    using masters
    apply (simp add: P_839_def P_def_def)[1]
    done
qed

lemma getword_825_to_830:
  assumes "(P_825 blocks fp) s"
  shows "(call_getc s && P_830 blocks fp) (The (run_until_pred (lines {830, 833, 839, ret_address}) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (boffset + 1345, 8) 10\<close>
   and \<open>master blocks (boffset + 1353, 8) 11\<close>
   and \<open>master blocks (boffset + 1361, 8) 12\<close>
    using assms[unfolded P_825_def P_839_def P_def_def pred_logic]
    by auto
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "ret_address > 1200"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"
   and "RIP s= boffset + 825"
    using assms[unfolded P_825_def P_839_def P_def_def pred_logic]
    by auto
  note assms' = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* call getc *)
    apply (finish_symbolic_execution)
    apply (simp add: call_getc_def Let_def field_simps)
    using masters
    apply (simp add: P_830_def P_def_def)[1]
    done
qed

definition block10 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block10 s s' \<equiv> RIP s' = boffset + 833 \<and> (s' \<turnstile> *[rsp\<^sub>0 - 16,4] = EAX s)"

lemma getword_830_to_833:
  assumes "(P_830 blocks fp) s"
  shows "(block10 s && (P_833 blocks fp || P_839 blocks fp)) (The (run_until_pred (lines {833, 839, ret_address}) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (boffset + 1345, 8) 10\<close>
   and \<open>master blocks (boffset + 1353, 8) 11\<close>
   and \<open>master blocks (boffset + 1361, 8) 12\<close>
    using assms[unfolded P_830_def P_def_def pred_logic]
    by auto
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "ret_address > 1200"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"
   and "RIP s= boffset + 830"
    using assms[unfolded P_830_def P_def_def pred_logic]
    by auto
  note assms' = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp add: block10_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply (simp)
    apply (simp add: P_833_def P_def_def)[1]
    apply (rewrite_one_let')+
    apply (simp)
    done
qed

definition block11 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block11 s s' \<equiv> EAX s' = (if s \<turnstile> *[rsp\<^sub>0 - 16,4] = (-1::32 word) then 0 else 1)"

lemma getword_839_to_ret:
  assumes "(P_839 blocks fp) s"
  shows "(block11 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (boffset + 1345, 8) 10\<close>
   and \<open>master blocks (boffset + 1353, 8) 11\<close>
   and \<open>master blocks (boffset + 1361, 8) 12\<close>
    using assms[unfolded P_839_def P_def_def pred_logic]
    by auto
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "ret_address > 1200"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = address fp"
   and "RIP s= boffset + 839"
    using assms[unfolded P_839_def P_def_def pred_logic]
    by auto
  note assms' = this

  show ?thesis
    apply (insert assms' minus_one_bit32)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* setne *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (auto simp add: block11_def)[1]
    apply (intro word_eqI)
    apply (auto simp add: word_size nth_shiftl test_bit_of_take_bits)[1]
    apply (auto simp add: P_ret_def P_def_def)[1]

    apply (rewrite_one_let')+
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (auto simp add: block11_def)[1]
    apply (intro word_eqI)
    apply (auto simp add: word_size nth_shiftl test_bit_of_take_bits word_ao_nth)[1]
    apply (auto simp add: P_ret_def P_def_def)[1]
    done
qed

definition abstract_wc :: "file_t \<Rightarrow> getword_state \<times> '\<sigma>\<^sub>C getword_caller_state_scheme \<Rightarrow> getword_state \<times> '\<sigma>\<^sub>C getword_caller_state_scheme \<Rightarrow> bool"
  where "abstract_wc fp \<equiv>
            call (abstract_feof fp) ;
            IF (\<lambda> \<sigma> . feof_ret\<^sub>v (\<L> \<sigma>) \<noteq> 0) THEN
              (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<C> \<sigma>') = 0)
            ELSE
              (\<lambda> \<sigma> \<sigma>' . feof_ret\<^sub>v (\<L> \<sigma>') = undefined) ;
              call (abstract_getc fp) ;
              (\<lambda> \<sigma> \<sigma>' . c\<^sub>v (\<L> \<sigma>') = getc_ret\<^sub>v (\<L> \<sigma>)) ;
              (WHILE (\<lambda> \<sigma> . \<not>breaked\<^sub>v\<^sub>1 (\<L> \<sigma>) \<and> c\<^sub>v (\<L> \<sigma>) \<noteq> -1)  DO
                skip ; 
                call\<^sub>1 abstract_isword (ucast o c\<^sub>v);
                IF (\<lambda> \<sigma> . isword_ret\<^sub>v (\<L> \<sigma>) = 0) THEN
                  (\<lambda> \<sigma> \<sigma>' . ccount\<^sub>v (\<C> \<sigma>') = ccount\<^sub>v (\<C> \<sigma>) + 1 \<and>
                            lcount\<^sub>v (\<C> \<sigma>') = (if c\<^sub>v (\<L> \<sigma>) = 10 then lcount\<^sub>v (\<C> \<sigma>) + 1 else lcount\<^sub>v (\<C> \<sigma>'))) ;
                  call (abstract_getc fp) ;
                  (\<lambda> \<sigma> \<sigma>' . c\<^sub>v (\<L> \<sigma>') = getc_ret\<^sub>v (\<L> \<sigma>))
                ELSE                  
                  (\<lambda> \<sigma> \<sigma>' . breaked\<^sub>v\<^sub>1 (\<L> \<sigma>') \<and> wcount\<^sub>v (\<C> \<sigma>') = wcount\<^sub>v (\<C> \<sigma>) + 1)
                FI 
              OD ;
              (\<lambda> \<sigma> \<sigma>' . breaked\<^sub>v\<^sub>1 (\<L> \<sigma>'))) ;
              (WHILE (\<lambda> \<sigma> . \<not>breaked\<^sub>v\<^sub>2 (\<L> \<sigma>) \<and> c\<^sub>v (\<L> \<sigma>) \<noteq> -1)  DO
                (\<lambda> \<sigma> \<sigma>' . ccount\<^sub>v (\<C> \<sigma>') = ccount\<^sub>v (\<C> \<sigma>) + 1 \<and>
                          lcount\<^sub>v (\<C> \<sigma>') = (if c\<^sub>v (\<L> \<sigma>) = 10 then lcount\<^sub>v (\<C> \<sigma>) + 1 else lcount\<^sub>v (\<C> \<sigma>'))) ;
                call\<^sub>1 abstract_isword (ucast o c\<^sub>v) ;
                (\<lambda> \<sigma> \<sigma>' . breaked\<^sub>v\<^sub>2 (\<L> \<sigma>') = (isword_ret\<^sub>v (\<L> \<sigma>) = 0)) ;
                IF (\<lambda> \<sigma> .  \<not>breaked\<^sub>v\<^sub>2 (\<L> \<sigma>)) THEN
                  call (abstract_getc fp) ;
                  (\<lambda> \<sigma> \<sigma>' . c\<^sub>v (\<L> \<sigma>') = getc_ret\<^sub>v (\<L> \<sigma>))
                ELSE skip FI 
              OD ;
              (\<lambda> \<sigma> \<sigma>' . breaked\<^sub>v\<^sub>2 (\<L> \<sigma>'))) ;
              (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<C> \<sigma>') = (if c\<^sub>v (\<L> \<sigma>) = -1 then 0 else 1))
           FI"
 


lemma getword_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {639,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 639"])
  apply (simp add: line_simps)
  done

lemma getword_decompose2:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {741,746,753,833,839,ret_address}) ;
          run_until_pred (lines {746,753,833,839,ret_address}) ;
          run_until_pred (lines {753,833,839,ret_address}) ;
          run_until_pred (lines {833,839,ret_address}) ;
          run_until_pred (lines {839,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 839"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 839}" "line 833"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 833, 839}" "line 753"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 833, 753, 839}" "line 746"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 746, 833, 753, 839}" "line 741"])
  apply (simp add: line_simps)
  done

lemma getword_decompose3:
  shows "run_until_pred (lines {ret_address, 833, 753, 839}) = 
          run_until_pred (lines {663,668,833,839,753,ret_address}) ;
          run_until_pred (lines {668,833,839,753,ret_address}) ;
          run_until_pred (lines {ret_address, 753, 833,839})"
  apply (subst compose[of "lines {ret_address, 833, 753, 839}" "line 668"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 668, 833, 753,839}" "line 663"])
  apply (simp add: line_simps)
  done

lemma getword_decompose4:
  shows "run_until_pred (lines {ret_address, 753, 833,839}) = 
          run_until_pred (lines {741,746,753,833,839,ret_address}) ;
          run_until_pred (lines {746,753,833,839,ret_address}) ;
          run_until_pred (lines {753,833,839,ret_address})"
  apply (subst compose[of "lines {ret_address, 753, 833, 839}" "line 746"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 746, 833, 753, 839}" "line 741"])
  apply (simp add: line_simps)
  done


lemma getword_decompose5:
  shows "run_until_pred (lines {ret_address, 833,839}) = 
          run_until_pred (lines {807,812,825,833,839,ret_address}) ;
          run_until_pred (lines {812,825,833,839,ret_address}) ;
          run_until_pred (lines {825,833,839,ret_address}) ;
          run_until_pred (lines {833,839,ret_address})"
  apply (subst compose[of "lines {ret_address, 833, 839}" "line 825"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 833, 825, 839}" "line 812"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 812, 833, 825, 839}" "line 807"])
  apply (simp add: line_simps)
  done

lemma getword_decompose6:
  shows "run_until_pred (lines {833,839,ret_address}) = 
          run_until_pred (lines {830,833,839,ret_address}) ;
          run_until_pred (lines {833,839,ret_address})"
  apply (subst compose[of "lines {833,839,ret_address}" "line 830"])
  apply (simp add: line_simps)
  done


lemma abstract_getc:
  assumes "call_getc s s'"
      and "RDI s = address fp"
  shows "abstract_getc fp ((), \<L> S s) ((), \<L> S s')"
proof-
  let ?\<sigma> = "((), \<L> S s)"
  let ?\<sigma>' = "((), \<L> S s')"
  have "RDI s = address fp \<and> call_getc s s' \<and> snd ?\<sigma> = fst (S s) \<and> snd ?\<sigma>' = fst (S s')"
    using assms
    by auto
  thus ?thesis
    unfolding abstract_getc_def
    by auto
qed


lemma abstract_isword:
  assumes "call_isword s s'"
      and "DL s = c"
  shows "abstract_isword c ((), \<L> S s) ((), \<L> S s')"
proof-
  let ?\<sigma> = "((), \<L> S s)"
  let ?\<sigma>' = "((), \<L> S s')"
  have "DL s = c \<and> call_isword s s' \<and> snd ?\<sigma> = fst (S s) \<and> snd ?\<sigma>' = fst (S s')"
    using assms
    by auto
  thus ?thesis
    unfolding abstract_isword_def
    by auto
qed

lemma getword:
  shows "S ::
         {P_608 blocks fp}
            run_until_pred (line ret_address) \<preceq> abstract_wc fp
         {P_ret}"
  apply (subst abstract_wc_def)
  apply (subst getword_decompose)
  (* Call feof(fp) *)
  apply (rule HL_compose[where Q="P_639 blocks fp"])
  apply (rule HL_call_generic[of "\<lambda> s . ((), \<L> S s)" _ _ "line 634" _ "P_634 blocks fp"])
  apply (simp add: comp_def)
  apply (simp add: line_simps)
  apply (rule HL_equality_intro)
  apply (erule getword_608_634)
  apply (simp add: skip_def)
  apply (rule HL_equality_intro)
  apply (erule getword_634_639)
  apply (auto simp add: call_feof_def Let_def abstract_feof_def P_634_def)[1]
  (* If then else *)
  apply (rule HL_ITE[where B="\<lambda> s . EAX s \<noteq> 0"])
    apply (auto simp add: P_639_def P_def_def S_def)[1]
    (* If True *)
    apply (rule HL_equality_intro)
    (* Return 0 *)
    apply (erule getword_639_ret_if_not_0)
    apply (auto simp add: block3_def S_def)[1]
    (* If False *)
    apply (subst getword_decompose2)
    (* Call getc *)
    apply (rule HL_compose[where Q="P_741 blocks fp"])
    apply (rule HL_equality_intro)
    apply (rule getword_639_741_if_0,simp add: pred_logic)
    apply (simp add: block1_def S_def)
    apply (rule HL_compose[where Q="P_746 blocks fp"])
    apply (rule HL_call_generic[of "\<lambda> s . ((), \<L> S s)" _ _ "line 741" _ "P_741 blocks fp"])
    apply (simp add: comp_def)
    apply (rule skip, simp add: line_simps pred_logic P_741_def P_def_def lines_def line_def)
    apply (rule HL_equality_intro)
    apply (erule getword_741_746)
    apply (erule abstract_getc,simp add: P_741_def P_def_def)
    (* Store result getc *)
    apply (rule HL_compose[where Q="P_753 blocks fp || P_833 blocks fp"])
    apply (rule HL_equality_intro)
    apply (erule getword_746_753)
    apply (auto simp add: block2_def S_def P_746_def P_753_def P_833_def P_def_def pred_logic)[1]
    apply (rule HL_compose[where Q="P_833 blocks fp"])
    (* While loop *)
      apply (rule HL_while_v2[of _ "\<lambda>s. \<not>flags s flag_zf" _ _ _ _ _ "line 753"])
      apply (auto simp add: P_753_def P_833_def P_def_def S_def lines_def line_def pred_logic)[1]
      (* Decompose while body into 3 chunks *)
      apply (rule HL_equality_intro)
      apply (erule getword_753_833_to_833)
      apply (simp add: block4_def S_def)
      apply (simp add: line_simps)
      apply (subst getword_decompose3)
      apply (subst seq_assoc[symmetric])
      apply (rule HL_compose)
      apply (rule HL_equality_intro_step[where Q="P_663 blocks fp"])
      apply (erule getword_753_663)
      apply (simp add: skip_def)
      apply (rule HL_compose[where Q="P_668 blocks fp"])
      apply (rule HL_call\<^sub>1_generic[of "\<lambda> s . ((), \<L> S s)" _ _ "line 663" _ "P_663 blocks fp" ])
      apply (simp add: comp_def)
      apply (rule skip,simp add: P_663_def P_def_def pred_logic line_def)
      apply (rule HL_equality_intro)
      apply (erule getword_663_668)
      apply (erule abstract_isword, simp add: S_def P_663_def P_def_def)
      (* IF then else *)
      apply (rule HL_ITE[where B="\<lambda> s . EAX s = 0"])
      apply (simp add: S_def P_668_def P_def_def)  
      apply (subst getword_decompose4)
      apply (rule HL_compose[where Q="P_741 blocks fp"])
      apply (rule HL_equality_intro)
      apply (erule getword_668_741_if_0)
      apply (auto simp add: block5_def S_def P_668_def P_def_def pred_logic)[1]
      apply (rule HL_compose[where Q="P_746 blocks fp"])
      apply (rule HL_call_generic[of "\<lambda> s . ((), \<L> S s)" _ _ "line 741" _ "P_741 blocks fp"])
      apply (simp add: comp_def)
      apply (rule skip, simp add: line_simps pred_logic P_741_def P_def_def lines_def line_def)
      apply (rule HL_equality_intro)
      apply (erule getword_741_746)
      apply (erule abstract_getc,simp add: P_741_def P_def_def)
      apply (rule HL_equality_intro)
      apply (erule getword_746_753)
      apply (auto simp add: block2_def S_def P_746_def P_753_def P_833_def P_def_def pred_logic)[1]
      apply (rule HL_equality_intro)
      apply (erule getword_668_833_if_not_0)
      apply (auto simp add: block6_def S_def)[1]
    (* For loop *)
    apply (rule weaken[where P'="P_833 blocks fp || P_839 blocks fp"])
    apply (auto simp add: pred_logic)[1]
    apply (rule HL_compose[where Q="P_839 blocks fp"])
      apply (rule HL_while_v2[of _ "\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 16,4] \<noteq> (-1::32 word)" _ _ _ _ _ "line 833"])
      apply (auto simp add: S_def P_833_def pred_logic lines_def line_def P_839_def P_def_def)[1]
      apply (rule HL_equality_intro)
      apply (erule getword_833_to_839)
      apply (auto simp add: S_def block7_def)[1]
      apply (simp add: line_simps)
      apply (subst getword_decompose5)
      apply (subst seq_assoc[symmetric])
      apply (rule HL_compose[where Q="P_807 blocks fp"])
      apply (rule HL_equality_intro_step)
      apply (erule getword_833_807)
      apply (auto simp add: S_def block8_def pred_logic P_833_def P_839_def P_def_def)[1]
      apply (rule HL_compose[where Q="P_812 blocks fp"])
      apply (rule HL_call\<^sub>1_generic[of "\<lambda> s . ((), \<L> S s)" _ _ "line 807" _ "P_807 blocks fp"])
      apply (simp add: comp_def)
      apply (rule skip,simp add: P_807_def P_def_def pred_logic line_def)
      apply (rule HL_equality_intro)
      apply (erule getword_807_812)
      apply (erule abstract_isword, simp add: S_def P_807_def P_def_def)
      apply (rule HL_compose[where Q="P_825 blocks fp || P_839 blocks fp"])
      apply (rule HL_equality_intro)
      apply (erule getword_812_to_825_or_839)
      apply (auto simp add: S_def block9_def P_812_def P_825_def P_839_def P_def_def pred_logic split: if_split_asm)[1]
      apply (rule HL_ITE[where B="\<lambda> s . RIP s \<noteq> boffset + 839"])
      apply (auto simp add: S_def)[1]
      apply (subst getword_decompose6)
      apply (rule HL_compose[where Q="P_830 blocks fp"])
      apply (rule HL_call_generic[of "\<lambda> s . ((), \<L> S s)" _ _ "line 825" _ "P_825 blocks fp"])
      apply (simp add: comp_def)
      apply (rule skip,auto simp add: P_825_def P_839_def P_def_def pred_logic line_def)[1]
      apply (rule HL_equality_intro)
      apply (erule getword_825_to_830)
      apply (erule abstract_getc, simp add: P_825_def P_def_def)
      apply (rule HL_equality_intro)
      apply (erule getword_830_to_833)
      apply (auto simp add: S_def P_830_def P_833_def P_839_def P_def_def block10_def pred_logic)[1]
      apply (rule skip,auto simp add: pred_logic lines_def P_825_def P_def_def line_def)[1]
      apply (rule HL_equality_intro)
      apply (erule getword_839_to_ret)
      apply (auto simp add: block11_def S_def P_839_def P_ret_def P_def_def)
  done 


end
