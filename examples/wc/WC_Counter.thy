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

theory WC_Counter
  imports "WC"
begin

(* FUNCTION counter *)


locale wc_counter_context = wc_context +
  fixes file_name_ptr\<^sub>0 :: "64 word"
    and rsp\<^sub>0 :: "64 word"
    and ret_address :: "64 word"
    and blocks :: "(nat \<times> 64 word \<times> nat) set"
    and \<sigma>\<^sub>C :: '\<sigma>\<^sub>C
  assumes ret_address: "ret_address < 851 \<or> ret_address > 1088"
    and file_name_ptr\<^sub>0_not_null: "file_name_ptr\<^sub>0 \<noteq> 0"
    and masters: "master blocks (rsp\<^sub>0, 8) 1"
        "master blocks (rsp\<^sub>0 - 8, 8) 2"
        "master blocks (rsp\<^sub>0 - 16, 8) 3"
        "master blocks (rsp\<^sub>0 - 32, 8) 6"
        "master blocks (boffset + 1345, 8) 100"
        "master blocks (boffset + 1353, 8) 101"
        "master blocks (boffset + 1361, 8) 102"
        "master blocks (boffset + 1321, 8) 103"
        "master blocks (boffset + 1329, 8) 104"
        "master blocks (boffset + 1337, 8) 105"
begin


definition P_def
  where "P_def rsp_offset rip_offset s \<equiv> 
      seps blocks
    \<and> RSP s = rsp\<^sub>0 + rsp_offset
    \<and> RIP s = boffset + rip_offset
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
declare P_def_def[simp add]

definition P_counter
  where "P_counter rip_offset s \<equiv> 
      P_def (-40) rip_offset s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = file_name_ptr\<^sub>0"
declare P_counter_def [simp add]

text "Precondition"

definition P_851
  where "P_851 s \<equiv> 
      P_def 0 851 s
    \<and> RDI s = file_name_ptr\<^sub>0"


text "Postcondition"

definition P_ret
  where "P_ret s \<equiv>
      RSP s = rsp\<^sub>0 + 8 \<and> 
      RIP s = boffset + ret_address"


text "The simulation relation. Maps concrete states to abstract ones."

definition S :: "state \<Rightarrow> counter_state \<times> counter_caller_state"
  where "S s =
            (\<lparr> ret\<^sub>v = if RIP s \<in> {boffset + 965} then EAX s else undefined ,
               wcount\<^sub>v = s \<turnstile> *[boffset + 1345,8],
               ccount\<^sub>v = s \<turnstile> *[boffset + 1353,8],
               lcount\<^sub>v = s \<turnstile> *[boffset + 1361,8],
               fp\<^sub>v = (let ptr = if RIP s = boffset + 880 then RAX s else s \<turnstile> *[rsp\<^sub>0 - 16,8] in if ptr = (0::64 word) then None else Some undefined)
               \<rparr>,
             \<lparr> total_wcount\<^sub>v = s \<turnstile> *[boffset + 1329,8],
               total_ccount\<^sub>v = s \<turnstile> *[boffset + 1321,8],
               total_lcount\<^sub>v = s \<turnstile> *[boffset + 1337,8]
               \<rparr>)"

end

locale wc_counter_context' = wc_counter_context +
  fixes abstract_fopen :: "'a \<times> counter_state \<Rightarrow> 'a \<times> counter_state \<Rightarrow> bool"
    and S0 :: "state \<Rightarrow> 'a \<times> counter_state"
    and P0 Q0 l0\<^sub>0 :: "state \<Rightarrow> bool"
  fixes abstract_fclose :: "'b \<times> counter_state \<Rightarrow> 'b \<times> counter_state \<Rightarrow> bool"
    and S1 :: "state \<Rightarrow> 'b \<times> counter_state"
    and P1 Q1 l1\<^sub>0 :: "state \<Rightarrow> bool"
  fixes abstract_getword :: "'c \<times> counter_state \<Rightarrow> 'c \<times> counter_state \<Rightarrow> bool"
    and S2 :: "state \<Rightarrow> 'c \<times> counter_state"
    and P2 Q2 l2\<^sub>0 :: "state \<Rightarrow> bool"
  fixes abstract_report :: "'d \<times> counter_state \<Rightarrow> 'd \<times> counter_state \<Rightarrow> bool"
    and S3 :: "state \<Rightarrow> 'd \<times> counter_state"
    and P3 Q3 l3\<^sub>0 :: "state \<Rightarrow> bool"
  fixes abstract_perrf :: "'e \<times> counter_state \<Rightarrow> 'e \<times> counter_state \<Rightarrow> bool"
    and S4 :: "state \<Rightarrow> 'e \<times> counter_state"
    and P4 Q4 l4\<^sub>0 :: "state \<Rightarrow> bool"
  assumes S0: "snd \<circ> S0 = fst \<circ> S"
      and prec0:  "S0:: {P_counter 875} run_until_pred (l0\<^sub>0 || F) \<preceq> skip {P0}"
      and hoare0: "S0:: {P0} run_until_pred F \<preceq> abstract_fopen {Q0}"
      and post0:  "\<turnstile> Q0 \<longmapsto> P_counter 880"
  assumes S1: "snd \<circ> S1 = fst \<circ> S"
      and prec1:  "S1:: {P_counter 976} run_until_pred (l1\<^sub>0 || F) \<preceq> skip {P1}"
      and hoare1: "S1:: {P1} run_until_pred F \<preceq> abstract_fclose {Q1}"
      and post1:  "\<turnstile> Q1 \<longmapsto> P_counter 981"
  assumes S2: "snd \<circ> S2 = fst \<circ> S"
      and prec2:  "S2:: {P_counter 960} run_until_pred (l2\<^sub>0 || F) \<preceq> skip {P2}"
      and hoare2: "S2:: {P2} run_until_pred F \<preceq> abstract_getword {Q2}"
      and post2:  "\<turnstile> Q2 \<longmapsto> P_counter 965"
  assumes S3: "snd \<circ> S3 = fst \<circ> S"
      and prec3:  "S3:: {P_counter 1009} run_until_pred (l3\<^sub>0 || F) \<preceq> skip {P3}"
      and hoare3: "S3:: {P3} run_until_pred F \<preceq> abstract_report {Q3}"
      and post3:  "\<turnstile> Q3 \<longmapsto> P_counter 1014"
  assumes S4: "snd \<circ> S4 = fst \<circ> S"
      and prec4:  "S4:: {P_counter 908} run_until_pred (l4\<^sub>0 || F) \<preceq> skip {P4}"
      and hoare4: "S4:: {P4} run_until_pred F \<preceq> abstract_perrf {Q4}"
      and post4:  "\<turnstile> Q4 \<longmapsto> P_counter 913"
begin



definition block1 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block1 s s' \<equiv> True"

lemma counter_851_875:
  assumes "P_851 s"
  shows "(block1 s && P_counter 875) (The (run_until_pred (lines {875,880,913,960,965,976,981,1009,1014,ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 851"
   and "RSP s = rsp\<^sub>0"
   and "RDI s = file_name_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
    using assms[unfolded P_851_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* push *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* sub *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters file_name_ptr\<^sub>0_not_null)
    apply (simp (no_asm_simp) add: block1_def)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    done
qed

lemma counter_880_908:
  assumes "(P_counter 880 && (\<lambda> s . RAX s = 0)) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_counter 908) (The (run_until_pred (lines {908,913,960,965,976,981,1009,1014,ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 880"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"  
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = file_name_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "RAX s = 0"
    using assms[unfolded P_counter_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: S_def)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules Let'_def)[1]
    done
qed


definition block2 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block2 s s' \<equiv> RIP s' = boffset + 913"

lemma counter_880_913:
  assumes "(P_counter 880 && ! (\<lambda> s . RAX s = 0)) s"
  shows "(block2 s && P_counter 913) (The (run_until_pred (lines {913,960,965,976,981,1009,1014,ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 880"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"  
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = file_name_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "RAX s \<noteq> 0"
    using assms[unfolded P_counter_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block2_def)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules Let'_def)[1]
    done
qed

definition block3 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block3 s s' \<equiv> s' \<turnstile> *[boffset + 1345,8] = (0::64 word)
                    \<and> s' \<turnstile> *[boffset + 1353,8] = (0::64 word)
                    \<and> s' \<turnstile> *[boffset + 1361,8] = (0::64 word)"

lemma counter_913_960:
  assumes "P_counter 913 s"
  shows "(block3 s && P_counter 960) (The (run_until_pred (lines {960,965,976,981,1009,1014,ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 913"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"  
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = file_name_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
    using assms[unfolded P_counter_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* nop *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block3_def)
    apply (rewrite_one_let')+
    apply (simp (no_asm_simp))         
    done
qed

lemma counter_965_960:
  assumes "(P_counter 965 && (\<lambda>s. EAX s \<noteq> 0)) s"
  shows "((\<lambda> s s' . RIP s' = boffset + 960) s && P_counter 960) (The (((\<lambda>s. (=) (step s)) ; run_until_pred (lines {ret_address, 960, 976, 1014, 1009, 965, 981})) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 965"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"  
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = file_name_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "EAX s \<noteq> 0"
    using assms[unfolded P_counter_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (rewrite_one_step) (* test *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    done
qed


lemma counter_965_976:
  assumes "(P_counter 965 && ! (\<lambda>s. EAX s \<noteq> 0)) s"
  shows "((\<lambda> s s' . RIP s' = boffset + 976) s && P_counter 976) (The (run_until_pred (lines {976, 981, 1009, 1014, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 965"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"  
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = file_name_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "EAX s = 0"
    using assms[unfolded P_counter_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    done
qed

lemma counter_981_1009:
  assumes "P_counter 981 s"
  shows "((\<lambda> s s' . S s' = S s) s && P_counter 1009) (The (run_until_pred (lines {1009, 1014, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 981"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"  
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = file_name_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
    using assms[unfolded P_counter_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: S_def)
    done
qed

definition block4 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block4 s s' \<equiv> s' \<turnstile> *[boffset + 1337,8] = (s \<turnstile> *[boffset + 1337,8]) + (s \<turnstile> *[boffset + 1361,8]::64 word)
                    \<and> s' \<turnstile> *[boffset + 1329,8] = (s \<turnstile> *[boffset + 1329,8]) + (s \<turnstile> *[boffset + 1345,8]::64 word)
                    \<and> s' \<turnstile> *[boffset + 1321,8] = (s \<turnstile> *[boffset + 1321,8]) + (s \<turnstile> *[boffset + 1353,8]::64 word)"

lemma counter_1014_ret:
  assumes "P_counter 1014 s"
  shows "(block4 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1014"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"  
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = file_name_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
    using assms[unfolded P_counter_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block4_def)
    apply (rewrite_one_let')+
    apply auto[1]
    apply (simp add: P_ret_def)
    done
qed

definition abstract_counter :: "counter_state \<times> counter_caller_state \<Rightarrow> counter_state \<times> counter_caller_state \<Rightarrow> bool"
  where "abstract_counter \<equiv> 
          (\<lambda> \<sigma> \<sigma>' . True) ;          
          call abstract_fopen;
          IF (\<lambda> \<sigma> . fp\<^sub>v (\<L> \<sigma>) = None) THEN
            call abstract_perrf
          ELSE 
            (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<L> \<sigma>') = undefined)
          FI ;
          (\<lambda> \<sigma> \<sigma>' . wcount\<^sub>v (\<L> \<sigma>') = 0
                  \<and> lcount\<^sub>v (\<L> \<sigma>') = 0
                  \<and> ccount\<^sub>v (\<L> \<sigma>') = 0) ;
          call abstract_getword ;
          WHILE (\<lambda> \<sigma> . ret\<^sub>v (\<L> \<sigma>) \<noteq> 0) DO
            (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<L> \<sigma>') = undefined) ;
            call abstract_getword
          OD; 
          (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<L> \<sigma>') = undefined) ;
          call abstract_fclose ;
          call abstract_report ;
          (\<lambda> \<sigma> \<sigma>' . total_wcount\<^sub>v (\<C> \<sigma>') = total_wcount\<^sub>v (\<C> \<sigma>) + wcount\<^sub>v (\<L> \<sigma>)
                  \<and> total_lcount\<^sub>v (\<C> \<sigma>') = total_lcount\<^sub>v (\<C> \<sigma>) + lcount\<^sub>v (\<L> \<sigma>)
                  \<and> total_ccount\<^sub>v (\<C> \<sigma>') = total_ccount\<^sub>v (\<C> \<sigma>) + ccount\<^sub>v (\<L> \<sigma>))"

lemma counter_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {875,880,913,960,965,976,981,1009,1014,ret_address}) ;
          run_until_pred (lines {880,913,960,965,976,981,1009,1014,ret_address}) ;
          run_until_pred (lines {913,960,965,976,981,1009,1014,ret_address}) ;
          run_until_pred (lines {960,965,976,981,1009,1014,ret_address}) ;
          run_until_pred (lines {965,976,981,1009,1014,ret_address}) ;
          run_until_pred (lines {976,981,1009,1014,ret_address}) ;
          run_until_pred (lines {981,1009,1014,ret_address}) ;
          run_until_pred (lines {1009,1014,ret_address}) ;
          run_until_pred (lines {1014,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 1014"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 1014}" "line 1009"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 1014, 1009}" "line 981"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 1014, 1009, 981}" "line 976"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 976, 1014, 1009, 981}" "line 965"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 976, 1014, 1009, 965, 981}" "line 960"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 960, 976, 1014, 1009, 965, 981}" "line 913"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 960, 976, 1014, 913, 1009, 965, 981}" "line 880"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 960, 976, 880, 1014, 913, 1009, 965, 981}" "line 875"])
  apply (simp add: line_simps)
  done

lemma counter_decompose2:
  shows "run_until_pred (lines {913, 960, 965, 976, 981, 1009, 1014, ret_address}) =
          run_until_pred (lines {908, 913, 960, 965, 976, 981, 1009, 1014, ret_address}) ;
          run_until_pred (lines {913, 960, 965, 976, 981, 1009, 1014, ret_address})"
  apply (subst compose[of "lines {913, 960, 965, 976, 981, 1009, 1014, ret_address}" "line 908"])
  apply (simp add: line_simps)
  done

lemma counter_decompose3:
  shows "run_until_pred (lines {ret_address, 976, 1014, 1009, 965, 981}) =
          run_until_pred (lines {ret_address, 960, 976, 1014, 1009, 965, 981}) ;
          run_until_pred (lines {ret_address, 976, 1014, 1009, 965, 981})"
  apply (subst compose[of "lines {ret_address, 976, 1014, 1009, 965, 981}" "line 960"])
  apply (simp add: line_simps)
  done


lemma counter:
  shows "S ::
         {P_851}
            run_until_pred (line ret_address) \<preceq> abstract_counter   
         {P_ret}"
  apply (subst abstract_counter_def)
  apply (subst counter_decompose)
  apply (rule HL_compose[where Q="P_counter 875"])
  apply (rule HL_equality_intro)
  apply (erule counter_851_875)
  apply (simp)
  apply (rule HL_compose[where Q="P_counter 880"])
  apply (rule HL_call_generic)
  apply (rule S0)
  apply (rule prec0)
  apply (rule strengthen[OF post0])
  apply (rule hoare0)
  apply (rule HL_compose[where Q="P_counter 913"])
  apply (rule HL_ITE[where B="\<lambda> s . RAX s = 0"])
  apply (simp add: S_def)
  apply (subst counter_decompose2)
  apply (subst add_skip[of "call _"])
  apply (rule HL_compose[where Q="P_counter 908"])
  apply (rule HL_equality_intro)
  apply (erule counter_880_908)
  apply (simp add: skip_def)
  apply (rule HL_call_generic)
  apply (rule S4)
  apply (rule prec4)
  apply (rule strengthen[OF post4])
  apply (rule hoare4)
  apply (rule HL_equality_intro)
  apply (erule counter_880_913)
  apply (simp add: block2_def S_def)
  apply (rule HL_compose[where Q="P_counter 960"])
  apply (rule HL_equality_intro)
  apply (erule counter_913_960)
  apply (simp add: block3_def S_def)
  apply (rule HL_compose[where Q="P_counter 965"])
  apply (rule HL_call_generic)
  apply (rule S2)
  apply (rule prec2)
  apply (rule strengthen[OF post2])
  apply (rule hoare2)
  apply (subst seq_assoc[symmetric,of "WHILE _ DO _ OD"])
  apply (rule HL_compose[where Q="P_counter 976"])
  apply (rule HL_while_generic[where B="\<lambda> s . EAX s \<noteq> 0" and F'="line 965"])
  using ret_address apply (auto simp add: lines_def line_def S_def)[1]
  apply (simp add: line_simps)
  apply (subst counter_decompose3)
  apply (subst seq_assoc[symmetric])
  apply (rule HL_compose[where Q="P_counter 960"])
  apply (rule HL_equality_intro_step)
  apply (erule counter_965_960)
  apply (simp add: S_def )
  apply (rule HL_call_generic)
  apply (rule S2)
  apply (rule prec2)
  apply (rule strengthen[OF post2])
  apply (rule hoare2)
  apply (rule HL_equality_intro)
  apply (erule counter_965_976)
  apply (simp add: S_def)
  apply (rule HL_compose[where Q="P_counter 981"])
  apply (rule HL_call_generic)
  apply (rule S1)
  apply (rule prec1)
  apply (rule strengthen[OF post1])
  apply (rule hoare1)
  apply (subst add_skip[of "call _"])
  apply (subst seq_assoc)
  apply (rule HL_compose[where Q="P_counter 1009"])
  apply (rule HL_equality_intro)
  apply (erule counter_981_1009)
  apply (simp add: skip_def)
  apply (rule HL_compose[where Q="P_counter 1014"])
  apply (rule HL_call_generic)
  apply (rule S3)
  apply (rule prec3)
  apply (rule strengthen[OF post3])
  apply (rule hoare3)
  apply (rule HL_equality_intro)
  apply (erule counter_1014_ret)
  apply (simp add: block4_def S_def)
  done

(* END FUNCTION counter *)

end
