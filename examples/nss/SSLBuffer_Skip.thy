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

theory SSLBuffer_Skip
  imports "SSLEncode"
          "../../isabelle/Calls"
begin

(* FUNCTION sslBuffer_Skip *)


text "The state of the caller of the function."


text "The local state."

type_synonym sslBuffer_Skip_state = sslBuffer_Grow_caller_state 

record sslBuffer_Skip_caller_state =
  savedOffset\<^sub>v :: "32 word option"
  ret'\<^sub>v :: "32 word"

locale sslBuffer_Skip_context = sslencode_context +
  fixes sslBuffer_ptr\<^sub>0 :: "64 word"
    and size\<^sub>0 :: "32 word"
    and buf_len\<^sub>0 :: "32 word"
    and savedOffset\<^sub>0 :: "32 word option"
    and savedOffset_ptr\<^sub>0 :: "64 word"
    and rsp\<^sub>0 :: "64 word"
    and ret_address :: "64 word"
    and blocks :: "(nat \<times> 64 word \<times> nat) set"
    and \<sigma>\<^sub>C :: '\<sigma>\<^sub>C
  assumes ret_address: "ret_address < 885 \<or> ret_address > 987"
    and m0: "master blocks (rsp\<^sub>0, 8) 1"
    and m1: "master blocks (rsp\<^sub>0 - 8, 8) 2"
    and m2: "master blocks (rsp\<^sub>0 - 16, 8) 3"
    and m3: "master blocks (rsp\<^sub>0 - 20, 4) 4"
    and m4: "master blocks (rsp\<^sub>0 - 32, 8) 5"
    and m5: "master blocks (sslBuffer_ptr\<^sub>0, 8) 100"
    and m6: "master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 101"
    and m7: "master blocks (savedOffset_ptr\<^sub>0, 4) 200"
begin


definition P_def
  where "P_def rsp_offset rip_offset s \<equiv> 
      seps blocks
    \<and> RSP s = rsp\<^sub>0 + rsp_offset
    \<and> RIP s = boffset + rip_offset
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
declare P_def_def[simp add]

definition P_sslBuffer_Skip
  where "P_sslBuffer_Skip rip_offset s \<equiv> 
      P_def (-40) rip_offset s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 20,4] = size\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = savedOffset_ptr\<^sub>0"
declare P_sslBuffer_Skip_def [simp add]

text "Precondition"

definition P_885
  where "P_885 s \<equiv> 
      P_def 0 885 s
    \<and> RDI s = sslBuffer_ptr\<^sub>0
    \<and> ESI s = size\<^sub>0
    \<and> RDX s = savedOffset_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0
    \<and> s \<turnstile> *[savedOffset_ptr\<^sub>0,4] = (if savedOffset_ptr\<^sub>0 = 0 then undefined else the savedOffset\<^sub>0)"

definition P_925
  where "P_925 s \<equiv> 
      P_sslBuffer_Skip 925 s
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0
    \<and> s \<turnstile> *[savedOffset_ptr\<^sub>0,4] = (if savedOffset_ptr\<^sub>0 = 0 then undefined else the savedOffset\<^sub>0)"

definition P_930
  where "P_930 s \<equiv> 
      P_sslBuffer_Skip 930 s
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0
    \<and> s \<turnstile> *[savedOffset_ptr\<^sub>0,4] = (if savedOffset_ptr\<^sub>0 = 0 then undefined else the savedOffset\<^sub>0)"

text "Postcondition"

definition P_ret
  where "P_ret s \<equiv>
      RSP s = rsp\<^sub>0 + 8 \<and> 
      RIP s = boffset + ret_address"


text "The simulation relation. Maps concrete states to abstract ones."

definition read_sslBuffer' :: "state \<Rightarrow> 64 word \<Rightarrow> sslBuffer"
  where "read_sslBuffer' s a = \<lparr>
            buf = undefined,
            space = undefined, 
            fixed = undefined,
            len = s \<turnstile> *[a + 8,4]\<rparr>"


definition S :: "state \<Rightarrow> sslBuffer_Skip_state \<times> sslBuffer_Skip_caller_state"
  where "S s \<equiv> (\<lparr> sslBuffer\<^sub>v = read_sslBuffer' s sslBuffer_ptr\<^sub>0 ,
                  ret\<^sub>v = if RIP s = boffset + 930 then EAX s else undefined\<rparr>,
                 \<lparr>savedOffset\<^sub>v = (if savedOffset_ptr\<^sub>0 = 0 then None else Some (s \<turnstile> *[savedOffset_ptr\<^sub>0,4])),
                  ret'\<^sub>v = if RIP s = boffset + ret_address then EAX s else undefined\<rparr>)"

end

locale sslBuffer_Skip_context' = sslBuffer_Skip_context +
  fixes abstract_sslBuffer_Grow :: "sslBuffer_Grow_state \<times> sslBuffer_Skip_state \<Rightarrow> sslBuffer_Grow_state \<times> sslBuffer_Skip_state \<Rightarrow> bool"
    and S' :: "state \<Rightarrow> sslBuffer_Grow_state \<times> sslBuffer_Skip_state"
    and P0 Q0 l0\<^sub>0 :: "state \<Rightarrow> bool"
  assumes S0: "snd \<circ> S0 = fst \<circ> S"
      and prec0:  "S0:: {P_925} run_until_pred (l0\<^sub>0 || F) \<preceq> skip {P0}"
      and hoare0: "S0:: {P} run_until_pred F \<preceq> abstract_sslBuffer_Grow {Q0}"
      and post0:  "\<turnstile> Q0 \<longmapsto> P_930"
begin


lemma sslBuffer_Skip_885_925:
  assumes "P_885 s"
  shows "((\<lambda> s s' . S s' = S s) s && P_925) (The (run_until_pred (lines {925, 930,ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0"
   and "RIP s = boffset + 885"
   and "RDI s = sslBuffer_ptr\<^sub>0"
   and "ESI s = size\<^sub>0"
   and "RDX s = savedOffset_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[savedOffset_ptr\<^sub>0,4] = (if savedOffset_ptr\<^sub>0 = 0 then undefined else the savedOffset\<^sub>0)"
    using assms[unfolded P_885_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  note masters = m0 and m1 and m2 and m3 and m4 and m5 and m6 and m7
  note masters = this

  show ?thesis
    apply (insert assms'(1-9) ret_address)
    apply (symbolic_execution masters: masters) (* push *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* sub *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: S_def read_sslBuffer'_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply (simp (no_asm_simp))
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (simp (no_asm_simp) add: P_925_def)
    apply (rewrite_one_let')+
    using assms'(10) apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    using assms'(10) apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    using assms'(10) apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    using assms'(10) apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    using assms'(10) apply (auto simp add: simp_rules)[1]
    using assms'(10) apply (auto simp add: simp_rules)[1]
    using assms'(10) apply (auto simp add: simp_rules)[1]
    using assms'(10) apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    using assms'(10) apply (auto simp add: simp_rules)[1]
    using assms'(10) apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    using assms'(10) apply (auto simp add: simp_rules)[1]
    done
qed


definition block1 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block1 s s' \<equiv> s' \<turnstile> *[savedOffset_ptr\<^sub>0,4] = (if savedOffset_ptr\<^sub>0 = 0 then s \<turnstile> *[savedOffset_ptr\<^sub>0,4] else s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] :: 32 word)
                        \<and> s' \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = (s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4]) + size\<^sub>0
                        \<and> EAX s' = 0"

lemma sslBuffer_Skip_930_ret:
  assumes "(P_930 && ! (\<lambda>s. EAX s \<noteq> 0)) s"
  shows "(block1 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 930"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 20,4] = size\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = savedOffset_ptr\<^sub>0"
   and "EAX s = 0"
   and "s \<turnstile> *[savedOffset_ptr\<^sub>0,4] = (if savedOffset_ptr\<^sub>0 = 0 then undefined else the savedOffset\<^sub>0)"
    using assms[unfolded P_930_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  note masters = m0 and m1 and m2 and m3 and m4 and m5 and m6 and m7
  note masters = this

  show ?thesis
    apply (insert assms'(1-11) ret_address)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (subst SSLBuffer_Skip.sslBuffer_Skip_context'.block1_def)
    using sslBuffer_Skip_context'_axioms apply auto[1]
    apply (insert masters)
    apply (rewrite_one_let')+
    using assms'(10) apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    using assms'(10) apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    using assms'(10) apply (auto simp add: simp_rules)[1]
    using assms'(10) apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    using assms'(10) apply (auto simp add: simp_rules)[1]
    apply (simp add: P_ret_def)

    apply (rewrite_one_let')+
    apply ((thin_tac \<open>master _ _ _\<close>)+)?
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block1_def)
    apply (rewrite_one_let')+
    apply simp
    apply (simp add: P_ret_def)
    done
qed


definition block2 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block2 s s' \<equiv> EAX s' = -1"

lemma sslBuffer_Skip_930_ret_not0:
  assumes "(P_930 && (\<lambda>s. EAX s \<noteq> 0)) s"
  shows "(block2 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 930"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 20,4] = size\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = savedOffset_ptr\<^sub>0"
   and "EAX s \<noteq> 0"
   and "s \<turnstile> *[savedOffset_ptr\<^sub>0,4] = (if savedOffset_ptr\<^sub>0 = 0 then undefined else the savedOffset\<^sub>0)"
    using assms[unfolded P_930_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  note masters = m0 and m1 and m2 and m3 and m4 and m5 and m6 and m7
  note masters = this

  show ?thesis
    apply (insert assms'(1-11) ret_address)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block2_def)
    apply (simp add: P_ret_def)
    done
qed


definition abstract_sslBuffer_Skip :: "sslBuffer_Skip_state \<times> '\<sigma>\<^sub>C sslBuffer_Skip_caller_state_scheme \<Rightarrow> sslBuffer_Skip_state \<times> '\<sigma>\<^sub>C sslBuffer_Skip_caller_state_scheme \<Rightarrow> bool"
  where "abstract_sslBuffer_Skip \<equiv> 
          call abstract_sslBuffer_Grow ;
          IF (\<lambda> \<sigma> . ret\<^sub>v (\<L> \<sigma>) \<noteq> 0) THEN
            (\<lambda> \<sigma> \<sigma>' . ret'\<^sub>v (\<C> \<sigma>') = -1)
          ELSE
            (\<lambda> \<sigma> \<sigma>' . savedOffset\<^sub>v (\<C> \<sigma>') = (case savedOffset\<^sub>v (\<C> \<sigma>) of None \<Rightarrow> None | Some _ \<Rightarrow> Some (len (sslBuffer\<^sub>v (\<L> \<sigma>))))
                    \<and> len (sslBuffer\<^sub>v (\<L> \<sigma>')) = len (sslBuffer\<^sub>v (\<L> \<sigma>)) + size\<^sub>0
                    \<and> ret'\<^sub>v (\<C> \<sigma>') = 0)
          FI"

lemma sslBuffer_Skip_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {925,930,ret_address}) ;
          run_until_pred (lines {930,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 930"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 930}" "line 925"])
  apply (simp add: line_simps)
  done

lemma sslBuffer_Skip:
  shows "S ::
         {P_885}
            run_until_pred (line ret_address) \<preceq> abstract_sslBuffer_Skip
         {P_ret}"
  apply (subst abstract_sslBuffer_Skip_def)
  apply (subst add_skip[of "call _"])
  apply (subst seq_assoc)
  apply (subst sslBuffer_Skip_decompose)
  apply (rule HL_compose[where Q="P_925"])
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Skip_885_925)
  apply (simp add: S_def skip_def)
  apply (rule HL_compose[where Q="Q0"])
  apply (rule HL_call_generic[of _ _ _ l0\<^sub>0])
  using S0 apply simp
  using prec0 apply auto[1]
  using hoare0 apply simp
  apply (rule weaken[of _ P_930])
  using post0 apply simp
  apply (rule HL_ITE[where B="\<lambda> s. EAX s \<noteq> 0"])
  apply (simp add: S_def P_930_def)
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Skip_930_ret_not0)
  apply (simp add: block2_def S_def read_sslBuffer'_def P_ret_def)
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Skip_930_ret)
  apply (simp add: block1_def S_def read_sslBuffer'_def P_ret_def)
  done

end
(* END FUNCTION sslBuffer_Skip *)





end
