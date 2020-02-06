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

theory SSLBuffer_AppendNumber
  imports "SSLEncode"
          "../../isabelle/Calls"
begin

(* FUNCTION sslBuffer_AppendNumber *)


text "The state of the caller of the function."

record sslBuffer_AppendNumber_caller_state =
  ret'\<^sub>v :: "32 word"

text "The local state."

type_synonym sslBuffer_AppendNumber_state = sslBuffer_Grow_caller_state



locale sslBuffer_AppendNumber_context = sslencode_context +
  fixes sslBuffer_ptr\<^sub>0 :: "64 word"
    and buf_ptr\<^sub>0 :: "64 word"
    and buf_len\<^sub>0 :: "32 word"
    and data_ptr\<^sub>0 :: "64 word"
    and size\<^sub>0 :: "32 word"
    and rsp\<^sub>0 :: "64 word"
    and ret_address :: "64 word"
    and blocks :: "(nat \<times> 64 word \<times> nat) set"
    and \<sigma>\<^sub>C :: '\<sigma>\<^sub>C
  assumes ret_address: "ret_address < 433 \<or> ret_address > 558"
begin


definition P_def
  where "P_def rsp_offset rip_offset ret_address_bounds s \<equiv> 
      seps blocks
    \<and> master blocks (rsp\<^sub>0, 8) 1
    \<and> master blocks (rsp\<^sub>0 - 8, 8) 2
    \<and> master blocks (rsp\<^sub>0 - 12, 4) 3
    \<and> master blocks (rsp\<^sub>0 - 32, 8) 5
    \<and> master blocks (rsp\<^sub>0 - 40, 8) 6
    \<and> master blocks (rsp\<^sub>0 - 44, 4) 7
    \<and> master blocks (sslBuffer_ptr\<^sub>0, 8) 100
    \<and> master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 101
    \<and> master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 102
    \<and> master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 103
    \<and> RSP s = rsp\<^sub>0 + rsp_offset
    \<and> RIP s = boffset + rip_offset
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address
    \<and> (ret_address < fst ret_address_bounds \<or> ret_address > snd ret_address_bounds)"
declare P_def_def[simp add]

definition P_sslBuffer_AppendNumber
  where "P_sslBuffer_AppendNumber rsp_offset rip_offset s \<equiv> 
      P_def rsp_offset rip_offset (433,558) s"
declare P_sslBuffer_AppendNumber_def [simp add]

text "Precondition"

definition P_433
  where "P_433 s \<equiv> 
      P_sslBuffer_AppendNumber 0 433 s
    \<and> RDI s = sslBuffer_ptr\<^sub>0
    \<and> RSI s = data_ptr\<^sub>0
    \<and> EDX s = size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"

definition P_473
  where "P_473 s \<equiv> 
      P_sslBuffer_AppendNumber (-56) 473 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> RDI s = sslBuffer_ptr\<^sub>0
    \<and> ESI s = buf_len\<^sub>0 + size\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 40,8] = data_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 44,4] = size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"

definition P_478
  where "P_478 s \<equiv> 
      P_sslBuffer_AppendNumber (-56) 478 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 44,4] = size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"

definition P_527
  where "P_527 s \<equiv> 
      P_sslBuffer_AppendNumber (-56) 527 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 44,4] = size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"

definition P_532
  where "P_532 s \<equiv> 
      P_sslBuffer_AppendNumber (-56) 532 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 44,4] = size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"

text "Postcondition"

definition P_ret
  where "P_ret s \<equiv>
      RSP s = rsp\<^sub>0 + 8 \<and> 
      RIP s = boffset + ret_address"


text "The simulation relation. Maps concrete states to abstract ones."

definition read_sslBuffer' :: "state \<Rightarrow> 64 word \<Rightarrow> sslBuffer"
  where "read_sslBuffer' s a = \<lparr>
            buf = undefined,
            space = s \<turnstile> *[a + 12,4], 
            fixed = undefined,
            len = s \<turnstile> *[a + 8,4]\<rparr>"


definition S :: "state \<Rightarrow> sslBuffer_AppendNumber_state \<times> ('\<sigma>\<^sub>C) sslBuffer_AppendNumber_caller_state_scheme"
  where "S s \<equiv> (\<lparr> sslBuffer\<^sub>v = read_sslBuffer' s sslBuffer_ptr\<^sub>0, 
                  ret\<^sub>v = if RIP s = boffset + 478 then EAX s else undefined
                   \<rparr>, 
                   \<lparr> ret'\<^sub>v = if RIP s = boffset + ret_address then EAX s else undefined,
                    \<dots> = \<sigma>\<^sub>C \<rparr>)"

end

locale sslBuffer_AppendNumber_context' = sslBuffer_AppendNumber_context +
  fixes abstract_sslBuffer_Grow :: "sslBuffer_Grow_state \<times> sslBuffer_AppendNumber_state \<Rightarrow> sslBuffer_Grow_state \<times> sslBuffer_AppendNumber_state \<Rightarrow> bool"
    and S' :: "state \<Rightarrow> sslBuffer_Grow_state \<times> sslBuffer_AppendNumber_state"
    and P Q l\<^sub>0 :: "state \<Rightarrow> bool"
  fixes abstract_ssl_EncodeUintX :: "'a \<times> sslBuffer_AppendNumber_state \<Rightarrow> 'a \<times> sslBuffer_AppendNumber_state \<Rightarrow> bool"
    and S'' :: "state \<Rightarrow> 'a \<times> sslBuffer_AppendNumber_state"
    and P' Q' l\<^sub>0' :: "state \<Rightarrow> bool"
  assumes S': "snd \<circ> S' = fst \<circ> S"
      and prec:  "S':: {P_473} run_until_pred (l\<^sub>0 || F) \<preceq> skip {P}"
      and hoare: "S':: {P} run_until_pred F \<preceq> abstract_sslBuffer_Grow {Q}"
      and post:  "\<turnstile> Q \<longmapsto> P_478"
  assumes S'': "snd \<circ> S'' = fst \<circ> S"
      and prec':  "S'':: {P_527} run_until_pred (l\<^sub>0' || F') \<preceq> skip {P'}"
      and hoare': "S'':: {P'} run_until_pred F \<preceq> abstract_ssl_EncodeUintX {Q'}"
      and post':  "\<turnstile> Q' \<longmapsto> P_532"
begin


lemma sslBuffer_AppendNumber_433_473:
  assumes "P_433 s"
  shows "((\<lambda> s s' . S s' = S s) s && P_473) (The (run_until_pred (lines {473, 478, ret_address}) s))"
  proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0"
   and "RIP s = boffset + 433"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "RDI s = sslBuffer_ptr\<^sub>0"
   and "RSI s = data_ptr\<^sub>0"
   and "EDX s = size\<^sub>0"
   and "ret_address < 433 \<or> ret_address > 558"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"
    using assms[unfolded P_433_def]
    by auto
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 40, 8) 6\<close>
   and \<open>master blocks (rsp\<^sub>0 - 44, 4) 7\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 102\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 103\<close>
    using assms[unfolded P_433_def]
    by auto
  note masters = this

  show ?thesis
    apply (insert assms')
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
    apply (insert masters)
    apply (simp (no_asm_simp) add: S_def read_sslBuffer'_def)[1]
    apply (rule conjI)
    apply auto[1]
    apply (rule impI)
    apply auto[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (simp (no_asm_simp) add: P_473_def)[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    done
qed

definition block2 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block2 s s' \<equiv> EAX s' = -1 \<and> RIP s' = boffset + ret_address"

lemma sslBuffer_AppendNumber_478_ret_not0:
  assumes "(P_478 && (\<lambda>s. EAX s \<noteq> 0)) s"
  shows "(block2 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 478"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 433 \<or> ret_address > 558"
   and "EAX s \<noteq> 0"
    using assms[unfolded P_478_def]
    by (auto simp add: pred_logic)
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 40, 8) 6\<close>
   and \<open>master blocks (rsp\<^sub>0 - 44, 4) 7\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 102\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 103\<close>
    using assms[unfolded P_478_def]
    by (auto simp add: pred_logic)
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block2_def)[1]
    apply (simp (no_asm_simp) add: P_ret_def)[1]
    done
qed


definition block1 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block1 s s' \<equiv> RIP s' = boffset + 527"

lemma sslBuffer_AppendNumber_478_527:
  assumes "(P_478 && ! (\<lambda>s. EAX s \<noteq> 0)) s"
  shows "(block1 s && P_527) (The (run_until_pred (lines {527, 532, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 478"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 433 \<or> ret_address > 558"
   and "EAX s = 0"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 44,4] = size\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
    using assms[unfolded P_478_def]
    by (auto simp add: pred_logic)
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 40, 8) 6\<close>
   and \<open>master blocks (rsp\<^sub>0 - 44, 4) 7\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 102\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 103\<close>
    using assms[unfolded P_478_def]
    by (auto simp add: pred_logic)
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* lea *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block1_def)[1]
    apply (simp (no_asm_simp) add: P_527_def)[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    done
qed


definition block3 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block3 s s' \<equiv> EAX s' = 0 
                        \<and> s' \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0 + size\<^sub>0"

lemma sslBuffer_AppendNumber_532_ret:
  assumes "P_532 s"
  shows "(block3 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 532"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 433 \<or> ret_address > 558"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 44,4] = size\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
    using assms[unfolded P_532_def]
    by (auto simp add: pred_logic)
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 12, 4) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 40, 8) 6\<close>
   and \<open>master blocks (rsp\<^sub>0 - 44, 4) 7\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 102\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 103\<close>
    using assms[unfolded P_532_def]
    by (auto simp add: pred_logic)
  note masters = this

  show ?thesis
    apply (insert assms')
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
    apply (simp (no_asm_simp) add: block3_def)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (simp (no_asm_simp) add: P_ret_def)
    done
qed


definition abstract_sslBuffer_AppendNumber :: "sslBuffer_AppendNumber_state \<times> '\<sigma>\<^sub>C sslBuffer_AppendNumber_caller_state_scheme \<Rightarrow> sslBuffer_AppendNumber_state \<times> '\<sigma>\<^sub>C sslBuffer_AppendNumber_caller_state_scheme \<Rightarrow> bool"
  where "abstract_sslBuffer_AppendNumber \<equiv> 
          call abstract_sslBuffer_Grow ;
          IF (\<lambda> \<sigma> . ret\<^sub>v (\<L> \<sigma>) \<noteq> 0) THEN
            (\<lambda> \<sigma> \<sigma>' . ret'\<^sub>v (\<C> \<sigma>') = -1)
          ELSE
            (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<L> \<sigma>') = undefined ) ;
            call abstract_ssl_EncodeUintX ;
            (\<lambda> \<sigma> \<sigma>' . ret'\<^sub>v (\<C> \<sigma>') = 0
                    \<and> len (sslBuffer\<^sub>v (\<L> \<sigma>')) = buf_len\<^sub>0 + size\<^sub>0)
          FI"

lemma sslBuffer_AppendNumber_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {473,478,ret_address}) ;
          run_until_pred (lines {478,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 478"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 478}" "line 473"])
  apply (simp add: line_simps)
  done

lemma sslBuffer_AppendNumber_decompose2:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {527,532,ret_address}) ;
          run_until_pred (lines {532,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 532"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 532}" "line 527"])
  apply (simp add: line_simps)
  done


lemma sslBuffer_AppendNumber:
  shows "S ::
         {P_433}
            run_until_pred (line ret_address) \<preceq> abstract_sslBuffer_AppendNumber
         {P_ret}"
  apply (subst abstract_sslBuffer_AppendNumber_def)
  apply (subst sslBuffer_AppendNumber_decompose)
  apply (subst add_skip[of "call abstract_sslBuffer_Grow"])
  apply (subst seq_assoc)
  apply (rule HL_compose[where Q="P_473"])
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_AppendNumber_433_473)
  apply (simp add: skip_def)
  apply (rule HL_compose[where Q=Q])
  apply (rule HL_call_generic[of S' _ _  l\<^sub>0 _ P])
  using S' apply simp
  using prec apply simp
  using hoare apply simp
  apply (rule weaken[of _ P_478])
  using post apply simp
  apply (rule HL_ITE[where B="\<lambda> s . EAX s \<noteq> 0"])
  apply (auto simp add: S_def P_478_def)[1]
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_AppendNumber_478_ret_not0)
  using ret_address apply (auto simp add: block2_def S_def P_ret_def pred_logic)[1]
  apply (subst sslBuffer_AppendNumber_decompose2)
  apply (rule HL_compose[where Q="P_527"])
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_AppendNumber_478_527)
  apply (simp add: block1_def S_def)
  apply (rule HL_compose[where Q=Q'])
  apply (rule HL_call_generic[of S'' _ _ l\<^sub>0' _ P'])
  using S'' apply simp
  using prec' apply simp
  using hoare' apply simp
  apply (rule weaken[of _ P_532])
  using post' apply simp
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_AppendNumber_532_ret)
  using ret_address apply (auto simp add: block3_def S_def P_ret_def read_sslBuffer'_def)[1]
  done

end
(* END FUNCTION sslBuffer_AppendNumber *)





end
