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

theory SSLBuffer_InsertLength
  imports "SSLEncode"
          "../../isabelle/Calls"
begin

(* FUNCTION sslBuffer_InsertLength *)


text "The state of the caller of the function."

record sslBuffer_InsertLength_caller_state =
  ret'\<^sub>v :: "32 word"

text "The local state."

record sslBuffer_InsertLength_state =
  sslBuffer\<^sub>v :: sslBuffer
  len\<^sub>v :: "32 word"


locale sslBuffer_InsertLength_context = sslencode_context +
  fixes sslBuffer_ptr\<^sub>0 :: "64 word"
    and at\<^sub>0 :: "32 word"
    and size\<^sub>0 :: "32 word"
    and buf_ptr\<^sub>0 :: "64 word"
    and buf_len\<^sub>0 :: "32 word"
    and data_ptr\<^sub>0 :: "64 word"
    and rsp\<^sub>0 :: "64 word"
    and ret_address :: "64 word"
    and blocks :: "(nat \<times> 64 word \<times> nat) set"
    and \<sigma>\<^sub>C :: '\<sigma>\<^sub>C
  assumes ret_address: "ret_address < 987 \<or> ret_address > 1101"
    and m0: "master blocks (rsp\<^sub>0, 8) 1"
    and m1: "master blocks (rsp\<^sub>0 - 8, 8) 2"
    and m2: "master blocks (rsp\<^sub>0 - 12, 4) 2"
    and m3: "master blocks (rsp\<^sub>0 - 32, 8) 6"
    and m4: "master blocks (rsp\<^sub>0 - 36, 4) 7"
    and m5: "master blocks (rsp\<^sub>0 - 40, 4) 8"
    and m6: "master blocks (sslBuffer_ptr\<^sub>0, 8) 100"
    and m7: "master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 101"
    and m8: "master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 102"
    and m9: "master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 103"
begin


definition P_def
  where "P_def rsp_offset rip_offset s \<equiv> 
      seps blocks
    \<and> RSP s = rsp\<^sub>0 + rsp_offset
    \<and> RIP s = boffset + rip_offset
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
declare P_def_def[simp add]

definition P_sslBuffer_InsertLength
  where "P_sslBuffer_InsertLength rip_offset s \<equiv> 
      P_def (-40) rip_offset s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 36,4] = at\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 40,4] = size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"

declare P_sslBuffer_InsertLength_def [simp add]

text "Precondition"

definition P_987
  where "P_987 s \<equiv> 
      P_def 0 987 s
    \<and> RDI s = sslBuffer_ptr\<^sub>0
    \<and> ESI s = at\<^sub>0
    \<and> EDX s = size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"

definition P_1042
  where "P_1042 s \<equiv> 
      P_sslBuffer_InsertLength 1042 s
    \<and> RAX s = (ucast (s \<turnstile> *[rsp\<^sub>0 - 12,4] :: 32 word) >> unat (\<langle>7,0\<rangle>(ucast size\<^sub>0 << 3 :: 64 word) :: 64 word))"

definition P_1052
  where "P_1052 s \<equiv> 
      P_sslBuffer_InsertLength 1052 s"

definition P_1057
  where "P_1057 s \<equiv> 
      P_sslBuffer_InsertLength 1057 s"

definition P_1089
  where "P_1089 s \<equiv> 
      P_sslBuffer_InsertLength 1089 s"

definition P_1094
  where "P_1094 s \<equiv> 
      P_sslBuffer_InsertLength 1094 s"


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


definition S :: "state \<Rightarrow> sslBuffer_InsertLength_state \<times> ('\<sigma>\<^sub>C) sslBuffer_InsertLength_caller_state_scheme"
  where "S s \<equiv> (\<lparr> sslBuffer\<^sub>v = read_sslBuffer' s sslBuffer_ptr\<^sub>0, 
                  len\<^sub>v = s \<turnstile> *[rsp\<^sub>0 - 12,4]
                   \<rparr>, 
                   \<lparr> ret'\<^sub>v = if RIP s = boffset + ret_address then EAX s else undefined,
                    \<dots> = \<sigma>\<^sub>C \<rparr>)"

end

locale sslBuffer_InsertLength_context' = sslBuffer_InsertLength_context +
  fixes abstract_PORT_SetError :: "32 word \<Rightarrow> 'a \<times> sslBuffer_InsertLength_state \<Rightarrow> 'a \<times> sslBuffer_InsertLength_state \<Rightarrow> bool"
    and S0 :: "state \<Rightarrow> 'a \<times> sslBuffer_InsertLength_state"
    and P0 Q0 l0\<^sub>0 :: "state \<Rightarrow> bool"
  fixes abstract_ssl_EncodeUintX :: "'b \<times> sslBuffer_InsertLength_state \<Rightarrow> 'b \<times> sslBuffer_InsertLength_state \<Rightarrow> bool"
    and S2 :: "state \<Rightarrow> 'b \<times> sslBuffer_InsertLength_state"
    and P2 Q2 l2\<^sub>0 :: "state \<Rightarrow> bool"
  assumes S0: "snd \<circ> S0 = fst \<circ> S"
      and prec0:  "S0:: {P_1052} run_until_pred (l0\<^sub>0 || F) \<preceq> skip {P0}"
      and hoare0: "S0:: {P0} run_until_pred F \<preceq> abstract_PORT_SetError p\<^sub>0 {Q0}"
      and post0:  "\<turnstile> Q0 \<longmapsto> P_1057"
  assumes S2: "snd \<circ> S2 = fst \<circ> S"
      and prec2:  "S2:: {P_1089} run_until_pred (l2\<^sub>0 || F) \<preceq> skip {P2}"
      and hoare2: "S2:: {P2} run_until_pred F \<preceq> abstract_ssl_EncodeUintX {Q2}"
      and post2:  "\<turnstile> Q2 \<longmapsto> P_1094"
begin

definition block1 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block1 s s' \<equiv> s' \<turnstile> *[rsp\<^sub>0 - 12,4] = buf_len\<^sub>0 - (at\<^sub>0 + size\<^sub>0)"

lemma sslBuffer_AppendVariable_987_1042:
  assumes "P_987 s"
  shows "(block1 s && P_1042) (The (run_until_pred (lines {1042, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0"
   and "RIP s = boffset + 987"
   and "RDI s = sslBuffer_ptr\<^sub>0"
   and "ESI s = at\<^sub>0"
   and "EDX s = size\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
    using assms[unfolded P_987_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  note masters = m0 and m1 and m2 and m3 and m4 and m5 and m6 and m7 and m8 and m9
  note masters = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* push *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* sub *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* sub *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* shl *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* shr *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block1_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply (simp)
    apply (simp (no_asm_simp) add: P_1042_def)
    apply (rewrite_one_let')+
    apply (simp)
    done
qed
    
lemma sslBuffer_AppendVariable_1042_1052_not0:
  assumes "(P_1042 && (\<lambda>s. regs s rax \<noteq> 0)) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_1052) (The (run_until_pred (lines {1052, 1057, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 1042"
   and "RAX s = (ucast (s \<turnstile> *[rsp\<^sub>0 - 12,4] :: 32 word) >> unat (\<langle>7,0\<rangle>(ucast size\<^sub>0 << 3 :: 64 word) :: 64 word))"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 36,4] = at\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,4] = size\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "RAX s \<noteq> 0"
    using assms[unfolded P_1042_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  note masters = m0 and m1 and m2 and m3 and m4 and m5 and m6 and m7 and m8 and m9
  note masters = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: S_def read_sslBuffer'_def)
    apply auto[1]
    apply (insert masters)
    apply (simp (no_asm_simp) add: P_1052_def)
    done
qed

definition block2 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block2 s s' \<equiv> EAX s' = -1"

lemma sslBuffer_AppendVariable_1057_ret:
  assumes "P_1057 s"
  shows "(block2 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 1057"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 36,4] = at\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,4] = size\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
    using assms[unfolded P_1057_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  note masters = m0 and m1 and m2 and m3 and m4 and m5 and m6 and m7 and m8 and m9
  note masters = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block2_def)
    apply (simp (no_asm_simp) add: P_ret_def)
    done
qed

lemma sslBuffer_AppendVariable_1042_1089_0:
  assumes "(P_1042 && ! (\<lambda>s. regs s rax \<noteq> 0)) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_1089) (The (run_until_pred (lines {1089, 1094, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 1042"
   and "RAX s = (ucast (s \<turnstile> *[rsp\<^sub>0 - 12,4] :: 32 word) >> unat (\<langle>7,0\<rangle>(ucast size\<^sub>0 << 3 :: 64 word) :: 64 word))"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 36,4] = at\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,4] = size\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "RAX s = 0"
    using assms[unfolded P_1042_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  note masters = m0 and m1 and m2 and m3 and m4 and m5 and m6 and m7 and m8 and m9
  note masters = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: S_def read_sslBuffer'_def)
    apply auto[1]
    apply (insert masters)
    apply (simp (no_asm_simp) add: P_1089_def)
    done
qed

definition block3 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block3 s s' \<equiv> EAX s' = 0"

lemma sslBuffer_AppendVariable_1094_ret:
  assumes "P_1094 s"
  shows "(block3 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 1094"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 36,4] = at\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,4] = size\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
    using assms[unfolded P_1094_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  note masters = m0 and m1 and m2 and m3 and m4 and m5 and m6 and m7 and m8 and m9
  note masters = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block3_def)
    apply (simp (no_asm_simp) add: P_ret_def)
    done
qed

definition abstract_sslBuffer_InsertLength :: "sslBuffer_InsertLength_state \<times> '\<sigma>\<^sub>C sslBuffer_InsertLength_caller_state_scheme \<Rightarrow> sslBuffer_InsertLength_state \<times> '\<sigma>\<^sub>C sslBuffer_InsertLength_caller_state_scheme \<Rightarrow> bool"
  where "abstract_sslBuffer_InsertLength \<equiv> 
          (\<lambda> \<sigma> \<sigma>' . len\<^sub>v (\<L> \<sigma>') = buf_len\<^sub>0 - (at\<^sub>0 + size\<^sub>0)) ;
          IF (\<lambda> \<sigma> . (ucast (len\<^sub>v (\<L> \<sigma>)) >> unat (\<langle>7,0\<rangle>(ucast size\<^sub>0 << 3 :: 64 word) :: 64 word) \<noteq> (0::64 word))) THEN
            call\<^sub>1 abstract_PORT_SetError (\<lambda> _ . 4294959105) ;
            (\<lambda> \<sigma> \<sigma>' . ret'\<^sub>v (\<C> \<sigma>') = -1)
          ELSE
            call abstract_ssl_EncodeUintX ;
            (\<lambda> \<sigma> \<sigma>' . ret'\<^sub>v (\<C> \<sigma>') = 0)            
          FI"

lemma sslBuffer_InsertLength_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {1042,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 1042"])
  apply (simp add: line_simps)
  done

lemma sslBuffer_InsertLength_decompose2:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {1052,1057,ret_address}) ;
          run_until_pred (lines {1057,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 1057"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address,1057}" "line 1052"])
  apply (simp add: line_simps)
  done


lemma sslBuffer_InsertLength_decompose3:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {1089,1094,ret_address}) ;
          run_until_pred (lines {1094,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 1094"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address,1094}" "line 1089"])
  apply (simp add: line_simps)
  done

lemma sslBuffer_InsertLength:
  shows "S ::
         {P_987}
            run_until_pred (line ret_address) \<preceq> abstract_sslBuffer_InsertLength
         {P_ret}"
  apply (subst abstract_sslBuffer_InsertLength_def)
  apply (subst sslBuffer_InsertLength_decompose)
  apply (rule HL_compose[where Q="P_1042"])
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_AppendVariable_987_1042)
  apply (simp add: block1_def S_def)
  apply (rule HL_ITE[where B="\<lambda> s . RAX s \<noteq> 0"])
  apply (simp add: P_1042_def S_def)
  apply (subst sslBuffer_InsertLength_decompose2)
  apply (subst add_skip[of "call\<^sub>1 _ _"])
  apply (subst seq_assoc)
  apply (rule HL_compose[where Q="P_1052"])
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_AppendVariable_1042_1052_not0)
  apply (simp add: skip_def)
  apply (rule HL_compose[where Q="Q0"])
  apply (rule HL_call\<^sub>1_generic[of _ _ _ l0\<^sub>0])
  using S0 apply simp
  using prec0 apply auto[1]
  using hoare0 apply simp
  apply (rule weaken[of _ P_1057])
  using post0 apply simp
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_AppendVariable_1057_ret)
  apply (simp add: block2_def S_def P_ret_def)
  apply (subst add_skip[of "call _"])
  apply (subst seq_assoc)
  apply (subst sslBuffer_InsertLength_decompose3)
  apply (rule HL_compose[where Q="P_1089"])
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_AppendVariable_1042_1089_0)
  apply (simp add: skip_def)
  apply (rule HL_compose[where Q="Q2"])
  apply (rule HL_call_generic[of _ _ _ l2\<^sub>0])
  using S2 apply simp
  using prec2 apply auto[1]
  using hoare2 apply simp
  apply (rule weaken[of _ P_1094])
  using post2 apply simp
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_AppendVariable_1094_ret)
  apply (simp add: S_def block3_def P_ret_def)
  done


end
(* END FUNCTION sslBuffer_InsertLength *)





end
