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

theory SSLBuffer_Clear
  imports "SSLEncode"
          "../../isabelle/Calls"
begin

(* FUNCTION sslBuffer_Clear *)


text "The state of the caller of the function."


text "The local state."

record sslBuffer_Clear_state =
  sslBuffer\<^sub>v :: sslBuffer
                  

locale sslBuffer_Clear_context = sslencode_context +
  fixes sslBuffer_ptr\<^sub>0 :: "64 word"
    and buf_ptr\<^sub>0 :: "64 word"
    and buf_fixed\<^sub>0 :: "32 word"
    and buf_len\<^sub>0 :: "32 word"
    and buf_space\<^sub>0 :: "32 word"
    and rsp\<^sub>0 :: "64 word"
    and ret_address :: "64 word"
    and blocks :: "(nat \<times> 64 word \<times> nat) set"
    and \<sigma>\<^sub>C :: '\<sigma>\<^sub>C
  assumes ret_address: "ret_address < 1101 \<or> ret_address > 1187"
    and m0: "master blocks (rsp\<^sub>0, 8) 1"
    and m1: "master blocks (rsp\<^sub>0 - 8, 8) 2"
    and m2: "master blocks (rsp\<^sub>0 - 16, 8) 3"
    and m5: "master blocks (sslBuffer_ptr\<^sub>0, 8) 100"
    and m6: "master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 101"
    and m7: "master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 102"
    and m8: "master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 103"
begin


definition P_def
  where "P_def rsp_offset rip_offset s \<equiv> 
      seps blocks
    \<and> RSP s = rsp\<^sub>0 + rsp_offset
    \<and> RIP s = boffset + rip_offset
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
declare P_def_def[simp add]

definition P_sslBuffer_Clear
  where "P_sslBuffer_Clear rip_offset s \<equiv> 
      P_def (-24) rip_offset s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 16,4] = buf_fixed\<^sub>0"
declare P_sslBuffer_Clear_def [simp add]

text "Precondition"

definition P_1101
  where "P_1101 s \<equiv> 
      P_def 0 1101 s
    \<and> RDI s = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = buf_space\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 16,4] = buf_fixed\<^sub>0"

definition P_1120
  where "P_1120 s \<equiv> 
      P_sslBuffer_Clear 1120 s
    \<and> EAX s = s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 16,4]
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = buf_space\<^sub>0"

definition P_1146
  where "P_1146 s \<equiv> 
      P_sslBuffer_Clear 1146 s
    \<and> buf_ptr\<^sub>0 \<noteq> 0"

definition P_1151
  where "P_1151 s \<equiv> 
      P_sslBuffer_Clear 1151 s
    \<and> buf_ptr\<^sub>0 \<noteq> 0"

definition P_1162
  where "P_1162 s \<equiv> 
      P_sslBuffer_Clear 1162 s"

definition P_1173
  where "P_1173 s \<equiv> 
      P_sslBuffer_Clear 1173 s"


text "Postcondition"

definition P_ret
  where "P_ret s \<equiv>
      RSP s = rsp\<^sub>0 + 8 \<and> 
      RIP s = boffset + ret_address"


text "The simulation relation. Maps concrete states to abstract ones."

definition read_sslBuffer' :: "state \<Rightarrow> 64 word \<Rightarrow> sslBuffer"
  where "read_sslBuffer' s a = \<lparr>
            buf = if s \<turnstile> *[a,8] = (0::64 word) then None else Some undefined,
            space = s \<turnstile> *[a + 12,4], 
            fixed = s \<turnstile> *[a + 16,4] \<noteq> (0::32 word),
            len = s \<turnstile> *[a + 8,4]\<rparr>"


definition S :: "state \<Rightarrow> sslBuffer_Clear_state \<times>  unit"
  where "S s \<equiv> (\<lparr> sslBuffer\<^sub>v = read_sslBuffer' s sslBuffer_ptr\<^sub>0 \<rparr>, ())"

end

locale sslBuffer_Clear_context' = sslBuffer_Clear_context +
  fixes abstract_PORT_Free :: "64 word \<Rightarrow> 'a \<times> sslBuffer_Clear_state \<Rightarrow> 'a \<times> sslBuffer_Clear_state \<Rightarrow> bool"
    and S0 :: "state \<Rightarrow> 'a \<times> sslBuffer_Clear_state"
    and P0 Q0 l0\<^sub>0 :: "state \<Rightarrow> bool"
  assumes S0: "snd \<circ> S0 = fst \<circ> S"
      and prec0:  "S0:: {P_1146} run_until_pred (l0\<^sub>0 || F) \<preceq> skip {P0}"
      and hoare0: "S0:: {P0} run_until_pred F \<preceq> abstract_PORT_Free p\<^sub>0 {Q0}"
      and post0:  "\<turnstile> Q0 \<longmapsto> P_1151"
begin


lemma sslBuffer_Clear_1101_1120:
  assumes "P_1101 s"
  shows "((\<lambda> s s' . S s' = S s) s && P_1120) (The (run_until_pred (lines {1120, 1173, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0"
   and "RIP s = boffset + 1101"
   and "RDI s = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = buf_space\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 16,4] = buf_fixed\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
    using assms[unfolded P_1101_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  note masters = m0 and m1 and m2 and m5 and m6 and m7 and m8
  note masters = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* push *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* sub *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: S_def read_sslBuffer'_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply (simp (no_asm_simp))
    apply (auto simp add: Let'_def simp_rules read_region'_def)[1]
    apply (auto simp add: Let'_def simp_rules read_region'_def)[1]
    apply (simp (no_asm_simp) add: P_1120_def)
    apply (rewrite_one_let')+
    apply (simp)
    done
qed


lemma sslBuffer_Clear_1120_1146:
  assumes "((P_1120 && (\<lambda>s. EAX s = 0)) && (\<lambda>s. buf_ptr\<^sub>0 \<noteq> 0)) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_1146) (The (run_until_pred (lines {1146, 1151, 1162, 1173, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 24"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 1120"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = buf_space\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 16,4] = buf_fixed\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0"
   and "EAX s = 0"
   and "buf_ptr\<^sub>0 \<noteq> 0"
    using assms[unfolded P_1120_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  note masters = m0 and m1 and m2 and m5 and m6 and m7 and m8
  note masters = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: S_def read_sslBuffer'_def)
    apply (simp (no_asm_simp) add: P_1146_def)
    done
qed


definition block1 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block1 s s' \<equiv> s' \<turnstile> *[sslBuffer_ptr\<^sub>0 ,8] = (0::64 word)"

lemma sslBuffer_Clear_1151_1162:
  assumes "P_1151 s"
  shows "(block1 s && P_1162) (The (run_until_pred (lines {1162, 1173, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 24"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 1151"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 16,4] = buf_fixed\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0"
   and "buf_ptr\<^sub>0 \<noteq> 0"
    using assms[unfolded P_1151_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  note masters = m0 and m1 and m2 and m5 and m6 and m7 and m8
  note masters = this

  show ?thesis
    apply (insert assms'(1-7) ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block1_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply simp
    apply (simp (no_asm_simp) add: P_1162_def)
    apply (rewrite_one_let' add: assms'(8))+
    apply simp
    done
qed


lemma sslBuffer_Clear_1120_1162:
  assumes "((P_1120 && (\<lambda>s. EAX s = 0)) && ! (\<lambda>s. buf_ptr\<^sub>0 \<noteq> 0)) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_1162) (The (run_until_pred (lines {1162, 1173, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 24"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 1120"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = buf_space\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 16,4] = buf_fixed\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0"
   and "EAX s = 0"
   and "buf_ptr\<^sub>0 = 0"
    using assms[unfolded P_1120_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  note masters = m0 and m1 and m2 and m5 and m6 and m7 and m8
  note masters = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: S_def read_sslBuffer'_def)
    apply (subst sslBuffer_Clear_context.P_1162_def[OF sslBuffer_Clear_context_axioms])
    apply (subst sslBuffer_Clear_context.P_sslBuffer_Clear_def[OF sslBuffer_Clear_context_axioms])
    apply (simp (no_asm_simp) add: sslBuffer_Clear_context.P_1162_def)
    done
qed

definition block2 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block2 s s' \<equiv> s' \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = (0::32 word)"

lemma sslBuffer_Clear_1162_1173:
  assumes "P_1162 s"
  shows "(block2 s && P_1173) (The (run_until_pred (lines {1173, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 24"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 1162"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 16,4] = buf_fixed\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0"
    using assms[unfolded P_1162_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  note masters = m0 and m1 and m2 and m5 and m6 and m7 and m8
  note masters = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block2_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply simp
    apply (simp (no_asm_simp) add: P_1173_def)
    apply (rewrite_one_let')+
    apply simp
    done
qed



lemma sslBuffer_Clear_1120_1173:
  assumes "(P_1120 && ! (\<lambda>s. EAX s = 0)) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_1173) (The (run_until_pred (lines {1173, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 24"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 1120"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = buf_space\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 16,4] = buf_fixed\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0"
   and "EAX s \<noteq> 0"
    using assms[unfolded P_1120_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  note masters = m0 and m1 and m2 and m5 and m6 and m7 and m8
  note masters = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: S_def read_sslBuffer'_def)
    apply (simp (no_asm_simp) add: P_1173_def)
    done
qed


definition block3 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block3 s s' \<equiv> s' \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = (0::32 word)"

lemma sslBuffer_Clear_1173_ret:
  assumes "P_1173 s"
  shows "(block3 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 24"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 1173"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 16,4] = buf_fixed\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0"
    using assms[unfolded P_1173_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  note masters = m0 and m1 and m2 and m5 and m6 and m7 and m8
  note masters = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* nop *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block3_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply simp
    apply (simp (no_asm_simp) add: P_ret_def)
    done
qed
                                                                                                                            

definition abstract_sslBuffer_Clear :: "sslBuffer_Clear_state \<times> unit \<Rightarrow> sslBuffer_Clear_state \<times> unit \<Rightarrow> bool"
  where "abstract_sslBuffer_Clear \<equiv> 
          skip ;
          IF (\<lambda> \<sigma> . \<not> fixed (sslBuffer\<^sub>v (\<L> \<sigma>))) THEN
            IF (\<lambda> \<sigma> . buf (sslBuffer\<^sub>v (\<L> \<sigma>)) \<noteq> None) THEN
              call\<^sub>1 abstract_PORT_Free (\<lambda> _ . sslBuffer_ptr\<^sub>0) ;
              (\<lambda> \<sigma> \<sigma>' . buf (sslBuffer\<^sub>v (\<L> \<sigma>')) = None)
            ELSE
              skip
            FI ;
            (\<lambda> \<sigma> \<sigma>' . space (sslBuffer\<^sub>v (\<L> \<sigma>')) = 0)
          ELSE
            skip
          FI ;
          (\<lambda> \<sigma> \<sigma>' . len (sslBuffer\<^sub>v (\<L> \<sigma>')) = 0)"

lemma sslBuffer_Clear_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {1120,1173,ret_address}) ;
          run_until_pred (lines {1173,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 1173"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 1173}" "line 1120"])
  apply (simp add: line_simps)
  done

lemma sslBuffer_Clear_decompose2:
  shows "run_until_pred (lines {1173,ret_address}) =
          run_until_pred (lines {1162,1173,ret_address}) ;
          run_until_pred (lines {1173,ret_address})"
  apply (subst compose[of "lines {1173,ret_address}" "line 1162"])
  apply (simp add: line_simps)
  done

lemma sslBuffer_Clear_decompose3:
  shows "run_until_pred (lines {1162,1173,ret_address}) =
          run_until_pred (lines {1146,1151,1162,1173,ret_address}) ;
          run_until_pred (lines {1151,1162,1173,ret_address}) ;
          run_until_pred (lines {1162,1173,ret_address})"
  apply (subst compose[of "lines {1162,1173,ret_address}" "line 1151"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 1162, 1173, 1151}" "line 1146"])
  apply (simp add: line_simps)
  done


lemma sslBuffer_Clear:
  shows "S ::
         {P_1101}
            run_until_pred (line ret_address) \<preceq> abstract_sslBuffer_Clear
         {P_ret}"
  apply (subst abstract_sslBuffer_Clear_def)
  apply (subst sslBuffer_Clear_decompose)
  apply (rule HL_compose[where Q="P_1120"])
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Clear_1101_1120)
  apply (simp add: S_def skip_def)
  apply (rule HL_compose[where Q="P_1173"])
  apply (rule HL_ITE[where B="\<lambda> s . EAX s = 0"])
  apply (simp add: P_1120_def S_def read_sslBuffer'_def)
  apply (subst sslBuffer_Clear_decompose2)
  apply (rule HL_compose[where Q="P_1162"])
  apply (rule HL_ITE[where B="\<lambda> s . buf_ptr\<^sub>0 \<noteq> 0"])
  apply (auto simp add: P_1120_def S_def read_sslBuffer'_def pred_logic)[1]
  apply (subst sslBuffer_Clear_decompose3)
  apply (subst add_skip[of "call\<^sub>1 _ _"])
  apply (subst seq_assoc)
  apply (rule HL_compose[where Q="P_1146"])
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Clear_1120_1146)
  apply (simp add: skip_def)
  apply (rule HL_compose[where Q="Q0"])
  apply (rule HL_call\<^sub>1_generic[of _ _ _ l0\<^sub>0])
  using S0 apply simp
  using prec0 apply auto[1]
  using hoare0 apply simp
  apply (rule weaken[of _ P_1151])
  using post0 apply simp
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Clear_1151_1162)
  apply (simp add: block1_def S_def read_sslBuffer'_def)
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Clear_1120_1162)
  apply (simp add: skip_def)
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Clear_1162_1173)
  apply (simp add: block2_def S_def read_sslBuffer'_def)
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Clear_1120_1173)
  apply (simp add: skip_def)
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Clear_1173_ret)
  apply (simp add: block3_def S_def read_sslBuffer'_def)
  done

end
(* END FUNCTION sslBuffer_Clear *)





end
