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

theory SSL3_AppendHandshakeNumber
  imports "SSLEncode"
          "../../isabelle/Calls"
begin

(* FUNCTION ssl3_AppendHandshakeNumber *)


text "The state of the caller of the function."

record sslSocket =
  buf :: "8 word list option"
  space :: "32 word"
  len :: "32 word"

record ssl3_AppendHandshakeNumber_caller_state = 
  sslSocket\<^sub>v :: sslSocket
  ret'\<^sub>v :: "32 word"

text "The local state."

record ssl3_AppendHandshakeNumber_state =
  b\<^sub>v :: "8 word list"
  rv\<^sub>v :: "32 word"

locale ssl3_AppendHandshakeNumber_context = sslencode_context +
  fixes sslSocket_ptr\<^sub>0 :: "64 word"
    and num\<^sub>0 :: "64 word"
    and lenSize\<^sub>0 :: "32 word"
    and rsp\<^sub>0 :: "64 word"
    and fs\<^sub>0 :: "64 word"
    and ret_address :: "64 word"
    and blocks :: "(nat \<times> 64 word \<times> nat) set"
    and \<sigma>\<^sub>C :: '\<sigma>\<^sub>C
  assumes ret_address: "ret_address < 2247 \<or> ret_address > 2347"
    and masters: "master blocks (rsp\<^sub>0, 8) 1"
        "master blocks (rsp\<^sub>0 - 8, 8) 2"
        "master blocks (rsp\<^sub>0 - 16, 8) 3"
        "master blocks (rsp\<^sub>0 - 24, 8) 4"
        "master blocks (rsp\<^sub>0 - 32, 8) 6"
        "master blocks (rsp\<^sub>0 - 40, 8) 7"
        "master blocks (rsp\<^sub>0 - 44, 4) 8"
        "master blocks (fs\<^sub>0 + 40, 8) 100"
begin

definition P_def
  where "P_def rsp_offset rip_offset s \<equiv> 
      seps blocks
    \<and> RSP s = rsp\<^sub>0 + rsp_offset
    \<and> RIP s = boffset + rip_offset
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
declare P_def_def[simp add]

definition P_ssl3_AppendHandshakeNumber
  where "P_ssl3_AppendHandshakeNumber rip_offsets s \<equiv> 
      P_def (-56) rip_offsets s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslSocket_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 40,8] = num\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 44,4] = lenSize\<^sub>0
    \<and> regs s fs = fs\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] = (s \<turnstile> *[fs\<^sub>0 + 40,8] :: 64 word)"
declare P_ssl3_AppendHandshakeNumber_def [simp add]

text "Precondition"

definition P_2247
  where "P_2247 s \<equiv> 
      P_def 0 2247 s
    \<and> RDI s = sslSocket_ptr\<^sub>0
    \<and> RSI s = num\<^sub>0
    \<and> EDX s = lenSize\<^sub>0
    \<and> regs s fs = fs\<^sub>0"

definition P_2298
  where "P_2298 s \<equiv> 
      P_ssl3_AppendHandshakeNumber 2298 s"

definition P_2303
  where "P_2303 s \<equiv> 
      P_ssl3_AppendHandshakeNumber 2303 s"

definition P_2320
  where "P_2320 s \<equiv> 
      P_ssl3_AppendHandshakeNumber 2320 s"

definition P_2325
  where "P_2325 s \<equiv> 
      P_ssl3_AppendHandshakeNumber 2325 s"

text "Postcondition"

definition P_ret
  where "P_ret s \<equiv>
      RSP s = rsp\<^sub>0 + 8 \<and> 
      RIP s = boffset + ret_address"


text "The simulation relation. Maps concrete states to abstract ones."

definition read_sslSocket :: "state \<Rightarrow> 64 word \<Rightarrow> sslSocket"
  where "read_sslSocket s a = \<lparr>
            buf = undefined,
            space = undefined,
            len = undefined\<rparr>"

definition S :: "state \<Rightarrow> ssl3_AppendHandshakeNumber_state \<times> ssl3_AppendHandshakeNumber_caller_state"
  where "S s \<equiv> (\<lparr> b\<^sub>v = read_array_8 s (rsp\<^sub>0 - 24) 8, 
                  rv\<^sub>v = if RIP s = boffset + 2325 then EAX s else undefined\<rparr>,
                \<lparr> sslSocket\<^sub>v = read_sslSocket s sslSocket_ptr\<^sub>0,
                  ret'\<^sub>v = if RIP s = boffset + ret_address then EAX s else undefined
                \<rparr>)"

end

locale ssl3_AppendHandshakeNumber_context' = ssl3_AppendHandshakeNumber_context +
  fixes abstract_ssl_EncodeUintX :: "64 word \<Rightarrow> 32 word \<Rightarrow> 'a \<times> ssl3_AppendHandshakeNumber_state \<Rightarrow> 'a \<times> ssl3_AppendHandshakeNumber_state \<Rightarrow> bool"
    and S0 :: "state \<Rightarrow> 'a \<times> ssl3_AppendHandshakeNumber_state"
    and P0 Q0 l0\<^sub>0 :: "state \<Rightarrow> bool"
  fixes abstract_ssl3_AppendHandshake :: "32 word \<Rightarrow> 'b \<times> ssl3_AppendHandshakeNumber_state \<Rightarrow> 'b \<times> ssl3_AppendHandshakeNumber_state \<Rightarrow> bool"
    and S1 :: "state \<Rightarrow> 'b \<times> ssl3_AppendHandshakeNumber_state"
    and P1 Q1 l1\<^sub>0 :: "state \<Rightarrow> bool"
  assumes S0: "snd \<circ> S0 = fst \<circ> S"
      and prec0:  "S0:: {P_2298} run_until_pred (l0\<^sub>0 || F) \<preceq> skip {P0}"
      and hoare0: "S0:: {P0} run_until_pred F \<preceq> abstract_ssl_EncodeUintX p0 p1 {Q0}"
      and post0:  "\<turnstile> Q0 \<longmapsto> P_2303"
  assumes S1: "snd \<circ> S1 = fst \<circ> S"
      and prec1:  "S1:: {P_2320} run_until_pred (l1\<^sub>0 || F) \<preceq> skip {P1}"
      and hoare1: "S1:: {P1} run_until_pred F \<preceq> abstract_ssl3_AppendHandshake p3 {Q1}"
      and post1:  "\<turnstile> Q1 \<longmapsto> P_2325"
begin


lemma ssl3_AppendHandshakeNumber_2247_2298:
  assumes "P_2247 s"
  shows "((\<lambda> s s' . S s' = S s) s && P_2298) (The (run_until_pred (lines {2298, 2303, 2320, 2325, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 2247"
   and "RSP s = rsp\<^sub>0"
   and "RDI s = sslSocket_ptr\<^sub>0"
   and "RSI s = num\<^sub>0"
   and "EDX s = lenSize\<^sub>0"
   and "regs s fs = fs\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
    using assms[unfolded P_2247_def] ret_address
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
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* xor *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* lea *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: S_def read_sslSocket_def)
    apply auto[1]
    apply (rule read_array_8_eqI[where 'a=64])
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (rule read_array_8_eqI[where 'a=64])
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (simp (no_asm_simp) add: P_2298_def)         
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    done
qed


lemma ssl3_AppendHandshakeNumber_2303_2320:
  assumes "P_2303 s"
  shows "((\<lambda> s s' . S s' = S s) s && P_2320) (The (run_until_pred (lines {2320, 2325, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 2303"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,8] = num\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 44,4] = lenSize\<^sub>0"
   and "regs s fs = fs\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = (s \<turnstile> *[fs\<^sub>0 + 40,8] :: 64 word)"
    using assms[unfolded P_2303_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* lea *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: S_def read_sslSocket_def read_array_8_write_flag read_array_8_write_reg)
    apply auto[1]
    apply (simp (no_asm_simp) add: P_2320_def)         
    done
qed

definition block1 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block1 s s' \<equiv> EAX s' = EAX s"

lemma ssl3_AppendHandshakeNumber_2325_ret:
  assumes "P_2325 s"
  shows "(block1 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 2325"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,8] = num\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 44,4] = lenSize\<^sub>0"
   and "regs s fs = fs\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = (s \<turnstile> *[fs\<^sub>0 + 40,8] :: 64 word)"
    using assms[unfolded P_2325_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* xor *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block1_def)
    apply (simp (no_asm_simp) add: P_ret_def)         
    done
qed


definition abstract_ssl3_AppendHandshakeNumber :: "ssl3_AppendHandshakeNumber_state \<times> '\<sigma>\<^sub>C ssl3_AppendHandshakeNumber_caller_state_scheme \<Rightarrow> ssl3_AppendHandshakeNumber_state \<times> '\<sigma>\<^sub>C ssl3_AppendHandshakeNumber_caller_state_scheme \<Rightarrow> bool"
  where "abstract_ssl3_AppendHandshakeNumber \<equiv> 
          call\<^sub>2 abstract_ssl_EncodeUintX (\<lambda> _ . num\<^sub>0) (\<lambda> _ . lenSize\<^sub>0);
          call\<^sub>1 abstract_ssl3_AppendHandshake (\<lambda> _ . lenSize\<^sub>0);
          (\<lambda> \<sigma> \<sigma>' . ret'\<^sub>v (\<C> \<sigma>') = rv\<^sub>v (\<L> \<sigma>))"

lemma ssl3_AppendHandshakeNumber_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {2298, 2303, 2320, 2325, ret_address}) ;
          run_until_pred (lines {2303, 2320, 2325, ret_address}) ;
          run_until_pred (lines {2320, 2325, ret_address}) ;
          run_until_pred (lines {2325, ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 2325"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 2325}" "line 2320"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 2320, 2325}" "line 2303"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 2320, 2325, 2303}" "line 2298"])
  apply (simp add: line_simps)
  done


lemma ssl3_AppendHandshakeNumber:
  shows "S ::
         {P_2247}
            run_until_pred (line ret_address) \<preceq> abstract_ssl3_AppendHandshakeNumber   
         {P_ret}"
  apply (subst abstract_ssl3_AppendHandshakeNumber_def)
  apply (subst ssl3_AppendHandshakeNumber_decompose)
  apply (subst add_skip[of "call\<^sub>2 _ _ _"])
  apply (subst seq_assoc)
  apply (rule HL_compose[where Q="P_2298"])
  apply (rule HL_equality_intro)
  apply (erule ssl3_AppendHandshakeNumber_2247_2298)
  apply (simp add: skip_def)
  apply (rule HL_compose[where Q="P_2303"])
  apply (rule HL_call\<^sub>2_generic)
  apply (rule S0)
  apply (rule prec0)
  apply (rule strengthen[OF post0])
  apply (rule hoare0)
  apply (subst add_skip[of "call\<^sub>1 _ _"])
  apply (subst seq_assoc)
  apply (rule HL_compose[where Q="P_2320"])
  apply (rule HL_equality_intro)
  apply (erule ssl3_AppendHandshakeNumber_2303_2320)
  apply (simp add: skip_def)
  apply (rule HL_compose[where Q="P_2325"])
  apply (rule HL_call\<^sub>1_generic)
  apply (rule S1)
  apply (rule prec1)
  apply (rule strengthen[OF post1])
  apply (rule hoare1)
  apply (rule HL_equality_intro)
  apply (erule ssl3_AppendHandshakeNumber_2325_ret)
  apply (simp add: S_def block1_def P_2325_def P_ret_def)  
  done


(* END FUNCTION ssl3_AppendHandshakeNumber *)

end
