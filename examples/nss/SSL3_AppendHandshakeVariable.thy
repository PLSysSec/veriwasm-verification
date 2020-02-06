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

theory SSL3_AppendHandshakeVariable
  imports "SSLEncode"
          "../../isabelle/Calls"
begin

(* FUNCTION ssl3_AppendHandshakeVariable *)


text "The state of the caller of the function."

record sslSocket =
  buf :: "8 word list option"
  space :: "32 word"
  len :: "32 word"

record ssl3_AppendHandshakeVariable_caller_state = 
  sslSocket\<^sub>v :: sslSocket
  src\<^sub>v :: "8 word list option"
  ret'\<^sub>v :: "32 word"

text "The local state."

record ssl3_AppendHandshakeVariable_state =
  rv\<^sub>v :: "32 word"

locale ssl3_AppendHandshakeVariable_context = sslencode_context +
  fixes sslSocket_ptr\<^sub>0 :: "64 word"
    and src_ptr\<^sub>0 :: "64 word"
    and bytes\<^sub>0 :: "32 word"
    and lenSize\<^sub>0 :: "32 word"
    and rsp\<^sub>0 :: "64 word"
    and ret_address :: "64 word"
    and blocks :: "(nat \<times> 64 word \<times> nat) set"
    and \<sigma>\<^sub>C :: '\<sigma>\<^sub>C
  assumes ret_address: "ret_address < 2347 \<or> ret_address > 2430"
    and masters: "master blocks (rsp\<^sub>0, 8) 1"
        "master blocks (rsp\<^sub>0 - 8, 8) 2"
        "master blocks (rsp\<^sub>0 - 12, 4) 3"
        "master blocks (rsp\<^sub>0 - 32, 8) 6"
        "master blocks (rsp\<^sub>0 - 40, 8) 7"
        "master blocks (rsp\<^sub>0 - 44, 4) 8"
        "master blocks (rsp\<^sub>0 - 48, 4) 9"
begin

definition P_def
  where "P_def rsp_offset rip_offset s \<equiv> 
      seps blocks
    \<and> RSP s = rsp\<^sub>0 + rsp_offset
    \<and> RIP s = boffset + rip_offset
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
declare P_def_def[simp add]

definition P_ssl3_AppendHandshakeVariable
  where "P_ssl3_AppendHandshakeVariable rip_offset s \<equiv> 
      P_def (-56) rip_offset s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslSocket_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 40,8] = src_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 44,4] = bytes\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 48,4] = lenSize\<^sub>0"
declare P_ssl3_AppendHandshakeVariable_def [simp add]

text "Precondition"

definition P_2347
  where "P_2347 s \<equiv> 
      P_def 0 2347 s
    \<and> RDI s = sslSocket_ptr\<^sub>0
    \<and> RSI s = src_ptr\<^sub>0
    \<and> EDX s = bytes\<^sub>0
    \<and> ECX s = lenSize\<^sub>0"

definition P_2385
  where "P_2385 s \<equiv> 
      P_ssl3_AppendHandshakeVariable 2385 s"

definition P_2390
  where "P_2390 s \<equiv> 
      P_ssl3_AppendHandshakeVariable 2390 s"

definition P_2423
  where "P_2423 s \<equiv> 
      P_ssl3_AppendHandshakeVariable 2423 s"

definition P_2428
  where "P_2428 s \<equiv> 
      P_ssl3_AppendHandshakeVariable 2428 s"

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

definition S :: "state \<Rightarrow> ssl3_AppendHandshakeVariable_state \<times> ssl3_AppendHandshakeVariable_caller_state"
  where "S s \<equiv> (\<lparr> rv\<^sub>v = if RIP s \<in> {boffset + 2390, boffset + 2428} then EAX s else undefined\<rparr>,
                \<lparr> sslSocket\<^sub>v = read_sslSocket s sslSocket_ptr\<^sub>0,
                  src\<^sub>v = undefined,
                  ret'\<^sub>v = if RIP s = boffset + ret_address then EAX s else undefined
                \<rparr>)"

end

locale ssl3_AppendHandshakeVariable_context' = ssl3_AppendHandshakeVariable_context +
  fixes abstract_ssl3_AppendHandshakeNumber :: "'a \<times> ssl3_AppendHandshakeVariable_state \<Rightarrow> 'a \<times> ssl3_AppendHandshakeVariable_state \<Rightarrow> bool"
    and S0 :: "state \<Rightarrow> 'a \<times> ssl3_AppendHandshakeVariable_state"
    and P0 Q0 l0\<^sub>0 :: "state \<Rightarrow> bool"
  fixes abstract_ssl3_AppendHandshake :: "'b \<times> ssl3_AppendHandshakeVariable_state \<Rightarrow> 'b \<times> ssl3_AppendHandshakeVariable_state \<Rightarrow> bool"
    and S1 :: "state \<Rightarrow> 'b \<times> ssl3_AppendHandshakeVariable_state"
    and P1 Q1 l1\<^sub>0 :: "state \<Rightarrow> bool"
  assumes S0: "snd \<circ> S0 = fst \<circ> S"
      and prec0:  "S0:: {P_2385} run_until_pred (l0\<^sub>0 || F) \<preceq> skip {P0}"
      and hoare0: "S0:: {P0} run_until_pred F \<preceq> ssl3_AppendHandshakeNumber {Q0}"
      and post0:  "\<turnstile> Q0 \<longmapsto> P_2390"
  assumes S1: "snd \<circ> S1 = fst \<circ> S"
      and prec1:  "S1:: {P_2423} run_until_pred (l1\<^sub>0 || F) \<preceq> skip {P1}"
      and hoare1: "S1:: {P1} run_until_pred F \<preceq> abstract_ssl3_AppendHandshake {Q1}"
      and post1:  "\<turnstile> Q1 \<longmapsto> P_2428"
begin


lemma ssl3_AppendHandshakeVariable_2347_2385:
  assumes "P_2347 s"
  shows "((\<lambda> s s' . S s' = S s) s && P_2385) (The (run_until_pred (lines {2385,2390, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 2347"
   and "RSP s = rsp\<^sub>0"
   and "RDI s = sslSocket_ptr\<^sub>0"
   and "RSI s = src_ptr\<^sub>0"
   and "EDX s = bytes\<^sub>0"
   and "ECX s = lenSize\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
    using assms[unfolded P_2347_def] ret_address
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
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: S_def read_sslSocket_def)
    apply auto[1]
    apply (simp (no_asm_simp) add: P_2385_def)         
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    done
qed

definition block1 :: "state \<Rightarrow> state \<Rightarrow> bool"
where "block1 s s' \<equiv> EAX s' = -1"

lemma ssl3_AppendHandshakeVariable_2390_ret:
  assumes "(P_2390 && (\<lambda> s . EAX s \<noteq> 0)) s"
  shows "(block1 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 2390"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,8] = src_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 44,4] = bytes\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,4] = lenSize\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "EAX s \<noteq> 0"
    using assms[unfolded P_2390_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block1_def)
    apply (simp (no_asm_simp) add: P_ret_def)
    done
qed

definition block2 :: "state \<Rightarrow> state \<Rightarrow> bool"
where "block2 s s' \<equiv> RIP s' = boffset + 2423"

lemma ssl3_AppendHandshakeVariable_2390_2423:
  assumes "(P_2390 && ! (\<lambda> s . EAX s \<noteq> 0)) s"
  shows "(block2 s && P_2423) (The (run_until_pred (lines {2423,2428, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 2390"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,8] = src_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 44,4] = bytes\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,4] = lenSize\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "EAX s = 0"
    using assms[unfolded P_2390_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block2_def)
    apply (simp (no_asm_simp) add: P_2423_def)
    apply (rewrite_one_let')+
    apply auto[1]
    done
qed

definition block3 :: "state \<Rightarrow> state \<Rightarrow> bool"
where "block3 s s' \<equiv> EAX s' = EAX s"

lemma ssl3_AppendHandshakeVariable_2428_ret:
  assumes "P_2428 s"
  shows "(block3 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 2428"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,8] = src_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 44,4] = bytes\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,4] = lenSize\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
    using assms[unfolded P_2428_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block3_def)
    apply (simp (no_asm_simp) add: P_ret_def)
    done
qed

definition abstract_ssl3_AppendHandshakeVariable :: "ssl3_AppendHandshakeVariable_state \<times> '\<sigma>\<^sub>C ssl3_AppendHandshakeVariable_caller_state_scheme \<Rightarrow> ssl3_AppendHandshakeVariable_state \<times> '\<sigma>\<^sub>C ssl3_AppendHandshakeVariable_caller_state_scheme \<Rightarrow> bool"
  where "abstract_ssl3_AppendHandshakeVariable \<equiv> 
          call abstract_ssl3_AppendHandshakeNumber;
          IF (\<lambda> \<sigma> . rv\<^sub>v (\<L> \<sigma>) \<noteq> 0) THEN
             (\<lambda> \<sigma> \<sigma>' . ret'\<^sub>v (\<C> \<sigma>') = -1)
          ELSE
            (\<lambda> \<sigma> \<sigma>' . rv\<^sub>v (\<L> \<sigma>') = undefined) ;
            call abstract_ssl3_AppendHandshake;
            (\<lambda> \<sigma> \<sigma>' . ret'\<^sub>v (\<C> \<sigma>') = rv\<^sub>v (\<L> \<sigma>))
          FI"

lemma ssl3_AppendHandshakeVariable_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {2385, 2390, ret_address}) ;
          run_until_pred (lines {2390, ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 2390"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 2390}" "line 2385"])
  apply (simp add: line_simps)
  done

lemma ssl3_AppendHandshakeVariable_decompose2:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {2423, 2428, ret_address}) ;
          run_until_pred (lines {2428, ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 2428"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 2428}" "line 2423"])
  apply (simp add: line_simps)
  done



lemma ssl3_AppendHandshakeVariable:
  shows "S ::
         {P_2347}
            run_until_pred (line ret_address) \<preceq> abstract_ssl3_AppendHandshakeVariable   
         {P_ret}"
  apply (subst abstract_ssl3_AppendHandshakeVariable_def)
  apply (subst ssl3_AppendHandshakeVariable_decompose)
  apply (subst add_skip[of "call _"])
  apply (subst seq_assoc)
  apply (rule HL_compose[where Q="P_2385"])
  apply (rule HL_equality_intro)
  apply (erule ssl3_AppendHandshakeVariable_2347_2385)
  apply (simp add: skip_def)
  apply (rule HL_compose[where Q="P_2390"])
  apply (rule HL_call_generic)
  apply (rule S0)
  apply (rule prec0)
  apply (rule strengthen[OF post0])
  apply (rule hoare0)
  apply (rule HL_ITE[where B="\<lambda> s . EAX s \<noteq> 0"])
  apply (simp add: S_def P_2390_def)  
  apply (rule HL_equality_intro)
  apply (erule ssl3_AppendHandshakeVariable_2390_ret)
  apply (simp add: block1_def S_def P_ret_def)
  apply (subst ssl3_AppendHandshakeVariable_decompose2)
  apply (rule HL_compose[where Q="P_2423"])
  apply (rule HL_equality_intro)
  apply (erule ssl3_AppendHandshakeVariable_2390_2423)
  apply (simp add: block2_def S_def)
  apply (rule HL_compose[where Q="P_2428"])
  apply (rule HL_call_generic)
  apply (rule S1)
  apply (rule prec1)
  apply (rule strengthen[OF post1])
  apply (rule hoare1)
  apply (rule HL_equality_intro)
  apply (erule ssl3_AppendHandshakeVariable_2428_ret)
  apply (simp add: block3_def S_def P_ret_def P_2428_def)
  done


(* END FUNCTION ssl3_AppendHandshakeVariable *)

end
