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

theory SSLBuffer_Append
  imports "SSLEncode"
          "../../isabelle/Calls"
begin

(* FUNCTION sslBuffer_Append *)


text "The state of the caller of the function."

record sslBuffer_Append_caller_state =
  data\<^sub>v :: "8 word list"
  ret'\<^sub>v :: "32 word"

text "The local state."

type_synonym sslBuffer_Append_state = sslBuffer_Grow_caller_state



locale sslBuffer_Append_context = sslencode_context +
  fixes sslBuffer_ptr\<^sub>0 :: "64 word"
    and buf_ptr\<^sub>0 :: "64 word"
    and buf_len\<^sub>0 :: "32 word"
    and data_ptr\<^sub>0 :: "64 word"
    and len\<^sub>0 :: "32 word"
    and rsp\<^sub>0 :: "64 word"
    and ret_address :: "64 word"
    and memcpy :: "'a ::len itself \<Rightarrow> state \<Rightarrow> state"
    and memcpy_size :: "'a::len itself"
    and blocks :: "(nat \<times> 64 word \<times> nat) set"
    and \<sigma>\<^sub>C :: '\<sigma>\<^sub>C
  assumes ret_address: "ret_address < 309 \<or> ret_address > 433"
    and no_len_overflow: "unat (buf_len\<^sub>0 + len\<^sub>0) = unat buf_len\<^sub>0 + unat len\<^sub>0"
    and len0: "unat len\<^sub>0 > 0"
    and len1: "unat len\<^sub>0 < LENGTH('a) div 8"
    and len2: "unat buf_len\<^sub>0 > 0"
    and len3: "8 * unat buf_len\<^sub>0 \<le> LENGTH('a)"
    and memcpy_funcs[simp]: "funcs ''memcpy'' = Some (memcpy memcpy_size)"
    and memcpy_spec: "si > 0 \<Longrightarrow> LENGTH('a) > unat si div 8 \<Longrightarrow> RDI s = dst \<Longrightarrow> RSI s = src \<Longrightarrow> EDX s = si \<Longrightarrow> memcpy (memcpy_size::'a::len itself) s = s\<lparr>mem := write_blocks [dst \<rhd> rev (\<lbrace>unat si-1,0\<rbrace>(s \<turnstile> *[src,unat si]::'a::len word))] (mem s)\<rparr>"
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
    \<and> master blocks (data_ptr\<^sub>0, unat len\<^sub>0) 200
    \<and> master blocks (buf_ptr\<^sub>0, unat buf_len\<^sub>0) 300
    \<and> master blocks (buf_ptr\<^sub>0 + ucast buf_len\<^sub>0, unat len\<^sub>0) 301
    \<and> RSP s = rsp\<^sub>0 + rsp_offset
    \<and> RIP s = boffset + rip_offset
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address
    \<and> (ret_address < fst ret_address_bounds \<or> ret_address > snd ret_address_bounds)"
declare P_def_def[simp add]

definition P_sslBuffer_Append
  where "P_sslBuffer_Append rsp_offset rip_offset s \<equiv> 
      P_def rsp_offset rip_offset (309,433) s"
declare P_sslBuffer_Append_def [simp add]

text "Precondition"

definition P_309
  where "P_309 s \<equiv> 
      P_sslBuffer_Append 0 309 s
    \<and> RDI s = sslBuffer_ptr\<^sub>0
    \<and> RSI s = data_ptr\<^sub>0
    \<and> EDX s = len\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = len\<^sub>0"

definition P_349
  where "P_349 s \<equiv> 
      P_sslBuffer_Append (-56) 349 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> RDI s = sslBuffer_ptr\<^sub>0
    \<and> ESI s = buf_len\<^sub>0 + len\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 40,8] = data_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 44,4] = len\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = len\<^sub>0"

definition P_354
  where "P_354 s \<equiv> 
      P_sslBuffer_Append (-56) 354 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 40,8] = data_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 44,4] = len\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = len\<^sub>0"

text "Postcondition"

definition P_ret
  where "P_ret s \<equiv>
      RSP s = rsp\<^sub>0 + 8 \<and> 
      RIP s = boffset + ret_address"

definition block1 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block1 s s' \<equiv> True"

text "The simulation relation. Maps concrete states to abstract ones."

definition read_sslBuffer :: "state \<Rightarrow> 64 word \<Rightarrow> sslBuffer"
  where "read_sslBuffer s a = \<lparr>
            buf = if s \<turnstile> *[a,8] = (0::64 word) then None else Some (read_array_8 s (s \<turnstile> *[a,8]) (unat (s \<turnstile> *[a + 8,4] :: 32 word))),
            space = s \<turnstile> *[a + 12,4], 
            fixed = s \<turnstile> *[a + 16,4] \<noteq> (0::32 word),
            len = s \<turnstile> *[a + 8,4]\<rparr>"


definition S :: "state \<Rightarrow> sslBuffer_Append_state \<times> ('\<sigma>\<^sub>C) sslBuffer_Append_caller_state_scheme"
  where "S s \<equiv> if RIP s \<in> {boffset + 309, boffset + 349} then undefined 
                else (\<lparr> sslBuffer\<^sub>v  = read_sslBuffer s sslBuffer_ptr\<^sub>0, 
                  ret\<^sub>v = if RIP s = boffset + 354 then EAX s else undefined
                   \<rparr>, 
                   \<lparr> data\<^sub>v = read_array_8 s data_ptr\<^sub>0 (unat len\<^sub>0),
                     ret'\<^sub>v = if RIP s = boffset + ret_address then EAX s else undefined,
                    \<dots> = \<sigma>\<^sub>C \<rparr>)"

end

locale sslBuffer_Append_context' = sslBuffer_Append_context +
  fixes abstract_sslBuffer_Grow :: "sslBuffer_Grow_state \<times> sslBuffer_Append_state \<Rightarrow> sslBuffer_Grow_state \<times> sslBuffer_Append_state \<Rightarrow> bool"
    and S' :: "state \<Rightarrow> sslBuffer_Grow_state \<times> sslBuffer_Append_state"
    and P Q l\<^sub>0 :: "state \<Rightarrow> bool"
  assumes S': "snd \<circ> S' = fst \<circ> S"
      and prec:  "S':: {P_349} run_until_pred (l\<^sub>0 || F) \<preceq> skip {P}"
      and hoare: "S':: {P} run_until_pred F \<preceq> abstract_sslBuffer_Grow {Q}"
      and post:  "\<turnstile> Q \<longmapsto> P_354"
begin

lemma sslBuffer_Append_309_349:
  assumes "P_309 s"
  shows "((\<lambda> s s' . S s' = S s) s && P_349) (The (run_until_pred (lines {349, 354, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0"
   and "RIP s = boffset + 309"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "RDI s = sslBuffer_ptr\<^sub>0"
   and "RSI s = data_ptr\<^sub>0"
   and "EDX s = len\<^sub>0"
   and "ret_address < 309 \<or> ret_address > 433"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = len\<^sub>0"
    using assms[unfolded P_309_def]
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
   and \<open>master blocks (data_ptr\<^sub>0, unat len\<^sub>0) 200\<close>
   and \<open>master blocks (buf_ptr\<^sub>0, unat buf_len\<^sub>0) 300\<close>
   and \<open>master blocks (buf_ptr\<^sub>0 + ucast buf_len\<^sub>0, unat len\<^sub>0) 301\<close>
    using assms[unfolded P_309_def]
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
    apply (simp (no_asm_simp) add: S_def)[1]
    apply (simp (no_asm_simp) add: P_349_def)[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    done
qed

definition block2 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block2 s s' \<equiv> EAX s' = -1 \<and> RIP s' = boffset + ret_address"

lemma sslBuffer_Append_354_ret_not0:
  assumes "(P_354 && (\<lambda>s. EAX s \<noteq> 0)) s"
  shows "(block2 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 354"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 309 \<or> ret_address > 433"
   and "EAX s \<noteq> 0"
    using assms[unfolded P_354_def]
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
   and \<open>master blocks (data_ptr\<^sub>0, unat len\<^sub>0) 200\<close>
   and \<open>master blocks (buf_ptr\<^sub>0, unat buf_len\<^sub>0) 300\<close>
   and \<open>master blocks (buf_ptr\<^sub>0 + ucast buf_len\<^sub>0, unat len\<^sub>0) 301\<close>
    using assms[unfolded P_354_def]
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


definition block3 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block3 s s' \<equiv> EAX s' = 0 
                        \<and> read_array_8 s' buf_ptr\<^sub>0 (unat buf_len\<^sub>0 + unat len\<^sub>0) = 
                          read_array_8 s buf_ptr\<^sub>0 (unat buf_len\<^sub>0) @ read_array_8 s data_ptr\<^sub>0 (unat len\<^sub>0)
                        \<and> s' \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
                        \<and> s' \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0 + len\<^sub>0"

lemma sslBuffer_Append_354_ret_0:
  assumes "(P_354 && ! (\<lambda>s. EAX s \<noteq> 0)) s"
  shows "(block3 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 354"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 309 \<or> ret_address > 433"
   and "EAX s = 0"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,8] = data_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 44,4] = len\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "unat len\<^sub>0 > 0"
   and "unat len\<^sub>0 < LENGTH('a) div 8"
   and "unat buf_len\<^sub>0 > 0"
   and "8 * unat buf_len\<^sub>0 \<le> LENGTH('a)"
    using assms[unfolded P_354_def] len0 len1 len2 len3
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
   and \<open>master blocks (data_ptr\<^sub>0, unat len\<^sub>0) 200\<close>
   and \<open>master blocks (buf_ptr\<^sub>0, unat buf_len\<^sub>0) 300\<close>
   and \<open>master blocks (buf_ptr\<^sub>0 + ucast buf_len\<^sub>0, unat len\<^sub>0) 301\<close>
    using assms[unfolded P_354_def]
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
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* call memcpy *)
    apply (subst memcpy_spec[where si=len\<^sub>0])
    apply unat_arith
    apply (simp (no_asm_simp) add: simp_rules)
    apply (simp (no_asm_simp) add: simp_rules)
    apply (simp (no_asm_simp) add: simp_rules)
    apply (simp (no_asm_simp) add: simp_rules)
    apply (subst memcpy_spec[where si=len\<^sub>0])
    apply unat_arith
    apply (simp (no_asm_simp) add: simp_rules)
    apply (simp (no_asm_simp) add: simp_rules)
    apply (simp (no_asm_simp) add: simp_rules)
    apply (simp (no_asm_simp) add: simp_rules)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply (simp (no_asm_simp) add: simp_rules)
    apply (thin_tac \<open>master _ _ _\<close>)+
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
    apply (rule conjI)
    apply (rule read_array_8_append[where s=s and si="unat buf_len\<^sub>0" and si'="unat len\<^sub>0" and 'a='a])
    apply (rewrite_one_let')+
    apply (simp (no_asm_simp) add: simp_rules)
    apply (subst read_array_8_from_mem[where 'a='a])
    apply (simp (no_asm_simp) add: simp_rules)
    apply (simp (no_asm_simp) add: simp_rules)
    apply (simp (no_asm_simp) add: simp_rules)
    apply (subst read_array_8_from_mem[where 'a='a])
    apply (simp (no_asm_simp) add: simp_rules)
    apply (simp (no_asm_simp) add: simp_rules)
    apply (simp (no_asm_simp) add: simp_rules)        

    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules Let'_def)[1]
    apply (rewrite_one_let')+
    apply (simp (no_asm_simp) add: simp_rules)
    apply (simp (no_asm_simp) add: simp_rules)
    apply (simp (no_asm_simp) add: simp_rules)
    subgoal proof- show ?thesis
      apply unat_arith
      by auto
      qed
    apply (rewrite_one_let')+
    apply (simp (no_asm_simp) add: simp_rules)
    apply (simp (no_asm_simp) add: P_ret_def)[1]
    done
qed



definition abstract_sslBuffer_Append :: "sslBuffer_Append_state \<times> '\<sigma>\<^sub>C sslBuffer_Append_caller_state_scheme \<Rightarrow> sslBuffer_Append_state \<times> '\<sigma>\<^sub>C sslBuffer_Append_caller_state_scheme \<Rightarrow> bool"
  where "abstract_sslBuffer_Append \<equiv> 
          call abstract_sslBuffer_Grow ;
          IF (\<lambda> \<sigma> . ret\<^sub>v (\<L> \<sigma>) \<noteq> 0) THEN
            (\<lambda> \<sigma> \<sigma>' . ret'\<^sub>v (\<C> \<sigma>') = -1)
          ELSE
            (\<lambda> \<sigma> \<sigma>' . ret'\<^sub>v (\<C> \<sigma>') = 0 
                    \<and> len (sslBuffer\<^sub>v (\<L> \<sigma>')) = buf_len\<^sub>0 + len\<^sub>0
                    \<and> (case buf (sslBuffer\<^sub>v (\<L> \<sigma>)) of
                          None \<Rightarrow> True
                        | Some b \<Rightarrow> buf (sslBuffer\<^sub>v (\<L> \<sigma>')) = Some (b @ (data\<^sub>v (\<C> \<sigma>)))))
          FI"

lemma sslBuffer_Append_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {349,354,ret_address}) ;
          run_until_pred (lines {354,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 354"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 354}" "line 349"])
  apply (simp add: line_simps)
  done

lemma sslBuffer_Append:
  shows "S ::
         {P_309}
            run_until_pred (line ret_address) \<preceq> abstract_sslBuffer_Append
         {P_ret}"
  apply (subst abstract_sslBuffer_Append_def)
  apply (subst sslBuffer_Append_decompose)
  apply (subst add_skip[of "call abstract_sslBuffer_Grow"])
  apply (subst seq_assoc)
  apply (rule HL_compose[where Q="P_349"])
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Append_309_349)
  apply (simp add: skip_def)
  apply (rule HL_compose[where Q=Q])
  apply (rule HL_call_generic[of S' _ _  l\<^sub>0 _ P])
  using S' apply simp
  using prec apply simp
  using hoare apply simp
  apply (rule weaken[of _ P_354])
  using post apply simp
  apply (rule HL_ITE[where B="\<lambda> s . EAX s \<noteq> 0"])
  apply (auto simp add: S_def P_354_def)[1]
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Append_354_ret_not0)
  using ret_address apply (auto simp add: block2_def S_def P_ret_def pred_logic)[1]
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Append_354_ret_0)
  using no_len_overflow
  apply (auto simp add: P_354_def block3_def S_def P_ret_def pred_logic read_sslBuffer_def)[1]
  done

end
(* END FUNCTION sslBuffer_Append *)





end
