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

theory SSL_EncodeUintX
  imports "SSLEncode"
begin

(* FUNCTION ssl_EncodeUintX *)

text "The state of the caller of the function."
record (overloaded) ('a::len) ssl_EncodeUintX_caller_state =
  to\<^sub>v :: "'a word"
  ret\<^sub>v :: "32 word"

text "The local state."

record (overloaded) ('a::len) ssl_EncodeUintX_state =
  PR_htonll_ret\<^sub>v :: "64 word"
  encoded\<^sub>v :: "64 word"
  memcpy_dst\<^sub>v :: "'a word"
  memcpy_src\<^sub>v :: "'a word"

locale ssl_EncodeUintX_context = sslencode_context +
  fixes to\<^sub>0 :: "64 word"
    and value\<^sub>0 :: "64 word"
    and bytes\<^sub>0 :: "32 word"
    and rsp\<^sub>0 :: "64 word"
    and fs\<^sub>0 :: "64 word"
    and ret_address :: "64 word"
    and PR_htonll :: "state \<Rightarrow> state"
    and PR_htonll\<^sub>a :: "64 word \<Rightarrow> 64 word"
    and memcpy :: "state \<Rightarrow> state"
    and memcpy_type :: "'memcpy_size::len itself"
    and \<sigma>\<^sub>C :: '\<sigma>\<^sub>C
assumes [simp]: "funcs ''PR_htonll'' = Some PR_htonll"
    and [simp]: "RDI s = value\<^sub>0 \<Longrightarrow> RAX (PR_htonll s) = PR_htonll\<^sub>a value\<^sub>0"
    and [simp]: "RSP (PR_htonll s) = RSP s"
    and [simp]: "RBP (PR_htonll s) = RBP s"
    and [simp]: "regs (PR_htonll s) fs = regs s fs"
    and [simp]: "PR_htonll s \<turnstile> *[rsp\<^sub>0,8] = (s \<turnstile> *[rsp\<^sub>0,8] :: 64 word)"
    and [simp]: "PR_htonll s \<turnstile> *[rsp\<^sub>0 - 16,8] = (s \<turnstile> *[rsp\<^sub>0 - 16,8] :: 64 word)"
    and [simp]: "PR_htonll s \<turnstile> *[rsp\<^sub>0 - 32,8] = (s \<turnstile> *[rsp\<^sub>0 - 32,8] :: 64 word)"
    and [simp]: "PR_htonll s \<turnstile> *[rsp\<^sub>0 - 44 ,4] = (s \<turnstile> *[rsp\<^sub>0 - 44,4] :: 32 word)"
    and [simp]: "PR_htonll s \<turnstile> *[fs\<^sub>0 + 40,8] = (s \<turnstile> *[fs\<^sub>0 + 40,8] :: 64 word)"
assumes [simp]: "funcs ''memcpy'' = Some memcpy"
    and memcpy_spec: "RDI s = dst \<Longrightarrow> RSI s = src \<Longrightarrow> EDX s = si \<Longrightarrow> (memcpy s \<turnstile> *[dst,unat si] :: 'memcpy_size word) = (s \<turnstile> *[src,unat si])"
    and [simp]: "RSP (memcpy s) = RSP s"
    and [simp]: "RBP (memcpy s) = RBP s"
    and [simp]: "regs (memcpy s) fs = regs s fs"
    and [simp]: "memcpy s \<turnstile> *[rsp\<^sub>0,8] = (s \<turnstile> *[rsp\<^sub>0,8] :: 64 word)"
    and [simp]: "memcpy s \<turnstile> *[rsp\<^sub>0 - 16,8] = (s \<turnstile> *[rsp\<^sub>0 - 16,8] :: 64 word)"
    and [simp]: "memcpy s \<turnstile> *[rsp\<^sub>0 - 44,4] = (s \<turnstile> *[rsp\<^sub>0 - 44,4] :: 32 word)"
    and [simp]: "memcpy s \<turnstile> *[fs\<^sub>0 + 40,8] = (s \<turnstile> *[fs\<^sub>0 + 40,8] :: 64 word)"
begin

definition P_def
  where "P_def blocks rsp_offset rip_offset ret_address_bounds s \<equiv> 
      seps blocks
    \<and> master blocks (rsp\<^sub>0, 8) 1
    \<and> master blocks (rsp\<^sub>0 - 8, 8) 2
    \<and> RSP s = rsp\<^sub>0 + rsp_offset
    \<and> RIP s = boffset + rip_offset
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address
    \<and> (ret_address < fst ret_address_bounds \<or> ret_address > snd ret_address_bounds)"
declare P_def_def[simp add]

definition P_ssl_EncodeUintX
  where "P_ssl_EncodeUintX blocks (a::'a::len itself) rsp_offset rip_offset s \<equiv> 
      P_def blocks rsp_offset rip_offset (0,109) s
    \<and> master blocks (rsp\<^sub>0 - 16, 8) 3
    \<and> master blocks (rsp\<^sub>0 - 24, 8) 4
    \<and> master blocks (rsp\<^sub>0 - 32, 8) 5
    \<and> master blocks (rsp\<^sub>0 - 40, 8) 6
    \<and> master blocks (rsp\<^sub>0 - 44, 4) 7
    \<and> master blocks (fs\<^sub>0 + 40,8) 100
    \<and> regs s fs = fs\<^sub>0
    \<and> 0 < bytes\<^sub>0 \<and> bytes\<^sub>0 \<le> 8
    \<and> 64 \<le> LENGTH('a)"

declare P_ssl_EncodeUintX_def [simp add]

text "Precondition"

definition P_0
  where "P_0 blocks a s \<equiv> 
      P_ssl_EncodeUintX blocks a  0 0 s
    \<and> RDI s = to\<^sub>0
    \<and> RSI s = value\<^sub>0
    \<and> EDX s = bytes\<^sub>0"

definition P_46
  where "P_46 blocks a s \<equiv> 
      P_ssl_EncodeUintX blocks a (-56) 46 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] = (s \<turnstile> *[fs\<^sub>0 + 40,8] :: 64 word)
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = to\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 44,4] = bytes\<^sub>0"

definition P_81
  where "P_81 blocks a s \<equiv> 
      P_ssl_EncodeUintX blocks a (-56) 81 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] = (s \<turnstile> *[fs\<^sub>0 + 40,8] :: 64 word)
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = to\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 44,4] = bytes\<^sub>0
    \<and> RDI s = to\<^sub>0
    \<and> RSI s = rsp\<^sub>0 - (ucast bytes\<^sub>0 + 16)
    \<and> EDX s = bytes\<^sub>0"


text "Postcondition"

definition P_ret
  where "P_ret s \<equiv>
      RSP s = rsp\<^sub>0 + 8 \<and> 
      RIP s = boffset + ret_address"


text "The concrete code for the block. A local variable is incremented,
  an array is updated and the RDI register remains unchanged."
definition block1 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block1 s s' \<equiv> RAX s' = PR_htonll\<^sub>a (RSI s)"

lemma ssl_EncodeUintX_0_46:
  assumes "P_0 blocks (a::'a::len itself) s"
  shows "(block1 s && P_46 blocks a) (The (run_until_pred (lines {46,81,ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0"
   and "RIP s = boffset"
   and "ret_address > 109"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "RDI s = to\<^sub>0"
   and "RSI s = value\<^sub>0"
   and "EDX s = bytes\<^sub>0"
   and "regs s fs = fs\<^sub>0"
   and "0 < bytes\<^sub>0 \<and> bytes\<^sub>0 \<le> 8"
   and "64 \<le> LENGTH('a)"
    using assms[unfolded P_0_def]
    by auto

  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 24, 8) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 40, 8) 6\<close>
   and \<open>master blocks (rsp\<^sub>0 - 44, 4) 7\<close>
   and \<open>master blocks (fs\<^sub>0 + 40,8) 100\<close>
    using assms[unfolded P_0_def]
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
    apply (symbolic_execution masters: masters) (* xor *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* call *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block1_def)[1]
    apply (simp (no_asm_simp) add: P_46_def)[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    done
qed


definition block2 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block2 s s' \<equiv>
          s' \<turnstile> *[rsp\<^sub>0 - 44,4] = bytes\<^sub>0
        \<and> s' \<turnstile> *[rsp\<^sub>0 - 24,8] = RAX s
        \<and> no_block_overflow (rsp\<^sub>0 - 24, 8)"

lemma ssl_EncodeUintX_46_81:
  assumes "P_46 blocks a s"
  shows "(block2 s && P_81 blocks a) (The (run_until_pred (lines {81,ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 46"
   and "ret_address > 109"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "regs s fs = fs\<^sub>0"
   and "0 < bytes\<^sub>0 \<and> bytes\<^sub>0 \<le> 8"
   and "64 \<le> LENGTH('a)"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = to\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 44,4] = bytes\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = (s \<turnstile> *[fs\<^sub>0 + 40,8] :: 64 word)"
    using assms[unfolded P_46_def]
    by auto
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 24, 8) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 40, 8) 6\<close>
   and \<open>master blocks (rsp\<^sub>0 - 44, 4) 7\<close>
   and \<open>master blocks (fs\<^sub>0 + 40,8) 100\<close>
    using assms[unfolded P_46_def]
    by auto
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* sub *)
    apply (symbolic_execution masters: masters) (* lea *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block2_def Let_def field_simps)[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (simp (no_asm_simp) add: P_81_def)[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    done
qed

definition block3 :: "'a ::len itself \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  where "block3 a s s' \<equiv>
            s' \<turnstile> *[to\<^sub>0, unat bytes\<^sub>0] = (s \<turnstile> *[rsp\<^sub>0 - (ucast bytes\<^sub>0 + 16),unat bytes\<^sub>0] :: 'a word)
          \<and> (s' \<turnstile> *[rsp\<^sub>0 - 44,4] :: 32 word) = s \<turnstile> *[rsp\<^sub>0 - 44,4]"

lemma ssl_EncodeUintX_81_ret:
  assumes "P_81 blocks a s"
  shows "(block3 memcpy_type s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 81"
   and "ret_address > 109"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "regs s fs = fs\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = (s \<turnstile> *[fs\<^sub>0 + 40,8] :: 64 word)"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = to\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 44,4] = bytes\<^sub>0"
   and "RDI s = to\<^sub>0"
   and "RSI s = rsp\<^sub>0 - (ucast bytes\<^sub>0 + 16)"
   and "EDX s = bytes\<^sub>0"
    using assms[unfolded P_81_def]
    by auto
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 24, 8) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 40, 8) 6\<close>
   and \<open>master blocks (rsp\<^sub>0 - 44, 4) 7\<close>
   and \<open>master blocks (fs\<^sub>0 + 40,8) 100\<close>
    using assms[unfolded P_81_def]
    by auto
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* call memcpy *)
    apply (symbolic_execution masters: masters) (* nop *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* xor *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block3_def memcpy_spec)
    apply (simp (no_asm_simp) add: P_ret_def)
    done
qed

text "The abstract code"

definition abstract_ssl_EncodeUintX :: "'memcpy_size ssl_EncodeUintX_state \<times> ('memcpy_size,'\<sigma>\<^sub>C) ssl_EncodeUintX_caller_state_scheme \<Rightarrow> 'memcpy_size ssl_EncodeUintX_state \<times> ('memcpy_size,'\<sigma>\<^sub>C) ssl_EncodeUintX_caller_state_scheme \<Rightarrow> bool"
  where "abstract_ssl_EncodeUintX \<equiv> 
           (\<lambda> \<sigma> \<sigma>' . PR_htonll_ret\<^sub>v (\<L> \<sigma>') = PR_htonll\<^sub>a value\<^sub>0) ;
           (\<lambda> \<sigma> \<sigma>' . memcpy_src\<^sub>v (\<L> \<sigma>') = \<langle>63, 64 - unat bytes\<^sub>0 * 8\<rangle> PR_htonll_ret\<^sub>v (\<L> \<sigma>)) ;
           (\<lambda> \<sigma> \<sigma>' . to\<^sub>v (\<C> \<sigma>') = memcpy_src\<^sub>v (\<L> \<sigma>))"

text "The simulation relation. Maps concrete states to abstract ones."

definition S :: "state \<Rightarrow> 'a ssl_EncodeUintX_state \<times> ('a::len,'\<sigma>\<^sub>C) ssl_EncodeUintX_caller_state_scheme"
  where "S s \<equiv> (\<lparr> PR_htonll_ret\<^sub>v = if RIP s = boffset + 46 then RAX s else undefined,
                  encoded\<^sub>v = s \<turnstile> *[RSP s - 24,8],
                  memcpy_dst\<^sub>v = if RIP s = boffset + 81 then s \<turnstile> *[rsp\<^sub>0 - 24, unat (s \<turnstile> *[rsp\<^sub>0 - 44,4] :: 32 word) ] else undefined,
                  memcpy_src\<^sub>v = if RIP s = boffset + 81 then s \<turnstile> *[rsp\<^sub>0 - 24 + (8 - ucast (s \<turnstile> *[rsp\<^sub>0 - 44,4] :: 32 word)), unat (s \<turnstile> *[rsp\<^sub>0 - 44,4] :: 32 word)] else undefined
                   \<rparr>, 
                   \<lparr> to\<^sub>v  = s \<turnstile> *[to\<^sub>0, unat (s \<turnstile> *[rsp\<^sub>0 - 44,4] :: 32 word) ], 
                     ret\<^sub>v = if RIP s = boffset + ret_address then EAX s else undefined,
                    \<dots> = \<sigma>\<^sub>C \<rparr>)"

                       
lemma ssl_EncodeUintX_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {46,81,ret_address}) ;
          run_until_pred (lines {81,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 81"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 81}" "line 46"])
  apply (simp add: line_simps)
  done

lemma ssl_EncodeUintX:
  shows "S ::
         {P_0 blocks memcpy_type}
            run_until_pred (line ret_address) \<preceq> abstract_ssl_EncodeUintX
         {P_ret}"
  apply (subst abstract_ssl_EncodeUintX_def)
  apply (subst ssl_EncodeUintX_decompose)
  apply (rule HL_compose[where Q="P_46 blocks memcpy_type"])
  apply (rule HL_equality_intro)
  apply (erule ssl_EncodeUintX_0_46)
  apply (auto simp add: block1_def S_def P_0_def P_46_def )[1]
  apply (rule HL_compose[where Q="P_81 blocks memcpy_type"])
  apply (rule HL_equality_intro)
  apply (erule ssl_EncodeUintX_46_81)
  apply (auto simp add: S_def block2_def P_81_def P_46_def)[1]
  subgoal premises prems for s s'
  proof-
    have "unat (8 - ucast bytes\<^sub>0 :: 64 word) = 8 - unat bytes\<^sub>0"
      using prems
      apply (auto simp add: unat_sub_if' unat_ucast is_up)
      by unat_arith
    moreover
    have "0 < unat bytes\<^sub>0"
      using prems
      by unat_arith
    moreover
    have "unat bytes\<^sub>0 * 8 + (8 - unat bytes\<^sub>0) * 8 - Suc 0 = 63"
      using prems
      apply (auto simp add: field_simps diff_mult_distrib2 )
      apply (subst add_diff_assoc)
      apply auto
      by unat_arith
    ultimately
    show ?thesis
      using prems dereference_with_offset[of "rsp\<^sub>0 - 24" "unat bytes\<^sub>0" "8 - ucast bytes\<^sub>0" s', where 'a='memcpy_size and 'b=64]
      by (auto simp add: field_simps diff_mult_distrib2)
  qed
  apply (rule HL_equality_intro)
  apply (erule ssl_EncodeUintX_81_ret)
  apply (auto simp add: S_def P_81_def block3_def field_simps)[1]
  done

end
(* END FUNCTION ssl_EncodeUintX *)





end
