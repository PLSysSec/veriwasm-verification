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

theory SSLBuffer_AppendVariable
  imports "SSLEncode"
          "../../isabelle/Calls"
begin

(* FUNCTION sslBuffer_AppendVariable *)


text "The state of the caller of the function."

record sslBuffer_AppendVariable_caller_state =
  ret'\<^sub>v :: "32 word"

text "The local state."

type_synonym sslBuffer_AppendVariable_state = sslBuffer_Grow_caller_state



locale sslBuffer_AppendVariable_context = sslencode_context +
  fixes sslBuffer_ptr\<^sub>0 :: "64 word"
    and buf_ptr\<^sub>0 :: "64 word"
    and buf_len\<^sub>0 :: "32 word"
    and data_ptr\<^sub>0 :: "64 word"
    and len\<^sub>0 :: "32 word"
    and size\<^sub>0 :: "32 word"
    and rsp\<^sub>0 :: "64 word"
    and ret_address :: "64 word"
    and blocks :: "(nat \<times> 64 word \<times> nat) set"
    and \<sigma>\<^sub>C :: '\<sigma>\<^sub>C
  assumes ret_address: "ret_address < 558 \<or> ret_address > 788"
begin


definition P_def
  where "P_def rsp_offset rip_offset ret_address_bounds s \<equiv> 
      seps blocks
    \<and> master blocks (rsp\<^sub>0, 8) 1
    \<and> master blocks (rsp\<^sub>0 - 8, 8) 2
    \<and> master blocks (rsp\<^sub>0 - 16, 8) 3
    \<and> master blocks (rsp\<^sub>0 - 24, 8) 4
    \<and> master blocks (rsp\<^sub>0 - 28, 4) 5
    \<and> master blocks (rsp\<^sub>0 - 32, 4) 6
    \<and> master blocks (sslBuffer_ptr\<^sub>0, 8) 100
    \<and> master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 101
    \<and> master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 102
    \<and> master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 103
    \<and> RSP s = rsp\<^sub>0 + rsp_offset
    \<and> RIP s = boffset + rip_offset
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address
    \<and> (ret_address < fst ret_address_bounds \<or> ret_address > snd ret_address_bounds)"
declare P_def_def[simp add]

definition P_sslBuffer_AppendVariable
  where "P_sslBuffer_AppendVariable rsp_offset rip_offset s \<equiv> 
      P_def rsp_offset rip_offset (558,788) s"
declare P_sslBuffer_AppendVariable_def [simp add]

text "Precondition"


definition P_588
  where "P_588 s \<equiv> 
      P_sslBuffer_AppendVariable 0 558 s
    \<and> RDI s = sslBuffer_ptr\<^sub>0
    \<and> RSI s = data_ptr\<^sub>0
    \<and> EDX s = len\<^sub>0
    \<and> ECX s = size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"

definition P_597
  where "P_597 s \<equiv> 
      P_sslBuffer_AppendVariable (-40) 597 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 24,8] = data_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 28,4] = len\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,4] = size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0
    \<and> RAX s = (ucast len\<^sub>0 >> unat (\<langle>7,0\<rangle>(ucast size\<^sub>0 << 3 :: 64 word) :: 64 word))"

definition P_607
  where "P_607 s \<equiv> 
      P_sslBuffer_AppendVariable (-40) 607 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 24,8] = data_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 28,4] = len\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,4] = size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0
    \<and> RDI s = 4294959105"

definition P_612
  where "P_612 s \<equiv> 
      P_sslBuffer_AppendVariable (-40) 612 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 24,8] = data_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 28,4] = len\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,4] = size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"

definition P_648
  where "P_648 s \<equiv> 
      P_sslBuffer_AppendVariable (-40) 648 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 24,8] = data_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 28,4] = len\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,4] = size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"

definition P_653
  where "P_653 s \<equiv> 
      P_sslBuffer_AppendVariable (-40) 653 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 24,8] = data_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 28,4] = len\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,4] = size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"

definition P_695
  where "P_695 s \<equiv> 
      P_sslBuffer_AppendVariable (-40) 695 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 24,8] = data_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 28,4] = len\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,4] = size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"

definition P_700
  where "P_700 s \<equiv> 
      P_sslBuffer_AppendVariable (-40) 700 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 24,8] = data_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 28,4] = len\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,4] = size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"

definition P_719
  where "P_719 s \<equiv> 
      P_sslBuffer_AppendVariable (-40) 719 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 24,8] = data_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 28,4] = len\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,4] = size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0 + size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"

definition P_757
  where "P_757 s \<equiv> 
      P_sslBuffer_AppendVariable (-40) 757 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 24,8] = data_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 28,4] = len\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,4] = size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0 + size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"

definition P_762
  where "P_762 s \<equiv> 
      P_sslBuffer_AppendVariable (-40) 762 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 24,8] = data_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 28,4] = len\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,4] = size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0 + size\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"


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


definition S :: "state \<Rightarrow> sslBuffer_AppendVariable_state \<times> ('\<sigma>\<^sub>C) sslBuffer_AppendVariable_caller_state_scheme"
  where "S s \<equiv> (\<lparr> sslBuffer\<^sub>v = read_sslBuffer' s sslBuffer_ptr\<^sub>0, 
                  ret\<^sub>v = if RIP s \<in> {boffset + 478, boffset + 653} then EAX s else undefined
                   \<rparr>, 
                   \<lparr> ret'\<^sub>v = if RIP s = boffset + ret_address then EAX s else undefined,
                    \<dots> = \<sigma>\<^sub>C \<rparr>)"

end

locale sslBuffer_AppendVariable_context' = sslBuffer_AppendVariable_context +
  fixes abstract_PORT_SetError :: "32 word \<Rightarrow> 'a \<times> sslBuffer_AppendVariable_state \<Rightarrow> 'a \<times> sslBuffer_AppendVariable_state \<Rightarrow> bool"
    and S0 :: "state \<Rightarrow> 'a \<times> sslBuffer_AppendVariable_state"
    and P0 Q0 l0\<^sub>0 :: "state \<Rightarrow> bool"
  fixes abstract_sslBuffer_Grow :: "sslBuffer_Grow_state \<times> sslBuffer_AppendVariable_state \<Rightarrow> sslBuffer_Grow_state \<times> sslBuffer_AppendVariable_state \<Rightarrow> bool"
    and S1 :: "state \<Rightarrow> sslBuffer_Grow_state \<times> sslBuffer_AppendVariable_state"
    and P1 Q1 l1\<^sub>0 :: "state \<Rightarrow> bool"
  fixes abstract_ssl_EncodeUintX :: "'b \<times> sslBuffer_AppendVariable_state \<Rightarrow> 'b \<times> sslBuffer_AppendVariable_state \<Rightarrow> bool"
    and S2 :: "state \<Rightarrow> 'b \<times> sslBuffer_AppendVariable_state"
    and P2 Q2 l2\<^sub>0 :: "state \<Rightarrow> bool"
  fixes abstract_memcpy :: "'c \<times> sslBuffer_AppendVariable_state \<Rightarrow> 'c \<times> sslBuffer_AppendVariable_state \<Rightarrow> bool"
    and S3 :: "state \<Rightarrow> 'c \<times> sslBuffer_AppendVariable_state"
    and P3 Q3 l3\<^sub>0 :: "state \<Rightarrow> bool"
  assumes S0: "snd \<circ> S0 = fst \<circ> S"
      and prec0:  "S0:: {P_607} run_until_pred (l0\<^sub>0 || F) \<preceq> skip {P0}"
      and hoare0: "S0:: {P0} run_until_pred F \<preceq> abstract_PORT_SetError p\<^sub>0 {Q0}"
      and post0:  "\<turnstile> Q0 \<longmapsto> P_612"
  assumes S1: "snd \<circ> S1 = fst \<circ> S"
      and prec1:  "S1:: {P_648} run_until_pred (l1\<^sub>0 || F) \<preceq> skip {P1}"
      and hoare1: "S1:: {P1} run_until_pred F \<preceq> abstract_sslBuffer_Grow {Q1}"
      and post1:  "\<turnstile> Q1 \<longmapsto> P_653"
  assumes S2: "snd \<circ> S2 = fst \<circ> S"
      and prec2:  "S2:: {P_695} run_until_pred (l2\<^sub>0 || F) \<preceq> skip {P2}"
      and hoare2: "S2:: {P2} run_until_pred F \<preceq> abstract_ssl_EncodeUintX {Q2}"
      and post2:  "\<turnstile> Q2 \<longmapsto> P_700"
  assumes S3: "snd \<circ> S3 = fst \<circ> S"
      and prec3:  "S3:: {P_757} run_until_pred (l3\<^sub>0 || F) \<preceq> skip {P3}"
      and hoare3: "S3:: {P3} run_until_pred F \<preceq> abstract_memcpy {Q3}"
      and post3:  "\<turnstile> Q3 \<longmapsto> P_762"
begin

lemma sslBuffer_AppendVariable_588_597:
  assumes "P_588 s"
  shows "((\<lambda> s s'. S s' = S s) s && P_597) (The (run_until_pred (lines {597,ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0"
   and "RIP s = boffset + 558"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "RDI s = sslBuffer_ptr\<^sub>0"
   and "RSI s = data_ptr\<^sub>0"
   and "EDX s = len\<^sub>0"
   and "ECX s = size\<^sub>0"
   and "ret_address < 558 \<or> ret_address > 788"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
    using assms[unfolded P_588_def]
    by auto
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 24, 8) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 28, 4) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 102\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 103\<close>
    using assms[unfolded P_588_def]
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
    apply (symbolic_execution masters: masters) (* shl *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* shr *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: S_def read_sslBuffer'_def)[1]
    apply (rule conjI)
    apply auto[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply auto[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (simp add: P_597_def)
    apply (rule conjI)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (rule conjI)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    done
qed


lemma sslBuffer_AppendVariable_597_607:
  assumes "(P_597 && (\<lambda>s. regs s rax \<noteq> 0)) s"
  shows "((\<lambda> s s'. S s' = S s) s && P_607) (The (run_until_pred (lines {607,612,ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 597"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 558 \<or> ret_address > 788"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 24,8] = data_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 28,4] = len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,4] = size\<^sub>0"
   and "RAX s \<noteq> 0"
    using assms[unfolded P_597_def]
    by (auto simp add: pred_logic)
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 24, 8) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 28, 4) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 102\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 103\<close>
    using assms[unfolded P_597_def]
    by (auto simp add: pred_logic)
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: S_def read_sslBuffer'_def)[1]
    apply auto[1]
    apply (simp add: P_607_def)
    done
qed

definition block1 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block1 s s' \<equiv> EAX s' = -1"

lemma sslBuffer_AppendVariable_612_ret:
  assumes "P_612 s"
  shows "(block1 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 612"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 558 \<or> ret_address > 788"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 24,8] = data_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 28,4] = len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,4] = size\<^sub>0"
    using assms[unfolded P_612_def]
    by (auto simp add: pred_logic)
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 24, 8) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 28, 4) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 102\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 103\<close>
    using assms[unfolded P_612_def]
    by (auto simp add: pred_logic)
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block1_def)[1]
    apply (simp add: P_ret_def)
    done
qed

(* (s\<lparr>flags := (flags s)
                 (flag_cf := undefined, flag_pf := undefined, flag_sf := undefined, flag_of := undefined,
                  flag_zf := undefined),
                 regs := (regs s)
                   (rdi := sslBuffer_ptr\<^sub>0, rsi := ucast (buf_len\<^sub>0 + (len\<^sub>0 + size\<^sub>0)),
                    rdx := ucast (buf_len\<^sub>0 + (len\<^sub>0 + size\<^sub>0)), rax := sslBuffer_ptr\<^sub>0,
                    rip := boffset + 648)\<rparr>)))*)
lemma sslBuffer_AppendVariable_597_648:
  assumes "(P_597 && ! (\<lambda>s. regs s rax \<noteq> 0)) s"
  shows "((\<lambda> s s'. S s' = S s) s && P_648) (The (run_until_pred (lines {648,653,ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 597"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 558 \<or> ret_address > 788"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 24,8] = data_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 28,4] = len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,4] = size\<^sub>0"
   and "RAX s = 0"
    using assms[unfolded P_597_def]
    by (auto simp add: pred_logic)  
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 24, 8) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 28, 4) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 102\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 103\<close>
    using assms[unfolded P_597_def]
    by (auto simp add: pred_logic)
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: S_def read_sslBuffer'_def)[1]
    apply auto[1]
    apply (simp add: P_648_def)
    done
qed



lemma sslBuffer_AppendVariable_653_ret:
  assumes "(P_653 && (\<lambda>s. EAX s \<noteq> 0)) s"
  shows "(block1 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 653"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 558 \<or> ret_address > 788"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 24,8] = data_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 28,4] = len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,4] = size\<^sub>0"
   and "EAX s \<noteq> 0"
    using assms[unfolded P_653_def]
    by (auto simp add: pred_logic)  
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 24, 8) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 28, 4) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 102\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 103\<close>
    using assms[unfolded P_653_def]
    by (auto simp add: pred_logic)
  note masters = this

  have 1: "\<langle>31,0\<rangle>regs s rax \<noteq> (0::1000 word)"
    apply (subst rewrite_take_bits_is_0_bit32)
    using assms'(14)
    by auto

  show ?thesis
    apply (insert assms' 1)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block1_def)[1]
    apply (simp add: P_ret_def)
    done
qed

lemma sslBuffer_AppendVariable_653_695:
  assumes "(P_653 && ! (\<lambda>s. EAX s \<noteq> 0)) s"
  shows "((\<lambda> s s' . RIP s' = boffset + 695) s && P_695) (The (run_until_pred (lines {695, 700, 719, 762, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 653"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 558 \<or> ret_address > 788"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 24,8] = data_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 28,4] = len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,4] = size\<^sub>0"
   and "EAX s = 0"
    using assms[unfolded P_653_def]
    by (auto simp add: pred_logic)  
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 24, 8) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 28, 4) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 102\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 103\<close>
    using assms[unfolded P_653_def]
    by (auto simp add: pred_logic)
  note masters = this

  have 1: "\<langle>31,0\<rangle>regs s rax = (0::1000 word)"
    apply (subst rewrite_take_bits_is_0_bit32)
    using assms'(14)
    by auto

  show ?thesis
    apply (insert assms' 1)
    apply (symbolic_execution masters: masters) (* test *)
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
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp add: P_695_def)
    done
qed

definition block2 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block2 s s' \<equiv> s' \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = (s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4]) + size\<^sub>0"

lemma sslBuffer_AppendVariable_700_719:
  assumes "P_700 s"
  shows "(block2 s && P_719) (The (run_until_pred (lines {719, 762, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 700"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 558 \<or> ret_address > 788"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 24,8] = data_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 28,4] = len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,4] = size\<^sub>0"
    using assms[unfolded P_700_def]
    by (auto simp add: pred_logic)  
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 24, 8) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 28, 4) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 102\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 103\<close>
    using assms[unfolded P_700_def]
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
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block2_def)[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (simp add: P_719_def)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    done
qed

lemma sslBuffer_AppendVariable_719_757:
  assumes "(P_719 && (\<lambda>_. len\<^sub>0 \<noteq> 0)) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_757) (The (run_until_pred (lines {757, 762, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 719"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 558 \<or> ret_address > 788"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0 + size\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 24,8] = data_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 28,4] = len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,4] = size\<^sub>0"
   and "len\<^sub>0 \<noteq> 0"
    using assms[unfolded P_719_def]
    by (auto simp add: pred_logic)  
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 24, 8) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 28, 4) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 102\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 103\<close>
    using assms[unfolded P_719_def]
    by (auto simp add: pred_logic)
  note masters = this

  show ?thesis
    apply (insert assms')
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
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: S_def read_sslBuffer'_def)[1]
    apply auto[1]
    apply (simp add: P_757_def)
    done
qed


lemma sslBuffer_AppendVariable_719_762:
  assumes "(P_719 && ! (\<lambda>_. len\<^sub>0 \<noteq> 0)) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_762) (The (run_until_pred (lines {762, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 719"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 558 \<or> ret_address > 788"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0 + size\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 24,8] = data_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 28,4] = len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,4] = size\<^sub>0"
   and "len\<^sub>0 = 0"
    using assms[unfolded P_719_def]
    by (auto simp add: pred_logic)  
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 24, 8) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 28, 4) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 102\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 103\<close>
    using assms[unfolded P_719_def]
    by (auto simp add: pred_logic)
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: S_def read_sslBuffer'_def)[1]
    apply auto[1]
    apply (subst sslBuffer_AppendVariable_context.P_762_def[OF sslBuffer_AppendVariable_context_axioms])
    apply (simp add: simp_rules)
    done
qed


definition block3 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block3 s s' \<equiv> s' \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = (s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4]) + len\<^sub>0
                       \<and> EAX s' = 0"

lemma sslBuffer_AppendVariable_762_ret:
  assumes "P_762 s"
  shows "(block3 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 762"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 558 \<or> ret_address > 788"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = size\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = buf_len\<^sub>0 + size\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 24,8] = data_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 28,4] = len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,4] = size\<^sub>0"
    using assms[unfolded P_762_def]
    by (auto simp add: pred_logic)  
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 24, 8) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 28, 4) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 102\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 103\<close>
    using assms[unfolded P_762_def]
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

definition abstract_sslBuffer_AppendVariable :: "sslBuffer_AppendVariable_state \<times> '\<sigma>\<^sub>C sslBuffer_AppendVariable_caller_state_scheme \<Rightarrow> sslBuffer_AppendVariable_state \<times> '\<sigma>\<^sub>C sslBuffer_AppendVariable_caller_state_scheme \<Rightarrow> bool"
  where "abstract_sslBuffer_AppendVariable \<equiv> 
          IF (\<lambda> \<sigma> . (ucast len\<^sub>0 >> unat (\<langle>7,0\<rangle>(ucast size\<^sub>0 << 3 :: 64 word) :: 64 word) \<noteq> (0::64 word))) THEN
            call\<^sub>1 abstract_PORT_SetError (\<lambda> _ . 4294959105) ;
            (\<lambda> \<sigma> \<sigma>' . ret'\<^sub>v (\<C> \<sigma>') = -1)
          ELSE
            call abstract_sslBuffer_Grow ;
            IF (\<lambda> \<sigma> . ret\<^sub>v (\<L> \<sigma>) \<noteq> 0) THEN
              (\<lambda> \<sigma> \<sigma>' . ret'\<^sub>v (\<C> \<sigma>') = -1)
            ELSE
              (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<L> \<sigma>') = undefined) ;
              call abstract_ssl_EncodeUintX ;
              (\<lambda> \<sigma> \<sigma>' . len (sslBuffer\<^sub>v (\<L> \<sigma>')) = len (sslBuffer\<^sub>v (\<L> \<sigma>)) + size\<^sub>0) ;
              IF (\<lambda> _ . len\<^sub>0 \<noteq> 0) THEN
                call abstract_memcpy 
              ELSE
                skip
              FI ;
              (\<lambda> \<sigma> \<sigma>' . len (sslBuffer\<^sub>v (\<L> \<sigma>')) = len (sslBuffer\<^sub>v (\<L> \<sigma>)) + len\<^sub>0
                      \<and> ret'\<^sub>v (\<C> \<sigma>') = 0)
            FI
          FI"

lemma sslBuffer_AppendVariable_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {597,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 597"])
  apply (simp add: line_simps)
  done

lemma sslBuffer_AppendVariable_decompose2:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {607,612,ret_address}) ;
          run_until_pred (lines {612,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 612"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 612}" "line 607"])
  apply (simp add: line_simps)
  done

lemma sslBuffer_AppendVariable_decompose3:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {648,653,ret_address}) ;
          run_until_pred (lines {653,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 653"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 653}" "line 648"])
  apply (simp add: line_simps)
  done

lemma sslBuffer_AppendVariable_decompose4:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {695,700,719,762,ret_address}) ;
          run_until_pred (lines {700,719,762,ret_address}) ;
          run_until_pred (lines {719,762,ret_address}) ;
          run_until_pred (lines {762,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 762"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 762}" "line 719"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 762, 719}" "line 700"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 700, 762, 719}" "line 695"])
  apply (simp add: line_simps)
  done

lemma sslBuffer_AppendVariable_decompose5:
  shows "run_until_pred (lines {762, ret_address}) =
          run_until_pred (lines {757,762,ret_address}) ;
          run_until_pred (lines {762, ret_address})"
  apply (subst compose[of "lines {762, ret_address}" "line 757"])
  apply (simp add: line_simps)
  done


lemma sslBuffer_AppendVariable:
  shows "S ::
         {P_588}
            run_until_pred (line ret_address) \<preceq> abstract_sslBuffer_AppendVariable
         {P_ret}"
  apply (subst abstract_sslBuffer_AppendVariable_def)
  apply (subst sslBuffer_AppendVariable_decompose)
  apply (subst add_skip[of "IF _ THEN _ ELSE _ FI"])
  apply (rule HL_compose[where Q="P_597"])
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_AppendVariable_588_597)
  apply (simp add: skip_def)
  apply (rule HL_ITE[where B="\<lambda> s . RAX s \<noteq> 0"])
  apply (simp add: P_597_def)
  apply (subst sslBuffer_AppendVariable_decompose2)
  apply (subst add_skip[of "call\<^sub>1 _ _"])
  apply (subst seq_assoc)
  apply (rule HL_compose[where Q="P_607"])
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_AppendVariable_597_607)
  apply (simp add: skip_def)
  apply (rule HL_compose[where Q="Q0"])
  apply (rule HL_call\<^sub>1_generic[of _ _ _ l0\<^sub>0])
  using S0 apply simp
  using prec0 apply auto[1]
  using hoare0 apply simp
  apply (rule weaken[of _ P_612])
  using post0 apply simp
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_AppendVariable_612_ret)
  apply (simp add: block1_def S_def P_ret_def)
  apply (subst add_skip[of "call _"])
  apply (subst seq_assoc)
  apply (subst sslBuffer_AppendVariable_decompose3)
  apply (rule HL_compose[where Q="P_648"])
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_AppendVariable_597_648)
  apply (simp add: skip_def)
  apply (rule HL_compose[where Q="Q1"])
  apply (rule HL_call_generic[of _ _ _ l1\<^sub>0])
  using S1 apply simp
  using prec1 apply auto[1]
  using hoare1 apply simp
  apply (rule weaken[of _ P_653])
  using post1 apply simp
  apply (rule HL_ITE[where B="\<lambda> s . EAX s \<noteq> 0"])
  apply (simp add: S_def P_653_def)
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_AppendVariable_653_ret)
  apply (simp add: S_def block1_def P_ret_def)
  apply (subst sslBuffer_AppendVariable_decompose4)
  apply (rule HL_compose[where Q="P_695"])
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_AppendVariable_653_695)
  apply (simp add: P_653_def pred_logic S_def)
  apply (rule HL_compose[where Q=Q2])
  apply (rule HL_call_generic[of _ _ _ l2\<^sub>0])
  using S2 apply simp
  using prec2 apply auto[1]
  using hoare2 apply simp
  apply (rule weaken[of _ P_700])
  using post2 apply simp
  apply (rule HL_compose[where Q=P_719])
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_AppendVariable_700_719)
  apply (simp add: S_def block2_def read_sslBuffer'_def)
  apply (rule HL_compose[where Q=P_762])
  apply (rule HL_ITE[where B="\<lambda>_. len\<^sub>0 \<noteq> 0"])
  apply simp
  apply (subst sslBuffer_AppendVariable_decompose5)
  apply (subst add_skip[of "call _"])
  apply (rule HL_compose[where Q="P_757"])
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_AppendVariable_719_757)
  apply (simp add: skip_def)
  apply (rule HL_call_generic[of _ _ _ l3\<^sub>0])
  using S3 apply simp
  using prec3 apply auto[1]
  apply (rule strengthen[of Q3])
  using post3 apply simp
  using hoare3 apply simp
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_AppendVariable_719_762)
  apply (simp add: skip_def)
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_AppendVariable_762_ret)
  apply (simp add: block3_def S_def read_sslBuffer'_def P_ret_def)
  done


end
(* END FUNCTION sslBuffer_AppendVariable *)





end
