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

theory SSLRead_ReadNumber
  imports "SSLEncode"
          "../../isabelle/Calls"
begin

(* FUNCTION sslRead_ReadNumber *)


text "The state of the caller of the function."

record sslReadBuffer =
  sslReadBuffer_buf :: "8 word list option"
  sslReadBuffer_len :: "32 word"

record sslReader =
  sslReader_buf :: sslReadBuffer
  sslReader_offset :: "32 word"

record sslRead_ReadNumber_caller_state =
  reader\<^sub>v :: "sslReader option"
  num\<^sub>v :: "64 word option"
  ret'\<^sub>v :: "32 word"

text "The local state."

record sslRead_ReadNumber_state =
  i\<^sub>v :: "32 word"
  number\<^sub>v :: "64 word"


locale sslRead_ReadNumber_context = sslencode_context +
  fixes reader_ptr\<^sub>0 :: "64 word"
    and bytes\<^sub>0 :: "32 word"
    and num\<^sub>0 :: "64 word"
    and buf_size\<^sub>0 :: nat
    and buf_offset\<^sub>0 :: "32 word"
    and buf_ptr\<^sub>0 :: "64 word"
    and num_ptr\<^sub>0 :: "64 word"
    and rsp\<^sub>0 :: "64 word"
    and ret_address :: "64 word"
    and blocks :: "(nat \<times> 64 word \<times> nat) set"
    and \<sigma>\<^sub>C :: '\<sigma>\<^sub>C
    and buf_size_itself :: "'buf_size::len"
  assumes ret_address: "ret_address < 1521 \<or> ret_address > 1752"
    and buf_offset\<^sub>0_bnd: "unat buf_offset\<^sub>0 + 8 < buf_size\<^sub>0 \<and> buf_size\<^sub>0 < 2^32"
    and buf_ptr\<^sub>0_not_null: "buf_ptr\<^sub>0 \<noteq> 0"
    and buf_size\<^sub>0_gt_0: "buf_size\<^sub>0 > 0"
    and buf_size\<^sub>0_le: "buf_size\<^sub>0 * 8 \<le> LENGTH('buf_size)"
    and masters: "master blocks (rsp\<^sub>0, 8) 1"
        "master blocks (rsp\<^sub>0 - 8, 8) 2"
        "master blocks (rsp\<^sub>0 - 16, 8) 3"
        "master blocks (rsp\<^sub>0 - 20, 4) 4"
        "master blocks (rsp\<^sub>0 - 32, 8) 5"
        "master blocks (rsp\<^sub>0 - 36, 4) 6"
        "master blocks (rsp\<^sub>0 - 48, 8) 7"
        "master blocks (reader_ptr\<^sub>0, 8) 100"
        "master blocks (reader_ptr\<^sub>0 + 8, 4) 101"
        "master blocks (reader_ptr\<^sub>0 + 16, 4) 102"
        "master blocks (num_ptr\<^sub>0, 8) 200"
    and m10: "master blocks (buf_ptr\<^sub>0,buf_size\<^sub>0) 300"
begin

definition P_def
  where "P_def rsp_offset rip_offset s \<equiv> 
      seps blocks
    \<and> RSP s = rsp\<^sub>0 + rsp_offset
    \<and> RIP s = boffset + rip_offset
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
declare P_def_def[simp add]

definition P_sslRead_ReadNumber
  where "P_sslRead_ReadNumber rip_offset s \<equiv> 
      P_def (-56) rip_offset s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = reader_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 36,4] = bytes\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 48,8] = num_ptr\<^sub>0
    \<and> s \<turnstile> *[reader_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
declare P_sslRead_ReadNumber_def [simp add]

text "Precondition"

definition P_1521
  where "P_1521 s \<equiv> 
      P_def 0 1521 s
    \<and> RDI s = reader_ptr\<^sub>0
    \<and> ESI s = bytes\<^sub>0
    \<and> RDX s = num_ptr\<^sub>0
    \<and> s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] = buf_offset\<^sub>0
    \<and> s \<turnstile> *[reader_ptr\<^sub>0,8] = buf_ptr\<^sub>0"

definition P_1559
  where "P_1559 s \<equiv> 
      P_sslRead_ReadNumber 1559 s"

definition P_1564
  where "P_1564 s \<equiv> 
      P_sslRead_ReadNumber 1564 s"

definition P_1626
  where "P_1626 s \<equiv> 
      P_sslRead_ReadNumber 1626 s
    \<and> s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] = buf_offset\<^sub>0
    \<and> reader_ptr\<^sub>0 \<noteq> 0
    \<and> num_ptr\<^sub>0 \<noteq> 0"

definition P_1631
  where "P_1631 s \<equiv> 
      P_sslRead_ReadNumber 1631 s
    \<and> s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] = buf_offset\<^sub>0
    \<and> reader_ptr\<^sub>0 \<noteq> 0
    \<and> num_ptr\<^sub>0 \<noteq> 0"

definition P_1707
  where "P_1707 s \<equiv> 
      P_sslRead_ReadNumber 1707 s
    \<and> s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] = buf_offset\<^sub>0
    \<and> bytes\<^sub>0 \<le> 8
    \<and> reader_ptr\<^sub>0 \<noteq> 0
    \<and> num_ptr\<^sub>0 \<noteq> 0"

definition P_1715
  where "P_1715 s \<equiv> 
      P_sslRead_ReadNumber 1715 s
    \<and> s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] = buf_offset\<^sub>0
    \<and> reader_ptr\<^sub>0 \<noteq> 0
    \<and> num_ptr\<^sub>0 \<noteq> 0"

text "Postcondition"

definition P_ret
  where "P_ret s \<equiv>
      RSP s = rsp\<^sub>0 + 8 \<and> 
      RIP s = boffset + ret_address"


text "The simulation relation. Maps concrete states to abstract ones."

definition read_sslReadBuffer :: "state \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> sslReadBuffer"
  where "read_sslReadBuffer s a buf_size = \<lparr>
            sslReadBuffer_buf = (if buf_ptr\<^sub>0 = 0 then None else Some (read_array_8 s buf_ptr\<^sub>0 buf_size)),
            sslReadBuffer_len = s \<turnstile> *[a + 8,4]\<rparr>"

definition read_sslReader :: "state \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow>  sslReader"
  where "read_sslReader s a buf_size = \<lparr>
            sslReader_buf = read_sslReadBuffer s a buf_size,
            sslReader_offset = s \<turnstile> *[a + 16,4]\<rparr>"


definition S :: "state \<Rightarrow> sslRead_ReadNumber_state \<times> sslRead_ReadNumber_caller_state"
  where "S s \<equiv> (\<lparr> i\<^sub>v = s \<turnstile> *[rsp\<^sub>0 - 20,4],
                  number\<^sub>v = s \<turnstile> *[rsp\<^sub>0 - 16,8] \<rparr>, 
                \<lparr> reader\<^sub>v = if reader_ptr\<^sub>0 = 0 then None else Some (read_sslReader s reader_ptr\<^sub>0 buf_size\<^sub>0),
                  num\<^sub>v = if num_ptr\<^sub>0 = 0 then None else Some (s \<turnstile> *[num_ptr\<^sub>0,8]),
                  ret'\<^sub>v = if RIP s = boffset + ret_address then EAX s else undefined
                \<rparr>)"

end

locale sslRead_ReadNumber_context' = sslRead_ReadNumber_context +
  fixes abstract_PORT_SetError :: "32 word \<Rightarrow> 'a \<times> sslRead_ReadNumber_state \<Rightarrow> 'a \<times> sslRead_ReadNumber_state \<Rightarrow> bool"
    and S0 :: "state \<Rightarrow> 'a \<times> sslRead_ReadNumber_state"
    and P0 Q0 l0\<^sub>0 :: "state \<Rightarrow> bool"
  assumes S0: "snd \<circ> S0 = fst \<circ> S"
      and prec0:  "S0:: {P_1559} run_until_pred (l0\<^sub>0 || F) \<preceq> skip {P0}"
      and hoare0: "S0:: {P0} run_until_pred F \<preceq> abstract_PORT_SetError p\<^sub>0 {Q0}"
      and post0:  "\<turnstile> Q0 \<longmapsto> P_1564"
      and prec0':  "S0:: {P_1626} run_until_pred (l0\<^sub>0 || F) \<preceq> skip {P0}"
      and post0':  "\<turnstile> Q0 \<longmapsto> P_1631"
begin


lemma sslRead_ReadNumber_1521_1559:
  assumes "(P_1521 && (\<lambda>s. reader_ptr\<^sub>0 = 0 \<or> num_ptr\<^sub>0 = 0)) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_1559) (The (run_until_pred (lines {1559, 1564, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1521"
   and "RSP s = rsp\<^sub>0"
   and "RDI s = reader_ptr\<^sub>0"
   and "ESI s = bytes\<^sub>0"
   and "RDX s = num_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "reader_ptr\<^sub>0 = 0 \<or> num_ptr\<^sub>0 = 0"
   and "s \<turnstile> *[reader_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
    using assms[unfolded P_1521_def] ret_address
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
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (subst sslRead_ReadNumber_context.S_def)
    using sslRead_ReadNumber_context_axioms apply auto[1]
    apply (subst sslRead_ReadNumber_context.S_def)
    using sslRead_ReadNumber_context_axioms apply auto[1]
    apply (insert masters)
    apply (auto simp add: read_sslReadBuffer_def)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]

    apply (subst sslRead_ReadNumber_context.P_1559_def)
    using sslRead_ReadNumber_context_axioms apply auto[1]
    apply (subst sslRead_ReadNumber_context.P_sslRead_ReadNumber_def)
    using sslRead_ReadNumber_context_axioms apply auto[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]

    apply (rewrite_one_let')+
    apply ((thin_tac \<open>master _ _ _\<close>)+)?
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (subst sslRead_ReadNumber_context.S_def)
    using sslRead_ReadNumber_context_axioms apply auto[1]
    apply (subst sslRead_ReadNumber_context.S_def)
    using sslRead_ReadNumber_context_axioms apply auto[1]
    apply (insert masters m10 buf_size\<^sub>0_gt_0)
    apply (auto simp add: read_sslReadBuffer_def read_sslReader_def)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rule read_array_8_eqI[OF _ _ buf_size\<^sub>0_le])
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rule read_array_8_eqI[OF _ _ buf_size\<^sub>0_le])
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]

    apply (subst sslRead_ReadNumber_context.P_1559_def)
    using sslRead_ReadNumber_context_axioms apply auto[1]
    apply (subst sslRead_ReadNumber_context.P_sslRead_ReadNumber_def)
    using sslRead_ReadNumber_context_axioms apply auto[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    done
qed


definition block1 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block1 s s' \<equiv> EAX s' = -1"

lemma sslRead_ReadNumber_1564_ret:
  assumes "P_1564 s"
  shows "(block1 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1564"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
    using assms[unfolded P_1564_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (simp add: block1_def)
    apply (simp add: P_ret_def)
    done
qed




lemma sslRead_ReadNumber_1521_1626:
  assumes "((P_1521 && !(\<lambda>s. reader_ptr\<^sub>0 = 0 \<or> num_ptr\<^sub>0 = 0)) &&
            (\<lambda> s . s \<turnstile> *[reader_ptr\<^sub>0 + 8,4] < (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] :: 32 word)
                 \<or> bytes\<^sub>0 > (s \<turnstile> *[reader_ptr\<^sub>0 + 8,4]) - (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4])
                 \<or> bytes\<^sub>0 > 8)) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_1626) (The (run_until_pred (lines {1626, 1631,ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1521"
   and "RSP s = rsp\<^sub>0"
   and "RDI s = reader_ptr\<^sub>0"
   and "ESI s = bytes\<^sub>0"
   and "RDX s = num_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "reader_ptr\<^sub>0 \<noteq> 0"
   and "num_ptr\<^sub>0 \<noteq> 0"
   and "s \<turnstile> *[reader_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] = buf_offset\<^sub>0"
   and "s \<turnstile> *[reader_ptr\<^sub>0 + 8,4] < (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] :: 32 word)
         \<or> bytes\<^sub>0 > (s \<turnstile> *[reader_ptr\<^sub>0 + 8,4]) - (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4])
         \<or> bytes\<^sub>0 > 8"
    using assms[unfolded P_1521_def] ret_address
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
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jb *)
    apply (symbolic_execution masters: masters) (* mov *)

    apply (finish_symbolic_execution)
    apply (insert masters m10 buf_size\<^sub>0_gt_0 buf_ptr\<^sub>0_not_null)[1]
    apply (simp (no_asm_simp) add: S_def read_sslReader_def read_sslReadBuffer_def)
    apply (rewrite_one_let')+
    apply auto[1]
    apply auto[1]
    apply (rewrite_one_let')+
    apply auto[1]
    apply auto[1]
    apply (rewrite_one_let')+
    apply auto[1]
    apply (rule read_array_8_eqI[OF _ _ buf_size\<^sub>0_le])
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (rule read_array_8_eqI[OF _ _ buf_size\<^sub>0_le])
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]

    apply (simp (no_asm_simp) add: P_1626_def)
    apply (insert masters)[1]
    apply (rewrite_one_let')+

    apply ((thin_tac \<open>master _ _ _\<close>)+)?
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* sub *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jb *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters m10 buf_size\<^sub>0_gt_0 buf_ptr\<^sub>0_not_null)[1]
    apply (simp (no_asm_simp) add: S_def read_sslReader_def read_sslReadBuffer_def)
    apply (rewrite_one_let')+
    apply auto[1]
    apply auto[1]
    apply (rewrite_one_let')+
    apply auto[1]
    apply auto[1]
    apply (rewrite_one_let')+
    apply auto[1]
    apply (rule read_array_8_eqI[OF _ _ buf_size\<^sub>0_le])
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (rule read_array_8_eqI[OF _ _ buf_size\<^sub>0_le])
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]

    apply (simp (no_asm_simp) add: P_1626_def)
    apply (insert masters)[1]
    apply (rewrite_one_let')+

    apply ((thin_tac \<open>master _ _ _\<close>)+)?
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jbe *)
    apply auto[1]

    apply (rewrite_one_let')+
    apply ((thin_tac \<open>master _ _ _\<close>)+)?
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters m10 buf_size\<^sub>0_gt_0 buf_ptr\<^sub>0_not_null)[1]
    apply (simp (no_asm_simp) add: S_def read_sslReader_def read_sslReadBuffer_def)
    apply (rewrite_one_let')+
    apply (rule read_array_8_eqI[OF _ _ buf_size\<^sub>0_le])
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply auto[1]
    apply (rewrite_one_let')+
    apply auto[1]
    apply auto[1]
    apply (rewrite_one_let')+
    apply (rule read_array_8_eqI[OF _ _ buf_size\<^sub>0_le])
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply auto[1]

    apply (simp (no_asm_simp) add: P_1626_def)
    apply (insert masters)[1]
    apply (rewrite_one_let')+
    apply auto[1]
    done
qed


definition block2 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block2 s s' \<equiv> EAX s' = -1"

lemma sslRead_ReadNumber_1631_ret:
  assumes "P_1631 s"
  shows "(block2 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1631"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"   
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = reader_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 36,4] = bytes\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = num_ptr\<^sub>0"
   and "s \<turnstile> *[reader_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "reader_ptr\<^sub>0 \<noteq> 0"
   and "num_ptr\<^sub>0 \<noteq> 0"
   and "s \<turnstile> *[reader_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
    using assms[unfolded P_1631_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (simp add: block2_def)
    apply (simp add: P_ret_def)
    done
qed



definition block3 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block3 s s' \<equiv> s' \<turnstile> *[rsp\<^sub>0 - 16,8] = (0::64 word) \<and> s' \<turnstile> *[rsp\<^sub>0 - 20,4] = (0::32 word)"

lemma sslRead_ReadNumber_1521_1707:
  assumes "((P_1521 && !(\<lambda>s. reader_ptr\<^sub>0 = 0 \<or> num_ptr\<^sub>0 = 0)) &&
            ! (\<lambda> s . s \<turnstile> *[reader_ptr\<^sub>0 + 8,4] < (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] :: 32 word)
                 \<or> bytes\<^sub>0 > (s \<turnstile> *[reader_ptr\<^sub>0 + 8,4]) - (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4])
                 \<or> bytes\<^sub>0 > 8)) s"
  shows "(block3 s && P_1707) (The (run_until_pred (lines {1707, 1715,ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1521"
   and "RSP s = rsp\<^sub>0"
   and "RDI s = reader_ptr\<^sub>0"
   and "ESI s = bytes\<^sub>0"
   and "RDX s = num_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "reader_ptr\<^sub>0 \<noteq> 0"
   and "num_ptr\<^sub>0 \<noteq> 0"
   and "s \<turnstile> *[reader_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] = buf_offset\<^sub>0"
   and "s \<turnstile> *[reader_ptr\<^sub>0 + 8,4] \<ge> (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] :: 32 word)"
   and "bytes\<^sub>0 \<le> (s \<turnstile> *[reader_ptr\<^sub>0 + 8,4]) - (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4])"
   and "bytes\<^sub>0 \<le> 8"
    using assms[unfolded P_1521_def] ret_address
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
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jb *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* sub *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jb *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jbe *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)[1]
    apply (simp (no_asm_simp) add: block3_def)
    apply (rewrite_one_let')+
    apply auto[1]

    apply (simp (no_asm_simp) add: P_1707_def)
    apply (insert masters)[1]
    apply (rewrite_one_let')+
    apply auto[1]
    done
qed

definition block4 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block4 s s' \<equiv> reader_ptr\<^sub>0 \<noteq> 0 \<and> buf_ptr\<^sub>0 \<noteq> 0 \<and> bytes\<^sub>0 \<le> 8
                      \<and> s' \<turnstile> *[rsp\<^sub>0 - 20,4] = (s \<turnstile> *[rsp\<^sub>0 - 20,4]::32 word) + 1
                      \<and> (s' \<turnstile> *[rsp\<^sub>0 - 16,8] ::64 word) = ((s \<turnstile> *[rsp\<^sub>0 - 16,8]::64 word) << 8) +
                              ucast (s \<turnstile> *[buf_ptr\<^sub>0 + ucast (buf_offset\<^sub>0 + (s \<turnstile> *[rsp\<^sub>0 - 20,4])),1] :: 8word)"

lemma sslRead_ReadNumber_1707_1707:
  assumes "(P_1707 && (\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 20,4] < bytes\<^sub>0)) s"
  shows "(block4 s && P_1707) (The (((\<lambda>s. (=) (step s)) ; run_until_pred (lines {ret_address, 1715, 1707})) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1707"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"   
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = reader_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 36,4] = bytes\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = num_ptr\<^sub>0"
   and "s \<turnstile> *[reader_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[reader_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] = buf_offset\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "reader_ptr\<^sub>0 \<noteq> 0"
   and "num_ptr\<^sub>0 \<noteq> 0"
   and "bytes\<^sub>0 \<le> 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 20,4] < bytes\<^sub>0"
    using assms[unfolded P_1707_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (rewrite_one_step)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jb *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* shl *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block4_def)
    apply (insert masters buf_ptr\<^sub>0_not_null)
    apply (rewrite_one_let')+
    apply auto[1]
    apply (simp (no_asm_simp) add: P_1707_def)
    apply (rewrite_one_let')+
    apply auto[1]
    done 
qed


lemma sslRead_ReadNumber_1707_1715:
  assumes "(P_1707 && ! (\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 20,4] < bytes\<^sub>0)) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_1715) (The (run_until_pred (lines {1715, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1707"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"   
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = reader_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 36,4] = bytes\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = num_ptr\<^sub>0"
   and "s \<turnstile> *[reader_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[reader_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] = buf_offset\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "reader_ptr\<^sub>0 \<noteq> 0"
   and "num_ptr\<^sub>0 \<noteq> 0"
   and "bytes\<^sub>0 \<le> 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 20,4] \<ge> bytes\<^sub>0"
    using assms[unfolded P_1707_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jb *)
    apply (finish_symbolic_execution)
    apply (auto simp add: S_def read_sslReader_def read_sslReadBuffer_def read_array_8_write_flag read_array_8_write_reg)[1]    
    apply (simp add: P_1715_def)
    done
qed


definition block5 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block5 s s' \<equiv> s' \<turnstile> *[reader_ptr\<^sub>0 + 16,4] = (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4]) + bytes\<^sub>0
                     \<and> num_ptr\<^sub>0 \<noteq> 0 \<and> s' \<turnstile> *[num_ptr\<^sub>0,8] = (s \<turnstile> *[rsp\<^sub>0 - 16,8] :: 64 word)
                     \<and> EAX s' = 0"

lemma sslRead_ReadNumber_1715_ret:
  assumes "P_1715 s"
  shows "(block5 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1715"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"   
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = reader_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 36,4] = bytes\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = num_ptr\<^sub>0"
   and "s \<turnstile> *[reader_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[reader_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] = buf_offset\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "reader_ptr\<^sub>0 \<noteq> 0"
   and "num_ptr\<^sub>0 \<noteq> 0"
    using assms[unfolded P_1715_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block5_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply auto[1]
    apply (simp add: P_ret_def)
    done
qed

definition abstract_sslRead_ReadNumber :: "sslRead_ReadNumber_state \<times> '\<sigma>\<^sub>C sslRead_ReadNumber_caller_state_scheme \<Rightarrow> sslRead_ReadNumber_state \<times> '\<sigma>\<^sub>C sslRead_ReadNumber_caller_state_scheme \<Rightarrow> bool"
  where "abstract_sslRead_ReadNumber \<equiv> 
          IF (\<lambda> \<sigma> . reader\<^sub>v (\<C> \<sigma>) = None \<or> num\<^sub>v (\<C> \<sigma>) = None) THEN
            call\<^sub>1 abstract_PORT_SetError (\<lambda> _ . 4294959109) ;
            (\<lambda> \<sigma> \<sigma>' . ret'\<^sub>v (\<C> \<sigma>') = -1)
          ELSE
            IF (\<lambda> \<sigma> . sslReadBuffer_len (sslReader_buf (the (reader\<^sub>v (\<C> \<sigma>)))) < sslReader_offset (the (reader\<^sub>v (\<C> \<sigma>)))
                    \<or> bytes\<^sub>0 > sslReadBuffer_len (sslReader_buf (the (reader\<^sub>v (\<C> \<sigma>)))) - sslReader_offset (the (reader\<^sub>v (\<C> \<sigma>)))
                    \<or> bytes\<^sub>0 > 8) THEN
              call\<^sub>1 abstract_PORT_SetError (\<lambda> _ . 4294959106) ;
              (\<lambda> \<sigma> \<sigma>' . ret'\<^sub>v (\<C> \<sigma>') = -1)
            ELSE
              (\<lambda> \<sigma> \<sigma>' . number\<^sub>v (\<L> \<sigma>') = 0
                      \<and> i\<^sub>v (\<L> \<sigma>') = 0) ;
              WHILE (\<lambda> \<sigma> . i\<^sub>v (\<L> \<sigma>) < bytes\<^sub>0) DO
                (\<lambda> \<sigma> \<sigma>' . number\<^sub>v (\<L> \<sigma>') = (number\<^sub>v (\<L> \<sigma>) << 8) +
                            ucast (the (sslReadBuffer_buf (sslReader_buf (the (reader\<^sub>v (\<C> \<sigma>))))) ! (unat (buf_offset\<^sub>0 + i\<^sub>v (\<L> \<sigma>))))
                        \<and> i\<^sub>v (\<L> \<sigma>') = i\<^sub>v (\<L> \<sigma>) + 1)
              OD ;
              (\<lambda> \<sigma> \<sigma>' . sslReader_offset (the (reader\<^sub>v (\<C> \<sigma>'))) = sslReader_offset (the (reader\<^sub>v (\<C> \<sigma>))) + bytes\<^sub>0
                      \<and> num\<^sub>v (\<C> \<sigma>') = Some (number\<^sub>v (\<L> \<sigma>))
                      \<and> ret'\<^sub>v (\<C> \<sigma>') = 0)
            FI
          FI"

lemma sslRead_ReadNumber_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {1559,1564,ret_address}) ;
          run_until_pred (lines {1564,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 1564"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 1564}" "line 1559"])
  apply (simp add: line_simps)
  done

lemma sslRead_ReadNumber_decompose2:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {1626,1631,ret_address}) ;
          run_until_pred (lines {1631,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 1631"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 1631}" "line 1626"])
  apply (simp add: line_simps)
  done

lemma sslRead_ReadNumber_decompose3:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {1707,1715,ret_address}) ;
          run_until_pred (lines {1715,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 1715"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 1715}" "line 1707"])
  apply (simp add: line_simps)
  done

lemma sslRead_ReadNumber:
  shows "S ::
         {P_1521}
            run_until_pred (line ret_address) \<preceq> abstract_sslRead_ReadNumber
         {P_ret}"
  apply (subst abstract_sslRead_ReadNumber_def)
  apply (rule HL_ITE[where B="\<lambda> s . reader_ptr\<^sub>0 = 0 \<or> num_ptr\<^sub>0 = 0"])
  apply (simp add: S_def)
  apply (subst sslRead_ReadNumber_decompose)
  apply (subst add_skip[of "call\<^sub>1 _ _"])
  apply (subst seq_assoc)
  apply (rule HL_compose[where Q="P_1559"])
  apply (rule HL_equality_intro)
  apply (erule sslRead_ReadNumber_1521_1559)
  apply (simp add: skip_def)
  apply (rule HL_compose[where Q="Q0"])
  apply (rule HL_call\<^sub>1_generic[of _ _ _ l0\<^sub>0])
  using S0 apply simp
  using prec0 apply auto[1]
  using hoare0 apply simp
  apply (rule weaken[of _ P_1564])
  using post0 apply simp
  apply (rule HL_equality_intro)
  apply (erule sslRead_ReadNumber_1564_ret)
  apply (simp add: block1_def S_def P_ret_def)
  apply (rule HL_ITE[where B="\<lambda> s . s \<turnstile> *[reader_ptr\<^sub>0 + 8,4] < (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] :: 32 word)
                                  \<or> bytes\<^sub>0 > (s \<turnstile> *[reader_ptr\<^sub>0 + 8,4]) - (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4])
                                  \<or> bytes\<^sub>0 > 8"])
  apply (auto simp add: pred_logic S_def read_sslReader_def read_sslReadBuffer_def)[1]
  apply (subst sslRead_ReadNumber_decompose2)
  apply (subst add_skip[of "call\<^sub>1 _ _"])
  apply (subst seq_assoc)
  apply (rule HL_compose[where Q="P_1626"])
  apply (rule HL_equality_intro)
  apply (erule sslRead_ReadNumber_1521_1626)
  apply (simp add: skip_def)
  apply (rule HL_compose[where Q="Q0"])
  apply (rule HL_call\<^sub>1_generic[of _ _ _ l0\<^sub>0])
  using S0 apply simp
  using prec0' apply auto[1]
  using hoare0 apply simp
  apply (rule weaken[of _ P_1631])
  using post0' apply simp
  apply (rule HL_equality_intro)
  apply (erule sslRead_ReadNumber_1631_ret)
  apply (simp add: block2_def S_def P_ret_def)
  apply (subst sslRead_ReadNumber_decompose3)
  apply (rule HL_compose[where Q="P_1707"])
  apply (rule HL_equality_intro)
  apply (erule sslRead_ReadNumber_1521_1707)
  apply (simp add: S_def block3_def)
  apply (rule HL_compose[where Q="P_1715"])
  apply (rule HL_while[where B="\<lambda> s . s \<turnstile> *[rsp\<^sub>0 - 20,4] < bytes\<^sub>0" and F'="line 1707"])
  apply (simp add: S_def P_1707_def lines_def line_def)
  using ret_address apply auto[1]
  apply (rule HL_equality_intro_step, simp add: line_simps)
  apply (erule sslRead_ReadNumber_1707_1707)
  apply (simp add: block4_def S_def read_sslReader_def read_sslReadBuffer_def)
  apply (subst nth_read_array_8)
  apply auto[1]  
  subgoal premises prems for s s'
  proof-
    have "s \<turnstile> *[rsp\<^sub>0 - 20,4] < bytes\<^sub>0"
      using prems
      by (auto simp add: pred_logic)
    thus ?thesis
      using prems(4) buf_offset\<^sub>0_bnd
      apply (auto simp add: unat_word_ariths)
      apply (subst mod_less)
      by unat_arith+
  qed
  apply auto[1]
  apply (rule HL_equality_intro)
  apply (erule sslRead_ReadNumber_1707_1715)
  apply (simp add: skip_def)
  apply (rule HL_equality_intro)
  apply (erule sslRead_ReadNumber_1715_ret)
  apply (simp add: block5_def S_def P_ret_def read_sslReader_def P_1715_def)
  done
end

(* END FUNCTION sslRead_ReadNumber *)

end
