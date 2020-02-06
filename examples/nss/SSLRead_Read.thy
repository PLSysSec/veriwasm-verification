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

theory SSLRead_Read
  imports "SSLEncode"
          "../../isabelle/Calls"
begin

(* FUNCTION sslRead_Read *)


text "The state of the caller of the function."

record sslReadBuffer =
  sslReadBuffer_buf :: "8 word list option"
  sslReadBuffer_len :: "32 word"

record sslReader =
  sslReader_buf :: sslReadBuffer
  sslReader_offset :: "32 word"

record sslRead_Read_caller_state =
  reader\<^sub>v :: "sslReader option"
  out\<^sub>v :: "sslReadBuffer option"
  ret'\<^sub>v :: "32 word"

text "The local state."

record sslRead_Read_state =
  variableLen\<^sub>v :: sslBuffer


locale sslRead_Read_context = sslencode_context +
  fixes reader_ptr\<^sub>0 :: "64 word"
    and count\<^sub>0 :: "32 word"
    and out_ptr\<^sub>0 :: "64 word"
    and buf_offset\<^sub>0 :: "32 word"
    and buf_ptr\<^sub>0 :: "64 word"
    and buf_ptr\<^sub>1 :: "64 word"
    and buf_size\<^sub>0 :: nat
    and buf_size\<^sub>1 :: nat
    and rsp\<^sub>0 :: "64 word"
    and ret_address :: "64 word"
    and blocks :: "(nat \<times> 64 word \<times> nat) set"
    and \<sigma>\<^sub>C :: '\<sigma>\<^sub>C
    and buf_size_itself :: "'buf_size::len"
  assumes ret_address: "ret_address < 1187 \<or> ret_address > 1357"
    and buf_size\<^sub>0_gt_0: "buf_size\<^sub>0 > 0"
    and buf_size\<^sub>0_gt: "unat buf_offset\<^sub>0 \<le> buf_size\<^sub>0"
    and buf_size\<^sub>0_le: "buf_size\<^sub>0 * 8 \<le> LENGTH('buf_size)"
    and buf_size\<^sub>1: "buf_size\<^sub>1 = buf_size\<^sub>0 - unat buf_offset\<^sub>0"
    and buf_size\<^sub>1_gt_0: "buf_size\<^sub>1 > 0"
    and buf_size\<^sub>1_gt: "unat buf_offset\<^sub>0 \<le> buf_size\<^sub>1"
    and buf_size\<^sub>1_le: "buf_size\<^sub>1 * 8 \<le> LENGTH('buf_size)"
    and m0: "master blocks (rsp\<^sub>0, 8) 1"
    and m1: "master blocks (rsp\<^sub>0 - 8, 8) 2"
    and m2: "master blocks (rsp\<^sub>0 - 16, 8) 3"
    and m3: "master blocks (rsp\<^sub>0 - 20, 4) 4"
    and m4: "master blocks (rsp\<^sub>0 - 32, 8) 5"
    and m5: "master blocks (reader_ptr\<^sub>0, 8) 100"
    and m6: "master blocks (reader_ptr\<^sub>0 + 8, 4) 101"
    and m7: "master blocks (reader_ptr\<^sub>0 + 16, 4) 102"
    and m8: "master blocks (out_ptr\<^sub>0, 8) 200"
    and m9: "master blocks (out_ptr\<^sub>0 + 8, 4) 201"
    and m10: "master blocks (buf_ptr\<^sub>0,buf_size\<^sub>0) 300"
    and m11: "master blocks (buf_ptr\<^sub>1,buf_size\<^sub>1) 400"
begin

definition P_def
  where "P_def rsp_offset rip_offset s \<equiv> 
      seps blocks
    \<and> RSP s = rsp\<^sub>0 + rsp_offset
    \<and> RIP s = boffset + rip_offset
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
declare P_def_def[simp add]

definition P_sslRead_Read
  where "P_sslRead_Read rip_offset s \<equiv> 
      P_def (-40) rip_offset s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] = reader_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 20,4] = count\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = out_ptr\<^sub>0
    \<and> s \<turnstile> *[reader_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[out_ptr\<^sub>0,8] = buf_ptr\<^sub>1"
declare P_sslRead_Read_def [simp add]

text "Precondition"

definition P_1187
  where "P_1187 s \<equiv> 
      P_def 0 1187 s
    \<and> RDI s = reader_ptr\<^sub>0
    \<and> ESI s = count\<^sub>0
    \<and> RDX s = out_ptr\<^sub>0
    \<and> s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] = buf_offset\<^sub>0
    \<and> s \<turnstile> *[reader_ptr\<^sub>0,8] = buf_ptr\<^sub>0
    \<and> s \<turnstile> *[out_ptr\<^sub>0,8] = buf_ptr\<^sub>1"

definition P_1120
  where "P_1120 s \<equiv> 
      P_sslRead_Read 1120 s"

definition P_1225
  where "P_1225 s \<equiv> 
      P_sslRead_Read 1225 s
    \<and> EDI s = 4294959109"

definition P_1230
  where "P_1230 s \<equiv> 
      P_sslRead_Read 1230 s"

definition P_1283
  where "P_1283 s \<equiv> 
      P_sslRead_Read 1283 s"

definition P_1288
  where "P_1288 s \<equiv> 
      P_sslRead_Read 1288 s"

text "Postcondition"

definition P_ret
  where "P_ret s \<equiv>
      RSP s = rsp\<^sub>0 + 8 \<and> 
      RIP s = boffset + ret_address"


text "The simulation relation. Maps concrete states to abstract ones."

definition read_sslReadBuffer :: "state \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> sslReadBuffer"
  where "read_sslReadBuffer s a buf_size = \<lparr>
            sslReadBuffer_buf = if a = 0 then None else Some (read_array_8 s (s \<turnstile> *[a,8]) buf_size),
            sslReadBuffer_len = s \<turnstile> *[a + 8,4]\<rparr>"

definition read_sslReader :: "state \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow>  sslReader"
  where "read_sslReader s a buf_size = \<lparr>
            sslReader_buf = read_sslReadBuffer s a buf_size,
            sslReader_offset = s \<turnstile> *[a + 16,4]\<rparr>"


definition S :: "state \<Rightarrow> sslRead_Read_state \<times> sslRead_Read_caller_state"
  where "S s \<equiv> (\<lparr> variableLen\<^sub>v = undefined \<rparr>, 
                \<lparr> reader\<^sub>v = if reader_ptr\<^sub>0 = 0 then None else Some (read_sslReader s reader_ptr\<^sub>0 buf_size\<^sub>0),
                  out\<^sub>v = if out_ptr\<^sub>0 = 0 then None else Some (read_sslReadBuffer s out_ptr\<^sub>0 buf_size\<^sub>1),
                  ret'\<^sub>v = if RIP s = boffset + ret_address then EAX s else undefined
                \<rparr>)"

end

locale sslRead_Read_context' = sslRead_Read_context +
  fixes abstract_PORT_SetError :: "32 word \<Rightarrow> 'a \<times> sslRead_Read_state \<Rightarrow> 'a \<times> sslRead_Read_state \<Rightarrow> bool"
    and S0 :: "state \<Rightarrow> 'a \<times> sslRead_Read_state"
    and P0 Q0 l0\<^sub>0 :: "state \<Rightarrow> bool"
  assumes S0: "snd \<circ> S0 = fst \<circ> S"
      and prec0:  "S0:: {P_1225} run_until_pred (l0\<^sub>0 || F) \<preceq> skip {P0}"
      and hoare0: "S0:: {P0} run_until_pred F \<preceq> abstract_PORT_SetError p\<^sub>0 {Q0}"
      and post0:  "\<turnstile> Q0 \<longmapsto> P_1230"
  assumes prec0':  "S0:: {P_1283} run_until_pred (l0\<^sub>0 || F) \<preceq> skip {P0}"
      and post0':  "\<turnstile> Q0 \<longmapsto> P_1288"
begin


lemma sslRead_Read_1187_1225:
  assumes "(P_1187 && (\<lambda>s. reader_ptr\<^sub>0 = 0 \<or> out_ptr\<^sub>0 = 0)) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_1225) (The (run_until_pred (lines {1225, 1230, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1187"
   and "RSP s = rsp\<^sub>0"
   and "RDI s = reader_ptr\<^sub>0"
   and "ESI s = count\<^sub>0"
   and "RDX s = out_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "reader_ptr\<^sub>0 = 0 \<or> out_ptr\<^sub>0 = 0"
   and "s \<turnstile> *[reader_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[out_ptr\<^sub>0,8] = buf_ptr\<^sub>1"
    using assms[unfolded P_1187_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  note masters = m0 and m1 and m2 and m3 and m4 and m5 and m6 and m7 and m8 and m9 and m10 and m11
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
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (finish_symbolic_execution)
    apply (subst sslRead_Read_context.S_def)
    using sslRead_Read_context_axioms apply auto[1]
    apply (subst sslRead_Read_context.S_def)
    using sslRead_Read_context_axioms apply auto[1]
    apply (insert masters)
    apply (auto simp add: read_sslReadBuffer_def)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rule read_array_8_eqI[where 'a='c])
    apply (insert buf_size\<^sub>0_gt_0 buf_size\<^sub>1_gt_0 buf_size\<^sub>0_le buf_size\<^sub>1_gt_0)
    apply (rewrite_one_let')+
    apply auto[1]
    apply (auto simp add: simp_rules)[1]
    using buf_size\<^sub>1_le apply auto[1]
    apply (rewrite_one_let')+
    apply auto[1]
    apply (rewrite_one_let')+
    apply auto[1]
    apply (rule read_array_8_eqI[where 'a='c])
    apply (insert buf_size\<^sub>0_gt_0 buf_size\<^sub>1_gt_0 buf_size\<^sub>0_le buf_size\<^sub>1_gt_0)
    apply (rewrite_one_let')+
    apply auto[1]
    apply (auto simp add: simp_rules)[1]
    using buf_size\<^sub>1_le apply auto[1]
    apply (rewrite_one_let')+
    apply auto[1]

    apply (subst sslRead_Read_context.P_1225_def)
    using sslRead_Read_context_axioms apply auto[1]
    apply (subst sslRead_Read_context.P_sslRead_Read_def)
    using sslRead_Read_context_axioms apply auto[1]
    apply (simp add: simp_rules)
    apply (rewrite_one_let')+

    apply ((thin_tac \<open>master _ _ _\<close>)+)?
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (finish_symbolic_execution)

    apply (subst sslRead_Read_context.S_def)
    using sslRead_Read_context_axioms apply auto[1]
    apply (subst sslRead_Read_context.S_def)
    using sslRead_Read_context_axioms apply auto[1]
    apply (insert masters)
    apply (auto simp add: read_sslReadBuffer_def read_sslReader_def)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rule read_array_8_eqI[where 'a='c])
    apply (insert buf_size\<^sub>0_gt_0 buf_size\<^sub>1_gt_0 buf_size\<^sub>0_le buf_size\<^sub>1_gt_0)
    apply (rewrite_one_let')+
    apply auto[1]
    apply (auto simp add: simp_rules)[1]
    using buf_size\<^sub>1_le apply auto[1]
    apply (rewrite_one_let')+
    apply auto[1]
    apply (rewrite_one_let')+
    apply auto[1]
    apply (rewrite_one_let')+
    apply auto[1]
    apply (rule read_array_8_eqI[where 'a='c])
    apply (insert buf_size\<^sub>0_gt_0 buf_size\<^sub>1_gt_0 buf_size\<^sub>0_le buf_size\<^sub>1_gt_0)
    apply (rewrite_one_let')+
    apply auto[1]
    apply (auto simp add: simp_rules)[1]
    using buf_size\<^sub>1_le apply auto[1]
    apply (rewrite_one_let')+
    apply auto[1]
    apply (rewrite_one_let')+
    apply auto[1]

    apply (subst sslRead_Read_context.P_1225_def)
    using sslRead_Read_context_axioms apply auto[1]
    apply (subst sslRead_Read_context.P_sslRead_Read_def)
    using sslRead_Read_context_axioms apply auto[1]
    apply (simp add: simp_rules)
    apply (rewrite_one_let')+
    apply auto[1]
    done
qed


definition block1 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block1 s s' \<equiv> EAX s' = -1"

lemma sslRead_Read_1230_ret:
  assumes "P_1230 s"
  shows "(block1 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1230"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = reader_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 20,4] = count\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = out_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
    using assms[unfolded P_1230_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  note masters = m0 and m1 and m2 and m3 and m4 and m5 and m6 and m7 and m8 and m9 and m10 and m11
  note masters = this

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


lemma sslRead_Read_1187_1283:
  assumes "((P_1187 && !(\<lambda>s. reader_ptr\<^sub>0 = 0 \<or> out_ptr\<^sub>0 = 0)) &&
            (\<lambda> s . s \<turnstile> *[reader_ptr\<^sub>0 + 8,4] < (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] :: 32 word)
                 \<or> count\<^sub>0 > (s \<turnstile> *[reader_ptr\<^sub>0 + 8,4]) - (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4]))) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_1283) (The (run_until_pred (lines {1283,1288, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1187"
   and "RSP s = rsp\<^sub>0"
   and "RDI s = reader_ptr\<^sub>0"
   and "ESI s = count\<^sub>0"
   and "RDX s = out_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "reader_ptr\<^sub>0 \<noteq> 0"
   and "out_ptr\<^sub>0 \<noteq> 0"
   and "s \<turnstile> *[reader_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[out_ptr\<^sub>0,8] = buf_ptr\<^sub>1"
    using assms[unfolded P_1187_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  note masters = m0 and m1 and m2 and m3 and m4 and m5 and m6 and m7 and m8 and m9 and m10 and m11
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
    apply (insert masters)
    apply (simp (no_asm_simp) add: S_def read_sslReader_def read_sslReadBuffer_def)
    apply (rewrite_one_let')+
    apply auto[1]
    apply (rewrite_one_let')+
    apply auto[1]
    apply auto[1]
    apply (rewrite_one_let')+
    apply auto[1]
    apply auto[1]
    apply (rewrite_one_let')+
    apply auto[1]
    apply (rule read_array_8_eqI[where 'a='c])
    apply (insert buf_size\<^sub>0_gt_0)
    apply (rewrite_one_let')+
    apply auto[1]
    apply (auto simp add: simp_rules)[1]
    using buf_size\<^sub>0_le apply auto[1]
    apply (rule read_array_8_eqI[where 'a='c])
    apply (insert buf_size\<^sub>0_gt_0)
    apply (rewrite_one_let')+
    apply auto[1]
    apply (auto simp add: simp_rules)[1]
    using buf_size\<^sub>0_le apply auto[1]
    apply (rewrite_one_let')+
    apply auto[1]
    apply (rule read_array_8_eqI[where 'a='c])
    apply (insert buf_size\<^sub>1_gt_0)
    apply (rewrite_one_let')+
    apply auto[1]
    apply (auto simp add: simp_rules)[1]
    using buf_size\<^sub>1_le apply auto[1]
    apply (rule read_array_8_eqI[where 'a='c])
    apply (insert buf_size\<^sub>1_gt_0)
    apply (rewrite_one_let')+
    apply auto[1]
    apply (auto simp add: simp_rules)[1]
    using buf_size\<^sub>1_le apply auto[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]

    apply (simp (no_asm_simp) add: P_1283_def)
    apply (rewrite_one_let')+

    apply ((thin_tac \<open>master _ _ _\<close>)+)?
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* sub *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jae *)
    using assms
    apply (auto simp add: pred_logic)[1]
    apply (rewrite_one_let' del: add:)+
    apply ((thin_tac \<open>master _ _ _\<close>)+)?
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: S_def read_sslReader_def read_sslReadBuffer_def)
    apply (insert buf_size\<^sub>0_gt_0 buf_size\<^sub>1_gt_0)
    apply (rewrite_one_let' add: read_array_8_eqI[where 'a='c])+
    apply auto[1]
    apply auto[1]
    apply (rewrite_one_let' add: read_array_8_eqI[where 'a='c])+
    apply auto[1]
    apply auto[1]
    apply (rewrite_one_let' add: read_array_8_eqI[where 'a='c])+
    apply auto[1]
    apply (rule read_array_8_eqI[where 'a='c])
    apply (insert buf_size\<^sub>0_gt_0)
    apply (rewrite_one_let')+
    apply auto[1]
    apply (auto simp add: simp_rules)[1]
    using buf_size\<^sub>0_le apply auto[1]
    apply (rule read_array_8_eqI[where 'a='c])
    apply (insert buf_size\<^sub>1_gt_0)
    apply (rewrite_one_let')+
    apply auto[1]
    apply (auto simp add: simp_rules)[1]
    using buf_size\<^sub>0_le apply auto[1]
    apply (rewrite_one_let')+
    apply auto[1]
    apply (rule read_array_8_eqI[where 'a='c])
    apply (insert buf_size\<^sub>1_gt_0)
    apply (rewrite_one_let')+
    apply auto[1]
    apply (auto simp add: simp_rules)[1]
    using buf_size\<^sub>1_le apply auto[1]
    apply (rule read_array_8_eqI[where 'a='c])
    apply (insert buf_size\<^sub>1_gt_0)
    apply (rewrite_one_let')+
    apply auto[1]
    apply (auto simp add: simp_rules)[1]
    using buf_size\<^sub>1_le apply auto[1]
    apply (rewrite_one_let')+
    apply auto[1]

    apply (simp (no_asm_simp) add: P_1283_def)
    apply (rewrite_one_let')+
    apply auto[1]
    done
qed

lemma sslRead_Read_1288_ret:
  assumes "P_1288 s"
  shows "(block1 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1288"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = reader_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 20,4] = count\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = out_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
    using assms[unfolded P_1288_def] ret_address
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
    apply (simp add: block1_def)
    apply (simp add: P_ret_def)
    done
qed


definition block2 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block2 s s' \<equiv>  s' \<turnstile> *[out_ptr\<^sub>0,8] = (s \<turnstile> *[reader_ptr\<^sub>0,8]::64 word) + ucast (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4]::32 word) (* out->buf = SSL_READER_CURRENT(reader)*)
                        \<and> s' \<turnstile> *[out_ptr\<^sub>0 + 8,4] = count\<^sub>0 (* out->len = count *)
                        \<and> s' \<turnstile> *[reader_ptr\<^sub>0 + 16,4] = count\<^sub>0 + (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4]) (* reader->offset += count*)
                        \<and> EAX s' = 0
                        \<and> s' \<turnstile> *[s \<turnstile> *[reader_ptr\<^sub>0,8],buf_size\<^sub>0] = (s \<turnstile> *[s \<turnstile> *[reader_ptr\<^sub>0,8],buf_size\<^sub>0] :: 'c word)
                        \<and> buf_size_itself = (buf_size_itself :: 'c)"

lemma sslRead_Read_1187_ret:
  assumes "((P_1187 && !(\<lambda>s. reader_ptr\<^sub>0 = 0 \<or> out_ptr\<^sub>0 = 0)) &&
            ! (\<lambda> s . s \<turnstile> *[reader_ptr\<^sub>0 + 8,4] < (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] :: 32 word)
                 \<or> count\<^sub>0 > (s \<turnstile> *[reader_ptr\<^sub>0 + 8,4]) - (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4]))) s"
  shows "(block2 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1187"
   and "RSP s = rsp\<^sub>0"
   and "RDI s = reader_ptr\<^sub>0"
   and "ESI s = count\<^sub>0"
   and "RDX s = out_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
   and "s \<turnstile> *[reader_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] = buf_offset\<^sub>0"
   and "reader_ptr\<^sub>0 \<noteq> 0"
   and "out_ptr\<^sub>0 \<noteq> 0"
   and "s \<turnstile> *[reader_ptr\<^sub>0,8] = buf_ptr\<^sub>0"
   and "s \<turnstile> *[out_ptr\<^sub>0,8] = buf_ptr\<^sub>1"
   and "s \<turnstile> *[reader_ptr\<^sub>0 + 8,4] \<ge> (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] :: 32 word)"
   and "count\<^sub>0 \<le> (s \<turnstile> *[reader_ptr\<^sub>0 + 8,4]) - (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4])"
    using assms[unfolded P_1187_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  note masters = m0 and m1 and m2 and m3 and m4 and m5 and m6 and m7 and m8 and m9 and m10 and m11
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
    apply (symbolic_execution masters: masters) (* jae *)
    defer
    apply auto[1]
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
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
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block2_def)
    apply (insert masters buf_size\<^sub>0_gt_0)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (simp add: simp_rules P_ret_def)
    done
qed

definition abstract_sslRead_Read :: "sslRead_Read_state \<times> '\<sigma>\<^sub>C sslRead_Read_caller_state_scheme \<Rightarrow> sslRead_Read_state \<times> '\<sigma>\<^sub>C sslRead_Read_caller_state_scheme \<Rightarrow> bool"
  where "abstract_sslRead_Read \<equiv> 
          IF (\<lambda> \<sigma> . reader\<^sub>v (\<C> \<sigma>) = None \<or> out\<^sub>v (\<C> \<sigma>) = None) THEN
            call\<^sub>1 abstract_PORT_SetError (\<lambda> _ . 4294959109) ;
            (\<lambda> \<sigma> \<sigma>' . ret'\<^sub>v (\<C> \<sigma>') = -1)
          ELSE
            IF (\<lambda> \<sigma> . sslReadBuffer_len (sslReader_buf (the (reader\<^sub>v (\<C> \<sigma>)))) < sslReader_offset (the (reader\<^sub>v (\<C> \<sigma>)))
                    \<or> count\<^sub>0 > sslReadBuffer_len (sslReader_buf (the (reader\<^sub>v (\<C> \<sigma>)))) - sslReader_offset (the (reader\<^sub>v (\<C> \<sigma>)))) THEN
              call\<^sub>1 abstract_PORT_SetError (\<lambda> _ . 4294959106) ;
              (\<lambda> \<sigma> \<sigma>' . ret'\<^sub>v (\<C> \<sigma>') = -1)
            ELSE
              (\<lambda> \<sigma> \<sigma>' . sslReadBuffer_buf (the (out\<^sub>v (\<C> \<sigma>'))) =
                        Some (drop (unat (sslReader_offset (the (reader\<^sub>v (\<C> \<sigma>)))))
                                   (the (sslReadBuffer_buf (sslReader_buf (the (reader\<^sub>v (\<C> \<sigma>)))))))
                      \<and> ret'\<^sub>v (\<C> \<sigma>') = 0)
            FI
          FI"

lemma sslRead_Read_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {1225,1230,ret_address}) ;
          run_until_pred (lines {1230,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 1230"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 1230}" "line 1225"])
  apply (simp add: line_simps)
  done

lemma sslRead_Read_decompose2:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {1283,1288,ret_address}) ;
          run_until_pred (lines {1288,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 1288"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 1288}" "line 1283"])
  apply (simp add: line_simps)
  done


lemma sslRead_Read:
  shows "S ::
         {P_1187}
            run_until_pred (line ret_address) \<preceq> abstract_sslRead_Read
         {P_ret}"
  apply (subst abstract_sslRead_Read_def)
  apply (rule HL_ITE[where B="\<lambda> s . reader_ptr\<^sub>0 = 0 \<or> out_ptr\<^sub>0 = 0"])
  apply (simp add: S_def)
  apply (subst sslRead_Read_decompose)
  apply (subst add_skip[of "call\<^sub>1 _ _"])
  apply (subst seq_assoc)
  apply (rule HL_compose[where Q="P_1225"])
  apply (rule HL_equality_intro)
  apply (erule sslRead_Read_1187_1225)
  apply (simp add: skip_def)
  apply (rule HL_compose[where Q="Q0"])
  apply (rule HL_call\<^sub>1_generic[of _ _ _ l0\<^sub>0])
  using S0 apply simp
  using prec0 apply auto[1]
  using hoare0 apply simp
  apply (rule weaken[of _ P_1230])
  using post0 apply simp
  apply (rule HL_equality_intro)
  apply (erule sslRead_Read_1230_ret)
  apply (simp add: block1_def S_def P_ret_def)
  apply (rule HL_ITE[where B="\<lambda> s . s \<turnstile> *[reader_ptr\<^sub>0 + 8,4] < (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4] :: 32 word)
                                  \<or> count\<^sub>0 > (s \<turnstile> *[reader_ptr\<^sub>0 + 8,4]) - (s \<turnstile> *[reader_ptr\<^sub>0 + 16,4])"])
  apply (auto simp add: pred_logic S_def read_sslReader_def read_sslReadBuffer_def)[1]
  apply (subst sslRead_Read_decompose2)
  apply (subst add_skip[of "call\<^sub>1 _ _"])
  apply (subst seq_assoc)
  apply (rule HL_compose[where Q="P_1283"])
  apply (rule HL_equality_intro)
  apply (erule sslRead_Read_1187_1283)
  apply (simp add: skip_def)
  apply (rule HL_compose[where Q="Q0"])
  apply (rule HL_call\<^sub>1_generic[of _ _ _ l0\<^sub>0])
  using S0 apply simp
  using prec0' apply auto[1]
  using hoare0 apply simp
  apply (rule weaken[of _ P_1288])
  using post0' apply simp
  apply (rule HL_equality_intro)
  apply (erule sslRead_Read_1288_ret)
  apply (simp add: block1_def S_def P_ret_def)
  apply (rule HL_equality_intro)
  apply (erule sslRead_Read_1187_ret)
  apply (rule conjI)

  using buf_size\<^sub>0_gt buf_size\<^sub>0_gt_0 buf_size\<^sub>0_le
  apply (auto simp add: pred_logic block2_def S_def  read_sslReadBuffer_def read_sslReader_def P_1187_def)[1]
  apply (rule drop_read_array_8[where 'x='c])
      apply auto[1]
      apply auto[1]
      using buf_size\<^sub>1
      apply auto[1]
      apply unat_arith
      apply auto[1]
      apply auto[1]
      apply (rule master_block_implies_no_block_overflow)
      using m10
      apply auto[1]
  apply (simp add: block2_def P_ret_def S_def)
  done


end
(* END FUNCTION sslRead_Read *)





end
