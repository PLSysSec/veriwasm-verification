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

theory SSLRead_ReadVariable
  imports "SSLEncode"
          "../../isabelle/Calls"
begin

(* FUNCTION sslRead_ReadVariable *)


text "The state of the caller of the function."

record sslReadBuffer =
  sslReadBuffer_buf :: "8 word list option"
  sslReadBuffer_len :: "32 word"

record sslReader =
  sslReader_buf :: sslReadBuffer
  sslReader_offset :: "32 word"

record sslRead_caller =
  reader\<^sub>v :: "sslReader option"
  out\<^sub>v :: "sslReadBuffer option"
  rv\<^sub>v :: "32 word"

type_synonym sslRead_ReadVariable_caller_state = sslRead_caller

text "The local state."

record sslRead_ReadVariable_state = sslRead_caller +
  variableLen\<^sub>v :: "64 word"



locale sslRead_ReadVariable_context = sslencode_context +
  fixes reader_ptr\<^sub>0 :: "64 word"
    and sizeLen\<^sub>0 :: "32 word"
    and out_ptr\<^sub>0 :: "64 word"
    and buf_size\<^sub>0 :: nat
    and buf_size\<^sub>1 :: nat
    and fs\<^sub>0 :: "64 word"
    and rsp\<^sub>0 :: "64 word"
    and ret_address :: "64 word"
    and blocks :: "(nat \<times> 64 word \<times> nat) set"
    and \<sigma>\<^sub>C :: '\<sigma>\<^sub>C
  assumes ret_address: "ret_address < 1357 \<or> ret_address > 1521"
    and out_ptr\<^sub>0_not_null: "out_ptr\<^sub>0 \<noteq> 0"
    and masters:
          "master blocks (rsp\<^sub>0, 8) 1"
          "master blocks (rsp\<^sub>0 - 8, 8) 2"
          "master blocks (rsp\<^sub>0 - 16, 8) 3"
          "master blocks (rsp\<^sub>0 - 24, 8) 4"
          "master blocks (rsp\<^sub>0 - 28, 4) 5"
          "master blocks (rsp\<^sub>0 - 48, 8) 6"
          "master blocks (rsp\<^sub>0 - 52, 4) 7"
          "master blocks (rsp\<^sub>0 - 64, 8) 8"
          "master blocks (reader_ptr\<^sub>0, 8) 100"
          "master blocks (reader_ptr\<^sub>0 + 8, 4) 101"
          "master blocks (reader_ptr\<^sub>0 + 16, 4) 102"
          "master blocks (out_ptr\<^sub>0, 8) 200"
          "master blocks (out_ptr\<^sub>0 + 8, 4) 201"  
          "master blocks (fs\<^sub>0 + 40, 8) 300"  
begin

definition P_def
  where "P_def rsp_offset rip_offset s \<equiv> 
      seps blocks
    \<and> RSP s = rsp\<^sub>0 + rsp_offset
    \<and> RIP s = boffset + rip_offset
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
declare P_def_def[simp add]

definition P_sslRead_ReadVariable
  where "P_sslRead_ReadVariable rip_offset s \<equiv> 
      P_def (-72) rip_offset s
    \<and> regs s fs = fs\<^sub>0
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 48,8] = reader_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 52,4] = sizeLen\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 64,8] = out_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] = (s \<turnstile> *[fs\<^sub>0 + 40,8] :: 64 word)"
declare P_sslRead_ReadVariable_def [simp add]

text "Precondition"

definition P_1357
  where "P_1357 s \<equiv> 
      P_def 0 1357 s
    \<and> regs s fs = fs\<^sub>0
    \<and> RDI s = reader_ptr\<^sub>0
    \<and> ESI s = sizeLen\<^sub>0
    \<and> RDX s = out_ptr\<^sub>0"

definition P_1415
  where "P_1415 s \<equiv> 
      P_sslRead_ReadVariable 1415 s"

definition P_1420
  where "P_1420 s \<equiv> 
      P_sslRead_ReadVariable 1420 s"

definition P_1434
  where "P_1434 s \<equiv> 
      P_sslRead_ReadVariable 1434 s
    \<and> EDI s = 4294959106"

definition P_1439
  where "P_1439 s \<equiv> 
      P_sslRead_ReadVariable 1439 s"

definition P_1446
  where "P_1446 s \<equiv> 
      P_sslRead_ReadVariable 1446 s"

definition P_1494
  where "P_1494 s \<equiv> 
      P_sslRead_ReadVariable 1494 s"

definition P_1499
  where "P_1499 s \<equiv> 
      P_sslRead_ReadVariable 1499 s"


text "Postcondition"

definition P_ret
  where "P_ret s \<equiv>
      RSP s = rsp\<^sub>0 + 8 \<and> 
      RIP s = boffset + ret_address"


text "The simulation relation. Maps concrete states to abstract ones."

definition read_sslReadBuffer :: "state \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> sslReadBuffer"
  where "read_sslReadBuffer s a buf_size = \<lparr>
            sslReadBuffer_buf = undefined,
            sslReadBuffer_len = s \<turnstile> *[a + 8,4]\<rparr>"

definition read_sslReader :: "state \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow>  sslReader"
  where "read_sslReader s a buf_size = \<lparr>
            sslReader_buf = read_sslReadBuffer s a buf_size,
            sslReader_offset = undefined\<rparr>"


definition S :: "state \<Rightarrow> sslRead_ReadVariable_state \<times> sslRead_ReadVariable_caller_state"
  where "S s \<equiv> (\<lparr> reader\<^sub>v = if reader_ptr\<^sub>0 = 0 then None else Some (read_sslReader s reader_ptr\<^sub>0 buf_size\<^sub>0),
                  out\<^sub>v = if out_ptr\<^sub>0 = 0 then None else Some (read_sslReadBuffer s out_ptr\<^sub>0 buf_size\<^sub>1),
                  rv\<^sub>v = if RIP s \<in> {boffset + 1420, boffset + 1499} then EAX s else undefined,
                  variableLen\<^sub>v = s \<turnstile> *[rsp\<^sub>0 - 24,8] \<rparr>, 
                \<lparr> reader\<^sub>v = if reader_ptr\<^sub>0 = 0 then None else Some (read_sslReader s reader_ptr\<^sub>0 buf_size\<^sub>0),
                  out\<^sub>v = if out_ptr\<^sub>0 = 0 then None else Some (read_sslReadBuffer s out_ptr\<^sub>0 buf_size\<^sub>1),
                  rv\<^sub>v = if RIP s = boffset + ret_address then EAX s else undefined
                \<rparr>)"


end

locale sslRead_ReadVariable_context' = sslRead_ReadVariable_context +
  fixes abstract_PORT_SetError :: "32 word \<Rightarrow> 'a \<times> sslRead_ReadVariable_state \<Rightarrow> 'a \<times> sslRead_ReadVariable_state \<Rightarrow> bool"
    and S0 :: "state \<Rightarrow> 'a \<times> sslRead_ReadVariable_state"
    and P0 Q0 l0\<^sub>0 :: "state \<Rightarrow> bool"
  fixes abstract_sslRead_ReadNumber :: "'b \<times> sslRead_ReadVariable_state \<Rightarrow> 'b \<times> sslRead_ReadVariable_state \<Rightarrow> bool"
    and S1 :: "state \<Rightarrow> 'b \<times> sslRead_ReadVariable_state"
    and P1 Q1 l1\<^sub>0 :: "state \<Rightarrow> bool"
  fixes abstract_sslRead_Read :: "'c \<times> sslRead_ReadVariable_state \<Rightarrow> 'c \<times> sslRead_ReadVariable_state \<Rightarrow> bool"
    and S2 :: "state \<Rightarrow> 'c \<times> sslRead_ReadVariable_state"
    and P2 Q2 l2\<^sub>0 :: "state \<Rightarrow> bool"
  assumes S0: "snd \<circ> S0 = fst \<circ> S"
      and prec0:  "S0:: {P_1434} run_until_pred (l0\<^sub>0 || F) \<preceq> skip {P0}"
      and hoare0: "S0:: {P0} run_until_pred F \<preceq> abstract_PORT_SetError p\<^sub>0 {Q0}"
      and post0:  "\<turnstile> Q0 \<longmapsto> P_1439"
  assumes S1: "snd \<circ> S1 = fst \<circ> S"
      and prec1:  "S1:: {P_1415} run_until_pred (l1\<^sub>0 || F) \<preceq> skip {P1}"
      and hoare1: "S1:: {P1} run_until_pred F \<preceq> abstract_sslRead_ReadNumber {Q1}"
      and post1:  "\<turnstile> Q1 \<longmapsto> P_1420"
  assumes S2: "snd \<circ> S2 = fst \<circ> S"
      and prec2:  "S2:: {P_1494} run_until_pred (l2\<^sub>0 || F) \<preceq> skip {P2}"
      and hoare2: "S2:: {P2} run_until_pred F \<preceq> abstract_sslRead_Read {Q2}"
      and post2:  "\<turnstile> Q2 \<longmapsto> P_1499"
begin


definition block1 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block1 s s' \<equiv> s' \<turnstile> *[rsp\<^sub>0 - 24,8] = (0::64 word)
                     \<and> s' \<turnstile> *[out_ptr\<^sub>0 + 8,4] = (s \<turnstile> *[out_ptr\<^sub>0 + 8,4]::32 word)
                     \<and> s' \<turnstile> *[reader_ptr\<^sub>0 + 8,4] = (s \<turnstile> *[reader_ptr\<^sub>0 + 8,4] :: 32 word)"

lemma sslRead_ReadVariable_1357_1415:
  assumes "P_1357 s"
  shows "(block1 s && P_1415) (The (run_until_pred (lines {1415, 1420, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0"
   and "RIP s = boffset + 1357"
   and "regs s fs = fs\<^sub>0"
   and "RDI s = reader_ptr\<^sub>0"
   and "ESI s = sizeLen\<^sub>0"
   and "RDX s = out_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 1357 \<or> ret_address > 1521"
    using assms[unfolded P_1357_def] ret_address
    by (auto simp add: pred_logic)  
  note assms' = this

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
    apply (symbolic_execution masters: masters) (* lea *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters out_ptr\<^sub>0_not_null)
    apply (simp (no_asm_simp) add: block1_def)
    apply (rewrite_one_let')+
    apply (simp)
    apply (simp (no_asm_simp) add: P_1415_def)
    apply (rewrite_one_let')+
    apply (simp)
    done
qed


definition block2 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block2 s s' \<equiv> RIP s' = boffset + 1434"

lemma sslRead_ReadVariable_1420_1434:
  assumes "(P_1420 && (\<lambda>s. EAX s \<noteq> 0)) s"
  shows "(block2 s && P_1434) (The (run_until_pred (lines {1434, 1439, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 72"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 1420"
   and "regs s fs = fs\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 1357 \<or> ret_address > 1521"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = reader_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 52,4] = sizeLen\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 64,8] = out_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = (s \<turnstile> *[fs\<^sub>0 + 40,8] :: 64 word)"
   and "EAX s \<noteq> 0"
    using assms[unfolded P_1420_def] ret_address
    by (auto simp add: pred_logic)  
  note assms' = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters out_ptr\<^sub>0_not_null)
    apply (simp (no_asm_simp) add: block2_def)
    apply (simp (no_asm_simp) add: P_1434_def)
    apply (rewrite_one_let')+
    apply (simp)
    done
qed

definition block3 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block3 s s' \<equiv> EAX s' = -1"

lemma sslRead_ReadVariable_1439_ret:
  assumes "P_1439 s"
  shows "(block3 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 72"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 1439"
   and "regs s fs = fs\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 1357 \<or> ret_address > 1521"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = reader_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 52,4] = sizeLen\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 64,8] = out_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = (s \<turnstile> *[fs\<^sub>0 + 40,8] :: 64 word)"
    using assms[unfolded P_1439_def] ret_address
    by (auto simp add: pred_logic)  
  note assms' = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* xor *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (insert masters out_ptr\<^sub>0_not_null)
    apply (simp (no_asm_simp) add: block3_def)
    apply (simp (no_asm_simp) add: P_ret_def)
    done
qed



definition block4 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block4 s s' \<equiv> RIP s' = boffset + 1446"

lemma sslRead_ReadVariable_1420_1446:
  assumes "(P_1420 && ! (\<lambda>s. EAX s \<noteq> 0)) s"
  shows "(block4 s && P_1446) (The (run_until_pred (lines {1446, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 72"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 1420"
   and "regs s fs = fs\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 1357 \<or> ret_address > 1521"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = reader_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 52,4] = sizeLen\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 64,8] = out_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = (s \<turnstile> *[fs\<^sub>0 + 40,8] :: 64 word)"
   and "EAX s = (0::32 word)"
    using assms[unfolded P_1420_def] ret_address
    by (auto simp add: pred_logic)  
  note assms' = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (finish_symbolic_execution)
    apply (insert masters out_ptr\<^sub>0_not_null)
    apply (simp (no_asm_simp) add: block4_def)
    apply (simp (no_asm_simp) add: P_1446_def)
    apply (rewrite_one_let')+
    apply simp
    done
qed


definition block5 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block5 s s' \<equiv> s' \<turnstile> *[out_ptr\<^sub>0 + 8,4] = (ucast (s \<turnstile> *[rsp\<^sub>0 - 24,8]::64 word)::32 word)
                     \<and> EAX s' = 0"

lemma sslRead_ReadVariable_1446_ret_yes0:
  assumes "(P_1446 && (\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 24,8] = (0::64 word))) s"
  shows "(block5 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 72"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 1446"
   and "regs s fs = fs\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 1357 \<or> ret_address > 1521"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = reader_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 52,4] = sizeLen\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 64,8] = out_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = (s \<turnstile> *[fs\<^sub>0 + 40,8] :: 64 word)"
   and "s \<turnstile> *[rsp\<^sub>0 - 24,8] = (0::64 word)"
    using assms[unfolded P_1446_def] ret_address
    by (auto simp add: pred_logic)  
  note assms' = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* xor *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (insert masters out_ptr\<^sub>0_not_null)
    apply (simp (no_asm_simp) add: block5_def)
    apply (rewrite_one_let')+
    apply auto[1]
    apply (simp (no_asm_simp) add: P_ret_def)
    done
qed

lemma sslRead_ReadVariable_1446_1495_not0:
  assumes "(P_1446 && ! (\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 24,8] = (0::64 word))) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_1494) (The (run_until_pred (lines {1494, 1499, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 72"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 1446"
   and "regs s fs = fs\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 1357 \<or> ret_address > 1521"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = reader_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 52,4] = sizeLen\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 64,8] = out_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = (s \<turnstile> *[fs\<^sub>0 + 40,8] :: 64 word)"
   and "s \<turnstile> *[rsp\<^sub>0 - 24,8] \<noteq> (0::64 word)"
    using assms[unfolded P_1446_def] ret_address
    by (auto simp add: pred_logic)  
  note assms' = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters out_ptr\<^sub>0_not_null)
    apply (simp (no_asm_simp) add: S_def read_sslReader_def read_sslReadBuffer_def)
    apply auto[1]
    apply (simp (no_asm_simp) add: P_1494_def)
    done
qed

definition block6 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block6 s s' \<equiv> EAX s' = EAX s"

lemma sslRead_ReadVariable_1499_ret:
  assumes "P_1499 s"
  shows "(block6 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 72"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 1499"
   and "regs s fs = fs\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address < 1357 \<or> ret_address > 1521"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = reader_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 52,4] = sizeLen\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 64,8] = out_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = (s \<turnstile> *[fs\<^sub>0 + 40,8] :: 64 word)"
    using assms[unfolded P_1499_def] ret_address
    by (auto simp add: pred_logic)  
  note assms' = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* xor *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block6_def)
    apply (simp (no_asm_simp) add: P_ret_def)
    done
qed


definition abstract_sslRead_ReadVariable :: "sslRead_ReadVariable_state \<times> '\<sigma>\<^sub>C sslRead_caller_scheme \<Rightarrow> sslRead_ReadVariable_state \<times> '\<sigma>\<^sub>C sslRead_caller_scheme \<Rightarrow> bool"
  where "abstract_sslRead_ReadVariable \<equiv> 
          (\<lambda> \<sigma> \<sigma>' . variableLen\<^sub>v (\<L> \<sigma>') = 0
                  \<and> reader\<^sub>v (\<L> \<sigma>') = reader\<^sub>v (\<C> \<sigma>)
                  \<and> out\<^sub>v (\<L> \<sigma>') = out\<^sub>v (\<C> \<sigma>)
                ) ;
          call abstract_sslRead_ReadNumber ;
          IF (\<lambda> \<sigma> . rv\<^sub>v (\<L> \<sigma>) \<noteq> 0) THEN
            (\<lambda> \<sigma> \<sigma>' . rv\<^sub>v (\<L> \<sigma>') = undefined) ;
            call\<^sub>1 abstract_PORT_SetError (\<lambda> _ . 4294959106) ;
            (\<lambda> \<sigma> \<sigma>' . rv\<^sub>v (\<C> \<sigma>') = -1)
          ELSE
            (\<lambda> \<sigma> \<sigma>' . rv\<^sub>v (\<L> \<sigma>') = undefined) ;
            IF (\<lambda> \<sigma> . variableLen\<^sub>v (\<L> \<sigma>) = 0) THEN
              (\<lambda> \<sigma> \<sigma>' . sslReadBuffer_len (the (out\<^sub>v (\<C> \<sigma>'))) = ucast (variableLen\<^sub>v (\<L> \<sigma>))
                      \<and> rv\<^sub>v (\<C> \<sigma>') = 0)
            ELSE
              call abstract_sslRead_Read ;
              (\<lambda> \<sigma> \<sigma>' . rv\<^sub>v (\<C> \<sigma>') = rv\<^sub>v (\<L> \<sigma>))
            FI
          FI"

lemma sslRead_ReadVariable_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {1415,1420,ret_address}) ;
          run_until_pred (lines {1420,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 1420"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 1420}" "line 1415"])
  apply (simp add: line_simps)
  done

lemma sslRead_ReadVariable_decompose2:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {1434,1439,ret_address}) ;
          run_until_pred (lines {1439,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 1439"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 1439}" "line 1434"])
  apply (simp add: line_simps)
  done

lemma sslRead_ReadVariable_decompose3:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {1446,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 1446"])
  apply (simp add: line_simps)
  done

lemma sslRead_ReadVariable_decompose4:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {1494,1499,ret_address}) ;
          run_until_pred (lines {1499,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 1499"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 1499}" "line 1494"])
  apply (simp add: line_simps)
  done

lemma sslRead_ReadVariable:
  shows "S ::
         {P_1357}
            run_until_pred (line ret_address) \<preceq> abstract_sslRead_ReadVariable
         {P_ret}"
  apply (subst abstract_sslRead_ReadVariable_def)
  apply (subst sslRead_ReadVariable_decompose)
  apply (rule HL_compose[where Q="P_1415"])
  apply (rule HL_equality_intro)
  apply (erule sslRead_ReadVariable_1357_1415)
  apply (auto simp add: pred_logic block1_def S_def read_sslReadBuffer_def read_sslReader_def )[1]
  apply (rule HL_compose[where Q="Q1"])
  apply (rule HL_call_generic[of _ _ _ l1\<^sub>0])
  using S1 apply simp
  using prec1 apply auto[1]
  using hoare1 apply simp
  apply (rule weaken[of _ P_1420])
  using post1 apply simp
  apply (rule HL_ITE[where B="\<lambda> s . EAX s \<noteq> 0"])
  apply (simp add: S_def P_1420_def)
  apply (subst sslRead_ReadVariable_decompose2)
  apply (rule HL_compose[where Q="P_1434"])
  apply (rule HL_equality_intro)
  apply (erule sslRead_ReadVariable_1420_1434)
  apply (auto simp add: pred_logic block2_def S_def read_sslReadBuffer_def read_sslReader_def )[1]
  apply (rule HL_compose[where Q="Q0"])
  apply (rule HL_call\<^sub>1_generic[of _ _ _ l0\<^sub>0])
  using S0 apply simp
  using prec0 apply auto[1]
  using hoare0 apply simp
  apply (rule weaken[of _ P_1439])
  using post0 apply simp
  apply (rule HL_equality_intro)
  apply (erule sslRead_ReadVariable_1439_ret)
  apply (simp add: block3_def S_def P_ret_def)
  apply (subst sslRead_ReadVariable_decompose3)
  apply (rule HL_compose[where Q="P_1446"])
  apply (rule HL_equality_intro)
  apply (erule sslRead_ReadVariable_1420_1446)
  apply (simp add: block4_def S_def)
  apply (rule HL_ITE[where B="\<lambda> s . s \<turnstile> *[rsp\<^sub>0 - 24,8] = (0::64 word)"])
  apply (simp add: S_def)
  apply (rule HL_equality_intro)
  apply (erule sslRead_ReadVariable_1446_ret_yes0)
  apply (simp add: S_def block5_def read_sslReadBuffer_def P_ret_def out_ptr\<^sub>0_not_null)
  apply (subst sslRead_ReadVariable_decompose4)
  apply (subst add_skip[of "call _"])
  apply (subst seq_assoc)
  apply (rule HL_compose[where Q="P_1494"])
  apply (rule HL_equality_intro)
  apply (erule sslRead_ReadVariable_1446_1495_not0)
  apply (auto simp add: skip_def)[1]
  apply (rule HL_compose[where Q="Q2"])
  apply (rule HL_call_generic[of _ _ _ l2\<^sub>0])
  using S2 apply simp
  using prec2 apply auto[1]
  using hoare2 apply simp
  apply (rule weaken[of _ P_1499])
  using post2 apply simp
  apply (rule HL_equality_intro)
  apply (erule sslRead_ReadVariable_1499_ret)
  apply (simp add: S_def block6_def P_ret_def P_1499_def)
  done

end
(* END FUNCTION sslRead_ReadVariable *)





end
