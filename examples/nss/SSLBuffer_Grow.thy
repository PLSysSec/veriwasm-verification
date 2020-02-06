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

theory SSLBuffer_Grow
  imports "SSLEncode"
          "../../isabelle/Malloc"
          "../../isabelle/Read_Array"
begin

(* FUNCTION sslBuffer_Grow *)



locale sslBuffer_Grow_context = sslencode_context +
  fixes sslBuffer_ptr\<^sub>0 :: "64 word"
    and sslBuffer_len\<^sub>0 :: "32 word"
    and newLen\<^sub>0 :: "32 word"
    and rsp\<^sub>0 :: "64 word"
    and ret_address :: "64 word"
    and \<sigma>\<^sub>C :: '\<sigma>\<^sub>C
    and newLen_t :: "'newLen::len"
    and blocks
    and PORT_SetError\<^sub>c :: "state \<Rightarrow> state"
  assumes ret_address: "ret_address < 109 \<or> ret_address > 309"
    and bufLen0: "8 * unat (1024 + sslBuffer_len\<^sub>0) \<le> LENGTH('newLen)"
    and bufLen1: "unat newLen\<^sub>0 * 8 \<le> LENGTH('newLen)"
    and bufLen2: "0 < unat (sslBuffer_len\<^sub>0 + 1024)"
    and bufLen3: "sslBuffer_len\<^sub>0 > 0"
    and bufBlock: "(200, s \<turnstile> *[sslBuffer_ptr\<^sub>0,8], unat sslBuffer_len\<^sub>0) \<in> blocks"
    and newLen_gt_0: "newLen\<^sub>0 > 0"
    and [simp]: "funcs ''PORT_SetError'' = Some PORT_SetError\<^sub>c"
    and [simp]: "RSP (PORT_SetError\<^sub>c s) = RSP s"
    and [simp]: "RBP (PORT_SetError\<^sub>c s) = RBP s"
    and [simp]: "PORT_SetError\<^sub>c s \<turnstile> *[rsp\<^sub>0,8] = (s \<turnstile> *[rsp\<^sub>0,8] :: 64 word)"
    and  [simp]: "funcs ''PORT_Alloc'' = Some (malloc blocks)"
    and  [simp]: "funcs ''PORT_Realloc'' = Some (realloc blocks)"
begin


definition masters 
  where "masters blocks' \<equiv>
      master blocks' (rsp\<^sub>0, 8) 1
    \<and> master blocks' (rsp\<^sub>0 - 8, 8) 2
    \<and> master blocks' (rsp\<^sub>0 - 16, 8) 3
    \<and> master blocks' (rsp\<^sub>0 - 32, 8) 5
    \<and> master blocks' (rsp\<^sub>0 - 36, 4) 6
    \<and> master blocks' (sslBuffer_ptr\<^sub>0, 8) 99
    \<and> master blocks' (sslBuffer_ptr\<^sub>0 + 8, 4) 100
    \<and> master blocks' (sslBuffer_ptr\<^sub>0 + 12, 4) 101
    \<and> master blocks' (sslBuffer_ptr\<^sub>0 + 16, 4) 102"

definition P_def
  where "P_def rsp_offset rip_offset s \<equiv> 
      seps blocks
    \<and> masters blocks 
    \<and> RSP s = rsp\<^sub>0 + rsp_offset
    \<and> RIP s = boffset + rip_offset
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
declare P_def_def[simp add]

definition P_sslBuffer_Grow
  where "P_sslBuffer_Grow rsp_offset rip_offset s \<equiv> 
      P_def rsp_offset rip_offset s"

declare P_sslBuffer_Grow_def [simp add]

text "Precondition"

definition P_109
  where "P_109 s \<equiv> 
      P_sslBuffer_Grow 0 109 s
    \<and> RDI s = sslBuffer_ptr\<^sub>0
    \<and> (s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = sslBuffer_len\<^sub>0)
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> ESI s = newLen\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0
    \<and> newLen_t = (newLen_t :: 'newLen)"

definition P_152
  where "P_152 s \<equiv> 
      P_sslBuffer_Grow (-40) 152 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> RDI s = 4294959105"

definition P_157
  where "P_157 s \<equiv> 
      P_sslBuffer_Grow (-40) 157 s
    \<and> RBP s = rsp\<^sub>0 - 8"

definition P_201
  where "P_201 s \<equiv> 
      P_sslBuffer_Grow (-40) 201 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0
    \<and> unat (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word) * 8 \<le> LENGTH('newLen)
    \<and> 0 < unat (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)
    \<and> newLen_t = (newLen_t :: 'newLen)"

definition P_258
  where "P_258 s \<equiv> 
      P_sslBuffer_Grow (-40) 258 s
    \<and> RDI s = ucast (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0
    \<and> unat (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word) * 8 \<le> LENGTH('newLen)
    \<and> 0 < unat (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)
    \<and> newLen_t = (newLen_t :: 'newLen)"

definition P_263
  where "P_263 s \<equiv> 
      P_sslBuffer_Grow (-40) 263 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> malloced masters (RAX s) (unat (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word))
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0
    \<and> unat (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word) * 8 \<le> LENGTH('newLen)
    \<and> 0 < unat (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)
    \<and> newLen_t = (newLen_t :: 'newLen)"


definition P_267
  where "P_267 s \<equiv> 
      P_sslBuffer_Grow (-40) 267 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0
    \<and> malloced masters (s \<turnstile> *[rsp\<^sub>0 - 16,8]) (unat (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word))
    \<and> unat (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word) * 8 \<le> LENGTH('newLen)
    \<and> 0 < unat (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)
    \<and> newLen_t = (newLen_t :: 'newLen)"

definition P_241
  where "P_241 s \<equiv> 
      P_sslBuffer_Grow (-40) 241 s
    \<and> RDI s = s \<turnstile> *[sslBuffer_ptr\<^sub>0,8]
    \<and> RSI s = ucast (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0
    \<and> s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] \<noteq> (0::64 word)
    \<and> unat (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word) * 8 \<le> LENGTH('newLen)
    \<and> 0 < unat (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)
    \<and> newLen_t = (newLen_t :: 'newLen)"

definition P_246
  where "P_246 s \<equiv> 
      P_sslBuffer_Grow (-40) 246 s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0
    \<and> malloced masters (RAX s) (unat (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word))
    \<and> unat (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word) * 8 \<le> LENGTH('newLen)
    \<and> 0 < unat (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)
    \<and> newLen_t = (newLen_t :: 'newLen)"

text "Postcondition"

definition P_ret
  where "P_ret s \<equiv>
      RSP s = rsp\<^sub>0 + 8 \<and> 
      RIP s = boffset + ret_address"


text "The simulation relation. Maps concrete states to abstract ones."

definition read_sslBuffer' :: "state \<Rightarrow> 64 word \<Rightarrow> sslBuffer"
  where "read_sslBuffer' s a = \<lparr>
            buf = if s \<turnstile> *[a,8] = (0::64 word) then None else Some (read_array_8 s (s \<turnstile> *[a,8]) (unat (s \<turnstile> *[a + 12,4] :: 32 word))),
            space = s \<turnstile> *[a + 12,4], 
            fixed = s \<turnstile> *[a + 16,4] \<noteq> (0::32 word),
            len = s \<turnstile> *[a + 8,4]\<rparr>"


definition S :: "state \<Rightarrow> sslBuffer_Grow_state \<times>'\<sigma>\<^sub>C sslBuffer_Grow_caller_state_scheme"
  where "S s \<equiv> (\<lparr> ptr\<^sub>v = (if RAX s = 0 \<or> RIP s \<notin> {boffset + 246, boffset + 263} then None else Some (RAX s)),
                  newBuf\<^sub>v = (if s \<turnstile> *[rsp\<^sub>0 - 16,8] = (0::64 word) then None else Some (read_array_8 s (s \<turnstile> *[rsp\<^sub>0 - 16,8]) (unat (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)))),
                  newLen\<^sub>v = s \<turnstile> *[rsp\<^sub>0 - 36,4],
                  buf_ptr = s \<turnstile> *[sslBuffer_ptr\<^sub>0,8]
                   \<rparr>, 
                   \<lparr> sslBuffer\<^sub>v  = read_sslBuffer' s sslBuffer_ptr\<^sub>0, 
                     ret\<^sub>v = if RIP s = boffset + ret_address then EAX s else undefined,
                    \<dots> = \<sigma>\<^sub>C \<rparr>)"

definition block0 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block0 s s' \<equiv> s' \<turnstile> *[rsp\<^sub>0 - 36,4] = newLen\<^sub>0"

lemma sslBuffer_Grow_109_152:
  assumes "((P_109 &&
            (\<lambda>s. s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 16,4] \<noteq> (0::32 word))) &&
            (\<lambda>s. newLen\<^sub>0 > s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4])) s"
  shows "(block0 s && P_152) (The (run_until_pred (lines {152, 157, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0"
   and "RIP s = boffset + 109"
   and "ret_address < 109 \<or> ret_address > 309"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "RDI s = sslBuffer_ptr\<^sub>0"
   and "ESI s = newLen\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 16,4] \<noteq> (0:: 32 word)"
   and "newLen\<^sub>0 > s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4]"
    using assms[unfolded P_109_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 36, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 99\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 102\<close>
    using assms[unfolded P_109_def]
    by (auto simp add: pred_logic masters_def)
  note masters = this

  have flg: "(1 + (ucast (NOT newLen\<^sub>0) + ucast (s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4]::32 word)) :: 33 word) !! 32 = (newLen\<^sub>0 \<le> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4])"
    using overflow_sub_bit32[of "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4]:: 32 word" newLen\<^sub>0]
    by (auto simp add: field_simps)

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* push *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* sub *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters add: flg) (* cmp *)
    apply (symbolic_execution masters: masters) (* jbe *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block0_def simp_rules)[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (simp (no_asm_simp) add: P_152_def masters_def)[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    done
qed


lemma sslBuffer_Grow_152_157:
  assumes "(P_152) s"
  shows "((call\<^sub>c PORT_SetError\<^sub>c) s && P_157) (The (run_until_pred (lines {157,ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 152"
   and "ret_address < 109 \<or> ret_address > 309"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
    using assms[unfolded P_152_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 36, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 99\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 102\<close>
    using assms[unfolded P_152_def]
    by (auto simp add: pred_logic masters_def)
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* call *)
    apply (finish_symbolic_execution)
    apply (auto simp add: call\<^sub>c_def Let_def field_simps)[1]
    apply (insert masters)
    apply (simp (no_asm_simp) add: P_157_def masters_def)
    apply auto
    done
qed

definition block1 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block1 s s' \<equiv> EAX s' = -1"

lemma sslBuffer_Grow_157_ret:
  assumes "(P_157) s"
  shows "(block1 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 157"
   and "ret_address < 109 \<or> ret_address > 309"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
    using assms[unfolded P_157_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 36, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 99\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 102\<close>
    using assms[unfolded P_157_def] 
    by (auto simp add: pred_logic masters_def)
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (auto simp add: block1_def)[1]
    apply (insert masters)
    apply (simp (no_asm_simp) add: P_ret_def)
    done
qed

definition block2 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block2 s s' \<equiv> EAX s' = 0"

lemma sslBuffer_Grow_109_ret:
  assumes "((P_109 &&
            (\<lambda>s. s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 16,4] \<noteq> (0::32 word))) &&
            ! (\<lambda>s. newLen\<^sub>0 > s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4])) s"
  shows "(block2 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0"
   and "RIP s = boffset + 109"
   and "ret_address < 109 \<or> ret_address > 309"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "RDI s = sslBuffer_ptr\<^sub>0"
   and "ESI s = newLen\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 16,4] \<noteq> (0:: 32 word)"
   and "newLen\<^sub>0 \<le> s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4]"
    using assms[unfolded P_109_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 36, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 99\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 102\<close>
    using assms[unfolded P_109_def]
    by (auto simp add: pred_logic masters_def)
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
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jbe *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block2_def)[1]
    apply (simp (no_asm_simp) add: P_ret_def)[1]
    apply auto
    done
qed


definition block3 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block3 s s' \<equiv> s' \<turnstile> *[rsp\<^sub>0 - 36,4] = max newLen\<^sub>0 ((s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4]) + 1024) "

lemma sslBuffer_Grow_109_201:
  assumes "((P_109 &&
            ! (\<lambda>s. s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 16,4] \<noteq> (0::32 word)))) s"
  shows "(block3 s && P_201) (The (run_until_pred (lines {201, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0"
   and "RIP s = boffset + 109"
   and "ret_address < 109 \<or> ret_address > 309"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "RDI s = sslBuffer_ptr\<^sub>0"
   and "ESI s = newLen\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 8,4] = sslBuffer_len\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 16,4] = (0:: 32 word)"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0"
    using assms[unfolded P_109_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 36, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 99\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 102\<close>
    using assms[unfolded P_109_def] ret_address
    by (auto simp add: pred_logic masters_def)
  note masters = this

  have flg: "(1 + (ucast (NOT newLen\<^sub>0) + ucast (sslBuffer_len\<^sub>0 + 1024)) :: 33 word) !! 32 = (newLen\<^sub>0 \<le> 1024 + sslBuffer_len\<^sub>0)"
    using overflow_sub_bit32[of "ucast (sslBuffer_len\<^sub>0 + 1024) :: 33 word" newLen\<^sub>0]
    by (auto simp add: field_simps ucast_id)

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* push *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* sub *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* lea *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters add: flg) (* cmovae *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block3_def max_def masters_def)[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (simp (no_asm_simp) add: P_201_def masters_def)[1]
    apply (rewrite_one_let')+
    using bufLen1
    apply (simp add: simp_rules)
    apply (rewrite_one_let')+
    using bufLen3 newLen_gt_0
    apply (simp add: simp_rules)
    apply unat_arith

    (* restart *)
    apply (rewrite_one_let')+
    apply ((thin_tac \<open>master _ _ _\<close>)+)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block3_def max_def)[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (simp (no_asm_simp) add: P_201_def masters_def)[1]
    apply (rewrite_one_let')+
    using bufLen0
    apply (simp add: simp_rules)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    using newLen_gt_0
    apply unat_arith
    done
qed


lemma sslBuffer_Grow_201_258:
  assumes "((P_201 &&
            (\<lambda>s. s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] < (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word))) &&
            (\<lambda>s. s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = (0::64 word))) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_258) (The (run_until_pred (lines {ret_address, 258, 267, 263}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 201"
   and "ret_address < 109 \<or> ret_address > 309"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] < (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word)"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = (0::64 word)"
   and "unat (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word) * 8 \<le> LENGTH('newLen)"
   and "0 < unat (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)"
    using assms[unfolded P_201_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 36, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 99\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 102\<close>
    using assms[unfolded P_201_def] ret_address
    by (auto simp add: pred_logic masters_def)
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jae *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: S_def read_sslBuffer'_def read_array_8_write_flag read_array_8_write_reg)[1]
    apply auto[1]
    apply (simp (no_asm_simp) add: P_258_def masters_def)[1]
    apply (simp add: simp_rules)
    done
qed


lemma sslBuffer_Grow_258_263:
  assumes "P_258 s"
  shows "((call\<^sub>c (malloc blocks)) s && P_263) (The (run_until_pred (lines  {263, 267, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 258"
   and "RDI s = ucast (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0"
   and "ret_address < 109 \<or> ret_address > 309"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "8 * unat (s \<turnstile> *[regs s rsp + 4,4]::32 word) \<le> LENGTH('newLen)"
   and "0 < unat (s \<turnstile> *[regs s rsp + 4,4]::32 word)"
    using assms[unfolded P_258_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 36, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 99\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 102\<close>
    using assms[unfolded P_258_def] ret_address
    by (auto simp add: pred_logic masters_def)
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* call *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: call\<^sub>c_def Let_def field_simps)[1]
    apply (simp (no_asm_simp) add: P_263_def simp_rules)
    apply (rule conjI)
    apply (auto simp add: masters_def)[1]
    apply (rule conjI)
    apply (auto simp add: malloc_def simp_rules)[1]
    apply (rule conjI)
    apply (auto simp add: malloc_def simp_rules)[1]
    apply (rule conjI)
    apply (auto simp add: malloc_def simp_rules)[1]
    apply (rule conjI)
    apply (rule malloced_malloced_block)
    apply simp
    apply (auto simp add: malloc_def simp_rules unat_ucast is_up)[1]
    apply (auto simp add: masters_def)[1]
    apply (auto simp add: malloc_def simp_rules)[1]
    done
qed

definition block4 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block4 s s' \<equiv> s' \<turnstile> *[rsp\<^sub>0 - 16,8] = RAX s"


lemma sslBuffer_Grow_263_267:
  assumes "P_263 s"
  shows "(block4 s && P_267) (The (run_until_pred (lines  {267, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 263"
   and "ret_address < 109 \<or> ret_address > 309"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "unat (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word) * 8 \<le> LENGTH('newLen)"
   and "0 < unat (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0"
   and "malloced masters (RAX s) (unat (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word))"
    using assms[unfolded P_263_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 36, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 99\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 102\<close>
    using assms[unfolded P_263_def] ret_address
    by (auto simp add: pred_logic masters_def)
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block4_def)[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (simp (no_asm_simp) add: masters_def P_267_def)[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    done
qed



lemma sslBuffer_Grow_201_241:
  assumes "((P_201 &&
            (\<lambda>s. s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] < (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word))) &&
            ! (\<lambda>s. s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = (0::64 word))) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_241) (The (run_until_pred (lines {ret_address, 246, 241, 267}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 201"
   and "ret_address < 109 \<or> ret_address > 309"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] < (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word)"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] \<noteq> (0::64 word)"
   and "unat (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word) * 8 \<le> LENGTH('newLen)"
   and "0 < unat (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)"
    using assms[unfolded P_201_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 36, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 99\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 102\<close>
    using assms[unfolded P_201_def]
    by (auto simp add: pred_logic masters_def)
  note masters = this


  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jae *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: S_def read_sslBuffer'_def read_array_8_write_reg read_array_8_write_flag)[1]
    apply auto[1]
    apply (simp (no_asm_simp) add: P_241_def masters_def)[1]
    apply (simp add: simp_rules)
    done
qed

lemma sslBuffer_Grow_241_246:
  assumes "P_241 s"
  shows "((call\<^sub>c (realloc blocks)) s && P_246) (The (run_until_pred (lines  {246, 267, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 241"
   and "ret_address < 109 \<or> ret_address > 309"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "RDI s = s \<turnstile> *[sslBuffer_ptr\<^sub>0,8]"
   and "RSI s = ucast (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] \<noteq> (0::64 word)"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0"
   and "unat (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word) * 8 \<le> LENGTH('newLen)"
   and "0 < unat (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)"
    using assms[unfolded P_241_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 36, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 99\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 102\<close>
    using assms[unfolded P_241_def]
    by (auto simp add: pred_logic masters_def)
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* call realloc *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: call\<^sub>c_def Let_def field_simps)[1]
    apply (simp add: P_246_def simp_rules unat_ucast is_up)
    apply (rule conjI)
    apply (auto simp add: masters_def)[1]
    apply (rule conjI)
    apply (auto simp add: realloc_def simp_rules)[1]
    apply (rule conjI)
    apply (auto simp add: realloc_def simp_rules)[1]
    apply (rule conjI)
    apply (auto simp add: realloc_def simp_rules)[1]
    apply (rule conjI)
    apply (auto simp add: realloc_def simp_rules)[1]
    apply (rule conjI)
    apply (rule malloced_realloced_block)
    apply simp
    using bufBlock 
    apply (auto simp add: realloc_def simp_rules unat_ucast is_up)[1]
    using bufLen3
    apply unat_arith
    apply (auto simp add: masters_def master_del_block realloc_def simp_rules)
    done
qed



lemma sslBuffer_Grow_246_267:
  assumes "P_246 s"
  shows "(block4 s && P_267) (The (run_until_pred (lines  {267, ret_address}) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 246"
   and "ret_address < 109 \<or> ret_address > 309"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0"
   and "malloced masters (RAX s) (unat (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word))"
   and "unat (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word) * 8 \<le> LENGTH('newLen)"
   and "0 < unat (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)"
    using assms[unfolded P_246_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 36, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 99\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 102\<close>
    using assms[unfolded P_246_def]
    by (auto simp add: pred_logic masters_def)
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block4_def)[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (simp (no_asm_simp) add: P_267_def)[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules masters_def)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules masters_def)
    done
qed

definition block5 :: "state \<Rightarrow> state \<Rightarrow> bool"
where "block5 s s' \<equiv> EAX s' = -1"

lemma sslBuffer_Grow_267_ret_0:
  assumes "(P_267 && (\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 16,8] = (0::64 word))) s"
  shows "(block5 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 267"
   and "ret_address < 109 \<or> ret_address > 309"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = (0::64 word)"
    using assms[unfolded P_267_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 36, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0, 8) 99\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 102\<close>
    using assms[unfolded P_267_def] ret_address
    by (auto simp add: pred_logic masters_def)
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block5_def)[1]
    apply (simp (no_asm_simp) add: P_ret_def)[1]
    done
qed



definition block6 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block6 s s' \<equiv> s' \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = (s \<turnstile> *[rsp\<^sub>0 - 16,8]::64 word)
                       \<and> s' \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] = (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)
                       \<and> EAX s' = 0
                       \<and> read_array_8 s' (s' \<turnstile> *[sslBuffer_ptr\<^sub>0,8]) (unat (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)) =
                          read_array_8 s (s \<turnstile> *[rsp\<^sub>0 - 16,8]) (unat (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word))"

lemma sslBuffer_Grow_267_ret_not_0:
  assumes "(P_267 && ! (\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 16,8] = (0::64 word))) s"
  shows "(block6 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  obtain i blocks' where blocks: "seps (insert (i, s \<turnstile> *[rsp\<^sub>0 - 16,8], unat (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word)) blocks') \<and> i \<notin> fst ` blocks' \<and> masters blocks'"
    using assms[unfolded P_267_def] ret_address
    by (auto simp add: pred_logic malloced_def)
  obtain blocks''  where blocks'': "blocks'' = insert (i, s \<turnstile> *[rsp\<^sub>0 - 16,8], unat (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word)) blocks'"
    by auto
  have "i \<noteq> 1" and "i \<noteq> 2" and "i \<noteq> 3" and "i \<noteq> 5" and "i \<noteq> 6" and "i \<noteq> 99" and "i \<noteq> 100" and "i \<noteq> 101" and "i \<noteq> 102"
    using blocks
    by (auto simp add: masters_def master_implies_id_in_blocks)
  note fresh_i = this

  have "seps blocks''"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 267"
   and "ret_address < 109 \<or> ret_address > 309"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] \<noteq> (0::64 word)"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0"
   and "unat (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word) * 8 \<le> LENGTH('newLen)"
   and "0 < unat (s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)"
    using assms[unfolded P_267_def] ret_address blocks blocks''
    by (auto simp add: pred_logic)
  note assms' = this

  have \<open>master blocks'' (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks'' (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks'' (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks'' (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks'' (rsp\<^sub>0 - 36, 4) 6\<close>
   and \<open>master blocks'' (sslBuffer_ptr\<^sub>0, 8) 99\<close>
   and \<open>master blocks'' (sslBuffer_ptr\<^sub>0 + 8, 4) 100\<close>
   and \<open>master blocks'' (sslBuffer_ptr\<^sub>0 + 12, 4) 101\<close>
   and \<open>master blocks'' (sslBuffer_ptr\<^sub>0 + 16, 4) 102\<close>
    using blocks blocks''
    by (auto simp add: pred_logic master_insert masters_def master_implies_id_in_blocks)
  note masters = this

  have "master blocks'' (s \<turnstile> *[rsp\<^sub>0 - 16,8], unat (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word)) i"
    apply (rule master_if_in_blocks)
    using assms'(1) blocks''
    by auto
  note masters = masters and this
  note masters = this

  show ?thesis
    apply (insert assms' )
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (insert masters fresh_i)
    apply (simp (no_asm_simp) add: block6_def)[1]
    apply (rewrite_one_let')+
    apply (simp (no_asm_simp) add: simp_rules)
    apply (rule read_array_8_eqI[where 'a='newLen])
    apply (rewrite_one_let')+
    apply (simp (no_asm_simp) add: simp_rules fresh_i)
    apply (simp (no_asm_simp) add: simp_rules)
    apply (simp (no_asm_simp) add: P_ret_def)[1]
    done
qed



lemma sslBuffer_Grow_201_ret:
  assumes "((P_201 &&
            ! (\<lambda>s. s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] < (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word)))) s"
  shows "(block2 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 201"
   and "ret_address < 109 \<or> ret_address > 309"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4] \<ge> (s \<turnstile> *[rsp\<^sub>0 - 36,4] :: 32 word)"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslBuffer_ptr\<^sub>0"
    using assms[unfolded P_201_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 32, 8) 5\<close>
   and \<open>master blocks (rsp\<^sub>0 - 36, 4) 6\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 8, 4) 100\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 12, 4) 101\<close>
   and \<open>master blocks (sslBuffer_ptr\<^sub>0 + 16, 4) 102\<close>
    using assms[unfolded P_201_def] ret_address
    by (auto simp add: pred_logic masters_def)
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jae *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block2_def)[1]
    apply (simp (no_asm_simp) add: P_ret_def)[1]
    apply auto
    done
qed


text "The abstract code"

definition abstract_sslBuffer_Grow :: "sslBuffer_Grow_state \<times> '\<sigma>\<^sub>C sslBuffer_Grow_caller_state_scheme \<Rightarrow> sslBuffer_Grow_state \<times> '\<sigma>\<^sub>C sslBuffer_Grow_caller_state_scheme \<Rightarrow> bool"
  where "abstract_sslBuffer_Grow \<equiv> 
           IF (\<lambda> \<sigma> . fixed (sslBuffer\<^sub>v (\<C> \<sigma>))) THEN 
             IF (\<lambda> \<sigma> . newLen\<^sub>0 > space (sslBuffer\<^sub>v (\<C> \<sigma>))) THEN
              (\<lambda> \<sigma> \<sigma>' . newLen\<^sub>v (\<L> \<sigma>') = newLen\<^sub>0) ;
              call\<^sub>1 (abstract\<^sub>1\<^sub>_\<^sub>3\<^sub>2 S PORT_SetError\<^sub>c) (\<lambda> _ . 4294959105) ;
              (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<C> \<sigma>') = -1)
             ELSE
              (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<C> \<sigma>') = 0)
             FI
           ELSE
             (\<lambda> \<sigma> \<sigma>' . newLen\<^sub>v (\<L> \<sigma>') = max newLen\<^sub>0 (len (sslBuffer\<^sub>v (\<C> \<sigma>)) + 1024)) ;
             IF (\<lambda> \<sigma> . newLen\<^sub>v (\<L> \<sigma>) > space (sslBuffer\<^sub>v (\<C> \<sigma>))) THEN 
               IF (\<lambda> \<sigma> . buf (sslBuffer\<^sub>v (\<C> \<sigma>)) = None) THEN 
                 call\<^sub>1 (abstract_malloc blocks) (ucast o newLen\<^sub>v) ;
                 (\<lambda> \<sigma> \<sigma>' . case newBuf\<^sub>v (\<L> \<sigma>) of
                              None \<Rightarrow> True
                            | Some x \<Rightarrow> length x = unat (newLen\<^sub>v (\<L> \<sigma>)))
               ELSE
                 call\<^sub>2 (abstract_realloc blocks) buf_ptr (ucast o newLen\<^sub>v) ;
                 (\<lambda> \<sigma> \<sigma>' . case newBuf\<^sub>v (\<L> \<sigma>) of
                              None \<Rightarrow> True
                            | Some x \<Rightarrow> length x = unat (newLen\<^sub>v (\<L> \<sigma>)))
               FI ;
               IF (\<lambda> \<sigma> . newBuf\<^sub>v (\<L> \<sigma>) = None) THEN
                  (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<C> \<sigma>') = -1)
               ELSE
                  (\<lambda> \<sigma> \<sigma>' . buf (sslBuffer\<^sub>v (\<C> \<sigma>')) = newBuf\<^sub>v (\<L> \<sigma>)
                          \<and> space (sslBuffer\<^sub>v (\<C> \<sigma>')) = newLen\<^sub>v (\<L> \<sigma>)
                          \<and> ret\<^sub>v (\<C> \<sigma>') = 0)
               FI
             ELSE
              (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<C> \<sigma>') = 0)
             FI
           FI"

                       
lemma sslBuffer_Grow_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {152,157,ret_address}) ;
          run_until_pred (lines {157,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 157"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address,157}" "line 152"])
  apply (simp add: line_simps)
  done

lemma sslBuffer_Grow_decompose1:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {201,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 201"])
  apply (simp add: line_simps)
  done

lemma sslBuffer_Grow_decompose2:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {267,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 267"])
  apply (simp add: line_simps)
  done

lemma sslBuffer_Grow_decompose3:
  shows "run_until_pred (lines {267,ret_address}) =
          run_until_pred (lines {263,267,ret_address}) ;
          run_until_pred (lines {267,ret_address})"
  apply (subst compose[of "lines {267,ret_address}" "line 263"])
  apply (simp add: line_simps)
  done

lemma sslBuffer_Grow_decompose4:
  shows "run_until_pred (lines {267,ret_address}) =
          run_until_pred (lines {246,267,ret_address}) ;
          run_until_pred (lines {267,ret_address})"
  apply (subst compose[of "lines {267,ret_address}" "line 246"])
  apply (simp add: line_simps)
  done


lemma sslBuffer_Grow:
  shows "S ::
         {P_109}
            run_until_pred (line ret_address) \<preceq> abstract_sslBuffer_Grow
         {P_ret}"
  apply (subst abstract_sslBuffer_Grow_def)
  apply (rule HL_ITE[where B ="\<lambda> s . s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 16, 4] \<noteq> (0::32 word)"])
  apply (auto simp add: S_def read_sslBuffer'_def)[1]
  apply (rule HL_ITE[where B ="\<lambda> s . newLen\<^sub>0 > s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12, 4]"])
  apply (auto simp add: S_def read_sslBuffer'_def)[1]
  apply (subst sslBuffer_Grow_decompose)
  apply (rule HL_compose[where Q=P_152])
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Grow_109_152)
  apply (simp add: block0_def S_def)
  apply (rule HL_compose[where Q=P_157])
  apply (rule HL_call\<^sub>1_generic[of "\<lambda> s . ((), \<L> S s)" _ _  "line 152" _ P_152])
  apply (auto simp add: S_def)[1]
  apply (rule skip)
  apply (simp add: pred_logic P_152_def lines_def line_def)
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Grow_152_157)
  apply (rule abstract_call\<^sub>1\<^sub>_\<^sub>3\<^sub>2)
  apply (simp add: P_152_def)
  apply simp
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Grow_157_ret)
  apply (auto simp add: S_def block1_def P_ret_def)[1]
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Grow_109_ret)
  apply (auto simp add: S_def P_ret_def block2_def)[1]
  apply (subst sslBuffer_Grow_decompose1)
  apply (rule HL_compose [where Q=P_201])
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Grow_109_201)
  apply (auto simp add: S_def read_sslBuffer'_def block3_def)[1]
  apply (rule HL_ITE[where B="\<lambda> s . s \<turnstile> *[rsp\<^sub>0 - 36,4] > s \<turnstile> *[sslBuffer_ptr\<^sub>0 + 12,4]"])
  apply (auto simp add: S_def read_sslBuffer'_def)[1]
  apply (subst sslBuffer_Grow_decompose2)
  apply (rule HL_compose [where Q=P_267])
  apply (rule HL_ITE[where B="\<lambda> s . s \<turnstile> *[sslBuffer_ptr\<^sub>0,8] = 0"])
  apply (auto simp add: S_def read_sslBuffer'_def)[1]
  apply (subst sslBuffer_Grow_decompose3)
  apply (rule HL_compose [where Q=P_263])
  apply (rule HL_call\<^sub>1_generic[of "\<lambda> s . ((), \<L> S s)" _ _  "line 258" _ P_258])
  apply (auto)[1]
  apply (rule HL_equality_intro)
  apply (simp add: line_simps)
  apply (erule sslBuffer_Grow_201_258)
  apply (simp add: skip_def)
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Grow_258_263)
  apply (rule malloc_abstract_malloc)
  apply simp
  apply (auto simp add: S_def P_258_def read_array_8_write_reg)[1]
  apply (auto simp add: S_def P_258_def)[1]
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Grow_263_267)
  apply (simp add: S_def length_read_array_8)[1]
  apply (subst sslBuffer_Grow_decompose4)
  apply (rule HL_compose [where Q=P_246])
  apply (rule HL_call\<^sub>2_generic[of "\<lambda> s . ((), \<L> S s)" _ _  "line 241" _ P_241])
  apply (auto)[1]
  apply (rule HL_equality_intro)
  apply (simp add: line_simps)
  apply (erule sslBuffer_Grow_201_241)
  apply (simp add: skip_def)
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Grow_241_246)
  apply (rule realloc_abstract_realloc)
  apply simp
  apply (auto simp add: P_241_def S_def read_array_8_write_reg)[1]
  apply (simp add: P_241_def S_def)[1]
  apply (simp add: P_241_def S_def)[1]
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Grow_246_267)
  apply (simp add: S_def length_read_array_8)[1]
  apply (rule HL_ITE[where B="\<lambda> s . s \<turnstile> *[rsp\<^sub>0 - 16,8] = (0::64 word)"])
  apply (auto simp add: P_267_def S_def)[1]
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Grow_267_ret_0)
  apply (simp add: block5_def S_def P_ret_def)
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Grow_267_ret_not_0)
  apply (auto simp add: block6_def S_def P_ret_def pred_logic read_sslBuffer'_def)[1]
  apply (rule HL_equality_intro)
  apply (erule sslBuffer_Grow_201_ret)
  apply (simp add: S_def block2_def P_ret_def)
  done

end
(* END FUNCTION sslBuffer_Grow *)





end
