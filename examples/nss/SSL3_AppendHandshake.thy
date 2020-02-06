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

theory SSL3_AppendHandshake
  imports "SSLEncode"
          "../../isabelle/Calls"
begin

(* FUNCTION ssl3_AppendHandshake *)


text "The state of the caller of the function."

record sslSocket =
  buf :: "8 word list option"
  space :: "32 word"
  len :: "32 word"

record ssl3_AppendHandshake_caller_state = 
  sslSocket\<^sub>v :: sslSocket
  void_src\<^sub>v :: "64 word"
  ret\<^sub>v :: "32 word"

text "The local state."

record ssl3_AppendHandshake_state =
  bytes\<^sub>v :: "32 word"
  room\<^sub>v :: "32 word"
  rv\<^sub>v :: "32 word"
  ret'd\<^sub>v :: bool


locale ssl3_AppendHandshake_context = sslencode_context +
  fixes sslSocket_ptr\<^sub>0 :: "64 word"
    and void_src_ptr\<^sub>0 :: "64 word"
    and bytes\<^sub>0 :: "32 word"
    and rsp\<^sub>0 :: "64 word"
    and ss_space\<^sub>0 :: "32 word"
    and ss_len\<^sub>0 :: "32 word"
    and ret_address :: "64 word"
    and blocks :: "(nat \<times> 64 word \<times> nat) set"
    and \<sigma>\<^sub>C :: '\<sigma>\<^sub>C
    and src_size_itself :: "'src_size::len"
  assumes ret_address: "ret_address < 1752 \<or> ret_address > 2247"
    and masters: "master blocks (rsp\<^sub>0, 8) 1"
        "master blocks (rsp\<^sub>0 - 8, 8) 2"
        "master blocks (rsp\<^sub>0 - 16, 8) 3"
        "master blocks (rsp\<^sub>0 - 20, 4) 4"
        "master blocks (rsp\<^sub>0 - 24, 4) 5"
        "master blocks (rsp\<^sub>0 - 32, 8) 6" (* rdi = sslSocket_ptr\<^sub>0 *)
        "master blocks (rsp\<^sub>0 - 40, 8) 7" (* rsi = void_src_ptr\<^sub>0 *)
        "master blocks (rsp\<^sub>0 - 44, 4) 8" (* bytes\<^sub>0 *)
        "master blocks (sslSocket_ptr\<^sub>0 + 268, 4) 100" (* ss->sec.ci.sendBuf.space *)
        "master blocks (sslSocket_ptr\<^sub>0 + 264, 4) 101" (* ss->sec.ci.sendBuf.len *)

begin

definition P_def
  where "P_def rsp_offset rip_offsets s \<equiv> 
      seps blocks
    \<and> RSP s = rsp\<^sub>0 + rsp_offset
    \<and> RIP s \<in> (+) boffset ` rip_offsets
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
declare P_def_def[simp add]

definition P_ssl3_AppendHandshake
  where "P_ssl3_AppendHandshake rip_offsets s \<equiv> 
      P_def (-56) rip_offsets s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslSocket_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 40,8] = void_src_ptr\<^sub>0
    \<and> s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] = ss_space\<^sub>0"
declare P_ssl3_AppendHandshake_def [simp add]

text "Precondition"

definition P_1752
  where "P_1752 s \<equiv> 
      P_def 0 {1752} s
    \<and> RDI s = sslSocket_ptr\<^sub>0
    \<and> RSI s = void_src_ptr\<^sub>0
    \<and> EDX s = bytes\<^sub>0
    \<and> s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] = ss_space\<^sub>0
    \<and> s \<turnstile> *[sslSocket_ptr\<^sub>0 + 264,4] = ss_len\<^sub>0"

definition P_1806
  where "P_1806 s \<equiv> 
      P_ssl3_AppendHandshake {1806} s
    \<and> s \<turnstile> *[rsp\<^sub>0 - 44,4] = bytes\<^sub>0
    \<and> s \<turnstile> *[sslSocket_ptr\<^sub>0 + 264,4] = ss_len\<^sub>0"

definition P_1924
  where "P_1924 s \<equiv> 
      P_ssl3_AppendHandshake {1924} s
    \<and> s \<turnstile> *[rsp\<^sub>0 - 44,4] = bytes\<^sub>0
    \<and> s \<turnstile> *[sslSocket_ptr\<^sub>0 + 264,4] = ss_len\<^sub>0"

definition P_1929
  where "P_1929 s \<equiv> 
      P_ssl3_AppendHandshake {1929} s
    \<and> s \<turnstile> *[rsp\<^sub>0 - 44,4] = bytes\<^sub>0
    \<and> s \<turnstile> *[sslSocket_ptr\<^sub>0 + 264,4] = ss_len\<^sub>0"

definition P_1992
  where "P_1992 s \<equiv> 
      P_ssl3_AppendHandshake {1992} s
    \<and> s \<turnstile> *[rsp\<^sub>0 - 44,4] = bytes\<^sub>0
    \<and> s \<turnstile> *[sslSocket_ptr\<^sub>0 + 264,4] = ss_len\<^sub>0"

definition P_1997
  where "P_1997 s \<equiv> 
      P_ssl3_AppendHandshake {1997} s
    \<and> s \<turnstile> *[rsp\<^sub>0 - 44,4] = bytes\<^sub>0
    \<and> s \<turnstile> *[sslSocket_ptr\<^sub>0 + 264,4] = ss_len\<^sub>0"

definition P_2159
  where "P_2159 s \<equiv> 
      P_ssl3_AppendHandshake {2159} s"

definition P_2068
  where "P_2068 s \<equiv> 
      P_ssl3_AppendHandshake {2068} s"

definition P_2073
  where "P_2073 s \<equiv> 
      P_ssl3_AppendHandshake {2073} s"

definition P_2110
  where "P_2110 s \<equiv> 
      P_ssl3_AppendHandshake {2110} s"

definition P_2115
  where "P_2115 s \<equiv> 
      P_ssl3_AppendHandshake {2115} s"

definition P_2210
  where "P_2210 s \<equiv> 
      P_ssl3_AppendHandshake {2210} s"

definition P_2215
  where "P_2215 s \<equiv> 
      P_ssl3_AppendHandshake {2215} s"


text "Postcondition"

definition P_ret
  where "P_ret s \<equiv>
      RSP s = rsp\<^sub>0 + 8 \<and> 
      RIP s = boffset + ret_address"

definition P_1992_or_ret
  where "P_1992_or_ret s \<equiv> P_1992 s \<or> P_ret s"


text "The simulation relation. Maps concrete states to abstract ones."

definition read_sslSocket :: "state \<Rightarrow> 64 word \<Rightarrow> sslSocket"
  where "read_sslSocket s a = \<lparr>
            buf = undefined,
            space = s \<turnstile> *[a + 268,4],
            len = s \<turnstile> *[a + 264,4]\<rparr>"

definition S :: "state \<Rightarrow> ssl3_AppendHandshake_state \<times> ssl3_AppendHandshake_caller_state"
  where "S s \<equiv> (\<lparr> bytes\<^sub>v = s \<turnstile> *[rsp\<^sub>0 - 44,4],
                  room\<^sub>v = s \<turnstile> *[rsp\<^sub>0 - 24,4],
                  rv\<^sub>v = if RIP s \<in> {boffset + 1929, boffset + 1997, boffset + 2115} then EAX s else undefined,
                  ret'd\<^sub>v = (RIP s = boffset + ret_address)\<rparr>, 
                \<lparr> sslSocket\<^sub>v = read_sslSocket s sslSocket_ptr\<^sub>0,
                  void_src\<^sub>v = s \<turnstile> *[rsp\<^sub>0 - 16,8],
                  ret\<^sub>v = if RIP s = boffset + ret_address then EAX s else undefined
                \<rparr>)"

end

locale ssl3_AppendHandshake_context' = ssl3_AppendHandshake_context +
  fixes abstract_sslBuffer_Grow :: "'a \<times> ssl3_AppendHandshake_state \<Rightarrow> 'a \<times> ssl3_AppendHandshake_state \<Rightarrow> bool"
    and S0 :: "state \<Rightarrow> 'a \<times> ssl3_AppendHandshake_state"
    and P0 Q0 l0\<^sub>0 :: "state \<Rightarrow> bool"
  fixes ssl3_UpdateHandshakeHashes :: "'b \<times> ssl3_AppendHandshake_state \<Rightarrow> 'b \<times> ssl3_AppendHandshake_state \<Rightarrow> bool"
    and S1 :: "state \<Rightarrow> 'b \<times> ssl3_AppendHandshake_state"
    and P1 Q1 l1\<^sub>0 :: "state \<Rightarrow> bool"
  fixes abstract_memcpy :: "'c \<times> ssl3_AppendHandshake_state \<Rightarrow> 'c \<times> ssl3_AppendHandshake_state \<Rightarrow> bool"
    and S2 :: "state \<Rightarrow> 'c \<times> ssl3_AppendHandshake_state"
    and P2 Q2 l2\<^sub>0 :: "state \<Rightarrow> bool"
  fixes abstract_ssl3_FlushHandshake :: "'d \<times> ssl3_AppendHandshake_state \<Rightarrow> 'd \<times> ssl3_AppendHandshake_state \<Rightarrow> bool"
    and S3 :: "state \<Rightarrow> 'd \<times> ssl3_AppendHandshake_state"
    and P3 Q3 l3\<^sub>0 :: "state \<Rightarrow> bool"
  assumes S0: "snd \<circ> S0 = fst \<circ> S"
      and prec0:  "S0:: {P_1924} run_until_pred (l0\<^sub>0 || F) \<preceq> skip {P0}"
      and hoare0: "S0:: {P0} run_until_pred F \<preceq> abstract_sslBuffer_Grow {Q0}"
      and post0:  "\<turnstile> Q0 \<longmapsto> P_1929"
  assumes S1: "snd \<circ> S1 = fst \<circ> S"
      and prec1:  "S1:: {P_1992} run_until_pred (l1\<^sub>0 || F) \<preceq> skip {P1}"
      and hoare1: "S1:: {P1} run_until_pred F \<preceq> ssl3_UpdateHandshakeHashes {Q1}"
      and post1:  "\<turnstile> Q1 \<longmapsto> P_1997"
  assumes S2: "snd \<circ> S2 = fst \<circ> S"
      and prec2:  "S2:: {P_2068} run_until_pred (l2\<^sub>0 || F) \<preceq> skip {P2}"
      and hoare2: "S2:: {P2} run_until_pred F \<preceq> abstract_memcpy {Q2}"
      and post2:  "\<turnstile> Q2 \<longmapsto> P_2073"
      and prec2':  "S2:: {P_2210} run_until_pred (l2\<^sub>0 || F) \<preceq> skip {P2}"
      and post2':  "\<turnstile> Q2 \<longmapsto> P_2215"
  assumes S3: "snd \<circ> S3 = fst \<circ> S"
      and prec3:  "S3:: {P_2110} run_until_pred (l3\<^sub>0 || F) \<preceq> skip {P3}"
      and hoare3: "S3:: {P3} run_until_pred F \<preceq> abstract_ssl3_FlushHandshake {Q3}"
      and post3:  "\<turnstile> Q3 \<longmapsto> P_2115"
begin


definition block1  :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block1 s s' \<equiv> s' \<turnstile> *[rsp\<^sub>0 - 24,4] = (s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4]:: 32 word) - (s \<turnstile> *[sslSocket_ptr\<^sub>0 + 264,4])"

lemma ssl3_AppendHandshake_1752_1806:
  assumes "P_1752 s"
  shows "(block1 s && P_1806) (The (run_until_pred (lines {1806, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1752"
   and "RSP s = rsp\<^sub>0"
   and "RDI s = sslSocket_ptr\<^sub>0"
   and "RSI s = void_src_ptr\<^sub>0"
   and "EDX s = bytes\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] = ss_space\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 264,4] = ss_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
    using assms[unfolded P_1752_def] ret_address
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
    apply (symbolic_execution masters: masters) (* sub *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block1_def)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (simp (no_asm_simp) add: P_1806_def)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    done
qed

definition block2 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block2 s s' \<equiv> EAX s' = 0"

lemma ssl3_AppendHandshake_1806_ret:
  assumes "(P_1806 && (\<lambda>s. bytes\<^sub>0 = 0)) s"
  shows "(block2 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1806"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8]  = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,8]  = void_src_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 44,4]  = bytes\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] = ss_space\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 264,4] = ss_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "bytes\<^sub>0 = 0"
    using assms[unfolded P_1806_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block2_def)
    apply (simp (no_asm_simp) add: P_ret_def)
    done
qed

lemma ssl3_AppendHandshake_1806_1924:
  assumes "((P_1806 && ! (\<lambda>s. bytes\<^sub>0 = 0)) && (\<lambda> s . s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] < (32000:: 32 word) \<and> s \<turnstile> *[rsp\<^sub>0 - 24,4] < bytes\<^sub>0)) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_1924) (The (run_until_pred (lines {1924, 1929, 1992, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1806"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8]  = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,8]  = void_src_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 44,4]  = bytes\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] = ss_space\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 264,4] = ss_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "bytes\<^sub>0 \<noteq> 0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] < (32000:: 32 word)"
   and "s \<turnstile> *[rsp\<^sub>0 - 24,4] < bytes\<^sub>0"
    using assms[unfolded P_1806_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* ja *)
    subgoal premises prems proof-
      have False
        using prems(12,15)
        by unat_arith
      thus ?thesis
        by auto
    qed
    apply (rewrite_one_let')+
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jae *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jbe *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: S_def read_sslSocket_def)
    apply auto[1] 
    apply (simp (no_asm_simp) add: P_1924_def)

    apply (rewrite_one_let')+
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* cmova *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: S_def read_sslSocket_def)
    apply auto[1] 
    apply (simp (no_asm_simp) add: P_1924_def)

    apply (rewrite_one_let')+
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: S_def read_sslSocket_def)
    apply auto[1] 
    apply (simp (no_asm_simp) add: P_1924_def)
    done
qed

definition block3 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block3 s s' \<equiv> EAX s' = -1 \<and> RIP s' = boffset + ret_address"

lemma ssl3_AppendHandshake_1929_1992_or_ret_not0:
  assumes "(P_1929 && (\<lambda>s. EAX s \<noteq> (0::32 word))) s"
  shows "(block3 s && P_1992_or_ret) (The (run_until_pred (lines {1992, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1929"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8]  = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,8]  = void_src_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 44,4]  = bytes\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] = ss_space\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 264,4] = ss_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "EAX s \<noteq> (0::32 word)"
    using assms[unfolded P_1929_def] ret_address
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
    apply (simp (no_asm_simp) add: block3_def)
    apply (simp (no_asm_simp) add: P_1992_or_ret_def P_ret_def)
    done
qed

definition block4 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block4 s s' \<equiv> s' \<turnstile> *[rsp\<^sub>0 - 24,4] = (s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4]:: 32 word) - (s \<turnstile> *[sslSocket_ptr\<^sub>0 + 264,4])
                          \<and> RIP s' = boffset + 1992"

lemma ssl3_AppendHandshake_1929_1992:
  assumes "(P_1929 && ! (\<lambda>s. EAX s \<noteq> (0::32 word))) s"
  shows "(block4 s && P_1992) (The (run_until_pred (lines {1992, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1929"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8]  = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,8]  = void_src_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 44,4]  = bytes\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] = ss_space\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 264,4] = ss_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "EAX s = (0::32 word)"
    using assms[unfolded P_1929_def] ret_address
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
    apply (symbolic_execution masters: masters) (* sub *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block4_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply simp
    apply (simp (no_asm_simp) add: P_1992_def)
    apply (rewrite_one_let')+
    apply simp
    done
qed


lemma ssl3_AppendHandshake_1806_1992:
  assumes "((P_1806 && ! (\<lambda>s. bytes\<^sub>0 = 0)) && ! (\<lambda> s . s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] < (32000:: 32 word) \<and> s \<turnstile> *[rsp\<^sub>0 - 24,4] < bytes\<^sub>0)) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_1992) (The (run_until_pred (lines {1992, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1806"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8]  = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,8]  = void_src_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 44,4]  = bytes\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] = ss_space\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 264,4] = ss_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "bytes\<^sub>0 \<noteq> 0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] \<ge> (32000:: 32 word) \<or> s \<turnstile> *[rsp\<^sub>0 - 24,4] \<ge> bytes\<^sub>0"
    using assms[unfolded P_1806_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* ja *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: S_def read_sslSocket_def read_array_8_write_flag read_array_8_write_reg)
    apply auto[1]  
    apply (simp (no_asm_simp) add: P_1992_def)
    apply (rewrite_one_let')+
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jae *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: S_def read_sslSocket_def read_array_8_write_flag read_array_8_write_reg)
    apply auto[1]  
    apply (simp (no_asm_simp) add: P_1992_def)
    apply (rewrite_one_let')+
    subgoal premises prems proof-
      have "ss_space\<^sub>0 < 31999 \<or> ss_space\<^sub>0 = 31999"
        using prems(14)
        by (auto simp add: unat_ucast is_up)
      hence False
        using prems(12,25)
        by unat_arith
      thus ?thesis
        by simp
    qed
    done
qed


lemma ssl3_AppendHandshake_1997_ret:
  assumes "(P_1997 && (\<lambda>s. EAX s \<noteq> (0::32 word))) s"
  shows "(block3 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1997"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8]  = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,8]  = void_src_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 44,4]  = bytes\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] = ss_space\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 264,4] = ss_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "EAX s \<noteq> (0::32 word)"
    using assms[unfolded P_1997_def] ret_address
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
    apply (simp (no_asm_simp) add: block3_def)
    apply (simp (no_asm_simp) add: P_ret_def)
    done
qed


lemma ssl3_AppendHandshake_1997_2159:
  assumes "(P_1997 && ! (\<lambda>s. EAX s \<noteq> (0::32 word))) s"
  shows "((\<lambda> s s' . RIP s' = boffset + 2159) s && (P_2159 || P_ret)) (The (run_until_pred (lines {2159, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 1997"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8]  = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,8]  = void_src_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 44,4]  = bytes\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] = ss_space\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 264,4] = ss_len\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "EAX s = (0::32 word)"
    using assms[unfolded P_1997_def] ret_address
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: P_2159_def)
    apply (rewrite_one_let')+
    apply (simp)
    done
qed

lemma ssl3_AppendHandshake_2159_2068:
  assumes "(((P_2159 || P_ret)
            && (\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 24,4] < (s \<turnstile> *[rsp\<^sub>0 - 44,4]::32 word))
            && ! line ret_address)
            && (\<lambda>s. (0::32 word) <s s \<turnstile> *[rsp\<^sub>0 - 24,4])) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_2068) (The (((\<lambda>s. (=) (step s)) ; run_until_pred (lines {ret_address, 2068, 2110, 2073, 2215, 2159})) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 2159"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8]  = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,8]  = void_src_ptr\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] = ss_space\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 24,4] < (s \<turnstile> *[rsp\<^sub>0 - 44,4]::32 word)"
   and "(0::32 word) <s s \<turnstile> *[rsp\<^sub>0 - 24,4]"
    using assms[unfolded P_2159_def P_ret_def] ret_address
    by (auto simp add: pred_logic line_def)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (rewrite_one_step)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* ja *)
    defer
    apply auto[1]
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jle *)
    subgoal premises prems proof-
      have False
        using prems(10,13)
        by (auto simp add: word_sless_alt)
      thus ?thesis
        by simp
    qed
    apply (rewrite_one_let')+
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mosxd *)
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
    apply (simp (no_asm_simp) add: S_def read_sslSocket_def read_array_8_write_flag read_array_8_write_reg)
    apply auto[1]  
    apply (simp (no_asm_simp) add: P_2068_def)
    done
qed

lemma sint_0_iff: "sint (x::'x::len word) = 0 \<longleftrightarrow> x = 0"
  using word_sint.Rep_inject
  by fastforce

lemma ssl3_AppendHandshake_2159_2073:
  assumes "(((P_2159 || P_ret)
            && (\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 24,4] < (s \<turnstile> *[rsp\<^sub>0 - 44,4]::32 word))
            && ! line ret_address)
            && ! (\<lambda>s. (0::32 word) <s s \<turnstile> *[rsp\<^sub>0 - 24,4])) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_2073) (The (((\<lambda>s. (=) (step s)) ; run_until_pred (lines {2073, 2110, 2215, 2159, ret_address})) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 2159"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8]  = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,8]  = void_src_ptr\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] = ss_space\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 24,4] < (s \<turnstile> *[rsp\<^sub>0 - 44,4]::32 word)"
   and "\<not> (0::32 word) <s s \<turnstile> *[rsp\<^sub>0 - 24,4]"
    using assms[unfolded P_2159_def P_ret_def] ret_address
    by (auto simp add: pred_logic line_def)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (rewrite_one_step)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* ja *)
    defer
    apply auto[1]
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jle *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: S_def read_sslSocket_def read_array_8_write_flag read_array_8_write_reg)
    apply auto[1]  
    apply (simp (no_asm_simp) add: P_2073_def)
    apply (rule impI)
    subgoal premises prems proof-
      have False
        using prems(10,23)
        by (auto simp add: word_sless_alt sint_0_iff)
      thus ?thesis
        by simp
    qed
    done
qed


definition block5 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block5 s s' \<equiv> s' \<turnstile> *[sslSocket_ptr\<^sub>0 + 264,4] = (s \<turnstile> *[sslSocket_ptr\<^sub>0 + 264,4]) + (s \<turnstile> *[rsp\<^sub>0 - 24,4]::32 word)"

lemma ssl3_AppendHandshake_2073_2110:
  assumes "P_2073 s"
  shows "(block5 s && P_2110) (The ((run_until_pred (lines {2110, 2215, 2159, ret_address})) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 2073"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8]  = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,8]  = void_src_ptr\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] = ss_space\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
    using assms[unfolded P_2073_def] ret_address
    by (auto simp add: pred_logic line_def)
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
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block5_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply auto[1]  
    apply (simp (no_asm_simp) add: P_2110_def)
    apply (rewrite_one_let')+
    apply auto[1]  
    done
qed

definition block6 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block6 s s' \<equiv> RIP s' = boffset + ret_address \<and> EAX s' = -1"

lemma ssl3_AppendHandshake_2115_ret:
  assumes "(P_2115 && (\<lambda>s. EAX s \<noteq> 0)) s"
  shows "(block6 s && (P_2159 || P_ret)) (The ((run_until_pred (lines {2159, ret_address})) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 2115"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8]  = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,8]  = void_src_ptr\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] = ss_space\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "EAX s \<noteq> 0"
    using assms[unfolded P_2115_def] ret_address
    by (auto simp add: pred_logic line_def)
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
    apply (simp (no_asm_simp) add: block6_def)
    apply (simp (no_asm_simp) add: P_ret_def)
    done
qed

definition block7 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block7 s s' \<equiv> RIP s' = boffset + 2159
                     \<and> s' \<turnstile> *[rsp\<^sub>0 - 16,8] = (s \<turnstile> *[rsp\<^sub>0 - 16,8] :: 64 word) + sextend (ucast (s \<turnstile> *[rsp\<^sub>0 - 24,4]:: 32 word)::64 word) 32 64
                     \<and> s' \<turnstile> *[rsp\<^sub>0 - 44,4] = (s \<turnstile> *[rsp\<^sub>0 - 44,4]) - (s \<turnstile> *[rsp\<^sub>0 - 24,4]::32 word)
                     \<and> s' \<turnstile> *[rsp\<^sub>0 - 24,4] = (s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268, 4]::32 word)"

lemma ssl3_AppendHandshake_2115_2159:
  assumes "(P_2115 && ! (\<lambda>s. EAX s \<noteq> 0)) s"
  shows "(block7 s && (P_2159 || P_ret)) (The ((run_until_pred (lines {2159, ret_address})) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 2115"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8]  = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,8]  = void_src_ptr\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] = ss_space\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "EAX s = 0"
    using assms[unfolded P_2115_def] ret_address
    by (auto simp add: pred_logic line_def)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* sub *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cdqe *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block7_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply auto[1]
    apply (simp (no_asm_simp) add: P_2159_def P_ret_def)
    apply (rewrite_one_let')+
    apply auto[1]
    done
qed


lemma ssl3_AppendHandshake_2159_2210:
  assumes "(((P_2159 || P_ret)
            && ! ((\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 24,4] < (s \<turnstile> *[rsp\<^sub>0 - 44,4]::32 word))
                  && ! line ret_address))
            && (\<lambda> s . RIP s \<noteq> boffset + ret_address)) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_2210) (The ((run_until_pred (lines {2210, 2215, ret_address})) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 2159"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8]  = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,8]  = void_src_ptr\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] = ss_space\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 24,4] \<ge> (s \<turnstile> *[rsp\<^sub>0 - 44,4] :: 32 word)"
    using assms[unfolded P_2159_def P_ret_def] ret_address
    by (auto simp add: pred_logic line_def)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* ja *)
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
    apply (simp (no_asm_simp) add: S_def read_sslSocket_def read_array_8_write_flag read_array_8_write_reg)
    apply auto[1]  
    apply (simp (no_asm_simp) add: P_2210_def)
    done
qed

definition block8 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block8 s s' \<equiv> s' \<turnstile> *[sslSocket_ptr\<^sub>0 + 264,4] = (s \<turnstile> *[sslSocket_ptr\<^sub>0 + 264,4]::32 word) + (s \<turnstile> *[rsp\<^sub>0 - 44,4])
                     \<and> EAX s' = 0"

lemma ssl3_AppendHandshake_2215_ret:
  assumes "P_2215 s"
  shows "(block8 s && P_ret) (The ((run_until_pred (line ret_address)) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 56"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 2215"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8]  = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 40,8]  = void_src_ptr\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] = ss_space\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
    using assms[unfolded P_2215_def] ret_address
    by (auto simp add: pred_logic line_def)
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
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block8_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply auto[1]
    apply (simp (no_asm_simp) add: P_ret_def)
    done
qed



definition abstract_ssl3_AppendHandshake :: "ssl3_AppendHandshake_state \<times> '\<sigma>\<^sub>C ssl3_AppendHandshake_caller_state_scheme \<Rightarrow> ssl3_AppendHandshake_state \<times> '\<sigma>\<^sub>C ssl3_AppendHandshake_caller_state_scheme \<Rightarrow> bool"
  where "abstract_ssl3_AppendHandshake \<equiv> 
          (\<lambda> \<sigma> \<sigma>' . room\<^sub>v (\<L> \<sigma>') = space (sslSocket\<^sub>v (\<C> \<sigma>)) - len (sslSocket\<^sub>v (\<C> \<sigma>))) ;
          IF (\<lambda> \<sigma> . bytes\<^sub>0 = 0) THEN
            (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<C> \<sigma>') = 0)
          ELSE
            IF (\<lambda> \<sigma> . space (sslSocket\<^sub>v (\<C> \<sigma>)) < 32000 \<and> room\<^sub>v (\<L> \<sigma>) < bytes\<^sub>0) THEN  
              call abstract_sslBuffer_Grow;
              IF (\<lambda> \<sigma> . rv\<^sub>v (\<L> \<sigma>) \<noteq> 0) THEN
                (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<C> \<sigma>') = -1 \<and> ret'd\<^sub>v (\<L> \<sigma>') = True)
              ELSE
                (\<lambda> \<sigma> \<sigma>' . room\<^sub>v (\<L> \<sigma>') = space (sslSocket\<^sub>v (\<C> \<sigma>)) - len (sslSocket\<^sub>v (\<C> \<sigma>)))
              FI
            ELSE skip FI ;
            IF (\<lambda> \<sigma> . \<not> ret'd\<^sub>v (\<L> \<sigma>)) THEN
              call ssl3_UpdateHandshakeHashes ;
              IF (\<lambda> \<sigma> . rv\<^sub>v (\<L> \<sigma>) \<noteq> 0) THEN
                (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<C> \<sigma>') = -1)
              ELSE
                (\<lambda> \<sigma> \<sigma>' . rv\<^sub>v (\<L> \<sigma>') = undefined) ;
                WHILE (\<lambda> \<sigma> . bytes\<^sub>v (\<L> \<sigma>) > room\<^sub>v (\<L> \<sigma>) \<and> \<not> ret'd\<^sub>v (\<L> \<sigma>)) DO
                  IF (\<lambda> \<sigma> . 0 <s room\<^sub>v (\<L> \<sigma>)) THEN
                    call abstract_memcpy 
                  ELSE skip FI ;
                  (\<lambda> \<sigma> \<sigma>' . len (sslSocket\<^sub>v (\<C> \<sigma>')) = len (sslSocket\<^sub>v (\<C> \<sigma>)) + room\<^sub>v (\<L> \<sigma>)) ;
                  call abstract_ssl3_FlushHandshake ;
                  IF (\<lambda> \<sigma> . rv\<^sub>v (\<L> \<sigma>) \<noteq> 0) THEN
                    (\<lambda> \<sigma> \<sigma>' . ret'd\<^sub>v (\<L> \<sigma>') \<and> ret\<^sub>v (\<C> \<sigma>') = -1)
                  ELSE
                    (\<lambda> \<sigma> \<sigma>' . bytes\<^sub>v (\<L> \<sigma>') = bytes\<^sub>v (\<L> \<sigma>) - room\<^sub>v (\<L> \<sigma>)
                          \<and> void_src\<^sub>v (\<C> \<sigma>') = void_src\<^sub>v (\<C> \<sigma>) + sextend (ucast (room\<^sub>v (\<L> \<sigma>))::64 word) 32 64
                          \<and> room\<^sub>v (\<L> \<sigma>') = space (sslSocket\<^sub>v (\<C> \<sigma>))
                          \<and> \<not>ret'd\<^sub>v (\<L> \<sigma>'))
                  FI
                OD ;           
                IF (\<lambda> \<sigma> . \<not> ret'd\<^sub>v (\<L> \<sigma>)) THEN
                  call abstract_memcpy ;
                  (\<lambda> \<sigma> \<sigma>' . len (sslSocket\<^sub>v (\<C> \<sigma>')) = len (sslSocket\<^sub>v (\<C> \<sigma>)) + bytes\<^sub>v (\<L> \<sigma>)
                          \<and> ret\<^sub>v (\<C> \<sigma>') = 0)
                ELSE skip FI
              FI
            ELSE skip FI
          FI"

lemma ssl3_AppendHandshake_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {1806,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 1806"])
  apply (simp add: line_simps)
  done

lemma ssl3_AppendHandshake_decompose2:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {1992,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 1992"])
  apply (simp add: line_simps)
  done

lemma ssl3_AppendHandshake_decompose3:
  shows "run_until_pred (lines {1992,ret_address}) =
          run_until_pred (lines {1924,1929,1992,ret_address}) ;
          run_until_pred (lines {1929,1992,ret_address}) ;
          run_until_pred (lines {1992,ret_address})"
  apply (subst compose[of "lines {1992,ret_address}" "line 1929"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 1992, 1929}" "line 1924"])
  apply (simp add: line_simps)
  done

lemma ssl3_AppendHandshake_decompose4:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {1997,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 1997"])
  apply (simp add: line_simps)
  done

lemma ssl3_AppendHandshake_decompose5:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {2159,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 2159"])
  apply (simp add: line_simps)
  done

lemma ssl3_AppendHandshake_decompose6:
  shows "run_until_pred (lines {ret_address,2159}) =
          run_until_pred (lines {2073,2110,2215,2159,ret_address}) ;
          run_until_pred (lines {2110,2215,2159,ret_address}) ;
          run_until_pred (lines {2215,2159,ret_address}) ;
          run_until_pred (lines {2159,ret_address})"
  apply (subst compose[of "lines {ret_address,2159}" "line 2215"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address,2215,2159}" "line 2110"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address,2110,2215,2159}" "line 2073"])
  apply (simp add: line_simps)
  done

lemma ssl3_AppendHandshake_decompose7:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {2210,2215,ret_address}) ;
          run_until_pred (lines {2215,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 2215"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 2215}" "line 2210"])
  apply (simp add: line_simps)
  done

lemma ssl3_AppendHandshake:
  shows "S ::
         {P_1752}
            run_until_pred (line ret_address) \<preceq> abstract_ssl3_AppendHandshake   
         {P_ret}"
  apply (subst abstract_ssl3_AppendHandshake_def)
  apply (subst ssl3_AppendHandshake_decompose)
  apply (rule HL_compose[where Q="P_1806"])
  apply (rule HL_equality_intro)
  apply (erule ssl3_AppendHandshake_1752_1806)
  apply (simp add: S_def block1_def read_sslSocket_def)
  apply (rule HL_ITE[where B="\<lambda> s . bytes\<^sub>0 = 0 "])
  apply (simp)
  apply (rule HL_equality_intro)
  apply (erule ssl3_AppendHandshake_1806_ret)
  apply (simp add: S_def block2_def read_sslSocket_def P_ret_def)
  apply (subst ssl3_AppendHandshake_decompose2)
  apply (rule HL_compose[where Q="P_1992_or_ret"])
  apply (rule HL_ITE[where B="\<lambda> s . s \<turnstile> *[sslSocket_ptr\<^sub>0 + 268,4] < (32000:: 32 word) \<and> s \<turnstile> *[rsp\<^sub>0 - 24,4] < bytes\<^sub>0"])
  apply (simp add: S_def read_sslSocket_def)
  apply (subst ssl3_AppendHandshake_decompose3)
  apply (subst add_skip[of "call _"])
  apply (subst seq_assoc)  
  apply (rule HL_compose[where Q="P_1924"])
  apply (rule HL_equality_intro)
  apply (erule ssl3_AppendHandshake_1806_1924)
  apply (simp add: skip_def)
  apply (rule HL_compose[where Q="Q0"])
  apply (rule HL_call_generic[of _ _ _ l0\<^sub>0])
  using S0 apply simp
  using prec0 apply auto[1]
  using hoare0 apply simp
  apply (rule weaken[of _ P_1929])
  using post0 apply simp
  apply (rule HL_ITE[where B="\<lambda> s . EAX s \<noteq> (0::32 word)"])
  apply (simp add: S_def P_1929_def)
  apply (rule HL_equality_intro)
  apply (erule ssl3_AppendHandshake_1929_1992_or_ret_not0)
  apply (simp add: S_def P_1992_or_ret_def block3_def)
  apply (rule strengthen[of P_1992])
  apply (simp add: pred_logic P_1992_def P_1992_or_ret_def)
  apply (rule HL_equality_intro)
  apply (erule ssl3_AppendHandshake_1929_1992)
  apply (simp add: S_def P_1992_def block4_def read_sslSocket_def)
  apply (rule strengthen[of P_1992])
  apply (simp add: pred_logic P_1992_def P_1992_or_ret_def)
  apply (rule HL_equality_intro)
  apply (erule ssl3_AppendHandshake_1806_1992)
  apply (simp add: skip_def)
  apply (rule HL_ITE[where B="\<lambda> s . RIP s \<noteq> boffset + ret_address"])
  apply (simp add: S_def)
  apply (rule weaken[of _ P_1992])
  apply (auto simp add: pred_logic P_1992_def P_1992_or_ret_def P_ret_def)[1]
  apply (subst ssl3_AppendHandshake_decompose4)
  apply (rule HL_compose[where Q="Q1"])
  apply (rule HL_call_generic[of _ _ _ l1\<^sub>0])
  using S1 apply simp
  using prec1 apply auto[1]
  using hoare1 apply simp
  apply (rule weaken[of _ P_1997])
  using post1 apply simp
  apply (rule HL_ITE[where B="\<lambda> s . EAX s \<noteq> (0::32 word)"])
  apply (simp add: S_def P_1997_def)
  apply (rule HL_equality_intro)
  apply (erule ssl3_AppendHandshake_1997_ret)
  apply (simp add: block3_def S_def)
  apply (subst ssl3_AppendHandshake_decompose5)
  apply (rule HL_compose[where Q="P_2159 || P_ret"])
  apply (rule HL_equality_intro)
  apply (erule ssl3_AppendHandshake_1997_2159)
  apply (simp add: S_def)
  apply (rule HL_while_v2[where B="\<lambda> s . s \<turnstile> *[rsp\<^sub>0 - 24,4] < (s \<turnstile> *[rsp\<^sub>0 - 44,4] :: 32 word)" and F'="line 2159"])
  using ret_address apply (auto simp add: S_def pred_logic line_def P_ret_def P_2159_def)[1]
  apply (rule HL_ITE[where B="\<lambda> s . RIP s \<noteq> boffset + ret_address"])
  apply (simp add: S_def)
  apply (subst ssl3_AppendHandshake_decompose7)
  apply (subst add_skip[of "call _"])
  apply (subst seq_assoc)
  apply (rule HL_compose[where Q="P_2210"])
  apply (rule HL_equality_intro)
  apply (erule ssl3_AppendHandshake_2159_2210)
  apply (simp add: skip_def)
  apply (rule HL_compose[where Q="P_2215"])
  apply (rule HL_call_generic[of _ _ _ l2\<^sub>0])
  using S2 apply simp
  using prec2' apply auto[1]
  apply (rule strengthen[of Q2])
  using post2' apply simp
  using hoare2 apply (auto simp add: pred_logic)[1]
  apply (rule HL_equality_intro)
  apply (erule ssl3_AppendHandshake_2215_ret)
  apply (simp add: block8_def S_def read_sslSocket_def P_ret_def)
  apply (rule skip)
  using ret_address apply (auto simp add: pred_logic P_2159_def line_def)[1]
  apply (simp add: line_simps)
  apply (subst ssl3_AppendHandshake_decompose6)
  apply (subst seq_assoc[symmetric])  
  apply (rule HL_compose[where Q="P_2073"])
  apply (rule HL_ITE[where B="\<lambda> s . (0::32 word) <s (s \<turnstile> *[rsp\<^sub>0 - 24,4])"])
  apply (simp add: S_def)                                                   
  apply (subst add_skip[of "call _"])
  apply (subst compose[of "lines {2073, 2110, 2215, 2159,ret_address}" "line 2068"])
  apply (simp add: line_simps)
  apply (subst seq_assoc[symmetric])
  apply (rule HL_compose[where Q="P_2068"])
  apply (rule HL_equality_intro_step)
  apply (erule ssl3_AppendHandshake_2159_2068)
  apply (simp add: skip_def)
  apply (rule HL_call_generic[of _ _ _ l2\<^sub>0])
  using S2 apply simp
  using prec2 apply auto[1]
  apply (rule strengthen[of Q2])
  using post2 apply (auto simp add: pred_logic)[1]
  using hoare2 apply simp
  apply (rule HL_equality_intro_step)
  apply (erule ssl3_AppendHandshake_2159_2073)
  apply (simp add: skip_def)
  apply (rule HL_compose[where Q="P_2110"])
  apply (rule HL_equality_intro)
  apply (erule ssl3_AppendHandshake_2073_2110)
  apply (simp add: S_def block5_def read_sslSocket_def)
  apply (rule HL_compose[where Q=P_2115])
  apply (rule HL_call_generic[of _ _ _ l3\<^sub>0])
  using S3 apply simp
  using prec3 apply auto[1]
  apply (rule strengthen[of Q3])
  using post3 apply (auto simp add: pred_logic)[1]
  using hoare3 apply simp
  apply (rule HL_ITE[where B="\<lambda> s . EAX s \<noteq>(0::32 word)"])
  apply (simp add: S_def P_2115_def)
  apply (rule HL_equality_intro)
  apply (erule ssl3_AppendHandshake_2115_ret)
  apply (simp add: block6_def S_def)
  apply (rule HL_equality_intro)
  apply (erule ssl3_AppendHandshake_2115_2159)
  using ret_address apply (auto simp add: S_def read_sslSocket_def block7_def)[1]
  apply (rule skip)
  using ret_address apply (auto simp add: pred_logic P_1992_def P_1992_or_ret_def line_def )[1]
  done


(* END FUNCTION ssl3_AppendHandshake *)

end
