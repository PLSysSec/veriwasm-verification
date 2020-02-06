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

theory SSL_GetCertificateRequestCAs
  imports "SSLCert"
          "../../isabelle/Calls"
begin

(* FUNCTION ssl_GetCertificateRequestCAs *)


text "The state of the caller of the function."

record SECItem =
  SECITEM_len :: "32 word"

record CERTDistNames =
  CERTDistNames_names :: "SECItem list option"
  CERTDistNames_nnames :: "32 word option"

record sslSocket =
  buf :: "8 word list option"
  space :: "32 word"
  len :: "32 word"
  ssl3_ca_list :: "CERTDistNames option"


record ssl_GetCertificateRequestCAs_caller_state = 
  sslSocket\<^sub>v :: sslSocket
  calen\<^sub>v :: "32 word option"
  names\<^sub>v :: "SECItem list option"
  nnames\<^sub>v :: "32 word option"
  static_names\<^sub>v :: "CERTDistNames option"
  rv\<^sub>v :: "32 word"

text "The local state."

record ssl_GetCertificateRequestCAs_state =
  ca_list\<^sub>v :: "CERTDistNames option"
  i\<^sub>v :: "32 word"
  ret\<^sub>v :: "32 word"
  exited\<^sub>v :: bool

locale ssl_GetCertificateRequestCAs_context = sslcert_context +
  fixes sslSocket_ptr\<^sub>0 :: "64 word"
    and calen_ptr\<^sub>0 :: "64 word"
    and names_ptr\<^sub>0 :: "64 word"
    and nnames_ptr\<^sub>0 :: "64 word"
    and static_names_ptr\<^sub>0 :: "64 word"
    and static_names_names_ptr\<^sub>0 :: "64 word"
    and static_names_nnames\<^sub>0 :: "32 word"
    and ssl3_ca_list_ptr\<^sub>0 :: "64 word"
    and ssl3_ca_list_names_ptr\<^sub>0 :: "64 word"
    and ssl3_ca_list_nnames\<^sub>0 :: "32 word"
    and rsp\<^sub>0 :: "64 word"
    and ret_address :: "64 word"
    and blocks :: "(nat \<times> 64 word \<times> nat) set"
    and \<sigma>\<^sub>C :: '\<sigma>\<^sub>C
    and x_itself :: "'x::len word"
  assumes ret_address: "ret_address < 26 \<or> ret_address > 245"
    and not_null: "calen_ptr\<^sub>0 \<noteq> 0"
                  "names_ptr\<^sub>0 \<noteq> 0"
                  "nnames_ptr\<^sub>0 \<noteq> 0"
                  "static_names_ptr\<^sub>0 \<noteq> 0"
                  "ssl3_ca_list_names_ptr\<^sub>0 \<noteq> 0"
                  "static_names_names_ptr\<^sub>0 \<noteq> 0"
    and masters: "master blocks (rsp\<^sub>0, 8) 1"
        "master blocks (rsp\<^sub>0 - 8, 8) 2"
        "master blocks (rsp\<^sub>0 - 16, 8) 3"
        "master blocks (rsp\<^sub>0 - 24, 8) 4"
        "master blocks (rsp\<^sub>0 - 28, 4) 5"
        "master blocks (rsp\<^sub>0 - 48, 8) 7"
        "master blocks (rsp\<^sub>0 - 56, 8) 8"
        "master blocks (rsp\<^sub>0 - 64, 8) 9"
        "master blocks (rsp\<^sub>0 - 72, 8) 10"
        "master blocks (calen_ptr\<^sub>0, 4) 100"
        "master blocks (names_ptr\<^sub>0, 8) 101"
        "master blocks (nnames_ptr\<^sub>0, 4) 102"
        "master blocks (sslSocket_ptr\<^sub>0 + 1488,8) 200"
        "master blocks (boffset + 438,8) 300"
        "master blocks (static_names_ptr\<^sub>0 + 8, 4) 500"
        "master blocks (static_names_ptr\<^sub>0 + 16, 8) 501"
        "master blocks (ssl3_ca_list_ptr\<^sub>0 + 8,4) 502"
        "master blocks (ssl3_ca_list_ptr\<^sub>0 + 16, 8) 503"
        "master blocks (ssl3_ca_list_names_ptr\<^sub>0, unat ssl3_ca_list_nnames\<^sub>0 * 24) 700"
        "master blocks (static_names_names_ptr\<^sub>0, unat static_names_nnames\<^sub>0 * 24) 700"
begin

definition P_def
  where "P_def rsp_offset rip_offset s \<equiv> 
      seps blocks
    \<and> RSP s = rsp\<^sub>0 + rsp_offset
    \<and> RIP s = boffset + rip_offset
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
declare P_def_def[simp add]

definition P
  where "P rip_offset s \<equiv> 
      P_def (-72) rip_offset s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 48,8] = sslSocket_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 56,8] = calen_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 64,8] = names_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 72,8] = nnames_ptr\<^sub>0
    \<and> s \<turnstile> *[boffset + 438,8] = static_names_ptr\<^sub>0
    \<and> s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 8,4] = ssl3_ca_list_nnames\<^sub>0
    \<and> s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 16,8] = ssl3_ca_list_names_ptr\<^sub>0
    \<and> s \<turnstile> *[static_names_ptr\<^sub>0 + 8,4] = static_names_nnames\<^sub>0
    \<and> s \<turnstile> *[static_names_ptr\<^sub>0 + 16,8] = static_names_names_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] \<in> {(s \<turnstile> *[boffset + 438,8] :: 64 word), ssl3_ca_list_ptr\<^sub>0}"

text "Precondition"

abbreviation \<open>RCX \<sigma>  \<equiv> regs \<sigma> rcx\<close>

definition P_26
  where "P_26 s \<equiv> 
      P_def 0 26s
    \<and> RDI s = sslSocket_ptr\<^sub>0
    \<and> RSI s = calen_ptr\<^sub>0
    \<and> RDX s = names_ptr\<^sub>0
    \<and> RCX s = nnames_ptr\<^sub>0
    \<and> s \<turnstile> *[sslSocket_ptr\<^sub>0 + 1488,8] = ssl3_ca_list_ptr\<^sub>0
    \<and> s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 8,4] = ssl3_ca_list_nnames\<^sub>0
    \<and> s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 16,8] = ssl3_ca_list_names_ptr\<^sub>0
    \<and> s \<turnstile> *[static_names_ptr\<^sub>0 + 8,4] = static_names_nnames\<^sub>0
    \<and> s \<turnstile> *[static_names_ptr\<^sub>0 + 16,8] = static_names_names_ptr\<^sub>0
    \<and> s \<turnstile> *[boffset + 438,8] = static_names_ptr\<^sub>0"

definition P_110 where "P_110 s \<equiv> P 110 s \<and> (s \<turnstile> *[names_ptr\<^sub>0,8] = (0::64 word) \<and> s \<turnstile> *[nnames_ptr\<^sub>0,4] = (0::32 word))"

definition P_115 where "P_115 s \<equiv> P 115 s \<and> (s \<turnstile> *[names_ptr\<^sub>0,8] = (0::64 word) \<and> s \<turnstile> *[nnames_ptr\<^sub>0,4] = (0::32 word))"

text "Postcondition"

definition P_ret
  where "P_ret s \<equiv>
      RSP s = rsp\<^sub>0 + 8 \<and> 
      RIP s = boffset + ret_address"


text "The simulation relation. Maps concrete states to abstract ones."

definition mk_SECItem :: "192 word \<Rightarrow> SECItem"
  where "mk_SECItem a \<equiv> \<lparr> SECITEM_len = \<langle>159,128\<rangle>a\<rparr>"

definition read_SECItem_list 
  where "read_SECItem_list s a si = map mk_SECItem (read_array s a 24 si)"

definition read_CERTDistNames :: "state \<Rightarrow> 64 word \<Rightarrow> CERTDistNames"
  where "read_CERTDistNames s a = \<lparr>
            CERTDistNames_names = if s \<turnstile> *[a + 16,8] = (0::64 word) then None else Some (read_SECItem_list s (s \<turnstile> *[a + 16,8]) (unat (s \<turnstile> *[a + 8,4]::32 word))),
            CERTDistNames_nnames = if a = (0::64 word) then None else Some (s \<turnstile> *[a + 8,4])\<rparr>"

definition read_sslSocket :: "state \<Rightarrow> 64 word \<Rightarrow> sslSocket"
  where "read_sslSocket s a = \<lparr>
            buf = undefined,
            space = undefined,
            len = undefined,
            ssl3_ca_list = if s \<turnstile> *[sslSocket_ptr\<^sub>0 + 1488,8] = (0::64 word) then None else Some (read_CERTDistNames s (s \<turnstile> *[sslSocket_ptr\<^sub>0 + 1488,8]))\<rparr>"


definition S :: "state \<Rightarrow> ssl_GetCertificateRequestCAs_state \<times> ssl_GetCertificateRequestCAs_caller_state"
  where "S s \<equiv> (\<lparr> ca_list\<^sub>v = if s \<turnstile> *[rsp\<^sub>0 - 16,8] = (0::64 word) then None else Some (read_CERTDistNames s (s \<turnstile> *[rsp\<^sub>0 - 16,8])),
                  i\<^sub>v = s \<turnstile> *[rsp\<^sub>0 - 28,4],
                  ret\<^sub>v = (if RIP s \<in> {boffset + 115} then EAX s else undefined),
                  exited\<^sub>v = (RIP s = boffset + ret_address)
                  \<rparr>,
                \<lparr> sslSocket\<^sub>v = read_sslSocket s sslSocket_ptr\<^sub>0,
                  calen\<^sub>v = if calen_ptr\<^sub>0 = 0 then None else Some (s \<turnstile> *[calen_ptr\<^sub>0,4]),
                  names\<^sub>v = if names_ptr\<^sub>0 = 0  \<or> s \<turnstile> *[names_ptr\<^sub>0,8] = (0::64 word) \<or> nnames_ptr\<^sub>0 = 0 then None
                           else Some (read_SECItem_list s (s \<turnstile> *[names_ptr\<^sub>0,8]) (unat (s \<turnstile> *[nnames_ptr\<^sub>0,4]::32 word))),
                  nnames\<^sub>v = if nnames_ptr\<^sub>0 = 0 then None else Some (s \<turnstile> *[nnames_ptr\<^sub>0,4]),
                  static_names\<^sub>v = if static_names_ptr\<^sub>0 = (0::64 word) then None else Some (read_CERTDistNames s static_names_ptr\<^sub>0),
                  rv\<^sub>v = (if RIP s = boffset + ret_address then EAX s else undefined)
                \<rparr>)"


end

locale ssl_GetCertificateRequestCAs_context' = ssl_GetCertificateRequestCAs_context +
  fixes abstract_ssl_SetupCAList :: "'a \<times> ssl_GetCertificateRequestCAs_state \<Rightarrow> 'a \<times> ssl_GetCertificateRequestCAs_state \<Rightarrow> bool"
    and S0 :: "state \<Rightarrow> 'a \<times> ssl_GetCertificateRequestCAs_state"
    and P0 Q0 l0\<^sub>0 :: "state \<Rightarrow> bool"
  assumes S0: "snd \<circ> S0 = fst \<circ> S"
      and prec0:  "S0:: {P_110} run_until_pred (l0\<^sub>0 || F) \<preceq> skip {P0}"
      and hoare0: "S0:: {P0} run_until_pred F \<preceq> abstract_ssl_SetupCAList {Q0}"
      and post0:  "\<turnstile> Q0 \<longmapsto> P_115"
begin

definition block1 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block1 s s' \<equiv> s' \<turnstile> *[calen_ptr\<^sub>0,4] = (0::32 word)
                     \<and> s' \<turnstile> *[names_ptr\<^sub>0,8] = (0::64 word)
                     \<and> s' \<turnstile> *[nnames_ptr\<^sub>0,4] = (0::32 word)
                     \<and> s' \<turnstile> *[rsp\<^sub>0 - 16,8] = ssl3_ca_list_ptr\<^sub>0
                     \<and> s' \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 8,4] = (s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 8,4]::32 word)
                     \<and> s' \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 16,8] = (s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 16,8]::64 word)
                     \<and> (unat (s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 8,4]::32 word) * 24 > 0 \<longrightarrow> 
                         s' \<turnstile> *[s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 16,8],unat (s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 8,4]::32 word) * 24] =
                        (s \<turnstile> *[s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 16,8],unat (s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 8,4]::32 word) * 24] :: 'c word))
                     \<and> x_itself = (x_itself :: 'c word)"

definition P_96 where "P_96 s \<equiv> P 96 s \<and> (s \<turnstile> *[names_ptr\<^sub>0,8] = (0::64 word) \<and> s \<turnstile> *[nnames_ptr\<^sub>0,4] = (0::32 word))"

lemma ssl_GetCertificateRequestCAs_26_96:
  assumes "P_26 s"
  shows "(block1 s && P_96) (The (run_until_pred (lines {96, 137, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 26"
   and "RSP s = rsp\<^sub>0"
   and "RDI s = sslSocket_ptr\<^sub>0"
   and "RSI s = calen_ptr\<^sub>0"
   and "RDX s = names_ptr\<^sub>0"
   and "RCX s = nnames_ptr\<^sub>0"
   and "s \<turnstile> *[boffset + 438,8] = static_names_ptr\<^sub>0"
   and "s \<turnstile> *[sslSocket_ptr\<^sub>0 + 1488,8] = ssl3_ca_list_ptr\<^sub>0"
   and "s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 8,4] = ssl3_ca_list_nnames\<^sub>0"
   and "s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 16,8] = ssl3_ca_list_names_ptr\<^sub>0"
   and "s \<turnstile> *[static_names_ptr\<^sub>0 + 8,4] = static_names_nnames\<^sub>0"
   and "s \<turnstile> *[static_names_ptr\<^sub>0 + 16,8] = static_names_names_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address" 
    using assms[unfolded P_26_def]
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* push *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
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
    apply (simp (no_asm_simp) add: block1_def)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (simp (no_asm_simp) add: P_def P_96_def)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    done
qed



lemma ssl_GetCertificateRequestCAs_96_110:
  assumes "(P_96 && (\<lambda> s . s \<turnstile> *[rsp\<^sub>0 - 16,8] = (0::64 word))) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_110) (The (run_until_pred (lines {137, 110, 115, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 96"
   and "RSP s = rsp\<^sub>0 - 72"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 56,8] = calen_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 64,8] = names_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 72,8] = nnames_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[boffset + 438,8] = static_names_ptr\<^sub>0"
   and "s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 8,4] = ssl3_ca_list_nnames\<^sub>0"
   and "s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 16,8] = ssl3_ca_list_names_ptr\<^sub>0"
   and "s \<turnstile> *[static_names_ptr\<^sub>0 + 8,4] = static_names_nnames\<^sub>0"
   and "s \<turnstile> *[static_names_ptr\<^sub>0 + 16,8] = static_names_names_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] \<in> {(s \<turnstile> *[boffset + 438,8] :: 64 word), ssl3_ca_list_ptr\<^sub>0}"
   and "s \<turnstile> *[names_ptr\<^sub>0,8] = (0::64 word) \<and> s \<turnstile> *[nnames_ptr\<^sub>0,4] = (0::32 word)"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = (0::64 word)"
    using assms[unfolded P_def P_96_def]
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: S_def read_sslSocket_def read_CERTDistNames_def read_SECItem_list_def read_array_write_flag read_array_write_reg)
    apply auto[1]
    apply (simp (no_asm_simp) add: P_def P_110_def)
    done
qed

definition block2 :: "state \<Rightarrow> state \<Rightarrow> bool"
where "block2 s s' \<equiv> RIP s' = boffset + ret_address \<and> EAX s' = -1"


lemma ssl_GetCertificateRequestCAs_115_ret:
  assumes "(P_115 && (\<lambda> s . EAX s \<noteq> 0)) s"
  shows "(block2 s && P_ret) (The (run_until_pred (lines {137, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 115"
   and "RSP s = rsp\<^sub>0 - 72"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 56,8] = calen_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 64,8] = names_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 72,8] = nnames_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[boffset + 438,8] = static_names_ptr\<^sub>0"
   and "s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 8,4] = ssl3_ca_list_nnames\<^sub>0"
   and "s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 16,8] = ssl3_ca_list_names_ptr\<^sub>0"
   and "s \<turnstile> *[static_names_ptr\<^sub>0 + 8,4] = static_names_nnames\<^sub>0"
   and "s \<turnstile> *[static_names_ptr\<^sub>0 + 16,8] = static_names_names_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] \<in> {(s \<turnstile> *[boffset + 438,8] :: 64 word), ssl3_ca_list_ptr\<^sub>0}"
   and "s \<turnstile> *[names_ptr\<^sub>0,8] = (0::64 word) \<and> s \<turnstile> *[nnames_ptr\<^sub>0,4] = (0::32 word)"
   and "EAX s \<noteq> 0"
    using assms[unfolded P_115_def P_def]
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
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

definition block3 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block3 s s' \<equiv> s' \<turnstile> *[rsp\<^sub>0 - 16,8] = (s \<turnstile> *[boffset + 438,8] :: 64 word)
                        \<and> s \<turnstile> *[boffset + 438,8] = static_names_ptr\<^sub>0
                        \<and> s' \<turnstile> *[static_names_ptr\<^sub>0 + 8,4] = (s \<turnstile> *[static_names_ptr\<^sub>0 + 8,4] :: 32 word)
                        \<and> s' \<turnstile> *[static_names_ptr\<^sub>0 + 16,8] = (s \<turnstile> *[static_names_ptr\<^sub>0 + 16,8] :: 64 word)
                        \<and> (unat (s \<turnstile> *[static_names_ptr\<^sub>0 + 8,4]::32 word) * 24 > 0 \<longrightarrow> 
                         s' \<turnstile> *[s \<turnstile> *[static_names_ptr\<^sub>0 + 16,8],unat (s \<turnstile> *[static_names_ptr\<^sub>0 + 8,4]::32 word) * 24] =
                        (s \<turnstile> *[s \<turnstile> *[static_names_ptr\<^sub>0 + 16,8],unat (s \<turnstile> *[static_names_ptr\<^sub>0 + 8,4]::32 word) * 24] :: 'c word))
                        \<and> x_itself = (x_itself :: 'c word)"

definition P_137 where "P_137 s \<equiv> P 137 s \<and> (s \<turnstile> *[names_ptr\<^sub>0,8] = (0::64 word) \<and> s \<turnstile> *[nnames_ptr\<^sub>0,4] = (0::32 word)
                                \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] \<noteq> (0::64 word))"

lemma ssl_GetCertificateRequestCAs_115_137:
  assumes "(P_115 && !(\<lambda> s . EAX s \<noteq> 0)) s"
  shows "(block3 s && P_137) (The (run_until_pred (lines {137, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 115"
   and "RSP s = rsp\<^sub>0 - 72"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 56,8] = calen_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 64,8] = names_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 72,8] = nnames_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[boffset + 438,8] = static_names_ptr\<^sub>0"
   and "s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 8,4] = ssl3_ca_list_nnames\<^sub>0"
   and "s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 16,8] = ssl3_ca_list_names_ptr\<^sub>0"
   and "s \<turnstile> *[static_names_ptr\<^sub>0 + 8,4] = static_names_nnames\<^sub>0"
   and "s \<turnstile> *[static_names_ptr\<^sub>0 + 16,8] = static_names_names_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] \<in> {(s \<turnstile> *[boffset + 438,8] :: 64 word), ssl3_ca_list_ptr\<^sub>0}"
   and "s \<turnstile> *[names_ptr\<^sub>0,8] = (0::64 word) \<and> s \<turnstile> *[nnames_ptr\<^sub>0,4] = (0::32 word)"
   and "EAX s = 0"
    using assms[unfolded P_115_def P_def]
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters not_null)
    apply (simp (no_asm_simp) add: block3_def)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (simp (no_asm_simp) add: P_def P_137_def)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    done
qed



lemma ssl_GetCertificateRequestCAs_96_137:
  assumes "(P_96 && ! (\<lambda> s . s \<turnstile> *[rsp\<^sub>0 - 16,8] = (0::64 word))) s"
  shows "((\<lambda> s s' . S s' = S s) s && P_137) (The (run_until_pred (lines {137, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 96"
   and "RSP s = rsp\<^sub>0 - 72"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 56,8] = calen_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 64,8] = names_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 72,8] = nnames_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[boffset + 438,8] = static_names_ptr\<^sub>0"
   and "s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 8,4] = ssl3_ca_list_nnames\<^sub>0"
   and "s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 16,8] = ssl3_ca_list_names_ptr\<^sub>0"
   and "s \<turnstile> *[static_names_ptr\<^sub>0 + 8,4] = static_names_nnames\<^sub>0"
   and "s \<turnstile> *[static_names_ptr\<^sub>0 + 16,8] = static_names_names_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] \<in> {(s \<turnstile> *[boffset + 438,8] :: 64 word), ssl3_ca_list_ptr\<^sub>0}"
   and "s \<turnstile> *[names_ptr\<^sub>0,8] = (0::64 word) \<and> s \<turnstile> *[nnames_ptr\<^sub>0,4] = (0::32 word)"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] \<noteq> (0::64 word)"
    using assms[unfolded P_96_def P_def]
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: S_def read_sslSocket_def read_CERTDistNames_def read_SECItem_list_def read_array_write_reg read_array_write_flag)
    apply auto[1]
    apply (simp (no_asm_simp) add: P_def P_137_def)
    done
qed



definition block4 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block4 s s' \<equiv> s' \<turnstile> *[names_ptr\<^sub>0,8] = (s \<turnstile> *[16 + (s \<turnstile> *[rsp\<^sub>0 - 16,8]),8] ::64 word)
                     \<and> s' \<turnstile> *[nnames_ptr\<^sub>0,4] = (s \<turnstile> *[8 + (s \<turnstile> *[rsp\<^sub>0 - 16,8]),4] ::32 word)
                     \<and> (unat (s \<turnstile> *[(s \<turnstile> *[rsp\<^sub>0 - 16,8]) + 8,4]::32 word) * 24 > 0 \<longrightarrow> 
                       s' \<turnstile> *[s \<turnstile> *[(s \<turnstile> *[rsp\<^sub>0 - 16,8]) + 16,8],unat (s \<turnstile> *[8 + (s \<turnstile> *[rsp\<^sub>0 - 16,8]),4]::32 word) * 24] =
                       (s \<turnstile> *[s \<turnstile> *[(s \<turnstile> *[rsp\<^sub>0 - 16,8]) + 16,8],unat (s \<turnstile> *[8 + (s \<turnstile> *[rsp\<^sub>0 - 16,8]),4]::32 word) * 24] :: 'c word))
                     \<and> x_itself = (x_itself :: 'c word)"

definition P_174 :: "state \<Rightarrow> bool"
  where "P_174 s \<equiv> P 174 s
                  \<and> s \<turnstile> *[names_ptr\<^sub>0,8] \<noteq> (0::64 word)
                  \<and> ((s \<turnstile> *[names_ptr\<^sub>0,8] = ssl3_ca_list_names_ptr\<^sub>0 \<and> s \<turnstile> *[nnames_ptr\<^sub>0,4] = ssl3_ca_list_nnames\<^sub>0) \<or>
                     (s \<turnstile> *[names_ptr\<^sub>0,8] = static_names_names_ptr\<^sub>0 \<and> s \<turnstile> *[nnames_ptr\<^sub>0,4] = static_names_nnames\<^sub>0))"

lemma ssl_GetCertificateRequestCAs_137_174_not0:
  assumes "(((P_137 || P_ret) && (\<lambda>s. regs s rip \<noteq> boffset + ret_address)) && (\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 16,8] \<noteq> (0::64 word))) s"
  shows "(block4 s && P_174) (The (run_until_pred (lines {174, 233, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 137"
   and "RSP s = rsp\<^sub>0 - 72"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 56,8] = calen_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 64,8] = names_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 72,8] = nnames_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[boffset + 438,8] = static_names_ptr\<^sub>0"
   and "s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 8,4] = ssl3_ca_list_nnames\<^sub>0"
   and "s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 16,8] = ssl3_ca_list_names_ptr\<^sub>0"
   and "s \<turnstile> *[static_names_ptr\<^sub>0 + 8,4] = static_names_nnames\<^sub>0"
   and "s \<turnstile> *[static_names_ptr\<^sub>0 + 16,8] = static_names_names_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] \<in> {static_names_ptr\<^sub>0, ssl3_ca_list_ptr\<^sub>0}"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] \<noteq> (0::64 word)"
    using assms[unfolded P_137_def P_def]
    by (auto simp add: pred_logic P_ret_def)
  note assms' = this

  let ?id = "if s \<turnstile> *[rsp\<^sub>0 - 16,8] = static_names_ptr\<^sub>0 then 500 else 502"
  have "master blocks (8 + (s \<turnstile> *[rsp\<^sub>0 - 16,8]), 4) ?id"
    using masters assms'
    by (auto simp add: simp_rules)
  note masters = masters this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* je *)
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
    apply (simp (no_asm_simp) add: block4_def)
    apply (rewrite_one_let')+
    apply (auto simp  add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp  add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp  add: simp_rules)[1]
    apply (auto simp  add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp  add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp  add: simp_rules)[1]
    apply (auto simp  add: simp_rules)[1]
    apply (auto simp  add: simp_rules)[1]

    apply (insert not_null)
    apply (simp (no_asm_simp) add: P_def P_174_def)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    done
qed

lemma ssl_GetCertificateRequestCAs_137_174_yes0:
  assumes "(((P_137 || P_ret) && (\<lambda>s. regs s rip \<noteq> boffset + ret_address)) && ! (\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 16,8] \<noteq> (0::64 word)))  s"
  shows "((\<lambda> s s' . S s' = S s) s && P_174) (The (run_until_pred (lines {174, 233, ret_address}) s))"
  using assms[unfolded P_137_def P_def]
  by (auto simp add: pred_logic P_ret_def)

definition block5 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block5 s s' \<equiv> s' \<turnstile> *[rsp\<^sub>0 - 28,4] = (0::32 word)"

definition P_233 :: "state \<Rightarrow> bool"
  where "P_233 s \<equiv> P 233 s
                  \<and> s \<turnstile> *[rsp\<^sub>0 - 24,8] = (s \<turnstile> *[names_ptr\<^sub>0,8] :: 64 word) + 24 * ucast (s \<turnstile> *[rsp\<^sub>0 - 28,4] :: 32 word)
                  \<and> EAX s = s \<turnstile> *[nnames_ptr\<^sub>0,4]
                  \<and> s \<turnstile> *[names_ptr\<^sub>0,8] \<noteq> (0::64 word)
                  \<and> ((s \<turnstile> *[names_ptr\<^sub>0,8] = ssl3_ca_list_names_ptr\<^sub>0 \<and> s \<turnstile> *[nnames_ptr\<^sub>0,4] = ssl3_ca_list_nnames\<^sub>0) \<or>
                     (s \<turnstile> *[names_ptr\<^sub>0,8] = static_names_names_ptr\<^sub>0 \<and> s \<turnstile> *[nnames_ptr\<^sub>0,4] = static_names_nnames\<^sub>0))"

lemma ssl_GetCertificateRequestCAs_174_233:
  assumes "P_174 s"
  shows "(block5 s && P_233) (The (run_until_pred (lines {233, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 174"
   and "RSP s = rsp\<^sub>0 - 72"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 56,8] = calen_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 64,8] = names_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 72,8] = nnames_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[boffset + 438,8] = static_names_ptr\<^sub>0"
   and "s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 8,4] = ssl3_ca_list_nnames\<^sub>0"
   and "s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 16,8] = ssl3_ca_list_names_ptr\<^sub>0"
   and "s \<turnstile> *[static_names_ptr\<^sub>0 + 8,4] = static_names_nnames\<^sub>0"
   and "s \<turnstile> *[static_names_ptr\<^sub>0 + 16,8] = static_names_names_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] \<in> {static_names_ptr\<^sub>0, ssl3_ca_list_ptr\<^sub>0}"
   and "s \<turnstile> *[names_ptr\<^sub>0,8] \<noteq> (0::64 word)"
   and "((s \<turnstile> *[names_ptr\<^sub>0,8] = ssl3_ca_list_names_ptr\<^sub>0 \<and> s \<turnstile> *[nnames_ptr\<^sub>0,4] = ssl3_ca_list_nnames\<^sub>0) \<or>
         (s \<turnstile> *[names_ptr\<^sub>0,8] = static_names_names_ptr\<^sub>0 \<and> s \<turnstile> *[nnames_ptr\<^sub>0,4] = static_names_nnames\<^sub>0))"
    using assms[unfolded P_174_def P_def]
    by (auto simp add: pred_logic P_ret_def)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters not_null)
    apply (simp (no_asm_simp) add: block5_def)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (simp (no_asm_simp) add: P_233_def P_def)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    done
qed


definition block6 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block6 s s' \<equiv> s' \<turnstile> *[calen_ptr\<^sub>0,4] = (2::32 word) + (s \<turnstile> *[calen_ptr\<^sub>0,4]) + (s \<turnstile> *[16 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),4])
                      \<and> s \<turnstile> *[names_ptr\<^sub>0,8] \<noteq> (0::64 word)"

lemma ssl_GetCertificateRequestCAs_233_233:
  assumes "(P_233 && (\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 28,4] < (s \<turnstile> *[nnames_ptr\<^sub>0,4] :: 32 word))) s"
  shows "(block6 s && P_233) (The (((\<lambda>s. (=) (step s)) ; run_until_pred (lines {ret_address, 233})) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 233"
   and "RSP s = rsp\<^sub>0 - 72"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 56,8] = calen_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 64,8] = names_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 72,8] = nnames_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[boffset + 438,8] = static_names_ptr\<^sub>0"
   and "s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 8,4] = ssl3_ca_list_nnames\<^sub>0"
   and "s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 16,8] = ssl3_ca_list_names_ptr\<^sub>0"
   and "s \<turnstile> *[static_names_ptr\<^sub>0 + 8,4] = static_names_nnames\<^sub>0"
   and "s \<turnstile> *[static_names_ptr\<^sub>0 + 16,8] = static_names_names_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] \<in> {static_names_ptr\<^sub>0, ssl3_ca_list_ptr\<^sub>0}"
   and "EAX s = s \<turnstile> *[nnames_ptr\<^sub>0,4]"
   and "s \<turnstile> *[names_ptr\<^sub>0,8] \<noteq> (0::64 word)"
   and "s \<turnstile> *[rsp\<^sub>0 - 24,8] = (s \<turnstile> *[names_ptr\<^sub>0,8] :: 64 word) + 24 * ucast (s \<turnstile> *[rsp\<^sub>0 - 28,4] :: 32 word)"
   and "s \<turnstile> *[rsp\<^sub>0 - 28,4] < (s \<turnstile> *[nnames_ptr\<^sub>0,4] :: 32 word)"
    using assms[unfolded P_233_def P_def]
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (rewrite_one_step) (* cmp *)
    apply (symbolic_execution masters: masters) (* jb *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* lea *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block6_def)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (simp (no_asm_simp) add: P_233_def)
    apply (rule conjI)
    apply (simp (no_asm_simp) add: P_def)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rule conjI)
    apply (rewrite_one_let')+
    apply (simp (no_asm_simp) add: simp_rules)
    subgoal premises prems
    proof-
      have "(s \<turnstile> *[rsp\<^sub>0 - 28,4] :: 32 word) < 2^32 - 1"
        using prems(19) 
        apply unat_arith
        by auto
      hence 1: "ucast (1 + (s \<turnstile> *[rsp\<^sub>0 - 28,4]) :: 32 word) = (1::64 word) + ucast (s \<turnstile> *[rsp\<^sub>0 - 28,4]::32 word)"
        apply unat_arith
        by (auto simp add: unat_ucast is_up unat_word_ariths)
      show ?thesis
        apply (insert 1 prems)
        apply (auto simp add: simp_rules)[1]    
        done
    qed
    apply (rule conjI)
    apply (rewrite_one_let')+
    apply (simp (no_asm_simp) add: simp_rules)
    apply (rule conjI)
    apply (rewrite_one_let')+
    apply (simp (no_asm_simp) add: simp_rules)
    apply (rewrite_one_let')+
    apply (simp (no_asm_simp) add: simp_rules)
    using assms apply (auto simp add: pred_logic P_233_def)[1]
    done
qed


lemma ssl_GetCertificateRequestCAs_233_ret:
  assumes "(P_233 && ! (\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 28,4] < (s \<turnstile> *[nnames_ptr\<^sub>0,4] :: 32 word))) s"
  shows "((\<lambda> s s' . EAX s' = 0) s && P_ret) (The ((run_until_pred (line ret_address)) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 233"
   and "RSP s = rsp\<^sub>0 - 72"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 56,8] = calen_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 64,8] = names_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 72,8] = nnames_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[boffset + 438,8] = static_names_ptr\<^sub>0"
   and "s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 8,4] = ssl3_ca_list_nnames\<^sub>0"
   and "s \<turnstile> *[ssl3_ca_list_ptr\<^sub>0 + 16,8] = ssl3_ca_list_names_ptr\<^sub>0"
   and "s \<turnstile> *[static_names_ptr\<^sub>0 + 8,4] = static_names_nnames\<^sub>0"
   and "s \<turnstile> *[static_names_ptr\<^sub>0 + 16,8] = static_names_names_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] \<in> {static_names_ptr\<^sub>0, ssl3_ca_list_ptr\<^sub>0}"
   and "EAX s = s \<turnstile> *[nnames_ptr\<^sub>0,4]"
   and "s \<turnstile> *[rsp\<^sub>0 - 24,8] = (s \<turnstile> *[names_ptr\<^sub>0,8] :: 64 word) + 24 * ucast (s \<turnstile> *[rsp\<^sub>0 - 28,4] :: 32 word)"
   and "s \<turnstile> *[rsp\<^sub>0 - 28,4] \<ge> (s \<turnstile> *[nnames_ptr\<^sub>0,4] :: 32 word)"
    using assms[unfolded P_233_def P_def]
    by (auto simp add: pred_logic)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jb *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* leave *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: P_ret_def)
    done
qed



definition abstract_ssl_GetCertificateRequestCAs :: "ssl_GetCertificateRequestCAs_state \<times> '\<sigma>\<^sub>C ssl_GetCertificateRequestCAs_caller_state_scheme \<Rightarrow> ssl_GetCertificateRequestCAs_state \<times> '\<sigma>\<^sub>C ssl_GetCertificateRequestCAs_caller_state_scheme \<Rightarrow> bool"
  where "abstract_ssl_GetCertificateRequestCAs \<equiv> 
          (\<lambda> \<sigma> \<sigma>' . calen\<^sub>v (\<C> \<sigma>') = Some 0
                  \<and> names\<^sub>v (\<C> \<sigma>') = None
                  \<and> nnames\<^sub>v (\<C> \<sigma>') = Some 0
                  \<and> ca_list\<^sub>v (\<L> \<sigma>') = ssl3_ca_list (sslSocket\<^sub>v (\<C> \<sigma>))) ;
          IF (\<lambda> \<sigma> . ca_list\<^sub>v (\<L> \<sigma>) = None) THEN
            call abstract_ssl_SetupCAList;
            IF (\<lambda> \<sigma> . ret\<^sub>v (\<L> \<sigma>) \<noteq> 0) THEN
              (\<lambda> \<sigma> \<sigma>' . rv\<^sub>v (\<C> \<sigma>') = -1 \<and> exited\<^sub>v (\<L> \<sigma>'))
            ELSE
              (\<lambda> \<sigma> \<sigma>' . ca_list\<^sub>v (\<L> \<sigma>') = static_names\<^sub>v (\<C> \<sigma>))
            FI
          FI;
          IF (\<lambda> \<sigma> . \<not> exited\<^sub>v (\<L> \<sigma>)) THEN
            IF (\<lambda> \<sigma> . ca_list\<^sub>v (\<L> \<sigma>) \<noteq> None) THEN
              (\<lambda> \<sigma> \<sigma>' . names\<^sub>v (\<C> \<sigma>') = CERTDistNames_names (the (ca_list\<^sub>v (\<L> \<sigma>)))
                      \<and> nnames\<^sub>v (\<C> \<sigma>') = CERTDistNames_nnames (the (ca_list\<^sub>v (\<L> \<sigma>))))
            FI ;
            (\<lambda> \<sigma> \<sigma>' . i\<^sub>v (\<L> \<sigma>') = 0) ;
            WHILE (\<lambda> \<sigma> . i\<^sub>v (\<L> \<sigma>) < the (nnames\<^sub>v (\<C> \<sigma>))) DO
              (\<lambda> \<sigma> \<sigma>' . calen\<^sub>v (\<C> \<sigma>') = Some (the (calen\<^sub>v (\<C> \<sigma>)) + 2 + SECITEM_len (the (names\<^sub>v (\<C> \<sigma>)) ! unat (i\<^sub>v (\<L> \<sigma>)))))
            OD ;
            (\<lambda> \<sigma> \<sigma>' . rv\<^sub>v (\<C> \<sigma>') = 0) 
          FI
          "

lemma ssl_GetCertificateRequestCAs_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {96, 137, ret_address}) ;
          run_until_pred (lines {137, ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 137"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 137}" "line 96"])
  apply (simp add: line_simps)
  done

lemma ssl_GetCertificateRequestCAs_decompose2:
  shows "run_until_pred (lines {137, ret_address}) =
          run_until_pred (lines {137, 110, 115, ret_address}) ;
          run_until_pred (lines {137, 115, ret_address}) ;
          run_until_pred (lines {137, ret_address})"
  apply (subst compose[of "lines {137, ret_address}" "line 115"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 115, 137}" "line 110"])
  apply (simp add: line_simps)
  done

lemma ssl_GetCertificateRequestCAs_decompose3:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {174, 233, ret_address}) ;
          run_until_pred (lines {233, ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 233"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 233}" "line 174"])
  apply (simp add: line_simps)
  done

lemma read_SECItem_list_eqI:
assumes "si > 0 \<Longrightarrow> s' \<turnstile> *[a,si*24] = (s \<turnstile> *[a,si*24] :: 'x::len word)"
    and "no_block_overflow (a, si*24)"
    and "8 * unat (of_nat si * 24 :: 64 word) \<le> LENGTH('x)"
  shows "read_SECItem_list s' a si = read_SECItem_list s a si"
proof(cases "si > 0")
  case True
  have "(read_array s' a 24 si ::192 word list) = read_array s a 24 si"
    apply (rule read_array_eqI_generic[of _ _ a "24*si",where 'a='x])
    using True assms
    by (auto simp add: field_simps )
  thus ?thesis
    by (auto simp add: read_SECItem_list_def assms)
next
  case False
  thus ?thesis
    by (auto simp add: read_SECItem_list_def assms)
qed

lemma temp:
  assumes "no_block_overflow (a, 24)"
  shows "s \<turnstile> *[16 + a,4] = (\<langle>159,128\<rangle>(s \<turnstile> *[a,24]::192 word) :: 32 word)"
proof-
  have 1: "no_block_overflow (a + 16, 4)"
    using assms
    apply (auto simp add: no_block_overflow.simps)
    by unat_arith
  {
    fix n :: nat
    assume "n < 32"
    hence "(s \<turnstile> *[16 + a,4]::32 word) !! n = (\<langle>159,128\<rangle>(s \<turnstile> *[a,24] :: 192 word) :: 32 word) !! n"
      unfolding read_region_def
      using assms 1
      by (auto simp add: min_def test_bit_of_take_bits test_bit_of_cat_bytes simp_rules Let'_def sublist_def read_bytes_nth)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed


lemma ssl_GetCertificateRequestCAs:
 assumes "ssl3_ca_list_nnames\<^sub>0 \<noteq> 0"
     and "8 * unat (ucast ssl3_ca_list_nnames\<^sub>0 * 24 :: 64 word) \<le> LENGTH('c)"
     and "8 * unat (ucast static_names_nnames\<^sub>0 * 24 :: 64 word) \<le> LENGTH('c)"
  shows "S ::
         {P_26}
            run_until_pred (line ret_address) \<preceq> abstract_ssl_GetCertificateRequestCAs   
         {P_ret}"
  apply (subst abstract_ssl_GetCertificateRequestCAs_def)
  apply (subst ssl_GetCertificateRequestCAs_decompose)
  apply (rule HL_compose[where Q="P_96"])
  apply (rule HL_equality_intro)
  apply (erule ssl_GetCertificateRequestCAs_26_96)
  apply (auto simp add: not_null S_def read_sslSocket_def read_CERTDistNames_def block1_def P_26_def)[1]
  apply (rule read_SECItem_list_eqI[where 'x='c],simp)
  using assms apply unat_arith
  using assms apply unat_arith
  apply (rule read_SECItem_list_eqI[where 'x='c],simp)
  using masters apply (simp add: simp_rules)
  using assms apply simp 

  apply (rule HL_compose[where Q="P_137 || P_ret"])
  apply (rule HL_ITE2[where B="\<lambda> s . s \<turnstile> *[rsp\<^sub>0 - 16,8] = (0::64 word)"])
  apply (simp add: S_def)
  apply (subst ssl_GetCertificateRequestCAs_decompose2)
  apply (subst add_skip[of "call _"])
  apply (subst seq_assoc)
  apply (rule HL_compose[where Q="P_110"])
  apply (rule HL_equality_intro)
  apply (erule ssl_GetCertificateRequestCAs_96_110)
  apply (simp add: skip_def)
  apply (rule HL_compose[where Q="P_115"])
  apply (rule HL_call_generic)
  apply (rule S0)
  apply (rule prec0)
  apply (rule strengthen[OF post0])
  apply (rule hoare0)  
  apply (rule HL_ITE[where B="\<lambda> s . EAX s \<noteq> 0"])
  apply (simp add: S_def P_def P_115_def)
  apply (rule strengthen[of P_ret])
  apply (simp add: pred_logic)
  apply (rule HL_equality_intro)
  apply (erule ssl_GetCertificateRequestCAs_115_ret)
  apply (auto simp add: not_null S_def read_sslSocket_def read_CERTDistNames_def block2_def)[1]
  apply (rule strengthen[of "P_137"])
  apply (simp add: pred_logic)
  apply (rule HL_equality_intro)
  apply (erule ssl_GetCertificateRequestCAs_115_137)
  apply (auto simp add: not_null S_def read_sslSocket_def read_CERTDistNames_def block3_def P_def P_115_def pred_logic simp_rules)[1]
  apply (simp add: read_SECItem_list_def)
  apply (rule read_SECItem_list_eqI[where 'x='c] ;
            (insert assms masters,auto simp add: simp_rules))
  apply (simp add: read_SECItem_list_def)
  apply (rule read_SECItem_list_eqI[where 'x='c] ;
            (insert assms masters,auto simp add: simp_rules))

  apply (rule strengthen[of "P_137"])
  apply (simp add: pred_logic)
  apply (rule HL_equality_intro)
  apply (erule ssl_GetCertificateRequestCAs_96_137)
  apply (simp add: skip_def)
  apply (rule HL_ITE2[where B="\<lambda> s. RIP s \<noteq> boffset + ret_address"])
  apply (simp add: S_def)
  apply (subst ssl_GetCertificateRequestCAs_decompose3)
  apply (rule HL_compose[where Q="P_174"])
  apply (rule HL_ITE2[where B="\<lambda> s . s \<turnstile> *[rsp\<^sub>0 - 16,8] \<noteq> (0::64 word)"])
  apply (simp add: S_def)
  apply (rule HL_equality_intro)
  apply (erule ssl_GetCertificateRequestCAs_137_174_not0)
  apply (auto simp add: not_null S_def read_sslSocket_def read_CERTDistNames_def block4_def pred_logic field_simps)[1]
  apply (simp add: read_SECItem_list_def)
  apply (rule read_SECItem_list_eqI[where 'x='c],simp add: field_simps)
  subgoal premises prems' for s s'
  proof-
    show ?thesis
      apply (insert prems' masters)
      apply (simp add: P_137_def P_def)
      using no_block_overflow_block_in_memory[of 24 ssl3_ca_list_names_ptr\<^sub>0 "24 * unat (s \<turnstile> *[nnames_ptr\<^sub>0,4]::32 word)" ssl3_ca_list_names_ptr\<^sub>0 "unat ssl3_ca_list_nnames\<^sub>0" "unat (s \<turnstile> *[rsp\<^sub>0 - 28,4]::32 word)"]
      using no_block_overflow_block_in_memory[of 24 static_names_names_ptr\<^sub>0 "24 * unat (s \<turnstile> *[nnames_ptr\<^sub>0,4]::32 word)" static_names_names_ptr\<^sub>0 "unat static_names_nnames\<^sub>0" "unat (s \<turnstile> *[rsp\<^sub>0 - 28,4]::32 word)"]
      by (auto simp add: mk_SECItem_def P_233_def pred_logic temp simp_rules)
  qed
  subgoal premises prems' for s s'
  proof-
    show ?thesis
      apply (insert prems' masters assms)
      apply (simp add: P_137_def P_def)
      by (auto simp add: mk_SECItem_def P_233_def pred_logic temp simp_rules)
  qed
  apply (simp add: read_SECItem_list_def)
  apply (rule read_SECItem_list_eqI[where 'x='c],simp add: field_simps)
  subgoal premises prems' for s s'
  proof-
    show ?thesis
      apply (insert prems' masters)
      apply (simp add: P_137_def P_def)
      using no_block_overflow_block_in_memory[of 24 ssl3_ca_list_names_ptr\<^sub>0 "24 * unat (s \<turnstile> *[nnames_ptr\<^sub>0,4]::32 word)" ssl3_ca_list_names_ptr\<^sub>0 "unat ssl3_ca_list_nnames\<^sub>0" "unat (s \<turnstile> *[rsp\<^sub>0 - 28,4]::32 word)"]
      using no_block_overflow_block_in_memory[of 24 static_names_names_ptr\<^sub>0 "24 * unat (s \<turnstile> *[nnames_ptr\<^sub>0,4]::32 word)" static_names_names_ptr\<^sub>0 "unat static_names_nnames\<^sub>0" "unat (s \<turnstile> *[rsp\<^sub>0 - 28,4]::32 word)"]
      by (auto simp add: mk_SECItem_def pred_logic temp simp_rules P_174_def)
  qed
  subgoal premises prems' for s s'
  proof-
    show ?thesis
      apply (insert prems' masters assms)
      apply (simp add: P_137_def P_def)
      by (auto simp add: mk_SECItem_def pred_logic temp simp_rules P_174_def)
  qed


  apply (rule HL_equality_intro)
  apply (erule ssl_GetCertificateRequestCAs_137_174_yes0)
  apply (simp add: skip_def)
  apply (rule HL_compose[where Q="P_233"])
  apply (rule HL_equality_intro)
  apply (erule ssl_GetCertificateRequestCAs_174_233)
  apply (auto simp add: not_null S_def read_sslSocket_def read_CERTDistNames_def block5_def pred_logic field_simps)[1]
  apply (rule HL_while_generic[where B="\<lambda> s . s \<turnstile> *[rsp\<^sub>0 - 28,4] < (s \<turnstile> *[nnames_ptr\<^sub>0,4] :: 32 word)" and F'="line 233"])
  using ret_address apply (auto simp add: not_null S_def P_233_def P_def line_def)[1]
  apply (simp add: line_simps)
  apply (rule HL_equality_intro_step)
  apply (erule ssl_GetCertificateRequestCAs_233_233)
  apply (simp add: not_null S_def block6_def read_SECItem_list_def)
  apply (simp add: not_null S_def block6_def read_SECItem_list_def P_233_def pred_logic)
  apply (subst nth_map)
  apply (auto simp add: pred_logic length_read_array)[1]
  apply unat_arith
  apply unat_arith

  subgoal premises prems' for s s'
  proof-
    have 1: "unat (s \<turnstile> *[rsp\<^sub>0 - 28,4] :: 32 word) < unat (s \<turnstile> *[nnames_ptr\<^sub>0,4]::32 word)"
      using prems'
      apply (auto simp add: pred_logic length_read_array)[1]
      by unat_arith+
    show ?thesis
      apply (insert prems' masters 1)
      apply (subst nth_read_array[OF 1])
      apply (auto simp add: pred_logic length_read_array)[1]
      using no_block_overflow_block_in_memory[of 24 ssl3_ca_list_names_ptr\<^sub>0 "24 * unat (s \<turnstile> *[nnames_ptr\<^sub>0,4]::32 word)" ssl3_ca_list_names_ptr\<^sub>0 "unat ssl3_ca_list_nnames\<^sub>0" "unat (s \<turnstile> *[rsp\<^sub>0 - 28,4]::32 word)"]
      using no_block_overflow_block_in_memory[of 24 static_names_names_ptr\<^sub>0 "24 * unat (s \<turnstile> *[nnames_ptr\<^sub>0,4]::32 word)" static_names_names_ptr\<^sub>0 "unat static_names_nnames\<^sub>0" "unat (s \<turnstile> *[rsp\<^sub>0 - 28,4]::32 word)"]
      by (auto simp add: mk_SECItem_def P_233_def pred_logic temp simp_rules)
  qed
  apply (rule HL_equality_intro)
  apply (erule ssl_GetCertificateRequestCAs_233_ret)
  apply (simp add: S_def P_ret_def)
  apply (rule skip)
  using ret_address apply (auto simp add: pred_logic line_def P_ret_def P_def P_137_def)[1]
  done


(* END FUNCTION ssl_GetCertificateRequestCAs *)

end
