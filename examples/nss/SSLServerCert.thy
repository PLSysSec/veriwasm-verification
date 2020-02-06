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

theory SSLServerCert
  imports "SSLCert"
          "../../isabelle/Calls"
begin

(* FUNCTION sslServerCert *)


text "The state of the caller of the function."

record PRC =
  PRC_ID :: "64 word"
  PRC_x :: "64 word"
  PRC_y :: "16 word"
  PRC_next :: "64 word"

record PRCList =
  PRCList_curr :: "64 word"
  PRCList_elts :: "PRC set"

record sslSocket =
  buf :: "8 word list option"
  space :: "32 word"
  len :: "32 word"
  serverCerts :: PRCList


record sslServerCert_caller_state = 
  sslSocket\<^sub>v :: sslSocket
  ret\<^sub>v :: "PRCList option"

text "The local state."

record sslServerCert_state =
  cursor\<^sub>v :: "PRCList"
  exited\<^sub>v :: bool  

locale sslServerCert_context = sslcert_context +
  fixes sslSocket_ptr\<^sub>0 :: "64 word"
    and namedCurve_ptr\<^sub>0 :: "64 word"
    and authType\<^sub>0 :: "32 word"
    and rsp\<^sub>0 :: "64 word"
    and ret_address :: "64 word"
    and blocks :: "(nat \<times> 64 word \<times> nat) set"
    and \<sigma>\<^sub>C :: '\<sigma>\<^sub>C
  assumes ret_address: "ret_address < 245 \<or> ret_address > 395"
    and masters: "master blocks (rsp\<^sub>0, 8) 1"
        "master blocks (rsp\<^sub>0 - 8, 8) 2"
        "master blocks (rsp\<^sub>0 - 16, 8) 3"
        "master blocks (rsp\<^sub>0 - 24, 8) 4"
        "master blocks (rsp\<^sub>0 - 32, 8) 5"
        "master blocks (rsp\<^sub>0 - 36, 4) 6"
        "master blocks (rsp\<^sub>0 - 48, 8) 7"
        "master blocks (sslSocket_ptr\<^sub>0 + 824, 8) 100"
begin

definition points_to :: "state \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> bool"
  where "points_to s a b \<equiv> s \<turnstile> *[a,8] = b"


definition P_def
  where "P_def rsp_offset rip_offset s \<equiv> 
      seps blocks
    \<and> RSP s = rsp\<^sub>0 + rsp_offset
    \<and> RIP s = boffset + rip_offset
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
declare P_def_def[simp add]

definition P
  where "P rip_offset s \<equiv> 
      P_def (-8) rip_offset s
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslSocket_ptr\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 36,4] = authType\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 48,8] = namedCurve_ptr\<^sub>0
    \<and> (\<forall> a . (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) a \<longrightarrow> master blocks (a,8) 3000 \<and> master blocks (16 + a,2) 3001 \<and> master blocks (24 + a,8) 3002)"

text "Precondition"

abbreviation \<open>RCX \<sigma>  \<equiv> regs \<sigma> rcx\<close>

definition P_245
  where "P_245 s \<equiv> 
      P_def 0 245 s
    \<and> RDI s = sslSocket_ptr\<^sub>0
    \<and> ESI s = authType\<^sub>0
    \<and> RDX s = namedCurve_ptr\<^sub>0
    \<and> (\<forall> a . (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) a \<longrightarrow> master blocks (a,8) 3000 \<and> master blocks (16 + a,2) 3001 \<and> master blocks (24 + a,8) 3002)"


text "Postcondition"

definition P_ret
  where "P_ret s \<equiv>
      RSP s = rsp\<^sub>0 + 8 \<and> 
      RIP s = boffset + ret_address"


text "The simulation relation. Maps concrete states to abstract ones."

definition read_PRC:: "state \<Rightarrow> 64 word \<Rightarrow> PRC"
  where "read_PRC s a \<equiv> \<lparr> PRC_ID = a, PRC_x = s \<turnstile> *[24 + a,8], PRC_y = s \<turnstile> *[16 + a,2], PRC_next = s \<turnstile> *[a,8]\<rparr>"

definition read_PRCList :: "state \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> PRCList"
  where "read_PRCList s a a\<^sub>0 \<equiv> \<lparr> PRCList_curr = a, PRCList_elts = read_PRC s ` { a' . (points_to s)\<^sup>*\<^sup>* a\<^sub>0 a'} \<rparr>"

definition read_sslSocket :: "state \<Rightarrow> 64 word \<Rightarrow> sslSocket"
  where "read_sslSocket s a = \<lparr>
            buf = undefined,
            space = undefined,
            len = undefined,
            serverCerts = read_PRCList s (a + 824) (a + 824)\<rparr>"


definition S :: "state \<Rightarrow> sslServerCert_state \<times> sslServerCert_caller_state"
  where "S s \<equiv> (\<lparr> cursor\<^sub>v = read_PRCList s (s \<turnstile> *[rsp\<^sub>0 - 24,8]) (sslSocket_ptr\<^sub>0 + 824),
                  exited\<^sub>v = (RIP s = boffset + ret_address)
                  \<rparr>,
                \<lparr> sslSocket\<^sub>v = read_sslSocket s sslSocket_ptr\<^sub>0,
                  ret\<^sub>v = if RIP s = boffset + ret_address then if RAX s = 0 then None else Some (read_PRCList s (s \<turnstile> *[rsp\<^sub>0 - 24,8]) (sslSocket_ptr\<^sub>0 + 824)) else undefined
                \<rparr>)"

end

locale sslServerCert_context' = sslServerCert_context +
  fixes abstract_ssl_SetupCAList :: "'a \<times> sslServerCert_state \<Rightarrow> 'a \<times> sslServerCert_state \<Rightarrow> bool"
    and S0 :: "state \<Rightarrow> 'a \<times> sslServerCert_state"
    and P0 Q0 l0\<^sub>0 :: "state \<Rightarrow> bool"
  assumes S0: "snd \<circ> S0 = fst \<circ> S"
      and prec0:  "S0:: {P_110} run_until_pred (l0\<^sub>0 || F) \<preceq> skip {P0}"
      and hoare0: "S0:: {P0} run_until_pred F \<preceq> abstract_ssl_SetupCAList {Q0}"
      and post0:  "\<turnstile> Q0 \<longmapsto> P_115"
begin




lemma points_to_eq:
  assumes "\<forall> b . (points_to s)\<^sup>*\<^sup>* a b \<longrightarrow> s' \<turnstile> *[b,8] = (s \<turnstile> *[b,8]::64 word)"
  shows "(points_to s')\<^sup>*\<^sup>* a b = (points_to s)\<^sup>*\<^sup>* a b"
proof-
  {
    assume "(points_to s')\<^sup>*\<^sup>* a b"
    hence "(points_to s)\<^sup>*\<^sup>* a b"
    proof(induct rule: rtranclp_induct)
      case base
      then show ?case
        by auto
    next
      case (step y z)
      hence "points_to s y z"
        using step assms
        unfolding points_to_def
        by auto
      thus ?case
        using step
        by auto
    qed
  }
  moreover
  {
    assume "(points_to s)\<^sup>*\<^sup>* a b"
    hence "(points_to s')\<^sup>*\<^sup>* a b"
    proof(induct rule: rtranclp_induct)
      case base
      then show ?case
        by auto
    next
      case (step y z)
      hence "points_to s' y z"
        using step assms
        unfolding points_to_def
        by auto
      thus ?case
        using step
        by auto
    qed
  }
  ultimately
  show ?thesis
    by auto
qed
      

definition P_386
  where "P_386 s \<equiv> P 386 s
                  \<and> flags s flag_zf = (s \<turnstile> *[rsp\<^sub>0 - 24,8] = sslSocket_ptr\<^sub>0 + 824)
                  \<and> (\<forall> a . (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) a \<longrightarrow> master blocks (a,8) 3000 \<and> master blocks (16 + a,2) 3001 \<and> master blocks (24 + a,8) 3002)
                  \<and> (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) (s \<turnstile> *[rsp\<^sub>0 - 24,8])"


definition block1 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block1 s s' \<equiv> s' \<turnstile> *[rsp\<^sub>0 - 24,8] = (s \<turnstile> *[sslSocket_ptr\<^sub>0 + 824,8] :: 64 word)
                      \<and> (points_to s')\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) = (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824)
                      \<and> (\<forall> a' . (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) a' \<longrightarrow>
                               s' \<turnstile> *[24 + a',8] = (s \<turnstile> *[24 + a',8]::64 word)
                             \<and> s' \<turnstile> *[16 + a',2] = (s \<turnstile> *[16 + a',2]::16 word)
                             \<and> s' \<turnstile> *[a',8] = (s \<turnstile> *[a',8]::64 word))"

lemma sslServerCert_245_386:
  assumes "P_245 s"
  shows "(block1 s && P_386) (The (run_until_pred (lines {386, ret_address}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 245"
   and "RSP s = rsp\<^sub>0"
   and "RDI s = sslSocket_ptr\<^sub>0"
   and "ESI s = authType\<^sub>0"
   and "RDX s = namedCurve_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "(\<forall> a . (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) a \<longrightarrow> master blocks (a,8) 3000 \<and> master blocks (16 + a,2) 3001 \<and> master blocks (24 + a,8) 3002)"
    using assms[unfolded P_245_def]
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
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (insert masters)
    subgoal premises prems
    proof-
      show ?thesis (is "(block1 s && P_386) (The (run_until_pred (lines {386, ret_address}) ?s'))")
      proof-
        have 1: "(points_to ?s')\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) = (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824)"
          apply (rule ext)
          apply (subst points_to_eq[of s])
          apply (rule allI, rule impI)
          subgoal premises prems' for a b
            apply (insert assms'(8)[THEN spec,of b,THEN mp, OF prems'],clarsimp)
            apply (insert prems)
            apply (rewrite_one_let')+
            apply (simp (no_asm_simp) add: simp_rules)
            done     
          apply (simp add: field_simps)
          done
        show ?thesis
          apply (finish_symbolic_execution)
          apply (insert prems)
          apply (simp (no_asm_simp) add: block1_def)
          apply (rule conjI)
          apply (rewrite_one_let')+
          apply (simp) 
          apply (rule conjI)
          apply (simp add: 1)  
          apply (rule allI,rule impI)
          subgoal premises prems' for a'
          proof-
            have masters': "master blocks (a', 8) 3000" "master blocks (a' + 16, 2) 3001" "master blocks (a' + 24, 8) 3002"
              using prems'
              by (auto simp add: field_simps)
            thus ?thesis
              apply (insert prems masters')
              apply (rewrite_one_let')+
              by (simp)
          qed
          apply (insert prems)
          apply (simp (no_asm_simp) add: P_386_def)
          apply (rule conjI)
          apply (simp (no_asm_simp) add: P_def)
          apply (rewrite_one_let')+
          apply (auto simp add: simp_rules)[1]
          apply (auto simp add: simp_rules 1)[1]
          apply (rewrite_one_let' add: 1)+
          apply (auto simp add: field_simps)[1]
          apply (rewrite_one_let' add: 1)+
          apply (auto simp add: field_simps)[1]
          apply (rule r_into_rtranclp, simp add: points_to_def)
          apply (rule r_into_rtranclp, simp add: points_to_def)
          done
      qed
    qed
    done
qed


lemma word_lsb_sint: "lsb w \<longleftrightarrow> sint w mod 2 = 1"
  apply (subst word_sint_msb_eq)
  using mod_minus_cong[of _ 2 _ "uint w" _ 0 "uint w"]
  by (auto simp add: word_lsb_int)

lemma a_bit_AND_1_eq_0:
  fixes a :: "'x::len word"
  shows "a AND 1 = 0 \<longleftrightarrow> sint a mod 2 = 0"
proof-
  {
    assume "a AND 1 = 0"
    hence "\<not>lsb a"
      apply (auto simp add: word_lsb_alt )
      by (metis \<open>a AND 1 = 0\<close> lsb0 nth_0 test_bit_1)
    hence "sint a mod 2 \<noteq> 1"
      using word_lsb_sint[of a]
      by blast
    hence "sint a mod 2 = 0"
      by auto
  }
  moreover
  {
    assume "sint a mod 2 = 0"
    hence "\<not>lsb a"
      using word_lsb_sint[of a]
      by simp
    hence "a AND 1 = 0"
      apply (intro word_eqI)
      apply (auto simp add: word_lsb_alt word_size word_ao_nth)
      using gt_or_eq_0 by blast
  }
  ultimately
  show ?thesis
    by auto
qed

lemma take_bits_sshiftr:
  fixes a :: "64 word"
  assumes "\<forall> i \<ge> 31 . \<not> a !! i"
  shows "\<langle>31,0\<rangle>(a >>> n) = (\<langle>31,0\<rangle>a::32 word) >>> n"
  apply (intro word_eqI)
  using assms
  by (auto simp add: test_bit_of_take_bits word_size nth_sshiftr)

lemma take_bits_dereference_out_of_bounds:
  assumes "i \<ge> n * 8"
      and "no_block_overflow (a,n)"
  shows "\<not>(s \<turnstile> *[a,n]) !! i"
  unfolding read_region_def
  using assms
  by (auto simp add: test_bit_of_cat_bytes simp_rules Let'_def)

lemma sint_ucast:
  fixes a :: "'x::len word"
assumes "LENGTH('x) < LENGTH('y::len)"
shows "sint (ucast a:: 'y word) = uint a"
  apply (subst word_sint_msb_eq)
  using assms
  apply (auto simp add: is_up uint_up_ucast msb_nth nth_ucast)
  by (metis (mono_tags, hide_lams) One_nat_def  assms bin_nth_uint_imp diff_Suc_Suc len_num1 lens_not_0(2) minus_eq minus_nat.diff_0 not_less_eq old.nat.exhaust word_test_bit_def)




definition block2 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block2 s s' \<equiv> s' \<turnstile> *[rsp\<^sub>0 - 24,8] = (s \<turnstile> *[s \<turnstile> *[rsp\<^sub>0 - 24,8],8] :: 64 word)
                      \<and> (points_to s')\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) = (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824)
                      \<and> (\<forall> a' . (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) a' \<longrightarrow>
                               s' \<turnstile> *[24 + a',8] = (s \<turnstile> *[24 + a',8]::64 word)
                             \<and> s' \<turnstile> *[16 + a',2] = (s \<turnstile> *[16 + a',2]::16 word)
                             \<and> s' \<turnstile> *[a',8] = (s \<turnstile> *[a',8]::64 word))"

lemma sslServerCert_386_386_eq:
  assumes "(((P_386 || P_ret) && (\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 24,8] \<noteq> sslSocket_ptr\<^sub>0 + 824 \<and> regs s rip \<noteq> boffset + ret_address) && ! line ret_address)
            && (\<lambda> s . uint (s \<turnstile> *[16 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),2]::16 word) div 2 ^ unat (\<langle>7,0\<rangle>(s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)::8 word) mod 2 = 0)) s"
  shows "(block2 s && P_386) (The (((\<lambda>s. (=) (step s)) ; run_until_pred (lines {ret_address, 386})) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 386"
   and "RSP s = rsp\<^sub>0 - 8"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 36,4] = authType\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = namedCurve_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "\<not>flags s flag_zf"
   and "(points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) (s \<turnstile> *[rsp\<^sub>0 - 24,8])"
   and "\<forall> a . (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) a \<longrightarrow> master blocks (a,8) 3000 \<and> master blocks (16 + a,2) 3001 \<and> master blocks (24 + a,8) 3002"
   and "(s \<turnstile> *[rsp\<^sub>0 - 24,8] \<noteq> sslSocket_ptr\<^sub>0 + 824)"
   and "uint (s \<turnstile> *[16 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),2]::16 word) div 2 ^ unat (\<langle>7,0\<rangle>authType\<^sub>0::8 word) mod 2 = 0"
    using assms[unfolded P_386_def P_def]
    by (auto simp add: pred_logic simp_rules P_ret_def)
  note assms' = this

  have 1: "\<And> n a :: 64 word. no_block_overflow (a, 2) \<Longrightarrow> 
             (ucast (s \<turnstile> *[a,2] :: 16 word) >>> n) AND 1 = (0::32 word)
           \<longleftrightarrow> 
        (uint (s \<turnstile> *[a,2] :: 16 word) div 2 ^ n mod 2 = 0)"
    by (auto simp add: a_bit_AND_1_eq_0 simp_rules sint_ucast sshiftr_div_2n)

  have "master blocks (s \<turnstile> *[rsp\<^sub>0 - 24,8], 8) 3000"
        "master blocks (16 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),2) 3001"
        "master blocks (24 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),8) 3002"
    using assms'
    by auto
  note masters = masters this

  show ?thesis
    apply (insert assms' ret_address)
    apply (rewrite_one_step) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* sar *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* and *)
    apply (symbolic_execution masters: masters add: 1) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* nop *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (insert masters)
    subgoal premises prems
    proof-
      show ?thesis (is "(block2 s && P_386) (The (run_until_pred (lines {ret_address, 386}) ?s'))")
      proof-
        have 1: "(points_to ?s')\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) = (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824)"
          apply (rule ext)
          apply (subst points_to_eq[of s])
          apply (rule allI, rule impI)
          subgoal premises prems' for a b
            apply (insert assms'(11)[THEN spec,of b,THEN mp, OF prems'],clarsimp)
            apply (insert prems)
            apply (rewrite_one_let')+
            apply (simp (no_asm_simp) add: simp_rules)
            done     
          apply (simp add: field_simps)
          done
        show ?thesis
          apply (finish_symbolic_execution)
          apply (insert prems)
          apply (simp (no_asm_simp) add: block2_def)
          apply (rule conjI) 
          apply (rewrite_one_let')+
          apply simp
          apply (rule conjI) 
          apply (simp add: 1)
          apply (rule allI,rule impI)
          subgoal premises prems' for a'
          proof-
            have masters': "master blocks (a', 8) 3000" "master blocks (a' + 16, 2) 3001" "master blocks (a' + 24, 8) 3002"
              using prems'
              by (auto simp add: field_simps)
            thus ?thesis
              apply (insert prems masters')
              apply (rewrite_one_let')+
              by (simp)
          qed

          apply (simp (no_asm_simp) add: P_386_def)
          apply (rule conjI)
          apply (simp (no_asm_simp) add: P_def)
          apply (rewrite_one_let')+
          apply (auto simp add: simp_rules)[1]
          apply (auto simp add: simp_rules 1)[1]
          apply (rewrite_one_let' add: 1)+
          apply (auto simp add: field_simps)[1]
          apply (rewrite_one_let' add: 1)+
          apply (auto simp add: field_simps)[1]
          apply (rule rtranclp.rtrancl_into_rtrancl,simp, simp add: points_to_def)
          apply (rule rtranclp.rtrancl_into_rtrancl,simp, simp add: points_to_def)
          done
      qed
    qed
    done
qed


lemma sslServerCert_386_386_neq:
  assumes "((((P_386 || P_ret) && (\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 24,8] \<noteq> sslSocket_ptr\<^sub>0 + 824 \<and> regs s rip \<noteq> boffset + ret_address) && ! line ret_address)
            && ! (\<lambda> s .  uint (s \<turnstile> *[16 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),2]::16 word) div 2 ^ unat (\<langle>7,0\<rangle>(s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)::8 word) mod 2 = 0))
            && (\<lambda> s . 
                ucast (s \<turnstile> *[16 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),2]::16 word) AND 112 \<noteq> (0::32 word)
              \<and> namedCurve_ptr\<^sub>0 \<noteq> 0
              \<and> namedCurve_ptr\<^sub>0 \<noteq> s \<turnstile> *[24 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),8])) s"
  shows "(block2 s && P_386) (The (((\<lambda>s. (=) (step s)) ; run_until_pred (lines {ret_address, 386})) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 386"
   and "RSP s = rsp\<^sub>0 - 8"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 36,4] = authType\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = namedCurve_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "\<not>flags s flag_zf"
   and "(points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) (s \<turnstile> *[rsp\<^sub>0 - 24,8])"
   and "\<forall> a . (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) a \<longrightarrow> master blocks (a,8) 3000 \<and> master blocks (16 + a,2) 3001 \<and> master blocks (24 + a,8) 3002"
   and "(s \<turnstile> *[rsp\<^sub>0 - 24,8] \<noteq> sslSocket_ptr\<^sub>0 + 824)"
   and "uint (s \<turnstile> *[16 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),2]::16 word) div 2 ^ unat (\<langle>7,0\<rangle>authType\<^sub>0::8 word) mod 2 \<noteq> 0"
   and "ucast (s \<turnstile> *[16 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),2]::16 word) AND 112 \<noteq> (0::32 word)"
   and "namedCurve_ptr\<^sub>0 \<noteq> 0"
   and "namedCurve_ptr\<^sub>0 \<noteq> s \<turnstile> *[24 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),8]"
    using assms[unfolded P_386_def P_def]
    by (auto simp add: pred_logic simp_rules P_ret_def)
  note assms' = this

  hence "master blocks (s \<turnstile> *[rsp\<^sub>0 - 24,8], 8) 3000"
        "master blocks (16 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),2) 3001"
        "master blocks (24 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),8) 3002"
    using assms'
    by auto
  note masters = masters this


  have 1: "\<And> n a :: 64 word. no_block_overflow (a, 2) \<Longrightarrow> 
             (ucast (s \<turnstile> *[a,2] :: 16 word) >>> n) AND 1 = (0::32 word)
           \<longleftrightarrow> 
        (uint (s \<turnstile> *[a,2] :: 16 word) div 2 ^ n mod 2 = 0)"
    apply (subst a_bit_AND_1_eq_0)
     apply (subst sshiftr_div_2n)
    using masters
     apply (auto simp add: take_bits_dereference_out_of_bounds simp_rules)[1]
    by (auto simp add: simp_rules sint_ucast)


  show ?thesis
    apply (insert assms' ret_address)
    apply (rewrite_one_step) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* sar *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* and *)
    apply (symbolic_execution masters: masters add: 1) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* and *)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (symbolic_execution masters: masters) (* nop *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* add *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (insert masters)
    subgoal premises prems
    proof-
      show ?thesis (is "(block2 s && P_386) (The (run_until_pred (lines {ret_address, 386}) ?s'))")
      proof-
        have 1: "(points_to ?s')\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) = (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824)"
          apply (rule ext)
          apply (subst points_to_eq[of s])
          apply (rule allI, rule impI)
          subgoal premises prems' for a b
            apply (insert assms'(11)[THEN spec,of b,THEN mp, OF prems'],clarsimp)
            apply (insert prems)
            apply (rewrite_one_let')+
            apply (simp (no_asm_simp) add: simp_rules)
            done     
          apply (simp add: field_simps)
          done
        show ?thesis
          apply (finish_symbolic_execution)
          apply (insert prems)
          apply (simp (no_asm_simp) add: block2_def)
          apply (rule conjI) 
          apply (rewrite_one_let')+
          apply simp
          apply (rule conjI) 
          apply (simp add: 1)
          apply (rule allI,rule impI)
          subgoal premises prems' for a'
          proof-
            have masters': "master blocks (a', 8) 3000" "master blocks (a' + 16, 2) 3001" "master blocks (a' + 24, 8) 3002"
              using prems'
              by (auto simp add: field_simps)
            thus ?thesis
              apply (insert prems masters')
              apply (rewrite_one_let')+
              by (simp)
          qed

          apply (simp (no_asm_simp) add: P_386_def)
          apply (rule conjI)
          apply (simp (no_asm_simp) add: P_def)
          apply (rewrite_one_let')+
          apply (auto simp add: simp_rules)[1]
          apply (auto simp add: simp_rules 1)[1]
          apply (rewrite_one_let' add: 1)+
          apply (auto simp add: field_simps)[1]
          apply (rewrite_one_let' add: 1)+
          apply (auto simp add: field_simps)[1]
          apply (rule rtranclp.rtrancl_into_rtrancl,simp, simp add: points_to_def)
          apply (rule rtranclp.rtrancl_into_rtrancl,simp, simp add: points_to_def)
          done
      qed
    qed
    done
qed

definition block3 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block3 s s' \<equiv> RAX s' = s \<turnstile> *[rsp\<^sub>0 - 24,8] \<and> RIP s' = boffset + ret_address
                      \<and> s' \<turnstile> *[rsp\<^sub>0 - 24,8] = (s \<turnstile> *[rsp\<^sub>0 - 24,8] :: 64 word)
                      \<and> (points_to s')\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) = (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824)
                      \<and> (\<forall> a' . (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) a' \<longrightarrow>
                               s' \<turnstile> *[24 + a',8] = (s \<turnstile> *[24 + a',8]::64 word)
                             \<and> s' \<turnstile> *[16 + a',2] = (s \<turnstile> *[16 + a',2]::16 word)
                             \<and> s' \<turnstile> *[a',8] = (s \<turnstile> *[a',8]::64 word))"


lemma sslServerCert_386_ret:
  assumes "((((P_386 || P_ret) && (\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 24,8] \<noteq> sslSocket_ptr\<^sub>0 + 824 \<and> regs s rip \<noteq> boffset + ret_address) && ! line ret_address)
            && ! (\<lambda> s .  uint (s \<turnstile> *[16 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),2]::16 word) div 2 ^ unat (\<langle>7,0\<rangle>(s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)::8 word) mod 2 = 0))
            && ! (\<lambda> s . 
                ucast (s \<turnstile> *[16 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),2]::16 word) AND 112 \<noteq> (0::32 word)
              \<and> namedCurve_ptr\<^sub>0 \<noteq> 0
              \<and> namedCurve_ptr\<^sub>0 \<noteq> s \<turnstile> *[24 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),8])) s"
  shows "(block3 s && P_ret) (The (((\<lambda>s. (=) (step s)) ; run_until_pred (lines {ret_address, 386})) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 386"
   and "RSP s = rsp\<^sub>0 - 8"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 36,4] = authType\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = namedCurve_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "\<not>flags s flag_zf"
   and "(points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) (s \<turnstile> *[rsp\<^sub>0 - 24,8])"
   and "\<forall> a . (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) a \<longrightarrow> master blocks (a,8) 3000 \<and> master blocks (16 + a,2) 3001 \<and> master blocks (24 + a,8) 3002"
   and "(s \<turnstile> *[rsp\<^sub>0 - 24,8] \<noteq> sslSocket_ptr\<^sub>0 + 824)"
   and "uint (s \<turnstile> *[16 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),2]::16 word) div 2 ^ unat (\<langle>7,0\<rangle>authType\<^sub>0::8 word) mod 2 \<noteq> 0"
   and "ucast (s \<turnstile> *[16 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),2]::16 word) AND 112 = (0::32 word)
        \<or> namedCurve_ptr\<^sub>0 = 0
        \<or> namedCurve_ptr\<^sub>0 = s \<turnstile> *[24 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),8]"
    using assms[unfolded P_386_def P_def]
    by (auto simp add: pred_logic simp_rules P_ret_def line_def)
  note assms' = this

  hence "master blocks (s \<turnstile> *[rsp\<^sub>0 - 24,8], 8) 3000"
        "master blocks (16 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),2) 3001"
        "master blocks (24 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),8) 3002"
    using assms'
    by auto
  note masters = masters this


  have 1: "\<And> n a :: 64 word. no_block_overflow (a, 2) \<Longrightarrow> 
             (ucast (s \<turnstile> *[a,2] :: 16 word) >>> n) AND 1 = (0::32 word)
           \<longleftrightarrow> 
        (uint (s \<turnstile> *[a,2] :: 16 word) div 2 ^ n mod 2 = 0)"
    apply (subst a_bit_AND_1_eq_0)
    apply (subst sshiftr_div_2n)
    using masters
    apply (auto simp add: take_bits_dereference_out_of_bounds simp_rules)[1]
    by (auto simp add: simp_rules sint_ucast)


  show ?thesis
    apply (insert assms' ret_address)
    apply (rewrite_one_step) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* sar *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* and *)
    apply (symbolic_execution masters: masters add: 1) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* and *)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* pop *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (insert masters)
    subgoal premises prems
    proof-
      show ?thesis (is "(block3 s && P_ret) (The (run_until_pred (lines {ret_address, 386}) ?s'))")
      proof-
        have 1: "(points_to ?s')\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) = (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824)"
          apply (rule ext)
          apply (subst points_to_eq[of s])
          apply (rule allI, rule impI)
          subgoal premises prems' for a b
            apply (insert assms'(11)[THEN spec,of b,THEN mp, OF prems'],clarsimp)
            apply (insert prems)
            apply (rewrite_one_let')+
            apply (simp (no_asm_simp) add: simp_rules)
            done     
          apply (simp add: field_simps)
          done
        show ?thesis
          apply (finish_symbolic_execution)
          apply (insert prems)
          apply (simp (no_asm_simp) add: block3_def)
          apply (rule conjI) 
          apply (rewrite_one_let')+
          apply simp
          apply (rule conjI) 
          apply (simp add: 1)
          apply (rule allI,rule impI)
          subgoal premises prems' for a'
          proof-
            have masters': "master blocks (a', 8) 3000" "master blocks (a' + 16, 2) 3001" "master blocks (a' + 24, 8) 3002"
              using prems'
              by (auto simp add: field_simps)
            thus ?thesis
              apply (insert prems masters')
              apply (rewrite_one_let')+
              by (simp)
          qed

          by (simp (no_asm_simp) add: P_ret_def)
      qed
    qed
          
          
          
    apply (rewrite_one_let')+
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* pop *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (insert masters)
    subgoal premises prems
    proof-
      show ?thesis (is "(block3 s && P_ret) (The (run_until_pred (lines {ret_address, 386}) ?s'))")
      proof-
        have 1: "(points_to ?s')\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) = (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824)"
          apply (rule ext)
          apply (subst points_to_eq[of s])
          apply (rule allI, rule impI)
          subgoal premises prems' for a b
            apply (insert assms'(11)[THEN spec,of b,THEN mp, OF prems'],clarsimp)
            apply (insert prems)
            apply (rewrite_one_let')+
            apply (simp (no_asm_simp) add: simp_rules)
            done     
          apply (simp add: field_simps)
          done
        show ?thesis
          apply (finish_symbolic_execution)
          apply (insert prems)
          apply (simp (no_asm_simp) add: block3_def)
          apply (rule conjI) 
          apply (rewrite_one_let')+
          apply simp
          apply (rule conjI) 
          apply (simp add: 1)
          apply (rule allI,rule impI)
          subgoal premises prems' for a'
          proof-
            have masters': "master blocks (a', 8) 3000" "master blocks (a' + 16, 2) 3001" "master blocks (a' + 24, 8) 3002"
              using prems'
              by (auto simp add: field_simps)
            thus ?thesis
              apply (insert prems masters')
              apply (rewrite_one_let')+
              by (simp)
          qed

          by (simp (no_asm_simp) add: P_ret_def)
      qed
    qed


    apply (rewrite_one_let')+
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* pop *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (insert masters)
    subgoal premises prems
    proof-
      show ?thesis (is "(block3 s && P_ret) (The (run_until_pred (lines {ret_address, 386}) ?s'))")
      proof-
        have 1: "(points_to ?s')\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) = (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824)"
          apply (rule ext)
          apply (subst points_to_eq[of s])
          apply (rule allI, rule impI)
          subgoal premises prems' for a b
            apply (insert assms'(11)[THEN spec,of b,THEN mp, OF prems'],clarsimp)
            apply (insert prems)
            apply (rewrite_one_let')+
            apply (simp (no_asm_simp) add: simp_rules)
            done     
          apply (simp add: field_simps)
          done
        show ?thesis
          apply (finish_symbolic_execution)
          apply (insert prems)
          apply (simp (no_asm_simp) add: block3_def)
          apply (rule conjI) 
          apply (rewrite_one_let')+
          apply simp
          apply (rule conjI) 
          apply (simp add: 1)
          apply (rule allI,rule impI)
          subgoal premises prems' for a'
          proof-
            have masters': "master blocks (a', 8) 3000" "master blocks (a' + 16, 2) 3001" "master blocks (a' + 24, 8) 3002"
              using prems'
              by (auto simp add: field_simps)
            thus ?thesis
              apply (insert prems masters')
              apply (rewrite_one_let')+
              by (simp)
          qed

          by (simp (no_asm_simp) add: P_ret_def)
      qed
    qed
    done
qed


definition block4 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block4 s s' \<equiv> (RIP s \<noteq> boffset + ret_address \<longrightarrow> RAX s' = 0) \<and> RIP s' = boffset + ret_address"

lemma sslServerCert_386_ret2:
  assumes "((P_386 || P_ret) &&
              ! ((\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 24,8] \<noteq> sslSocket_ptr\<^sub>0 + 824 \<and> regs s rip \<noteq> boffset + ret_address) && ! line ret_address)) s"
  shows "(block4 s && P_ret) (The ((run_until_pred (line ret_address)) s))"
proof(cases "RIP s = boffset + ret_address")
  case True
  hence 1: "P_ret s"
    using assms
    using ret_address
    by (auto simp add: pred_logic P_386_def P_def)
  show ?thesis
    apply (insert True)
    apply (finish_symbolic_execution)
    using 1
    by (auto simp add: block4_def P_ret_def)
next
  case False
  hence "seps blocks"
   and "RIP s = boffset + 386"
   and "RSP s = rsp\<^sub>0 - 8"
   and "RBP s = rsp\<^sub>0 - 8"
   and "s \<turnstile> *[rsp\<^sub>0 - 32,8] = sslSocket_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 36,4] = authType\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 48,8] = namedCurve_ptr\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "(points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) (s \<turnstile> *[rsp\<^sub>0 - 24,8])"
   and "\<forall> a . (points_to s)\<^sup>*\<^sup>* (sslSocket_ptr\<^sub>0 + 824) a \<longrightarrow> master blocks (a,8) 3000 \<and> master blocks (16 + a,2) 3001 \<and> master blocks (24 + a,8) 3002"
   and "(s \<turnstile> *[rsp\<^sub>0 - 24,8] = sslSocket_ptr\<^sub>0 + 824)"
   and "flags s flag_zf"
    using assms[unfolded P_386_def P_def] ret_address
    by (auto simp add: pred_logic line_def P_ret_def)
  note assms' = this

  show ?thesis
    apply (insert assms' ret_address)
    apply (symbolic_execution masters: masters) (* jne *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* pop *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block4_def)
    apply (simp (no_asm_simp) add: P_ret_def)
    done
qed



definition PRCList_get :: "PRCList \<Rightarrow> 64 word \<Rightarrow> PRC"
  where "PRCList_get x ID \<equiv> The (\<lambda> p . p \<in> PRCList_elts x \<and> PRC_ID p = ID)"

definition PRCList_get_curr :: "PRCList \<Rightarrow> PRC"
  where "PRCList_get_curr x \<equiv> PRCList_get x (PRCList_curr x)"

definition PRCList_next :: "PRCList \<Rightarrow> PRCList"
  where "PRCList_next x \<equiv> x \<lparr> PRCList_curr := PRC_next (PRCList_get_curr x)\<rparr>"

lemma PRCList_next:
  assumes "a \<in> elts"
  shows "PRCList_next \<lparr>PRCList_curr = a, PRCList_elts = read_PRC s ` elts\<rparr> =
          \<lparr>PRCList_curr = PRC_next (read_PRC s a), PRCList_elts = read_PRC s ` elts\<rparr>"
proof-
  have "(THE p. p \<in> read_PRC s ` elts \<and> PRC_ID p = a) = read_PRC s a"
    apply (rule the1_equality)
    using assms
    by (auto simp add: read_PRC_def)
  thus ?thesis
    by (auto simp add: PRCList_next_def PRCList_get_def PRCList_get_curr_def)
qed

lemma PRCList_get_curr:
  assumes "a \<in> elts"
  shows "PRCList_get_curr \<lparr>PRCList_curr = a, PRCList_elts = read_PRC s ` elts\<rparr> = read_PRC s a"
proof-
  have "(THE p. p \<in> read_PRC s ` elts \<and> PRC_ID p = a) = read_PRC s a"
    apply (rule the1_equality)
    using assms
    by (auto simp add: read_PRC_def)
  thus ?thesis
    by (auto simp add: PRCList_next_def PRCList_get_def PRCList_get_curr_def)
qed


lemma read_PRC_eqI:
  assumes "\<forall> a' \<in> a . s' \<turnstile> *[24 + a',8] = (s \<turnstile> *[24 + a', 8] :: 64 word) \<and> s' \<turnstile> *[16 + a',2] = (s \<turnstile> *[16 + a', 2] :: 16 word) \<and> s' \<turnstile> *[a',8] = (s \<turnstile> *[a', 8] :: 64 word)"
  shows "read_PRC s' ` a = read_PRC s ` a"
  using assms
  apply (auto simp add: read_PRC_def)
  apply (rule rev_image_eqI)
  by (auto simp add: read_PRC_def)

definition abstract_sslServerCert :: "sslServerCert_state \<times> '\<sigma>\<^sub>C sslServerCert_caller_state_scheme \<Rightarrow> sslServerCert_state \<times> '\<sigma>\<^sub>C sslServerCert_caller_state_scheme \<Rightarrow> bool"
  where "abstract_sslServerCert \<equiv> 
          (\<lambda> \<sigma> \<sigma>' . cursor\<^sub>v (\<L> \<sigma>') = PRCList_next (serverCerts (sslSocket\<^sub>v (\<C> \<sigma>)))) ;
          WHILE (\<lambda> \<sigma> . \<not>exited\<^sub>v (\<L> \<sigma>) 
                  \<and> PRCList_curr (cursor\<^sub>v (\<L> \<sigma>)) \<noteq> PRCList_curr (serverCerts (sslSocket\<^sub>v (\<C> \<sigma>))))
          DO
            IF (\<lambda> \<sigma> . uint (PRC_y (PRCList_get_curr (cursor\<^sub>v (\<L> \<sigma>)))) div 2 ^ unat (\<langle>7,0\<rangle>authType\<^sub>0::8 word) mod 2 = 0) THEN
              (\<lambda> \<sigma> \<sigma>' . cursor\<^sub>v (\<L> \<sigma>') = PRCList_next (cursor\<^sub>v (\<L> \<sigma>)))
            ELSE IF (\<lambda> \<sigma>. ucast (PRC_y (PRCList_get_curr (cursor\<^sub>v (\<L> \<sigma>)))) AND 112 \<noteq> (0::32 word)
                        \<and> namedCurve_ptr\<^sub>0 \<noteq> 0
                        \<and> namedCurve_ptr\<^sub>0 \<noteq> PRC_x (PRCList_get_curr (cursor\<^sub>v (\<L> \<sigma>)))) THEN 
              (\<lambda> \<sigma> \<sigma>' . cursor\<^sub>v (\<L> \<sigma>') = PRCList_next (cursor\<^sub>v (\<L> \<sigma>)))
            ELSE 
              (\<lambda> \<sigma> \<sigma>' . exited\<^sub>v (\<L> \<sigma>')
                      \<and> ret\<^sub>v (\<C> \<sigma>') = (if PRC_ID (PRCList_get_curr (cursor\<^sub>v (\<L> \<sigma>))) = 0 then None else Some (cursor\<^sub>v (\<L> \<sigma>))))
            FI FI
          OD ;
          (\<lambda> \<sigma> \<sigma>' . exited\<^sub>v (\<L> \<sigma>') \<and> (\<not>exited\<^sub>v (\<L> \<sigma>) \<longrightarrow> ret\<^sub>v (\<C> \<sigma>') = None))"

lemma sslServerCert_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {386, ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 386"])
  apply (simp add: line_simps)
  done

lemma sslServerCert:
  shows "S ::
         {P_245}
            run_until_pred (line ret_address) \<preceq> abstract_sslServerCert   
         {P_ret}"
  apply (subst abstract_sslServerCert_def)
  apply (subst sslServerCert_decompose)
  apply (rule HL_compose[where Q="P_386 || P_ret"])
  apply (rule strengthen[of "P_386"])
  apply (simp add: pred_logic)
  apply (rule HL_equality_intro)
  apply (erule sslServerCert_245_386)
  apply (auto simp add: S_def read_sslSocket_def block1_def read_PRCList_def PRCList_next read_PRC_def read_PRC_eqI)[1]
  apply (rule HL_while_v2[where B="\<lambda>s. s \<turnstile> *[rsp\<^sub>0 - 24,8] \<noteq> sslSocket_ptr\<^sub>0 + 824 \<and> RIP s \<noteq> boffset + ret_address" and F'="line 386"])
  apply (auto simp add: S_def read_PRCList_def read_sslSocket_def pred_logic line_def)[1]
  apply (rule HL_equality_intro)
  apply (erule sslServerCert_386_ret2)
  using ret_address apply (auto simp add: block4_def S_def pred_logic P_386_def P_def)[1]
  apply (simp add: line_simps)
  apply (rule HL_ITE[where B="\<lambda> s . uint (s \<turnstile> *[16 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),2]::16 word) div 2 ^ unat (\<langle>7,0\<rangle>(s \<turnstile> *[rsp\<^sub>0 - 36,4]::32 word)::8 word) mod 2 = 0"])
  apply (auto simp add: S_def read_PRCList_def PRCList_get_curr pred_logic P_386_def read_PRC_def P_def line_def P_ret_def)[1]
  apply (rule strengthen[of "P_386"])
  apply (simp add: pred_logic)
  apply (rule HL_equality_intro_step)
  apply (erule sslServerCert_386_386_eq)
  apply (auto simp add: S_def read_sslSocket_def block2_def read_PRCList_def PRCList_next read_PRC_def read_PRC_eqI P_386_def pred_logic P_ret_def line_def)[1]
  apply (rule HL_ITE[where B="\<lambda> s . 
                ucast (s \<turnstile> *[16 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),2]::16 word) AND 112 \<noteq> (0::32 word)
              \<and> namedCurve_ptr\<^sub>0 \<noteq> 0
              \<and> namedCurve_ptr\<^sub>0 \<noteq> s \<turnstile> *[24 + (s \<turnstile> *[rsp\<^sub>0 - 24,8]),8]"])
  apply (auto simp add: S_def PRCList_get_curr read_PRCList_def P_386_def pred_logic read_PRC_def line_def P_ret_def)[1]
  apply (rule strengthen[of "P_386"])
  apply (simp add: pred_logic)
  apply (rule HL_equality_intro_step)
  apply (erule sslServerCert_386_386_neq)
  apply (auto simp add: S_def read_sslSocket_def block2_def read_PRCList_def PRCList_next read_PRC_def read_PRC_eqI P_386_def pred_logic P_ret_def line_def)[1]
  apply (rule strengthen[of "P_ret"])
  apply (simp add: pred_logic)
  apply (rule HL_equality_intro_step)
  apply (erule sslServerCert_386_ret)
  apply (auto simp add: S_def read_sslSocket_def block3_def read_PRCList_def PRCList_next read_PRC_def read_PRC_eqI PRCList_get_curr P_386_def pred_logic P_ret_def line_def)[1]
  done


(* END FUNCTION sslServerCert *)

end
