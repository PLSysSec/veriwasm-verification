theory Palindrome
  imports "../../isabelle/Det_Step"
          "../../isabelle/Read_Array"
          "../../isabelle/Presimplified_Semantics_Manual2"
begin


text \<open>Load the palindrome.s file.\<close>
x86_64_parser "../examples/palindrome/palindrome.s"

lemmas palindrome.assembly_def [code]


record astate =
  ret :: "32 word"
  cs_arr :: "8 word list"
  ct_arr :: "8 word list"

record strncmp_state =
  c1 :: "8 word"
  c2 :: "8 word"
  cs' :: "64 word"
  ct' :: "64 word"
  count :: "64 word"
  breaked :: bool
  ret'd :: bool

locale palindrome_context = palindrome + presimplified_semantics +
  assumes funcs_def: "funcs \<equiv> \<lambda> _ . None"
begin

abbreviation "\<alpha> \<equiv> assembly"

schematic_goal unfold_semantics:
  shows \<open>instr_semantics semantics instr_sig = ?x\<close>
  by (simp add: semantics_def simp_rules)

lemma binary_offset[simp]:
  shows "binary_offset assembly = boffset"
  by (simp add: assembly_def assembly.defs)
schematic_goal unfold_labels[simp]:
  shows "label_to_address assembly = ?x"
  apply (rule ext)
  apply (unfold label_to_address_def)
  apply (unfold binary_offset)
  by (auto simp add: label_to_address_def assembly_def assembly.defs)

fun palindrome_flag_annotation :: flag_annotation where
  \<open>palindrome_flag_annotation loc = (if loc \<in> {boffset + 58, boffset + 86, boffset + 99} then {flag_zf} else
                                     if loc \<in> {boffset + 67} then {flag_cf}
                                     else {})\<close>


definition step :: \<open>state \<Rightarrow> state\<close> where
  \<open>step s \<equiv>
    let  pc = get_rip s;
         index = the (instr_index lookup_table boffset pc) in
    let' (_,i,si) = (text_sections \<alpha>)!index;
         s = exec_instr \<alpha> semantics palindrome_flag_annotation i si s
    in
      s\<close>

definition line :: "64 word \<Rightarrow> state \<Rightarrow> bool" where
  "line n \<sigma> \<equiv> get_rip \<sigma> = boffset + n"

definition lines :: "64 word set \<Rightarrow> state \<Rightarrow> bool" where
  "lines N \<sigma> \<equiv> \<exists> n \<in> N . line n \<sigma>"

lemma line_OR_line:
  shows "(line n || line m) = lines {n,m}"
  unfolding pred_OR_def lines_def
  by auto

lemma line_OR_lines:
  shows "(line n || lines N) = lines ({n} \<union> N)"
  unfolding pred_OR_def lines_def
  by auto

lemma lines_OR_lines:
  shows "(lines N || lines M) = lines (N \<union> M)"
  unfolding pred_OR_def lines_def
  by auto

lemma lines_OR_line:
  shows "(lines N || line n) = lines (N \<union> {n})"
  unfolding pred_OR_def lines_def
  by auto

lemmas line_simps = line_OR_line line_OR_lines lines_OR_lines lines_OR_line insert_commute


sublocale det_step step get_rip .


method rewrite_one_step uses masters add del =
  (subst step_seq_run)?,
  (simp (no_asm_simp) add: add step_def lookup_table_def instr_index_def entry_size_def del: del),
  (rewrite_one_let' del: del add: add assembly_def),
  (simp add: exec_instr_def),
  (subst presimplify),
  (rewrite_one_let' del: del add: add),
  (subst is_manual),
  ((insert masters)[1]),
  (rewrite_one_let' del: del add: add)+,
  (thin_tac \<open>master _ _ _\<close>)+

method symbolic_execution uses masters add del =
    (* unfold one step *)
    (subst run_until_pred_step[symmetric]),
    (* show that we are not at the end *)
    (simp add: lines_def at_loc_def pred_OR_def line_def; (unat_arith; ((auto simp add: unat_of_nat)[1])?)?),
    (* rewrite one step *)
    rewrite_one_step masters: masters add: add del: del

method finish_symbolic_execution =
    (* Stop at the current state *)
    subst run_until_pred_stop,
    (* Show that we are at the end. Otherwise, fail *)
    (determ \<open>(simp add: lines_def at_loc_def pred_OR_def line_def; (unat_arith; ((auto simp add: unat_of_nat)[1])?)?)\<close> ; fail),
    (* Simplify and split the current subgoal *)
    (simp (no_asm_simp) add: pred_logic simp_rules),
    ((rule ifI | rule conjI | rule impI)+)?


definition P_0 :: "('a::len0 word) itself \<Rightarrow> _"
  where "P_0 a blocks cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address s \<equiv>
      seps blocks
    \<and> (8, cs\<^sub>0, unat count\<^sub>0) \<in> blocks
    \<and> (8, ct\<^sub>0, unat count\<^sub>0) \<in> blocks
    \<and> master blocks (regs s rsp, 8) 1
    \<and> master blocks (regs s rsp - 8, 8) 2
    \<and> master blocks (regs s rsp - 9, Suc 0) 3
    \<and> master blocks (regs s rsp - 10, Suc 0) 4
    \<and> master blocks (regs s rsp - 32, 8) 5
    \<and> master blocks (regs s rsp - 40, 8) 6
    \<and> master blocks (regs s rsp - 48, 8) 7
    \<and> RDI s = cs\<^sub>0
    \<and> RSI s = ct\<^sub>0
    \<and> RDX s = count\<^sub>0
    \<and> RIP s = boffset
    \<and> s \<turnstile> *[RSP s,8] = boffset + ret_address
    \<and> ret_address > 150
    \<and> unat count\<^sub>0 * 8 \<le> LENGTH('a)"

definition P_104_92_111 :: "('a::len0 word) itself \<Rightarrow> _"
  where "P_104_92_111 a blocks cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address s \<equiv>
      seps blocks
    \<and> (8, cs\<^sub>0, unat count\<^sub>0) \<in> blocks
    \<and> (8, ct\<^sub>0, unat count\<^sub>0) \<in> blocks
    \<and> master blocks (regs s rsp + 8, 8) 1
    \<and> master blocks (regs s rsp, 8) 2
    \<and> master blocks (regs s rsp - 1, Suc 0) 3
    \<and> master blocks (regs s rsp - 2, Suc 0) 4
    \<and> master blocks (regs s rsp - 24, 8) 5
    \<and> master blocks (regs s rsp - 32, 8) 6
    \<and> master blocks (regs s rsp - 40, 8) 7
    \<and> (RIP s = boffset + 104 \<longrightarrow>
            (read_flg s flag_zf = (s \<turnstile> *[RSP s - 40,8] = (0::64 word))
              \<and> (s \<turnstile> *[regs s rsp - 24,8]) = (count\<^sub>0 + cs\<^sub>0 - (s \<turnstile> *[regs s rsp - 40,8]) :: 64 word)
              \<and> (s \<turnstile> *[regs s rsp - 32,8]) = (count\<^sub>0 + ct\<^sub>0 - (s \<turnstile> *[regs s rsp - 40,8]) :: 64 word)))
    \<and> RIP s \<in> {boffset + 104, boffset + 92, boffset + 111}
    \<and> RBP s = RSP s
    \<and> s \<turnstile> *[RSP s + 8,8] = boffset + ret_address
    \<and> ret_address > 150
    \<and> (s \<turnstile> *[regs s rsp - 40,8]) \<le> count\<^sub>0
    \<and> unat count\<^sub>0 * 8 \<le> LENGTH('a)"

definition P_61 :: "('a::len0 word) itself \<Rightarrow> _"
  where "P_61 a blocks cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address s \<equiv>
  let' cs = s \<turnstile> *[regs s rsp - 24,8];
       ct = s \<turnstile> *[regs s rsp - 32,8];
       count = s \<turnstile> *[regs s rsp - 40,8]
  in
      seps blocks
    \<and> (8, cs\<^sub>0, unat count\<^sub>0) \<in> blocks
    \<and> (8, ct\<^sub>0, unat count\<^sub>0) \<in> blocks
    \<and> master blocks (regs s rsp + 8, 8) 1
    \<and> master blocks (regs s rsp, 8) 2
    \<and> master blocks (regs s rsp - 1, Suc 0) 3
    \<and> master blocks (regs s rsp - 2, Suc 0) 4
    \<and> master blocks (regs s rsp - 24, 8) 5
    \<and> master blocks (regs s rsp - 32, 8) 6
    \<and> master blocks (regs s rsp - 40, 8) 7
    \<and> RIP s = boffset + 61
    \<and> RBP s = RSP s
    \<and> s \<turnstile> *[RSP s + 8,8] = boffset + ret_address
    \<and> ret_address > 150
    \<and> cs = (count\<^sub>0 + cs\<^sub>0 - count) + 1
    \<and> ct = (count\<^sub>0 + ct\<^sub>0 - count) + 1
    \<and> count \<noteq> (0::64 word)
    \<and> count \<le> count\<^sub>0
    \<and> flags s flag_zf = (s \<turnstile> *[cs - 1,1] = (s \<turnstile> *[ct - 1,1] :: 8 word))
    \<and> unat count\<^sub>0 * 8 \<le> LENGTH('a)"


definition P_106_ret :: "('a::len0 word) itself \<Rightarrow> _"
  where "P_106_ret a blocks cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address s \<equiv>
      seps blocks
    \<and> (8, cs\<^sub>0, unat count\<^sub>0) \<in> blocks
    \<and> (8, ct\<^sub>0, unat count\<^sub>0) \<in> blocks
    \<and> unat count\<^sub>0 * 8 \<le> LENGTH('a)
    \<and> ret_address > 150
    \<and> (if RIP s = boffset + 106 then
           RBP s = RSP s
        \<and> master blocks (regs s rsp + 8, 8) 1
        \<and> s \<turnstile> *[RSP s + 8,8] = boffset + ret_address
       else
         RIP s = boffset + ret_address)"

definition P_ret
  where "P_ret ret_address s \<equiv>
      RIP s = boffset + ret_address"

definition block1 :: "('a::len0 word) itself \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  where "block1 a cs\<^sub>0 ct\<^sub>0 count\<^sub>0 s s' \<equiv>
        s' \<turnstile> *[RSP s' - 40, 8] = count\<^sub>0
      \<and> s' \<turnstile> *[RSP s' - 24,8] = cs\<^sub>0
      \<and> s' \<turnstile> *[RSP s' - 32,8] = ct\<^sub>0
      \<and> RIP s' = boffset + 104
      \<and> (unat count\<^sub>0 > 0 \<longrightarrow> s' \<turnstile> *[cs\<^sub>0,unat count\<^sub>0] = (s \<turnstile> *[cs\<^sub>0,unat count\<^sub>0] :: 'a::len0 word))
      \<and> (unat count\<^sub>0 > 0 \<longrightarrow> s' \<turnstile> *[ct\<^sub>0,unat count\<^sub>0] = (s \<turnstile> *[ct\<^sub>0,unat count\<^sub>0] :: 'a::len0 word))"

definition block2 :: "('a::len0 word) itself \<Rightarrow> 64 word \<Rightarrow> 64 word => 64 word \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  where "block2 a cs\<^sub>0 ct\<^sub>0 count\<^sub>0 s s' \<equiv>
          s' \<turnstile> *[RSP s' - 24, 8] = (1 + (s \<turnstile> *[regs s rsp - 24,8]) :: 64 word)
        \<and> s' \<turnstile> *[RSP s' - 32, 8] = (1 + (s \<turnstile> *[regs s rsp - 32,8]) :: 64 word)
        \<and> s' \<turnstile> *[RSP s' - 2,1] = (s \<turnstile> *[s \<turnstile> *[regs s rsp - 24,8],1] :: 8 word)
        \<and> s' \<turnstile> *[RSP s' - 1,1] = (s \<turnstile> *[s \<turnstile> *[regs s rsp - 32,8],1] :: 8 word)
        \<and> s' \<turnstile> *[RSP s' - 40, 8] = (s \<turnstile> *[regs s rsp - 40,8] :: 64 word)
        \<and> s' \<turnstile> *[cs\<^sub>0,unat count\<^sub>0] = (s \<turnstile> *[cs\<^sub>0,unat count\<^sub>0] :: 'a::len0 word)
        \<and> s' \<turnstile> *[ct\<^sub>0,unat count\<^sub>0] = (s \<turnstile> *[ct\<^sub>0,unat count\<^sub>0] :: 'a::len0 word)"

definition block3 :: "('a::len0 word) itself \<Rightarrow> 64 word \<Rightarrow> 64 word => 64 word \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  where "block3 a cs\<^sub>0 ct\<^sub>0 count\<^sub>0 s s' \<equiv>
          (if s \<turnstile> *[(s \<turnstile> *[regs s rsp - 24,8]) - 1,Suc 0] \<noteq> (s \<turnstile> *[(s \<turnstile> *[regs s rsp - 32,8]) - 1,Suc 0] :: 8 word) then
              EAX s' = (if s \<turnstile> *[RSP s - 2,1] < (s \<turnstile> *[RSP s - 1,1] :: 8 word) then 4294967295 else 1) \<and>
              RIP s' = boffset + 111 \<and>
              s' \<turnstile> *[RSP s' - 40, 8] = (s \<turnstile> *[regs s rsp - 40,8] :: 64 word)
          else if s \<turnstile> *[RSP s - 2,1] = (0::8 word) then
              RIP s' = boffset + 92 \<and>
              s' \<turnstile> *[RSP s' - 40, 8] = (s \<turnstile> *[regs s rsp - 40,8] :: 64 word)
          else
              s' \<turnstile> *[RSP s' - 40, 8] = (s \<turnstile> *[RSP s  - 40, 8] :: 64 word) - 1 \<and>
              RIP s' = boffset + 104)
        \<and> s' \<turnstile> *[RSP s' - 24, 8] = ((s \<turnstile> *[regs s rsp - 24,8]) :: 64 word)
        \<and> s' \<turnstile> *[RSP s' - 32, 8] = ((s \<turnstile> *[regs s rsp - 32,8]) :: 64 word)
        \<and> s' \<turnstile> *[cs\<^sub>0,unat count\<^sub>0] = (s \<turnstile> *[cs\<^sub>0,unat count\<^sub>0] :: 'a::len0 word)
        \<and> s' \<turnstile> *[ct\<^sub>0,unat count\<^sub>0] = (s \<turnstile> *[ct\<^sub>0,unat count\<^sub>0] :: 'a::len0 word)"

definition block4 :: "('a::len0 word) itself \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  where "block4 a cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address s s' \<equiv>
          RIP s' = (if RIP s = boffset + 111 then boffset + ret_address else boffset + 106)
        \<and> EAX s' = EAX s
        \<and> s' \<turnstile> *[cs\<^sub>0,unat count\<^sub>0] = (s \<turnstile> *[cs\<^sub>0,unat count\<^sub>0] :: 'a::len0 word)
        \<and> s' \<turnstile> *[ct\<^sub>0,unat count\<^sub>0] = (s \<turnstile> *[ct\<^sub>0,unat count\<^sub>0] :: 'a::len0 word)"

definition block5 :: "('a::len0 word) itself \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  where "block5 a cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address s s' \<equiv>
          (if RIP s = boffset + ret_address then
            s' = s
          else
            RIP s' = boffset + ret_address \<and> EAX s' = 0)
        \<and> s' \<turnstile> *[cs\<^sub>0,unat count\<^sub>0] = (s \<turnstile> *[cs\<^sub>0,unat count\<^sub>0] :: 'a::len0 word)
        \<and> s' \<turnstile> *[ct\<^sub>0,unat count\<^sub>0] = (s \<turnstile> *[ct\<^sub>0,unat count\<^sub>0] :: 'a::len0 word)"

lemma palindrome_0_104:
  assumes "P_0 a blocks cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address s"
  shows "(block1 a cs\<^sub>0 ct\<^sub>0 count\<^sub>0 s && P_104_92_111 a blocks cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address) (The (run_until_pred (lines {104, 106, ret_address}) s))"
proof-
  have "seps blocks"
   and "get_rip s = boffset"
   and "ret_address > 150"
   and "s \<turnstile> *[regs s rsp,8] = boffset + ret_address"
   and "RDI s = cs\<^sub>0"
   and "RSI s = ct\<^sub>0"
   and "RDX s = count\<^sub>0"
   and "(8, cs\<^sub>0, unat count\<^sub>0) \<in> blocks"
   and "(8, ct\<^sub>0, unat count\<^sub>0) \<in> blocks"
   and "unat count\<^sub>0 * 8 \<le> LENGTH('a)"
    using assms[unfolded P_0_def]
    by simp+
  note assms' = this

  have 0: "master blocks (cs\<^sub>0, unat count\<^sub>0) 8"
   and 00: "master blocks (ct\<^sub>0, unat count\<^sub>0) 8"
    by (find_master assms: assms')+
  have \<open>master blocks (regs s rsp, 8) 1\<close>
   and \<open>master blocks (regs s rsp - 8, 8) 2\<close>
   and \<open>master blocks (regs s rsp - 9, 1) 3\<close>
   and \<open>master blocks (regs s rsp - 10, 1) 4\<close>
   and \<open>master blocks (regs s rsp - 32, 8) 5\<close>
   and \<open>master blocks (regs s rsp - 40, 8) 6\<close>
   and \<open>master blocks (regs s rsp - 48, 8) 7\<close>
    using assms[unfolded P_0_def]
    by simp+
  note masters = this and 0 and 00
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)

    apply (finish_symbolic_execution)
    apply (simp add: block1_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (simp add: P_104_92_111_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    done
qed


lemma palindrome_104_to_61:
assumes "((P_104_92_111 a blocks cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address) && (\<lambda> s . \<not> flags s flag_zf \<and> line 104 s)) s"
  shows "(block2 a cs\<^sub>0 ct\<^sub>0 count\<^sub>0 s && P_61 a blocks cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address) (The (((\<lambda>s. (=) (step s)) ; run_until_pred (lines {ret_address, 61, 104, 92, 106, 111})) s))"
proof-
  have "seps blocks"
   and "(8, cs\<^sub>0, unat count\<^sub>0) \<in> blocks"
   and "(8, ct\<^sub>0, unat count\<^sub>0) \<in> blocks"
   and "RIP s = boffset + 104"
   and "RBP s = RSP s"
   and "s \<turnstile> *[RSP s + 8,8] = boffset + ret_address"
   and "ret_address > 150"
   and "\<not> flags s flag_zf"
   and "(s \<turnstile> *[RSP s - 40,8] \<noteq> (0::64 word))"
   and "(s \<turnstile> *[regs s rsp - 24,8]) + (s \<turnstile> *[regs s rsp - 40,8]) = count\<^sub>0 + cs\<^sub>0"
   and "(s \<turnstile> *[regs s rsp - 32,8]) + (s \<turnstile> *[regs s rsp - 40,8]) = count\<^sub>0 + ct\<^sub>0"
   and "(s \<turnstile> *[regs s rsp - 40,8]) \<le> count\<^sub>0"
   and "unat count\<^sub>0 * 8 \<le> LENGTH('a)"
    using assms[unfolded P_104_92_111_def]
    by (auto simp add: pred_logic line_def read_flg_def get_def)
  note assms' = this

  
  have \<open>master blocks (regs s rsp + 8, 8) 1\<close>
   and \<open>master blocks (regs s rsp, 8) 2\<close>
   and \<open>master blocks (regs s rsp - 1, Suc 0) 3\<close>
   and \<open>master blocks (regs s rsp - 2, Suc 0) 4\<close>
   and \<open>master blocks (regs s rsp - 24, 8) 5\<close>
   and \<open>master blocks (regs s rsp - 32, 8) 6\<close>
   and \<open>master blocks (regs s rsp - 40, 8) 7\<close>
    using assms[unfolded P_104_92_111_def]
    by (simp add: pred_logic)+
  note masters = this
  have 0: "master blocks (cs\<^sub>0, unat count\<^sub>0) 8"
   and 00: "master blocks (ct\<^sub>0, unat count\<^sub>0) 8"
    by (find_master assms: assms')+
  have 1: "(s \<turnstile> *[regs s rsp - 24,8]) = count\<^sub>0 + cs\<^sub>0 - (s \<turnstile> *[regs s rsp - 40,8])"
   and 11: "(s \<turnstile> *[regs s rsp - 32,8]) = count\<^sub>0 + ct\<^sub>0 - (s \<turnstile> *[regs s rsp - 40,8])"
    using assms'(10,11)
    by (auto simp add: field_simps)

  have 2: "cs\<^sub>0 \<le> max_word - count\<^sub>0"
   and 22: "ct\<^sub>0 \<le> max_word - count\<^sub>0"
    using master_block_implies_no_block_overflow[OF 0]
    apply (auto simp add: no_block_overflow.simps)[1]
    apply unat_arith
    apply (auto simp add: max_word_eq)[1]
    using master_block_implies_no_block_overflow[OF 00]
    apply (auto simp add: no_block_overflow.simps)[1]
    apply unat_arith
    by (auto simp add: max_word_eq)
  have 3: "(s \<turnstile> *[regs s rsp - 40,8]) - 1 \<le> count\<^sub>0 + cs\<^sub>0"
   and 33: "(s \<turnstile> *[regs s rsp - 40,8]) - 1 \<le> count\<^sub>0 + ct\<^sub>0"
    using assms'(9,12) master_block_implies_no_block_overflow[OF 0]
    apply (auto simp add: no_block_overflow.simps field_simps)[1]
    apply unat_arith
    apply auto[1]
    using assms'(9,12) master_block_implies_no_block_overflow[OF 00]
    apply (auto simp add: no_block_overflow.simps field_simps)[1]
    apply unat_arith
    by auto[1]
  have \<open>master blocks (s \<turnstile> *[regs s rsp - 24,8], Suc 0) 8\<close>
   and \<open>master blocks (s \<turnstile> *[regs s rsp - 32,8], Suc 0) 8\<close> 
    apply (rule master_of_enclosed[OF assms'(1), of _ _ "(cs\<^sub>0,unat count\<^sub>0)"])
    using assms'(9,10,12) master_block_implies_no_block_overflow[OF 0]
    apply (auto simp add: no_block_overflow.simps)[1]
    apply unat_arith
    using assms' apply simp
    using assms'(9,12) master_block_implies_no_block_overflow[OF 0]
    apply (subst 1)
    using x_less_x_plus_y[of cs\<^sub>0 "count\<^sub>0 - (s \<turnstile> *[regs s rsp - 40,8])",OF less_max_word_minus[OF 2]]
    apply (auto simp add: enclosed.simps no_block_overflow.simps field_simps)[1]
    using 3 word_sub_le[of  "(s \<turnstile> *[regs s rsp - 40,8]) - 1" "count\<^sub>0 + cs\<^sub>0"]
    apply (auto simp add: field_simps)[1]

    apply (rule master_of_enclosed[OF assms'(1), of _ _ "(ct\<^sub>0,unat count\<^sub>0)"])
    using assms'(9,11,12) master_block_implies_no_block_overflow[OF 00]
    apply (auto simp add: no_block_overflow.simps)[1]
    apply unat_arith
    using assms' apply simp
    using assms'(9,12) master_block_implies_no_block_overflow[OF 00]
    apply (subst 11)
    using x_less_x_plus_y[of ct\<^sub>0 "count\<^sub>0 - (s \<turnstile> *[regs s rsp - 40,8])",OF less_max_word_minus[OF 22]]
    apply (auto simp add: enclosed.simps no_block_overflow.simps field_simps)[1]
    using 33 word_sub_le[of  "(s \<turnstile> *[regs s rsp - 40,8]) - 1" "count\<^sub>0 + ct\<^sub>0"]
    by (auto simp add: field_simps)[1]
  note masters = masters and this and 0 and 00
  note masters = this

  have count\<^sub>0: "0 < unat count\<^sub>0"
    using assms'(9,12)
    by unat_arith
  show ?thesis
    apply (insert assms'(1-8) count\<^sub>0)
    apply (rewrite_one_step masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)

    apply (insert assms'(9-))
    apply (finish_symbolic_execution)
    apply (simp add: block2_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (simp add: P_61_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    done
qed



lemma palindrome_61_to_111:
assumes "(P_61 a blocks cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address) s"
shows "(block3 a cs\<^sub>0 ct\<^sub>0 count\<^sub>0 s && P_104_92_111 a blocks cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address) (The (run_until_pred (lines  {ret_address, 104, 92, 106,111}) s))"
proof-
  have \<open>master blocks (regs s rsp + 8, 8) 1\<close>
   and \<open>master blocks (regs s rsp, 8) 2\<close>
   and \<open>master blocks (regs s rsp - 1, Suc 0) 3\<close>
   and \<open>master blocks (regs s rsp - 2, Suc 0) 4\<close>
   and \<open>master blocks (regs s rsp - 24, 8) 5\<close>
   and \<open>master blocks (regs s rsp - 32, 8) 6\<close>
   and \<open>master blocks (regs s rsp - 40, 8) 7\<close>
    using assms[unfolded P_61_def]
    by (simp add: pred_logic Let'_def Let_def)+
  note masters = this

  have "seps blocks"
   and "(8, cs\<^sub>0, unat count\<^sub>0) \<in> blocks"
   and "(8, ct\<^sub>0, unat count\<^sub>0) \<in> blocks"
   and "RIP s = boffset + 61"
   and "RBP s = RSP s"
   and "s \<turnstile> *[RSP s + 8,8] = boffset + ret_address"
   and "ret_address > 150"
   and "(s \<turnstile> *[RSP s - 40,8] \<noteq> (0::64 word))"
   and "(s \<turnstile> *[regs s rsp - 24,8]) + (s \<turnstile> *[regs s rsp - 40,8]) = count\<^sub>0 + cs\<^sub>0 + 1"
   and "(s \<turnstile> *[regs s rsp - 32,8]) + (s \<turnstile> *[regs s rsp - 40,8]) = count\<^sub>0 + ct\<^sub>0 + 1"
   and "(s \<turnstile> *[regs s rsp - 40,8]) \<le> count\<^sub>0"
   and "flags s flag_zf = (s \<turnstile> *[(s \<turnstile> *[regs s rsp - 24,8]) - 1,1] = (s \<turnstile> *[(s \<turnstile> *[regs s rsp - 32,8]) - 1,1] :: 8 word))"
   and "unat count\<^sub>0 * 8 \<le> LENGTH('a)"
    using assms[unfolded P_61_def]
    by (auto simp add: pred_logic line_def read_flg_def get_def Let'_def Let_def)
  note assms = this


  have "master blocks (cs\<^sub>0, unat count\<^sub>0) 8"
   and "master blocks (ct\<^sub>0, unat count\<^sub>0) 8"
    by (find_master assms: assms)+
  note masters = masters and this
  note masters = this

  have count\<^sub>0: "0 < unat count\<^sub>0"
    using assms(8,11)
    by unat_arith

  show ?thesis
    apply (insert assms count\<^sub>0)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)

    apply (finish_symbolic_execution)
    apply (simp add: block3_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (simp add: P_104_92_111_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    subgoal premises prems
    proof-
      show ?thesis
        using prems(8,11)
        by unat_arith
    qed

    apply (subst run_until_pred_stop)
    apply (auto simp add: lines_def at_loc_def pred_logic line_def simp_rules Let'_def)[1]
    apply (auto simp add: lines_def at_loc_def pred_logic line_def simp_rules Let'_def)[1]
    apply (simp add: block3_def)
    apply (simp add: P_104_92_111_def)

    apply (rewrite_one_let')+
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (finish_symbolic_execution)
    apply (simp add: block3_def)
    apply (simp add: P_104_92_111_def)
    apply (insert masters)
    apply (simp add: simp_rules)[1]

    apply (rewrite_one_let')+
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (finish_symbolic_execution)
    apply (simp add: block3_def)
    apply (simp add: P_104_92_111_def)
    apply (insert masters)
    by (simp add: pred_AND_def simp_rules)[1]
qed


lemma palindrome_104_92_111_to_106_ret:
assumes "(P_104_92_111 a blocks cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address  && ! (\<lambda>s. \<not> flags s flag_zf \<and> line 104 s)) s"
shows "(block4 a cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address s && P_106_ret a blocks cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address) (The (run_until_pred (lines  {106, ret_address}) s))"
proof-
  have \<open>master blocks (regs s rsp + 8, 8) 1\<close>
   and \<open>master blocks (regs s rsp, 8) 2\<close>
   and \<open>master blocks (regs s rsp - 24, 8) 5\<close>
   and \<open>master blocks (regs s rsp - 32, 8) 6\<close>
   and \<open>master blocks (regs s rsp - 40, 8) 7\<close>
    using assms[unfolded P_104_92_111_def]
    by (simp add: pred_logic)+
  note masters = this

  have "seps blocks"
   and "(8, cs\<^sub>0, unat count\<^sub>0) \<in> blocks"
   and "(8, ct\<^sub>0, unat count\<^sub>0) \<in> blocks"
   and "RBP s = RSP s"
   and "s \<turnstile> *[RSP s + 8,8] = boffset + ret_address"
   and "ret_address > 150"
   and "RIP s = boffset + 104 \<longrightarrow> flags s flag_zf"
   and "unat count\<^sub>0 * 8 \<le> LENGTH('a)"
    using assms[unfolded P_104_92_111_def]
    by (auto simp add: pred_logic line_def read_flg_def get_def)
  note assms' = this

  consider (breaked) "RIP s = boffset + 92" | (normal) "RIP s = boffset + 104" | (ret'd) "RIP s = boffset + 111"
    using assms[unfolded P_104_92_111_def]
    by (auto simp add: pred_logic line_def read_flg_def get_def)
  thus ?thesis
  proof(cases)
    case breaked
    show ?thesis
      apply (insert assms' breaked)
      apply (symbolic_execution masters: masters)
      apply (finish_symbolic_execution)
      apply (insert masters)
      by (auto simp add: pred_logic P_106_ret_def block4_def masters)    
  next
    case normal
    show ?thesis
      apply (insert assms' normal)
      apply (symbolic_execution masters: masters)
      apply (finish_symbolic_execution)
      apply (insert masters)
      by (auto simp add: pred_logic P_106_ret_def block4_def)    
  next
    case ret'd
    show ?thesis
      apply (insert assms' ret'd)
      apply (symbolic_execution masters: masters)
      apply (symbolic_execution masters: masters)
      apply (finish_symbolic_execution)
      by (auto simp add: pred_logic P_106_ret_def block4_def)    
  qed
qed



lemma palindrome_106_ret_to_ret:
assumes "(P_106_ret a blocks cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address ) s"
  shows "(block5 a cs\<^sub>0 ct\<^sub>0 count\<^sub>0  ret_address s && P_ret ret_address) (The (run_until_pred (line ret_address) s))"
proof-
  consider (normal) "RIP s = boffset + 106" |  (ret'd) "RIP s = boffset + ret_address"
    using assms[unfolded P_106_ret_def]
    by (auto simp add: pred_logic line_def read_flg_def get_def split: if_split_asm)
  thus ?thesis
  proof(cases)
    case normal
    hence \<open>master blocks (regs s rsp + 8, 8) 1\<close>
      using assms[unfolded P_106_ret_def]
      by (auto simp add: pred_logic split: if_split_asm)
    note masters = this

    have "seps blocks"
     and "RBP s = RSP s"
     and "s \<turnstile> *[RSP s + 8,8] = boffset + ret_address"
     and "ret_address > 150"
      using normal assms[unfolded P_106_ret_def]
      by (auto simp add: pred_logic line_def read_flg_def get_def split: if_split_asm)
    note assms' = this

    show ?thesis
      apply (insert assms' normal)
      apply (symbolic_execution masters: masters)
      apply (symbolic_execution masters: masters)
      apply (symbolic_execution masters: masters)
      apply (finish_symbolic_execution)
      by (auto simp add: pred_logic P_ret_def block5_def)    
  next
    case ret'd
    have "seps blocks"
     and "ret_address > 150"
     and "RIP s = boffset + ret_address"
      using ret'd assms[unfolded P_106_ret_def]
      by (auto simp add: pred_logic line_def read_flg_def get_def split: if_split_asm)
    note assms' = this

    show ?thesis
      apply (insert assms')
      apply (finish_symbolic_execution)
      by (auto simp add: pred_logic P_ret_def block5_def)    
  qed
qed

definition S :: "'\<sigma>\<^sub>C \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> state \<Rightarrow> strncmp_state \<times> '\<sigma>\<^sub>C astate_scheme"
  where "S \<sigma>\<^sub>C cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address s =
                  (\<lparr> c1 = s \<turnstile> *[RSP s - 2,1],
                     c2 = s \<turnstile> *[RSP s - 1,1],
                     cs' = (s \<turnstile> *[RSP s - 24,8]) - cs\<^sub>0,
                     ct' = (s \<turnstile> *[RSP s - 32,8]) - ct\<^sub>0,
                     count = s \<turnstile> *[RSP s  - 40, 8] ,
                     breaked = (RIP s = boffset + 92),
                     ret'd = (RIP s \<in> {boffset + 111, boffset + ret_address})\<rparr>,
                   \<lparr> ret = EAX s,
                     cs_arr = read_array_8 s cs\<^sub>0 (unat count\<^sub>0),
                     ct_arr = read_array_8 s ct\<^sub>0 (unat count\<^sub>0),
                      \<dots> = \<sigma>\<^sub>C\<rparr>)"

lemma palindrome_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {104,106,ret_address}) ;
          run_until_pred (lines {106,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 106"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address,106}" "line 104"])
  by (simp add: line_simps)



definition abstract_strncmp :: "64 word \<Rightarrow> strncmp_state \<times> 'b astate_scheme \<Rightarrow> strncmp_state \<times> 'b astate_scheme \<Rightarrow> bool"
  where "abstract_strncmp count\<^sub>0 \<equiv>
         (\<lambda> \<sigma> \<sigma>' . count (\<L> \<sigma>') = count\<^sub>0
           \<and> cs' (\<L> \<sigma>') = 0
           \<and> ct' (\<L> \<sigma>') = 0
           \<and> \<not>ret'd (\<L> \<sigma>')
           \<and> \<not>breaked (\<L> \<sigma>')
           \<and> cs_arr (\<C> \<sigma>') = cs_arr (\<C> \<sigma>)
           \<and> ct_arr (\<C> \<sigma>') = ct_arr (\<C> \<sigma>));
          WHILE \<lambda> \<sigma> . count (\<L> \<sigma>) \<noteq> 0 \<and> \<not>breaked (\<L> \<sigma>) \<and> \<not>ret'd (\<L> \<sigma>) DO 
            (\<lambda> \<sigma> \<sigma>' . c1 (\<L> \<sigma>')  = cs_arr (\<C> \<sigma>) ! unat (cs' (\<L> \<sigma>)) \<and>
                      c2 (\<L> \<sigma>')  = ct_arr (\<C> \<sigma>) ! unat (ct' (\<L> \<sigma>)) \<and>
                      cs' (\<L> \<sigma>') = 1 + cs' (\<L> \<sigma>) \<and>
                      ct' (\<L> \<sigma>') = 1 + ct' (\<L> \<sigma>) \<and>
                      count (\<L> \<sigma>') = count (\<L> \<sigma>) \<and>
                      cs_arr (\<C> \<sigma>') = cs_arr (\<C> \<sigma>) \<and>
                      ct_arr (\<C> \<sigma>') = ct_arr (\<C> \<sigma>));
            (\<lambda> \<sigma> \<sigma>' . (if cs_arr (\<C> \<sigma>) ! unat (cs' (\<L> \<sigma>) - 1) \<noteq> ct_arr (\<C> \<sigma>) ! unat (ct' (\<L> \<sigma>) - 1) then
                        ret (\<C> \<sigma>') = (if c1 (\<L> \<sigma>) < c2 (\<L> \<sigma>) then -1 else 1) \<and>
                        ret'd (\<L> \<sigma>') \<and>
                        \<not>breaked (\<L> \<sigma>') \<and>
                        count (\<L> \<sigma>') = count (\<L> \<sigma>)
                      else if c1 (\<L> \<sigma>) = 0 then
                        breaked (\<L> \<sigma>') \<and>
                        \<not>ret'd (\<L> \<sigma>') \<and>
                        count (\<L> \<sigma>') = count (\<L> \<sigma>)
                      else
                        \<not>breaked (\<L> \<sigma>') \<and>
                        \<not>ret'd (\<L> \<sigma>') \<and>
                        count (\<L> \<sigma>') = count (\<L> \<sigma>) - 1) \<and>
                      cs' (\<L> \<sigma>') = cs' (\<L> \<sigma>) \<and>
                      ct' (\<L> \<sigma>') = ct' (\<L> \<sigma>) \<and>
                      cs_arr (\<C> \<sigma>') = cs_arr (\<C> \<sigma>) \<and>
                      ct_arr (\<C> \<sigma>') = ct_arr (\<C> \<sigma>))
          OD ;
          (\<lambda> \<sigma> \<sigma>' . ret'd (\<L> \<sigma>') = ret'd (\<L> \<sigma>) \<and>
                    ret (\<C> \<sigma>') = ret (\<C> \<sigma>) \<and>
                    cs_arr (\<C> \<sigma>') = cs_arr (\<C> \<sigma>) \<and>
                    ct_arr (\<C> \<sigma>') = ct_arr (\<C> \<sigma>)) ;
          (\<lambda> \<sigma> \<sigma>' . ret (\<C> \<sigma>') = (if ret'd (\<L> \<sigma>) then ret (\<C> \<sigma>) else 0) \<and>
                    cs_arr (\<C> \<sigma>') = cs_arr (\<C> \<sigma>) \<and>
                    ct_arr (\<C> \<sigma>') = ct_arr (\<C> \<sigma>))"



lemma strncmp:
  fixes a :: "'a::len word itself"
  shows "(S \<sigma>\<^sub>C cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address) ::
         {P_0 a blocks cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address}
            run_until_pred (line ret_address) \<preceq> abstract_strncmp count\<^sub>0
         {P_ret ret_address}"
  apply (subst abstract_strncmp_def)
  apply (subst palindrome_decompose)
  apply (rule HL_compose[of _ _ _ _ "P_104_92_111 a blocks cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address"])
  apply (rule HL_equality_intro)    
  apply (rule palindrome_0_104[unfolded block1_def],simp)
  subgoal premises prems for s s'
  proof-
    show ?thesis
      using prems
      apply (auto simp add: S_def P_0_def)[1]
      apply (rule read_array_8_eqI[where 'a='a])
      apply simp
      apply (rule master_block_implies_no_block_overflow)
      apply (rule master_if_in_blocks)
      apply simp
      apply simp
      apply simp
      apply (rule read_array_8_eqI[where 'a='a])
      apply simp
      apply (rule master_block_implies_no_block_overflow)
      apply (rule master_if_in_blocks)
      apply simp
      apply simp
      apply simp
      done
  qed
  apply (subst seq_assoc[symmetric])
  apply (rule HL_compose[of _ _ _ _ "P_106_ret a blocks cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address"]) 
  apply (rule HL_while_generic[of _ _ "\<lambda>s. \<not>flags s flag_zf \<and> line 104 s" _ _ "lines {104,111,92}"],simp add: line_simps)
  apply (auto simp add: S_def P_104_92_111_def lines_def line_def read_flg_def get_def)[1]
  apply (subst compose[of _ "line 61"],simp add: line_simps)
  apply (subst seq_assoc[symmetric])
  apply (rule HL_compose[of _ _ _ _ "P_61 a blocks cs\<^sub>0 ct\<^sub>0 count\<^sub>0 ret_address"])
  apply (rule HL_equality_intro_step)
  apply (rule palindrome_104_to_61,simp)
  subgoal premises prems for s s'
  proof-
    have 0: "no_block_overflow (cs\<^sub>0, unat count\<^sub>0)"
      apply (rule master_block_implies_no_block_overflow)
      apply (rule master_if_in_blocks)
      using prems
      by (auto simp add: P_104_92_111_def pred_logic)
    have 1: "no_block_overflow (ct\<^sub>0, unat count\<^sub>0)"
      apply (rule master_block_implies_no_block_overflow)
      apply (rule master_if_in_blocks)
      using prems
      by (auto simp add: P_104_92_111_def pred_logic)
    thus ?thesis
      using prems 0 1
      apply (auto simp add: S_def block2_def)[1]
      apply (subst nth_read_array_8)
      apply (auto simp add: P_104_92_111_def pred_logic read_flg_def get_def line_def unat_sub_if')[1]
      subgoal premises prems
      proof-
        show ?thesis
          using prems(29,30)
          by unat_arith
      qed
      apply unat_arith
      apply (auto)[1]  
      apply (subst nth_read_array_8)
      apply (auto simp add: P_104_92_111_def pred_logic read_flg_def get_def line_def unat_sub_if')[1]
      subgoal premises prems
      proof-
        show ?thesis
          using prems(29,30)
          by unat_arith
      qed
      apply unat_arith
      apply simp
      apply (rule read_array_8_eqI)
      apply (auto simp add: P_104_92_111_def pred_logic read_flg_def get_def line_def)
      apply (rule read_array_8_eqI)
      by (auto simp add: P_104_92_111_def pred_logic read_flg_def get_def line_def)
  qed
  apply (rule HL_equality_intro)
  apply (rule palindrome_61_to_111,simp)
  subgoal premises prems for s s'
  proof-
    have 0: "no_block_overflow (cs\<^sub>0, unat count\<^sub>0)"
      apply (rule master_block_implies_no_block_overflow)
      apply (rule master_if_in_blocks)
      using prems
      by (auto simp add: P_61_def pred_logic Let'_def Let_def)
    have 00: "no_block_overflow (ct\<^sub>0, unat count\<^sub>0)"
      apply (rule master_block_implies_no_block_overflow)
      apply (rule master_if_in_blocks)
      using prems
      by (auto simp add: P_61_def pred_logic Let'_def Let_def)
    have 1: "s \<turnstile> *[regs s rsp - 40,8] \<noteq> (0::64 word)"
     and 2: "s \<turnstile> *[regs s rsp - 40,8] \<le> count\<^sub>0"
      using prems
      unfolding P_61_def
      by (auto simp add: Let'_def Let_def)
    have 3: "(s \<turnstile> *[regs s rsp - 24,8]) = (1::64 word) + (count\<^sub>0 + cs\<^sub>0) - (s \<turnstile> *[regs s rsp - 40,8])"
      using prems
      unfolding P_61_def
      by (auto simp add: Let'_def Let_def)
    have 4: "(s \<turnstile> *[regs s rsp - 32,8]) = (1::64 word) + (count\<^sub>0 + ct\<^sub>0) - (s \<turnstile> *[regs s rsp - 40,8])"
      using prems
      unfolding P_61_def
      by (auto simp add: Let'_def Let_def)
    have "read_array_8 s cs\<^sub>0 (unat count\<^sub>0) ! unat ((s \<turnstile> *[regs s rsp - 24,8]) - cs\<^sub>0 - 1) = s \<turnstile> *[(s \<turnstile> *[regs s rsp - 24,8]) - 1,Suc 0]"
      apply (subst nth_read_array_8)
      apply (rule unat_mono)
      apply (subst 3)
      apply (simp add: field_simps)
      using 1 2
      apply unat_arith
      by simp
    moreover
    have "read_array_8 s ct\<^sub>0 (unat count\<^sub>0) ! unat ((s \<turnstile> *[regs s rsp - 32,8]) - ct\<^sub>0 - 1) = s \<turnstile> *[(s \<turnstile> *[regs s rsp - 32,8]) - 1,Suc 0]"
      apply (subst nth_read_array_8)
      apply (rule unat_mono)
      apply (subst 4)
      apply (simp add: field_simps)
      using 1 2
      apply unat_arith
      by simp
    moreover
    have "read_array_8 s' cs\<^sub>0 (unat count\<^sub>0) = read_array_8 s cs\<^sub>0 (unat count\<^sub>0)"
      apply (rule read_array_8_eqI)
      using prems 0
      by (auto simp add: block3_def P_61_def Let'_def simp_rules)
    moreover
    have "read_array_8 s' ct\<^sub>0 (unat count\<^sub>0) = read_array_8 s ct\<^sub>0 (unat count\<^sub>0)"
      apply (rule read_array_8_eqI)
      using prems 00
      by (auto simp add: block3_def P_61_def Let'_def simp_rules)
    ultimately
    show ?thesis
      using prems
      by (auto simp add: block3_def P_61_def S_def Let'_def simp_rules max_word_minus[symmetric] max_word_eq)
  qed
  apply (rule HL_equality_intro)
  apply (rule palindrome_104_92_111_to_106_ret,simp)
  subgoal premises prems for s s'
  proof-
    have 0: "no_block_overflow (cs\<^sub>0, unat count\<^sub>0)"
      apply (rule master_block_implies_no_block_overflow)
      apply (rule master_if_in_blocks)
      using prems
      by (auto simp add: P_104_92_111_def pred_logic Let'_def Let_def)
    have 00: "no_block_overflow (ct\<^sub>0, unat count\<^sub>0)"
      apply (rule master_block_implies_no_block_overflow)
      apply (rule master_if_in_blocks)
      using prems
      by (auto simp add: P_104_92_111_def pred_logic Let'_def Let_def)
    have "read_array_8 s' cs\<^sub>0 (unat count\<^sub>0) = read_array_8 s cs\<^sub>0 (unat count\<^sub>0)"
      apply (rule read_array_8_eqI)
      using prems 0
      by (auto simp add: block4_def P_104_92_111_def pred_logic Let'_def simp_rules)
    moreover
    have "read_array_8 s' ct\<^sub>0 (unat count\<^sub>0) = read_array_8 s ct\<^sub>0 (unat count\<^sub>0)"
      apply (rule read_array_8_eqI)
      using prems 00
      by (auto simp add: block4_def P_104_92_111_def pred_logic Let'_def simp_rules)
    ultimately
    show ?thesis
      using prems
      by (auto simp add: S_def P_104_92_111_def block4_def pred_logic)
  qed
  apply (rule HL_equality_intro)
  apply (rule palindrome_106_ret_to_ret,simp)
  subgoal premises prems for s s'
  proof-
    have 0: "no_block_overflow (cs\<^sub>0, unat count\<^sub>0)"
      apply (rule master_block_implies_no_block_overflow)
      apply (rule master_if_in_blocks)
      using prems
      by (auto simp add: P_106_ret_def pred_logic Let'_def Let_def)
    have 00: "no_block_overflow (ct\<^sub>0, unat count\<^sub>0)"
      apply (rule master_block_implies_no_block_overflow)
      apply (rule master_if_in_blocks)
      using prems
      by (auto simp add: P_106_ret_def pred_logic Let'_def Let_def)
    have "read_array_8 s' cs\<^sub>0 (unat count\<^sub>0) = read_array_8 s cs\<^sub>0 (unat count\<^sub>0)"
      apply (rule read_array_8_eqI)
      using prems 0
      by (auto simp add: block5_def P_106_ret_def pred_logic Let'_def simp_rules)
    moreover
    have "read_array_8 s' ct\<^sub>0 (unat count\<^sub>0) = read_array_8 s ct\<^sub>0 (unat count\<^sub>0)"
      apply (rule read_array_8_eqI)
      using prems 00
      by (auto simp add: block5_def P_106_ret_def pred_logic Let'_def simp_rules)
    ultimately
    show ?thesis
      using prems
      by (auto simp add: S_def P_106_ret_def block5_def pred_logic)
  qed
  done                                   



lemma strncmp_correct:
assumes "i < unat count\<^sub>0 \<and> count\<^sub>0 < 2 ^64"
    and "cs_arr\<^sub>0 ! i = 0 \<and> (\<forall> i' < i . cs_arr\<^sub>0 ! i' \<noteq> 0)"
  shows "
  { \<lambda> \<sigma> . cs_arr (\<L> \<sigma>) = cs_arr\<^sub>0}
  call (abstract_strncmp count\<^sub>0)
  { \<lambda> \<sigma> . cs_arr (\<L> \<sigma>) = cs_arr\<^sub>0 \<and> (if ret (\<L> \<sigma>) = 0 then \<forall> n < i . cs_arr (\<L> \<sigma>) ! n = ct_arr (\<L> \<sigma>) ! n else \<exists> n \<le> i . cs_arr (\<L> \<sigma>) ! n \<noteq> ct_arr (\<L> \<sigma>) ! n)}"
  unfolding abstract_strncmp_def
  apply (rule CallRule[where P'="\<lambda> \<sigma> . cs_arr \<sigma> = cs_arr\<^sub>0" and Q'="\<lambda> \<sigma> . cs_arr \<sigma> = cs_arr\<^sub>0 \<and> (if ret \<sigma> = 0 then \<forall> n < i . cs_arr \<sigma> ! n = ct_arr \<sigma> ! n else \<exists> n \<le> i . cs_arr \<sigma> ! n \<noteq> ct_arr \<sigma> ! n)"])
  apply (rule SeqRule[of _ _ "\<lambda> \<sigma> . cs_arr (\<C> \<sigma>) = cs_arr\<^sub>0 \<and>
                                    count (\<L> \<sigma>) = count\<^sub>0 \<and> 
                                    cs' (\<L> \<sigma>) = 0 \<and>
                                    ct' (\<L> \<sigma>) = 0 \<and>
                                    \<not>ret'd (\<L> \<sigma>) \<and> \<not>breaked (\<L> \<sigma>) \<and>
                                    (\<forall> n < count\<^sub>0 - count (\<L> \<sigma>) . cs_arr (\<C> \<sigma>) ! unat n = ct_arr (\<C> \<sigma>) ! unat n)"])
  apply (rule BasicRule)
  apply (auto)[1] 
  apply (rule SeqRule[of _ _ "\<lambda> \<sigma> . cs_arr (\<C> \<sigma>) = cs_arr\<^sub>0 \<and>
                                    (if ret'd (\<L> \<sigma>) then ret (\<C> \<sigma>) \<noteq> 0 \<and> (\<exists> n \<le> i . cs_arr (\<C> \<sigma>) ! n \<noteq> ct_arr (\<C> \<sigma>) ! n)
                                      else \<forall> n < i . cs_arr (\<C> \<sigma>) ! n = ct_arr (\<C> \<sigma>) ! n)"])
  apply (rule WhileRule[of _ "\<lambda> \<sigma> . cs_arr (\<C> \<sigma>) = cs_arr\<^sub>0 \<and>
                                  count (\<L> \<sigma>) \<le> count\<^sub>0 \<and> 
                                  unat (count\<^sub>0 - count (\<L> \<sigma>)) \<le> i \<and>
                                  (breaked (\<L> \<sigma>) \<longrightarrow> unat (count\<^sub>0 - count (\<L> \<sigma>)) = i) \<and>
                                  (if \<not>ret'd (\<L> \<sigma>) then 
                                     (\<not>breaked (\<L> \<sigma>) \<longrightarrow> 
                                        cs' (\<L> \<sigma>) = count\<^sub>0 - count (\<L> \<sigma>) \<and>
                                        ct' (\<L> \<sigma>) = count\<^sub>0 - count (\<L> \<sigma>)) \<and>
                                     (\<forall> n < count\<^sub>0 - count (\<L> \<sigma>) . cs_arr (\<C> \<sigma>) ! unat n = ct_arr (\<C> \<sigma>) ! unat n)
                                    else ret (\<C> \<sigma>) \<noteq> 0 \<and> cs_arr (\<C> \<sigma>) ! (unat (count\<^sub>0 - count (\<L> \<sigma>))) \<noteq> ct_arr (\<C> \<sigma>) ! unat (count\<^sub>0 - count (\<L> \<sigma>)))"])
  apply (auto simp add: pred_logic)[1]
  using assms
  apply (auto simp add: pred_logic )[1]
  subgoal premises prems for l\<sigma> c\<sigma> n
  proof-
    have "of_nat n < count\<^sub>0 - count l\<sigma>"
      using assms(1)
      by unat_arith
    thus ?thesis
      using prems(11) assms(1) prems(8)[THEN spec,of "of_nat n"]
      apply (auto simp add: unat_of_nat)
      by unat_arith
  qed
  subgoal premises prems for l\<sigma> c\<sigma> n
  proof-
    have "of_nat n < count\<^sub>0 - count l\<sigma>"
      using assms(1)
      by unat_arith
    thus ?thesis
      using prems(11) assms(1) prems(8)[THEN spec,of "of_nat n"]
      apply (auto simp add: unat_of_nat)
      by unat_arith
  qed
  apply (rule SeqRule[of _ _ "\<lambda> \<sigma> . cs_arr (\<C> \<sigma>) = cs_arr\<^sub>0 \<and>
                                    c1 (\<L> \<sigma>)  = cs_arr (\<C> \<sigma>) ! unat (cs' (\<L> \<sigma>) - 1) \<and>
                                    c2 (\<L> \<sigma>)  = ct_arr (\<C> \<sigma>) ! unat (ct' (\<L> \<sigma>) - 1) \<and>
                                    cs_arr (\<C> \<sigma>) ! i = 0 \<and>
                                    count (\<L> \<sigma>)  > 0 \<and> count (\<L> \<sigma>) \<le> count\<^sub>0 \<and>
                                    unat (count\<^sub>0 - count (\<L> \<sigma>)) \<le> i \<and>
                                    cs' (\<L> \<sigma>) = count\<^sub>0 - count (\<L> \<sigma>) + 1 \<and>
                                    ct' (\<L> \<sigma>) = count\<^sub>0 - count (\<L> \<sigma>) + 1 \<and>
                                    (\<forall> n < count\<^sub>0 - count (\<L> \<sigma>) . cs_arr (\<C> \<sigma>) ! unat n = ct_arr (\<C> \<sigma>) ! unat n)"])
  apply (rule BasicRule)
  apply (auto simp add: pred_logic assms)[1]
  apply unat_arith
  apply unat_arith
  apply (rule BasicRule)
  using assms
  apply (auto simp add: pred_logic split: if_split_asm)[1]
  subgoal premises prems for l\<sigma> c\<sigma> l\<sigma>' c\<sigma>'
    using prems
    by (cases "unat (count\<^sub>0 - count l\<sigma>) < i";auto simp add: pred_logic split: if_split_asm)
  apply (meson gt_zero_is_le_one order_trans_rules(23) word_sub_le_iff)
  subgoal premises prems for l\<sigma> c\<sigma> l\<sigma>' c\<sigma>'
  proof-
    have "unat (count\<^sub>0 - count l\<sigma>) \<le> i \<Longrightarrow> unat (count\<^sub>0 - count l\<sigma>) \<noteq> i \<Longrightarrow> unat (count\<^sub>0 - (count l\<sigma> - 1)) \<le> i"
      by unat_arith
    thus ?thesis
      using assms prems
      by (cases "unat (count\<^sub>0 - count l\<sigma>) = i",auto simp add: unat_of_nat)
  qed
  subgoal for l\<sigma> c\<sigma> l\<sigma>' c\<sigma>' n
    apply (cases "n < count\<^sub>0 - count l\<sigma>";cases "n > count\<^sub>0 - count l\<sigma>";auto simp add: field_simps)
    by unat_arith
  apply (auto simp add: pred_logic)[1]
  apply (rule SeqRule[of _ _ "\<lambda> \<sigma> . cs_arr (\<C> \<sigma>) = cs_arr\<^sub>0 \<and>
                                    (if ret'd (\<L> \<sigma>) then ret (\<C> \<sigma>) \<noteq> 0 \<and> (\<exists> n \<le> i . cs_arr (\<C> \<sigma>) ! n \<noteq> ct_arr (\<C> \<sigma>) ! n)
                                      else \<forall> n < i . cs_arr (\<C> \<sigma>) ! n = ct_arr (\<C> \<sigma>) ! n)"])
  apply (rule BasicRule)
  apply (auto simp add: pred_logic assms)[1]
  apply (rule BasicRule)
  apply (auto simp add: pred_logic assms split: if_split_asm)[1]
  apply simp
  by auto

end
end