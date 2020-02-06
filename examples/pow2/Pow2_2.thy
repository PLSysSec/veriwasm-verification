theory Pow2_2
  imports "../../isabelle/Det_Step"
          "../../isabelle/Presimplified_Semantics_Manual2"
begin



text \<open>Load the pow2.s file.\<close>
x86_64_parser "../examples/pow2/pow2.s"

locale pow2_context = pow2 + presimplified_semantics +
  assumes funcs_def: "funcs \<equiv> \<lambda> _ . None"
begin

abbreviation "\<alpha> \<equiv> assembly"

lemma binary_offset[simp]:
  shows "binary_offset assembly = boffset"
  by (simp add: assembly_def assembly.defs)
schematic_goal unfold_labels[simp]:
  shows "label_to_address assembly = ?x"
  apply (rule ext)
  apply (unfold label_to_address_def)
  apply (unfold binary_offset)
  by (auto simp add: label_to_address_def assembly_def assembly.defs)

fun pow2_flag_annotation :: flag_annotation where
  \<open>pow2_flag_annotation loc = (if loc = boffset + 35 then {flag_cf} else {})\<close>


definition step :: \<open>state \<Rightarrow> state\<close> where
  \<open>step s \<equiv>
    let  pc = get_rip s;
         index = the (instr_index lookup_table boffset pc) in
    let' (_,i,si) = (text_sections \<alpha>)!index;
         s = exec_instr \<alpha> semantics pow2_flag_annotation i si s
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
  ((thin_tac \<open>master _ _ _\<close>)+)?

method symbolic_execution uses masters add del =
    (* Unfold one step *)
    (subst run_until_pred_step[symmetric]),
    (* Show that we are not at the end. Otherwise, fail. *)
    (determ \<open>(simp add: lines_def at_loc_def pred_OR_def line_def; (unat_arith; ((auto simp add: unat_of_nat)[1])?)?)\<close> ; fail),
    (* Rewrite one step *)
    rewrite_one_step masters: masters add: add del: del
              
method finish_symbolic_execution =
    (* Stop at the current state *)
    subst run_until_pred_stop,
    (* Show that we are at the end. Otherwise, fail *)
    (determ \<open>(simp add: lines_def at_loc_def pred_OR_def line_def; (unat_arith; ((auto simp add: unat_of_nat)[1])?)?)\<close> ; fail),
    (* Simplify and split the current subgoal *)
    (simp (no_asm_simp) add: pred_logic simp_rules),
    ((rule ifI | rule conjI | rule impI)+)?


definition P_0
  where "P_0 blocks n ret_address rsp\<^sub>0 \<sigma> \<equiv>
      seps blocks
    \<and> master blocks (regs \<sigma> rsp, 8) 1
    \<and> master blocks (regs \<sigma> rsp - 8, 8) 2
    \<and> master blocks (regs \<sigma> rsp - 16, 8) 3
    \<and> master blocks (regs \<sigma> rsp - 20, 4) 4
    \<and> master blocks (regs \<sigma> rsp - 28, 4) 5
    \<and> EDI \<sigma> = n
    \<and> RSP \<sigma> = rsp\<^sub>0
    \<and> get_rip \<sigma> = boffset
    \<and> \<sigma> \<turnstile> *[RSP \<sigma>,8] = boffset + ret_address
    \<and> ret_address > 45"

definition P_38
  where "P_38 blocks n ret_address rsp\<^sub>0 \<sigma> \<equiv>
      seps blocks
    \<and> master blocks (regs \<sigma> rsp + 8, 8) 1
    \<and> master blocks (regs \<sigma> rsp, 8) 2
    \<and> master blocks (regs \<sigma> rsp - 8, 8) 3
    \<and> master blocks (regs \<sigma> rsp - 12, 4) 4
    \<and> master blocks (regs \<sigma> rsp - 20, 4) 5
    \<and> RBP \<sigma> = RSP \<sigma>
    \<and> RSP \<sigma> = rsp\<^sub>0 - 8
    \<and> \<sigma> \<turnstile> *[RSP \<sigma> - 20,4] = (n :: 32 word)
    \<and> read_flg \<sigma> flag_cf = (\<sigma> \<turnstile> *[RSP \<sigma> - 12,4] < n)
    \<and> get_rip \<sigma> = boffset + 38
    \<and> \<sigma> \<turnstile> *[RSP \<sigma> + 8,8] = boffset + ret_address
    \<and> ret_address > 45"

definition P_40
  where "P_40 blocks n ret_address rsp\<^sub>0 \<sigma> \<equiv>
      seps blocks
    \<and> master blocks (regs \<sigma> rsp + 8, 8) 1
    \<and> master blocks (regs \<sigma> rsp, 8) 2
    \<and> master blocks (regs \<sigma> rsp - 8, 8) 3
    \<and> master blocks (regs \<sigma> rsp - 12, 4) 4
    \<and> master blocks (regs \<sigma> rsp - 20, 4) 5
    \<and> RBP \<sigma> = RSP \<sigma>
    \<and> RSP \<sigma> = rsp\<^sub>0 - 8
    \<and> \<sigma> \<turnstile> *[RSP \<sigma> - 20,4] = (n :: 32 word)
    \<and> get_rip \<sigma> = boffset + 40
    \<and> \<sigma> \<turnstile> *[RSP \<sigma> + 8,8] = boffset + ret_address
    \<and> ret_address > 45"

definition P_ret
  where "P_ret ret_address rsp\<^sub>0 \<sigma> \<equiv>
      RSP \<sigma> = rsp\<^sub>0 + 8 \<and> 
      RIP \<sigma> = boffset + ret_address"

definition incr_rip_pred :: "nat \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  where "incr_rip_pred n s s' \<equiv> s' = incr_rip n s"  

definition block1 :: "state \<Rightarrow> bool"
  where "block1 \<sigma> \<equiv> \<sigma> \<turnstile> *[RSP \<sigma>  - 12, 4] = (0::32 word)
                  \<and> \<sigma> \<turnstile> *[RSP \<sigma>  - 8, 8]  = (1::64 word)"

definition block2 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block2 \<sigma> \<sigma>' \<equiv> \<sigma>' \<turnstile> *[RSP \<sigma>'  - 12, 4] = (1 + (\<sigma> \<turnstile> *[RSP \<sigma> - 12,4]) :: 32 word)
                     \<and> \<sigma>' \<turnstile> *[RSP \<sigma>' - 8, 8]   = ((\<sigma> \<turnstile> *[RSP \<sigma> - 8,8]) * 2 :: 64 word)"

definition block3 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block3 s s' \<equiv> RAX s' = s \<turnstile> *[regs s rsp - 8,8]"


lemma pow2_0_10:
  assumes "P_0 blocks n ret_address rsp\<^sub>0 s"
  shows "(block1 && P_38 blocks n ret_address rsp\<^sub>0) (The (run_until_pred (lines {38,40,ret_address}) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 20, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 28, 4) 5\<close> \<comment> \<open>4-byte alignment gap at @{text rsp\<^sub>0} - 24\<close>
    using assms[unfolded P_0_def]
    by simp+
  note masters = this

  have "seps blocks"
   and "EDI s = n"
   and "RSP s = rsp\<^sub>0"
   and "RIP s = boffset"
   and "ret_address > 45"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
    using assms[unfolded P_0_def]
    by simp+
  note assms = this

  show ?thesis
    apply (insert assms)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)

    apply (finish_symbolic_execution)
    apply (simp add: block1_def simp_rules)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    apply (simp add: P_38_def simp_rules)
    apply (rewrite_one_let')+
    apply (auto simp add: simp_rules)[1]
    done
qed


lemma pow2_10_10:
  assumes "((P_38 blocks n ret_address rsp\<^sub>0) && (\<lambda> s . flags s flag_cf)) s"
shows "(block2 s && P_38 blocks n ret_address rsp\<^sub>0) (The (((\<lambda>s. (=) (step s)) ; run_until_pred (lines {ret_address,40,38})) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 20, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 28, 4) 5\<close> \<comment> \<open>4-byte alignment gap at @{text rsp\<^sub>0} - 24\<close>
    using assms[unfolded P_38_def pred_AND_def]
    by simp+
  note masters = this

  have "seps blocks"
   and "RBP s = RSP s"
   and "s \<turnstile> *[RSP s - 20,4] = (n :: 32 word)"
   and "read_flg s flag_cf = (s \<turnstile> *[RSP s - 12,4] < n)"
   and "get_rip s = boffset + 38"
   and "flags s flag_cf"
   and "s \<turnstile> *[regs s rsp + 8,8] = boffset + ret_address"
   and "ret_address > 45"
   and "RSP s = rsp\<^sub>0 - 8"
    using assms[unfolded P_38_def pred_AND_def]
    by simp+
  note assms = this


  show ?thesis
    apply (insert assms)
    apply (rewrite_one_step)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)

    apply (finish_symbolic_execution)
    apply (simp add: block2_def)
    apply (insert masters)
    apply (rewrite_one_let' add: P_38_def block2_def)+
    apply (simp add: simp_rules shiftl_t2n)
    apply (simp add: P_38_def)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    done
qed


lemma pow2_10_11:
assumes "((P_38 blocks n ret_address rsp\<^sub>0) && ! (\<lambda>s. flags s flag_cf)) s"
  shows "(incr_rip_pred 2 s && P_40 blocks n ret_address rsp\<^sub>0) (The (run_until_pred (lines {40,ret_address}) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 20, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 28, 4) 5\<close> \<comment> \<open>4-byte alignment gap at @{text rsp\<^sub>0} - 24\<close>
    using assms[unfolded P_38_def pred_AND_def]
    by simp+
  note masters = this

  have "seps blocks"
   and "RBP s = RSP s"
   and "s \<turnstile> *[RSP s - 20,4] = (n :: 32 word)"
   and "get_rip s = boffset + 38"
   and "\<not>flags s flag_cf"
   and "s \<turnstile> *[regs s rsp + 8,8] = boffset + ret_address"
   and "ret_address > 45"
   and "RSP s = rsp\<^sub>0 - 8"
    using assms[unfolded P_38_def pred_logic]
    by simp+
  note assms = this

  show ?thesis
    apply (insert assms)
    apply (symbolic_execution masters: masters)
    apply (finish_symbolic_execution)
    apply (simp add: incr_rip_pred_def incr_rip_def set_def field_simps)
    apply (simp add: P_40_def)
    apply (insert masters)
    by (auto)[1]
qed

lemma pow2_11_13:
  assumes "(P_40 blocks n ret_address rsp\<^sub>0) s"
    shows "(block3 s && P_ret ret_address rsp\<^sub>0) (The (run_until_pred (line ret_address) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 20, 4) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 28, 4) 5\<close> \<comment> \<open>4-byte alignment gap at @{text rsp\<^sub>0} - 24\<close>
    using assms[unfolded P_40_def pred_AND_def]
    by simp+
  note masters = this

  have "seps blocks"
   and "RBP s = RSP s"
   and "s \<turnstile> *[RSP s - 20,4] = (n :: 32 word)"
   and "get_rip s = boffset + 40"
   and "s \<turnstile> *[regs s rsp + 8,8] = boffset + ret_address"
   and "ret_address > 45"
   and "RSP s = rsp\<^sub>0 - 8"
    using assms[unfolded P_40_def pred_logic]
    by simp+
  note assms = this

  show ?thesis
    apply (insert assms)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (finish_symbolic_execution)
    apply (simp add: simp_rules at_loc_def shiftl_t2n pred_AND_def block3_def)
    apply (metis add_diff_cancel_right assms(2) numeral.simps(2))
    apply (simp add: P_ret_def)
    done
qed

end

record astate =
  ret :: "64 word"

record pow2_state =
  i :: "32 word"
  a :: "64 word"

context pow2_context
begin

definition abstract_pow2 :: "32 word \<Rightarrow> pow2_state \<times> 'a astate_scheme \<Rightarrow> pow2_state \<times> 'a astate_scheme \<Rightarrow> bool"
  where "abstract_pow2 n \<equiv>
            (\<lambda> \<sigma> \<sigma>' . i (\<L> \<sigma>') = 0 \<and>
                      a (\<L> \<sigma>') = 1);
            WHILE (\<lambda> \<sigma> . i (\<L> \<sigma>) < n) DO
                  (\<lambda> \<sigma> \<sigma>' .  i (\<L> \<sigma>') = i (\<L> \<sigma>) + 1 \<and>
                             a (\<L> \<sigma>') = a (\<L> \<sigma>) * 2)
            OD;
            (\<lambda> \<sigma> \<sigma>' . ret (\<C> \<sigma>') = a (\<L> \<sigma>))"
 
definition S :: "'\<sigma>\<^sub>C \<Rightarrow> state \<Rightarrow> pow2_state \<times> '\<sigma>\<^sub>C astate_scheme"
  where "S \<sigma>\<^sub>C s = (\<lparr> i = s \<turnstile> *[RSP s  - 12, 4],
                     a = s \<turnstile> *[RSP s  - 8, 8] \<rparr>,
                   \<lparr> ret = RAX s, \<dots> = \<sigma>\<^sub>C\<rparr>)"

lemma pow2_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {38,40,ret_address}) ;
          run_until_pred (lines {40,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 40"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address,40}" "line 38"])
  by (simp add: line_simps)

lemma pow2:
  shows "S \<sigma>\<^sub>C ::
         {P_0 blocks n ret_address rsp\<^sub>0}
            run_until_pred (line ret_address) \<preceq> abstract_pow2 n
         {P_ret ret_address rsp\<^sub>0}"
  apply (subst abstract_pow2_def)
  apply (subst pow2_decompose)
  apply (rule HL_compose[of _ _ _ _ "P_38 blocks n ret_address rsp\<^sub>0"])
  apply (rule HL_equality_intro)
  apply (rule pow2_0_10[unfolded block1_def],simp)
  apply (simp add: S_def)
  apply (rule HL_compose[of _ _ _ _ "P_40 blocks n ret_address rsp\<^sub>0"])
  apply (rule HL_while[of _ _ "\<lambda>s. flags s flag_cf" _ _ "line 38"],simp add: line_simps)
  apply (auto simp add: P_38_def lines_def line_def pred_logic get_def read_flg_def block1_def S_def)[1]
  apply (rule HL_equality_intro_step,simp add: line_simps)
  apply (rule pow2_10_10[unfolded block2_def],simp)
  apply (simp add: S_def field_simps)
  apply (rule HL_equality_intro)
  apply (rule pow2_10_11,simp)
  apply (simp add: S_def field_simps skip_def incr_rip_pred_def incr_rip_def Machine.set_def)
  apply (rule HL_equality_intro)
  apply (rule pow2_11_13[unfolded block3_def],simp)
  apply (simp add: S_def field_simps)
  done


lemma unatSuc_r: "1 + n \<noteq> 0 \<Longrightarrow> unat (n + 1) = Suc (unat n)"
  for n :: "'a::len word"
  by unat_arith

lemma pow2_func_correct:
  shows "
  { \<lambda> \<sigma> . True}
  call (abstract_pow2 n)
  { \<lambda> \<sigma> . ret (\<L> \<sigma>) = 2 ^ (unat n) }"
  unfolding abstract_pow2_def
  apply (rule CallRule[where P'="\<lambda> \<sigma> . True" and Q' = "\<lambda> \<sigma> . ret \<sigma> = 2 ^ (unat n)"])
  apply (rule SeqRule[where Q = "\<lambda> \<sigma> . i (\<L> \<sigma>) = 0 \<and> a (\<L> \<sigma>) = 1"])
  apply (rule BasicRule,simp)
  apply (rule SeqRule[where Q = "\<lambda> \<sigma> . a (\<L> \<sigma>) = 2 ^ (unat n)"])
  apply (rule WhileRule[where I = "\<lambda> \<sigma> . a (\<L> \<sigma>) = 2 ^ unat (i (\<L> \<sigma>)) \<and> i (\<L> \<sigma>) \<le> n"])
  apply (simp add: pred_logic )
  apply (simp add: pred_logic)
  apply force
  apply (rule BasicRule)
  apply (simp add: pred_logic)
  apply (subst unatSuc_r,unat_arith)
  apply simp
  apply unat_arith
  apply (auto simp add: unat_word_ariths)[1]
  apply (rule BasicRule)
  apply (simp add: case_prod_unfold)
  apply simp
  apply simp
  done

end

end




(* 
    apply (subst run_until_pred_step[symmetric])
    apply (determ \<open>((auto simp add: lines_def at_loc_def pred_OR_def line_def split: if_split_asm)[1]; (unat_arith; ((auto simp add: unat_of_nat)[1])?)?)\<close> ; fail)
    apply (subst step_seq_run)?
    apply (simp (no_asm_simp) add: step_def lookup_table_def instr_index_def entry_size_def del:)
    apply (rewrite_one_let' del: add: assembly_def)
    apply (simp add: exec_instr_def)
    apply (subst presimplify)
    apply (rewrite_one_let' del: add:)
    apply (subst is_manual)
    apply ((insert masters)[1])
    apply (rewrite_one_let' del: add:)+
*)  