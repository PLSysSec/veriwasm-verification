(*

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions andf
 limitations under the License.
 
 *)

theory Build_Array
  imports "../../isabelle/Presimplified_Semantics_Manual2"
          "../../isabelle/Det_Step"
          "../../isabelle/Read_Array"
          "../../isabelle/Malloc"
begin



text \<open>Load the malloc.s file.\<close>
x86_64_parser "../examples/malloc/malloc.s"

lemmas malloc.assembly_def [code]

record build_array_state = malloc_caller_state +
  i\<^sub>v :: "8 word"

record astate =
  ret\<^sub>v :: "32 word list option"


locale malloc_context = malloc + presimplified_semantics +
  assumes malloc_funcs: "funcs ''malloc'' = Some (malloc blocks)"
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

fun malloc_flag_annotation :: flag_annotation where
  \<open>malloc_flag_annotation loc = (if loc = boffset + 33 then {flag_zf} else if loc = boffset + 92 then {flag_cf} else {})\<close>

definition step :: \<open>state \<Rightarrow> state\<close> where
  \<open>step s \<equiv>
    let  pc = get_rip s;
         index = the (instr_index lookup_table boffset pc) in
    let' (_,i,si) = (text_sections \<alpha>)!index;
         s = exec_instr \<alpha> semantics malloc_flag_annotation i si s
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
    (* Unfold one step *)
    (subst run_until_pred_step[symmetric]),
    (* Show that we are not at the end. Otherwise, fail. *)
    (determ \<open>((auto simp add: lines_def at_loc_def pred_OR_def line_def split: if_split_asm)[1]; (unat_arith; ((auto simp add: unat_of_nat)[1])?)?)\<close> ; fail),
    (* Rewrite one step *)
    rewrite_one_step masters: masters add: add del: del
              
method finish_symbolic_execution =
    (* Stop at the current state *)
    subst run_until_pred_stop,
    (* Show that we are at the end. Otherwise, fail *)
    (determ \<open>((auto simp add: lines_def at_loc_def pred_OR_def line_def split: if_split_asm)[1]; (unat_arith; ((auto simp add: unat_of_nat)[1])?)?)\<close> ; fail),
    (* Simplify and split the current subgoal *)
    (simp (no_asm_simp) add: pred_logic simp_rules),
    ((rule ifI | rule conjI | rule impI)+)?

definition P_0
  where "P_0 blocks ret_address rsp\<^sub>0 n\<^sub>0 s \<equiv>
      seps blocks
    \<and> RSP s = rsp\<^sub>0
    \<and> master blocks (rsp\<^sub>0, 8) 1
    \<and> master blocks (rsp\<^sub>0 - 8, 8) 2
    \<and> master blocks (rsp\<^sub>0 - 16, 8) 3
    \<and> master blocks (rsp\<^sub>0 - 17, 1) 4
    \<and> master blocks (rsp\<^sub>0 - 28, 1) 5
    \<and> DL s = n\<^sub>0
    \<and> RIP s = boffset
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address
    \<and> ret_address > 102
    \<and> n\<^sub>0 > 0"

definition P_24
  where "P_24 blocks ret_address rsp\<^sub>0 (n\<^sub>0::8 word) s \<equiv>
      seps blocks
    \<and> RSP s = rsp\<^sub>0 - 40
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> master blocks (rsp\<^sub>0, 8) 1
    \<and> master blocks (rsp\<^sub>0 - 8, 8) 2
    \<and> master blocks (rsp\<^sub>0 - 16, 8) 3
    \<and> master blocks (rsp\<^sub>0 - 17, 1) 4
    \<and> master blocks (rsp\<^sub>0 - 28, 1) 5
    \<and> RIP s = boffset + 24
    \<and> RDI s = ucast n\<^sub>0 * 4
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address
    \<and> s \<turnstile> *[rsp\<^sub>0 - 28,1] = n\<^sub>0
    \<and> ret_address > 102
    \<and> n\<^sub>0 > 0"

definition P_29
  where "P_29 blocks ret_address rsp\<^sub>0 (n\<^sub>0::8word) s \<equiv>
      seps blocks
    \<and> RSP s = rsp\<^sub>0 - 40
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> master blocks (rsp\<^sub>0, 8) 1
    \<and> master blocks (rsp\<^sub>0 - 8, 8) 2
    \<and> master blocks (rsp\<^sub>0 - 16, 8) 3
    \<and> master blocks (rsp\<^sub>0 - 17, 1) 4
    \<and> master blocks (rsp\<^sub>0 - 28, 1) 5
    \<and> (RAX s \<noteq> 0 \<longrightarrow> (\<exists> i. i \<notin> fst ` blocks \<and> seps ({(i,RAX s,unat (ucast n\<^sub>0 * 4 :: 64 word))} \<union> blocks)))
    \<and> RIP s = boffset + 29
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address
    \<and> s \<turnstile> *[rsp\<^sub>0 - 28,1] = n\<^sub>0
    \<and> ret_address > 102
    \<and> n\<^sub>0 > 0"

definition P_95
  where "P_95 blocks ret_address rsp\<^sub>0 (n\<^sub>0::8 word) s \<equiv>
      seps blocks
    \<and> RSP s = rsp\<^sub>0 - 40
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> master blocks (rsp\<^sub>0, 8) 1
    \<and> master blocks (rsp\<^sub>0 - 8, 8) 2
    \<and> master blocks (rsp\<^sub>0 - 16, 8) 3
    \<and> master blocks (rsp\<^sub>0 - 17, 1) 4
    \<and> master blocks (rsp\<^sub>0 - 28, 1) 5
    \<and> (\<exists> i. i \<notin> fst ` blocks \<and> seps ({(i,s \<turnstile> *[rsp\<^sub>0 - 16,8],unat (ucast n\<^sub>0 * 4 :: 64 word))} \<union> blocks))
    \<and> RIP s = boffset + 95
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address
    \<and> s \<turnstile> *[rsp\<^sub>0 - 28,1] = n\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] \<noteq> (0::64 word)
    \<and> read_flg s flag_cf = (s \<turnstile> *[rsp\<^sub>0 - 17,1] < n\<^sub>0)
    \<and> ret_address > 102
    \<and> n\<^sub>0 > 0"

definition P_ret
  where "P_ret ret_address rsp\<^sub>0 \<sigma> \<equiv>
      RSP \<sigma> = rsp\<^sub>0 + 8 \<and> 
      RIP \<sigma> = boffset + ret_address"



lemma build_array_0_24:
  assumes "P_0 blocks ret_address rsp\<^sub>0 n\<^sub>0 s"
  shows "((\<lambda> s s' . True) s && P_24 blocks ret_address rsp\<^sub>0 n\<^sub>0) (The (run_until_pred (lines {ret_address, 24, 29}) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 17, Suc 0) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 28, Suc 0) 5\<close>
    using assms[unfolded P_0_def]
    by auto
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0"
   and "DL s = n\<^sub>0"
   and "RIP s = boffset"
   and "ret_address > 102"
   and "n\<^sub>0 > 0"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
    using assms[unfolded P_0_def]
    by auto
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
    apply (insert masters)
    apply (simp add: P_24_def)
    apply (auto simp add:  shiftl_t2n field_simps)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: P_24_def shiftl_t2n field_simps)[1]
    apply (rewrite_one_let')+
    apply (auto simp add: P_24_def shiftl_t2n field_simps)[1]
    done
qed


lemma build_array_24_24:
  assumes "P_24 blocks ret_address rsp\<^sub>0 n\<^sub>0 s"
  shows "(skip s && P_24 blocks ret_address rsp\<^sub>0 n\<^sub>0) (The (run_until_pred (lines {ret_address, 24, 29}) s))"
proof-
  have "RIP s = boffset + 24"
    using assms[unfolded P_24_def]
    by auto
  note assms' = this

  show ?thesis
    apply (insert assms')
    apply (finish_symbolic_execution)
    apply (simp add: skip_def)
    using assms
    apply (simp)
    done
qed

lemma build_array_24_29:
  assumes "P_24 blocks ret_address rsp\<^sub>0 n\<^sub>0 s"
  shows "((call\<^sub>c (malloc blocks)) s && P_29 blocks ret_address rsp\<^sub>0 n\<^sub>0) (The (run_until_pred (lines {29,ret_address}) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 17, Suc 0) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 28, Suc 0) 5\<close>
    using assms[unfolded P_24_def]
    by auto
  note masters = this
  
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 24"
   and "RDI s = ucast n\<^sub>0 * 4"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "ret_address > 102"
   and "n\<^sub>0 > 0"
   and "s \<turnstile> *[rsp\<^sub>0 - 28,1] = n\<^sub>0"
    using assms[unfolded P_24_def]
    by auto
  note assms = this

  show ?thesis
    apply (insert assms)
    apply (symbolic_execution masters: masters add: malloc_funcs[of blocks])
    apply (finish_symbolic_execution)
    apply (simp add: call\<^sub>c_def simp_rules)
    using masters 
    apply (auto simp add: P_29_def malloc_def Let_def)
    using someI_ex[of "\<lambda> a . a \<noteq> 0 \<and> (\<exists>i. i \<notin> fst ` blocks \<and> seps (insert (i, a, unat (ucast (s \<turnstile> *[rsp\<^sub>0 - 28,1] :: 8 word) * 4 :: 64 word)) blocks))"]
    by auto
qed

definition block2 :: "64 word \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  where "block2 rsp\<^sub>0 s s' \<equiv> RAX s' = 0 \<and> s' \<turnstile> *[rsp\<^sub>0 - 16, 8] = (0::64 word)"

lemma build_array_29_ret:
  assumes "(P_29 blocks ret_address rsp\<^sub>0 n\<^sub>0 && (\<lambda>s. RAX s = 0)) s"
  shows "(block2 rsp\<^sub>0 s && P_ret ret_address rsp\<^sub>0) (The (run_until_pred (line ret_address) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 17, Suc 0) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 28, Suc 0) 5\<close>
    using assms[unfolded P_29_def]
    by (auto simp add: pred_logic)
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 29"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 28,1] = n\<^sub>0"
   and "ret_address > 102"
   and "n\<^sub>0 > 0"
   and "RAX s = 0"
    using assms[unfolded P_29_def]
    by (auto simp add: pred_logic)
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
    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp add: block2_def simp_rules)
    apply (rewrite_one_let')+
    apply (simp add: block2_def simp_rules)
    by (simp add: P_ret_def)
qed

definition block3 :: "64 word \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  where "block3 rsp\<^sub>0 s s' \<equiv> s' \<turnstile> *[rsp\<^sub>0 - 17, 1] = (0::8 word) \<and> s' \<turnstile> *[rsp\<^sub>0 - 16, 8] \<noteq> (0::64 word)"


lemma build_array_29_95:
  assumes "(P_29 blocks ret_address rsp\<^sub>0 n\<^sub>0 && ! (\<lambda>s. RAX s = 0)) s"
  shows "(block3 rsp\<^sub>0 s && P_95 blocks ret_address rsp\<^sub>0 n\<^sub>0) (The (run_until_pred (lines {95,ret_address}) s))"
proof-
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 17, Suc 0) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 28, Suc 0) 5\<close>
    using assms[unfolded P_29_def]
    by (auto simp add: pred_logic)
  note masters = this

  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 29"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 28,1] = n\<^sub>0"
   and "ret_address > 102"
   and "RAX s \<noteq> 0"
   and "n\<^sub>0 > 0"
   and "\<exists> i. i \<notin> fst ` blocks \<and> seps ({(i,RAX s,unat (ucast n\<^sub>0 * 4 :: 64 word))} \<union> blocks)"
    using assms[unfolded P_29_def]
    by (auto simp add: pred_logic)
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
    apply (finish_symbolic_execution)
    apply (simp add: block3_def)[1]
    apply (insert masters)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (simp add: P_95_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    done
qed




definition block4 :: "64 word \<Rightarrow> 8 word \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  where "block4 rsp\<^sub>0 n\<^sub>0 s s' \<equiv> s' \<turnstile> *[rsp\<^sub>0 - 17, 1] = (s \<turnstile> *[rsp\<^sub>0 - 17, 1] :: 8 word) + 1
                          \<and> (s' \<turnstile> *[rsp\<^sub>0 - 16,8]) = (s \<turnstile> *[rsp\<^sub>0 - 16,8] :: 64 word)
                          \<and> (s' \<turnstile> *[rsp\<^sub>0 - 28,1]) = (s \<turnstile> *[rsp\<^sub>0 - 28,1] :: 8word)
                          \<and> RIP s' = boffset + 95
                          \<and> array_update s s' (s' \<turnstile> *[rsp\<^sub>0 - 16,8]) 4 (unat n\<^sub>0) (unat(s \<turnstile> *[rsp\<^sub>0 - 17,1]::8 word)) (0::32 word)"



lemma build_array_95_95:
  assumes "((P_95 blocks ret_address rsp\<^sub>0 n\<^sub>0) && (\<lambda> s . flags s flag_cf)) s"
shows "(block4 rsp\<^sub>0 n\<^sub>0 s && P_95 blocks ret_address rsp\<^sub>0 n\<^sub>0) (The (((\<lambda>s. (=) (step s)) ; run_until_pred (lines {ret_address,95})) s))"
proof-
  have "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 95"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 28,1] = n\<^sub>0"
   and "ret_address > 102"
   and "n\<^sub>0 > 0"
   and "flags s flag_cf"
   and "s \<turnstile> *[rsp\<^sub>0 - 17,1] < n\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] \<noteq> (0::64word)"
    using assms[unfolded P_95_def]
    by (auto simp add: pred_logic read_flg_def get_def)
  note assms' = this
  
  obtain i where i_fresh': "i \<notin> fst ` blocks" and seps: "seps ({(i,s \<turnstile> *[rsp\<^sub>0 - 16,8],unat (ucast n\<^sub>0 * 4::64 word))} \<union> blocks)"
    using assms[unfolded P_95_def]
    by (auto simp add: pred_logic)
  let ?blocks = "insert (i,s \<turnstile> *[rsp\<^sub>0 - 16,8],unat (ucast n\<^sub>0 * 4::64 word)) blocks"    

  have 1: "unat (ucast n\<^sub>0 * 4 :: 64 word) = unat n\<^sub>0 * 4"
    apply unat_arith
    by (auto simp add: unat_word_ariths unat_ucast is_up)
  have 2: "of_nat (unat (s \<turnstile> *[rsp\<^sub>0 - 17,Suc 0] :: 8 word)) = (ucast (s \<turnstile> *[rsp\<^sub>0 - 17,Suc 0]::8word) :: 64 word)"
    by unat_arith
  have masters: "master ?blocks ((s \<turnstile> *[rsp\<^sub>0 - 16,8]) + 4 * ucast (s \<turnstile> *[rsp\<^sub>0 - 17,Suc 0] :: 8 word), 4) i"
    using master_for_array_update[OF seps, of i "(s \<turnstile> *[rsp\<^sub>0 - 16,8])" 4 "unat n\<^sub>0" 
                                  "unat (ucast (s \<turnstile> *[rsp\<^sub>0 - 17,Suc 0] :: 8 word) :: 64 word)"] 
          assms'(9) 1 2
    apply (auto simp add: unat_ucast is_up) 
    apply unat_arith
    by (auto simp add: unat_ucast is_up)

  have \<open>master ?blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master ?blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master ?blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master ?blocks (rsp\<^sub>0 - 17, Suc 0) 4\<close>
   and \<open>master ?blocks (rsp\<^sub>0 - 28, Suc 0) 5\<close>
    using assms[unfolded P_95_def] i_fresh' 
    by (auto simp add: pred_logic master_insert master_implies_id_in_blocks)
  note masters = masters and this
  note masters = this

  have "i\<noteq>1" and "i\<noteq>2" and "i\<noteq>3" and "i\<noteq>4" and "i\<noteq>5"
    using assms[unfolded P_95_def] i_fresh' master_implies_id_in_blocks
    by (auto simp add: pred_logic)
  note i_fresh = this


  show ?thesis
    apply (insert assms' i_fresh seps)
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
    apply (finish_symbolic_execution)
    apply (simp add: block4_def)
    apply (rule conjI)
    apply (insert masters)[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)

    apply (rule conjI)
    apply (insert masters)[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)

    apply (rule conjI)
    apply (insert masters)[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    
    apply (insert masters)[1]
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)

    apply (rule array_update[where I=i and ts=4,simplified],simp, simp add: 1)
    apply unat_arith
    apply (rewrite_one_let' add: 2)+
    apply (simp add: simp_rules)
    apply (rewrite_one_let' add: 2)+
    apply (simp add: simp_rules 2 sep_implies_not_enclosed)
    apply (rewrite_one_let' add: 2)+
    apply (simp add: simp_rules 2 sep_implies_not_enclosed)
    apply (simp add: simp_rules 2 sep_implies_not_enclosed)

    apply (auto simp add: P_95_def)
    using assms
    apply (auto simp add: pred_logic P_95_def)[1]
    using assms
    apply (auto simp add: pred_logic P_95_def)[1]
    using assms
    apply (auto simp add: pred_logic P_95_def)[1]
    using assms
    apply (auto simp add: pred_logic P_95_def)[1]
    using assms
    apply (auto simp add: pred_logic P_95_def)[1]
    using assms
    apply (simp add: pred_logic P_95_def)[1]
    apply (insert masters seps i_fresh i_fresh')[1]
    apply (simp add: simp_rules)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply blast

    apply (insert masters seps i_fresh)[1]
    apply (simp add: simp_rules)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)

    apply (insert masters seps i_fresh)[1]
    apply (simp add: simp_rules)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
      
    apply (insert masters seps i_fresh)[1]
    apply (simp add: simp_rules Let'_def get'_def read_region'_def)

    apply (insert masters seps i_fresh)[1]
    apply (simp add: simp_rules)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules Let'_def get'_def read_region'_def)

    apply (insert masters seps i_fresh)[1]
    apply (simp add: simp_rules)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules Let'_def get'_def read_region'_def)

    done
qed

definition block5 :: "'a::len0 itself \<Rightarrow> 64 word \<Rightarrow> 8 word \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  where "block5 a rsp\<^sub>0 n\<^sub>0 s s' \<equiv> (s' \<turnstile> *[rsp\<^sub>0 - 28,1]) = (s \<turnstile> *[rsp\<^sub>0 - 28,1] :: 8 word)
                          \<and> (s' \<turnstile> *[rsp\<^sub>0 - 16,8]) = (s \<turnstile> *[rsp\<^sub>0 - 16,8] :: 64 word)
                          \<and> (s' \<turnstile> *[(s' \<turnstile> *[rsp\<^sub>0 - 16,8]),unat n\<^sub>0 * 4] :: 'a::len0 word) = (s \<turnstile> *[(s \<turnstile> *[rsp\<^sub>0 - 16,8]),unat n\<^sub>0 * 4])"


lemma build_array_95_ret:
  assumes "((P_95 blocks ret_address rsp\<^sub>0 n\<^sub>0) && ! (\<lambda> s . flags s flag_cf)) s"
  shows "(block5 a rsp\<^sub>0 n\<^sub>0 s && P_ret ret_address rsp\<^sub>0) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "RSP s = rsp\<^sub>0 - 40"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 95"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[rsp\<^sub>0 - 28,1] = n\<^sub>0"
   and "ret_address > 102"
   and "n\<^sub>0 > 0"
   and "\<not>flags s flag_cf"
   and "s \<turnstile> *[rsp\<^sub>0 - 17,1] \<ge> n\<^sub>0"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] \<noteq> (0::64word)"
    using assms[unfolded P_95_def]
    by (auto simp add: pred_logic read_flg_def get_def)
  note assms' = this

  obtain i where i_fresh': "i \<notin> fst ` blocks" and seps: "seps ({(i,s \<turnstile> *[rsp\<^sub>0 - 16,8],unat (ucast n\<^sub>0 * 4::64 word))} \<union> blocks)"
    using assms[unfolded P_95_def]
    by (auto simp add: pred_logic)
  let ?blocks = "insert (i,s \<turnstile> *[rsp\<^sub>0 - 16,8],unat (ucast n\<^sub>0 * 4::64 word)) blocks"    

  have 1: "unat n\<^sub>0 * 4 mod 18446744073709551616 = unat n\<^sub>0 * 4"
    apply (rule mod_less)
    apply unat_arith
    by auto

  have masters: "master ?blocks (s \<turnstile> *[rsp\<^sub>0 - 16,8],unat n\<^sub>0 * 4) i"
    apply (rule master_if_in_blocks)
    using seps apply simp
    by (auto simp add: unat_ucast is_up unat_word_ariths 1)
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 17, Suc 0) 4\<close>
   and \<open>master blocks (rsp\<^sub>0 - 28, Suc 0) 5\<close>
    using assms[unfolded P_95_def]
    by (auto simp add: pred_logic)
  note masters = masters and this
  note masters = masters

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (symbolic_execution masters: masters)
    apply (finish_symbolic_execution)
    apply (simp add: block5_def)
    apply (simp add: P_ret_def)
    done
qed

definition S :: "'\<sigma>\<^sub>C \<Rightarrow> 64 word \<Rightarrow> state \<Rightarrow> build_array_state \<times> '\<sigma>\<^sub>C astate_scheme"
  where "S \<sigma>\<^sub>C rsp\<^sub>0 s = (\<lparr> ptr\<^sub>v = (if RAX s = 0 then None else Some (RAX s)),
                            i\<^sub>v = s \<turnstile> *[rsp\<^sub>0 - 17, 1] \<rparr>,
                        \<lparr> ret\<^sub>v = (if s \<turnstile> *[rsp\<^sub>0 - 16, 8] = (0::64 word) then None else Some (read_array_32 s (s \<turnstile> *[rsp\<^sub>0 - 16, 8]) (unat (s \<turnstile> *[rsp\<^sub>0 - 28,1] :: 8word)))), \<dots> = \<sigma>\<^sub>C\<rparr>)"


definition abstract_build_array :: "(nat \<times> 64 word \<times> nat) set \<Rightarrow> 8 word \<Rightarrow> build_array_state \<times> 'a astate_scheme \<Rightarrow> build_array_state \<times> 'a astate_scheme \<Rightarrow> bool"
  where "abstract_build_array blocks n \<equiv>
            (\<lambda> \<sigma> \<sigma>' . True) ;
            call\<^sub>1 (abstract_malloc blocks) (\<lambda> _ . ucast n * 4) ;
            IF (\<lambda> \<sigma> . ptr\<^sub>v (\<L> \<sigma>) = None) THEN
              (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<C> \<sigma>') = None)
            ELSE
              (\<lambda> \<sigma> \<sigma>' . i\<^sub>v (\<L> \<sigma>') = 0
                      \<and> ret\<^sub>v (\<C> \<sigma>') \<noteq> None) ;
              WHILE (\<lambda> \<sigma> . i\<^sub>v (\<L> \<sigma>) < n) DO
                (\<lambda> \<sigma> \<sigma>' . i\<^sub>v (\<L> \<sigma>')  = i\<^sub>v (\<L> \<sigma>) + 1 
                        \<and> ret\<^sub>v (\<C> \<sigma>') = Some (the (ret\<^sub>v (\<C> \<sigma>))[unat (i\<^sub>v (\<L> \<sigma>)) := 0]))
              OD ;
              (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<C> \<sigma>') = ret\<^sub>v (\<C> \<sigma>))
           FI"
 


lemma build_array_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {24,29,ret_address}) ;
          run_until_pred (lines {29,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 29"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 29}" "line 24"])
  apply (simp add: line_simps)
  done

lemma build_array_decompose2:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {95,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 95"])
  apply (simp add: line_simps)
  done


lemma build_array:
  fixes a :: "'a::len word"
  assumes "32 * unat n\<^sub>0 = LENGTH('a)"
  shows "S \<sigma>\<^sub>C rsp\<^sub>0 ::
         {P_0 blocks ret_address rsp\<^sub>0 n\<^sub>0}
            run_until_pred (line ret_address) \<preceq> abstract_build_array blocks n\<^sub>0
         {P_ret ret_address rsp\<^sub>0}"
  apply (subst abstract_build_array_def)
  apply (subst build_array_decompose)
  apply (rule HL_compose[where Q="P_24 blocks ret_address rsp\<^sub>0 n\<^sub>0"])
  apply (simp add: line_simps)
  apply (rule HL_equality_intro)
  apply (rule build_array_0_24,simp)
  apply simp  
  apply (rule HL_compose[where Q="P_29 blocks ret_address rsp\<^sub>0 n\<^sub>0"])
  apply (rule HL_call\<^sub>1_generic[of "\<lambda> s . ((), \<L> S \<sigma>\<^sub>C rsp\<^sub>0 s)" _ _ "line 24" _ "P_24 blocks ret_address rsp\<^sub>0 n\<^sub>0"])
  apply (auto simp add: S_def comp_def split: if_split_asm)[1]
  apply (simp add: line_simps)
  apply (rule HL_equality_intro)
  apply (rule build_array_24_24,simp)
  apply (simp add: skip_def)
  apply (rule HL_equality_intro)
  apply (rule build_array_24_29,simp)
  apply (rule malloc_abstract_malloc,simp)
  apply (auto simp add: S_def read_array_32_write_reg P_24_def P_29_def split: option.splits)[1]
  apply (auto simp add: S_def read_array_32_write_reg P_29_def P_24_def split: option.splits)[1]
  apply (rule HL_ITE[where B="\<lambda> s . RAX s = 0"])
  apply (simp add: S_def)
  apply (rule HL_equality_intro)
  apply (rule build_array_29_ret,simp)
  apply (simp add: block2_def S_def)
  apply (subst build_array_decompose2)
  apply (rule HL_compose)
  apply (rule HL_equality_intro)
  apply (rule build_array_29_95,simp)  
  apply (simp add: block3_def S_def P_95_def)
  apply (rule HL_while_generic[of _ _ "\<lambda>s. flags s flag_cf" _ _ "line 95"])
  apply (auto simp add: P_95_def line_def S_def read_flg_def get_def)[1]
  apply (simp add: line_simps)
  apply (rule HL_equality_intro_step)
  apply (rule build_array_95_95,simp)
  apply (auto simp add: block4_def S_def P_95_def pred_logic)[1]
    apply (rule read_array_32_update_nth)     
    apply (auto simp add: block4_def S_def read_flg_def get_def)[1]
    apply unat_arith
    apply (auto simp add: block4_def S_def read_flg_def get_def)[1]
  apply (rule HL_equality_intro)
  apply (rule build_array_95_ret[where 'a='a],simp)
  using assms
  apply (auto simp add: block5_def S_def P_95_def pred_logic read_flg_def get_def)
    apply (rule read_array_32_eqI[where 'a='a])
    apply (auto)[1]
  subgoal premises prems for s s' i
  proof-
    have 1:  "unat (ucast (s' \<turnstile> *[rsp\<^sub>0 - 28,Suc 0] :: 8 word) * 4::64 word) = unat (s' \<turnstile> *[rsp\<^sub>0 - 28,Suc 0]::8 word) * 4"
      apply unat_arith
      by (auto simp add: unat_word_ariths unat_ucast is_up)
    show ?thesis
      apply (rule master_block_implies_no_block_overflow[of _ _ i])
      apply (rule master_if_in_blocks)
      using prems(16)
      apply simp
      using 1 by simp
  qed
  apply simp
  done

thm build_array

end
