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

theory WC
  imports "../../isabelle/Presimplified_Semantics_Manual2"
          "../../isabelle/Det_Step"
begin

text \<open>Load the malloc.s file.\<close>
x86_64_parser "../examples/wc/wc.s"


record file_t = 
  contents :: "8 word list"
  fileptr  :: "nat"
  address  :: "64 word"

(* state function getword *)
record getword_state =
  feof_ret\<^sub>v :: "32 word"
  getc_ret\<^sub>v :: "32 word"
  isword_ret\<^sub>v :: "32 word"
  breaked\<^sub>v\<^sub>1 :: bool
  breaked\<^sub>v\<^sub>2 :: bool
  c\<^sub>v :: "32 word"

record getword_caller_state =
  ret\<^sub>v  :: "32 word"
  wcount\<^sub>v :: "64 word"
  ccount\<^sub>v :: "64 word"
  lcount\<^sub>v :: "64 word"

(* state counter *)
record counter_state = getword_caller_state +
  fp\<^sub>v :: "file_t option"

record counter_caller_state =
  total_wcount\<^sub>v :: "64 word"
  total_ccount\<^sub>v :: "64 word"
  total_lcount\<^sub>v :: "64 word"


locale wc_context = wc + presimplified_semantics 
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

fun wc_flag_annotation :: flag_annotation where
  \<open>wc_flag_annotation loc = (if loc \<in> { boffset + 639, boffset + 668, boffset + 710, boffset + 749, boffset + 775, boffset + 812,
                                         boffset + 833, boffset + 839, boffset + 1353, boffset + 884,  boffset + 965} then {flag_zf} else {})\<close>

definition step :: \<open>state \<Rightarrow> state\<close> where
  \<open>step s \<equiv>
    let  pc = get_rip s;
         index = the (instr_index lookup_table boffset pc) in
    let' (_,i,si) = (text_sections \<alpha>)!index;
         s = exec_instr \<alpha> semantics wc_flag_annotation i si s
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
    (determ \<open>((auto simp add: lines_def at_loc_def pred_OR_def line_def split: if_split_asm)[1]; (unat_arith; ((auto simp add: unat_of_nat)[1])?)?)\<close> ; fail),
    (* Rewrite one step *)
    rewrite_one_step masters: masters add: add del: del
              
method finish_symbolic_execution uses add del =
    (* Stop at the current state *)
    subst run_until_pred_stop,
    (* Show that we are at the end. Otherwise, fail *)
    (determ \<open>((auto simp add: lines_def at_loc_def pred_OR_def line_def split: if_split_asm)[1]; (unat_arith; ((auto simp add: unat_of_nat)[1])?)?)\<close> ; fail),
    (* Simplify and split the current subgoal *)
    (simp (no_asm_simp) add: pred_logic simp_rules add: add del: del),
    ((rule ifI | rule conjI | rule impI)+)?


end

end
