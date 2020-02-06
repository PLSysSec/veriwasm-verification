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

theory Memcpy
  imports "HOL-Library.Rewrite"
          "../../isabelle/Monads/Abstract_System"
          "../../isabelle/Presimplified_Semantics_Manual2"
begin





text \<open>Load the memcpy.s file.\<close>
x86_64_parser "../examples/memcpy/memcpy.s"
lemmas memcpy.assembly_def [code]

text \<open>
  A Floyd invariant is a partial map from locations to state predicates.
  A location consists of a tuple (ts, pc) which stores the current text section and the program
  counter.
\<close>
type_synonym floyd_invar = \<open>64 word \<rightharpoonup> (state \<Rightarrow> bool)\<close>

locale assembly = memcpy + presimplified_semantics +
  fixes ret_address :: "64 word"
assumes ret_address: "outside ret_address 0 80"
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


fun memcpy_flag_annotation :: flag_annotation where
  \<open>memcpy_flag_annotation loc = (if loc = boffset + 59 then {flag_zf} else if loc = boffset + 35 then {flag_cf} else {})\<close>


text \<open>
  The step function fetches the next instruction and executes it.
  This matches exactly what method rewrite\_one\_instruction is able to rewrite.
\<close>
definition step :: \<open>(unit, state) se\<close> where
  \<open>step \<sigma> \<equiv>
    let  pc = get_rip \<sigma>;
         index = the (instr_index lookup_table boffset pc) in
    let' (_,i,s) = (text_sections \<alpha>)!index;
         \<sigma> = exec_instr \<alpha> semantics memcpy_flag_annotation i s \<sigma>
    in
      Some ((), \<sigma>)\<close>

lemma wps_stepI[wps_intros]:
  assumes \<open>
     let  pc = get_rip \<sigma>;
          index = the (instr_index lookup_table boffset pc) in
     let' (_,i,s) = (text_sections \<alpha>)!index;
          \<sigma> = exec_instr \<alpha> semantics memcpy_flag_annotation i s \<sigma>
    in
             Q () \<sigma>\<close>
  shows \<open>wps step Q \<sigma>\<close>
  using assms
  unfolding step_def
  by (auto simp add: Let'_def Let_def wps_def)

definition halted :: \<open>state \<Rightarrow> bool\<close> where
  \<open>halted \<sigma> = (get_rip \<sigma> = boffset + 79)\<close>
declare halted_def[simp]

definition wf_state :: \<open>state \<Rightarrow> bool\<close> where
  \<open>wf_state _ = True\<close>
declare wf_state_def[simp]

sublocale cfg_system step \<open>halted\<close> wf_state get_rip
  by standard (simp add: det_system.is_weak_invar_def)

abbreviation \<open>FS \<sigma>  \<equiv> regs \<sigma> fs\<close>


text \<open>The Floyd invariant expresses for some locations properties that are invariably true.\<close>
definition pp_\<Theta> :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> 64 word \<Rightarrow> 8 word \<Rightarrow> floyd_invar\<close>
  where \<open>pp_\<Theta> rsp\<^sub>0 rdi\<^sub>0 rsi\<^sub>0 fs\<^sub>0 v\<^sub>0 v\<^sub>1 \<equiv>
  [
  (* The precondition of the program: *)
  (boffset) \<mapsto> (\<lambda>\<sigma>. 
                 RSP \<sigma> = rsp\<^sub>0
               \<and> RDI \<sigma> = rdi\<^sub>0
               \<and> RSI \<sigma> = rsi\<^sub>0
               \<and> FS \<sigma> = fs\<^sub>0
               \<and> \<sigma> \<turnstile> *[rsi\<^sub>0,8] = v\<^sub>0
               \<and> \<sigma> \<turnstile> *[rsi\<^sub>0+8,1] = v\<^sub>1
            ),
  (* The postcondition *)
  (boffset + 79) \<mapsto> (\<lambda>\<sigma>. \<sigma> \<turnstile> *[rdi\<^sub>0,8] = v\<^sub>0 \<and> \<sigma> \<turnstile> *[rdi\<^sub>0+8,1] = v\<^sub>1)
  ]\<close>
method symbolic_execution uses masters add del =
  (rule wps_rls),
  (simp (no_asm_simp) add: add step_def lookup_table_def instr_index_def entry_size_def del: del),
  (rewrite_one_let' del: del add: add assembly_def),
  (simp add: exec_instr_def),
  (subst presimplify),
  (rewrite_one_let' del: del add: add),
  (subst is_manual),
  ((insert masters)[1]),
  (rewrite_one_let' del: del add: add)+,
  ((thin_tac \<open>master _ _ _\<close>)+)?,
  rule linvar_unfoldI,
  (simp (no_asm_simp) add: spec_of_outside add del: del)

method restart_symbolic_execution uses add del =
  ((rewrite_one_let' add: add del: del)+,
  (thin_tac \<open>master _ _ _\<close>)+,
  rule linvar_unfoldI,
  (simp (no_asm_simp) add: spec_of_outside add del: del))
|
  (((thin_tac "master _ _ _")+)?,
  rule linvar_unfoldI,
  (simp (no_asm_simp) add: spec_of_outside add del: del))

method finish_symbolic_execution uses add del masters =
  (insert masters,
   simp add: simp_rules add del: del,
   (rewrite_one_let' add: add del: del)+,
   (simp add: simp_rules add: add del: del)?,
   ((thin_tac "master _ _ _")+)?)


text \<open>Add some rules to the simplifier to simplify proofs.\<close>
schematic_goal pp_\<Theta>_zero[simp]:
  shows \<open>pp_\<Theta> rsp\<^sub>0 rdi\<^sub>0 rsi\<^sub>0 fs\<^sub>0 v\<^sub>0 v\<^sub>1 boffset = ?x\<close>
  unfolding pp_\<Theta>_def
  by simp
schematic_goal pp_\<Theta>_numeral_l[simp]:
  shows \<open>pp_\<Theta> rsp\<^sub>0 rdi\<^sub>0 rsi\<^sub>0 fs\<^sub>0 v\<^sub>0 v\<^sub>1 (n + boffset) = ?x\<close>
  unfolding pp_\<Theta>_def
  by simp
schematic_goal pp_\<Theta>_numeral_r[simp]:
  shows \<open>pp_\<Theta> rsp\<^sub>0 rdi\<^sub>0 rsi\<^sub>0 fs\<^sub>0 v\<^sub>0 v\<^sub>1 (boffset + n) = ?x\<close>
  unfolding pp_\<Theta>_def
  by simp


lemma rewrite_memcpy:
  assumes \<open>seps blocks\<close>
      and \<open>master blocks (fs\<^sub>0  + 40, 8) 1\<close>
      and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
      and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
      and \<open>master blocks (rsp\<^sub>0 - 32, Suc 0) 4\<close>
      and \<open>master blocks (rsp\<^sub>0 - 40, 8) 5\<close>
      and "master blocks (rdi\<^sub>0, 8) 6"
      and "master blocks (rdi\<^sub>0 + 8, Suc 0) 7"
      and "master blocks (rdi\<^sub>0, 9) 8"
      and "master blocks (rsi\<^sub>0, 8) 9"
      and "master blocks (rsi\<^sub>0 + 8, Suc 0) 10"
      and "master blocks (rsi\<^sub>0, 9) 11"
    shows \<open>is_std_invar (floyd.invar (pp_\<Theta> rsp\<^sub>0 rdi\<^sub>0 rsi\<^sub>0 fs\<^sub>0 v\<^sub>0 v\<^sub>1))\<close>
proof -
  (* Boilerplate code for setting up the master blocks: *)
  note masters = assms(2-)
  show ?thesis
    (* Boilerplate code from Peter to start the VCG *)
    apply (rule floyd_invarI)
    apply (rewrite at \<open>floyd_vcs \<hole> _\<close> pp_\<Theta>_def)
    apply (intro floyd_vcsI; clarsimp?)

    (* Subgoal for (ts, pc) = (6, 0) to (6, 14) *)
    subgoal premises prems for \<sigma>
    proof -
      show ?thesis
        (* Insert relevant knowledge *)
        thm prems(1)
        thm prems(2-7)[symmetric]
        apply (insert prems(1) prems(2-7)[symmetric] assms(1) ret_address)
        (* Apply VCG / symb. execution *)
        apply (symbolic_execution masters: masters) (* sub *)
        apply (symbolic_execution masters: masters) (* mov *)
        apply (symbolic_execution masters: masters) (* mov *)
        apply (symbolic_execution masters: masters) (* xor *)
        apply (symbolic_execution masters: masters) (* mov *)
        apply (symbolic_execution masters: masters) (* mov *)
        apply (symbolic_execution masters: masters) (* movzx *)
        apply (symbolic_execution masters: masters) (* mov *)
        apply (symbolic_execution masters: masters) (* mov *)
        apply (symbolic_execution masters: masters) (* mov *)
        apply (symbolic_execution masters: masters) (* movzx *)
        apply (symbolic_execution masters: masters) (* mov *)
        apply (symbolic_execution masters: masters) (* mov *)
        apply (symbolic_execution masters: masters) (* mov *)
        apply (symbolic_execution masters: masters) (* mov *)
        apply (symbolic_execution masters: masters) (* xor *)
        apply (symbolic_execution masters: masters) (* je *)
        apply (symbolic_execution masters: masters) (* add *)
        by (finish_symbolic_execution masters: masters)
    qed
    done
qed

thm rewrite_memcpy

end

end
