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

theory Pow2
  imports "../../isabelle/Presimplified_Semantics_Manual2"
          "HOL-Library.Rewrite"
          "../../isabelle/Monads/Abstract_System"
begin

text \<open>Load the pow2.s file.\<close>
x86_64_parser "../examples/pow2/pow2.s"

text \<open>
  A Floyd invariant is a partial map from locations to state predicates.
  A location consists of an address which stores the current text section and the program
  counter.
\<close>
type_synonym floyd_invar = \<open>64 word \<rightharpoonup> (state \<Rightarrow> bool)\<close>


text \<open>A locale building a context for the pow2.s file. This locale can be auto-generated.\<close>
locale pow2_context = pow2 + presimplified_semantics
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


text \<open>
  The step function fetches the next instruction and executes it.
  This matches exactly what method rewrite\_one\_instruction is able to rewrite.
\<close>
definition step :: \<open>(unit, state) se\<close> where
  \<open>step \<sigma> \<equiv>
    let  pc = get_rip \<sigma>;
         index = the (instr_index lookup_table boffset pc) in
    let' (_,i,s) = (text_sections \<alpha>)!index;
         \<sigma> = exec_instr \<alpha> semantics pow2_flag_annotation i s \<sigma>
    in
      Some ((), \<sigma>)\<close>

lemma wps_stepI[wps_intros]:
  assumes \<open>
     let  pc = get_rip \<sigma>;
          index = the (instr_index lookup_table boffset pc) in
     let' (_,i,s) = (text_sections \<alpha>)!index;
          \<sigma> = exec_instr \<alpha> semantics pow2_flag_annotation i s \<sigma>
    in
             Q () \<sigma>\<close>
  shows \<open>wps step Q \<sigma>\<close>
  using assms
  unfolding step_def
  by (auto simp add: Let'_def Let_def wps_def)

definition halted :: \<open>64 word \<Rightarrow> state \<Rightarrow> bool\<close> where
  \<open>halted ret_address \<sigma> = (get_rip \<sigma> = boffset + ret_address)\<close>
declare halted_def[simp]

definition wf_state :: \<open>state \<Rightarrow> bool\<close> where
  \<open>wf_state _ = True\<close>
declare wf_state_def[simp]

sublocale cfg_system step \<open>halted ret_address\<close> wf_state get_rip
  by standard (simp add: det_system.is_weak_invar_def)


lemma floyd_invarI':
  assumes "pp_\<Theta> (regs s' rip) = Some \<phi>"
      and "\<phi> s'"
    shows "floyd.invar ret_address pp_\<Theta> s'"
proof-
  have 1: "floyd.isys.is_result ret_address pp_\<Theta> s' (Some s')"
    using assms(1)
    by (auto simp add: floyd.isys.is_result_def floyd.has_invar_def linvar_def split: option.splits)
  hence "The (floyd.isys.is_result ret_address pp_\<Theta> s') = Some s'"
    using floyd.isys.result_determ
          theI_unique[of "floyd.isys.is_result ret_address pp_\<Theta> s'"]
    by (auto split: option.splits simp add: floyd.invar_def floyd.isys.yields'_def)
  thus ?thesis
    using assms(1,2) 
    apply (auto simp add: floyd.invar_def floyd.isys.yields'_def linvar_def split: option.splits)
    using 1
    by metis
qed


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

end


text \<open>One locale per function in the binary.\<close>
locale pow2_function = pow2_context +
  fixes rsp\<^sub>0 :: "64 word"
    and ret_address :: "64 word"
    and blocks :: "(nat \<times> 64 word \<times> nat) set"
assumes seps: \<open>seps blocks\<close>
    and masters: \<open>master blocks (rsp\<^sub>0, 8) 0\<close>
                 \<open>master blocks (rsp\<^sub>0 - 8, 8) 1\<close>
                 \<open>master blocks (rsp\<^sub>0 - 16, 8) 2\<close>
                 \<open>master blocks (rsp\<^sub>0 - 20, 4) 3\<close>
                 \<open>master blocks (rsp\<^sub>0 - 28, 4) 4\<close>
    and ret_address: "outside ret_address 0 45"
begin


text \<open>The Floyd invariant expresses for some locations properties that are invariably true.\<close>
definition pp_\<Theta> :: floyd_invar where \<open>pp_\<Theta> \<equiv> [
  \<comment> \<open>The precondition of the program:\<close>
  boffset \<mapsto> (\<lambda>\<sigma>. RSP \<sigma> = rsp\<^sub>0
               \<and> \<sigma> \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address
               \<and> EDI \<sigma> \<le> 64),
  \<comment> \<open> The loop invariant \<close>
  boffset + 35 \<mapsto> \<lambda>\<sigma>. (\<sigma> \<turnstile> *[rsp\<^sub>0 - 16, 8]::64 word) = 2 ^ unat (EAX \<sigma>)
               \<and> \<sigma> \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address
               \<and> EAX \<sigma> \<le> EDI \<sigma>
               \<and> RSP \<sigma> = rsp\<^sub>0 - 8
               \<and> RBP \<sigma> = rsp\<^sub>0 - 8
               \<and> \<sigma> \<turnstile> *[rsp\<^sub>0 - 20, 4] = EAX \<sigma>
               \<and> \<sigma> \<turnstile> *[rsp\<^sub>0 - 28, 4] = EDI \<sigma>
               \<and> EDI \<sigma> \<le> 64,
  \<comment> \<open> The postcondition \<close>
  boffset + ret_address \<mapsto> (\<lambda>\<sigma>. RAX \<sigma> = 2 ^ unat (EDI \<sigma>))
]\<close>

schematic_goal pp_\<Theta>_zero[simp]:
  shows \<open>pp_\<Theta> boffset = ?x\<close>
  unfolding pp_\<Theta>_def
  by simp
schematic_goal pp_\<Theta>_numeral_l[simp]:
  shows \<open>pp_\<Theta> (n + boffset) = ?x\<close>
  unfolding pp_\<Theta>_def
  by simp
schematic_goal pp_\<Theta>_numeral_r[simp]:
  shows \<open>pp_\<Theta> (boffset + n) = ?x\<close>
  unfolding pp_\<Theta>_def
  by simp

lemma shiftl_is_exp2: \<open>(2 :: 'a::len word) ^ i << n = 2 ^ (i + n)\<close>
  by (simp add: power_add shiftl_t2n)

lemma rewrite_pow2:
 shows \<open>is_std_invar ret_address (floyd.invar ret_address pp_\<Theta>)\<close>
proof -

  show ?thesis
    (* Boilerplate code from Peter to start the VCG *)
    apply (rule floyd_invarI)
    apply (rewrite at \<open>floyd_vcs ret_address \<hole> _\<close> pp_\<Theta>_def)
    apply (intro floyd_vcsI)

    (* Subgoal for (ts, pc) = (0, 0) to (0, 9) *)
    subgoal premises prems for \<sigma>
    proof -
      show ?thesis
        (* Insert relevant knowledge *)
        apply (insert prems seps ret_address)
        apply (symbolic_execution masters: masters)+
        (* Proof that the reached state indeed satisfies the invariant. This is the part
           that is manual, up to here it should all be automated / boilerplate *)
        apply (insert masters)
        apply (simp add: simp_rules)
        apply rewrite_one_let'+
        apply (simp add: simp_rules)
        done
    qed

    (* Subgoal for (ts, pc) = (0, 9) to (0, 9) and to (0, 13) *)
    subgoal premises prems for \<sigma>
    proof -
      show ?thesis
        apply (insert prems seps ret_address)
        apply (symbolic_execution masters: masters)+
        subgoal
          (* This subgoal corresponds to jumping back and looping.
             The jump provides the assumption: eax < edi.
             This proves the loop invariant. *)
          apply (insert masters)
          apply (rewrite_one_let')+
          apply (simp (no_asm_simp) add: simp_rules shiftl_is_exp2)
          apply (auto simp add: unat_word_ariths(1))[1]
          subgoal premises prems'
            using prems'(5) prems'(18)
            apply unat_arith
            by (auto simp add: unat_word_ariths(1))[1]
          apply (rewrite_one_let')+
          apply (auto simp add: unat_word_ariths(1))[1]
          subgoal premises prems'
            using prems'(5)
            by unat_arith
          apply (rewrite_one_let')+
          by (auto simp add: simp_rules shiftl_is_exp2)
        subgoal
          (* This subgoal corresponds to terminating the loop. *)
          apply (restart_symbolic_execution)
          by (symbolic_execution masters: masters)+
        done
    qed

    subgoal for \<sigma>
      apply simp
      done
    done
qed

theorem pow_prog_htriple:
  shows \<open>htriple ret_address
                 (\<lambda>\<sigma>. RIP \<sigma> = boffset \<and> EDI \<sigma> \<le> 64 \<and> RSP \<sigma> = rsp\<^sub>0 \<and> \<sigma> \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address)
                 (\<lambda>\<sigma>. RIP \<sigma> = boffset + ret_address \<and> RAX \<sigma> = 2 ^ unat (EDI \<sigma>))\<close>
  apply (rule floyd_htripleI[where \<Theta> = \<open>pp_\<Theta>\<close>])
  subgoal
    apply (rule linvar_unfoldI)
    using ret_address
    by (auto simp add: outside_def)
  subgoal
    by (simp add: rewrite_pow2)
  subgoal for \<sigma> \<phi>
    unfolding pp_\<Theta>_def
    by (auto split: if_split_asm)
  done


end

end


(* 
        apply (rule wps_rls)
        apply (simp (no_asm_simp) add: step_def lookup_table_def instr_index_def entry_size_def del:)
        apply (rewrite_one_let' del: add: assembly_def)
        apply (rewrite_one_let' del: add: exec_instr_def)
        apply (rewrite_one_let' del: add:)
        apply (subst presimplify)
        apply (subst is_manual)
        apply (rewrite_one_let' del: add:)+
        apply (rule linvar_unfoldI)
        apply (simp (no_asm_simp) add: spec_of_outside del:)
*)