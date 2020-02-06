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

theory Leviathan_Setup
  imports "ObjDump_Setup" 
begin 

declare bv_cat.simps[simp del]
declare sep.simps[simp del]
declare enclosed.simps(1)[simp del]
declare write_block.simps[simp del]
declare write_bytes.simps[simp del]
declare write_blocks.simps(2)[simp del]
declare merge_blocks.simps[simp del]
declare read_bytes.simps(2)[simp del]
declare cat_bytes.simps(2)[simp del]

declare take_bits_bitAND_bit32[simp add]
declare take_bits_bitAND_bit64[simp add]
declare take_bits_bitAND_bit64_high[simp add]
declare take_bits_bitOR_bit32[simp add]
declare take_bits_bitXOR_bit32[simp add]
declare take_bits_of_take_bits[simp add]
declare take_bits_dereference_bit8[simp add]
declare take_bits_dereference_bit32[simp add]
declare rewrite_byte_of_to_take_bits[simp add]
declare rewrite_cat_bytes_to_take_bits[simp add]
declare take_bits_cat_bytes[simp add]
declare sextend.simps[simp del]

declare bv_cat.simps[simp del]
declare bv_slice.simps[simp del]

declare linorder_class.not_le[simp add]



context execution_context
begin

declare sub_sign_flag_eq_sub_overflow_flag[simp add]
declare bit_vector_simps[simp add]
declare exec_instr.simps[simp del]

lemmas simp_rules = assembly.defs(1) Let_def
                    Suc3_eq_add_3  semantics.defs(1)
                    incr_rip_def apply_binop_def jmp_def case_prod_unfold
                    take_rev drop_rev ucast_id
                    get_set_rewrite_rules sep_enclosed_simps
                    memory_read_rewrite_rules memory_write_rewrite_rules nth_ucast
                    algebra_simps

method rewrite_one_let' uses add del =
  (
     (* First, rewrite the first let' *)
     (simp (no_asm_simp) add: add simp_rules del: del imp_disjL cong: Let'_weak_cong)?,
     (* This may produce '-versions of functions, which should be substituted by their original *)
     (subst get'_def)?, (subst set'_def)?, (subst write_block'_def)?, (subst read_region'_def)?, (subst bv_cat'_def)?,
     (* Unfold the rewritten let' *)
     subst inline_Let',
     (* If the rewritten let' contained an if statement, split the goal *)
     ((rule ifI | rule conjI | rule impI)+)?,
     (* Some cleaning up of the entire goal *)
     (simp_all (no_asm_simp) only: nat_to_numeral if_not_true not_True_eq_False simp_Let'_mem simp_Let'_mem2)?
   )


method rewrite_one_instruction uses add del masters a lt =
      (
        (* Unfold the let' that instructs to fetch the next instruction *)
        rewrite_one_let' add: exec_assembly_def add del: del,
        rewrite_one_let' add: a add del: del,
        (* Unfold the assembly definition to fetch the next instruction *)
        rewrite_one_let' add: lt instr_index_def entry_size_def del: del,
        rewrite_one_let' add: a add del: del,
        (* Unfold exec_instr to start execution of the instruction *)
        rewrite_one_let' add: exec_instr.simps del: del,
        (* Add the master-knowledge to the current goal *)
        insert masters,
        (* Do rewriting of let's *)
        (rewrite_one_let' add: add del: del)+,
        (* Remove the master-knowledge from the current goal *)
        (thin_tac "master _ _ _")+
      )


ML \<open>
val fail_on_multiple_subgoals_tac =
  COND (fn st => Thm.nprems_of st > 1) no_tac all_tac
\<close>

method rewrite_one_instruction' uses add del masters a =
  determ \<open>rewrite_one_instruction add: add del: del imp_disjL masters: masters a: a\<close>,
  tactic fail_on_multiple_subgoals_tac


end
end
