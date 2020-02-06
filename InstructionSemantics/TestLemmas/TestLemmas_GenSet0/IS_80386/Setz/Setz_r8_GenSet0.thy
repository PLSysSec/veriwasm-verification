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

theory Setz_r8_GenSet0
  imports Setz_Setup_GenSet0 Setz_r8_IOPairs_GenSet0
begin

locale setz_r8_test = execution_context + strata_rules_setz
begin

schematic_goal unfold_semantics[simp]:
  shows "instr_semantics semantics instr_sig = ?x"
  by (simp add: semantics_def simp_rules)

lemma is_manual_setz_r8 [simp]:
  shows "is_manual assembly semantics (Unary (IS_80386 Setz)     (Storage (Reg (General EightLow r_1 )))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

abbreviation Instr   where "Instr      \<equiv> r_Instr"
abbreviation RegSrcSize where "RegSrcSize \<equiv> EightLow"

declare write_block.simps    [simp del]
declare write_bytes.simps    [simp del]
declare write_blocks.simps(2)[simp del]
declare read_bytes.simps(2)  [simp del]
declare cat_bytes.simps(2)   [simp del]

declare exec_instr_def [simp add]
declare get_semantics_def [simp add]

lemma Test1:
  assumes "src \<in> general_regs"
    shows "(let start_regs = concat [(zip [src] Test1_src_start), Test1_xtra_regs_start]
               in exec_instr assembly semantics flag_annotation (Instr InstructionUnderTest  RegSrcSize src) 0
                            (State start_regs [] Test1_flags_start \<sigma>)) 
           = (State (concat [(zip [src] Test1_src_end),Test1_xtra_regs_end]) [] Test1_flags_end \<sigma>)"
  apply (insert assms)
  apply (simp)
  apply (rewrite_one_let' del: incr_rip_def)+
  by    (simp add:incr_rip_def to_bl_def)
lemma Test2:
  assumes "src \<in> general_regs"
    shows "(let start_regs = concat [(zip [src] Test2_src_start), Test2_xtra_regs_start]
               in exec_instr assembly semantics flag_annotation (Instr InstructionUnderTest  RegSrcSize src) 0
                            (State start_regs [] Test2_flags_start \<sigma>)) 
           = (State (concat [(zip [src] Test2_src_end),Test2_xtra_regs_end]) [] Test2_flags_end \<sigma>)"
  apply (insert assms)
  apply (simp)
  apply (rewrite_one_let' del: incr_rip_def)+
  by    (simp add:incr_rip_def to_bl_def)
lemma Test3:
  assumes "src \<in> general_regs"
    shows "(let start_regs = concat [(zip [src] Test3_src_start), Test3_xtra_regs_start]
               in exec_instr assembly semantics flag_annotation (Instr InstructionUnderTest  RegSrcSize src) 0
                            (State start_regs [] Test3_flags_start \<sigma>)) 
           = (State (concat [(zip [src] Test3_src_end),Test3_xtra_regs_end]) [] Test3_flags_end \<sigma>)"
  apply (insert assms)
  apply (simp)
  apply (rewrite_one_let' del: incr_rip_def)+
  by    (simp add:incr_rip_def to_bl_def)
lemma Test4:
  assumes "src \<in> general_regs"
    shows "(let start_regs = concat [(zip [src] Test4_src_start), Test4_xtra_regs_start]
               in exec_instr assembly semantics flag_annotation (Instr InstructionUnderTest  RegSrcSize src) 0
                            (State start_regs [] Test4_flags_start \<sigma>)) 
           = (State (concat [(zip [src] Test4_src_end),Test4_xtra_regs_end]) [] Test4_flags_end \<sigma>)"
  apply (insert assms)
  apply (simp)
  apply (rewrite_one_let' del: incr_rip_def)+
  by    (simp add:incr_rip_def to_bl_def)
lemma Test5:
  assumes "src \<in> general_regs"
    shows "(let start_regs = concat [(zip [src] Test5_src_start), Test5_xtra_regs_start]
               in exec_instr assembly semantics flag_annotation (Instr InstructionUnderTest  RegSrcSize src) 0
                            (State start_regs [] Test5_flags_start \<sigma>)) 
           = (State (concat [(zip [src] Test5_src_end),Test5_xtra_regs_end]) [] Test5_flags_end \<sigma>)"
  apply (insert assms)
  apply (simp)
  apply (rewrite_one_let' del: incr_rip_def)+
  by    (simp add:incr_rip_def to_bl_def)


end
end
