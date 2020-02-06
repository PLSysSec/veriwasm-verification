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

theory Sub_r32_r32_GenSet0
  imports Sub_Setup_GenSet0 Sub_r32_r32_IOPairs_GenSet0 "reassembly_setup.Leviathan_Setup"
begin

locale sub_r32_r32_test = execution_context + strata_rules_sub
begin

schematic_goal unfold_semantics[simp]:
  shows "instr_semantics semantics instr_sig = ?x"
  by (simp add: semantics_def simp_rules)

lemma is_manual_sub_r32_r32 [simp]:
  shows "is_manual assembly semantics (Binary (IS_8088 Sub) (Reg (General  ThirtyTwo r_1)) (Storage (Reg (General ThirtyTwo r_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

abbreviation Instr   where "Instr      \<equiv> r_r_Instr"
abbreviation RegDstSize where "RegDstSize \<equiv> ThirtyTwo"
abbreviation RegSrcSize where "RegSrcSize \<equiv> ThirtyTwo"

declare write_block.simps    [simp del]
declare write_bytes.simps    [simp del]
declare write_blocks.simps(2)[simp del]
declare read_bytes.simps(2)  [simp del]
declare cat_bytes.simps(2)   [simp del]

declare exec_instr_def [simp add]
declare get_semantics_def [simp add]

lemma Test1:
  assumes "dst \<noteq> src"
  and     "dst \<in> general_regs"
  and     "src \<in> general_regs"
shows "    (let  start_regs = concat [(zip [dst] Test1_dst_start), (zip [src] Test1_src_start), Test1_xtra_regs_start]
            in   exec_instr assembly semantics flag_annotation (Instr InstructionUnderTest RegDstSize dst RegSrcSize src) 0
                            (State start_regs [] Test1_flags_start \<sigma>)) 
            = (State (concat [(zip [dst] Test1_dst_end),(zip [src] Test1_src_end),Test1_xtra_regs_end]) [] Test1_flags_end \<sigma>)"
  apply (insert assms)
  apply (simp)
  apply (rewrite_one_let' del: incr_rip_def)+
  by    (simp add:incr_rip_def)
lemma Test2:
  assumes "dst \<noteq> src"
  and     "dst \<in> general_regs"
  and     "src \<in> general_regs"
shows "    (let  start_regs = concat [(zip [dst] Test2_dst_start), (zip [src] Test2_src_start), Test2_xtra_regs_start]
            in   exec_instr assembly semantics flag_annotation (Instr InstructionUnderTest RegDstSize dst RegSrcSize src) 0
                            (State start_regs [] Test2_flags_start \<sigma>)) 
            = (State (concat [(zip [dst] Test2_dst_end),(zip [src] Test2_src_end),Test2_xtra_regs_end]) [] Test2_flags_end \<sigma>)"
  apply (insert assms)
  apply (simp)
  apply (rewrite_one_let' del: incr_rip_def)+
  by    (simp add:incr_rip_def)
lemma Test3:
  assumes "dst \<noteq> src"
  and     "dst \<in> general_regs"
  and     "src \<in> general_regs"
shows "    (let  start_regs = concat [(zip [dst] Test3_dst_start), (zip [src] Test3_src_start), Test3_xtra_regs_start]
            in   exec_instr assembly semantics flag_annotation (Instr InstructionUnderTest RegDstSize dst RegSrcSize src) 0
                            (State start_regs [] Test3_flags_start \<sigma>)) 
            = (State (concat [(zip [dst] Test3_dst_end),(zip [src] Test3_src_end),Test3_xtra_regs_end]) [] Test3_flags_end \<sigma>)"
  apply (insert assms)
  apply (simp)
  apply (rewrite_one_let' del: incr_rip_def)+
  by    (simp add:incr_rip_def)
lemma Test4:
  assumes "dst \<noteq> src"
  and     "dst \<in> general_regs"
  and     "src \<in> general_regs"
shows "    (let  start_regs = concat [(zip [dst] Test4_dst_start), (zip [src] Test4_src_start), Test4_xtra_regs_start]
            in   exec_instr assembly semantics flag_annotation (Instr InstructionUnderTest RegDstSize dst RegSrcSize src) 0
                            (State start_regs [] Test4_flags_start \<sigma>)) 
            = (State (concat [(zip [dst] Test4_dst_end),(zip [src] Test4_src_end),Test4_xtra_regs_end]) [] Test4_flags_end \<sigma>)"
  apply (insert assms)
  apply (simp)
  apply (rewrite_one_let' del: incr_rip_def)+
  by    (simp add:incr_rip_def)
lemma Test5:
  assumes "dst \<noteq> src"
  and     "dst \<in> general_regs"
  and     "src \<in> general_regs"
shows "    (let  start_regs = concat [(zip [dst] Test5_dst_start), (zip [src] Test5_src_start), Test5_xtra_regs_start]
            in   exec_instr assembly semantics flag_annotation (Instr InstructionUnderTest RegDstSize dst RegSrcSize src) 0
                            (State start_regs [] Test5_flags_start \<sigma>)) 
            = (State (concat [(zip [dst] Test5_dst_end),(zip [src] Test5_src_end),Test5_xtra_regs_end]) [] Test5_flags_end \<sigma>)"
  apply (insert assms)
  apply (simp)
  apply (rewrite_one_let' del: incr_rip_def)+
  by    (simp add:incr_rip_def)


end
end
