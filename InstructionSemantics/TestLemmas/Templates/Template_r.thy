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

theory %1%_r%3%%6%
  imports %1%_Setup%6% %1%_r%3%_IOPairs%6%
begin

locale %2%_r%3%_test = execution_context + strata_rules_%2%
begin

schematic_goal unfold_semantics[simp]:
  shows "instr_semantics semantics instr_sig = ?x"
  by (simp add: semantics_def simp_rules)

lemma is_manual_%2%_r%3% [simp]:
  shows "is_manual assembly semantics (Unary (%7% %1%)     (Storage (Reg (General %4% r_1 )))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

abbreviation Instr   where "Instr      \<equiv> r_Instr"
abbreviation RegSrcSize where "RegSrcSize \<equiv> %4%"

declare write_block.simps    [simp del]
declare write_bytes.simps    [simp del]
declare write_blocks.simps(2)[simp del]
declare read_bytes.simps(2)  [simp del]
declare cat_bytes.simps(2)   [simp del]

declare exec_instr_def [simp add]
declare get_semantics_def [simp add]

%5%

end
end
