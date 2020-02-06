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

theory %1%_m%3%_r%5%%8%
  imports %1%_Setup%8% %1%_m%3%_r%5%_IOPairs%8%
begin

locale %2%_m%3%_r%5%_test = execution_context + strata_rules_%2%
begin

schematic_goal unfold_semantics[simp]:
  shows "instr_semantics semantics instr_sig = ?x"
  by (simp add: semantics_def simp_rules)

abbreviation Instr   where    "Instr      \<equiv> m_r_Instr"
abbreviation MemSize    where "MemSize    \<equiv> %4%"
abbreviation RegSrcSize where "RegSrcSize \<equiv> %6%"

declare write_block.simps    [simp del]
declare write_bytes.simps    [simp del]
declare write_blocks.simps(2)[simp del]
declare read_bytes.simps(2)  [simp del]
declare cat_bytes.simps(2)   [simp del]

%7%

end
end
