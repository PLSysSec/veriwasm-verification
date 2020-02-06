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

theory TestAssemblies
  imports Main  
      "../../../x86-64_parser/Leviathan_Setup"
begin
definition m_r_Assembly :: "instr_mnemonic \<Rightarrow> nat \<Rightarrow> register_type \<Rightarrow> 64 word \<Rightarrow> register_mnemonic  \<Rightarrow> assembly"
  where "m_r_Assembly mnemonic msize rtype dst src  \<equiv>  \<lparr>text_sections = 
    [\<lparr>ts_name=''main'', instructions=[(Binary mnemonic (Memory msize (A_WordConstant dst)) (Storage (Reg (General rtype src))))]\<rparr>],
                    data_sections = [], labels_to_addresses = [], labels_to_indices=[]\<rparr>"

definition r_imm_Assembly :: "instr_mnemonic \<Rightarrow> register_type \<Rightarrow> int \<Rightarrow> register_mnemonic \<Rightarrow> assembly"
  where "r_imm_Assembly mnemonic rtype imm dst  \<equiv>  \<lparr>text_sections = 
    [\<lparr>ts_name=''main'', instructions=[(Binary mnemonic (Reg (General rtype dst)) (Immediate (ImmSixtyFour imm)) )]\<rparr>],
                    data_sections = [], labels_to_addresses = [], labels_to_indices=[]\<rparr>"

definition r_r_Assembly :: "instr_mnemonic \<Rightarrow> register_type \<Rightarrow> register_type \<Rightarrow> register_mnemonic \<Rightarrow> register_mnemonic \<Rightarrow> assembly"
  where "r_r_Assembly mnemonic rt1 rt2 dst src  \<equiv>  \<lparr>text_sections = 
    [\<lparr>ts_name=''main'', instructions=[]\<rparr>],
                    data_sections = [], labels_to_addresses = [], labels_to_indices=[]\<rparr>"

definition r_m_Assembly :: "instr_mnemonic \<Rightarrow> register_type \<Rightarrow> nat \<Rightarrow> register_mnemonic \<Rightarrow> 64 word \<Rightarrow> assembly"
  where "r_m_Assembly mnemonic rtype msize dst src  \<equiv>  \<lparr>text_sections = 
    [\<lparr>ts_name=''main'', instructions=[(Binary mnemonic  (Reg (General rtype dst)) (Storage (Memory msize (A_WordConstant src))))]\<rparr>],
                    data_sections = [], labels_to_addresses = [], labels_to_indices=[]\<rparr>"

definition m_imm_Assembly :: "instr_mnemonic \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> 64 word \<Rightarrow>  assembly"
  where "m_imm_Assembly mnemonic msize imm dst  \<equiv>  \<lparr>text_sections = 
    [\<lparr>ts_name=''main'', instructions=[(Binary mnemonic (Memory msize (A_WordConstant dst)) (Immediate (ImmSixtyFour imm)) )]\<rparr>],
                    data_sections = [], labels_to_addresses = [], labels_to_indices=[]\<rparr>"


lemmas assembly_defs = m_r_Assembly_def r_imm_Assembly_def r_r_Assembly_def r_m_Assembly_def m_imm_Assembly_def
end