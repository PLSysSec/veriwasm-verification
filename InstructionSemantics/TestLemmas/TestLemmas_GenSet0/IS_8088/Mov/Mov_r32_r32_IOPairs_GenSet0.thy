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

theory Mov_r32_r32_IOPairs_GenSet0
  imports reassembly_machine.Machine
begin

type_synonym DstSize = "64"
type_synonym SrcSize = "64"

abbreviation Test1_dst_start :: "DstSize word list" where "Test1_dst_start \<equiv> [0xbf4ac1508d69a99d]" 
abbreviation Test1_dst_end :: "DstSize word list" where   "Test1_dst_end   \<equiv> [0xee078f05]" 
abbreviation Test1_src_start :: "SrcSize word list" where "Test1_src_start \<equiv> [0x60164718ee078f05]"
abbreviation Test1_src_end :: "SrcSize word list" where   "Test1_src_end   \<equiv> [0x60164718ee078f05]"
abbreviation Test1_flags_start :: "(flag \<times> bool) list" where "Test1_flags_start \<equiv> []"
abbreviation Test1_flags_end :: "(flag \<times> bool) list" where "Test1_flags_end \<equiv> []"
abbreviation Test1_xtra_regs_start ::  "(register_mnemonic \<times> 64 word) list"  where "Test1_xtra_regs_start  \<equiv> []"
abbreviation Test1_xtra_regs_end ::  "(register_mnemonic \<times> 64 word) list"   where "Test1_xtra_regs_end    \<equiv> []"

abbreviation Test2_dst_start :: "DstSize word list" where "Test2_dst_start \<equiv> [0xbdcf1da526979889]" 
abbreviation Test2_dst_end :: "DstSize word list" where   "Test2_dst_end   \<equiv> [0x5201b347]" 
abbreviation Test2_src_start :: "SrcSize word list" where "Test2_src_start \<equiv> [0xd77d34245201b347]"
abbreviation Test2_src_end :: "SrcSize word list" where   "Test2_src_end   \<equiv> [0xd77d34245201b347]"
abbreviation Test2_flags_start :: "(flag \<times> bool) list" where "Test2_flags_start \<equiv> []"
abbreviation Test2_flags_end :: "(flag \<times> bool) list" where "Test2_flags_end \<equiv> []"
abbreviation Test2_xtra_regs_start ::  "(register_mnemonic \<times> 64 word) list"  where "Test2_xtra_regs_start  \<equiv> []"
abbreviation Test2_xtra_regs_end ::  "(register_mnemonic \<times> 64 word) list"   where "Test2_xtra_regs_end    \<equiv> []"

abbreviation Test3_dst_start :: "DstSize word list" where "Test3_dst_start \<equiv> [0x56049a57ab5e3237]" 
abbreviation Test3_dst_end :: "DstSize word list" where   "Test3_dst_end   \<equiv> [0x64cab32b]" 
abbreviation Test3_src_start :: "SrcSize word list" where "Test3_src_start \<equiv> [0x4132376664cab32b]"
abbreviation Test3_src_end :: "SrcSize word list" where   "Test3_src_end   \<equiv> [0x4132376664cab32b]"
abbreviation Test3_flags_start :: "(flag \<times> bool) list" where "Test3_flags_start \<equiv> []"
abbreviation Test3_flags_end :: "(flag \<times> bool) list" where "Test3_flags_end \<equiv> []"
abbreviation Test3_xtra_regs_start ::  "(register_mnemonic \<times> 64 word) list"  where "Test3_xtra_regs_start  \<equiv> []"
abbreviation Test3_xtra_regs_end ::  "(register_mnemonic \<times> 64 word) list"   where "Test3_xtra_regs_end    \<equiv> []"

abbreviation Test4_dst_start :: "DstSize word list" where "Test4_dst_start \<equiv> [0x38fe914348a12838]" 
abbreviation Test4_dst_end :: "DstSize word list" where   "Test4_dst_end   \<equiv> [0x70f85f39]" 
abbreviation Test4_src_start :: "SrcSize word list" where "Test4_src_start \<equiv> [0x8892763970f85f39]"
abbreviation Test4_src_end :: "SrcSize word list" where   "Test4_src_end   \<equiv> [0x8892763970f85f39]"
abbreviation Test4_flags_start :: "(flag \<times> bool) list" where "Test4_flags_start \<equiv> []"
abbreviation Test4_flags_end :: "(flag \<times> bool) list" where "Test4_flags_end \<equiv> []"
abbreviation Test4_xtra_regs_start ::  "(register_mnemonic \<times> 64 word) list"  where "Test4_xtra_regs_start  \<equiv> []"
abbreviation Test4_xtra_regs_end ::  "(register_mnemonic \<times> 64 word) list"   where "Test4_xtra_regs_end    \<equiv> []"

abbreviation Test5_dst_start :: "DstSize word list" where "Test5_dst_start \<equiv> [0x98339fd3ba52e001]" 
abbreviation Test5_dst_end :: "DstSize word list" where   "Test5_dst_end   \<equiv> [0xe4ebd6fa]" 
abbreviation Test5_src_start :: "SrcSize word list" where "Test5_src_start \<equiv> [0x6fefb310e4ebd6fa]"
abbreviation Test5_src_end :: "SrcSize word list" where   "Test5_src_end   \<equiv> [0x6fefb310e4ebd6fa]"
abbreviation Test5_flags_start :: "(flag \<times> bool) list" where "Test5_flags_start \<equiv> []"
abbreviation Test5_flags_end :: "(flag \<times> bool) list" where "Test5_flags_end \<equiv> []"
abbreviation Test5_xtra_regs_start ::  "(register_mnemonic \<times> 64 word) list"  where "Test5_xtra_regs_start  \<equiv> []"
abbreviation Test5_xtra_regs_end ::  "(register_mnemonic \<times> 64 word) list"   where "Test5_xtra_regs_end    \<equiv> []"



end
