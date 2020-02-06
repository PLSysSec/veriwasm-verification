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

theory Bswap_r64_IOPairs_GenSet0
  imports reassembly_machine.Machine
begin

type_synonym DstSize = "64"
type_synonym SrcSize = "64"

abbreviation Test1_dst_start :: "DstSize word list" where "Test1_dst_start \<equiv> [0xbf4ac1508d69a99d]" 
abbreviation Test1_dst_end :: "DstSize word list" where   "Test1_dst_end   \<equiv> [0x9da9698d50c14abf]" 
abbreviation Test1_src_start :: "SrcSize word list" where "Test1_src_start \<equiv> [0xbf4ac1508d69a99d]"
abbreviation Test1_src_end :: "SrcSize word list" where   "Test1_src_end   \<equiv> [0x9da9698d50c14abf]"
abbreviation Test1_flags_start :: "(flag \<times> bool) list" where "Test1_flags_start \<equiv> []"
abbreviation Test1_flags_end :: "(flag \<times> bool) list" where "Test1_flags_end \<equiv> []"
abbreviation Test1_xtra_regs_start ::  "(register_mnemonic \<times> 64 word) list"  where "Test1_xtra_regs_start  \<equiv> []"
abbreviation Test1_xtra_regs_end ::  "(register_mnemonic \<times> 64 word) list"   where "Test1_xtra_regs_end    \<equiv> []"

abbreviation Test2_dst_start :: "DstSize word list" where "Test2_dst_start \<equiv> [0xbdcf1da526979889]" 
abbreviation Test2_dst_end :: "DstSize word list" where   "Test2_dst_end   \<equiv> [0x89989726a51dcfbd]" 
abbreviation Test2_src_start :: "SrcSize word list" where "Test2_src_start \<equiv> [0xbdcf1da526979889]"
abbreviation Test2_src_end :: "SrcSize word list" where   "Test2_src_end   \<equiv> [0x89989726a51dcfbd]"
abbreviation Test2_flags_start :: "(flag \<times> bool) list" where "Test2_flags_start \<equiv> []"
abbreviation Test2_flags_end :: "(flag \<times> bool) list" where "Test2_flags_end \<equiv> []"
abbreviation Test2_xtra_regs_start ::  "(register_mnemonic \<times> 64 word) list"  where "Test2_xtra_regs_start  \<equiv> []"
abbreviation Test2_xtra_regs_end ::  "(register_mnemonic \<times> 64 word) list"   where "Test2_xtra_regs_end    \<equiv> []"

abbreviation Test3_dst_start :: "DstSize word list" where "Test3_dst_start \<equiv> [0x56049a57ab5e3237]" 
abbreviation Test3_dst_end :: "DstSize word list" where   "Test3_dst_end   \<equiv> [0x37325eab579a0456]" 
abbreviation Test3_src_start :: "SrcSize word list" where "Test3_src_start \<equiv> [0x56049a57ab5e3237]"
abbreviation Test3_src_end :: "SrcSize word list" where   "Test3_src_end   \<equiv> [0x37325eab579a0456]"
abbreviation Test3_flags_start :: "(flag \<times> bool) list" where "Test3_flags_start \<equiv> []"
abbreviation Test3_flags_end :: "(flag \<times> bool) list" where "Test3_flags_end \<equiv> []"
abbreviation Test3_xtra_regs_start ::  "(register_mnemonic \<times> 64 word) list"  where "Test3_xtra_regs_start  \<equiv> []"
abbreviation Test3_xtra_regs_end ::  "(register_mnemonic \<times> 64 word) list"   where "Test3_xtra_regs_end    \<equiv> []"

abbreviation Test4_dst_start :: "DstSize word list" where "Test4_dst_start \<equiv> [0x38fe914348a12838]" 
abbreviation Test4_dst_end :: "DstSize word list" where   "Test4_dst_end   \<equiv> [0x3828a1484391fe38]" 
abbreviation Test4_src_start :: "SrcSize word list" where "Test4_src_start \<equiv> [0x38fe914348a12838]"
abbreviation Test4_src_end :: "SrcSize word list" where   "Test4_src_end   \<equiv> [0x3828a1484391fe38]"
abbreviation Test4_flags_start :: "(flag \<times> bool) list" where "Test4_flags_start \<equiv> []"
abbreviation Test4_flags_end :: "(flag \<times> bool) list" where "Test4_flags_end \<equiv> []"
abbreviation Test4_xtra_regs_start ::  "(register_mnemonic \<times> 64 word) list"  where "Test4_xtra_regs_start  \<equiv> []"
abbreviation Test4_xtra_regs_end ::  "(register_mnemonic \<times> 64 word) list"   where "Test4_xtra_regs_end    \<equiv> []"

abbreviation Test5_dst_start :: "DstSize word list" where "Test5_dst_start \<equiv> [0x98339fd3ba52e001]" 
abbreviation Test5_dst_end :: "DstSize word list" where   "Test5_dst_end   \<equiv> [0x1e052bad39f3398]" 
abbreviation Test5_src_start :: "SrcSize word list" where "Test5_src_start \<equiv> [0x98339fd3ba52e001]"
abbreviation Test5_src_end :: "SrcSize word list" where   "Test5_src_end   \<equiv> [0x1e052bad39f3398]"
abbreviation Test5_flags_start :: "(flag \<times> bool) list" where "Test5_flags_start \<equiv> []"
abbreviation Test5_flags_end :: "(flag \<times> bool) list" where "Test5_flags_end \<equiv> []"
abbreviation Test5_xtra_regs_start ::  "(register_mnemonic \<times> 64 word) list"  where "Test5_xtra_regs_start  \<equiv> []"
abbreviation Test5_xtra_regs_end ::  "(register_mnemonic \<times> 64 word) list"   where "Test5_xtra_regs_end    \<equiv> []"



end
