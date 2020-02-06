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

theory Cmpxchg_r8_rh_IOPairs_GenSet0
  imports reassembly_machine.Machine
begin

type_synonym DstSize = "64"
type_synonym SrcSize = "64"

abbreviation Test1_dst_start :: "DstSize word list" where "Test1_dst_start \<equiv> [0xbf4ac1508d69a99d]" 
abbreviation Test1_dst_end :: "DstSize word list" where   "Test1_dst_end   \<equiv> [0xbf4ac1508d69a99d]" 
abbreviation Test1_src_start :: "SrcSize word list" where "Test1_src_start \<equiv> [0x60164718ee078f05]"
abbreviation Test1_src_end :: "SrcSize word list" where   "Test1_src_end   \<equiv> [0x60164718ee078f05]"
abbreviation Test1_flags_start :: "(flag \<times> bool) list" where "Test1_flags_start \<equiv> [(flag_cf, False),(flag_pf, True),(flag_zf, True),(flag_sf, True),(flag_of, True)]"
abbreviation Test1_flags_end :: "(flag \<times> bool) list" where "Test1_flags_end \<equiv> [(flag_cf, True),(flag_pf, undefined),(flag_zf, False),(flag_sf, True),(flag_of, True)]"
abbreviation Test1_xtra_regs_start ::  "(register_mnemonic \<times> 64 word) list"  where "Test1_xtra_regs_start  \<equiv> [(rax,0x33c411e159c97046)]"
abbreviation Test1_xtra_regs_end ::  "(register_mnemonic \<times> 64 word) list"   where "Test1_xtra_regs_end    \<equiv> [(rax,0x33c411e159c9709d)]"

abbreviation Test2_dst_start :: "DstSize word list" where "Test2_dst_start \<equiv> [0xbdcf1da526979889]" 
abbreviation Test2_dst_end :: "DstSize word list" where   "Test2_dst_end   \<equiv> [0xbdcf1da526979889]" 
abbreviation Test2_src_start :: "SrcSize word list" where "Test2_src_start \<equiv> [0xd77d34245201b347]"
abbreviation Test2_src_end :: "SrcSize word list" where   "Test2_src_end   \<equiv> [0xd77d34245201b347]"
abbreviation Test2_flags_start :: "(flag \<times> bool) list" where "Test2_flags_start \<equiv> [(flag_cf, True),(flag_pf, True),(flag_zf, True),(flag_sf, False),(flag_of, True)]"
abbreviation Test2_flags_end :: "(flag \<times> bool) list" where "Test2_flags_end \<equiv> [(flag_cf, True),(flag_pf, undefined),(flag_zf, False),(flag_sf, True),(flag_of, True)]"
abbreviation Test2_xtra_regs_start ::  "(register_mnemonic \<times> 64 word) list"  where "Test2_xtra_regs_start  \<equiv> [(rax,0x903d7060777c0275)]"
abbreviation Test2_xtra_regs_end ::  "(register_mnemonic \<times> 64 word) list"   where "Test2_xtra_regs_end    \<equiv> [(rax,0x903d7060777c0289)]"

abbreviation Test3_dst_start :: "DstSize word list" where "Test3_dst_start \<equiv> [0x56049a57ab5e3237]" 
abbreviation Test3_dst_end :: "DstSize word list" where   "Test3_dst_end   \<equiv> [0x56049a57ab5e3237]" 
abbreviation Test3_src_start :: "SrcSize word list" where "Test3_src_start \<equiv> [0x4132376664cab32b]"
abbreviation Test3_src_end :: "SrcSize word list" where   "Test3_src_end   \<equiv> [0x4132376664cab32b]"
abbreviation Test3_flags_start :: "(flag \<times> bool) list" where "Test3_flags_start \<equiv> [(flag_cf, False),(flag_pf, False),(flag_zf, False),(flag_sf, False),(flag_of, True)]"
abbreviation Test3_flags_end :: "(flag \<times> bool) list" where "Test3_flags_end \<equiv> [(flag_cf, False),(flag_pf, undefined),(flag_zf, False),(flag_sf, True),(flag_of, False)]"
abbreviation Test3_xtra_regs_start ::  "(register_mnemonic \<times> 64 word) list"  where "Test3_xtra_regs_start  \<equiv> [(rax,0x274428fa660730fb)]"
abbreviation Test3_xtra_regs_end ::  "(register_mnemonic \<times> 64 word) list"   where "Test3_xtra_regs_end    \<equiv> [(rax,0x274428fa66073037)]"

abbreviation Test4_dst_start :: "DstSize word list" where "Test4_dst_start \<equiv> [0x38fe914348a12838]" 
abbreviation Test4_dst_end :: "DstSize word list" where   "Test4_dst_end   \<equiv> [0x38fe914348a12838]" 
abbreviation Test4_src_start :: "SrcSize word list" where "Test4_src_start \<equiv> [0x8892763970f85f39]"
abbreviation Test4_src_end :: "SrcSize word list" where   "Test4_src_end   \<equiv> [0x8892763970f85f39]"
abbreviation Test4_flags_start :: "(flag \<times> bool) list" where "Test4_flags_start \<equiv> [(flag_cf, False),(flag_pf, False),(flag_zf, False),(flag_sf, True),(flag_of, False)]"
abbreviation Test4_flags_end :: "(flag \<times> bool) list" where "Test4_flags_end \<equiv> [(flag_cf, True),(flag_pf, undefined),(flag_zf, False),(flag_sf, True),(flag_of, False)]"
abbreviation Test4_xtra_regs_start ::  "(register_mnemonic \<times> 64 word) list"  where "Test4_xtra_regs_start  \<equiv> [(rax,0x2f579ae04cc1fc1e)]"
abbreviation Test4_xtra_regs_end ::  "(register_mnemonic \<times> 64 word) list"   where "Test4_xtra_regs_end    \<equiv> [(rax,0x2f579ae04cc1fc38)]"

abbreviation Test5_dst_start :: "DstSize word list" where "Test5_dst_start \<equiv> [0x98339fd3ba52e001]" 
abbreviation Test5_dst_end :: "DstSize word list" where   "Test5_dst_end   \<equiv> [0x98339fd3ba52e001]" 
abbreviation Test5_src_start :: "SrcSize word list" where "Test5_src_start \<equiv> [0x6fefb310e4ebd6fa]"
abbreviation Test5_src_end :: "SrcSize word list" where   "Test5_src_end   \<equiv> [0x6fefb310e4ebd6fa]"
abbreviation Test5_flags_start :: "(flag \<times> bool) list" where "Test5_flags_start \<equiv> [(flag_cf, True),(flag_pf, True),(flag_zf, False),(flag_sf, True),(flag_of, True)]"
abbreviation Test5_flags_end :: "(flag \<times> bool) list" where "Test5_flags_end \<equiv> [(flag_cf, False),(flag_pf, undefined),(flag_zf, False),(flag_sf, True),(flag_of, False)]"
abbreviation Test5_xtra_regs_start ::  "(register_mnemonic \<times> 64 word) list"  where "Test5_xtra_regs_start  \<equiv> [(rax,0x15866f61fc3fc0d4)]"
abbreviation Test5_xtra_regs_end ::  "(register_mnemonic \<times> 64 word) list"   where "Test5_xtra_regs_end    \<equiv> [(rax,0x15866f61fc3fc001)]"



end
