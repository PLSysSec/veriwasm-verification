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

theory TestInstructions
  imports Main  
      "reassembly_setup.Leviathan_Setup"
begin

abbreviation nullary_Instr :: " instr_mnemonic \<Rightarrow> instr"       
  where "nullary_Instr iut  \<equiv> (Nullary iut )"

abbreviation r_Instr :: " instr_mnemonic \<Rightarrow> register_type \<Rightarrow> register_mnemonic \<Rightarrow> instr"       
  where "r_Instr iut ssize src  \<equiv> (Unary iut  (Storage (Reg (General ssize src))))"

abbreviation m_Instr :: " instr_mnemonic \<Rightarrow> nat \<Rightarrow> 64 word   \<Rightarrow> instr"       
  where "m_Instr iut dsize dst  \<equiv> (Unary iut (Storage (Memory dsize (A_WordConstant dst))))"

abbreviation r_r_Instr :: " instr_mnemonic \<Rightarrow> register_type \<Rightarrow> register_mnemonic \<Rightarrow> register_type \<Rightarrow> register_mnemonic \<Rightarrow> instr"       
  where "r_r_Instr iut dsize dst ssize src \<equiv> (Binary iut (Reg (General dsize dst)) (Storage (Reg (General ssize src))))"

abbreviation r_imm_Instr :: " instr_mnemonic \<Rightarrow> register_type \<Rightarrow> register_mnemonic \<Rightarrow> int \<Rightarrow> instr"       
  where "r_imm_Instr iut dsize dst imm \<equiv> (Binary iut (Reg (General dsize dst)) (Immediate (ImmSixtyFour imm)) )"

abbreviation r_m_Instr :: " instr_mnemonic \<Rightarrow> register_type \<Rightarrow> register_mnemonic \<Rightarrow> nat \<Rightarrow> 64 word  \<Rightarrow> instr"       
  where "r_m_Instr iut dsize dst ssize src \<equiv> (Binary iut (Reg (General dsize dst)) (Storage ((Memory ssize (A_WordConstant src)))) )"

abbreviation m_r_Instr :: " instr_mnemonic \<Rightarrow> nat \<Rightarrow> 64 word  \<Rightarrow> register_type \<Rightarrow> register_mnemonic \<Rightarrow> instr"       
  where "m_r_Instr iut dsize dst ssize src \<equiv> (Binary iut (Memory dsize (A_WordConstant dst)) (Storage (Reg (General ssize src))))"

abbreviation m_imm_Instr :: " instr_mnemonic \<Rightarrow> nat \<Rightarrow> 64 word  \<Rightarrow> int \<Rightarrow> instr"       
  where "m_imm_Instr iut dsize dst imm \<equiv> (Binary iut (Memory dsize (A_WordConstant dst)) (Immediate (ImmSixtyFour imm)) )"

fun xmm_xmm_Instr :: " instr_mnemonic \<Rightarrow> 
    (register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic) \<Rightarrow>  
    (register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic) \<Rightarrow>  
    instr"       
  where "xmm_xmm_Instr iut (d3w,d2w,d1w,d0w) (s3w,s2w,s1w,s0w)  = (Binary iut (Reg (SSE d3w d2w d1w d0w )) (Storage (Reg (SSE s3w s2w s1w s0w))))"

fun ymm_ymm_Instr :: " instr_mnemonic \<Rightarrow> 
    (register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic) \<Rightarrow>  
    (register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic) \<Rightarrow>  
    instr"       
  where "ymm_ymm_Instr iut (d3w,d2w,d1w,d0w) (s3w,s2w,s1w,s0w)  = (Binary iut (Reg (AVX d3w d2w d1w d0w )) (Storage (Reg (AVX s3w s2w s1w s0w))))"

fun xmm_ymm_Instr :: " instr_mnemonic \<Rightarrow> 
    (register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic) \<Rightarrow>  
    (register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic) \<Rightarrow>  
    instr"       
  where "xmm_ymm_Instr iut (d3w,d2w,d1w,d0w) (s3w,s2w,s1w,s0w)  = (Binary iut (Reg (SSE d3w d2w d1w d0w )) (Storage (Reg (AVX s3w s2w s1w s0w))))"


fun ymm_xmm_Instr :: " instr_mnemonic \<Rightarrow> 
    (register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic) \<Rightarrow>  
    (register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic) \<Rightarrow>  
    instr"       
  where "ymm_xmm_Instr iut (d3w,d2w,d1w,d0w) (s3w,s2w,s1w,s0w)  = (Binary iut (Reg (AVX d3w d2w d1w d0w )) (Storage (Reg (SSE s3w s2w s1w s0w))))"

fun xmm_m_Instr :: " instr_mnemonic \<Rightarrow> 
    (register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic) \<Rightarrow>  
    nat \<Rightarrow> 64 word \<Rightarrow> instr"
  where "xmm_m_Instr iut (d3w,d2w,d1w,d0w) ssize src  = (Binary iut (Reg (SSE d3w d2w d1w d0w )) (Storage (Memory ssize (A_WordConstant src))) )"

fun ymm_m_Instr :: " instr_mnemonic \<Rightarrow> 
    (register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic) \<Rightarrow>  
    nat \<Rightarrow> 64 word \<Rightarrow> instr"
  where "ymm_m_Instr iut (d3w,d2w,d1w,d0w) ssize src  = (Binary iut (Reg (AVX d3w d2w d1w d0w )) (Storage (Memory ssize (A_WordConstant src))) )"

fun m_xmm_Instr :: " instr_mnemonic \<Rightarrow> 
     nat \<Rightarrow> 64 word \<Rightarrow> 
     (register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic) \<Rightarrow>  
     instr"
  where "m_xmm_Instr iut dsize dst (s3w,s2w,s1w,s0w) = (Binary iut (Memory dsize (A_WordConstant dst)) (Storage (Reg (SSE s3w s2w s1w s0w))))"

fun m_ymm_Instr :: " instr_mnemonic \<Rightarrow> 
     nat \<Rightarrow> 64 word \<Rightarrow> 
     (register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic) \<Rightarrow>  
     instr"
  where "m_ymm_Instr iut dsize dst (s3w,s2w,s1w,s0w) = (Binary iut (Memory dsize (A_WordConstant dst)) (Storage (Reg (AVX s3w s2w s1w s0w))))"

fun xmm_r_Instr :: " instr_mnemonic \<Rightarrow> 
    (register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic) \<Rightarrow>  
    register_type \<Rightarrow> register_mnemonic \<Rightarrow>  
    instr"       
  where "xmm_r_Instr iut (d3w,d2w,d1w,d0w) ssize src  = (Binary iut (Reg (SSE d3w d2w d1w d0w )) (Storage (Reg (General ssize src))))"

fun ymm_r_Instr :: " instr_mnemonic \<Rightarrow> 
    (register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic) \<Rightarrow>  
    register_type \<Rightarrow> register_mnemonic \<Rightarrow>  
    instr"       
  where "ymm_r_Instr iut (d3w,d2w,d1w,d0w) ssize src  = (Binary iut (Reg (AVX d3w d2w d1w d0w )) (Storage (Reg (General ssize src))))"

fun r_xmm_Instr :: " instr_mnemonic \<Rightarrow> 
     register_type \<Rightarrow> register_mnemonic \<Rightarrow> 
     (register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic) \<Rightarrow>  
     instr"
  where "r_xmm_Instr iut dsize dst (s3w,s2w,s1w,s0w) = (Binary iut (Reg (General dsize dst)) (Storage (Reg (SSE s3w s2w s1w s0w))))"

fun r_ymm_Instr :: " instr_mnemonic \<Rightarrow> 
     register_type \<Rightarrow> register_mnemonic \<Rightarrow> 
     (register_mnemonic \<times> register_mnemonic \<times> register_mnemonic \<times> register_mnemonic) \<Rightarrow>  
     instr"
  where "r_ymm_Instr iut dsize dst (s3w,s2w,s1w,s0w) = (Binary iut (Reg (General dsize dst)) (Storage (Reg (AVX s3w s2w s1w s0w))))"

end

