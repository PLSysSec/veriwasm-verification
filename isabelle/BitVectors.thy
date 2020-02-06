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

theory BitVectors
  imports AbstractFloat Chum_Datatypes

begin

section \<open>Bit vectors\<close>

text \<open>
Chum consists of formula's over bit-vectors. The length of bit vectors vary, which is hard to model in Isabelle
with the standard Word library. We therefore assume a maximum length over all bit-vectors.
A bit-vector of, e.g., length 51 is modelled as a tuple with the bit-vector of that maximum length, plus the size.
This allows expressing a semantics, of, e.g., bit vector concatenation.
\<close>
abbreviation "\<M> \<equiv> 1000"
type_synonym longword = "1000 word"
type_synonym bv = "longword \<times> nat"



subsection \<open>Logical Operators\<close>

fun bv_NOT :: "bv \<Rightarrow> bv"
  where "bv_NOT (a,s) = (\<langle>s-1,0\<rangle>(NOT a), s)"

definition bv_to_bool :: "bv \<Rightarrow> bool"
  where "bv_to_bool bvf \<equiv>
      (let bit  = lsb (fst bvf);
           size = snd bvf in 
        if size \<noteq> 1 then
          undefined
        else
          bit)"

fun bool_to_bv :: "bool \<Rightarrow> bv"
  where "bool_to_bv True = (1,1)"
  | "bool_to_bv False = (0,1)"


subsection \<open>Concatenation and slicing\<close>

fun bv_slice :: "nat \<Rightarrow> nat \<Rightarrow> bv \<Rightarrow> bv"
  where "bv_slice h l (w0,s0) = (\<langle>h,l\<rangle>w0, h + 1 - l)"
declare bv_slice.simps[simp del]



subsection \<open>Arithmetic\<close>

definition exec_BV_Plus :: "bv \<Rightarrow> bv \<Rightarrow> bv" (infixl "+\<^sup>b\<^sup>v" 65)
  where "exec_BV_Plus bv1 bv2 \<equiv> let (w1,s1) = bv1;(w2,s2) = bv2 in (\<langle>max s1 s2  - 1,0\<rangle>(w1 + w2), max s1 s2)"

subsection \<open>Floating point operations\<close>

context abstract_float
begin        

definition exec_BV_Plus_Double :: "bv \<Rightarrow> bv \<Rightarrow> bv" (infixl "fplus\<^sup>b\<^sup>v" 65)
  where "exec_BV_Plus_Double bv1 bv2 \<equiv> let (w1,s1) = bv1; (w2,s2) = bv2 in (\<langle>63,0\<rangle>(\<langle>63,0\<rangle>w1 +\<^sup>f \<langle>63,0\<rangle>w2), 64)"

definition exec_BV_Sub_Double :: "bv \<Rightarrow> bv \<Rightarrow> bv" (infixl "fsub\<^sup>b\<^sup>v" 65)
  where "exec_BV_Sub_Double bv1 bv2 \<equiv> let (w1,s1) = bv1; (w2,s2) = bv2 in (\<langle>63,0\<rangle>(\<langle>63,0\<rangle>w1 -\<^sup>f \<langle>63,0\<rangle>w2), 64)"

definition exec_BV_Mul_Double :: "bv \<Rightarrow> bv \<Rightarrow> bv" (infixl "fmult\<^sup>b\<^sup>v" 65)
  where "exec_BV_Mul_Double bv1 bv2 \<equiv> let (w1,s1) = bv1; (w2,s2) = bv2 in (\<langle>63,0\<rangle>(\<langle>63,0\<rangle>w1 *\<^sup>f \<langle>63,0\<rangle>w2), 64)"

definition exec_BV_Div_Double :: "bv \<Rightarrow> bv \<Rightarrow> bv" (infixl "fdiv\<^sup>b\<^sup>v" 65)
  where "exec_BV_Div_Double bv1 bv2 \<equiv> let (w1,s1) = bv1; (w2,s2) = bv2 in (\<langle>63,0\<rangle>(\<langle>63,0\<rangle>w1 div\<^sup>f \<langle>63,0\<rangle>w2), 64)"

end

end