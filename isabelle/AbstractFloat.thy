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

theory AbstractFloat
  imports Machine
begin




definition signed_greater_than :: "'a :: len word \<Rightarrow> 'a :: len word \<Rightarrow> bool" ("(_/ >s _)" [50, 51] 50)
  where "a >s b \<equiv> a \<noteq> b \<and> \<not>(a <s b)"
declare signed_greater_than_def[symmetric,simp add]

definition signed_le :: "'a :: len word \<Rightarrow> 'a :: len word \<Rightarrow> bool" ("(_/ \<le>s _)" [50, 51] 50)
  where "a \<le>s b \<equiv> a = b \<or> a <s b"
declare signed_le_def[symmetric,simp add]

lemma signed_not_le[simp]:
  shows "\<not> a \<le>s b \<longleftrightarrow> a >s b"
  unfolding signed_le_def signed_greater_than_def
  by metis




subsection "Making a float"

text \<open> Make a float from a sign-bit, an exponent and a mantissa. \<close>
fun mk_float :: "bool \<times> nat \<times> nat \<Rightarrow> 64 word"
  where "mk_float (s,e,m) = ((if s then 1 else 0) << 63) OR (of_nat e AND mask 11 << 52) OR (of_nat m AND mask 52)"

text \<open> Simplify @{term mk_float} only when it is given concrete values. \<close>
lemmas mk_float_simps_numeral[simp] =
  mk_float.simps[of True 0 0]
  mk_float.simps[of True 0 1]
  mk_float.simps[of True 0 "numeral m"]
  mk_float.simps[of True 1 0]
  mk_float.simps[of True 1 1]
  mk_float.simps[of True 1 "numeral m"]
  mk_float.simps[of True "numeral n" 0]
  mk_float.simps[of True "numeral n" 1]
  mk_float.simps[of True "numeral n" "numeral m"]
  mk_float.simps[of False 0 0]
  mk_float.simps[of False 0 1]
  mk_float.simps[of False 0 "numeral m"]
  mk_float.simps[of False 1 0]
  mk_float.simps[of False 1 1]
  mk_float.simps[of False 1 "numeral m"]
  mk_float.simps[of False "numeral n" 0]
  mk_float.simps[of False "numeral n" 1]
  mk_float.simps[of False "numeral n" "numeral m"]
  for n m
declare mk_float.simps[simp del]

text \<open>Constants and Accessor Functions\<close>

definition plus_zero :: "64 word" ("0\<^sup>+")
  where "plus_zero \<equiv> mk_float (False,0,0)"

definition minus_zero :: "64 word" ("0\<^sup>-")
  where "minus_zero \<equiv> mk_float (True,0,0)"

definition plus_infty :: "64 word" ("\<infinity>\<^sup>+")
  where "plus_infty \<equiv> mk_float (False,2^11 - 1,0)"

definition minus_infty :: "64 word" ("\<infinity>\<^sup>-")
  where "minus_infty \<equiv> mk_float (True,2^11 - 1,0)"

definition exp :: "64 word \<Rightarrow> 64 word"
  where "exp w \<equiv> \<langle>62,52\<rangle>w"

definition mant :: "64 word \<Rightarrow> 64 word"
  where "mant w \<equiv> \<langle>51,0\<rangle>w"

definition sign :: "64 word \<Rightarrow> bool"
  where "sign \<equiv> msb"

definition isNaN :: "64 word \<Rightarrow> bool"
  where "isNaN w \<equiv> exp w = 2^11-1"

definition float_abs :: "'a::len0 word \<Rightarrow> 'a::len0 word" ("\<bar>_\<bar>\<^sup>f")
  where "\<bar>w\<bar>\<^sup>f \<equiv> set_bit w (LENGTH('a) - 1)  False"


(*
lemma sign_mk_float:
  shows "sign (mk_float (s,e,m)) = s"
  unfolding sign_def
  by (auto simp add: msb_nth mk_float.simps test_bit_of_take_bits word_ao_nth nth_shiftl)

lemma exp_mk_float:
  shows "exp (mk_float (s,e,m)) = ((of_nat e)::64 word) AND mask 11"
  unfolding exp_def
  apply word_bitwise
  by (auto simp add: mk_float.simps test_bit_of_take_bits word_ao_nth nth_shiftl)

lemma mant_mk_float:
  shows "mant (mk_float (s,e,m)) = ((of_nat m)::64 word) AND mask 52"
  unfolding mant_def
  apply word_bitwise
  apply (auto simp add: mk_float.simps test_bit_of_take_bits word_ao_nth nth_shiftl simp del: take_bits_bitAND)
  by (simp only: numeral_2_eq_2)+
*)

datatype float_cmp = Unordered | GT | LT | EQ  

text \<open>
  For the following functions, we do not yet have an implementation.
  We constraint them according the IEEE 754 standard.
\<close>

locale abstract_float =
  fixes float_plus :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word" (infixl "+\<^sup>f" 65)
    and float_minus :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word" (infixl "-\<^sup>f" 65)
    and float_times:: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word" (infixl "*\<^sup>f" 65)
    and float_div :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word" (infixl "div\<^sup>f" 65)
    and float_mod :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word" (infixl "mod\<^sup>f" 70)
    and float_ucmp :: "64 word \<Rightarrow> 64 word \<Rightarrow> float_cmp"
    and cvttsd2si :: "64 word \<Rightarrow> 32 word"
assumes plus_plus_zero [simp]: "x +\<^sup>f 0\<^sup>+ = x"
    and plus_minus_zero[simp]: "x +\<^sup>f 0\<^sup>- = x"
    and isNan_div_0_0: "x \<in> {0\<^sup>-,0\<^sup>+} \<Longrightarrow> y \<in> {0\<^sup>-,0\<^sup>+} \<Longrightarrow> isNaN (x div\<^sup>f y)"
    and div_by_plus_zero:  "x \<notin> {0\<^sup>-,0\<^sup>+} \<Longrightarrow> x div\<^sup>f 0\<^sup>+ = (if sign x then \<infinity>\<^sup>- else \<infinity>\<^sup>+)"
    and div_by_minus_zero: "x \<notin> {0\<^sup>-,0\<^sup>+} \<Longrightarrow> x div\<^sup>f 0\<^sup>- = (if sign x then \<infinity>\<^sup>+ else \<infinity>\<^sup>-)"
    and times_by_plus_zero [simp]: "x *\<^sup>f 0\<^sup>+ = (if sign x then 0\<^sup>- else 0\<^sup>+)"
    and time_by_neg_zero [simp]: "x *\<^sup>f 0\<^sup>- = (if sign x then 0\<^sup>+ else 0\<^sup>-)"
    and times_plus_zero: "0\<^sup>+ *\<^sup>f x = (if sign x then 0\<^sup>- else 0\<^sup>+)"
    and times_neg_zero: "0\<^sup>- *\<^sup>f x = (if sign x then 0\<^sup>+ else 0\<^sup>-)"
begin


end

interpretation abstract_float
  "\<lambda> x y . x"
  "\<lambda> x y . x"
  "\<lambda> x y . if y = 0\<^sup>+ then (if sign x then 0\<^sup>- else 0\<^sup>+) else if y = 0\<^sup>- then (if sign x then 0\<^sup>+ else 0\<^sup>-) else 
           if x = 0\<^sup>+ then (if sign y then 0\<^sup>- else 0\<^sup>+) else if x = 0\<^sup>- then (if sign y then 0\<^sup>+ else 0\<^sup>-)
           else x"
  "\<lambda> x y . if x \<in> {0\<^sup>-,0\<^sup>+} then mk_float(False,2^11-1,0)
           else if x = 0\<^sup>- then 0\<^sup>-
           else if y = 0\<^sup>+ then (if sign x then \<infinity>\<^sup>- else \<infinity>\<^sup>+)
           else if y = 0\<^sup>- then (if sign x then \<infinity>\<^sup>+ else \<infinity>\<^sup>-)
           else 0\<^sup>-"
  apply (unfold_locales)
  by (auto simp add: isNaN_def exp_def take_bits_def plus_zero_def minus_zero_def sign_def)



lemma bit_AND_bit_pattern_is_float_abs_bit32[simp]:
  fixes w :: "32 word"
  shows "w AND 2147483647 = \<bar>w\<bar>\<^sup>f"
  apply (word_bitwise)
  by (auto simp add: word_ao_nth float_abs_def test_bit_set_gen)
lemma bit_AND_bit_pattern_is_float_abs_bit64[simp]:
  fixes a :: "64 word"
  shows "a AND 9223372036854775807 = \<bar>a\<bar>\<^sup>f"
  unfolding float_abs_def
  apply word_bitwise
  by (auto simp add: test_bit_set_gen del: )


end


