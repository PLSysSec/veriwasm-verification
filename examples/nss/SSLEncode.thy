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

theory SSLEncode
  imports "../../isabelle/Presimplified_Semantics_Manual2"
          "../../isabelle/Det_Step"
          "../../isabelle/Read_Array"
          "../../isabelle/Malloc"
begin

(* TO BE MERGED *)
context execution_context
begin


lemma unat_bitslice_to_32:
  fixes a :: "'b::len0 word"
  assumes "LENGTH('a) > 32"
      and "LENGTH('b) > 32"
  shows "unat (\<langle>31,0\<rangle>a :: 'a::len0 word) = unat (\<langle>31,0\<rangle>a :: 32 word)"
proof-
  have "unat ((\<langle>31,0\<rangle>a :: 'a::len0 word)) = unat (ucast (\<langle>31,0\<rangle>a :: 32 word) :: 'a::len0 word)"
    using assms
    by auto
  also have "... = unat (\<langle>31,0\<rangle>a :: 32 word)"
    apply (subst unat_ucast)
    using assms
    by (auto simp add: is_up)
  finally
  show ?thesis
    by auto
qed

lemma rewrite_take_bits_is_0_bit32: (* Do not add to simplifier, can introduce infinite rewrite loop *)
  fixes a :: "'b::len0 word"
  assumes "LENGTH('b) > 32"
      and "LENGTH('a) \<ge> LENGTH('b)"
  shows "\<langle>31,0\<rangle>a = (0::'a::len0 word) \<longleftrightarrow> \<langle>31,0\<rangle>a = (0 :: 32 word)"
  apply unat_arith
  using assms
  apply (auto)
  apply (smt le_antisym le_trans less_or_eq_imp_le linorder_neqE_nat unat_0 unat_bitslice_to_32)
  by (smt less_le_trans unat_bitslice_to_32 unat_eq_0)


(*TODO: update other theorems such as take_bits_bitXOR_bit32 *)
lemma take_bits_bitXOR_bit64[simp]:
  fixes a b :: "'a::len0 word"
  assumes "LENGTH('b) \<ge> 64"
      and "LENGTH('a) > 64"
  shows "((\<langle>63,0\<rangle>(a XOR b))::'b::len0 word) = ucast (((\<langle>63,0\<rangle>a)::64 word) XOR ((\<langle>63,0\<rangle>b)::64 word))"
proof-
  {
    fix i :: nat
    assume "i < LENGTH('b)"
    hence "((\<langle>63,0\<rangle>(a XOR b))::'b::len0 word) !! i = ((ucast (((\<langle>63,0\<rangle>a)::64 word) XOR ((\<langle>63,0\<rangle>b)::64 word))) :: 'b::len0 word) !! i"
      using assms(1-2)
      using if_test_bit_of_take_bits_is_set[of 63 0 a i,where 'b=64]
      apply (auto simp add: nth_ucast bitXOR_nth test_bit_of_take_bits word_size)
      using if_test_bit_of_take_bits_is_set[of 63 0 b i,where 'b=64]
      by auto
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed


lemma read_bytes_plus_offset:
  assumes "no_block_overflow (a, si + unat offset)"
  shows "read_bytes m (a + offset, si) = drop (unat offset) (read_bytes m (a, si + unat offset))"
proof-
  have 1: "no_block_overflow (a + offset, si)"
    using assms
    apply (auto simp add: no_block_overflow.simps field_simps)
    by unat_arith
  {
    fix i :: nat
    assume "i < si"
    hence "read_bytes m (a + offset, si) ! i = drop (unat offset) (read_bytes m (a, si + unat offset)) ! i"
      using assms 1
      by (auto simp add: spec_of_read_bytes length_read_bytes field_simps)
  }
  thus ?thesis
    apply (intro nth_equalityI)
    by (auto simp add: length_read_bytes)
qed

lemma read_bytes_smaller_block:
  assumes "no_block_overflow (a, si')"
      and "si \<le> si'"
  shows "read_bytes m (a, si) = take si (read_bytes m (a, si'))"
proof-
  have 1: "no_block_overflow (a, si)"
    using assms
    by (auto simp add: no_block_overflow.simps)
  {
    fix i :: nat
    assume "i < si"
    hence "read_bytes m (a, si) ! i = take si (read_bytes m (a, si')) ! i"
      using 1 assms 
      by (auto simp add: spec_of_read_bytes length_read_bytes field_simps)
  }
  thus ?thesis
    apply (intro nth_equalityI)
    using assms
    by (auto simp add: length_read_bytes min_def)
qed

lemma split_take_bits_into_two_parts:
  fixes x :: "'a::len0 word"
  assumes "h < LENGTH('a)"
      and "l' < h"
      and "l < l'"
  shows "(\<langle>h,l\<rangle>x :: 'a word) = ((\<langle>h,l'\<rangle>x :: 'a word) << l' - l) OR (\<langle>l'-1,l\<rangle>x :: 'a word)"
proof-
  {
    fix i
    assume "i< LENGTH('a)"
    hence "(\<langle>h,l\<rangle>x :: 'a word) !! i = (((\<langle>h,l'\<rangle>x :: 'a word) << l' - l) OR (\<langle>l'-1,l\<rangle>x :: 'a word)) !! i"
      using assms
      by (auto simp add: test_bit_of_take_bits word_ao_nth nth_shiftl field_simps)
  }
  thus ?thesis
    apply (subst word_eq_iff)
    by auto
qed

lemma test_bit_of_cat_bytes_out_of_range:
  assumes "i \<ge> length x * 8"
  shows "\<not>cat_bytes x !! i"
  apply (subst test_bit_of_cat_bytes)
  using assms
  by (auto)

lemma cat_bytes_take:
  assumes "length x * 8 - Suc 0 < LENGTH('a)"
      and "n \<le> length x"
      and "length x > 0"
  shows "(cat_bytes (take n x) :: 'a::len word) = \<langle>length x * 8 - 1,length x * 8 - n * 8\<rangle> (cat_bytes x :: 'a::len word)"
proof-
  have 1: "length x \<le> LENGTH('a) div 8"
    using assms
    by auto
  have 2: "(n * 8 + 8 * (length x - n)) = 8 * length x"
    using assms
    by auto
  have "(cat_bytes (take n x) :: 'a::len word) = \<langle>length x * 8 - 1,length x * 8 - n * 8\<rangle> (cat_bytes (take n x @ drop n x) :: 'a::len word)"
    apply (subst cat_bytes_append)
    apply (auto simp add: assms bv_cat.simps 1)
    apply (subst word_eq_iff)
    apply (rule allI)
    subgoal for i
      using 1 2 assms
      by (auto simp add: test_bit_of_take_bits sublist_def)
    apply (subst word_eq_iff)
    apply (rule allI)
    subgoal for i
      using 1 2 assms
      apply (auto simp add: test_bit_of_take_bits word_ao_nth sublist_def nth_shiftl)
      apply (subst (asm) test_bit_of_cat_bytes_out_of_range[of "drop n x"])
      apply auto
      apply (subst (asm) test_bit_of_cat_bytes_out_of_range[of "take n x"])
      by auto
    done
  thus ?thesis
    by auto
qed

lemma take_bits_zero:
  assumes "l > h"
      and "h < LENGTH('b)"
  shows "(\<langle>h,l\<rangle> (x :: 'b::len0 word) ::'a::len0 word) = 0"
proof-
  {
    fix i
    assume i: "i < LENGTH('a)"
    hence "(\<langle>h,l\<rangle> (x :: 'b::len0 word) ::'a::len0 word) !! i= (0::'a::len0 word) !! i"
      using assms 
      by (auto simp add: test_bit_of_take_bits)
  }
  thus ?thesis
    apply (subst word_eq_iff)
    by auto
qed

lemma cat_bytes_drop:
  assumes "length x * 8 - Suc 0 < LENGTH('a)"
      and "n \<le> length x"
  shows "(cat_bytes (drop n x) :: 'a::len word) = (if n = length x then 0 else \<langle>length x * 8  - n * 8 - 1,0\<rangle> (cat_bytes x :: 'a::len word))"
proof(cases "length x = n")
  case True
  thus ?thesis
    by auto
next
  case False
  have 1: "length x \<le> LENGTH('a) div 8"
    using assms
    by auto
  have "(cat_bytes (drop n x) :: 'a::len word) = \<langle>length x * 8 - n * 8 - 1,0\<rangle> (cat_bytes (take n x @ drop n x) :: 'a::len word)"
    apply (subst cat_bytes_append)
    using assms False
    apply (auto simp add: bv_cat.simps 1)
    apply (subst word_eq_iff)
    apply (rule allI)
    subgoal for i
      using 1 assms
      apply (auto simp add: test_bit_of_take_bits word_ao_nth sublist_def nth_shiftl)      
      apply (subst (asm) test_bit_of_cat_bytes_out_of_range[of "drop n x"])
      by (cases "n=0",auto simp add: min_def field_simps)
    done
  thus ?thesis
    by auto
qed

lemma dereference_with_offset:
  assumes "no_block_overflow (a, si + unat offset)"
      and "si * 8 + unat offset * 8 - Suc 0 < LENGTH('a)"
      and "si * 8 + unat offset * 8 - Suc 0 < LENGTH('b)"
      and "si > 0"
  shows "(s \<turnstile> *[a + offset, si] :: 'a::len word) = \<langle>si * 8 + unat offset * 8 - Suc 0,unat offset * 8\<rangle> (s \<turnstile> *[a, si + unat offset] :: 'b::len word)"
proof-
  have 1: "no_block_overflow (a + offset, si)"
    using assms(1)
    apply (auto simp add: no_block_overflow.simps)
    by unat_arith
  show ?thesis
    using 1 assms
    apply (auto simp add: read_region_def simp_rules Let'_def)
    apply (subst read_bytes_plus_offset)
    using assms
    by (auto simp add: rev_drop length_read_bytes cat_bytes_take)
qed

lemma dereference_smaller_size:
  assumes "no_block_overflow (a, si')"
      and "si > 0"
      and "si \<le> si'"
      and "si' * 8 - Suc 0 < LENGTH('a)"
      and "si * 8 - Suc 0 < LENGTH('b)"
  shows "(s \<turnstile> *[a, si] :: 'a::len word) = \<langle>si * 8 - 1,0\<rangle>(s \<turnstile> *[a, si'] :: 'b::len word)"
proof-
  have 1: "no_block_overflow (a, si)"
    using assms(1,3)
    by (auto simp add: no_block_overflow.simps)
  have 2: "si' * 8 - Suc ((si' - si) * 8) = si * 8 - 1"
    using assms(2-3)
    by auto
  show ?thesis
    using 1 assms
    apply (auto simp add: read_region_def simp_rules Let'_def simp del: take_bits_cat_bytes)
    apply (subst read_bytes_smaller_block[where si'=si'])
    apply (auto simp add: length_read_bytes rev_take simp del: take_bits_cat_bytes)
    apply (subst cat_bytes_drop)
    apply (auto simp add: 2 length_read_bytes simp del: take_bits_cat_bytes)
    apply (subst word_eq_iff)
    apply (auto simp add: test_bit_of_take_bits test_bit_of_cat_bytes)
    done
qed

end





record sslBuffer =
  buf :: "8 word list option"
  space :: "32 word"
  fixed :: bool
  len :: "32 word"

record sslBuffer_Grow_caller_state = 
  sslBuffer\<^sub>v :: sslBuffer
  ret\<^sub>v :: "32 word"

record sslBuffer_Grow_state = malloc_caller_state +
  newBuf\<^sub>v :: "8 word list option"
  newLen\<^sub>v :: "32 word"
  buf_ptr :: "64 word" \<comment> \<open>needed for realloc\<close>



text \<open>Load the sslencode.s file.\<close>
x86_64_parser "../examples/nss/sslencode.s"

locale sslencode_context = sslencode + presimplified_semantics
begin

abbreviation "\<alpha> \<equiv> assembly"

lemma binary_offset[simp]:
  shows "binary_offset assembly = boffset"
  by (simp add: assembly_def assembly.defs)

schematic_goal unfold_labels[simp]:
  shows "label_to_address assembly = ?x"
  apply (rule ext)
  apply (unfold label_to_address_def)
  apply (unfold binary_offset)
  by (auto simp add: label_to_address_def assembly_def assembly.defs)


fun sslencode_flag_annotation :: flag_annotation where
  \<open>sslencode_flag_annotation loc =
      (if loc \<in> {boffset + 91, boffset + 13, boffset + 131, boffset + 220, boffset + 267, boffset + 357, boffset + 481, boffset + 597, boffset + 653, boffset + 719,
                   boffset + 930, boffset + 941, boffset + 1042, boffset + 1120, boffset + 1131, boffset + 1206, boffset + 1213, boffset + 1423, boffset + 1450, boffset + 1503,
                   boffset + 1540, boffset + 1547, boffset + 1806, boffset + 1932, boffset + 2000, boffset + 2118, boffset + 2329, boffset + 2393} then
           {flag_zf}
       else if loc \<in> {boffset + 193, boffset + 208,  boffset + 1251, boffset + 1273, boffset + 1540, boffset + 1588,
                       boffset + 1610, boffset + 1710, boffset + 1846} then {flag_cf} 
       else if loc \<in> {boffset + 142, boffset + 1547, boffset + 1615, boffset + 1832, boffset + 1866, boffset + 1893, boffset + 2162} then {flag_zf,flag_cf} 
       else if loc \<in> {boffset + 2020} then {flag_zf,flag_sf,flag_of}
       else {})\<close>

definition step :: \<open>state \<Rightarrow> state\<close> where
  \<open>step \<sigma> \<equiv>
    let  pc = get_rip \<sigma>;
         boffset = binary_offset \<alpha>;
         index = the (instr_index lookup_table boffset pc) in
    let' (_,i,s) = (text_sections \<alpha>)!index;
         \<sigma> = exec_instr \<alpha> semantics sslencode_flag_annotation i s \<sigma>
    in
      \<sigma>\<close>


definition line :: "64 word \<Rightarrow> state \<Rightarrow> bool" where
  "line n \<sigma> \<equiv> get_rip \<sigma> = boffset + n"

definition lines :: "64 word set \<Rightarrow> state \<Rightarrow> bool" where
  "lines N \<sigma> \<equiv> \<exists> n \<in> N . line n \<sigma>"

lemma line_OR_line:
  shows "(line n || line m) = lines {n,m}"
  unfolding pred_OR_def lines_def
  by auto

lemma line_OR_lines:
  shows "(line n || lines N) = lines ({n} \<union> N)"
  unfolding pred_OR_def lines_def
  by auto

lemma lines_OR_lines:
  shows "(lines N || lines M) = lines (N \<union> M)"
  unfolding pred_OR_def lines_def
  by auto

lemma lines_OR_line:
  shows "(lines N || line n) = lines (N \<union> {n})"
  unfolding pred_OR_def lines_def
  by auto

lemmas line_simps = line_OR_line line_OR_lines lines_OR_lines lines_OR_line insert_commute


sublocale det_step step get_rip .



method rewrite_one_step uses masters add del =
  (subst step_seq_run)?,
  (simp (no_asm_simp) add: add step_def lookup_table_def instr_index_def entry_size_def del: del),
  (rewrite_one_let' del: del add: add assembly_def),
  (simp add: exec_instr_def),
  (subst presimplify),
  (rewrite_one_let' del: del add: add),
  (subst is_manual),
  ((insert masters)[1]),
  (rewrite_one_let' del: del add: add)+,
  ((thin_tac \<open>master _ _ _\<close>)+)?

method symbolic_execution uses masters add del =
    (* Unfold one step *)
    (subst run_until_pred_step[symmetric]),
    (* Show that we are not at the end. Otherwise, fail. *)
    (determ \<open>((auto simp add: lines_def at_loc_def pred_OR_def line_def split: if_split_asm)[1]; (unat_arith; ((auto simp add: unat_of_nat)[1])?)?)\<close> ; fail),
    (* Rewrite one step *)
    rewrite_one_step masters: masters add: add del: del
              
method finish_symbolic_execution uses add del =
    (* Stop at the current state *)
    subst run_until_pred_stop,
    (* Show that we are at the end. Otherwise, fail *)
    (determ \<open>((auto simp add: lines_def at_loc_def pred_OR_def line_def split: if_split_asm)[1]; (unat_arith; ((auto simp add: unat_of_nat)[1])?)?)\<close> ; fail),
    (* Simplify and split the current subgoal *)
    (simp (no_asm_simp) add: pred_logic simp_rules add: add del: del),
    ((rule ifI | rule conjI | rule impI)+)?


end
end


