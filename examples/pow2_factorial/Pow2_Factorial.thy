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

theory Pow2_Factorial
  imports "../../isabelle/Presimplified_Semantics_Manual2"
          "../../isabelle/Det_Step"

begin

text \<open>Load the pow2_factorial.s file.\<close>
x86_64_parser "../examples/pow2_factorial/pow2_factorial.s"

locale pow2_factorial_context = pow2_factorial + presimplified_semantics +
  assumes[simp] : "funcs ''factorial'' = None" \<comment> \<open>There is no predefined factorial function\<close>
begin

abbreviation "\<alpha> \<equiv> assembly"

schematic_goal unfold_semantics:
  shows \<open>instr_semantics semantics instr_sig = ?x\<close>
  by (simp add: semantics_def simp_rules)

lemma binary_offset[simp]:
  shows "binary_offset assembly = boffset"
  by (simp add: assembly_def assembly.defs)
schematic_goal unfold_labels[simp]:
  shows "label_to_address assembly = ?x"
  apply (rule ext)
  apply (unfold label_to_address_def)
  apply (unfold binary_offset)
  by (auto simp add: label_to_address_def assembly_def assembly.defs)

fun pow2_factorial_flag_annotation :: flag_annotation where
  \<open>pow2_factorial_flag_annotation loc = (if loc \<in> {boffset + 60} then {flag_zf} else {})\<close>

definition step :: \<open>state \<Rightarrow> state\<close> where
  \<open>step s \<equiv>
    let  pc = get_rip s;
         index = the (instr_index lookup_table boffset pc) in
    let' (_,i,si) = (text_sections \<alpha>)!index;
         s = exec_instr \<alpha> semantics pow2_factorial_flag_annotation i si s
    in
      s\<close>


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
              
method finish_symbolic_execution =
    (* Stop at the current state *)
    subst run_until_pred_stop,
    (* Show that we are at the end. Otherwise, fail *)
    (determ \<open>((auto simp add: lines_def at_loc_def pred_OR_def line_def split: if_split_asm)[1]; (unat_arith; ((auto simp add: unat_of_nat)[1])?)?)\<close> ; fail),
    (* Simplify and split the current subgoal *)
    (simp (no_asm_simp) add: pred_logic simp_rules),
    ((rule ifI | rule conjI | rule impI)+)?




end



context pow2_factorial_context
begin
  

definition P_46
  where "P_46 blocks ret_address n\<^sub>0 rsp\<^sub>0 s \<equiv>
      seps blocks
    \<and> (\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 48, 8) (2001 - unat j + unat i))
    \<and> (\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 56, 8) (3001 - unat j + unat i))
    \<and> (\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 64, 8) (4001 - unat j + unat i))
    \<and> (\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 72, 8) (5001 - unat j + unat i))
    \<and> (\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 76, Suc 0) (6001 - unat j + unat i))
    \<and> (\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 84, Suc 0) (7001 - unat j + unat i))
    \<and> RSP s = rsp\<^sub>0 
    \<and> DL s = n\<^sub>0
    \<and> s \<turnstile> *[RSP s,8] = boffset + ret_address
    \<and> RIP s = boffset + 46
    \<and> ret_address > 150" (* TODO *)

definition "DL_is_0 s \<equiv> DL s = 0"
definition P_64
  where "P_64 blocks n\<^sub>0 ret_address rsp\<^sub>0 s \<equiv>
      seps blocks
    \<and> DL s \<le> n\<^sub>0
    \<and> flags s flag_zf = (DL_is_0 s)
    \<and> RSP s = rsp\<^sub>0 - 40 - ucast (n\<^sub>0 - DL s) * 48
    \<and> RBP s = RSP s + 32
    \<and> (\<forall> i < n\<^sub>0 - DL s . s \<turnstile> *[RSP s + (ucast i) * 48 + 24, 8] = (ucast (DL s + i + 1) :: 64 word))
    \<and> (\<forall> i \<le> n\<^sub>0 - DL s . s \<turnstile> *[RSP s + (ucast i) * 48 + 12, 1] = DL s + i)
    \<and> (\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 48, 8) (2001 - unat j + unat i))
    \<and> (\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 56, 8) (3001 - unat j + unat i))
    \<and> (\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 64, 8) (4001 - unat j + unat i))
    \<and> (\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 72, 8) (5001 - unat j + unat i))
    \<and> (\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 76, Suc 0) (6001 - unat j + unat i))
    \<and> (\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 84, Suc 0) (7001 - unat j + unat i))
    \<and> (\<forall> i < n\<^sub>0 - DL s . s \<turnstile> *[RSP s + (ucast i) * 48 + 40, 8] = boffset + 87) 
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address
    \<and> s \<turnstile> *[RSP s + 12,1] = DL s (* TODO remove *)
    \<and> RIP s = boffset + 64
    \<and> (DL s < n\<^sub>0 \<longrightarrow> RBX s = ucast (DL s + 1))
    \<and> ret_address > 150" (* TODO *)

definition P_104
  where "P_104 blocks (n\<^sub>0 :: 8 word) ret_address rsp\<^sub>0 s \<equiv>
      seps blocks
    \<and> n\<^sub>0 \<ge> (s \<turnstile> *[RSP s - 28,1])
    \<and> RSP s = rsp\<^sub>0 - ucast (n\<^sub>0 - (s \<turnstile> *[RSP s - 28, 1])) * 48
    \<and> (\<forall> i < n\<^sub>0 - (s \<turnstile> *[RSP s - 28, 1]) . s \<turnstile> *[RSP s + (ucast i) * 48 - 16, 8] = (ucast ((s \<turnstile> *[RSP s - 28, 1]) + i + 1 :: 8 word) :: 64 word))
    \<and> (\<forall> i \<le> n\<^sub>0 - (s \<turnstile> *[RSP s - 28, 1]) . s \<turnstile> *[RSP s + (ucast i) * 48 - 28, 1] = (s \<turnstile> *[RSP s - 28, 1]) + i)
    \<and> (\<forall> i < n\<^sub>0 - (s \<turnstile> *[RSP s - 28, 1]) . s \<turnstile> *[RSP s + (ucast i) * 48, 8] = boffset + 87) 
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address
    \<and> RIP s = boffset + 104
    \<and> ((s \<turnstile> *[regs s rsp - 28,1]) < n\<^sub>0 \<longrightarrow> RBX s = ucast ((s \<turnstile> *[regs s rsp - 28,1]) + 1 :: 8 word))
    \<and> ret_address > 150" (* TODO *)

definition P_ret
  where "P_ret ret_address rsp\<^sub>0 s \<equiv>
      RIP s = boffset + ret_address
    \<and> RSP s = rsp\<^sub>0 + 8"

definition block1 :: "8 word \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  where "block1 n\<^sub>0 s s' \<equiv> DL s' = n\<^sub>0"

lemma factorial_46:
assumes "(P_46 blocks ret_address n\<^sub>0 rsp\<^sub>0) s"
shows "(block1 n\<^sub>0 s && P_64 blocks n\<^sub>0 ret_address rsp\<^sub>0) (The (run_until_pred (lines {ret_address, 64, 104}) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 46"
   and "ret_address > 150"
   and "DL s = n\<^sub>0"
   and "rsp\<^sub>0 = regs s rsp"
   and "s \<turnstile> *[regs s rsp,8] = boffset + ret_address"
    using assms[unfolded P_46_def]
    by auto
  note assms' = this

  have "(\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 48, 8) (2001 - unat j + unat i))"
   and "(\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 56, 8) (3001 - unat j + unat i))"
   and "(\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 64, 8) (4001 - unat j + unat i))"
   and "(\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 72, 8) (5001 - unat j + unat i))"
   and "(\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 76, Suc 0) (6001 - unat j + unat i))"
   and "(\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 84, Suc 0) (7001 - unat j + unat i))"
    using assms[unfolded P_46_def]
    by (auto simp add: pred_logic)
  note masters =  this
  have \<open>master blocks (RSP s, 8) 2000\<close>
   and \<open>master blocks (RSP s - 8, 8) 3000\<close>
   and \<open>master blocks (RSP s - 16, 8) 4000\<close>
   and \<open>master blocks (RSP s - 24, 8) 5000\<close>
   and \<open>master blocks (RSP s - 28, Suc 0) 6000\<close>
   and \<open>master blocks (RSP s - 36, Suc 0) 7000\<close>
    using masters[THEN spec,THEN spec,of 1 0] assms'(5)
    by (auto simp add: field_simps unat_ucast is_up)
  note masters = this

  have 2: "(18446744073709551576::64 word) = -40"
   and 3: "(18446744073709551584::64 word) = -32"
   and 4: "(255 :: 8 word) = -1"
    by auto

  show ?thesis
    apply (insert assms' 2 3 4)
    apply (symbolic_execution masters: masters) (* push *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* push *)
    apply (symbolic_execution masters: masters) (* sub *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (finish_symbolic_execution)
    apply (simp add: block1_def)
    using assms
    apply (auto simp add: P_64_def P_46_def DL_is_0_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    done
qed

definition block3 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block3 s s' \<equiv> RAX s' = 1 \<and> (s' \<turnstile> *[RSP s' - 28, 1] :: 8 word) = DL s"



lemma factorial_64_104:
assumes "((P_64 blocks n\<^sub>0 ret_address rsp\<^sub>0) && (\<lambda>s. flags s flag_zf)) s"
  shows "(block3 s && P_104 blocks n\<^sub>0 ret_address rsp\<^sub>0) (The ((run_until_pred (lines {ret_address,104}) s)))"
proof-
  have "seps blocks"
   and "DL s \<le> n\<^sub>0"
   and "RBP s = RSP s + 32"
   and "RIP s = boffset + 64"
   and "ret_address > 150"
   and "flags s flag_zf"
   and "s \<turnstile> *[RSP s + 12,1] = DL s"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "RSP s + ucast (n\<^sub>0 - DL s) * 48 = rsp\<^sub>0 - 40"
   and "DL s < n\<^sub>0 \<longrightarrow> RBX s = ucast (DL s + 1)"
    using assms[unfolded P_64_def]
    by (auto simp add: pred_logic)
  note assms' = this

  have 0:"\<forall> i < n\<^sub>0 - DL s . s \<turnstile> *[RSP s + (ucast i) * 48 + 24, 8] = (ucast (DL s + i + 1) :: 64 word)"
    using assms[unfolded P_64_def]
    by (auto simp add: pred_logic)
  have 0: "DL s < n\<^sub>0 \<Longrightarrow> s \<turnstile> *[regs s rsp + 24,8] = (ucast (DL s + 1) :: 64 word)"
    using 0[THEN spec,of 0]
    by auto

  note masters = assms'(1)

  have 2: "(18446744073709551608::64 word) = -8"
   and 3: "(18446744073709551568::64 word) = -48"
   and 4: "(255 :: 8 word) = -1"
    by auto

  show ?thesis
    apply (insert assms' 2 3 4)
    apply (symbolic_execution masters: ) (* je *)
    apply (symbolic_execution masters: ) (* mov *)
    apply (symbolic_execution masters: ) (* add *)
    apply (symbolic_execution masters: ) (* pop *)
    apply (symbolic_execution masters: ) (* pop *)
    apply (finish_symbolic_execution)
    apply (simp add: block3_def)
    using assms[unfolded P_64_def]
    apply (auto simp add: field_simps pred_logic)[1]
    apply (auto simp add: P_104_def) 
    apply (simp add: field_simps)
    using assms[unfolded P_64_def]
    apply (auto simp add: field_simps pred_logic)[1]
    using assms[unfolded P_64_def]
    apply (auto simp add: field_simps pred_logic)[1]
    using assms[unfolded P_64_def]
    apply (auto simp add: field_simps pred_logic)[1]
    using assms[unfolded P_64_def]
    apply (auto simp add: field_simps pred_logic)[1]
    using 0
    apply (auto simp add: field_simps pred_logic ucast_id)[1]
    done
qed

function read_array :: "state \<Rightarrow> 8 word \<Rightarrow> 64 word \<Rightarrow> 64 word list"
  where "read_array s i offset = (if i = 0 then [] else (read_array s (i-1) offset)@[s \<turnstile> *[RSP s + ucast (i-1) * 48 + offset, 8]])"
  by (pat_completeness,auto)
termination read_array
  apply (relation "measure (unat o fst o snd)")
  apply auto
  by unat_arith
declare read_array.simps[simp del]

lemma length_read_array:
  shows "length (read_array s n offset) = unat n"
proof(induct s n offset rule: read_array.induct)
  case (1 s n)
  thus ?case
  proof(cases "n=0")
    case True
    thus ?thesis
      by (auto simp add: read_array.simps[of s 0])
  next
    case False
    thus ?thesis
      using 1
      apply (auto simp add: read_array.simps[of s n])
      by unat_arith
  qed
qed

lemma read_array_elt:
  assumes "\<forall> i < n\<^sub>0 . s \<turnstile> *[RSP s + ucast i * 48 + offset, 8] = (f i :: 64 word)"
      and "of_nat i < n"
      and "i < 256"
      and "n \<le> n\<^sub>0"
    shows "read_array s n offset ! i = f (of_nat i)"
  using assms
proof(induct s n offset rule: read_array.induct)
  case (1 s n)
  thus ?case
  proof(cases "n=0")
    case True
    thus ?thesis
      using 1(3)
      by auto
  next
    case False
    moreover
    have "n \<noteq> 0 \<Longrightarrow> i < unat (n - 1) \<Longrightarrow> of_nat i < n - 1"
      apply unat_arith
      by (auto simp add: unat_of_nat)
    moreover
    have "\<not> i < unat (n - 1) \<Longrightarrow> i = unat (n - 1)"
      using 1(3)
      apply unat_arith
      using 1(4)
      by (auto simp add: unat_of_nat)
    moreover
    have "n \<noteq> 0 \<Longrightarrow> n - 1 \<le> n\<^sub>0"
      using 1(5)
      by unat_arith
    ultimately
    show ?thesis
      using 1
      by (auto simp add: read_array.simps[of s n] nth_append length_read_array)
  qed
qed

lemma read_array_hd:
  assumes "0 < n"
    shows "hd (read_array s n offset) = s \<turnstile> *[RSP s + offset, 8]"
  using assms
proof(induct s n offset rule: read_array.induct)
  case (1 s n offset)
  thus ?case
  proof(cases "n=0")
    case True
    thus ?thesis
      using 1
      by auto
  next
    case False
    moreover
    have "n \<noteq> 0 \<Longrightarrow> n \<noteq> 1 \<Longrightarrow> 0 < n - 1"
      by unat_arith
    ultimately
    show ?thesis
      using 1
      apply (auto simp add: read_array.simps[of s n] length_read_array hd_append)
      using length_read_array[of s "n-1" offset]
      apply (cases "n=1",auto simp add: )
      apply unat_arith
      by (cases "n=1",auto simp add: )
  qed
qed


lemma read_array_tl:
  assumes "\<forall> i < n' . s  \<turnstile> *[RSP s + ucast i * 48 + offset, 8]  = (f (i-1) :: 64 word)"
      and "\<forall> i < n  . s' \<turnstile> *[RSP s' + ucast i * 48 + offset, 8] = (f i :: 64 word)"
      and "RSP s' = RSP s + 48"
      and "n' = n + 1"
      and "n' \<ge> n"
    shows "read_array s' n offset = tl (read_array s n' offset)"
proof-
  {
    fix i
    assume i: "i < unat n"
    hence 0: "of_nat i < n"
      apply unat_arith
      by (auto simp add: unat_of_nat)
    have 1: "i < 256"
      using i
      apply unat_arith
      by auto
    have 2: "i < unat n' - Suc 0"
      using i assms(4,5)
      by unat_arith
    have 3: "of_nat (Suc i) < n'"
      using i assms(4,5)
      apply unat_arith
      by (auto simp add: unat_of_nat)
    have 4: "Suc i < 256"
      using i 
      apply unat_arith
      by (auto simp add: unat_of_nat)
    have "read_array s' n offset ! i = tl (read_array s n' offset) ! i"
      apply (subst read_array_elt[OF assms(2) 0 1],simp)
      apply (subst nth_tl,simp add: length_read_array 2)
      apply (subst read_array_elt[OF assms(1) 3 4],simp)
      by simp
  }
  thus ?thesis
    apply (intro nth_equalityI)
    apply (simp add: length_read_array)
    using assms
    apply unat_arith
    by (simp add: length_read_array assms)
qed


lemma read_array_Cons:
  assumes "\<forall> i < n' . s \<turnstile> *[RSP s + ucast i * 48 + offset, 8] = (f (i+1) :: 64 word)"
      and "\<forall> i < n . s' \<turnstile> *[RSP s' + ucast i * 48 + offset, 8] = (f i :: 64 word)"
      and "RSP s' = RSP s - 48"
      and "n' = n - 1"
      and "0 < n"
  shows "read_array s' n offset = (f 0)#(read_array s n' offset)"
proof-
  {
    fix i
    assume i: "i < unat n"
    hence 0: "of_nat i < n"
      apply unat_arith
      by (auto simp add: unat_of_nat)
    have 1: "i < 256"
      using i
      apply unat_arith
      by auto
    have "(read_array s' n offset) ! i = ((f 0)#(read_array s (n-1) offset)) ! i"
      apply (subst read_array_elt[OF assms(2) 0 1], simp)
      apply (cases i)
      apply simp
      apply simp
      apply (subst read_array_elt[OF assms(1)])
      using i
      apply unat_arith
      apply (auto simp add: unat_of_nat)
      using 1
      apply unat_arith
      using i assms(4)
      apply (auto)
      by (simp add: field_simps assms(4))
  }
  thus ?thesis
    apply (intro nth_equalityI)
    apply (simp add: length_read_array)
    using assms
    apply unat_arith
    by (simp add: length_read_array assms)
qed

definition block2 :: "8 word \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  where "block2 n\<^sub>0 s s' \<equiv> read_array s' (n\<^sub>0 - DL s') 24 = (ucast (DL s))#read_array s (n\<^sub>0 - DL s) 24
                          \<and> DL s' = DL s - 1
                          \<and> RIP s' = boffset + 64"

lemma factorial_64:
assumes "((P_64 blocks n\<^sub>0 ret_address rsp\<^sub>0) && (\<lambda>s. \<not>flags s flag_zf)) s"
  shows "(block2 n\<^sub>0 s && P_64 blocks n\<^sub>0 ret_address rsp\<^sub>0) (The (((\<lambda>s. (=) (step s)) ; run_until_pred (lines {ret_address,64,104})) s))"
proof-
  have "seps blocks"
   and "RBP s = RSP s + 32"
   and "RIP s = boffset + 64"
   and "ret_address > 150"
   and "\<not>flags s flag_zf"
   and "DL s > 0"
   and "s \<turnstile> *[RSP s + 12,1] = DL s"
   and "RSP s + ucast (n\<^sub>0 - DL s) * 48 = rsp\<^sub>0 - 40"
    using assms[unfolded P_64_def]
    apply (auto simp add: pred_logic DL_is_0_def)
    by unat_arith+
  note assms' = this

  have "(\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 48, 8) (2001 - unat j + unat i))"
   and "(\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 56, 8) (3001 - unat j + unat i))"
   and "(\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 64, 8) (4001 - unat j + unat i))"
   and "(\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 72, 8) (5001 - unat j + unat i))"
   and "(\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 76, Suc 0) (6001 - unat j + unat i))"
   and "(\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 84, Suc 0) (7001 - unat j + unat i))"
    using assms[unfolded P_64_def]
    by (auto simp add: pred_logic)
  note masters = this

  have \<open>master blocks (RSP s - 8, 8)  (2001 + unat (n\<^sub>0 - DL s))\<close>
   and \<open>master blocks (RSP s - 16, 8) (3001 + unat (n\<^sub>0 - DL s))\<close>
   and \<open>master blocks (RSP s - 24, 8) (4001 + unat (n\<^sub>0 - DL s))\<close>
   and \<open>master blocks (RSP s - 36, Suc 0) (6001 + unat (n\<^sub>0 - DL s))\<close>
    using assms'(8) masters[THEN spec,THEN spec, of 0 "ucast (n\<^sub>0 - DL s)"]
    by (auto simp add: field_simps unat_ucast is_up)
  note masters = this

  have 2: "(18446744073709551608::64 word) = -8"
   and 3: "(18446744073709551568::64 word) = -48"
   and 4: "(255 :: 8 word) = -1"
    by auto

  show ?thesis
    apply (insert assms' 2 3 4)
    apply (rewrite_one_step) (* je *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* sub *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* call *)
    apply (symbolic_execution masters: masters) (* push *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* push *)
    apply (symbolic_execution masters: masters) (* sub *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)    
    apply (symbolic_execution masters: masters) (* cmp *)
    apply (finish_symbolic_execution)
    apply (simp add: block2_def ucast_id)
    apply (rule read_array_Cons[where f="\<lambda> i . ucast (DL s + i)",simplified])
    apply (rule allI,rule impI)
    subgoal premises prems for i 
    proof-
      have 0: "\<forall> i < n\<^sub>0 - DL s . s \<turnstile> *[RSP s + ucast i * 48 + 24, 8] = (ucast (DL s + i + 1) :: 64 word)"
        using assms[unfolded P_64_def]
        by (auto simp add: pred_logic)
      show ?thesis
        using 0[THEN spec,of i] prems(9)
        by (auto simp add: field_simps)
    qed
    apply (rule allI,rule impI)
    subgoal premises prems for i 
    proof-
      have 0: "\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 64, 8) (4001 - unat j + unat i)"
        using assms[unfolded P_64_def]
        by (auto simp add: pred_logic)
      have "master blocks (regs s rsp + ucast i * 48 - 24,8) (4001 - unat i + unat (n\<^sub>0 - \<langle>7,0\<rangle>regs s rdi))"
        using prems(8) 0[THEN spec,THEN spec, of "ucast i" "ucast (n\<^sub>0 - DL s)" ]
        by (auto simp add: field_simps unat_ucast is_up)
      note masters = masters and this
      note masters = this
      
      have 1: "\<forall> i < n\<^sub>0 - DL s . s \<turnstile> *[RSP s + (ucast i) * 48 + 24, 8] = (ucast (DL s + i + 1) :: 64 word)"
        using assms[unfolded P_64_def]
        by (auto simp add: pred_logic)

      have 0: "4001 - unat i > 3000"
        by (unat_arith,simp)
      have 00: "i \<noteq> 0 \<Longrightarrow> 4001 - unat i \<noteq> 4001"
        by unat_arith
      have 000: "unat (n\<^sub>0 - DL s) + 4001 - unat i \<noteq> unat (n\<^sub>0 - DL s) + 3001"
        apply unat_arith
        by (auto)
      have 0000: "i \<noteq> 0 \<Longrightarrow> unat (n\<^sub>0 - DL s) + 4001 - unat i \<noteq> unat (n\<^sub>0 - DL s) + 4001"
        by unat_arith

      have 1: "\<forall> i < n\<^sub>0 - DL s . s \<turnstile> *[RSP s + ucast i * 48 + 24, 8] = (ucast (DL s + i + 1) :: 64 word)"
        using assms[unfolded P_64_def]
        by (auto simp add: pred_logic)
      have 3: "i \<noteq> 0 \<Longrightarrow> i < 1 + n\<^sub>0 - DL s \<Longrightarrow> i - 1 < n\<^sub>0 - DL s"
        by unat_arith
      have 2: "i \<noteq> 0 \<Longrightarrow> ucast (i - 1) = (ucast i - 1 :: 64 word)"
        apply unat_arith
        by (auto simp add: unat_ucast is_up unat_sub_if')

      show ?thesis
        apply (insert masters prems 0 00 000 0000)
        apply (cases "i=0")
        apply (rewrite_one_let')+
        apply (simp add: simp_rules)
        apply (rewrite_one_let')+
        apply (simp add: simp_rules)
        using 1[THEN spec, of "i-1"] 2 3
        by (auto simp add: field_simps)
    qed
    apply (simp add: simp_rules)
    apply (simp add: simp_rules)
    subgoal premises prems
    proof-
      have "DL s \<le> n\<^sub>0"
        using assms[unfolded P_64_def]
        by (auto simp add: pred_logic)
      thus ?thesis
        using prems(6)
        by unat_arith
    qed
    apply (auto simp add: P_64_def DL_is_0_def)[1]
    apply (simp add: ucast_id 2)        
    subgoal premises prems
    proof-
      have "DL s \<le> n\<^sub>0"
        using assms[unfolded P_64_def]
        by (auto simp add: pred_logic)
      thus ?thesis
        using prems(6)
        by unat_arith
    qed
    apply (simp add: ucast_id 2)        
    subgoal premises prems
    proof-
      have "DL s \<le> n\<^sub>0"
        using assms[unfolded P_64_def]
        by (auto simp add: pred_logic)
      hence "ucast (n\<^sub>0 - (DL s - 1)) = (ucast (n\<^sub>0 - DL s) :: 64 word) + 1"
        using assms'(6)
        apply unat_arith
        by (auto simp add: unat_ucast is_up unat_word_ariths unat_sub_if' Suc_diff_le split: if_split_asm)
      thus ?thesis
        using prems(8)
        by (auto simp add: field_simps)
    qed
    apply (simp add: ucast_id)
    subgoal premises prems for i
    proof-
      have 0: "\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 64, 8) (4001 - unat j + unat i)"
        using assms[unfolded P_64_def]
        by (auto simp add: pred_logic)
      have "master blocks (regs s rsp + ucast i * 48 - 24,8) (4001 - unat i + unat (n\<^sub>0 - \<langle>7,0\<rangle>regs s rdi))"
        using prems(8) 0[THEN spec,THEN spec, of "ucast i" "ucast (n\<^sub>0 - DL s)" ]
        by (auto simp add: field_simps unat_ucast is_up)
      note masters = masters and this
      note masters = this
      
      have 3: "i \<noteq> 0 \<Longrightarrow> i < 1 + n\<^sub>0 - DL s \<Longrightarrow> i - 1 < n\<^sub>0 - DL s"
        by unat_arith
      have 2: "i \<noteq> 0 \<Longrightarrow> ucast (i - 1) = (ucast i - 1 :: 64 word)"
        apply unat_arith
        by (auto simp add: unat_ucast is_up unat_sub_if')

      have 1: "\<forall> i < n\<^sub>0 - DL s . s \<turnstile> *[RSP s + (ucast i) * 48 + 24, 8] = (ucast (DL s + i + 1) :: 64 word)"
        using assms[unfolded P_64_def]
        by (auto simp add: pred_logic)

      have 0: "4001 - unat i > 3000"
        by (unat_arith,simp)
      have 00: "i \<noteq> 0 \<Longrightarrow> 4001 - unat i \<noteq> 4001"
        by unat_arith
      have 000: "unat (n\<^sub>0 - DL s) + 4001 - unat i \<noteq> unat (n\<^sub>0 - DL s) + 3001"
        apply unat_arith
        by (auto)
      show ?thesis
        apply (cases "i=0")
        apply (insert masters assms' 0 00 000)
        apply (rewrite_one_let')+
        apply (simp add: simp_rules)
        apply simp
        apply (insert masters assms')
        apply (rewrite_one_let')+
        using 1[THEN spec,of "i-1"] prems(9) 2 3
        by (auto simp add: simp_rules)
    qed
    apply (simp add: ucast_id)
    subgoal premises prems for i
    proof-
      have 0: "\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 76, Suc 0) (6001 - unat j + unat i)"
        using assms[unfolded P_64_def]
        by (auto simp add: pred_logic)
      have "master blocks (regs s rsp + ucast i * 48 - 36,Suc 0) (6001 - unat i + unat (n\<^sub>0 - \<langle>7,0\<rangle>regs s rdi))"
        using prems(8) 0[THEN spec,THEN spec, of "ucast i" "ucast (n\<^sub>0 - DL s)" ]
        by (auto simp add: field_simps unat_ucast is_up)
      note masters = masters and this
      note masters = this
      
      have 3: "i \<noteq> 0 \<Longrightarrow> i \<le> 1 + n\<^sub>0 - DL s \<Longrightarrow> i - 1 \<le> n\<^sub>0 - DL s"
        by unat_arith
      have 2: "i \<noteq> 0 \<Longrightarrow> ucast (i - 1) = (ucast i - 1 :: 64 word)"
        apply unat_arith
        by (auto simp add: unat_ucast is_up unat_sub_if')

      have 1: "\<forall> i \<le> n\<^sub>0 - DL s . s \<turnstile> *[RSP s + (ucast i) * 48 + 12, 1] = DL s + i"
        using assms[unfolded P_64_def]
        by (auto simp add: pred_logic)

      have 0: "6001 - unat i > 5000"
        by (unat_arith,simp)
      have 00: "i \<noteq> 0 \<Longrightarrow> 6001 - unat i \<noteq> 6001"
        by unat_arith

      show ?thesis
        apply (cases "i=0")
        apply (insert masters assms' 0 00)
        apply (rewrite_one_let')+
        apply (simp add: simp_rules)
        apply simp
        apply (insert masters assms')
        apply (rewrite_one_let')+
        using 1[THEN spec,of "i-1"] prems(9) 2 3
        by (auto simp add: simp_rules)
    qed
    using assms[unfolded P_64_def] apply (auto simp add: pred_logic)[1]
    using assms[unfolded P_64_def] apply (auto simp add: pred_logic)[1]
    using assms[unfolded P_64_def] apply (auto simp add: pred_logic)[1]
    using assms[unfolded P_64_def] apply (auto simp add: pred_logic)[1]
    using assms[unfolded P_64_def] apply (auto simp add: pred_logic)[1]
    using assms[unfolded P_64_def] apply (auto simp add: pred_logic)[1]
    apply (simp add: ucast_id)
    subgoal premises prems for i
    proof-
      have 0: "\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 48, 8) (2001 - unat j + unat i)"
        using assms[unfolded P_64_def]
        by (auto simp add: pred_logic)
      have "master blocks (regs s rsp + ucast i * 48 - 8,8) (2001 - unat i + unat (n\<^sub>0 - \<langle>7,0\<rangle>regs s rdi))"
        using prems(8) 0[THEN spec,THEN spec, of "ucast i" "ucast (n\<^sub>0 - DL s)" ]
        by (auto simp add: field_simps unat_ucast is_up)
      note masters = masters and this
      note masters = this

      have 0: "2001 - unat i > 1000"
        by (unat_arith,simp)
      have 00: "i \<noteq> 0 \<Longrightarrow> 2001 - unat i \<noteq> 2001"
        by unat_arith

      have 1: "\<forall> i < n\<^sub>0 - DL s . s \<turnstile> *[RSP s + (ucast i) * 48 + 40, 8] = boffset + 87"
        using assms[unfolded P_64_def]
        by (auto simp add: pred_logic)
      have 3: "i \<noteq> 0 \<Longrightarrow> i < 1 + n\<^sub>0 - DL s \<Longrightarrow> i - 1 < n\<^sub>0 - DL s"
        by unat_arith
      have 2: "i \<noteq> 0 \<Longrightarrow> ucast (i - 1) = (ucast i - 1 :: 64 word)"
        apply unat_arith
        by (auto simp add: unat_ucast is_up unat_sub_if')

      show ?thesis
        apply (cases "i=0")
        apply (insert masters assms' 0 00)
        apply (rewrite_one_let')+
        apply (simp add: simp_rules)
        apply (insert masters assms')
        apply clarsimp
        apply (rewrite_one_let')+
        using 1[THEN spec,of "i-1"] prems(9) 2 3
        by (auto simp add: simp_rules)
    qed
    subgoal premises prems
    proof-
      have 0: "\<forall> i j . master blocks (rsp\<^sub>0 + j * 48 - i * 48 - 48, 8) (2001 - unat j + unat i)"
        using assms[unfolded P_64_def]
        by (auto simp add: pred_logic)
      have "master blocks (rsp\<^sub>0,8) 2000"
        using 0[THEN spec,THEN spec, of 1 0]
        by (auto simp add: field_simps unat_ucast is_up)
      note masters = masters and this
      note masters = this

      have 1: "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
        using assms[unfolded P_64_def]
        by (auto simp add: pred_logic)

      show ?thesis
        apply (insert masters assms'(1) 1)
        apply (rewrite_one_let')+
        by (simp add: simp_rules)
    qed
    apply (simp add: ucast_id)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (simp add: ucast_id)
    done
qed


definition block4 :: "8 word \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  where "block4 n\<^sub>0 s s' \<equiv> (s' \<turnstile> *[regs s' rsp - 28,1]) = 
                ((s \<turnstile> *[regs s rsp - 28,1]) + 1 :: 8 word)
              \<and> read_array s' (n\<^sub>0 - (s' \<turnstile> *[regs s' rsp - 28,1])) (-16) = tl (read_array s (n\<^sub>0 - (s \<turnstile> *[regs s rsp - 28,1])) (-16))
              \<and> RAX s' = RAX s * ucast ((s \<turnstile> *[regs s rsp - 28,1]) + 1 :: 8 word)
              \<and> RIP s' = boffset + 104"

lemma factorial_104_104:
assumes "((P_104 blocks n\<^sub>0 ret_address rsp\<^sub>0) && (\<lambda>s. n\<^sub>0 > (s \<turnstile> *[regs s rsp - 28,1]))) s"
shows "(block4 n\<^sub>0 s && P_104 blocks n\<^sub>0 ret_address rsp\<^sub>0) (The (((\<lambda>s. (=) (step s)) ; run_until_pred (lines {ret_address,104})) s))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 104"
   and "ret_address > 150"
   and "n\<^sub>0 > (s \<turnstile> *[regs s rsp - 28,1])"
   and "RSP s + ucast (n\<^sub>0 - (s \<turnstile> *[RSP s - 28, 1])) * 48 = rsp\<^sub>0"
   and "\<forall> i < n\<^sub>0 - (s \<turnstile> *[RSP s - 28, 1]) . s \<turnstile> *[RSP s + (ucast i) * 48, 8] = boffset + 87"
   and "\<forall> i < n\<^sub>0 - (s \<turnstile> *[RSP s - 28, 1]) . s \<turnstile> *[RSP s + (ucast i) * 48 - 16, 8] = (ucast ((s \<turnstile> *[RSP s - 28, 1]) + i + 1 :: 8 word) :: 64 word)"
   and "\<forall> i \<le> n\<^sub>0 - (s \<turnstile> *[RSP s - 28, 1]) . s \<turnstile> *[RSP s + (ucast i) * 48 - 28, 1] = ((s \<turnstile> *[RSP s - 28, 1]) + i :: 8 word)"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "RBX s = ucast ((s \<turnstile> *[regs s rsp - 28,1]) + 1 :: 8 word)"
    using assms[unfolded P_104_def]
    by (auto simp add: pred_logic field_simps)
  note assms' = this

  have "s \<turnstile> *[20 + RSP s, 1] = (s \<turnstile> *[RSP s - 28, 1]) + (1:: 8 word)"
    using assms'(8)[THEN spec,of 0] assms'(8)[THEN spec,of 1] assms'(4)
    by (auto simp add: field_simps)
  note assms' = assms' and this
  note assms' = this
  have "s \<turnstile> *[RSP s, 8] = boffset + 87"
    using assms'(4) assms'(6)[THEN spec,of 0]
    by auto
  note assms' = assms' and this
  note assms' = this

  have 2: "(18446744073709551608::64 word) = -8"
   and 3: "(18446744073709551568::64 word) = -48"
   and 4: "(255 :: 8 word) = -1"
    by auto

  show ?thesis
    apply (insert assms' 2 3 4)
    apply (rewrite_one_step) (* ret *)
    apply (symbolic_execution masters: ) (* imul *)
    apply (symbolic_execution masters: ) (* jmp *)
    apply (symbolic_execution masters: ) (* add *)
    apply (symbolic_execution masters: ) (* pop *)
    apply (symbolic_execution masters: ) (* pop *)
    apply (finish_symbolic_execution)
    apply (auto simp add: block4_def)[1]
    apply (rule read_array_tl[where f="\<lambda> i . ucast ((s \<turnstile> *[regs s rsp - 28,1]) + i + 2)",simplified])
    apply (rule allI,rule impI)
    subgoal premises prems for i 
    proof-
      show ?thesis
        using assms'(7) prems(13)
        by (auto simp add: field_simps)
    qed
    apply (rule allI,rule impI)
    subgoal premises prems for i 
    proof-
      have "i + 1 < n\<^sub>0 - (s \<turnstile> *[regs s rsp - 28,1])"
        using prems(4,13)
        by unat_arith
      moreover
      have "ucast (i + 1) = (ucast i + 1::64 word)"
        using prems(4,13)
        apply unat_arith
        by (auto simp add: unat_ucast is_up unat_word_ariths unat_sub_if')
      ultimately
      show ?thesis
        using assms'(7)[THEN spec,of "i+1"]
        by (simp add: field_simps)
    qed
    apply simp
    apply simp
    subgoal premises prems
    proof-
      have "s \<turnstile> *[regs s rsp - 28,Suc 0] \<le> ((s \<turnstile> *[regs s rsp - 28,Suc 0]) + 1 :: 8 word)"
        using prems(4)
        by unat_arith
      moreover
      have "(s \<turnstile> *[regs s rsp - 28,Suc 0]) + 1 \<le> n\<^sub>0"
        using prems(4)
        by unat_arith
      ultimately
      show ?thesis
        using prems
        by (auto)
    qed
    apply (auto simp add: P_104_def field_simps) 
    subgoal premises prems
    proof-
      show ?thesis
        using prems(4)
        by unat_arith
    qed
    subgoal premises prems
    proof-
      show ?thesis
        using prems(4)
        apply unat_arith
        by (auto simp add: unat_ucast is_up unat_word_ariths unat_sub_if')
    qed
    subgoal premises prems for i
    proof-
      have "i + 1 < n\<^sub>0 - (s \<turnstile> *[regs s rsp - 28,1])"
        using prems(4,13)
        by unat_arith
      moreover
      have "ucast (i + 1) = (ucast i + 1::64 word)"
        using prems(4,13)
        apply unat_arith
        by (auto simp add: unat_ucast is_up unat_word_ariths unat_sub_if')
      ultimately
      show ?thesis
        using assms'(7)[THEN spec,of "i+1"]
        by (auto simp add: field_simps)
    qed
    subgoal premises prems for i
    proof-
      have "i + 1 \<le> n\<^sub>0 - (s \<turnstile> *[regs s rsp - 28,1])"
        using prems(4,13)
        by unat_arith
      moreover
      have "ucast (i + 1) = (ucast i + 1::64 word)"
        using prems(4,13)
        apply unat_arith
        by (auto simp add: unat_ucast is_up unat_word_ariths unat_sub_if')
      ultimately
      show ?thesis
        using assms'(8)[THEN spec, of "i+1"] 
        by (auto simp add: field_simps)
    qed
    subgoal premises prems for i
    proof-
      have "i + 1 < n\<^sub>0 - (s \<turnstile> *[regs s rsp - 28,1])"
        using prems(4,13)
        by unat_arith
      moreover
      have "ucast (i + 1) = (ucast i + 1::64 word)"
        using prems(4,13)
        apply unat_arith
        by (auto simp add: unat_ucast is_up unat_word_ariths unat_sub_if')
      ultimately
      show ?thesis
        using assms'(6)[THEN spec,of "i+1"]
        by (auto simp add: field_simps)
    qed
    subgoal premises prems
    proof-
      have "1 < n\<^sub>0 - (s \<turnstile> *[regs s rsp - 28,Suc 0])"
        using prems(4,13)
        by unat_arith
      thus ?thesis
        using assms'(7)[THEN spec,of "1"]
        by (simp add: field_simps)
    qed
    done
qed

definition block5 :: "64 word \<Rightarrow> 64 word \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  where "block5 ret_address rsp\<^sub>0 s s' \<equiv> s' = s\<lparr>regs := (regs s)(rip := boffset + ret_address, rsp := rsp\<^sub>0 + 8)\<rparr>"  


lemma factorial_104_ret:
assumes "((P_104 blocks n\<^sub>0 ret_address rsp\<^sub>0) && ! (\<lambda>s. n\<^sub>0 > (s \<turnstile> *[regs s rsp - 28,1]))) s"
  shows "(block5 ret_address rsp\<^sub>0 s && P_ret ret_address rsp\<^sub>0) (The ((run_until_pred (line ret_address) s)))"
proof-
  have "seps blocks"
   and "RIP s = boffset + 104"
   and "ret_address > 150"
   and "n\<^sub>0 = (s \<turnstile> *[regs s rsp - 28,1])"
   and "RSP s + ucast (n\<^sub>0 - (s \<turnstile> *[RSP s - 28, 1])) * 48 = rsp\<^sub>0"
   and "\<forall> i < n\<^sub>0 - (s \<turnstile> *[RSP s - 28, 1]) . s \<turnstile> *[RSP s + (ucast i) * 48, 8] = boffset + 87"
   and "\<forall> i \<le> n\<^sub>0 - (s \<turnstile> *[RSP s - 28, 1]) . s \<turnstile> *[RSP s + (ucast i) * 48 - 28, 1] = ((s \<turnstile> *[RSP s - 28, 1]) + i :: 8 word)"
   and "s \<turnstile> *[regs s rsp,8] = boffset + ret_address"
    using assms[unfolded P_104_def]
    by (auto simp add: pred_logic field_simps)
  note assms' = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: ) (* ret *)
    apply (finish_symbolic_execution)
    apply (simp add: block5_def)
    by (auto simp add: P_ret_def) 
qed

end

record astate =
  ret\<^sub>v :: "64 word"

record factorial_state =
  x\<^sub>v :: "64 word list"
  n\<^sub>v :: "8 word"

context pow2_factorial_context
begin

definition abstract_factorial :: "8 word \<Rightarrow> factorial_state \<times> astate \<Rightarrow> factorial_state \<times> astate \<Rightarrow> bool"
  where "abstract_factorial n\<^sub>0 \<equiv>
            (\<lambda> \<sigma> \<sigma>' . n\<^sub>v (\<L> \<sigma>') = n\<^sub>0) ;
            WHILE (\<lambda> \<sigma> . n\<^sub>v (\<L> \<sigma>) > 0) DO
              (\<lambda> \<sigma> \<sigma>' . x\<^sub>v (\<L> \<sigma>') = ucast (n\<^sub>v (\<L> \<sigma>)) # x\<^sub>v (\<L> \<sigma>) \<and>
                        n\<^sub>v (\<L> \<sigma>') = n\<^sub>v (\<L> \<sigma>) - 1)
            OD ;
            (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<C> \<sigma>') = 1) ;
            WHILE (\<lambda> \<sigma> . n\<^sub>0 > n\<^sub>v (\<L> \<sigma>)) DO
              (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<C> \<sigma>') = ret\<^sub>v (\<C> \<sigma>) * ucast (hd (x\<^sub>v (\<L> \<sigma>))) \<and>
                        x\<^sub>v (\<L> \<sigma>') = tl (x\<^sub>v (\<L> \<sigma>)) \<and>
                        n\<^sub>v (\<L> \<sigma>') = n\<^sub>v (\<L> \<sigma>) + 1)
            OD ;
            (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<C> \<sigma>') = ret\<^sub>v (\<C> \<sigma>))"

definition S :: "'\<sigma>\<^sub>C \<Rightarrow> 8 word \<Rightarrow> 64 word \<Rightarrow> state \<Rightarrow> factorial_state \<times> '\<sigma>\<^sub>C astate_scheme"
  where "S \<sigma>\<^sub>C n\<^sub>0 ret_address s = (let n = if RIP s \<in> {boffset + 104, boffset + ret_address} then s \<turnstile> *[RSP s - 28, 1] else DL s in 
                 \<lparr> x\<^sub>v = read_array s (n\<^sub>0 -n) (if RIP s = boffset + 104 then -16 else 24),
                   n\<^sub>v = n \<rparr>,
                 \<lparr> ret\<^sub>v = RAX s, \<dots> = \<sigma>\<^sub>C\<rparr>)"

lemma factorial_decompose:
  shows "run_until_pred (line ret_address) =
            run_until_pred (lines {ret_address, 64, 104}) ;
            run_until_pred (lines {ret_address, 104}) ;
            run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 104"])
  apply (simp add: line_simps)
  apply (subst compose[of "lines {ret_address, 104}" "line 64"])
  apply (simp add: line_simps)
  done

lemma factorial:
  shows "S \<sigma>\<^sub>C n\<^sub>0 ret_address ::
         {P_46 blocks ret_address n\<^sub>0 rsp\<^sub>0}
            run_until_pred (line ret_address) \<preceq> abstract_factorial n\<^sub>0
         {P_ret ret_address rsp\<^sub>0}"
  apply (simp add: abstract_factorial_def)
  apply (subst factorial_decompose)
  apply (rule HL_compose[of _ _ _ _ "P_64 blocks n\<^sub>0 ret_address rsp\<^sub>0"])
  apply (rule HL_equality_intro)
  apply (rule factorial_46,simp)
  apply (auto simp add: block1_def S_def P_64_def)[1]
  apply (subst seq_assoc[symmetric])
  apply (rule HL_compose[of _ _ _ _ "P_104 blocks n\<^sub>0 ret_address rsp\<^sub>0"])
  apply (rule HL_while_generic[of _ _ "(\<lambda>s. \<not> flags s flag_zf)" _ _ "line 64"])
  apply (auto simp add: S_def lines_def line_def Let_def)[1]
    apply (auto simp add: P_64_def)[1] 
    apply (auto simp add: P_64_def)[1] 
    apply (auto simp add: P_64_def DL_is_0_def word_gt_0)[1] 
    apply (auto simp add: P_64_def)[1] 
    apply (subst (asm) DL_is_0_def)
    apply unat_arith
    apply (subst (asm) DL_is_0_def)
    apply unat_arith
  apply (simp add: line_simps)
  apply (rule HL_equality_intro_step)
  apply (rule factorial_64,simp)
  apply (auto simp add: block2_def S_def P_64_def pred_logic Let_def)[1]
  apply (rule HL_equality_intro)
  apply (rule factorial_64_104,simp add: pred_logic)
  apply (simp add: block3_def S_def)
  apply (rule HL_while_generic[of _ _ "\<lambda>s. n\<^sub>0 > (s \<turnstile> *[regs s rsp - 28,1])" _ _ "line 104"])
  apply (auto simp add: S_def line_def P_104_def Let_def)[1]
  apply (rule HL_equality_intro_step)
  apply (simp add: line_simps)
  apply (rule factorial_104_104,simp)
  apply (auto simp add: S_def block4_def P_104_def pred_logic Let_def)[1]
    apply (subst read_array_hd)
    subgoal premises prems for s
    proof-
    show ?thesis
      using prems(14)
      by unat_arith
    qed
    subgoal premises prems for s s'
    proof-
    have "s \<turnstile> *[RSP s - 16, 8] = (ucast ((s \<turnstile> *[RSP s - 28, 1]) + 1 :: 8 word) :: 64 word)"
      using prems(8)[THEN spec,of 0] prems(14)
      by auto
    thus ?thesis
      by (auto simp add: ucast_id)
    qed
  apply (rule HL_equality_intro)
  apply (rule factorial_104_ret,simp)
  by (auto simp add: S_def block5_def skip_def P_104_def pred_logic P_ret_def)




text {*
  Actually, the whole array is unnecessary:
*}
definition abstract_factorial2 :: "8 word \<Rightarrow> factorial_state \<times> astate \<Rightarrow> factorial_state \<times> astate \<Rightarrow> bool"
  where "abstract_factorial2 n\<^sub>0 \<equiv>
            (\<lambda> \<sigma> \<sigma>' . n\<^sub>v (\<L> \<sigma>') = n\<^sub>0) ;
            WHILE (\<lambda> \<sigma> . n\<^sub>v (\<L> \<sigma>) > 0) DO
              (\<lambda> \<sigma> \<sigma>' . n\<^sub>v (\<L> \<sigma>') = n\<^sub>v (\<L> \<sigma>) - 1)
            OD ;
            (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<C> \<sigma>') = 1 \<and>
                      n\<^sub>v (\<L> \<sigma>') = n\<^sub>v (\<L> \<sigma>)) ;
            WHILE (\<lambda> \<sigma> . n\<^sub>0 > n\<^sub>v (\<L> \<sigma>)) DO
              (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<C> \<sigma>') = ret\<^sub>v (\<C> \<sigma>) * ucast (n\<^sub>v (\<L> \<sigma>) + 1) \<and>
                        n\<^sub>v (\<L> \<sigma>') = n\<^sub>v (\<L> \<sigma>) + 1)
            OD ;
            (\<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<C> \<sigma>') = ret\<^sub>v (\<C> \<sigma>))"


lemma factorial2:
  shows "S \<sigma>\<^sub>C n\<^sub>0 ret_address ::
         {P_46 blocks ret_address n\<^sub>0 rsp\<^sub>0}
            run_until_pred (line ret_address) \<preceq> abstract_factorial2 n\<^sub>0
         {P_ret ret_address rsp\<^sub>0}"
  apply (simp add: abstract_factorial2_def)
  apply (subst factorial_decompose)
  apply (rule HL_compose[of _ _ _ _ "P_64 blocks n\<^sub>0 ret_address rsp\<^sub>0"])
  apply (rule HL_equality_intro)
  apply (rule factorial_46,simp)
  apply (auto simp add: block1_def S_def P_64_def)[1]
  apply (subst seq_assoc[symmetric])
  apply (rule HL_compose[of _ _ _ _ "P_104 blocks n\<^sub>0 ret_address rsp\<^sub>0"])
  apply (rule HL_while_generic[of _ _ "(\<lambda>s. \<not> flags s flag_zf)" _ _ "line 64"])
  apply (auto simp add: S_def lines_def line_def Let_def)[1]
    apply (auto simp add: P_64_def)[1] 
    apply (auto simp add: P_64_def)[1] 
    apply (auto simp add: P_64_def DL_is_0_def word_gt_0)[1] 
    apply (auto simp add: P_64_def )[1] 
    apply (subst (asm) DL_is_0_def)
    apply unat_arith
    apply (subst (asm) DL_is_0_def)
    apply unat_arith
  apply (simp add: line_simps)
  apply (rule HL_equality_intro_step)
  apply (rule factorial_64,simp)
  apply (auto simp add: block2_def S_def P_64_def pred_logic Let_def)[1]
  apply (rule HL_equality_intro)
  apply (rule factorial_64_104,simp add: pred_logic)
  apply (auto simp add: block3_def S_def P_64_def P_104_def pred_logic Let_def)[1]
  apply (rule HL_while_generic[of _ _ "\<lambda>s. n\<^sub>0 > (s \<turnstile> *[regs s rsp - 28,1])" _ _ "line 104"])
  apply (auto simp add: S_def line_def P_104_def Let_def)[1]
  apply (rule HL_equality_intro_step)
  apply (simp add: line_simps)
  apply (rule factorial_104_104,simp)
  apply (auto simp add: S_def block4_def P_104_def pred_logic Let_def)[1]
  apply (rule HL_equality_intro)
  apply (rule factorial_104_ret,simp)
  by (auto simp add: S_def block5_def skip_def P_104_def pred_logic P_ret_def)


function factorial :: "8 word \<Rightarrow> 64 word"
  where "factorial n = (if n = 0 then 1 else ucast n * factorial (n - 1))"
   by (pat_completeness,auto)
termination factorial 
  apply (relation "measure unat",auto)
  by unat_arith
declare factorial.simps[simp del]

lemma factorial_simps[simp]:
  shows "factorial 0 = 1"
    and "n < 255 \<Longrightarrow> factorial (n + 1) = ucast (n + 1) * factorial n"
  apply (auto simp add: factorial.simps[of 0] factorial.simps[of "n+1"])
  apply unat_arith
  by (auto)

lemma factorial_correct:
  shows "
  { \<lambda> \<sigma> . True}
  call (abstract_factorial2 n)
  { \<lambda> \<sigma> . ret\<^sub>v (\<L> \<sigma>) = factorial n }"
  unfolding abstract_factorial2_def
  apply (rule CallRule[where P'="\<lambda> \<sigma> . True" and Q'="\<lambda> \<sigma> . ret\<^sub>v \<sigma> = factorial n"])
  apply (rule SeqRule[where Q = "\<lambda> \<sigma> . n\<^sub>v (\<L> \<sigma>) = n"])
  apply (rule BasicRule,simp)
  apply (rule SeqRule[where Q = "\<lambda> \<sigma> . n\<^sub>v (\<L> \<sigma>) = 0"])
  apply (rule WhileRule[where I = "\<lambda> \<sigma> . True"])
  apply (auto simp add: pred_logic)[1]
  apply (auto simp add: pred_logic)[1]
  apply (rule BasicRule,simp)
  apply (rule SeqRule[where Q = "\<lambda> \<sigma> . ret\<^sub>v (\<C> \<sigma>) = 1 \<and> n\<^sub>v (\<L> \<sigma>) = 0"])
  apply (rule BasicRule,simp)
  apply (rule SeqRule[where Q = "\<lambda> \<sigma> . ret\<^sub>v (\<C> \<sigma>) = factorial n"])
  apply (rule WhileRule[where I = "\<lambda> \<sigma> . n\<^sub>v (\<L> \<sigma>) \<le> n \<and> ret\<^sub>v (\<C> \<sigma>) = factorial (n\<^sub>v (\<L> \<sigma>))"])
  apply (auto simp add: pred_logic)[1]
  apply (auto simp add: pred_logic)[1]
  apply (rule BasicRule)
  apply (auto simp add: pred_logic)[1]
  apply unat_arith
  apply (subst factorial_simps(2))
  apply unat_arith
  apply (auto)[1]
  apply (simp)
  apply (rule BasicRule)
  apply (simp add: case_prod_unfold)
  apply simp
  apply simp
  done

end
end