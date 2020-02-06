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

theory Stack
  imports "../../isabelle/Presimplified_Semantics_Manual2"
          "../../isabelle/Read_Array"
          "../../isabelle/Det_Step"
begin

text \<open>Load the stack.s file.\<close>
x86_64_parser "../examples/stack/stack.s"

lemmas stack.assembly_def [code]

locale stack_context = stack + presimplified_semantics +
  fixes rsp\<^sub>0 :: "64 word"
    and ret_address :: "64 word"
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

fun stack_flag_annotation :: flag_annotation where
  \<open>stack_flag_annotation loc = (if loc \<in> {boffset + 356, boffset + 411} then {flag_zf} else {})\<close>

definition step :: \<open>state \<Rightarrow> state\<close> where
  \<open>step s \<equiv>
    let  pc = get_rip s;
         index = the (instr_index lookup_table boffset pc) in
    let' (_,i,si) = (text_sections \<alpha>)!index;
         s = exec_instr \<alpha> semantics stack_flag_annotation i si s
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
              
method finish_symbolic_execution uses add del =
    (* Stop at the current state *)
    subst run_until_pred_stop,
    (* Show that we are at the end. Otherwise, fail *)
    (determ \<open>((auto simp add: lines_def at_loc_def pred_OR_def line_def split: if_split_asm)[1]; (unat_arith; ((auto simp add: unat_of_nat)[1])?)?)\<close> ; fail),
    (* Simplify and split the current subgoal *)
    (simp (no_asm_simp) add: pred_logic simp_rules add: add del: del),
    ((rule ifI | rule conjI | rule impI)+)?

end

(* FUNCTION PUSH *)

text "The state of the caller of the function.
  In this example, the caller has to have the Stack class variables and a variable to store a return value."
record class_Stack_state =
  elems\<^sub>v :: "32 word list"
  i\<^sub>v :: "16 word"
  ret\<^sub>v :: "32 word"

context stack_context
begin

text "Precondition"
definition P_279
  where "P_279 blocks (v\<^sub>0 :: 32 word) s \<equiv> 
      seps blocks
    \<and> (102, RDI s, 40) \<in> blocks
    \<and> master blocks (rsp\<^sub>0, 8) 1
    \<and> master blocks (rsp\<^sub>0 - 8, 8) 2
    \<and> master blocks (rsp\<^sub>0 - 16, 8) 3
    \<and> master blocks (rsp\<^sub>0 - 24, 8) 4
    \<and> master blocks (RDI s + 40, 2) 100
    \<and> master blocks (RSI s, 4) 101
    \<and> RSP s = rsp\<^sub>0
    \<and> s \<turnstile> *[RSI s,4] = v\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address
    \<and> s \<turnstile> *[RDI s + 40,2] < (10:: 16 word)
    \<and> RIP s = boffset + 279
    \<and> (ret_address < 279 \<and> ret_address > 340)"

text "Postcondition"

definition P_ret
  where "P_ret s \<equiv>
      RSP s = rsp\<^sub>0 + 8 \<and> 
      RIP s = boffset + ret_address"

text "The concrete code for the block. A local variable is incremented,
  an array is updated and the RDI register remains unchanged."
definition block1 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block1 s s' \<equiv> (s' \<turnstile> *[RDI s' + 40,2]) = (s \<turnstile> *[RDI s + 40,2]) + (1::16 word)
                    \<and> array_update s s' (RDI s) 4 10 (unat (s \<turnstile> *[RDI s + 40,2] :: 16 word)) (s \<turnstile> *[RSI s,4] :: 32 word)
                    \<and> RDI s' = RDI s"

text "Proof that assuming the precondition, running until the return address is simulated by block1, and
      that the postcondition is guaranteed."
lemma push_279_ret:
  assumes "P_279 blocks v\<^sub>0 s"
  shows "(block1 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "(102, RDI s, 4 * 10) \<in> blocks"
   and "RSP s = rsp\<^sub>0"
   and "RIP s = boffset + 279"
   and "ret_address < 279 \<or> ret_address > 340"
   and "s \<turnstile> *[RDI s + 40,2] < (10:: 16 word)"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
    using assms[unfolded P_279_def]
    by auto
  note assms' = this

  have "unat (s \<turnstile> *[RDI s + 40,2] :: 16 word) < 10"
    using assms'(6)
    by unat_arith
  hence \<open>master blocks (RDI s + 4 * ucast (s \<turnstile> *[RDI s + 40,2] :: 16 word), 4) 102\<close>
    using master_for_array_update[OF assms'(1,2),of "unat (s \<turnstile> *[RDI s + 40,2]::16 word)"]
    by auto
  note masters = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (rsp\<^sub>0 - 24, 8) 4\<close>
   and \<open>master blocks (RDI s + 40, 2) 100\<close>
   and \<open>master blocks (RSI s, 4) 101\<close>
    using assms[unfolded P_279_def] assms'(3)
    by auto
  note masters = masters and this
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* push *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters add: is_up ucast_up_ucast) (* movsxd *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* lea *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* nop *)
    apply (symbolic_execution masters: masters) (* pop *)
    apply (symbolic_execution masters: masters) (* ret *)

    apply (finish_symbolic_execution)
    apply (insert masters)
    apply (simp (no_asm_simp) add: block1_def)[1]
    apply (rewrite_one_let')+
    apply (simp add: ucast_id)
    apply (rule array_update)
    apply simp
    apply simp
    apply unat_arith
    apply simp
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (simp add: simp_rules)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (frule sep_implies_not_enclosed)
    apply (simp add: simp_rules)
    apply (simp add: simp_rules)
    apply (simp add: simp_rules)
    apply (simp add: simp_rules)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (simp (no_asm_simp) add: P_ret_def)
    done
qed

text "The simulation relation. Maps concrete states to abstract ones."

definition S :: "'\<sigma>\<^sub>C \<Rightarrow> state \<Rightarrow> unit \<times> '\<sigma>\<^sub>C class_Stack_state_scheme"
  where "S \<sigma>\<^sub>C s \<equiv> ((), 
                  \<lparr> elems\<^sub>v = read_array_32 s (RDI s) 10, 
                    i\<^sub>v = s \<turnstile> *[RDI s + 40,2],
                    ret\<^sub>v = (if RIP s = boffset + ret_address then EAX s else undefined),
                    \<dots> = \<sigma>\<^sub>C \<rparr>)"

text "The abstract code. Corrseponds to the following source code:
        i++;
        elems[i] = elem;
     "

definition abstract_push :: "32 word \<Rightarrow> unit \<times> '\<sigma>\<^sub>C class_Stack_state_scheme \<Rightarrow> unit \<times> '\<sigma>\<^sub>C class_Stack_state_scheme \<Rightarrow> bool"
  where "abstract_push v \<equiv>  \<lambda> \<sigma> \<sigma>' . i\<^sub>v (\<C> \<sigma>') = i\<^sub>v (\<C> \<sigma>) + 1
                                   \<and> elems\<^sub>v (\<C> \<sigma>') = elems\<^sub>v (\<C> \<sigma>)[unat (i\<^sub>v (\<C> \<sigma>)) := v]"

text "The proof: running from line 279 until a given return address is a refinement of the abstract code."

lemma push:
  shows "S \<sigma>\<^sub>C ::
         {P_279 blocks v\<^sub>0}
            run_until_pred (line ret_address) \<preceq> abstract_push v\<^sub>0
         {P_ret}"
  apply (subst abstract_push_def)
  apply (rule HL_equality_intro)
  apply (erule push_279_ret)
  apply (auto simp add: block1_def S_def)[1]
  apply (rule read_array_32_update_nth)
  apply (simp add: P_279_def)
  apply (simp add: P_279_def,unat_arith)
  done

(* END FUNCTION PUSH *)





(* FUNCTION TOP *)

definition P_340
  where "P_340 blocks s \<equiv> 
      seps blocks
    \<and> (102, RDI s, 40) \<in> blocks
    \<and> master blocks (rsp\<^sub>0, 8) 1
    \<and> master blocks (rsp\<^sub>0 - 8, 8) 2
    \<and> master blocks (rsp\<^sub>0 - 16, 8) 3
    \<and> master blocks (RDI s + 40, 2) 100 
    \<and> RSP s = rsp\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address
    \<and> RIP s = boffset + 340
    \<and> s \<turnstile> *[RDI s + 40,2] < (10:: 16 word)
    \<and> (ret_address < 340 \<or> ret_address > 395)"

definition P_356
  where "P_356 blocks s \<equiv> 
      seps blocks
    \<and> (102, RDI s, 40) \<in> blocks
    \<and> master blocks (rsp\<^sub>0, 8) 1
    \<and> master blocks (rsp\<^sub>0 - 8, 8) 2
    \<and> master blocks (rsp\<^sub>0 - 16, 8) 3
    \<and> master blocks (RDI s + 40, 2) 100 
    \<and> RSP s = rsp\<^sub>0 - 8
    \<and> RBP s = rsp\<^sub>0 - 8
    \<and> AX s = s \<turnstile> *[RDI s + 40,2]
    \<and> s \<turnstile> *[rsp\<^sub>0 - 16,8] = RDI s
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address
    \<and> RIP s = boffset + 356
    \<and> s \<turnstile> *[RDI s + 40,2] < (10:: 16 word)
    \<and> (ret_address < 340 \<or> ret_address > 395)"

lemma top_decompose:
  shows "run_until_pred (line ret_address) =
          run_until_pred (lines {356,ret_address}) ;
          run_until_pred (line ret_address)"
  apply (subst compose[of "line ret_address" "line 356"])
  apply (simp add: line_simps)
  done


lemma top_340_356:
  assumes "P_340 blocks s"
  shows "((\<lambda> s s'. S \<sigma>\<^sub>C s' = S \<sigma>\<^sub>C s) s && P_356 blocks) (The (run_until_pred (lines {356,ret_address}) s))"
proof-
  have "seps blocks"
   and "(102, RDI s, 40) \<in> blocks"
   and "RSP s = rsp\<^sub>0"
   and "RIP s = boffset + 340"
   and "ret_address < 340 \<or> ret_address > 395"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[RDI s + 40,2] < (10:: 16 word)"
    using assms[unfolded P_340_def]
    by auto
  note assms' = this

  have \<open>master blocks (RDI s, 40) 102\<close>
    using assms'(1,2)
    by (rule master_if_in_blocks)
  note masters = this
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (RDI s + 40, 2) 100\<close>
    using assms[unfolded P_340_def]
    by auto
  note masters = masters and this
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* push *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (finish_symbolic_execution)
    apply (rewrite_one_let' add: S_def)+
    apply unat_arith
    apply unat_arith
    apply (rewrite_one_let')+
    apply unat_arith
    apply unat_arith
    apply (rewrite_one_let')+
    apply (rule read_array_32_eqI[where 'a=320])
    apply (insert masters)
    apply (simp add: simp_rules)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (simp add: simp_rules)
    apply (simp add: simp_rules)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (rewrite_one_let' add: P_356_def)+
    apply (simp add: simp_rules)
    done
qed


definition block2 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block2 s s' \<equiv> let a = (s \<turnstile> *[rsp\<^sub>0 - 16,8] :: 64 word) in
                          EAX s' = (s \<turnstile> *[a + 4 * (ucast (s \<turnstile> *[40 + a,2] :: 16 word) - 1),4])"

lemma top_356_ret_not0:
  assumes "(P_356 blocks && (\<lambda>s. AX s \<noteq> 0)) s"
  shows "(block2 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "(102, RDI s, 40) \<in> blocks"
   and "RSP s = rsp\<^sub>0 - 8"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 356"
   and "ret_address < 340 \<or> ret_address > 395"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "AX s \<noteq> 0"
   and "AX s = s \<turnstile> *[RDI s + 40,2]"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = RDI s"
   and "s \<turnstile> *[RDI s + 40,2] < (10:: 16 word)"
    using assms[unfolded P_356_def pred_logic]
    by simp+
  note assms' = this

  have \<open>master blocks (RDI s, 40) 102\<close>
    using assms'(1,2)
    by (rule master_if_in_blocks)
  note masters = this
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (RDI s + 40, 2) 100\<close>
    using assms[unfolded P_356_def pred_logic]
    by auto
  note masters = masters and this
  note masters = this

  have 1: "1 \<le> uint (s \<turnstile> *[RDI s + 40,2] :: 16 word)"
    using assms'(8,9)
    by uint_arith
  hence 2: "ucast (s \<turnstile> *[RDI s + 40,2]::16word) - 1 < (2 ^ (32 - 1) :: 64 word)"
    apply uint_arith
    by (auto simp add: uint_up_ucast is_up)
  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters add: rewrite_take_bits_is_0_bit16) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* lea *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* movsxd *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* jmp *)
    apply (symbolic_execution masters: masters) (* pop *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block2_def Let_def)+
    using 1 2
    apply (simp add: ucast_up_ucast uint_up_ucast is_up simp_rules ucast_minus sextend_remove)
    apply (simp add: P_ret_def)+
    done
qed


definition block3 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block3 s s' \<equiv> let a = (s \<turnstile> *[rsp\<^sub>0 - 16,8] :: 64 word) in
                          EAX s' = (s \<turnstile> *[a,4])"


lemma top_356_ret_0:
  assumes "(P_356 blocks && ! (\<lambda>s. AX s \<noteq> 0)) s"
  shows "(block3 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "(102, RDI s, 40) \<in> blocks"
   and "RSP s = rsp\<^sub>0 - 8"
   and "RBP s = rsp\<^sub>0 - 8"
   and "RIP s = boffset + 356"
   and "ret_address < 340 \<or> ret_address > 395"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "AX s = 0"
   and "AX s = s \<turnstile> *[RDI s + 40,2]"
   and "s \<turnstile> *[rsp\<^sub>0 - 16,8] = RDI s"
   and "s \<turnstile> *[RDI s + 40,2] < (10:: 16 word)"
    using assms[unfolded P_356_def pred_logic]
    by auto
  note assms' = this

  have \<open>master blocks (RDI s, 40) 102\<close>
    using assms'(1,2)
    by (rule master_if_in_blocks)
  note masters = this
  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (RDI s + 40, 2) 100\<close>
    using assms[unfolded P_356_def pred_logic]
    by auto
  note masters = masters and this
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters add: rewrite_take_bits_is_0_bit16) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* pop *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block3_def Let_def)+
    apply (simp add: ucast_up_ucast uint_up_ucast is_up simp_rules ucast_minus sextend_remove)
    apply (simp add: P_ret_def)+
    done
qed


definition abstract_top :: "unit \<times> '\<sigma>\<^sub>C class_Stack_state_scheme \<Rightarrow> unit \<times> '\<sigma>\<^sub>C class_Stack_state_scheme \<Rightarrow> bool"
  where "abstract_top \<equiv> skip;
                        IF \<lambda> \<sigma> . i\<^sub>v (\<C> \<sigma>) \<noteq> 0 THEN
                          \<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<C> \<sigma>') = elems\<^sub>v (\<C> \<sigma>) ! unat (i\<^sub>v (\<C> \<sigma>) - 1)
                        ELSE
                          \<lambda> \<sigma> \<sigma>' . ret\<^sub>v (\<C> \<sigma>') = elems\<^sub>v (\<C> \<sigma>) ! 0
                        FI"

lemma top:
  shows "S \<sigma>\<^sub>C ::
         {P_340 blocks}
            run_until_pred (line ret_address) \<preceq> abstract_top
         {P_ret}"
  apply (subst abstract_top_def)
  apply (subst top_decompose)
  apply (rule HL_compose[where Q="P_356 blocks"])
  apply (rule HL_equality_intro)
  apply (erule top_340_356)
  apply (auto simp add: S_def skip_def)[1]
  apply (rule HL_ITE[where B="\<lambda> s . AX s \<noteq> (0::16 word)"])
  apply (auto simp add: P_356_def S_def)[1]
   apply (rule HL_equality_intro)
  apply (erule top_356_ret_not0)
  apply (auto simp add: S_def pred_logic P_356_def P_ret_def block2_def Let_def)[1]
    apply (subst nth_read_array_32)
    subgoal premises prems for s s'
      using prems(16,17)
      by unat_arith
    apply (auto simp add: field_simps ucast_minus)[1]
    apply uint_arith
    apply (subst nth_read_array_32)
    subgoal premises prems for s s'
      using prems(16,17)
      by unat_arith
    apply (auto simp add: field_simps ucast_minus)[1]
    apply uint_arith
  apply (rule HL_equality_intro)
  apply (erule top_356_ret_0)
  apply (auto simp add: S_def pred_logic P_356_def P_ret_def block3_def Let_def)[1]
    apply (subst nth_read_array_32)
    apply simp
    apply (auto simp add: field_simps ucast_minus)[1]
    apply (subst nth_read_array_32)
    apply simp
    apply (auto simp add: field_simps ucast_minus)[1]
  done 

(* END TOP *)







(* FUNCTION POP *)

definition P_395
  where "P_395 blocks s \<equiv> 
      seps blocks
    \<and> (102, RDI s, 40) \<in> blocks
    \<and> master blocks (rsp\<^sub>0, 8) 1
    \<and> master blocks (rsp\<^sub>0 - 8, 8) 2
    \<and> master blocks (rsp\<^sub>0 - 16, 8) 3
    \<and> master blocks (RDI s + 40, 2) 100 
    \<and> RSP s = rsp\<^sub>0
    \<and> s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address
    \<and> RIP s = boffset + 395
    \<and> s \<turnstile> *[RDI s + 40,2] < (10:: 16 word)
    \<and> (ret_address < 395 \<or> ret_address > 438)"

definition block4 :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "block4 s s' \<equiv> let i = (s \<turnstile> *[RDI s + 40,2] :: 16 word);
                           i' = s' \<turnstile> *[RDI s' + 40,2] in
                          i' = (if i \<noteq> 0 then i - 1 else i)"

lemma pop_395_ret:
  assumes "P_395 blocks s"
  shows "(block4 s && P_ret) (The (run_until_pred (line ret_address) s))"
proof-
  have "seps blocks"
   and "(102, RDI s, 40) \<in> blocks"
   and "RSP s = rsp\<^sub>0"
   and "RIP s = boffset + 395"
   and "ret_address < 395 \<or> ret_address > 438"
   and "s \<turnstile> *[rsp\<^sub>0,8] = boffset + ret_address"
   and "s \<turnstile> *[RDI s + 40,2] < (10:: 16 word)"
    using assms[unfolded P_395_def]
    by auto
  note assms' = this

  have \<open>master blocks (rsp\<^sub>0, 8) 1\<close>
   and \<open>master blocks (rsp\<^sub>0 - 8, 8) 2\<close>
   and \<open>master blocks (rsp\<^sub>0 - 16, 8) 3\<close>
   and \<open>master blocks (RDI s + 40, 2) 100\<close>
    using assms[unfolded P_395_def]
    by auto
  note masters = this

  show ?thesis
    apply (insert assms')
    apply (symbolic_execution masters: masters) (* push *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* test *)
    apply (symbolic_execution masters: masters) (* je *)
    apply (symbolic_execution masters: masters) (* nop *)
    apply (symbolic_execution masters: masters) (* pop *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block4_def Let_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (simp (no_asm_simp) add: P_ret_def)

    apply (rewrite_one_let')+
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* movzx *)
    apply (symbolic_execution masters: masters) (* lea *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* mov *)
    apply (symbolic_execution masters: masters) (* nop *)
    apply (symbolic_execution masters: masters) (* pop *)
    apply (symbolic_execution masters: masters) (* ret *)
    apply (finish_symbolic_execution)
    apply (simp (no_asm_simp) add: block4_def Let_def)
    apply (insert masters)
    apply (rewrite_one_let')+
    apply (simp add: simp_rules)
    apply (simp (no_asm_simp) add: P_ret_def)
    done
qed

definition abstract_pop :: "unit \<times> '\<sigma>\<^sub>C class_Stack_state_scheme \<Rightarrow> unit \<times> '\<sigma>\<^sub>C class_Stack_state_scheme \<Rightarrow> bool"
  where "abstract_pop \<equiv> \<lambda> \<sigma> \<sigma>' . i\<^sub>v (\<C> \<sigma>') = (if i\<^sub>v (\<C> \<sigma>) \<noteq> 0 then i\<^sub>v (\<C> \<sigma>) - 1 else i\<^sub>v (\<C> \<sigma>))"

lemma pop:
  shows "S \<sigma>\<^sub>C ::
         {P_395 blocks}
            run_until_pred (line ret_address) \<preceq> abstract_pop
         {P_ret}"
  apply (subst abstract_pop_def)
  apply (rule HL_equality_intro)
  apply (erule pop_395_ret)
  apply (auto simp add: S_def block4_def)[1]
  done 

(* END POP *)


end
