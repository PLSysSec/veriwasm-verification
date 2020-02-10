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


(* TODO: this file can be removed from this branch, has been incoroporated into branch "presimplify" *)

theory Simplified_Semantics
  imports "reassembly_all.Leviathan_Setup"
begin



definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "\<otimes>" 36)
  where "a \<otimes> b \<equiv> (a \<and> \<not>b) \<or> (\<not>a \<and> b)"

definition parity :: "'a::len0 word \<Rightarrow> bool"
  where "parity a \<equiv> fold (\<otimes>) (drop (LENGTH('a) - 8) (to_bl a)) True"

(*5 flags generation CF,SF,OF,ZF,PF *)
instruction_semantics_parser "../InstructionSemantics/strata_rules_5flags"   
lemmas strata_rules_5flags.semantics_def [code]


locale execution_plus_strata_rules_5flags = execution_context + strata_rules_5flags
begin

fun get_OP1 :: "bitvector_formula list \<Rightarrow> BV_var"
  where
    "get_OP1 [] = undefined" 
  | "get_OP1 ((BV_Assignment v bvf)#_) = v"
  | "get_OP1 (_#bfs) = get_OP1 bfs"

fun writes_pflag :: "bitvector_formula list \<Rightarrow> bool"
  where
    "writes_pflag [] = False" 
  | "writes_pflag ((BV_Assignment v bvf)#bfs) = writes_pflag bfs"
  | "writes_pflag ((BV_Flag_Assignment flag_pf bvf)#bfs) = True"
  | "writes_pflag ((BV_Flag_Assignment _ bvf)#bfs) = writes_pflag bfs"
  | "writes_pflag _ = undefined"

fun exec_learned_instr' :: "assembly \<Rightarrow> bitvector_formula list \<Rightarrow> instr \<Rightarrow> state \<Rightarrow> state"
  where 
  "exec_learned_instr' \<alpha> [] i \<sigma> = \<sigma>"
| "exec_learned_instr' \<alpha> ((BV_Assignment v bvf)#bfs) i \<sigma> =
    (let' bv = ((exec_chum_bvf \<alpha> bvf i \<sigma>));
          od = operand_src_to_operand_dest (resolve_BV_Var i v);
          \<sigma>' = exec_learned_instr' \<alpha> bfs i \<sigma> in
      bv_put \<alpha> od bv \<sigma>')"
| "exec_learned_instr' \<alpha> ((BV_Flag_Assignment flag_pf bvf)#bfs) i \<sigma> =
    (let' \<sigma>' = exec_learned_instr' \<alpha> bfs i \<sigma> in
        \<sigma>')"
| "exec_learned_instr' \<alpha> ((BV_Flag_Assignment flg bvf)#bfs) i \<sigma> =
    (let' \<sigma>' = exec_learned_instr' \<alpha> bfs i \<sigma>;
           e  = exec_chum_bvf \<alpha> bvf i \<sigma>;
           f  = bv_to_bool e;
           \<sigma>'' = write_flg flg f \<sigma>' in
        \<sigma>'')"
| "exec_learned_instr' _ _ i \<sigma> = undefined"


definition write_pflag :: "assembly \<Rightarrow> instr \<Rightarrow> BV_var \<Rightarrow> state \<Rightarrow> state"
  where "write_pflag \<alpha> i op1 \<sigma> \<equiv>
  let' op1 = resolve_BV_Var i op1 ;
       (a,s) = exec_chum_bv_get \<alpha> \<sigma> i op1 in
    write_flg flag_pf (parity a) \<sigma>"

lemma parity_ucast[simp]:
  fixes a :: "'b::len0 word"
  assumes "LENGTH('a) > LENGTH('b)"
      and "LENGTH('b) \<ge> 8"
  shows "parity (ucast a :: 'a::len0 word) = parity a"
  using assms
  unfolding parity_def
  by (auto simp add: to_bl_ucast)    

definition get_semantics :: "assembly \<Rightarrow> instr \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state"
  where
    "get_semantics \<alpha> insr s \<equiv>
      let' (fam,n,o_sig) = Get_Instr_Sig insr;
           family_list = instr_semantics semantics fam;
           manual = (family_list = None);
           variant_list = (if manual then None else the family_list n);
           manual = (variant_list = None);
           bv_formula = (if manual then None else the variant_list o_sig);
           manual = (bv_formula = None);
           exec = (if manual then manual_exec_instr \<alpha> insr s else exec_learned_instr' \<alpha> (the bv_formula) insr);
           exec' = (if writes_pflag (the bv_formula) then (write_pflag \<alpha> insr (get_OP1 (the bv_formula)) o exec) else exec) in
      exec'"

lemma sub_overflow_flag:
  fixes a b :: "'a::len0 word"
  assumes "LENGTH('a) \<ge> 32"
  shows "((\<not> b !! 31) = a !! 31 \<and> b !! 31 = (sint (\<langle>31,0\<rangle>a - \<langle>31,0\<rangle>b::32 word) < 0)) \<longleftrightarrow>
            ((2147483648::32 word) > \<langle>31,0\<rangle>b \<and> sint (\<langle>31,0\<rangle>a - \<langle>31,0\<rangle>b::32 word) \<ge> 0 \<and> (2147483648::32 word) \<le> \<langle>31,0\<rangle>a)
             \<or>
             ((2147483648::32 word) \<le> \<langle>31,0\<rangle>b \<and> sint (\<langle>31,0\<rangle>a - \<langle>31,0\<rangle>b::32 word) < 0 \<and> (2147483648::32 word) > \<langle>31,0\<rangle>a)"
proof-
  have 1: "a !! 31 = msb (\<langle>31,0\<rangle> a :: 32 word)"
   and 2: "b !! 31 = msb (\<langle>31,0\<rangle> b :: 32 word)"
    using assms
    by (auto simp add: msb_nth test_bit_of_take_bits)
  show ?thesis
    using assms
    apply (subst 1)
    apply (subst 2)+
    apply (subst msb_is_gt_2p)+
    apply simp
    by (auto)
qed


abbreviation "read_mem \<alpha> \<sigma> s a \<equiv> fst (read_memory \<alpha> \<sigma> s a)"
abbreviation "write_mem \<alpha> \<sigma> a v s \<equiv> bv_put \<alpha> (Memory s a) (ucast v,0) \<sigma>"


lemma get_semantics_sub_r32_m32:
  shows "get_semantics \<alpha> (Binary (IS_8088 Sub) (Reg (General ThirtyTwo r32)) (Storage (Memory 32 a))) s = 
        (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r32 :: 32 word;
                   op2 = \<langle>31,0\<rangle>(read_mem \<alpha> \<sigma> 32 a) :: 32 word in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r32 := ucast (op1 - op2)),
          flags := (flags \<sigma>)
          (flag_pf := parity (op1 - op2),
           flag_cf := op2 > op1,
           flag_zf := op1 = op2,
           flag_sf := sint (op1 - op2) < 0,
           flag_of := (op2 < (2^31::32 word) \<and> 0 \<le> sint (op1 - op2) \<and> 2^31 \<le> op1)
                      \<or>
                      (op2 \<ge> (2^31::32 word) \<and> sint (op1  - op2) < 0 \<and> op1 < 2^31))\<rparr>)"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')+
  apply (rewrite_one_let' add: write_pflag_def)+
  apply (simp add: write_pflag_def simp_rules test_bit_of_take_bits  )
  apply (subst sub_overflow_flag)
  by auto




fun remove_flags :: "flag list \<Rightarrow> (state \<Rightarrow> state) \<Rightarrow> state \<Rightarrow> state"
  where "remove_flags [] t = t"
  | "remove_flags (flag_pf#flgs) t = remove_flags flgs (\<lambda> \<sigma> . let \<sigma>' = t \<sigma> in (\<sigma>'\<lparr>flags := (flags \<sigma>')(flag_pf := undefined)\<rparr>))"
  | "remove_flags (flag_cf#flgs) t = remove_flags flgs (\<lambda> \<sigma> . let \<sigma>' = t \<sigma> in (\<sigma>'\<lparr>flags := (flags \<sigma>')(flag_cf := undefined)\<rparr>))"
  | "remove_flags (flag_zf#flgs) t = remove_flags flgs (\<lambda> \<sigma> . let \<sigma>' = t \<sigma> in (\<sigma>'\<lparr>flags := (flags \<sigma>')(flag_zf := undefined)\<rparr>))"
  | "remove_flags (flag_of#flgs) t = remove_flags flgs (\<lambda> \<sigma> . let \<sigma>' = t \<sigma> in (\<sigma>'\<lparr>flags := (flags \<sigma>')(flag_of := undefined)\<rparr>))"
  | "remove_flags (flag_sf#flgs) t = remove_flags flgs (\<lambda> \<sigma> . let \<sigma>' = t \<sigma> in (\<sigma>'\<lparr>flags := (flags \<sigma>')(flag_sf := undefined)\<rparr>))"

primrec filter_flag_annotation :: "flag_annotation \<Rightarrow> 64 word \<Rightarrow> flag list \<Rightarrow> flag list"
  where "filter_flag_annotation \<phi> loc [] = []"
  | "filter_flag_annotation \<phi> loc (flg#flgs) = (if flg \<notin> \<phi> loc then [flg] else [])@(filter_flag_annotation \<phi> loc flgs)"

definition exec_instr' :: "assembly \<Rightarrow> flag_annotation \<Rightarrow> instr \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state"
  where                 
    "exec_instr' \<alpha> \<phi> i s \<sigma> \<equiv>
      let t = get_semantics \<alpha> i s;
          flgs = filter_flag_annotation \<phi> (get_rip \<sigma>) [flag_pf,flag_cf,flag_zf,flag_sf,flag_of];
          t = remove_flags flgs t in
        t \<sigma>"

lemma temp:
  shows "exec_instr' \<alpha> (\<lambda> \<sigma> . {flag_zf, flag_pf}) (Binary (IS_8088 Sub) (Reg (General ThirtyTwo r32)) (Storage (Memory 32 a))) s
          \<sigma> =
          x"
  apply (simp add: exec_instr'_def get_semantics_sub_r32_m32 Let_def)
  oops

end
