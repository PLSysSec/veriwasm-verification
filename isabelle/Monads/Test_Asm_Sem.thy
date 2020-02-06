theory Test_Asm_Sem
imports
  Lense_Knowledge_Base
  "HOL-Word.Word"
  "More_Eisbach_Tools"
  Abstract_System
  "HOL-Library.Rewrite"
begin

  section \<open>Syntax\<close>

  type_synonym val64 = "64 word"
  (*type_synonym byte = "8 word"*)

  datatype rname = RAX_REG | RBX_REG | RCX_REG | RDX_REG | RIP_REG
  datatype fname = Z_FLAG

  datatype instr =
    LOAD rname rname  (* LOAD dst:reg src:reg    dst = [src] *)
  | STORE rname rname (* STORE dst:reg src:reg   [dst] = src *)
  | LOADI rname val64
  | MOV rname rname
  | ADD rname rname rname
  | CMP rname rname
  | JMP val64
  | JE val64
  | HLT        (* Defined termination of program *)

  section \<open>Semantics\<close>


  datatype state = STATE
    (regs: "rname \<Rightarrow> val64")
    (mem: "val64 \<Rightarrow> val64")
    (flags: "fname \<Rightarrow> bool")
    (instrs: "instr list")
    (halted: bool)

  define_lenses state

  lemma pre_state_lenses[simp]:
    "pre_get regs\<^sub>L s"
    "pre_get mem\<^sub>L s"
    "pre_get flags\<^sub>L s"
    "pre_get instrs\<^sub>L s"
    "pre_get halted\<^sub>L s"
    unfolding regs\<^sub>L_def mem\<^sub>L_def flags\<^sub>L_def instrs\<^sub>L_def halted\<^sub>L_def
    by (auto split: state.splits)

  lemma state\<^sub>L_indeps[simp]:
    "regs\<^sub>L \<bowtie> mem\<^sub>L"
    "regs\<^sub>L \<bowtie> flags\<^sub>L"
    "regs\<^sub>L \<bowtie> instrs\<^sub>L"
    "regs\<^sub>L \<bowtie> halted\<^sub>L"

    "mem\<^sub>L \<bowtie> flags\<^sub>L"
    "mem\<^sub>L \<bowtie> instrs\<^sub>L"
    "mem\<^sub>L \<bowtie> halted\<^sub>L"

    "flags\<^sub>L \<bowtie> instrs\<^sub>L"
    "flags\<^sub>L \<bowtie> halted\<^sub>L"

    "instrs\<^sub>L \<bowtie> halted\<^sub>L"
    by (unfold_locales; unfold regs\<^sub>L_def mem\<^sub>L_def flags\<^sub>L_def instrs\<^sub>L_def halted\<^sub>L_def; auto split: state.split)+

  lemmas [simp] = state\<^sub>L_indeps[THEN lens_indep_sym]



  definition "reg\<^sub>L r \<equiv> regs\<^sub>L (r)\<^sub>L"    (* TODO: Attribute [lens] to auto-prove and register "lens x" lemma! *)
  definition "flag\<^sub>L r \<equiv> flags\<^sub>L (r)\<^sub>L"

  lemma lens_reg\<^sub>L[simp]: "hlens (reg\<^sub>L r)" by (simp add: reg\<^sub>L_def)
  lemma pre_reg\<^sub>L[simp]: "pre_get (reg\<^sub>L r) s" by (simp add: reg\<^sub>L_def)
  lemma lens_flag\<^sub>L[simp]: "hlens (flag\<^sub>L r)" by (simp add: flag\<^sub>L_def)
  lemma pre_flag\<^sub>L[simp]: "pre_get (flag\<^sub>L r) s" by (simp add: flag\<^sub>L_def)

  fun exec_instr :: "instr \<Rightarrow> (unit, state) se" where
    "exec_instr (LOAD dst src) = doE {
      addr \<leftarrow> use (reg\<^sub>L src);
      val \<leftarrow> use (mem\<^sub>L (addr)\<^sub>L);
      reg\<^sub>L dst ::= val
    }"
  | "exec_instr (STORE dst src) = doE {
      addr \<leftarrow> use (reg\<^sub>L dst);
      val \<leftarrow> use (reg\<^sub>L src);
      mem\<^sub>L (addr)\<^sub>L ::= val
    }"
  | "exec_instr (LOADI dst val) = doE {
      reg\<^sub>L dst ::= val
    }"
  | "exec_instr (MOV dst src) = doE {
      reg\<^sub>L dst ::^= use (reg\<^sub>L src)
    }"
  | "exec_instr (ADD dst src1 src2) = doE {
      v1 \<leftarrow> use (reg\<^sub>L src1);
      v2 \<leftarrow> use (reg\<^sub>L src2);
      let v = v1+v2;
      reg\<^sub>L dst ::= v;
      flag\<^sub>L Z_FLAG ::= (v=0)
    }"
  | "exec_instr (CMP src1 src2) = doE {
      v1 \<leftarrow> use (reg\<^sub>L src1);
      v2 \<leftarrow> use (reg\<^sub>L src2);
      flag\<^sub>L Z_FLAG ::= (v1 = v2)
    }"
  | "exec_instr (JMP tgt) = doE {
      reg\<^sub>L RIP_REG ::= tgt
    }"
  | "exec_instr (JE tgt) = doE {
      zf \<leftarrow> use (flag\<^sub>L Z_FLAG);
      if zf then
        reg\<^sub>L RIP_REG ::= tgt
      else sreturn ()
    }"
  | "exec_instr HLT = doE { halted\<^sub>L ::= True }"


  definition "fetch_instr \<equiv> doE {
    ip \<leftarrow> use (reg\<^sub>L RIP_REG);
    use (instrs\<^sub>L[unat ip]\<^sub>L)
  }"

  definition step :: "(unit, state) se" where
    "step \<equiv> doE {
      instr \<leftarrow> fetch_instr;
      reg\<^sub>L RIP_REG %= op+1;
      exec_instr instr
    }"


  global_interpretation det_system step halted
    defines yields = yields' .

  declare yields_unfold[code]

  definition "execute \<equiv> doE {
    s \<leftarrow> sget;
    s \<leftarrow> lift (yields s);
    case s of None \<Rightarrow> sfail | Some s \<Rightarrow> sput s
  }"


  definition zero_state :: state where
    "zero_state \<equiv> (STATE
      (\<lambda>_. 0)
      (\<lambda>_. 0)
      (\<lambda>_. False)
      ([])
      False
    )"


  section \<open>Execution Example\<close>


  definition "pow_prog \<equiv> [
(*0*)   LOADI RCX_REG 0,
(*1*)   LOADI RAX_REG 1,
(*2*)   LOADI RBX_REG 1,
(*3*)   CMP RCX_REG RDX_REG,
(*4*)   JE 8,
(*5*)     ADD RAX_REG RAX_REG RAX_REG,
(*6*)     ADD RCX_REG RCX_REG RBX_REG,
(*7*)   JMP 3,
(*8*)   HLT
(*9*)
  ]"

  value "(doE {
    reg\<^sub>L RDX_REG ::= 5;
    instrs\<^sub>L ::= pow_prog;
    execute;
    use (reg\<^sub>L RAX_REG)
  })
  zero_state"



section \<open>Verification\<close>


definition wf_state :: "state \<Rightarrow> bool"
  where "wf_state _ \<equiv> True" (* Can be used to add additional constraints to state *)

lemma wf_state_weak_invar: "is_weak_invar wf_state"
  apply (rule is_weak_invarI)
  by (simp add: wf_state_def)

hide_fact (open) wf_state_def (* Once wf_state is established as invariant,
  we should not need it any more! -- At least for now, when it is True.
  Thus, wf_state is just a dummy to show that additional invariant kbxfer works!
*)


lemma [DEL_KBXFER_simps]:
  assumes "KBXFER R s s'"
  shows
    "wf_state s = DEL_TAG (wf_state s)"
    by (auto simp: DEL_TAG_def)


interpretation std_invar_system step halted wf_state
  apply standard
  by (rule wf_state_weak_invar)




definition "location \<equiv> get' (reg\<^sub>L RIP_REG)"

interpretation cfg_system step halted wf_state location by standard

type_synonym floyd_invar = "val64 \<rightharpoonup> (state \<Rightarrow> bool)"

thm floyd_invarI floyd_vcsI



lemma reg\<^sub>L_indep[simp]: "r\<noteq>r' \<Longrightarrow> reg\<^sub>L r \<bowtie> reg\<^sub>L r'"
  unfolding reg\<^sub>L_def
  by (simp add: lens_indep_left_comp)

lemma flag\<^sub>L_indep[simp]: "r\<noteq>r' \<Longrightarrow> flag\<^sub>L r \<bowtie> flag\<^sub>L r'"
  unfolding flag\<^sub>L_def
  by (simp add: lens_indep_left_comp)

lemma flag_regL_indep[simp, THEN lens_indep_sym, simp]:
  "flag\<^sub>L f \<bowtie> reg\<^sub>L r"
  unfolding reg\<^sub>L_def flag\<^sub>L_def
  by (simp add: lens_indep_extend2)

lemma flag\<^sub>L_more_indep[simp, THEN lens_indep_sym, simp]:
  "flag\<^sub>L f \<bowtie> mem\<^sub>L"
  "flag\<^sub>L f \<bowtie> instrs\<^sub>L"
  "flag\<^sub>L f \<bowtie> halted\<^sub>L"
  unfolding flag\<^sub>L_def
  by (simp_all add: lens_indep_left_ext)

lemma reg\<^sub>L_more_indep[simp, THEN lens_indep_sym, simp]:
  "reg\<^sub>L f \<bowtie> mem\<^sub>L"
  "reg\<^sub>L f \<bowtie> instrs\<^sub>L"
  "reg\<^sub>L f \<bowtie> halted\<^sub>L"
  unfolding reg\<^sub>L_def
  by (simp_all add: lens_indep_left_ext)


abbreviation "REG r \<equiv> VAL (reg\<^sub>L r)"
abbreviation "RAX \<equiv> REG RAX_REG"
abbreviation "RBX \<equiv> REG RBX_REG"
abbreviation "RCX \<equiv> REG RCX_REG"
abbreviation "RDX \<equiv> REG RDX_REG"
abbreviation "RIP \<equiv> REG RIP_REG"
abbreviation "FLAG f \<equiv> VAL (flag\<^sub>L f)"
abbreviation "ZFLAG \<equiv> FLAG Z_FLAG"
abbreviation "PROG \<equiv> VAL instrs\<^sub>L"


text \<open>Use to convert location into value for RIP\<close>
lemma location_eq_conv: "location s = i \<longleftrightarrow> RIP i s"
  unfolding VAL_def by (auto simp: location_def)

lemma halted_eq_conv:
  "halted s \<longleftrightarrow> VAL halted\<^sub>L True s"
  "\<not>VAL halted\<^sub>L True s \<longleftrightarrow> VAL halted\<^sub>L False s"
  "VAL halted\<^sub>L True s \<Longrightarrow> \<not>VAL halted\<^sub>L False s"
  unfolding VAL_def
  by auto (auto simp: halted\<^sub>L_def split: state.splits)

lemmas prep_precond_conv = location_eq_conv halted_eq_conv

lemma location_conv[simp]: "RIP i s \<Longrightarrow> location s = i"
  by (auto simp: location_def)




lemma wps_fetch_instr_eq[wps_iffs]:
  assumes "RIP i s" "PROG \<pi> s"
  assumes "unat i < length \<pi>"
  shows "wps fetch_instr Q s \<longleftrightarrow> Q (\<pi> ! unat i) s"
  unfolding fetch_instr_def
  using assms
  by (simp add: wps_eqs wps_use_eq)


lemma wps_stepI[wps_intros]:
  assumes "RIP i s" "PROG \<pi> s"
  assumes "unat i < length \<pi>"
  assumes "\<And>s'. \<lbrakk>KBXFER (ltrans (reg\<^sub>L RIP_REG)) s s'; RIP (1 + i) s'\<rbrakk> \<Longrightarrow> wps (exec_instr (\<pi> ! unat i)) Q s'"
  shows "wps step Q s"
  unfolding step_def
  apply (rule wps_rls | fact)+
  done


lemma wps_CMPI[wps_intros]:
  assumes "REG r1 x1 s" "REG r2 x2 s"
  assumes "\<And>s'. \<lbrakk>KBXFER (ltrans (flag\<^sub>L Z_FLAG)) s s'; ZFLAG (x1 = x2) s'\<rbrakk> \<Longrightarrow> Q () s'"
  shows "wps (exec_instr (CMP r1 r2)) Q s"
  apply (simp)
  apply (intro wps_rls)
  apply (fact|simp)+
  done


lemma wps_JEI[wps_intros]:
  assumes "ZFLAG z s"
  assumes "\<And>s'. \<lbrakk>z; KBXFER (ltrans (reg\<^sub>L RIP_REG)) s s'; RIP tgt s'\<rbrakk> \<Longrightarrow> Q () s'"
  assumes "\<not> z \<Longrightarrow> Q () s"
  shows "wps (exec_instr (JE tgt)) Q s"
  apply (simp)
  apply (intro wps_rls)
  apply (fact|simp)+
  done

lemma wps_JMPI[wps_intros]:
  assumes "\<And>s'. \<lbrakk>KBXFER (ltrans (reg\<^sub>L RIP_REG)) s s'; RIP tgt s'\<rbrakk> \<Longrightarrow> Q () s'"
  shows "wps (exec_instr (JMP tgt)) Q s"
  apply (simp)
  apply (intro wps_rls)
  apply (fact|simp)+
  done


lemma wps_HLTI[wps_intros]:
  assumes "\<And>s'. \<lbrakk>KBXFER (ltrans halted\<^sub>L) s s'; VAL halted\<^sub>L True s'\<rbrakk> \<Longrightarrow> Q () s'"
  shows "wps (exec_instr HLT) Q s"
  apply (simp)
  apply (intro wps_rls)
  apply (fact|simp)+
  done

lemma wps_ADDI[wps_intros]:
  assumes "REG r2 x2 s" "REG r3 x3 s"
  assumes "\<And>s'a. \<lbrakk>REG r1 (x2 + x3) s'a; ZFLAG (x2 + x3 = 0) s'a;
            KBXFER (ltrans (reg\<^sub>L r1) OO ltrans (flag\<^sub>L Z_FLAG)) s s'a\<rbrakk>
           \<Longrightarrow> Q () s'a"
  shows "wps (exec_instr (ADD r1 r2 r3)) Q s"
  apply (simp add: Let_def)
  apply (rule wps_rls | fact | kbxfer')+
  apply kbxfer_trans
  by fact

lemma wps_LOADI[wps_intros]:
  assumes "\<And>s'. \<lbrakk>KBXFER (ltrans (reg\<^sub>L r)) s s'; REG r i s'\<rbrakk> \<Longrightarrow> Q () s'"
  shows "wps (exec_instr (LOADI r i)) Q s"
  apply (simp)
  apply (intro wps_rls)
  apply (fact|simp)+
  done



declare exec_instr.simps[simp del]


section \<open>Verification Example\<close>


lemma nat_to_numeral1:
  "Suc 0 = Numeral1"
  "Suc (numeral n) = numeral (Num.inc n)"
  by (auto simp: add_One)

lemmas nat_to_numeral = nat_to_numeral1 Num.inc.simps


schematic_goal [simplified nat_to_numeral, simp]: "length pow_prog = ?l"
  unfolding pow_prog_def by simp

schematic_goal [simplified,simp]:
  "pow_prog ! 0 = ?c0"
  "pow_prog ! 1 = ?c1"
  "pow_prog ! 2 = ?c2"
  "pow_prog ! 3 = ?c3"
  "pow_prog ! 4 = ?c4"
  "pow_prog ! 5 = ?c5"
  "pow_prog ! 6 = ?c6"
  "pow_prog ! 7 = ?c7"
  "pow_prog ! 8 = ?c8"
  unfolding pow_prog_def by auto


prop "RDX p s \<and> VAL (mem\<^sub>L((p + 0))\<^sub>L) x0 s \<and> VAL (mem\<^sub>L((p + 1))\<^sub>L) x1 s"

definition pp_\<Theta> :: "_ \<Rightarrow> floyd_invar" where "pp_\<Theta> rdx\<^sub>0 \<equiv> [
  0 \<mapsto> (\<lambda>s. VAL halted\<^sub>L False s \<and> PROG pow_prog s \<and> RDX rdx\<^sub>0 s),
  3 \<mapsto> (\<lambda>s. \<exists>rax rbx rcx hlt. RAX rax s \<and> RBX rbx s \<and> RCX rcx s \<and> RDX rdx\<^sub>0 s
      \<and> VAL halted\<^sub>L hlt s \<and> \<not>hlt \<and> PROG pow_prog s
      \<and> rbx = 1 \<and> rax = 2 ^ unat rcx \<and> rcx \<le> rdx\<^sub>0),
  9 \<mapsto> (\<lambda>s. \<exists>rax hlt. RAX rax s \<and> RDX rdx\<^sub>0 s
      \<and> VAL halted\<^sub>L hlt s \<and> hlt \<and> PROG pow_prog s
      \<and> rax = 2 ^ unat rdx\<^sub>0
      )
]"

schematic_goal [simplified,simp]:
  "pp_\<Theta> rdx\<^sub>0 0 = ?p0"
  "pp_\<Theta> rdx\<^sub>0 3 = ?p3"
  "pp_\<Theta> rdx\<^sub>0 9 = ?p9"
  "i\<notin>{0,3,9} \<Longrightarrow> pp_\<Theta> rdx\<^sub>0 i = None"
  unfolding pp_\<Theta>_def by auto

lemma incr_aux1:
  fixes a b :: "'a::len word"
  shows "a \<le> b \<Longrightarrow> a \<noteq> b \<Longrightarrow> unat (a+1) = Suc (unat a)"
  by (smt Suc_eq_plus1 add.commute inc_i inc_le le_less not_less unatSuc unat_1 unat_plus_simple)

lemma incr_aux2:
  fixes a b :: "'a::len word"
  shows "a \<le> b \<Longrightarrow> a \<noteq> b \<Longrightarrow> a+1\<le>b"
  by (simp add: inc_le)

(* TODO: Move this VCG to more generic place! Currently placed here for quick experiments. *)
method vcg_clarify = (intro impI conjI)?, (((rule exI, rule conjI, assumption)+ | (simp add: prep_precond_conv))+)?
method vcg_step_aux = (rule wps_rls linvar_unfoldI, (assumption+)?); kbxfer?
method vcg_step = vcg_clarify, vcg_step_aux
method vcg = (vcg_step+, vcg_clarify)


lemma pp_std_invar: "is_std_invar (floyd.invar (pp_\<Theta> rdx\<^sub>0))"
  apply (rule floyd_invarI)
  apply (rewrite at "floyd_vcs \<hole> _" pp_\<Theta>_def)
  apply (intro floyd_vcsI; (clarsimp simp: prep_precond_conv)?)

  subgoal for s by vcg

  subgoal for s
    apply vcg
    apply (elim_determ thin_rl[of "VAL _ _ _"])
    apply (auto simp: incr_aux1 inc_le) []
    done
  done



theorem pow_prog_correct: "htriple
  (\<lambda>s. RIP 0 s \<and> PROG pow_prog s \<and> VAL halted\<^sub>L False s \<and> RDX n s)
  (\<lambda>s. RAX (2^unat n) s)"
  apply (rule floyd_htripleI[where \<Theta> = "pp_\<Theta> n"], clarify)
  subgoal by vcg
  subgoal by (rule pp_std_invar)
  subgoal for s \<phi>
    unfolding pp_\<Theta>_def
    by (clarsimp split: if_splits simp: prep_precond_conv)
  done

end
