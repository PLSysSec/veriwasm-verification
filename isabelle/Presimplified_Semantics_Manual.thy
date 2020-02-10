theory Presimplified_Semantics_Manual
  imports "reassembly_setup.Leviathan_Setup"
begin

(*5 flags generation CF,SF,OF,ZF,PF *)
instruction_semantics_parser "../InstructionSemantics/strata_rules_5flags"   
lemmas strata_rules_5flags.semantics_def [code]         

locale presimplified_semantics = execution_context + strata_rules_5flags
begin

named_theorems presimplify
named_theorems is_manual

(* MANUAL SEMANTICS *)

schematic_goal unfold_semantics:
  shows \<open>instr_semantics semantics instr_sig = ?x\<close>
  by (simp add: semantics_def simp_rules)

(* push and pop *)

lemma is_manual_Push[is_manual]:
  shows "is_manual assembly semantics (Unary (IS_8088 Push) op1) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_Push[presimplify]:
  shows "get_semantics assembly semantics (Unary (IS_8088 Push) op1) = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done

lemma is_manual_Pop[is_manual]:
  shows "is_manual assembly semantics (Unary (IS_8088 Pop) op1) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_Pop[presimplify]:
  shows "get_semantics assembly semantics (Unary (IS_8088 Pop) op1) = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done

(* shifting *)

lemma is_manual_Shl[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Shl) op1 op2) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_Shl[presimplify]:
  shows "get_semantics assembly semantics (Binary (IS_8088 Shl) op1 op2) = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done

lemma is_manual_Shr[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Shr) op1 op2) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_Shr[presimplify]:
  shows "get_semantics assembly semantics (Binary (IS_8088 Shr) op1 op2) = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done

(* Bsr *)

lemma is_manual_Sbr[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_80386 Bsr) op1 op2) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_Sbr[presimplify]:
  shows "get_semantics assembly semantics (Binary (IS_80386 Bsr) op1 op2) = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done


(* call / ret / leave *)

lemma is_manual_Leave[is_manual]:
  shows "is_manual assembly semantics (Nullary (IS_80188 Leave)) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_Leave[presimplify]:
  shows "get_semantics assembly semantics (Nullary (IS_80188 Leave)) = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done

lemma is_manual_Ret[is_manual]:
  shows "is_manual assembly semantics (Nullary (IS_8088 Ret)) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_Ret[presimplify]:
  shows "get_semantics assembly semantics (Nullary (IS_8088 Ret)) = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done

lemma is_manual_Call[is_manual]:
  shows "is_manual assembly semantics (Unary (IS_8088 Call) op1) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_Call[presimplify]:
  shows "get_semantics assembly semantics (Unary (IS_8088 Call) op1) = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done

(* lea *)
lemma is_manual_Lea[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Lea) op1 op2) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_Lea[presimplify]:
  shows "get_semantics assembly semantics (Binary (IS_8088 Lea) op1 op2) = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done

(* imul *)
lemma is_manual_Imul[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Imul) op1 op2) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_Imul[presimplify]:
  shows "get_semantics assembly semantics (Binary (IS_8088 Imul) op1 op2) = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done

(* jumps *)

lemma is_manual_Jmp[is_manual]:
  shows "is_manual assembly semantics (Unary (IS_8088 Jmp) op1) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_Jmp[presimplify]:
  shows "get_semantics assembly semantics (Unary (IS_8088 Jmp) op1) = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done

lemma is_manual_Ja[is_manual]:
  shows "is_manual assembly semantics (Unary (IS_8088 Ja) op1) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_Ja[presimplify]:
  shows "get_semantics assembly semantics (Unary (IS_8088 Ja) op1) = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done

lemma is_manual_Jae[is_manual]:
  shows "is_manual assembly semantics (Unary (IS_8088 Jae) op1) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_Jae[presimplify]:
  shows "get_semantics assembly semantics (Unary (IS_8088 Jae) op1) = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done

lemma is_manual_Jb[is_manual]:
  shows "is_manual assembly semantics (Unary (IS_8088 Jb) op1) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_Jb[presimplify]:
  shows "get_semantics assembly semantics (Unary (IS_8088 Jb) op1) = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done

lemma is_manual_Jbe[is_manual]:
  shows "is_manual assembly semantics (Unary (IS_8088 Jbe) op1) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_Jbe[presimplify]:
  shows "get_semantics assembly semantics (Unary (IS_8088 Jbe) op1) = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done

lemma is_manual_Je[is_manual]:
  shows "is_manual assembly semantics (Unary (IS_8088 Je) op1) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_Je[presimplify]:
  shows "get_semantics assembly semantics (Unary (IS_8088 Je) op1) = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done

lemma is_manual_Jle[is_manual]:
  shows "is_manual assembly semantics (Unary (IS_8088 Jle) op1) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_Jle[presimplify]:
  shows "get_semantics assembly semantics (Unary (IS_8088 Jle) op1) = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done

lemma is_manual_Jne[is_manual]:
  shows "is_manual assembly semantics (Unary (IS_8088 Jne) op1) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_Jne[presimplify]:
  shows "get_semantics assembly semantics (Unary (IS_8088 Jne) op1) = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done


(* sub *)
lemma is_manual_sub_m64_imm64[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Sub) (Memory SixtyFour Mem) (Immediate ImmSize (ImmVal ImmValue))) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_sub_m64_imm64[presimplify]:
  shows "get_semantics assembly semantics (Binary (IS_8088 Sub) (Memory SixtyFour Mem) (Immediate ImmSize (ImmVal Immvalue))) = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done


end
end
