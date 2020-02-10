theory Presimplified_Semantics_Manual2
  imports reassembly_all.Presimplified_Semantics
begin

(* This file contains instructions for which we unecessarily use manual semantics
   For each of these instructions, we need to add the learned semantics to the strata_rules_5flags file,
   and prove two theorems in Presimplified_Semantics.thy: one that is_manual returns False, and one that provides semantics.
*)
context presimplified_semantics
begin



lemma is_manual_mov_r32_immLabel[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Reg (General ThirtyTwo r1_32)) (Immediate ImmSize (ImmLabel imm))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_mov_r32_immLabel[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Mov) (Reg (General ThirtyTwo r1_32)) (Immediate SixtyFour (ImmLabel Imm))) si = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done

lemma is_manual_movsd_m64_xmm[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_SSE2_SIMD Movsd) (Memory SixtyFour Mem) (Storage (Reg (SIMD OneHundredTwentyEight r0 r1 r2 r3)))) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_movsd_m64_xmm[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_SSE2_SIMD Movsd) (Memory SixtyFour Mem) (Storage (Reg (SIMD OneHundredTwentyEight r0 r1 r2 r3)))) si = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done


lemma is_manual_ucomisd_xmm_m64[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_SSE2_SIMD Ucomisd) (Reg (SIMD OneHundredTwentyEight r0 r1 r2 r3)) (Storage (Memory SixtyFour Mem))) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_ucomisd_xmm_m64[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_SSE2_SIMD Ucomisd) (Reg (SIMD OneHundredTwentyEight r0 r1 r2 r3)) (Storage (Memory SixtyFour Mem))) si = ?x"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done

lemma is_manual_ucomisd_cvttsd2si_r32_xmm[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_SSE2_SIMD Cvttsd2si) (Reg (General ThirtyTwo r4)) (Storage (Reg (SIMD OneHundredTwentyEight r0 r1 r2 r3)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_cvttsd2si_r32_xmm[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_SSE2_SIMD Cvttsd2si) (Reg (General ThirtyTwo r4)) (Storage (Reg (SIMD OneHundredTwentyEight r0 r1 r2 r3)))) si = 
            (\<lambda> \<sigma> . \<sigma>\<lparr> regs := (regs \<sigma>)(r4 := ucast (cvttsd2si (regs \<sigma> r3)))\<rparr>)"
   apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
   apply (rewrite_one_let' add: semantics_def)
   apply (rewrite_one_let')+
  by (simp add: simp_rules)


lemma is_manual_cmp_m64_r64[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Cmp) (Memory SixtyFour a) (Storage (Reg (General SixtyFour r64)))) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_cmp_m64_r64[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Cmp) (Memory SixtyFour a) (Storage (Reg (General SixtyFour r64))))  si = ?x"
   apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done

lemma is_manual_Sar[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Sar) op1 op2) = True"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

schematic_goal get_semantics_Sar[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Sar) op1 op2) si = ?x"
   apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done

end
end
