lemma Test%1%:
  shows "\<forall> (dst) . dst \<in> general_regs \<longrightarrow>
    (let' (fam,n,o_sig) = Get_Instr_Sig  (Instr InstructionUnderTest RegDstSize dst (uint (last Test%1%_src_start)));
           test_formula = the ((the ((the ((instr_semantics semantics) (fam))) (n))) (o_sig))
      in exec_learned_instr_testing  
          flag_annotation test_formula (Instr InstructionUnderTest RegDstSize dst (uint (last Test%1%_src_start)))
          (State (concat [(zip [dst] Test%1%_dst_start),Test%1%_xtra_regs_start]) [] Test%1%_flags_start \<sigma>)) 
    = (State (concat [(zip [dst] Test%1%_dst_end),Test%1%_xtra_regs_end]) [] Test%1%_flags_end \<sigma>)"

proof-
  show ?thesis
    by (rewrite_one_let'_and_simplify)+
qed
