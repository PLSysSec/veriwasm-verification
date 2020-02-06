lemma Test%1%:
    shows "\<forall> (src) . ( src \<in> general_regs ) \<longrightarrow> 
            (let (fam,n,o_sig) = Get_Instr_Sig  (Instr InstructionUnderTest RegSrcSize src);
                  test_formula = the ((the ((the ((instr_semantics semantics) (fam))) (n))) (o_sig));
                  start_regs = concat [(zip [src] Test%1%_src_start), Test%1%_xtra_regs_start]
               in exec_learned_instr_testing  
                    flag_annotation test_formula (Instr InstructionUnderTest RegSrcSize src)
                    (State start_regs [] Test%1%_flags_start \<sigma>)) 
           = (State (concat [(zip [src] Test%1%_src_end),Test%1%_xtra_regs_end]) [] Test%1%_flags_end \<sigma>)"
  by (simp)
  