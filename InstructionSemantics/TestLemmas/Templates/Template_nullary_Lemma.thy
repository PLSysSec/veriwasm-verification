lemma Test%1%:
    shows " (let (fam,n,o_sig) = Get_Instr_Sig  (Instr InstructionUnderTest);
                  test_formula = the ((the ((the ((instr_semantics semantics) (fam))) (n))) (o_sig))
               in exec_learned_instr_testing  
                    flag_annotation test_formula (Instr InstructionUnderTest)
                    (State Test%1%_xtra_regs_start [] Test%1%_flags_start \<sigma>)) 
           = (State Test%1%_xtra_regs_end [] Test%1%_flags_end \<sigma>)"
  by (rewrite_one_let'_and_simplify)+
  