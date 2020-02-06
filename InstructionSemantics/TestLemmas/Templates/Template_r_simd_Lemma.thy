lemma Test%1%:
  shows  " ( dst \<in> general_regs \<and> src = simd_src ) \<longrightarrow>          
     (let'  
        (fam,n,o_sig) = Get_Instr_Sig  (Instr InstructionUnderTest RegDstSize dst src);
        test_formula = the ((the ((the ((instr_semantics semantics) (fam))) (n))) (o_sig));
        start_regs = concat [(zip [dst] Test%1%_dst_start),  
                             (zip (tuple_to_list src) Test%1%_src_start), 
                             Test%1%_xtra_regs_start]
      in exec_learned_instr_testing  
          flag_annotation test_formula (Instr InstructionUnderTest RegDstSize dst src)
          (State start_regs [] Test%1%_flags_start \<sigma>)) 
   = (let'
        end_regs = concat [(zip [dst] Test%1%_dst_end),  
                           (zip (tuple_to_list src) Test%1%_src_end), 
                            Test%1%_xtra_regs_end]
      in State end_regs [] Test%1%_flags_end \<sigma>)"
  by (rewrite_one_let'_and_simplify)+
