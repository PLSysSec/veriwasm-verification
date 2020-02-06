lemma Test%1%:
  shows  " (dst = simd_dst \<and> src \<in> general_regs) \<longrightarrow>          
     (let'  
        (fam,n,o_sig) = Get_Instr_Sig  (Instr InstructionUnderTest dst RegSrcSize src);
        test_formula = the ((the ((the ((instr_semantics semantics) (fam))) (n))) (o_sig));
        start_regs = concat [(zip (tuple_to_list dst) Test%1%_dst_start),  
                             (zip [src] Test%1%_src_start), 
                             Test%1%_xtra_regs_start]
      in exec_learned_instr_testing  
          flag_annotation test_formula (Instr InstructionUnderTest dst RegSrcSize src)
          (State start_regs [] Test%1%_flags_start \<sigma>)) 
   = (let'
        end_regs = concat [(zip (tuple_to_list dst) Test%1%_dst_end),  
                           (zip [src] Test%1%_src_end), 
                            Test%1%_xtra_regs_end]
      in State end_regs [] Test%1%_flags_end \<sigma>)"
  by (rewrite_one_let'_and_simplify)+
