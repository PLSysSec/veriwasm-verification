lemma Samereg_Test%1%:
    shows "\<forall> (dst) (src) . (src=dst)\<longrightarrow>
            (let' (fam,n,o_sig) = Get_Instr_Sig  (Instr InstructionUnderTest RegDstSize dst RegSrcSize src);
           test_formula = the ((the ((the ((instr_semantics semantics) (fam))) (n))) (o_sig))
           in exec_learned_instr_testing  
                flag_annotation test_formula  (Instr InstructionUnderTest RegDstSize dst RegSrcSize src)
                (State (concat [[(dst,Test1s_reg_start)],Test1s_xtra_regs_start]) [] Test1s_flags_start \<sigma>)) 
           = (let end_regs = concat [[(dst,Test1s_reg_end)],Test1_xtra_regs_end]
                in State end_regs [] Test1s_flags_end 
              \<sigma>)"
    apply (rewrite_one_let')+
    by (simp)
