lemma Test%1%:
  assumes "src \<in> general_regs"
    shows "(let start_regs = concat [(zip [src] Test%1%_src_start), Test%1%_xtra_regs_start]
               in exec_instr assembly semantics flag_annotation (Instr InstructionUnderTest  RegSrcSize src) 0
                            (State start_regs [] Test%1%_flags_start \<sigma>)) 
           = (State (concat [(zip [src] Test%1%_src_end),Test%1%_xtra_regs_end]) [] Test%1%_flags_end \<sigma>)"
  apply (insert assms)
  apply (simp)
  apply (rewrite_one_let' del: incr_rip_def)+
  by    (simp add:incr_rip_def to_bl_def)
