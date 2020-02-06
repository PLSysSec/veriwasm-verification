lemma Test%1%:
  assumes "dst \<noteq> src"
  and     "dst \<in> general_regs"
  and     "src \<in> general_regs"
  and     "dst \<noteq> rax"
  and     "src \<noteq> rax"
  shows "  (let  start_regs = concat [(zip [dst] Test%1%_dst_start), (zip [src] Test%1%_src_start), Test%1%_xtra_regs_start]
            in   exec_instr assembly semantics flag_annotation (Instr InstructionUnderTest RegDstSize dst RegSrcSize src) 0
                            (State start_regs [] Test%1%_flags_start \<sigma>)) 
            = (State (concat [(zip [dst] Test%1%_dst_end),(zip [src] Test%1%_src_end),Test%1%_xtra_regs_end]) [] Test%1%_flags_end \<sigma>)"
  apply (insert assms)
  apply (simp)
  apply (rewrite_one_let' del: incr_rip_def)+
  by    (simp add:incr_rip_def)
