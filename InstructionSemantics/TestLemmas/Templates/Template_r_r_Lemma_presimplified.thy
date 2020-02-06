lemma Test%1%:
  assumes "dst \<noteq> src"
  and     "dst \<in> general_regs"
  and     "src \<in> general_regs"
shows "    (let  start_regs = concat [(zip [dst] Test1_dst_start), (zip [src] Test1_src_start), Test1_xtra_regs_start]
            in   exec_instr assembly semantics flag_annotation (Instr InstructionUnderTest RegDstSize dst RegSrcSize src) 0
                            (State start_regs [] Test1_flags_start \<sigma>)) 
            = (State (concat [(zip [dst] Test1_dst_end),(zip [src] Test1_src_end),Test1_xtra_regs_end]) [] Test1_flags_end \<sigma>)"
  apply (insert assms)
  apply(simp add: exec_instr_def is_manual incr_rip_def) 
  apply(subst presimplify)
  apply(rewrite_one_let')+
  apply(simp add:incr_rip_def parity_def xor_def )
  apply (rule state_eqI)
  by (auto) 
