theory Mockup_Test_Abs_Sys
  imports Abstract_System More_Eisbach_Tools
begin
  typedecl state
  typedecl program
  typedecl location

  consts step :: "program \<Rightarrow> state \<Rightarrow> state"
  consts halted :: "program \<Rightarrow> state \<Rightarrow> bool"
  consts location :: "state \<Rightarrow> location"




  definition "stepse \<pi> \<equiv> doE { s\<leftarrow>sget; sput (step \<pi> s) }"


  global_interpretation det_system "stepse \<pi>" "halted \<pi>" for \<pi>
    defines yields = yields'
    .

  declare yields_unfold[code]

  interpretation cfg_system "stepse \<pi>" "halted \<pi>" "\<lambda>_. True" location
    apply unfold_locales by (rule is_weak_invarI) simp


method vcg_clarify = (intro impI conjI)?, (((rule exI, rule conjI, assumption)+ | (simp add: prep_precond_conv))+)?
method vcg_step_aux = (rule wps_rls linvar_unfoldI, (assumption+)?); kbxfer?
method vcg_step = vcg_clarify, vcg_step_aux
method vcg = (vcg_step+, vcg_clarify)

  term htriple

  lemma "htriple \<pi> (\<lambda>s. location s = foo) Q"
    apply (rule floyd_htripleI[where \<Theta>="[
      foo \<mapsto> \<lambda>s. \<not> halted \<pi> s \<and> \<Phi>\<^sub>1 s,
      bar \<mapsto> \<lambda>s. halted \<pi> s \<and> \<Phi>\<^sub>2 s,
      bar2 \<mapsto> \<lambda>s. halted \<pi> s \<and> \<Phi>\<^sub>3 s
      ]"])

    subgoal
      apply (rule linvar_unfoldI)
      apply simp
      sorry

    subgoal
      apply (rule floyd_invarI)
      apply (intro floyd_vcsI; (clarsimp simp: )?)

      apply (subst stepse_def[abs_def])
      apply (simp add: wps_eqs)

      apply (rule linvar_unfoldI)
      apply clarsimp apply (intro impI conjI; simp?)

      prefer 16
      apply (subst stepse_def[abs_def])
      apply (simp add: wps_eqs)
      sorry

    subgoal for s
      apply (clarsimp split: if_splits)
      sorry

    oops



  term "yields \<pi>"





end

