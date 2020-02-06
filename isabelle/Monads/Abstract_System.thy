theory Abstract_System
  imports SE_Monad
begin

locale det_system =
  fixes step :: "(unit,'s) se"
  fixes halted :: "'s \<Rightarrow> bool"
begin

  definition "step_rel s s' \<equiv>
    case s of
      None \<Rightarrow> False
    | Some s \<Rightarrow> \<not>halted s \<and> map_option snd (step s) = s'"

  fun terminated where
    "terminated (Some s) = halted s"
  | "terminated None = True "

  lemma terminated_no_step[simp, intro]: "terminated s \<Longrightarrow> \<not>step_rel s s'"
    by (auto simp: step_rel_def split: option.splits)

  lemma terminated_no_step': "terminated s \<longleftrightarrow> (\<forall>s'. \<not>step_rel s s')"
    by (cases s; auto simp: step_rel_def split: option.splits)

  definition "is_result s s' \<equiv> step_rel\<^sup>*\<^sup>* (Some s) s' \<and> terminated s'"

  lemma is_result_1_step_eq: "\<not>halted s \<Longrightarrow> step s = Some ((),sh) \<Longrightarrow> is_result s s' \<longleftrightarrow> is_result sh s'"
    apply (rule iffI)
    subgoal
      unfolding is_result_def step_rel_def
      by (auto split: option.splits elim: converse_rtranclpE)
    subgoal
      unfolding is_result_def
      apply simp
      apply (rule converse_rtranclp_into_rtranclp)
      apply (auto simp: step_rel_def) []
      by simp
    done

  lemma result_determ: "is_result s s' \<Longrightarrow> is_result s s'' \<Longrightarrow> s'=s''"
    unfolding is_result_def
    apply safe
    apply (induction rule: converse_rtranclp_induct)
    apply (erule converse_rtranclpE; auto; fail)

    apply (erule converse_rtranclpE[of _ _ s'']; clarsimp)
    apply (auto simp: step_rel_def split: option.splits; fail)
    done

  definition "yields' s \<equiv> if \<exists>s'. is_result s s' then Some (THE s'. is_result s s') else None"

  lemma yields_eq_Some_conv: "yields' s = Some s' \<longleftrightarrow> is_result s s'"
    unfolding yields'_def using result_determ
    by (auto simp: theI2)

  lemma yields_eq_None_conv: "yields' s = None \<longleftrightarrow> (\<nexists>s'. is_result s s')"
    unfolding yields'_def by auto

  lemma halted_res[simp]: "halted s \<Longrightarrow> is_result s (Some s)"
    by (auto simp: is_result_def)

  lemma exec1_None_res[simp]: "\<lbrakk>step s = None; \<not> halted s\<rbrakk> \<Longrightarrow> is_result s None"
    by (auto simp: is_result_def step_rel_def r_into_rtranclp)

  lemma yields_unfold: "yields' s = (
    if halted s then
      Some (Some s)
    else
      case step s of
        Some (_,s') \<Rightarrow> yields' s'
      | None \<Rightarrow> Some None
    )"
    apply (clarsimp split: option.splits simp: yields_eq_Some_conv yields_eq_None_conv)
    subgoal for s'
      apply (cases "yields' s"; cases "yields' s'"; simp only:)
      apply (auto
        split: option.splits
        simp: yields_eq_Some_conv yields_eq_None_conv is_result_1_step_eq result_determ
        )+
      done
    done

  lemma yields'_simps[simp]:
    "halted s \<Longrightarrow> yields' s = Some (Some s)"
    "\<not>halted s \<Longrightarrow> step s = Some ((),s') \<Longrightarrow> yields' s = yields' s'"
    "\<not>halted s \<Longrightarrow> step s = None \<Longrightarrow> yields' s = Some None"
    by (subst yields_unfold; auto split: option.splits)+


  definition "is_invar \<phi> \<equiv> \<forall>s. \<phi> s \<and> \<not>halted s \<longrightarrow> wps step (\<lambda>_. \<phi>) s"
  definition "is_weak_invar \<phi> \<equiv> \<forall>s s'. \<phi> s \<and> \<not>halted s \<and> step s = Some ((),s') \<longrightarrow> \<phi> s'"

  lemma is_invar_step: "is_invar \<phi> \<Longrightarrow> \<phi> s \<Longrightarrow> step_rel (Some s) so' \<Longrightarrow> \<exists>s'. so'=Some s' \<and> \<phi> s'"
    by (auto simp: is_invar_def wps_def step_rel_def split: option.splits)

  lemma is_weak_invar_step: "is_weak_invar \<phi> \<Longrightarrow> \<phi> s \<Longrightarrow> step_rel (Some s) (Some s') \<Longrightarrow> \<phi> s'"
    by (auto simp: is_weak_invar_def wps_def step_rel_def split: option.splits)

  lemma is_invar_exec:
    assumes "is_invar \<phi>"
    assumes "\<phi> s"
    assumes "step_rel\<^sup>*\<^sup>* (Some s) so'"
    shows "\<exists>s'. so'=Some s' \<and> \<phi> s'"
    using assms(3,2)
    apply (induction a\<equiv>"Some s" arbitrary: s rule: converse_rtranclp_induct)
    subgoal by simp
    apply (drule (1) is_invar_step[OF \<open>is_invar \<phi>\<close>])
    by auto

  lemma step_rel_rtrancl_None_eq[simp]: "step_rel\<^sup>*\<^sup>* None s \<longleftrightarrow> s=None"
    using converse_rtranclpE by fastforce

  lemma is_weak_invar_exec:
    assumes "is_weak_invar \<phi>"
    assumes "\<phi> s"
    assumes "step_rel\<^sup>*\<^sup>* (Some s) (Some s')"
    shows "\<phi> s'"
    using assms(3,2)
    apply (induction a\<equiv>"Some s" arbitrary: s rule: converse_rtranclp_induct)
    subgoal by simp
    subgoal for z s
      apply (cases z; simp)
      apply (drule (1) is_weak_invar_step[OF \<open>is_weak_invar \<phi>\<close>])
      by auto
    done

  lemma is_invar_yields:
    assumes "is_invar \<phi>"
    assumes "\<phi> s"
    assumes "yields' s = Some so'"
    shows "\<exists>s'. so'=Some s' \<and> halted s' \<and> \<phi> s'"
    using assms
    apply (auto simp: yields_eq_Some_conv is_result_def is_invar_exec)
    using is_invar_exec terminated.simps(1) by blast

  lemma is_weak_invar_yields:
    assumes "is_weak_invar \<phi>"
    assumes "\<phi> s"
    assumes "yields' s = Some (Some s')"
    shows "\<phi> s'"
    using assms
    by (auto simp: yields_eq_Some_conv is_result_def is_weak_invar_exec)




  lemma is_invarI:
    assumes "\<And>s. \<lbrakk> \<phi> s; \<not>halted s \<rbrakk> \<Longrightarrow> wps step (\<lambda>_. \<phi>) s"
    shows "is_invar \<phi>"
    using assms
    unfolding is_invar_def by blast

  lemma is_weak_invarI:
    assumes "\<And>s s'. \<lbrakk> \<phi> s; \<not>halted s; step s = Some ((),s') \<rbrakk> \<Longrightarrow> \<phi> s'"
    shows "is_weak_invar \<phi>"
    using assms
    unfolding is_weak_invar_def by blast

  lemma app_weak_invar:
    assumes "is_weak_invar \<phi>'"
    assumes "\<not>halted s" "\<phi>' s"
    assumes "wps step (\<lambda>_ s'. \<phi>' s' \<longrightarrow> \<phi> s') s"
    shows "wps step (\<lambda>_. \<phi>) s"
    using assms unfolding is_weak_invar_def wps_def
    by (auto split: option.splits)

  lemma is_weak_invarD:
    assumes "is_weak_invar \<phi>"
    assumes "\<phi> s" "\<not>halted s"
    assumes "step s = Some ((),s')"
    shows "\<phi> s'"
    using assms
    by (auto simp: is_weak_invar_def)


end

locale std_invar_system = det_system step halted for step :: "(unit,'s) se" and halted +
  fixes stdI :: "'s \<Rightarrow> bool"
  assumes stdI: "is_weak_invar stdI"
begin
  definition "is_std_invar \<phi> \<equiv> is_invar (\<lambda>s. stdI s \<and> \<phi> s)"

  lemma is_std_invarI:
    assumes "\<And>s. \<lbrakk> \<phi> s; stdI s; \<not>halted s \<rbrakk> \<Longrightarrow> wps step (\<lambda>_ s'. stdI s' \<longrightarrow> \<phi> s') s"
    shows "is_std_invar \<phi>"
    unfolding is_std_invar_def
    apply (rule is_invarI)
    apply (rule app_weak_invar[OF stdI]; simp)
    using assms by blast

  definition "htriple P Q \<equiv> \<forall>s. stdI s \<and> P s \<longrightarrow> (case yields' s of
      None \<Rightarrow> True
    | Some None \<Rightarrow> False
    | Some (Some s') \<Rightarrow> Q s'
  )"

  lemma htripleI:
    assumes "\<And>s so'. \<lbrakk> stdI s; P s; yields' s = Some so' \<rbrakk> \<Longrightarrow> \<exists>s'. so' = Some s' \<and> (stdI s' \<longrightarrow> Q s')"
    shows "local.htriple P Q"
    using assms unfolding htriple_def
    using local.is_weak_invar_yields local.stdI
    by (fastforce split: option.split)

end


locale floyd_system = std_invar_system step halted stdI for step :: "(unit,'s) se" and halted stdI +
  fixes \<Theta> :: "'s \<rightharpoonup> bool"
begin
  definition "has_invar s \<equiv> halted s \<or> \<Theta> s \<noteq> None"

  lemma has_invar_simps[simp]:
    "\<Theta> s = Some x \<Longrightarrow> has_invar s"
    "\<Theta> s = None \<Longrightarrow> has_invar s = halted s"
    by (auto simp: has_invar_def)

  sublocale isys: det_system step has_invar .


  definition "invar s \<equiv>
    case isys.yields' s of
      None \<Rightarrow> False
    | Some so' \<Rightarrow> (case so' of None \<Rightarrow> False | Some s' \<Rightarrow> \<Theta> s' = Some True)
    "

  lemma invar_unfold:
    "invar s = (case \<Theta> s of Some b \<Rightarrow> b | None \<Rightarrow> (\<not>halted s \<and> wps (step) (\<lambda>_. invar) s))"
    unfolding invar_def wps_def
    apply (subst isys.yields_unfold)
    by (auto split: option.splits)


  lemma invar_step: "\<not>has_invar s \<Longrightarrow> invar s = wps (step) (\<lambda>_. invar) s"
    by (auto simp: invar_def wps_def split: option.split)


  lemma invar_imp_\<Theta>_true: "invar s \<Longrightarrow> has_invar s \<Longrightarrow> \<Theta> s = Some True"
    unfolding invar_def by (auto split: option.splits)

  lemma invarI:
    assumes "\<And>s. \<lbrakk> \<Theta> s = Some True; stdI s; \<not>halted s \<rbrakk> \<Longrightarrow> wps step (\<lambda>_ s'. stdI s' \<longrightarrow> invar s') s"
    shows "is_std_invar invar"
  proof (rule is_std_invarI)
    fix s
    assume "invar s" "\<not>halted s" "stdI s"

    from \<open>invar s\<close> consider (HAS_INVAR) "\<Theta> s = Some True" | (NO_INVAR) "\<Theta> s = None"
      using has_invar_def invar_imp_\<Theta>_true by blast
    then show "wps step (\<lambda>_ s'. stdI s' \<longrightarrow> invar s') s" proof cases
      case HAS_INVAR
      then show ?thesis
        using \<open>\<not> halted s\<close> \<open>stdI s\<close> assms by blast
    next
      case NO_INVAR
      hence "\<not>has_invar s" using \<open>\<not> halted s\<close> by (auto simp: has_invar_def)
      then show ?thesis
        using \<open>invar s\<close> invar_step wps_mono by fastforce
    qed
  qed


  lemma halted_invar_conv:
    assumes [simp]: "halted s"
    shows "invar s \<longleftrightarrow> \<Theta> s = Some True"
    by (subst invar_unfold) (auto split: option.split)

  lemma std_invar_yields:
    assumes "is_std_invar invar"
    assumes "stdI s" "invar s" "yields' s = Some so'"
    shows "\<exists>s'. so' = Some s' \<and> halted s' \<and> stdI s' \<and> \<Theta> s' = Some True"
  proof -
    from assms(1) have "is_invar (\<lambda>s. stdI s \<and> invar s)" by (simp add: is_std_invar_def)
    note X1 = is_invar_yields[OF this]

    from assms(2-) X1 obtain s' where X2: "so' = Some s'" "halted s'" "stdI s'" "invar s'"
      by auto
    with halted_invar_conv have "\<Theta> s' = Some True" by blast
    with X2 show ?thesis by blast
  qed

end



locale cfg_system = std_invar_system step halted stdI for step :: "(unit,'s) se" and halted stdI +
  fixes location :: "'s \<Rightarrow> 'loc"
begin
  definition linvar :: "('loc \<Rightarrow> ('s \<Rightarrow> bool) option) \<Rightarrow> 's \<Rightarrow> bool option" where
    "linvar \<Theta> s \<equiv>
        case \<Theta> (location s) of
          None \<Rightarrow> None
        | Some \<phi> \<Rightarrow> Some (\<phi> s)"

  sublocale floyd: floyd_system step halted stdI "linvar \<Theta>" for \<Theta> by standard

  definition "floyd_vcs \<Theta>' \<Theta> \<equiv>
    \<forall>\<phi> s. \<Theta>' (location s) = Some \<phi> \<and> \<phi> s \<and> stdI s \<and> \<not>halted s \<longrightarrow> wps step (\<lambda>_ s'. stdI s' \<longrightarrow> floyd.invar \<Theta> s') s"

  lemma floyd_vcs_emptyI:
    "floyd_vcs Map.empty \<Theta>"
    by (auto simp: floyd_vcs_def)

  lemma floyd_vcs_updI:
    assumes "floyd_vcs \<Theta>' \<Theta>"
    assumes "\<And>s. \<lbrakk> location s = l; \<phi> s; stdI s; \<not>halted s \<rbrakk> \<Longrightarrow> wps step (\<lambda>_ s'. stdI s' \<longrightarrow> floyd.invar \<Theta> s') s"
    shows "floyd_vcs (\<Theta>'(l\<mapsto>\<phi>)) \<Theta>"
    using assms
    by (auto simp: floyd_vcs_def)

  lemmas floyd_vcsI = floyd_vcs_emptyI floyd_vcs_updI

  lemma linvar_conv:
    "linvar \<Theta> s = None \<longleftrightarrow> \<Theta> (location s) = None"
    "linvar \<Theta> s = Some b \<longleftrightarrow> (\<exists>\<phi>. \<Theta> (location s) = Some \<phi> \<and> b=\<phi> s)"
    by (auto simp: linvar_def split: option.splits)

  lemma floyd_invarI: "floyd_vcs \<Theta> \<Theta> \<Longrightarrow> is_std_invar (floyd.invar \<Theta>)"
    apply (rule floyd.invarI)
    unfolding floyd_vcs_def
    by (auto simp: linvar_conv)

  lemma linvar_unfoldI:
    assumes "case \<Theta> (location s) of
        None \<Rightarrow> \<not>halted s \<and> wps step (\<lambda>_. floyd.invar \<Theta>) s
      | Some \<phi> \<Rightarrow> \<phi> s"
    shows "floyd.invar \<Theta> s"
    apply (subst floyd.invar_unfold)
    using assms
    by (auto simp: linvar_conv split: option.split)


  lemma floyd_htripleI:
    assumes "\<And>s. P s \<Longrightarrow> floyd.invar \<Theta> s" \<comment> \<open>Precondition implies invariant\<close>
    assumes "is_std_invar (floyd.invar \<Theta>)" \<comment> \<open>Invariant\<close>
    assumes "\<And>s \<phi>. \<lbrakk> halted s; stdI s; \<Theta> (location s) = Some \<phi>; \<phi> s \<rbrakk> \<Longrightarrow> Q s" \<comment> \<open>On termination, invariant implies postcondition\<close>
    shows "local.htriple P Q"
    apply (rule htripleI)
    subgoal for s so'
      using floyd.std_invar_yields[OF assms(2), of s so']
      apply (clarsimp simp: linvar_conv)
      using assms(1,3) by blast
    done


end

end
