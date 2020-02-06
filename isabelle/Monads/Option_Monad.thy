theory Option_Monad
  imports Main "HOL-Library.Monad_Syntax"
begin

  definition "assert \<Phi> \<equiv> if \<Phi> then Some () else None"
  lemma assert_simps[simp]:
    "assert True = Some ()"
    "assert False = None"
    "assert \<Phi> = Some x \<longleftrightarrow> \<Phi>"
    "assert \<Phi> = None \<longleftrightarrow> \<not>\<Phi>"
    by (auto simp: assert_def)

  definition "wpo c Q \<equiv> \<exists>x. c=Some x \<and> Q x"

  lemma wpo_simps[simp]:
    "\<not>wpo None Q"
    "wpo (Some x) Q \<longleftrightarrow> Q x"
    "wpo (do {x\<leftarrow>m; f x}) Q \<longleftrightarrow> wpo m (\<lambda>x. wpo (f x) Q)"
    "wpo (assert \<Phi>) Qu \<longleftrightarrow> \<Phi> \<and> Qu ()"
    by (auto simp: wpo_def split: Option.bind_splits)

  lemma wpoI:
    "Q x \<Longrightarrow> wpo (Some x) Q"
    "wpo m (\<lambda>x. wpo (f x) Q) \<Longrightarrow> wpo (do {x\<leftarrow>m; f x}) Q"
    "\<lbrakk>\<Phi>; Qu ()\<rbrakk> \<Longrightarrow> wpo (assert \<Phi>) Qu"
    by auto

  lemma wpo_cons:
    "\<lbrakk>wpo c P; \<And>x. P x \<Longrightarrow> Q x\<rbrakk>\<Longrightarrow> wpo c Q"
    by (auto simp: wpo_def)


end
