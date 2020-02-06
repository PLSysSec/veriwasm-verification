theory Lense_Knowledge_Base (* TODO: Improve Theory Name! *)
  imports SE_Monad More_Eisbach_Tools
begin

section \<open>Generic Lens Based Transfer Tool\<close>
definition "VAL L x s \<equiv> hlens L \<and> get L s = Some x"

lemma VAL_get[simp]:
  assumes "VAL L x s"
  shows "pre_get L s" "get' L s = x"
  using assms unfolding VAL_def by auto


definition DEL_TAG :: "bool \<Rightarrow> bool" where "DEL_TAG x \<equiv> x"
definition DEL_TAG' :: "bool \<Rightarrow> bool" where "DEL_TAG' x \<equiv> True"
lemma DEL_TAG_cong[cong]: "DEL_TAG x = DEL_TAG x" ..
lemma DEL_TAG'_cong[cong]: "DEL_TAG' x = DEL_TAG' x" ..

lemmas DEL_congs = DEL_TAG_cong DEL_TAG'_cong

lemma DEL_TAG'E: "P \<Longrightarrow> DEL_TAG' P \<Longrightarrow> Q \<Longrightarrow> Q" .

lemma DEL_TAG'_simp:
  "DEL_TAG' x \<Longrightarrow> x = DEL_TAG x"
  by (auto simp: DEL_TAG_def)



definition KBXFER :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool" where "KBXFER R s s' \<equiv> R s s'"

lemma KBXFER_trans: "KBXFER R\<^sub>1 s sh \<Longrightarrow> KBXFER R\<^sub>2 sh s' \<Longrightarrow> KBXFER (R\<^sub>1 OO R\<^sub>2) s s'"
  by (auto simp: KBXFER_def)

lemma KBXFER_transE:
  assumes "KBXFER R s\<^sub>1 s\<^sub>2"
  assumes "KBXFER R' s\<^sub>2 s\<^sub>3"
  obtains "KBXFER (R OO R') s\<^sub>1 s\<^sub>3" "DEL_TAG' (KBXFER R' s\<^sub>2 s\<^sub>3)"
  using KBXFER_trans[OF assms] by (auto simp: DEL_TAG'_def)

named_theorems DEL_KBXFER_simps

lemma [DEL_KBXFER_simps]:
  assumes "KBXFER R s s'"
  shows
    "VAL L x s = DEL_TAG (VAL L x s)"
    by (auto simp: DEL_TAG_def)


lemma KBXFER_simp: "KBXFER R s s' \<Longrightarrow> eq_on\<^sub>L R L \<Longrightarrow> VAL L x s = VAL L x s'"
  unfolding VAL_def KBXFER_def
  by (simp add: eq_on\<^sub>L_def)

method handle_del =
  ((determ \<open>erule (1) DEL_TAG'E\<close>)+)?;
  elim_determ thin_rl[of "DEL_TAG _"] thin_rl[of "DEL_TAG' _"]

method kbxfer_trans =
  (determ \<open>erule (1) KBXFER_transE\<close>)+;
  handle_del;
  (simp only: triv_forall_equality)?


method kbxfer' =
  (simp add: KBXFER_simp eq_on_ltrans_indepI eq_on_compI)

method kbxfer =
  kbxfer';
  (simp only: DEL_KBXFER_simps cong: DEL_TAG_cong)?;
  elim_determ thin_rl[of "KBXFER _ _ _"] thin_rl[of "DEL_TAG _"];
  (simp only: triv_forall_equality)?


section \<open>Wps Setup\<close>

lemma wps_use_val_eq[wps_iffs]:
  assumes "VAL L x s"
  shows "wps (use L) Q s \<longleftrightarrow> Q x s"
  supply wps_use_eq[wps_iffs]
  using assms by (auto simp: VAL_def wps_eqs)

lemma wps_upd_val_eq[wps_simps]  (* Not in wps_rls, as we will put a kbxfer-based lemma there *):
  assumes "VAL L x s"
  shows "wps (L %= f) Q s \<longleftrightarrow> Q () (put' L (f x) s)"
  supply wps_upd_eq[wps_iffs]
  using assms by (auto simp: VAL_def wps_eqs)

lemma wps_upd_valI[wps_intros]:
  assumes "VAL L x s"
  assumes "\<And>s'. KBXFER (ltrans L) s s' \<Longrightarrow> VAL L (f x) s' \<Longrightarrow> Q () s'"
  shows "wps (L %= f) Q s"
  supply wps_upd_eq[wps_iffs]
  apply (rule wps_rls)
  using assms unfolding VAL_def
  by (auto simp: KBXFER_def)

lemma wps_set_valI[wps_intros]:
  assumes "hlens L" "pre_put L s"
  assumes "\<And>s'. KBXFER (ltrans L) s s' \<Longrightarrow> VAL L x s' \<Longrightarrow> Q () s'"
  shows "wps (L ::= x) Q s"
  supply wps_assign_eq[wps_iffs]
  apply (rule wps_rls)
  using assms unfolding VAL_def
  by (auto simp: KBXFER_def)


end
