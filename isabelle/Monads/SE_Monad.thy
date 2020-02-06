theory SE_Monad
imports Main Option_Monad Lenses
begin
  text \<open>State exception monad, without state type change\<close>
  type_synonym ('a,'s) se = "'s \<rightharpoonup> ('a \<times> 's)"

  (* return = RNormal, throw = Abrupt o Some   *)

  definition sreturn :: "'a \<Rightarrow> ('a,'s) se" where "sreturn x s \<equiv> Some (x,s)"
  definition sfail :: "('a,'s) se" where "sfail s \<equiv> None"
  definition sbind :: "('a,'s) se \<Rightarrow> ('a \<Rightarrow> ('b,'s) se) \<Rightarrow> ('b,'s) se" where
    "sbind m f s \<equiv> case m s of Some (x,s) \<Rightarrow> f x s | _ \<Rightarrow> None"

  definition sget :: "('s,'s) se" where "sget s \<equiv> Some (s,s)"
  definition sput :: "'s \<Rightarrow> (unit,'s) se" where "sput s' s \<equiv> Some ((),s')"

  (* adhoc_overloading bind sbind *)


  abbreviation (do_notation) bind_doE where "bind_doE \<equiv> sbind"

  subsection \<open>Syntax Magic\<close>
  notation (input) sbind (infixr "\<bind>" 54)
  notation (output) bind_doE (infixr "\<bind>" 54)


  nonterminal doE_binds and doE_bind
  syntax
    "_doE_block" :: "doE_binds \<Rightarrow> 'a" ("doE {//(2  _)//}" [12] 62)
    "_doE_bind"  :: "[pttrn, 'a] \<Rightarrow> doE_bind" ("(2_ \<leftarrow>/ _)" 13)
    "_doE_let" :: "[pttrn, 'a] \<Rightarrow> doE_bind" ("(2let _ =/ _)" [1000, 13] 13)
    "_doE_then" :: "'a \<Rightarrow> doE_bind" ("_" [14] 13)
    "_doE_final" :: "'a \<Rightarrow> doE_binds" ("_")
    "_doE_cons" :: "[doE_bind, doE_binds] \<Rightarrow> doE_binds" ("_;//_" [13, 12] 12)
    "_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixr "\<then>" 54)

  syntax (ASCII)
    "_doE_bind" :: "[pttrn, 'a] \<Rightarrow> doE_bind" ("(2_ <-/ _)" 13)
    "_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixr ">>" 54)

  translations
    "_doE_block (_doE_cons (_doE_then t) (_doE_final e))"
      \<rightleftharpoons> "CONST bind_doE t (\<lambda>_. e)"
    "_doE_block (_doE_cons (_doE_bind p t) (_doE_final e))"
      \<rightleftharpoons> "CONST bind_doE t (\<lambda>p. e)"
    "_doE_block (_doE_cons (_doE_let p t) bs)"
      \<rightleftharpoons> "let p = t in _doE_block bs"
    "_doE_block (_doE_cons b (_doE_cons c cs))"
      \<rightleftharpoons> "_doE_block (_doE_cons b (_doE_final (_doE_block (_doE_cons c cs))))"
    "_doE_cons (_doE_let p t) (_doE_final s)"
      \<rightleftharpoons> "_doE_final (let p = t in s)"
    "_doE_block (_doE_final e)" \<rightharpoonup> "e"
    "(m \<then> n)" \<rightharpoonup> "(CONST bind_doE m (\<lambda>_. n))"




  lemma xrm_monad_laws[simp]:
    "doE {x \<leftarrow> sreturn y; f x} = f y"
    "doE {x \<leftarrow> m; sreturn x} = m"
    "doE {x\<leftarrow>(doE {y\<leftarrow>m; f y}); g x } = doE {y\<leftarrow>m; x\<leftarrow>f y; g x}"

    "doE {sfail; m} = sfail"
    "doE {_\<leftarrow>m; sfail} = sfail"

    "doE {s\<leftarrow>sget; sput s} = sreturn ()"
    "doE {sput s1; sput s2} = sput s2"
    "doE {sput s; sget} = doE {sput s; sreturn s}"

    unfolding sreturn_def sbind_def sfail_def sget_def sput_def
    by (auto split: option.splits)


  lemma sbind_split: "P (sbind m f s) \<longleftrightarrow> (m s = None \<longrightarrow> P None) \<and> (\<forall>r s'. m s = Some (r,s') \<longrightarrow> P (f r s'))"
    by (auto simp: sbind_def split: option.split)

  lemma sbind_split_asm: "P (sbind m f s)
    \<longleftrightarrow> \<not> ((m s = None \<and> \<not> P None) \<or> (\<exists>r s'. m s = Some (r,s') \<and> \<not> P (f r s')))"
    by (auto simp: sbind_def split: option.split)

  lemmas sbind_splits = sbind_split sbind_split_asm




  definition se_ord :: "('a,'s) se \<Rightarrow> _" where "se_ord \<equiv> fun_ord (flat_ord None)"
  definition se_lub :: "('a,'s) se set \<Rightarrow> _" where "se_lub \<equiv> fun_lub (flat_lub None)"

  abbreviation "mono_se \<equiv> monotone (fun_ord se_ord) se_ord"

  interpretation se_monad: partial_function_definitions se_ord se_lub
    unfolding se_ord_def se_lub_def
    apply (rule partial_function_lift)
    by standard

  declaration \<open>Partial_Function.init "se_monad" @{term se_monad.fixp_fun}
    @{term se_monad.mono_body} @{thm se_monad.fixp_rule_uc} @{thm se_monad.fixp_induct_uc}
    ( (*SOME @{thm fixp_induct_option}*) NONE )\<close> (* TODO: Induction rule! *)


  lemma sebind_mono[partial_function_mono]:
    assumes mf: "mono_se B" and mg: "\<And>y. mono_se (\<lambda>f. C y f)"
    shows "mono_se (\<lambda>f. sbind (B f) (\<lambda>y. C y f))"
    apply (rule monotoneI)
    using monotoneD[OF mf] monotoneD[OF mg]
    unfolding se_ord_def flat_ord_def fun_ord_def
    apply (auto split: sbind_splits dest: )
    apply (metis option.simps(3))
    by (metis fst_conv option.sel option.simps(3) snd_conv)





  definition "sassert \<Phi> \<equiv> if \<Phi> then sreturn () else sfail"

  lemma xassert_simps[simp]:
    "sassert True = sreturn ()"
    "sassert False = sfail"
    by (auto simp: sassert_def)

  lemma sfail_eq_conv[simp]:
    "sfail s = None"
    by (auto simp: sfail_def)

  lemma sreturn_eq_conv[simp]:
    "sreturn x s = Some (x,s)"
    by (auto simp: sreturn_def)

  lemma sget_eq_conv[simp]:
    "sget s = Some (s,s)"
    by (auto simp: sget_def)

  lemma xput_eq_conv[simp]:
    "sput s ss = Some ((),s)"
    by (auto simp: sput_def)

  lemma sassert_eq_conv[simp]:
    "sassert \<Phi> s = Some us \<longleftrightarrow> us=((),s) \<and> \<Phi>"
    "sassert \<Phi> s = None \<longleftrightarrow> \<not>\<Phi>"
    by (auto simp: sassert_def)



  definition wps :: "('a,'s) se \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool" where
    "wps c Q s = (case c s of Some (x,s) \<Rightarrow> Q x s | None \<Rightarrow> False)"

  named_theorems wps_iffs \<open>Equality laws for weakest precondition (also used to generate intro-rules)\<close>
  named_theorems wps_simps \<open>Equality laws for weakest precondition\<close>
  named_theorems wps_intros \<open>Introduction rules for weakest precondition\<close>

  local_setup \<open>
    let
      fun get_wps_eqs ctxt =
          Named_Theorems.get ctxt @{named_theorems wps_iffs}
        @ Named_Theorems.get ctxt @{named_theorems wps_simps}

      fun get_wps_rls ctxt =
          Named_Theorems.get ctxt @{named_theorems wps_intros}
        @ map (fn thm => thm RS @{thm iffD2}) (Named_Theorems.get ctxt @{named_theorems wps_iffs})
    in
      I
      #> Local_Theory.add_thms_dynamic (@{binding wps_rls}, get_wps_rls o Context.proof_of)
      #> Local_Theory.add_thms_dynamic (@{binding wps_eqs}, get_wps_eqs o Context.proof_of)
    end
  \<close>


  lemma wps_basic_eq[wps_iffs]:
    "\<And>Q E x s. wps (sreturn x) Q s = Q x s"
    "\<And>Q E s. wps (sfail) Q s = False"
    "\<And>Q E s. wps (sget) Q s = Q s s"
    "\<And>Q E r s. wps (sput r) Q s = Q () r"
    "\<And>m f Q E s. wps (doE {x\<leftarrow>m; f x}) Q s = wps m (\<lambda>x. wps (f x) Q) s"
    unfolding wps_def
    by (auto split: sbind_splits option.splits)

  lemma wps_assert_eq[wps_iffs]:
    "wps (sassert \<Phi>) Q s \<longleftrightarrow> \<Phi> \<and> Q () s"
    unfolding wps_def by (auto split: option.splits)

  lemma
    wps_if_eq[wps_simps]: "wps (if b then t else e) Q s = (if b then wps t Q s else wps e Q s)"
    and wps_ifI[wps_intros]: "\<lbrakk> b \<Longrightarrow> wps t Q s; \<not>b \<Longrightarrow> wps e Q s \<rbrakk> \<Longrightarrow> wps (if b then t else e) Q s"
    and wps_if_eq': "wps (if b then t else e) Q = (if b then wps t Q else wps e Q)"
    by auto

  lemma wps_mono': "Q\<le>Q' \<Longrightarrow> wps c Q \<le> wps c Q'"
    unfolding wps_def by (auto split: option.splits)

  lemma wps_mono:
    assumes "wps c Q s"
    assumes "\<And>r s. Q r s \<Longrightarrow> Q' r s"
    shows "wps c Q' s"
    using wps_mono'[of Q Q' c] assms
    by (auto)


  definition sexec :: "('a,'s) se \<Rightarrow> 's \<Rightarrow> ('a\<times>'s,'t) se" where
    "sexec f s \<equiv> case f s of Some (a,s) \<Rightarrow> sreturn (a,s) | None \<Rightarrow> sfail"

  lemma wps_sexec_eq[wps_iffs]:
    "wps (sexec f s) Q t = wps f (\<lambda>a s. Q (a,s) t) s"
    by (auto simp: sexec_def wps_def split: option.splits)

  definition lift :: "'a option \<Rightarrow> ('a,'s) se" where
    "lift m \<equiv> case m of None \<Rightarrow> sfail | Some x \<Rightarrow> sreturn x"

  definition use :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a,'s) se" where
    "use L \<equiv> doE { s \<leftarrow> sget; r\<leftarrow>lift (get L s); sreturn r }"

  definition modify :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> (unit,'s) se"
    (infix "%=" 50) where
    "L %= f \<equiv> doE { s \<leftarrow> sget; x \<leftarrow> lift (get L s); s \<leftarrow> lift (put L (f x) s); sput s }"

  definition modifyM :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a \<Rightarrow> ('a,'s) se) \<Rightarrow> (unit,'s) se"
    (infix "%^=" 50) where
    "L %^= f \<equiv> doE {
      s \<leftarrow> sget;
      x \<leftarrow> lift (get L s);
      x \<leftarrow> f x;
      s \<leftarrow> lift (put L x s);
      sput s
    }"

  definition assign :: "('a \<Longrightarrow> 's) \<Rightarrow> 'a \<Rightarrow> (unit,'s) se"
    (infix "::=" 50) where
    "L ::= x \<equiv> doE { s \<leftarrow> sget; s \<leftarrow> lift (put L x s); sput s }"

  definition assignM (infix "::^=" 50) where
    "L ::^= x \<equiv> doE { x\<leftarrow>x; L ::= x }"


  schematic_goal [simp]: "(lift f) s = ?s"
    unfolding lift_def by simp

  schematic_goal [simp]: "(use L) s = ?s"
    unfolding use_def by simp

  schematic_goal [simp]: "(x%=f) s = ?s"
    unfolding modify_def by simp

  schematic_goal [simp]: "(x%^=f) s = ?s"
    unfolding modifyM_def by simp

  schematic_goal [simp]: "(x::=v) s = ?s"
    unfolding assign_def by simp

  schematic_goal [simp]: "(x::^=m) s = ?s"
    unfolding assignM_def by simp

  lemma wps_use_eq:
    assumes "lens L"
    assumes "pre_get L s"
    shows "wps (use L) Q s \<longleftrightarrow> Q (get' L s) s"
    using assms by (auto simp: wps_def split: sbind_splits option.splits)

  lemma wps_upd_eq:
    assumes "lens L"
    assumes "pre_get L s"
    shows "wps (L %= f) Q s \<longleftrightarrow> Q () (put' L (f (get' L s)) s)"
    using assms by (auto simp: wps_def split: sbind_splits option.splits)

  lemma wps_assign_eq:
    assumes "lens L"
    assumes "pre_put L s"
    shows "wps (L ::= x) Q s \<longleftrightarrow> Q () (put' L x s)"
    using assms by (auto simp: wps_def split: sbind_splits option.splits)



  abbreviation lens_comp_bwd (infixr "\<bullet>" 90) where "a\<bullet>b \<equiv> b;\<^sub>La"
  abbreviation idx_lens_comp ("_[_]\<^sub>L" [100,100] 100) where "l[i]\<^sub>L \<equiv> l \<bullet> idx\<^sub>L i"
  abbreviation fun_lens_comp ("_'(_')\<^sub>L" [100,100] 100) where "f(x)\<^sub>L \<equiv> f \<bullet> fun\<^sub>L x"






  section \<open>Tests and Examples\<close>


  context begin

    private definition "test1 \<equiv> doE {
      let x = id\<^sub>L;
      let i = 2;
      idx\<^sub>L i \<bullet>fst\<^sub>L ::= 41;
      x[i]\<^sub>L\<bullet>fst\<^sub>L ::= 42;
      l \<leftarrow> use x;
      sreturn (l!i)
    }"

    private lemma "test1 = doE {
      t \<leftarrow> use (id\<^sub>L[2]\<^sub>L);
      id\<^sub>L[2]\<^sub>L\<bullet>fst\<^sub>L ::= 42;
      sreturn (42, snd t)
    }"
      apply (rule ext)
      by (auto simp: test1_def split: sbind_splits option.splits)

    value "test1 [(1::nat,2::nat),(n,4),(5,6)]"
    qualified definition "Monad3_test_foo n \<equiv>
      test1 [(1::nat,2::nat),(n,4),(5,6)]"

    code_thms SE_Monad.Monad3_test_foo
    value [simp] "Monad3_test_foo 3"

    export_code SE_Monad.Monad3_test_foo checking SML

    ML_val \<open>
      @{code SE_Monad.Monad3_test_foo} (@{code nat_of_integer} 2)
    \<close>

    term "f(x)\<^sub>L \<bullet> the\<^sub>L"

    private definition "test2 \<equiv> doE {
      let db=id\<^sub>L;
      db(''Hello'')\<^sub>L\<bullet>the\<^sub>L\<bullet>snd\<^sub>L %= (+) (5::nat);
      db(''Hello'')\<^sub>L\<bullet>the\<^sub>L\<bullet>fst\<^sub>L ::= (''World'');

      r \<leftarrow> use (db(''Hello'')\<^sub>L \<bullet> the\<^sub>L   );
      sreturn r
    }"

    value "test2 [''Hello'' \<mapsto> (''x'',3::nat)]"

    private definition "test3 \<equiv> doE {
      let db=id\<^sub>L;
      db(''Hello'')\<^sub>L\<bullet>crov\<^sub>L ::= ''World'';
      r \<leftarrow> use (db(''Hello'')\<^sub>L \<bullet> the\<^sub>L );
      sreturn r
    }"

    value "test3 Map.empty"
    (* the.snd.lookup("Hello")   *)

    value "get' (the\<^sub>L \<bullet> snd\<^sub>L \<bullet> fun\<^sub>L ''Hello'') (test3 Map.empty)"


    private datatype 'a test = A (xcord: nat) (ycord: 'a) | B (name: string) | C bool bool int

    private define_lenses test

    value [code] "put' ycord\<^sub>L ''bar'' (A 3 ''foo'')"
  end







end
