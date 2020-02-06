theory Det_Step
  imports Main "HOL-Eisbach.Eisbach"
begin

text {*
  Logical operators over predicates.
*}
definition pred_AND :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool)" (infixr "&&" 35)
  where "pred_AND p0 p1 s \<equiv> p0 s \<and> p1 s"

definition pred_OR :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool)" (infixr "||" 30)
  where "pred_OR p0 p1 s \<equiv> p0 s \<or> p1 s"

definition pred_NOT :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool)" ("! _" [40] 40)
  where "pred_NOT p0 s \<equiv> \<not>p0 s"

definition pred_IMP :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool" (infixr "\<longmapsto>" 25)
  where "pred_IMP p0 p1 s \<equiv> p0 s \<longrightarrow> p1 s"

definition pred_True :: "('s \<Rightarrow> bool) \<Rightarrow> bool" ("\<turnstile> _ "[25] 25)
  where "pred_True p0 \<equiv> \<forall> s . p0 s"


lemmas pred_logic = pred_AND_def pred_OR_def pred_NOT_def pred_IMP_def pred_True_def

text {*
  Composition: two transition relations are composed by an intermediate state $\sigma''$.
*}
definition seq :: "('\<sigma> \<Rightarrow> '\<sigma> \<Rightarrow> bool) \<Rightarrow> ('\<sigma> \<Rightarrow> '\<sigma> \<Rightarrow> bool) \<Rightarrow> ('\<sigma> \<Rightarrow> '\<sigma> \<Rightarrow> bool)" (infixr ";" 70)
  where "(a ; b) \<sigma> \<sigma>'' \<equiv> \<exists> \<sigma>' . a \<sigma> \<sigma>' \<and> b \<sigma>' \<sigma>''"

text {*
  Skip. Use for if-then-else without else.
*}
definition skip :: "'\<sigma> \<Rightarrow> '\<sigma> \<Rightarrow> bool"
  where "skip \<equiv> (=)"


text {* If-then-else 
*}
inductive if_pred :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> ('\<sigma> \<Rightarrow> '\<sigma> \<Rightarrow> bool) \<Rightarrow> ('\<sigma> \<Rightarrow> '\<sigma> \<Rightarrow> bool) \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma> \<Rightarrow> bool"
  where "B \<sigma> \<Longrightarrow> b0 \<sigma> \<sigma>' \<Longrightarrow> if_pred B b0 b1 \<sigma> \<sigma>'"
  | "\<not>B \<sigma> \<Longrightarrow> b1 \<sigma> \<sigma>' \<Longrightarrow> if_pred B b0 b1 \<sigma> \<sigma>'"

abbreviation if_pred_syntax ("IF _ THEN _ ELSE _ FI")
  where "IF B THEN b0 ELSE b1 FI \<equiv> if_pred B b0 b1"

abbreviation if2_pred_syntax ("IF _ THEN _ FI")
  where "IF B THEN b0 FI \<equiv> if_pred B b0 skip"


text {*
  While. Standard big-step semantics.
*}
inductive while_pred :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> ('\<sigma> \<Rightarrow> '\<sigma> \<Rightarrow> bool) \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma> \<Rightarrow> bool"
  where "\<not>B \<sigma> \<Longrightarrow> while_pred B body \<sigma> \<sigma>"
  | "B \<sigma> \<Longrightarrow> body \<sigma> \<sigma>' \<Longrightarrow> while_pred B body \<sigma>' \<sigma>'' \<Longrightarrow> while_pred B body \<sigma> \<sigma>''"

abbreviation while_pred_syntax ("WHILE _ DO _ OD")
  where "WHILE B DO body OD \<equiv> while_pred B body"

text {*
  While v2. 
*}
inductive while2_pred :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> ('\<sigma> \<Rightarrow> '\<sigma> \<Rightarrow> bool) \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma> \<Rightarrow> bool"
  where "body \<sigma> \<sigma>' \<Longrightarrow> \<not>B \<sigma>' \<Longrightarrow> while2_pred B body \<sigma> \<sigma>'"
  | "body \<sigma> \<sigma>' \<Longrightarrow> B \<sigma>' \<Longrightarrow> while_pred B body \<sigma>' \<sigma>'' \<Longrightarrow> while2_pred B body \<sigma> \<sigma>''"

abbreviation while2_pred_syntax ("DO _ WHILE _ OD")
  where "DO body WHILE B OD \<equiv> while2_pred B body"


text {*
  Call. Takes a function whose execution requires a locale state $\sigma_L$ and the state of the
  caller $\sigma_C$. It executes that function with an undefined initial local state.
  After execution, the resulting local state is disregarded.
  This preserves determinism, as long as the initial local state is irrelevant for execution of
  the function.
*}
definition get_local_state_part :: "'a \<times> 'b \<Rightarrow> 'a" ("\<L> _" [50] 50)
  where "get_local_state_part \<equiv> fst"

definition get_caller_state_part :: "'a \<times> 'b \<Rightarrow> 'b" ("\<C> _" [60] 60)
  where "get_caller_state_part \<equiv> snd"

declare get_local_state_part_def[simp add]
declare get_caller_state_part_def[simp add]


definition call :: "('\<sigma>\<^sub>L \<times> '\<sigma>\<^sub>C \<Rightarrow> '\<sigma>\<^sub>L \<times> '\<sigma>\<^sub>C \<Rightarrow> bool) \<Rightarrow> ('\<sigma>\<^sub>C \<times> '\<sigma>\<^sub>C\<^sub>C) \<Rightarrow> ('\<sigma>\<^sub>C \<times> '\<sigma>\<^sub>C\<^sub>C) \<Rightarrow> bool"
  where "call f \<sigma>\<^sub>C \<sigma>'\<^sub>C \<equiv> \<exists> \<sigma>\<^sub>L \<sigma>'\<^sub>L . f (\<sigma>\<^sub>L, \<L> \<sigma>\<^sub>C) (\<sigma>'\<^sub>L, \<L> \<sigma>'\<^sub>C) \<and> (\<C> \<sigma>'\<^sub>C) = (\<C> \<sigma>'\<^sub>C)"

definition call\<^sub>1 :: "('a \<Rightarrow> '\<sigma>\<^sub>L \<times> '\<sigma>\<^sub>C \<Rightarrow> '\<sigma>\<^sub>L \<times> '\<sigma>\<^sub>C \<Rightarrow> bool) \<Rightarrow> ('\<sigma>\<^sub>C \<Rightarrow> 'a) \<Rightarrow> ('\<sigma>\<^sub>C \<times> '\<sigma>\<^sub>C\<^sub>C) \<Rightarrow> ('\<sigma>\<^sub>C \<times> '\<sigma>\<^sub>C\<^sub>C) \<Rightarrow> bool"
  where "call\<^sub>1 f p1 \<sigma>\<^sub>C \<sigma>'\<^sub>C \<equiv> \<exists> \<sigma>\<^sub>L \<sigma>'\<^sub>L . f (p1 (\<L> \<sigma>\<^sub>C)) (\<sigma>\<^sub>L, \<L> \<sigma>\<^sub>C) (\<sigma>'\<^sub>L, \<L> \<sigma>'\<^sub>C)"

definition call\<^sub>2 :: "('a \<Rightarrow> 'b \<Rightarrow> '\<sigma>\<^sub>L \<times> '\<sigma>\<^sub>C \<Rightarrow> '\<sigma>\<^sub>L \<times> '\<sigma>\<^sub>C \<Rightarrow> bool) \<Rightarrow> ('\<sigma>\<^sub>C \<Rightarrow> 'a) \<Rightarrow> ('\<sigma>\<^sub>C \<Rightarrow> 'b) \<Rightarrow> ('\<sigma>\<^sub>C \<times> '\<sigma>\<^sub>C\<^sub>C) \<Rightarrow> ('\<sigma>\<^sub>C \<times> '\<sigma>\<^sub>C\<^sub>C) \<Rightarrow> bool"
  where "call\<^sub>2 f p1 p2 \<sigma>\<^sub>C \<sigma>'\<^sub>C \<equiv> \<exists> \<sigma>\<^sub>L \<sigma>'\<^sub>L . f (p1 (\<L> \<sigma>\<^sub>C)) (p2 (\<L> \<sigma>\<^sub>C)) (\<sigma>\<^sub>L, \<L> \<sigma>\<^sub>C) (\<sigma>'\<^sub>L, \<L> \<sigma>'\<^sub>C)"






text {*
Hoare logic 
*}
definition Valid :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> ('\<sigma> \<Rightarrow> '\<sigma> \<Rightarrow> bool) \<Rightarrow> ('\<sigma> \<Rightarrow> bool) \<Rightarrow> bool" ("{_} _ {_}")
  where "{P} c {Q} \<equiv> \<forall> s s'. c s s' \<longrightarrow> P s \<longrightarrow> Q s'"

lemma SkipRule: "\<turnstile> P \<longmapsto> Q \<Longrightarrow> {P} skip {Q}"
  by (auto simp: Valid_def skip_def pred_logic)

lemma BasicRule: "(\<And> s s' . P s \<Longrightarrow> f s s' \<Longrightarrow> Q s') \<Longrightarrow> {P} f {Q}"
  by (auto simp: Valid_def)

lemma SeqRule: "{P} f {Q} \<Longrightarrow> {Q} g {R} \<Longrightarrow> {P} (f;g) {R}"
  by (auto simp: Valid_def seq_def)

lemma WhileRule:
  assumes "\<turnstile> P \<longmapsto> I"
      and "\<turnstile> I && (!B) \<longmapsto> Q"
      and "{I && B} body {I}"
    shows "{P} (WHILE B DO body OD) {Q}"
proof-
  {
    fix \<sigma> \<sigma>'
    assume "(WHILE B DO body OD) \<sigma> \<sigma>'"
      and "I \<sigma>"
    hence "Q \<sigma>'"
      using assms
    proof(induct rule: while_pred.induct)
      case (1 B \<sigma> body)
      thus ?case
        by (auto simp add: pred_logic)
    next
      case (2 B \<sigma> body \<sigma>' \<sigma>'')
      thus ?case
        by (auto simp add: Valid_def pred_logic)
    qed
  }
  thus ?thesis
    using assms(1)
    by (auto simp add: Valid_def pred_logic)
qed

lemma While2Rule:
  assumes "\<turnstile> I && (!B) \<longmapsto> Q"
      and "{P} body {I}"
      and "{I && B} body {I}"
    shows "{P} (DO body WHILE B OD) {Q}"
proof-
  {
    fix \<sigma> \<sigma>'
    assume "(DO body WHILE B OD) \<sigma> \<sigma>'"
       and "P \<sigma>"
    hence "Q \<sigma>'"
      using assms
    proof(induct rule: while2_pred.induct)
      case (1 body \<sigma> \<sigma>' B)
      then show ?case 
        by (auto simp add: pred_logic Valid_def)
    next
      case (2 body \<sigma> \<sigma>' B \<sigma>'')
      thus ?case
        using WhileRule[OF _ 2(5,7),of I] 
        by (auto simp add: pred_logic Valid_def)
    qed
  }
  thus ?thesis
    by (auto simp add: Valid_def pred_logic)
qed

lemma CallRule: 
  assumes "{\<lambda> (\<sigma>\<^sub>L, \<sigma>\<^sub>C) . P' \<sigma>\<^sub>C} f {\<lambda> (\<sigma>'\<^sub>L, \<sigma>'\<^sub>C) . Q' \<sigma>'\<^sub>C}"
    and "\<forall> \<sigma> . P \<sigma> \<longrightarrow> P' (fst \<sigma>)"
    and "\<forall> \<sigma> . Q' (fst \<sigma>) \<longrightarrow> Q \<sigma>"
  shows "{P} call f {Q}"
proof-
  {
    fix \<sigma>\<^sub>C \<sigma>'\<^sub>C
    assume P: "P \<sigma>\<^sub>C"
       and "call f \<sigma>\<^sub>C \<sigma>'\<^sub>C"
    then obtain \<sigma>\<^sub>L \<sigma>'\<^sub>L where loc: "f (\<sigma>\<^sub>L, fst \<sigma>\<^sub>C) (\<sigma>'\<^sub>L, fst \<sigma>'\<^sub>C)"
      unfolding call_def
      by auto
    hence "Q' (fst \<sigma>'\<^sub>C)"
      using P assms(1)[unfolded Valid_def] assms(2)
      by (auto simp add: assms(2))
    hence "Q \<sigma>'\<^sub>C"
      using assms(3)
      by blast
  }
  thus ?thesis
    unfolding Valid_def
    by auto
qed


lemma temp: "
 { \<lambda> \<sigma> . \<sigma> i < (n::nat)}
  WHILE (\<lambda> \<sigma> . \<sigma> i < n) DO
        (\<lambda> \<sigma> \<sigma>' . \<sigma>' i = \<sigma> i + 1)
  OD
 { \<lambda> \<sigma> . \<sigma> i = n }"
  apply (rule WhileRule[where I =  "\<lambda> \<sigma> . \<sigma> i \<le> n"])
  apply (simp add: pred_logic)
  apply (simp add: pred_logic)
  apply (rule BasicRule)
  apply (simp add: pred_logic)
  oops

lemma temp: "
 { \<lambda> \<sigma> . \<sigma> x = 3}
  (\<lambda> \<sigma> \<sigma>' . \<sigma>' x = \<sigma> x) ;
  (\<lambda> \<sigma> \<sigma>' . \<sigma>' y = \<sigma> x)
 { \<lambda> \<sigma> . \<sigma> y = 3 }"
  apply (rule SeqRule[where Q = "\<lambda> \<sigma> . \<sigma> x = 3"])
  apply (rule BasicRule)
  apply simp
  apply (rule BasicRule)
  apply simp
  oops




text {*
  Introduces a deterministic step function, where each state has a location.
*}
locale det_step =
  fixes step :: "'s \<Rightarrow> 's"
    and loc :: "'s \<Rightarrow> 'loc"
begin

text {*
  A fix-point definition of running until some predicate P is satisfied.
  This prevents the need for a termination proof.
*}
inductive run_until_pred :: "('s \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool"
  where "P \<sigma> \<Longrightarrow> run_until_pred P \<sigma> \<sigma>"
  | "\<not>P \<sigma> \<Longrightarrow> run_until_pred P (step \<sigma>) \<sigma>' \<Longrightarrow> run_until_pred P \<sigma> \<sigma>'"

definition terminates 
  where "terminates P \<sigma> \<equiv> Ex (run_until_pred P \<sigma>)"

definition run_until :: "('s \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> 's option"
  where "run_until P \<sigma> \<equiv> if terminates P \<sigma> then Some (THE \<sigma>' . run_until_pred P \<sigma> \<sigma>') else None"

definition at_loc :: "'loc \<Rightarrow> 's \<Rightarrow> bool"
  where "at_loc l \<sigma> \<equiv> loc \<sigma> = l"

lemma deterministic:
  shows "run_until P \<sigma> = Some \<sigma>' \<longleftrightarrow> run_until_pred P \<sigma> \<sigma>'"
proof-
  have "\<And> x y . run_until_pred P \<sigma> x \<Longrightarrow> run_until_pred P \<sigma> y \<Longrightarrow> x = y"
  proof-
    fix x y
    show "run_until_pred P \<sigma> x \<Longrightarrow> run_until_pred P \<sigma> y \<Longrightarrow> x = y"
    proof(induct rule: run_until_pred.induct)
    case (1 P \<sigma>)
    thus ?case
      using run_until_pred.cases by blast
    next
    case (2 P \<sigma> \<sigma>')
    thus ?case
      using run_until_pred.cases by blast
    qed
  qed
  thus ?thesis
    unfolding run_until_def terminates_def
    apply auto
    apply (rule theI')
    by auto
qed



text {*
  A path is non-empty list of states connected by the step function.
  Each state (but the last) does not satisfy predicate P.
*}
fun is_path :: "('s \<Rightarrow> bool) \<Rightarrow> 's list \<Rightarrow> bool"
  where "is_path P [] = False"
  | "is_path P [s] = True"
  | "is_path P (s#s'#path) = (s' = step s \<and> \<not> P s \<and> is_path P (s'#path))"

lemma run_until_pred_as_path:
  shows "run_until_pred P \<sigma> \<sigma>' \<longleftrightarrow> (\<exists> \<pi> . is_path P \<pi> \<and> hd \<pi> = \<sigma> \<and> last \<pi> = \<sigma>' \<and> P \<sigma>')"
proof-
  {
    assume "run_until_pred P \<sigma> \<sigma>'"
    hence "\<exists> \<pi> . is_path P \<pi> \<and> hd \<pi> = \<sigma> \<and> last \<pi> = \<sigma>'\<and> P (last \<pi>)"
    proof(induct rule: run_until_pred.induct)
      case (1 P \<sigma>)
      hence "is_path P [\<sigma>] \<and> hd [\<sigma>] = \<sigma> \<and> last [\<sigma>] = \<sigma> \<and> P \<sigma>"
        by auto
      thus ?case
        by metis
    next
      case (2 P \<sigma> \<sigma>')
      then obtain \<pi> where "is_path P \<pi> \<and> hd \<pi> = step \<sigma> \<and> last \<pi> = \<sigma>' \<and> P \<sigma>'"
        by auto
      hence "is_path P (\<sigma>#\<pi>) \<and> hd (\<sigma>#\<pi>) = \<sigma> \<and> last (\<sigma>#\<pi>) = \<sigma>' \<and> P \<sigma>'"
        using 2(1)
        by (cases \<pi>,auto split: if_split_asm)
      thus ?case
        by metis
    qed
  }
  moreover
  {
    assume "\<exists> \<pi> . is_path P \<pi> \<and> hd \<pi> = \<sigma> \<and> last \<pi> = \<sigma>' \<and> P \<sigma>'"
    then obtain \<pi> where "is_path P \<pi> \<and> hd \<pi> = \<sigma> \<and> last \<pi> = \<sigma>' \<and> P \<sigma>'"
      by auto
    hence "run_until_pred P \<sigma> \<sigma>'"
    proof(induct \<pi> arbitrary: \<sigma>)
      case Nil
      thus ?case
        by auto
    next
      case (Cons a \<pi>)
      show ?case
        using Cons(1)[of "hd \<pi>"] Cons(2-)
        by (cases \<pi>,auto simp add: run_until_pred.intros)
    qed
  }
  ultimately
  show ?thesis
    by auto
qed
    
lemma is_path_append:
  shows "is_path P (\<pi>0 @ \<pi>1) = (if \<pi>0 = [] then is_path P \<pi>1
                                else if \<pi>1 = [] then is_path P \<pi>0
                                else is_path P \<pi>0 \<and> is_path P \<pi>1 \<and> (hd \<pi>1 = step (last \<pi>0)) \<and> \<not>P(last \<pi>0))"
proof(induct \<pi>0 arbitrary: \<pi>1)
  case Nil
  thus ?case
    by auto
next
  case (Cons s \<pi>0)
  show ?case
    using Cons(1)[of \<pi>1]
    by (cases \<pi>1; cases \<pi>0; auto split: if_split_asm)
qed

lemma is_path_pred_OR:
  assumes "is_path (P0 || P1) \<pi>"
  shows "is_path P1 \<pi>"
  using assms
proof(induct \<pi>)
  case Nil
  thus ?case
    by auto
next
  case (Cons a \<pi>)
  thus ?case
    by (cases \<pi>,auto simp add: pred_OR_def)
qed


lemma is_path_drop:
  assumes "is_path P \<pi>"
      and "n < length \<pi>"
  shows "is_path P (drop n \<pi>)"
  using assms
proof(induct n arbitrary: \<pi>)
  case 0
  thus ?case by auto
next
  case (Suc n)
  thus ?case 
    by (cases \<pi>;cases "tl \<pi>";auto)
qed

lemma two_paths_same_start:
  assumes "is_path (P0 || P1) \<pi>\<^sub>0"
      and "is_path P1 \<pi>\<^sub>1"
      and "hd \<pi>\<^sub>0 = hd \<pi>\<^sub>1"
      and "P1 (last \<pi>\<^sub>1)"
    shows "\<pi>\<^sub>0 = take (length \<pi>\<^sub>0) \<pi>\<^sub>1"
  using assms
proof(induct \<pi>\<^sub>0 arbitrary: \<pi>\<^sub>1)
  case Nil
  thus ?case
    by auto
next
  case (Cons a \<pi>\<^sub>0)
  note 0 = this
  have 1: "\<pi>\<^sub>1 \<noteq> [] \<and> hd \<pi>\<^sub>1 = a"
    using 0
    by auto
  show ?case
  proof(cases \<pi>\<^sub>0)
    case Nil
    thus ?thesis
      using Cons
      by (cases \<pi>\<^sub>1,auto)
  next
    case (Cons s \<pi>\<^sub>0')
    note 2 = this
    show ?thesis
    proof(cases \<pi>\<^sub>1)
      case Nil
      thus ?thesis
        using 0 1 2 
        by auto
    next
      case (Cons s' \<pi>\<^sub>1')
      have 3: "is_path (P0 || P1) \<pi>\<^sub>0"
        using 0(2) 2
        by auto
      have 4: "is_path P1 \<pi>\<^sub>1'"
        using Cons 0(3) 1 2 0(5) 0(2)
        by (cases \<pi>\<^sub>1;cases \<pi>\<^sub>1';auto simp add: pred_OR_def)
      have "step a = hd \<pi>\<^sub>0"
        using 0(2) 2
        by auto
      moreover
      have "step a = hd \<pi>\<^sub>1'"
        using 0 1 2 Cons
        by (cases \<pi>\<^sub>1;cases \<pi>\<^sub>1';auto simp add: pred_OR_def)
      ultimately
      have 5: "hd \<pi>\<^sub>0 = hd \<pi>\<^sub>1'"
        by auto
      show ?thesis
        using 1 2 Cons
        apply (auto)
        using 0(1)[of \<pi>\<^sub>1',OF 3 4 5] 1 2 3 0
        by (cases \<pi>\<^sub>1;cases \<pi>\<^sub>1';auto simp add: pred_OR_def)
    qed
  qed
qed

lemma exists_path_pred_OR:
  assumes "is_path P1 \<pi>"
      and "P1 (last \<pi>)"
  shows "\<exists> \<pi>' . is_path (P0 || P1) \<pi>' \<and> hd \<pi>' = hd \<pi> \<and> (P0 || P1) (last \<pi>')"
  using assms
proof(induct \<pi>)
  case Nil
  thus ?case by auto
next
  case (Cons a \<pi>)
  have 1: "P1 a \<Longrightarrow> is_path (P0 || P1) [a] \<and> hd [a] = a \<and> (P0 || P1) (last [a])"
    by (auto simp add: pred_OR_def)
  show ?case 
    using Cons
    apply (cases \<pi>,auto split: if_split_asm)
    using 1
    apply metis
    apply (metis det_step.is_path.simps(2) is_path.simps(3) last_ConsL list.sel(1) local.Cons(3) pred_OR_def)
    by (metis det_step.is_path.simps(2) det_step.is_path.simps(3) is_path.simps(1) last_ConsL last_ConsR list.exhaust_sel list.sel(1))
qed


lemma paths_with_same_start:
  assumes "hd \<pi>\<^sub>0 = hd \<pi>\<^sub>1"
      and "last \<pi>\<^sub>0 = last \<pi>\<^sub>1"
      and "P (last \<pi>\<^sub>0)"
      and "is_path P \<pi>\<^sub>0"
      and "is_path P \<pi>\<^sub>1"
    shows "\<pi>\<^sub>0 = \<pi>\<^sub>1"
  using assms
proof(induct \<pi>\<^sub>0 arbitrary: \<pi>\<^sub>1)
  case Nil
  thus ?case
    by auto
next
  case (Cons s \<pi>\<^sub>0)
  show ?case
    using Cons(1)[of "tl \<pi>\<^sub>1"] Cons(2-)
    apply (auto split: if_split_asm)
    apply (cases \<pi>\<^sub>1,auto split: if_split_asm)
    apply (metis det_step.is_path.simps(3) list.exhaust_sel)
    apply (cases \<pi>\<^sub>1,auto split: if_split_asm)
    apply (cases \<pi>\<^sub>0,auto split: if_split_asm)
    apply (cases \<pi>\<^sub>0,auto split: if_split_asm)
    apply (cases "tl \<pi>\<^sub>1",auto split: if_split_asm)
    by (cases "tl \<pi>\<^sub>1",auto split: if_split_asm)
qed

lemma paths_are_unique:
  assumes "is_path P \<pi> \<and> hd \<pi> = \<sigma> \<and> last \<pi> = \<sigma>' \<and> P \<sigma>'"
      and "is_path P \<pi>' \<and> hd \<pi>' = \<sigma> \<and> last \<pi>' = \<sigma>' \<and> P \<sigma>'"
    shows "\<pi> = \<pi>'"
  using assms
proof(induct \<pi> arbitrary: \<pi>')
case Nil
  thus ?case
    by auto
next
  case (Cons a \<pi>)
  show ?case
    using Cons(1)[of "tl \<pi>'"] Cons(2-)
    apply (cases \<pi>';auto split: if_split_asm)
    apply (cases "tl \<pi>'";auto split: if_split_asm)
    apply (cases \<pi>;auto split: if_split_asm)
    apply (cases \<pi>;auto split: if_split_asm)
    apply (cases "tl \<pi>";auto split: if_split_asm)
    apply (cases "tl \<pi>'";auto split: if_split_asm)
    apply (metis (full_types) det_step.is_path.simps(3) list.exhaust)
    by (metis Cons.prems(2) list.inject local.Cons(2) paths_with_same_start)
qed



lemma run_until_pred_step:
  assumes "\<not>P \<sigma>"
    shows "run_until_pred P (step \<sigma>) = run_until_pred P \<sigma>"
proof-
  {
    fix \<sigma>'
    assume "run_until_pred P \<sigma> \<sigma>'"
    then obtain \<pi> where \<pi>: "is_path P \<pi> \<and> hd \<pi> = \<sigma> \<and> last \<pi> = \<sigma>' \<and> P \<sigma>'"
      by (auto simp add: run_until_pred_as_path)
    hence "is_path P (tl \<pi>) \<and> hd (tl \<pi>) = step \<sigma> \<and> last (tl \<pi>) = \<sigma>' \<and> P \<sigma>'"
      using assms(1)
      apply (cases \<pi>;auto split: if_split_asm)
      by (cases "tl \<pi>";auto split: if_split_asm)+
    hence "run_until_pred P (step \<sigma>) \<sigma>'"
      by (auto simp add: run_until_pred_as_path)
  }
  thus ?thesis
    using assms
    by (auto simp add: run_until_pred.intros)
qed

lemma run_until_pred_stop:
  shows "P \<sigma> \<Longrightarrow> The (run_until_pred P \<sigma>) = \<sigma>"
  by (metis det_step.deterministic option.distinct(2) option.inject run_until_def run_until_pred.intros(1))



lemma compose1:
  assumes "run_until_pred (P0 || P1) \<sigma> \<sigma>'"
      and "run_until_pred P1 \<sigma>' \<sigma>''"
    shows "run_until_pred P1 \<sigma> \<sigma>''"
proof-
  obtain \<pi>0 \<pi>1 where \<pi>0: "is_path (P0 || P1) \<pi>0 \<and> hd \<pi>0 = \<sigma> \<and> last \<pi>0 = \<sigma>' \<and> (P0 || P1) \<sigma>'"
     and \<pi>1 : "is_path P1 \<pi>1 \<and> hd \<pi>1 = \<sigma>' \<and> last \<pi>1 = \<sigma>'' \<and> P1 \<sigma>''" 
    using assms
    by (auto simp add: run_until_pred_as_path)
  hence "is_path P1 (\<pi>0 @ (tl \<pi>1)) \<and> hd (\<pi>0 @ (tl \<pi>1)) = \<sigma> \<and> last (\<pi>0 @ (tl \<pi>1)) = \<sigma>'' \<and> P1 \<sigma>''"
    using is_path_pred_OR[of P0 P1]
    apply (cases \<pi>1;auto simp add: is_path_append)
    by (cases "tl \<pi>1";auto simp add: is_path_append)+
  thus ?thesis
    apply (subst run_until_pred_as_path)
    by metis
qed

lemma compose2:
  assumes "run_until_pred (P0 || P1) \<sigma> \<sigma>''"
      and "run_until_pred P1 \<sigma> \<sigma>'"
    shows "run_until_pred P1 \<sigma>'' \<sigma>'"
proof-
  from assms(1) obtain \<pi>\<^sub>0 where \<pi>\<^sub>0: "is_path (P0 || P1) \<pi>\<^sub>0 \<and> hd \<pi>\<^sub>0 = \<sigma> \<and> last \<pi>\<^sub>0 = \<sigma>'' \<and> (P0 || P1) \<sigma>''"
    by (auto simp add: run_until_pred_as_path)
  from assms(2) obtain \<pi>\<^sub>1 where \<pi>\<^sub>1: "is_path P1 \<pi>\<^sub>1 \<and> hd \<pi>\<^sub>1 = \<sigma> \<and> last \<pi>\<^sub>1 = \<sigma>' \<and> P1 \<sigma>'"
    by (auto simp add: run_until_pred_as_path)

  have "\<exists> \<pi> . is_path P1 \<pi> \<and> hd \<pi> = \<sigma>'' \<and> last \<pi> = \<sigma>' \<and> P1 \<sigma>'"
  proof(cases "length \<pi>\<^sub>0 < length \<pi>\<^sub>1")
    case True
    let ?\<pi> = "drop (length \<pi>\<^sub>0 - 1) \<pi>\<^sub>1"
    have "is_path P1 ?\<pi> \<and> hd ?\<pi> = \<sigma>'' \<and> last ?\<pi> = \<sigma>' \<and> P1 \<sigma>'"
      using True \<pi>\<^sub>0 \<pi>\<^sub>1 two_paths_same_start[of P0 P1 \<pi>\<^sub>0 \<pi>\<^sub>1]
      apply (auto simp add: is_path_drop hd_drop_conv_nth)
      apply (subst last_conv_nth)
      apply auto
      using nth_take[of "length \<pi>\<^sub>0 - 1" "length \<pi>\<^sub>0" \<pi>\<^sub>1]
      apply (cases "\<pi>\<^sub>0")
      apply (auto)[1]
      by (metis One_nat_def Suc_diff_1 is_path.simps(1) length_greater_0_conv lessI)
    thus ?thesis
      by auto
  next
    case False
    hence 1: "\<pi>\<^sub>0 = \<pi>\<^sub>1"
      using \<pi>\<^sub>0 \<pi>\<^sub>1 two_paths_same_start[of P0 P1 \<pi>\<^sub>0 \<pi>\<^sub>1]
      by auto
    have "is_path P1 [\<sigma>''] \<and> hd [\<sigma>''] = \<sigma>'' \<and> last [\<sigma>''] = \<sigma>' \<and> P1 \<sigma>'"
      using \<pi>\<^sub>0 \<pi>\<^sub>1 1 is_path_pred_OR[of P0 P1]
      by auto
    thus ?thesis
      by metis
  qed
  thus ?thesis
    by (auto simp add: run_until_pred_as_path)
qed


lemma terminates_pred_OR:
  assumes "terminates P1 \<sigma>"
  shows "terminates (P0 || P1) \<sigma>"
proof-
  obtain \<sigma>' where "run_until_pred P1 \<sigma> \<sigma>'"
    using assms
    unfolding terminates_def
    by auto
  then obtain \<pi> where \<pi>: "is_path P1 \<pi> \<and> hd \<pi> = \<sigma> \<and> last \<pi> = \<sigma>' \<and> P1 \<sigma>'"
    by (auto simp add: run_until_pred_as_path)
  then obtain \<pi>' where "is_path (P0 || P1) \<pi>' \<and> hd \<pi>' = \<sigma> \<and> (P0 || P1) (last \<pi>')"
    using exists_path_pred_OR[of P1 \<pi> P0]
    by (auto)
  hence "run_until_pred (P0 || P1) \<sigma> (last \<pi>')"
    by (auto simp add: run_until_pred_as_path)
  thus ?thesis
    by (auto simp add: terminates_def)
qed

lemma compose:
  shows "run_until_pred P1 = run_until_pred (P0 || P1) ; run_until_pred P1"
proof-
  {
    fix \<sigma> \<sigma>'
    have "run_until_pred P1 \<sigma> \<sigma>' = seq (run_until_pred (P0 || P1)) (run_until_pred P1) \<sigma> \<sigma>'"
    proof (cases "terminates (P0 || P1) \<sigma>")
      case False
      {
        assume "run_until_pred P1 \<sigma> \<sigma>'"
        hence "terminates (P0 || P1) \<sigma>"
          using terminates_pred_OR
          apply (auto simp add: terminates_def)
          by metis
      }
      thus ?thesis
        using False
        by (auto simp add: terminates_def seq_def)
    next
      case True
      then obtain \<sigma>'' where \<sigma>'': "run_until_pred (P0 || P1) \<sigma> \<sigma>''"
        by (auto simp add: terminates_def)
      show ?thesis
          using \<sigma>'' compose1[of P0 P1] compose2[of P0 P1 \<sigma> \<sigma>'' \<sigma>']
          by (auto simp add: terminates_def seq_def)
    qed
  }
  thus ?thesis
    by auto
qed

lemma seq_assoc[simp]:
  shows "(a ; b) ;c = a;b;c"
  unfolding seq_def
  by auto


text {*
  While
*}

text {*
  This is the while as executed in assembly.
  1.) If the branching condition B does not hold, then execution resumes with whatever follows (i.e., finish).
  2.) If the termination condition P0 holds, then terminate.
  3.) Otherwise, execute the body, and iterate the while.
*}
inductive while'_pred :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool"
  where "\<not>B \<sigma> \<Longrightarrow> \<not>P0 \<sigma> \<Longrightarrow> finish \<sigma> \<sigma>' \<Longrightarrow> while'_pred P0 B body finish \<sigma> \<sigma>'"
  | "P0 \<sigma> \<Longrightarrow> while'_pred P0 B body finish \<sigma> \<sigma>"
  | "B \<sigma> \<Longrightarrow> \<not>P0 \<sigma> \<Longrightarrow> body (step \<sigma>) \<sigma>' \<Longrightarrow> while'_pred P0 B body finish \<sigma>' \<sigma>'' \<Longrightarrow> while'_pred P0 B body finish \<sigma> \<sigma>''"

lemma length_path_decreases_step:
  assumes "run_until_pred P \<sigma> \<sigma>'"
      and "\<not> P \<sigma>"
    shows "length (THE \<pi> . is_path P \<pi> \<and> hd \<pi> = (step \<sigma>) \<and> last \<pi> = \<sigma>' \<and> P \<sigma>') <
           length (THE \<pi> . is_path P \<pi> \<and> hd \<pi> = \<sigma> \<and> last \<pi> = \<sigma>' \<and> P \<sigma>')"
proof-
  obtain \<pi>\<^sub>0 where \<pi>\<^sub>0: "is_path P \<pi>\<^sub>0 \<and> hd \<pi>\<^sub>0 = \<sigma> \<and> last \<pi>\<^sub>0 = \<sigma>' \<and> P \<sigma>'"
    using assms(1)
    by (auto simp add: run_until_pred_as_path)
  have "run_until_pred P (step \<sigma>) \<sigma>'"
    using assms run_until_pred_step
    by auto
  then obtain \<pi>\<^sub>1 where \<pi>\<^sub>1: "is_path P \<pi>\<^sub>1 \<and> hd \<pi>\<^sub>1 = step \<sigma> \<and> last \<pi>\<^sub>1 = \<sigma>' \<and> P \<sigma>'"
    using assms(1)
    by (auto simp add: run_until_pred_as_path)
  have "\<pi>\<^sub>1 = tl \<pi>\<^sub>0"
    using paths_with_same_start[of \<pi>\<^sub>1 "tl \<pi>\<^sub>0" P] \<pi>\<^sub>0 \<pi>\<^sub>1 assms(2)
    apply (cases \<pi>\<^sub>1;auto split: if_split_asm)
    apply (cases \<pi>\<^sub>0;auto split: if_split_asm)
    apply (cases "tl \<pi>\<^sub>0";auto split: if_split_asm)
    apply (cases \<pi>\<^sub>0;auto split: if_split_asm)
    by (cases "tl \<pi>\<^sub>0";auto split: if_split_asm)
  hence "length \<pi>\<^sub>1 < length \<pi>\<^sub>0"
    using \<pi>\<^sub>0 
    by (cases \<pi>\<^sub>0;auto split: if_split_asm)
  moreover
  have "(THE \<pi> . is_path P \<pi> \<and> hd \<pi> = \<sigma> \<and> last \<pi> = \<sigma>' \<and> P \<sigma>') = \<pi>\<^sub>0"
    apply (rule the_equality)
    using paths_are_unique \<pi>\<^sub>0
    by auto
  moreover
  have "(THE \<pi> . is_path P \<pi> \<and> hd \<pi> = step \<sigma> \<and> last \<pi> = \<sigma>' \<and> P \<sigma>') = \<pi>\<^sub>1"
    apply (rule the_equality)
    using paths_are_unique \<pi>\<^sub>1
    by auto
  ultimately
  show ?thesis
    by auto
qed

lemma length_path_not_increases_run_until:
  assumes "run_until_pred P \<sigma> \<sigma>'"
    shows "length (THE \<pi> . is_path P \<pi> \<and> Some (hd \<pi>) = run_until (P || P1) \<sigma> \<and> last \<pi> = \<sigma>' \<and> P \<sigma>') \<le>
           length (THE \<pi> . is_path P \<pi> \<and> hd \<pi> = \<sigma> \<and> last \<pi> = \<sigma>' \<and> P \<sigma>')"
proof-
  obtain \<pi>\<^sub>0 where \<pi>\<^sub>0: "is_path P \<pi>\<^sub>0 \<and> hd \<pi>\<^sub>0 = \<sigma> \<and> last \<pi>\<^sub>0 = \<sigma>' \<and> P \<sigma>'"
    using assms(1)
    by (auto simp add: run_until_pred_as_path)

  have 0: "(P1 || P) = (P || P1)"
    unfolding pred_OR_def
    by auto
  have "terminates P \<sigma>"
    unfolding terminates_def
    using assms
    by auto
  hence terminates: "terminates (P || P1) \<sigma>"
    using terminates_pred_OR[of P _ P1] 0
    by auto
  then obtain \<sigma>'' where "run_until (P || P1) \<sigma> = Some \<sigma>''"
    unfolding run_until_def
    by auto
  hence "run_until_pred (P || P1) \<sigma> \<sigma>''"
    apply (subst (asm) deterministic)
    by (simp add: terminates)+

  obtain \<pi>\<^sub>0 where \<pi>\<^sub>0: "is_path P \<pi>\<^sub>0 \<and> hd \<pi>\<^sub>0 = \<sigma> \<and> last \<pi>\<^sub>0 = \<sigma>' \<and> P \<sigma>'"
    using assms(1)
    by (auto simp add: run_until_pred_as_path)

  obtain \<sigma>'' where 1: "run_until_pred (P1 || P) \<sigma> \<sigma>'' \<and> run_until_pred P \<sigma>'' \<sigma>'"
    using compose[of P P1] assms(1)
    unfolding seq_def
    by meson
  then obtain \<pi>\<^sub>1 \<pi>\<^sub>2 where \<pi>\<^sub>1: "is_path P \<pi>\<^sub>1 \<and> hd \<pi>\<^sub>1 = \<sigma>'' \<and> last \<pi>\<^sub>1 = \<sigma>' \<and> P \<sigma>'"
                   and \<pi>\<^sub>2: "is_path (P1 || P) \<pi>\<^sub>2 \<and> hd \<pi>\<^sub>2 = \<sigma> \<and> last \<pi>\<^sub>2 = \<sigma>'' \<and> (P1 || P) \<sigma>''"
    by (auto simp add: run_until_pred_as_path)

  have 2: "hd \<pi>\<^sub>0 = hd (\<pi>\<^sub>2 @ tl \<pi>\<^sub>1)"
    using \<pi>\<^sub>0 \<pi>\<^sub>2
    by (cases \<pi>\<^sub>2;auto)
  have 3: "last \<pi>\<^sub>0 = last (\<pi>\<^sub>2 @ tl \<pi>\<^sub>1)"
    using \<pi>\<^sub>0 \<pi>\<^sub>1 \<pi>\<^sub>2
    by (cases \<pi>\<^sub>0;cases \<pi>\<^sub>1;auto split: if_split_asm)
  have 4: "is_path P (\<pi>\<^sub>2 @ tl \<pi>\<^sub>1)"
    using \<pi>\<^sub>1 \<pi>\<^sub>2
    using is_path_pred_OR[of P1 P]
    apply (auto simp add: is_path_append)
    by (cases \<pi>\<^sub>1;cases \<pi>\<^sub>2;cases "tl \<pi>\<^sub>1";cases "tl \<pi>\<^sub>2";auto split: if_split_asm simp add: pred_OR_def)+

  have "\<pi>\<^sub>0 = \<pi>\<^sub>2 @ tl \<pi>\<^sub>1"
    using paths_with_same_start[of \<pi>\<^sub>0 "\<pi>\<^sub>2 @ tl \<pi>\<^sub>1" P, OF 2 3 _ _ 4] \<pi>\<^sub>0
    by auto
  hence "length \<pi>\<^sub>1 \<le> length \<pi>\<^sub>0"
    using \<pi>\<^sub>2
    by (cases \<pi>\<^sub>1;cases \<pi>\<^sub>2;auto)
  moreover
  have 5: "Some \<sigma>'' = run_until (P || P1) \<sigma>"
    using 0 1
    unfolding run_until_def
    apply auto
    apply (metis det_step.run_until_def deterministic option.inject)
    by (metis terminates_def)
  have "(THE \<pi>. is_path P \<pi> \<and> Some (hd \<pi>) = run_until (P || P1) \<sigma> \<and> last \<pi> = \<sigma>' \<and> P \<sigma>') = \<pi>\<^sub>1"
    apply (rule the_equality)
    using paths_are_unique \<pi>\<^sub>1 5
    apply auto
    by (metis option.inject)
  moreover
  have "(THE \<pi>. is_path P \<pi> \<and> hd \<pi> = \<sigma> \<and> last \<pi> = \<sigma>' \<and> P \<sigma>') = \<pi>\<^sub>0"
    apply (rule the_equality)
    using paths_are_unique \<pi>\<^sub>0
    by auto
  ultimately
  show ?thesis
    by auto
qed

lemma run_until_pred_run_until_pred_OR:
  assumes "terminates P0 \<sigma>"
      and "run_until (P0 || P1) \<sigma> = Some \<sigma>'"
  shows "run_until_pred P0 \<sigma>' = run_until_pred P0 \<sigma>"
proof-
  {
    fix \<sigma>''
    have 1: "(P0 || P1) = (P1 || P0)"
      unfolding pred_OR_def
      by auto
    have "terminates (P0 || P1) \<sigma>"
      using assms terminates_pred_OR[of P0 _ P1] 1
      by auto
    hence 0: "run_until_pred (P0 || P1) \<sigma> \<sigma>'"
      using assms
      by (subst (asm) deterministic,simp+)
    hence "run_until_pred P0 \<sigma>' \<sigma>''  = run_until_pred P0 \<sigma> \<sigma>''"
      using compose[of P0 P1] 1 assms
      apply (auto simp add: seq_def)
      using compose1 apply blast
      by (meson det_step.compose1 det_step.compose2)
  }
  thus ?thesis
    by auto
qed

lemma terminates_stepI:
  assumes "terminates P \<sigma>"
      and "\<not> P \<sigma>"
    shows "terminates P (step \<sigma>)"
proof-
  from assms obtain \<sigma>' where "run_until_pred P \<sigma> \<sigma>'"
    unfolding terminates_def
    by auto
  hence "run_until_pred P (step \<sigma>) \<sigma>'"
    using assms(2)
    by (auto simp add: run_until_pred_step)
  thus ?thesis
    unfolding terminates_def
    by auto
qed

function big_step :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> 's option"
  where "big_step P0 P1 \<sigma> =
            (if \<not> terminates P0 \<sigma> \<or> P0 \<sigma> then
                Some \<sigma>
             else case run_until (P0 || P1) (step \<sigma>) of
                 None \<Rightarrow> None
               | Some \<sigma> \<Rightarrow> big_step P0 P1 \<sigma>)"
  by pat_completeness auto
termination big_step
  apply (relation "measure (\<lambda>(P0,P1,\<sigma>) . length (THE \<pi> . is_path P0 \<pi> \<and> hd \<pi> = \<sigma> \<and> last \<pi> = The (run_until_pred P0 \<sigma>) \<and> P0 (The (run_until_pred P0 \<sigma>))))")
  apply auto
  subgoal for P0 P1 \<sigma> \<sigma>'
    apply (rule order.strict_trans1[of _ "length (THE \<pi>. is_path P0 \<pi> \<and> hd \<pi> = step \<sigma> \<and> last \<pi> = The (run_until_pred P0 (step \<sigma>)) \<and> P0 (The (run_until_pred P0 (step \<sigma>))))"])
    apply (subst run_until_pred_run_until_pred_OR[of _ "step \<sigma>" P1 \<sigma>'])
    apply (simp add: terminates_stepI)
    apply (simp)
    apply (subst run_until_pred_run_until_pred_OR[of _ "step \<sigma>" P1 \<sigma>'])
    apply (simp add: terminates_stepI)
    apply (simp)
    using length_path_not_increases_run_until[of P0 "step \<sigma>" "The (run_until_pred P0 (step \<sigma>))" P1]
    apply (cases "run_until_pred P0 (step \<sigma>) (The (run_until_pred P0 (step \<sigma>)))",auto simp add: run_until_def split: if_split_asm)[1]
    apply (metis det_step.deterministic det_step.run_until_def det_step.run_until_pred_step)
    apply (subst run_until_pred_step,simp)+
    apply (rule length_path_decreases_step)
    apply (metis det_step.deterministic det_step.run_until_def)
    apply simp
    done
  done

lemma halted_run_until_pred:
  assumes "run_until_pred P \<sigma> \<sigma>'"
  shows "P \<sigma>'"
  using assms
  by(induct rule: run_until_pred.induct,auto)

lemma halted_run_until:
  assumes "run_until P \<sigma> = Some \<sigma>'"
  shows "P \<sigma>'"
proof-
  obtain \<sigma>' where \<sigma>': "run_until P \<sigma> = \<sigma>'"
    by auto
  thus ?thesis
    using assms \<sigma>' halted_run_until_pred
    apply (subst (asm) deterministic)
    by (auto)
qed


lemma run_until_pred_pred_OR_halts_in_state:
  assumes "run_until_pred P0 \<sigma> \<sigma>'"
      and "run_until_pred (P0 || P1) \<sigma> \<sigma>''"
      and "P0 \<sigma>''"    
    shows "\<sigma>'' = \<sigma>'"
  using assms
proof(induct rule: run_until_pred.induct)
case (1 P \<sigma>)
  thus ?case 
    using run_until_pred.intros(1)[of "P || P1" \<sigma>]
    by (metis det_step.run_until_pred.cases pred_OR_def)
next
  case (2 P \<sigma> \<sigma>')
  thus ?case
    apply auto
    by (metis det_step.run_until_pred.cases)
qed

lemma while'_pred:
assumes "terminates P \<sigma>"
  shows "run_until_pred P \<sigma> = while'_pred P B (run_until_pred (P || Q)) (run_until_pred P) \<sigma>"
proof-
  {
    fix P0 P1 B body finish \<sigma> \<sigma>'
    assume "while'_pred P0 B body finish \<sigma> \<sigma>'"
       and "body = run_until_pred (P0 || Q)"
       and "finish = run_until_pred P0"
    hence "run_until_pred P0 \<sigma> \<sigma>'"
    proof(induct rule: while'_pred.induct)
      case (1 B \<sigma> P0 \<sigma>' P1)
      thus ?case
        by auto
    next
      case (2 P0 \<sigma> B body finish)
      thus ?case
        using run_until_pred.intros(1)
        by auto
    next
      case (3 B \<sigma> P0 body \<sigma>' finish \<sigma>'')
      have 4: "(Q || P0) = (P0 || Q)"
        unfolding pred_OR_def
        by auto
      have 5: "run_until_pred (Q || P0) (step \<sigma>) \<sigma>'"
        using 3(3,6) 4 deterministic[of "P0 || Q" "step \<sigma>" \<sigma>']
        by (cases "terminates (P0 || Q) (step \<sigma>)",auto simp add: run_until_def)
      show ?case
        apply (rule run_until_pred.intros(2))
        using 3 apply simp
        using 3 4 5 compose[of P0 Q, unfolded seq_def]
        apply auto
        by (metis)
    qed
  }
  note 0 = this[of P B "run_until_pred (P || Q)" "run_until_pred P" \<sigma> _, simplified]
  {
    fix \<sigma>' \<sigma>''
    assume "run_until_pred P \<sigma>'' \<sigma>'"
       and "terminates P \<sigma>''"
    hence "while'_pred P B (run_until_pred (P || Q)) (run_until_pred P) \<sigma>'' \<sigma>'"
    proof (induct P Q \<sigma>'' rule: big_step.induct)
      case (1 P Q \<sigma>'')
      show ?case
      proof (cases "B \<sigma>'' \<and> \<not>P \<sigma>''")
        case False
        then consider (a) "\<not>B \<sigma>'' \<and> \<not>P \<sigma>''" | (b) "P \<sigma>''"
          by auto
        thus ?thesis
        proof(cases)
          case (a)
          show ?thesis
            apply (rule while'_pred.intros(1))
            apply (simp add: a)+
            by (simp add: 1)
        next
          case (b)
          thus ?thesis
            using 1(1)[of \<sigma>'']
            using while'_pred.intros(2)[of P \<sigma>'' ] 1 run_until_pred.intros(1)[of P \<sigma>'']
            apply auto
            by (metis det_step.run_until_pred.simps)
        qed
      next
        case True
        note 10 = this
        have commute_pred_OR: "(Q || P) = (P || Q)"
          unfolding pred_OR_def
          by auto
        have 4: "terminates (P || Q) (step \<sigma>'')"
          using 1 terminates_pred_OR[of P "step \<sigma>''" Q] commute_pred_OR terminates_stepI True
          by auto
        then obtain \<sigma>''' where 11: "run_until_pred (P || Q) (step \<sigma>'') \<sigma>'''"
          unfolding terminates_def
          by (auto simp add: run_until_def)
        hence 12: "run_until_pred (P || Q) (step \<sigma>'') \<sigma>'''"
          using 11
          by (auto simp add: deterministic)
        have 13: "run_until_pred P (step \<sigma>'') \<sigma>'"
          using 1 10
          by (simp add: det_step.run_until_pred_step)
        show ?thesis
        proof(cases "P \<sigma>'''")
          case True
          hence 13: "\<sigma>''' = \<sigma>'"
            using 12 13 run_until_pred_pred_OR_halts_in_state[of P "step \<sigma>''" \<sigma>' Q \<sigma>''']
            by auto
          show ?thesis
            apply (rule while'_pred.intros(3)[of _ _ _ _ \<sigma>'])
            using 10 apply simp
            using 10 apply simp
            using 12 13 apply simp
            apply (rule while'_pred.intros(2))
            using True 13 apply simp
            done 
        next
          case False
          have commute_pred_OR: "(Q || P) = (P || Q)"
            unfolding pred_OR_def
            by auto
          have 4: "terminates (P || Q) (step \<sigma>'')"
            using 1 terminates_pred_OR[of P "step \<sigma>''" Q] commute_pred_OR terminates_stepI True
            by auto
          have commute_pred_OR: "(Q || P) = (P || Q)"
            unfolding pred_OR_def
            by auto
          hence 6: "run_until_pred P \<sigma>''' \<sigma>'"
            using 13 11 4 compose2[of Q P "step \<sigma>''" \<sigma>''' \<sigma>'] 1(3)
            by (auto simp add: deterministic commute_pred_OR)

          have 14: "terminates P \<sigma>''"
            using 1(3)
            unfolding terminates_def
            by auto
          
          show ?thesis
            apply (rule while'_pred.intros(3)[of _ _ _ _ \<sigma>'''])
            apply (simp add: True)
            apply (simp add: True)
            apply (simp add: 11)
            using 0 1 4 11 6 14 True
            apply auto
            using terminates_def 
            by (meson det_step.deterministic)
        qed
      qed
    qed
  }
  note 1 = this[of \<sigma>, simplified]
  show ?thesis
    using 0 1 assms 
    by auto
qed


text {*
  Rewriting to a Higher-Level spec:
  Let S be a simulation relation from concrete states @{typ 's} to abstract states @{typ '\<sigma>}.
  Transition relation $f$ is an abstraction of $a$ if any step by $a$ can be simulated by $f$.
  Precondition $P$ can be assumed, postcondition $Q$ must be guaranteed.
*}
definition HL_equality :: "('s \<Rightarrow> '\<sigma>) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('\<sigma> \<Rightarrow> '\<sigma> \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" ("_:: {_} _ \<preceq> _ {_}")
  where "S:: {P} a \<preceq> f {Q} \<equiv> \<forall> s s' . P s \<longrightarrow> a s s' \<longrightarrow> f (S s) (S s') \<and> Q s'"

text {*
  Compositionality:
*}
lemma HL_compose:
  assumes "S:: {P} a \<preceq> f {Q}"
      and "S:: {Q} b \<preceq> g {R}"
    shows "S:: {P} (a;b) \<preceq> (f;g) {R}"
proof-
  {
    fix s s'
    assume P: "P s"
       and ab: "(a;b) s s'"
    then obtain s'' where s'': "a s s'' \<and> b s'' s'"
      unfolding seq_def
      by auto
    hence "f (S s) (S s'') \<and> Q s'' \<and> g (S s'') (S s') \<and> R s'"
      using assms(1)[unfolded HL_equality_def,THEN spec,THEN spec,of s s''] P
      using assms(2)[unfolded HL_equality_def,THEN spec,THEN spec,of s'' s'] s''
      by auto
    hence "(f;g) (S s) (S s') \<and> R s'"
      unfolding seq_def
      by auto
  }
  thus ?thesis
    unfolding HL_equality_def
    by auto
qed

text {*
  Introduce the equality for a run in assembly.
  If the precondition implies that running until F produces a state that is also produced by $f'$,
  and which satisfies postcondition $Q$, and
  if f' is simulated by f, then a run until F is simulated by f.
*}
lemma HL_equality_intro:
  assumes "\<And> s . P s \<Longrightarrow> (a s && Q) (The (run_until_pred F s))"
      and "\<And> s s' . P s \<Longrightarrow> Q s' \<Longrightarrow> a s s' \<Longrightarrow> f (S s) (S s')" 
    shows "S:: {P} run_until_pred F \<preceq> f {Q}"
proof-
  {
    fix s s'
    assume "P s"
       and "run_until_pred F s s'"
    hence "f (S s) (S s') \<and> Q s'"
      using assms(1)[of s] assms(2)[of s s']
      apply (auto simp add: pred_AND_def)
      by (metis det_step.run_until_def deterministic option.distinct(1) option.inject)+
  }
  thus ?thesis
    unfolding HL_equality_def
    by auto
qed


lemma HL_equality_intro_step:
  assumes "\<And> s . P s \<Longrightarrow> (f' s && Q) (The (((\<lambda>s. (=) (step s)) ; run_until_pred F) s))"
      and "\<And> s s' . P s \<Longrightarrow> f' s s' \<Longrightarrow> f (S s) (S s')" 
    shows "S:: {P} (\<lambda>s. (=) (step s)) ; run_until_pred F \<preceq> f {Q}"
proof-
  {
    fix s s'
    assume P: "P s"
       and 1: "((\<lambda>s. (=) (step s)) ; run_until_pred F) s s'"
    hence "f (S s) (S s') \<and> Q s'"
      using assms(1)[of s] assms(2)[of s s']
      apply (auto simp add: pred_AND_def seq_def)
      by (smt 1 deterministic option.inject seq_def the_equality)+
  }
  thus ?thesis
    unfolding HL_equality_def
    by auto
qed

text {*
  While
*}
lemma rewrite_while_to_HL:
assumes "\<forall> s . P s \<longrightarrow> \<not>F s \<and> (B s = B' (S s))"
    and "S:: {P && B} ((\<lambda> s s' . step s = s');body) \<preceq> f {P}"
    and "S:: {P && (! B)} finish \<preceq> g {Q}"
  shows "S:: {P} (while'_pred F B body finish) \<preceq> (while_pred B' f ; g) {Q}"
proof-
  {
    fix s s'
    assume "while'_pred F B body finish s s'"
       and "S:: {P && B} ((\<lambda> s s' . step s = s');body) \<preceq> f {P}"
       and "S:: {P && (! B)} finish \<preceq> g {Q}"
       and "\<forall> s . P s \<longrightarrow> \<not>F s \<and> (B s = B' (S s))"
       and "P s"
    hence "((while_pred B' f) ; g) (S s) (S s') \<and> Q s'"
    proof(induct rule: while'_pred.induct)
      case (1 B s F finish s' body)
      have "WHILE B' DO f OD (S s) (S s)"
        using while_pred.intros(1)[of B' "S s" f] 1
        by auto
      moreover
      have "g (S s) (S s') \<and> Q s'"
        using 1(3) 1(5)[unfolded HL_equality_def,THEN spec,THEN spec,of s s'] 1(1,7)
        by (auto simp add: pred_AND_def pred_NOT_def pred_OR_def)
      ultimately
      show ?case
        unfolding seq_def
        by auto
    next
      case (2 F s B body finish)
      thus ?case
        by (simp add: pred_OR_def pred_AND_def pred_NOT_def)
    next
      case (3 B s F body s' finish s'')
      have s'': "(WHILE B' DO f OD ; g) (S s') (S s'') \<and> Q s''"
        using 3(5)[OF 3(6-8)]
        using 3(6)[unfolded HL_equality_def,THEN spec,THEN spec,of s s'] 3(1,3,9)
        by (auto simp: pred_AND_def seq_def)
      then obtain \<sigma>''' where \<sigma>''': "(WHILE B' DO f OD) (S s') \<sigma>''' \<and> g \<sigma>''' (S s'')"
        by (auto simp add: seq_def)
      have "(WHILE B' DO f OD) (S s) \<sigma>'''"
        apply (rule while_pred.intros(2)[of _ _ _ "S s'"])
        using 3 apply simp
        using 3(6)[unfolded HL_equality_def,THEN spec,THEN spec,of s s'] 3(1,3,9)
        apply (auto simp: pred_AND_def seq_def)[1]
        using \<sigma>''' by simp
      thus ?case
        using \<sigma>''' s''
        by (auto simp add: seq_def)
    qed
  }
  note 1 = this[OF _ assms(2-3,1)]
  thus ?thesis
    unfolding HL_equality_def
    by (auto)
qed

lemma rewrite_while_to_HL_v2:
assumes "\<forall> s . P s \<longrightarrow> (B s = B' (S s))"
    and "S:: {P && B} ((\<lambda> s s' . step s = s');body) \<preceq> f {P}"
    and "S:: {P && (! B)} finish \<preceq> g {Q}"
    and "\<turnstile> P && F \<longmapsto> !B"
    and "\<forall> s . P s \<and> \<not>B s \<and> F s \<longrightarrow> finish s s"
  shows "S:: {P} (while'_pred F B body finish) \<preceq> (while_pred B' f ; g) {Q}"
proof-
  {
    fix s s'
    assume "while'_pred F B body finish s s'"
       and "S:: {P && B} ((\<lambda> s s' . step s = s');body) \<preceq> f {P}"
       and "S:: {P && (! B)} finish \<preceq> g {Q}"
       and "\<forall> s . P s \<longrightarrow> (B s = B' (S s))"
       and "\<turnstile> P && F \<longmapsto> !B"
       and "\<forall> s . P s \<and> \<not>B s \<and> F s \<longrightarrow> finish s s"
       and "P s"
    hence "((while_pred B' f) ; g) (S s) (S s') \<and> Q s'"
    proof(induct rule: while'_pred.induct)
      case (1 B s F finish s' body)
      have "WHILE B' DO f OD (S s) (S s)"
        using while_pred.intros(1)[of B' "S s" f] 1
        by auto
      moreover
      have "g (S s) (S s') \<and> Q s'"
        using 1 1(5)[unfolded HL_equality_def,THEN spec,THEN spec,of s s'] 
        by (auto simp add: pred_AND_def pred_NOT_def pred_OR_def)
      ultimately
      show ?case
        unfolding seq_def
        by auto
    next
      case (2 F s B body finish)
      hence "\<not>B' (S s)"
        by (auto simp add: pred_logic)
      hence "(WHILE B' DO f OD) (S s) (S s)"
        by (simp add: while_pred.intros(1))
      thus ?case
        using 2(3)[unfolded HL_equality_def,THEN spec,THEN spec,of s s] 2
        by (auto simp add: seq_def pred_logic)
    next
      case (3 B s F body s' finish s'')
      have s'': "(WHILE B' DO f OD ; g) (S s') (S s'') \<and> Q s''"
        using 3(5)[OF 3(6-8)]
        using 3(6)[unfolded HL_equality_def,THEN spec,THEN spec,of s s'] 3
        by (auto simp: pred_AND_def seq_def)
      then obtain \<sigma>''' where \<sigma>''': "(WHILE B' DO f OD) (S s') \<sigma>''' \<and> g \<sigma>''' (S s'')"
        by (auto simp add: seq_def)
      have "(WHILE B' DO f OD) (S s) \<sigma>'''"
        apply (rule while_pred.intros(2)[of _ _ _ "S s'"])
        using 3 apply simp
        using 3(6)[unfolded HL_equality_def,THEN spec,THEN spec,of s s'] 3
        apply (auto simp: pred_AND_def seq_def)[1]
        using \<sigma>''' by simp
      thus ?case
        using \<sigma>''' s''
        by (auto simp add: seq_def)
    qed
  }
  note 1 = this[OF _ assms(2-3,1,4,5)]
  thus ?thesis
    unfolding HL_equality_def
    by (auto)
qed


text {*
  A run until F is simulated by a while loop with branching condition B', body f, sequenatially followed by g, if:
  1.) if B, then doing one step (the jump back) and running until F or F' is simulated by the body f.
  2.) if B, then stopping the while and running until F is simulated by g.
  3.) the precondition excludes the termination condition F and ensures that the branching condition B
      is simulated by B'.
*}

lemma HL_while_generic:
assumes "\<forall> s . P s \<longrightarrow> \<not>F s \<and> (B s = B' (S s))"
    and "S:: {P && B} ((\<lambda> s s' . step s = s');run_until_pred (F || F')) \<preceq> f {P}"
    and "S:: {P && !B} run_until_pred F \<preceq> g {Q}"
  shows "S:: {P} run_until_pred F \<preceq> WHILE B' DO f OD ; g {Q}"
proof-
  {
    fix s s'
    assume P: "P s"
       and run: "run_until_pred F s s'"
    hence "terminates F s"
      unfolding terminates_def
      by auto
    hence "while'_pred F B (run_until_pred (F || F')) (run_until_pred F) s s'"
      using run 
      apply (subst (asm) while'_pred)
      by simp+
    hence "(while_pred B' f ; g) (S s) (S s') \<and> Q s'"
      using P rewrite_while_to_HL[OF assms(1-3),unfolded HL_equality_def,THEN spec,THEN spec,of s s']
      by (auto)
  }
  thus ?thesis
    unfolding HL_equality_def
    by auto
qed

lemma remove_skip:
  shows "f ; skip = f"
  unfolding seq_def skip_def
  by auto

lemma add_skip:
  shows "f = skip ; f"
  unfolding seq_def skip_def
  by auto

lemma add_skip':
  shows "f = f ; skip"
  unfolding seq_def skip_def
  by auto


lemma HL_while:
assumes "\<forall> s . P s \<longrightarrow> \<not>F s \<and> (B s = B' (S s))"
    and "S:: {P && B} ((\<lambda> s s' . step s = s');run_until_pred (F || F')) \<preceq> f {P}"
    and "S:: {P && !B} run_until_pred F \<preceq> skip {Q}"
  shows "S:: {P} run_until_pred F \<preceq> WHILE B' DO f OD {Q}"
proof-
  {
    fix s s'
    assume P: "P s"
       and run: "run_until_pred F s s'"
    hence "terminates F s"
      unfolding terminates_def
      by auto
    hence "while'_pred F B (run_until_pred (F || F')) (run_until_pred F) s s'"
      using run 
      apply (subst (asm) while'_pred)
      by simp+
    hence "(while_pred B' f) (S s) (S s') \<and> Q s'"
      using P rewrite_while_to_HL[OF assms(1-3),unfolded HL_equality_def,THEN spec,THEN spec,of s s']
      by (auto simp add: remove_skip)
  }
  thus ?thesis
    unfolding HL_equality_def
    by auto
qed

lemma HL_while_v2:
assumes "\<forall> s . P s \<longrightarrow> ((B && ! F) s = B' (S s))"
    and "S:: {P && ! (B && ! F)} run_until_pred F \<preceq> g {Q}"
    and "S:: {P && B && !F} ((\<lambda> s s' . step s = s');run_until_pred (F || F')) \<preceq> f {P}"
  shows "S:: {P} run_until_pred F \<preceq> (WHILE B' DO f OD ; g) {Q}"
proof-
  {
    fix s s'
    assume P: "P s"
       and run: "run_until_pred F s s'"
    hence "terminates F s"
      unfolding terminates_def
      by auto
    hence "while'_pred F (B && ! F) (run_until_pred (F || F')) (run_until_pred F) s s'"
      using run 
      apply (subst (asm) while'_pred)
      by simp+
    moreover
    have "\<forall>s. P s \<and> \<not> B s \<and> F s \<longrightarrow> run_until_pred F s s"
      by (simp add: run_until_pred.intros(1))
    moreover
    have "\<turnstile> P && F \<longmapsto> ! (B && ! F)"
      by (auto simp add: pred_logic)
    moreover
    have "\<forall>s. P s \<and> \<not> (B && ! F) s \<and> F s \<longrightarrow> run_until_pred F s s"
      by (auto simp add: pred_logic det_step.run_until_pred.intros(1))
    ultimately
    have "(while_pred B' f ; g) (S s) (S s') \<and> Q s'"
      using rewrite_while_to_HL_v2[of P "B && !F" B' S "run_until_pred (F || F')" f "run_until_pred F" g Q F,
                OF _ assms(3,2),unfolded HL_equality_def,THEN spec,THEN spec,of s s']
            assms(1) P
      by (auto simp add: remove_skip)
  }
  thus ?thesis
    unfolding HL_equality_def
    by auto
qed


lemma HL_while2:
assumes "\<forall> s . I s \<longrightarrow> \<not>F s \<and> (B s = B' (S s))"
    and "S:: {P} run_until_pred (F || F') \<preceq> f {I}"
    and "S:: {I && B} ((\<lambda> s s' . step s = s');run_until_pred (F || F')) \<preceq> f {I}"
    and "S:: {I && (! B)} run_until_pred F \<preceq> skip {Q}"
  shows "S:: {P} run_until_pred F \<preceq> (DO f WHILE B' OD) {Q}"
proof-
  have 0: "(F' || F) = (F || F')"
    by (auto simp add: pred_logic)
  {
    fix s s'
    assume P: "P s"
       and run: "run_until_pred F s s'"
    hence "(run_until_pred (F' || F) ; run_until_pred F) s s'" 
      using compose
      by auto
    then obtain s0 where s0: "run_until_pred (F || F') s s0 \<and> run_until_pred F s0 s'"
      by (auto simp add: seq_def pred_logic 0)
    hence 1: "f (S s) (S s0) \<and> I s0"
      using assms(2) P
      by (auto simp add: HL_equality_def)
    hence "while2_pred B' f (S s) (S s') \<and> Q s'"
    proof(cases "B s0")
      case True
      hence 2: "B' (S s0)"
        using 1 assms(1)[THEN spec,of s0]
        by auto
      show ?thesis
        using while2_pred.intros(2)[of f "S s" "S s0" B' "S s'"] 1 2
              HL_while assms s0
        apply (auto simp add: HL_equality_def)
        by blast+
    next
      case False
      show ?thesis
        using while2_pred.intros(1)[of f "S s" "S s'" B']
              assms(1,4) False s0 1
        by (auto simp add: HL_equality_def skip_def pred_logic)
    qed
  }
  thus ?thesis
    unfolding HL_equality_def
    by auto
qed

lemma HL_ITE:
assumes "\<forall> s . P s \<longrightarrow> (B s = B' (S s))"
    and "S:: {P && B} a \<preceq> f {Q}"
    and "S:: {P && (! B)} a \<preceq> g {Q}"
  shows "S:: {P} a \<preceq> (IF B' THEN f ELSE g FI) {Q}"
proof-
  {
    fix s s'
    assume P: "P s"
       and run: "a s s'"
    have "(if_pred B' f g) (S s) (S s') \<and> Q s'"
    proof(cases "B s")
      case True
      hence "f (S s) (S s') \<and> Q s'"
        using assms(2)[unfolded HL_equality_def,THEN spec,THEN spec,of s s'] P run
        by (auto simp add: pred_AND_def)
      thus ?thesis
        using assms(1)[THEN spec,of s] P True
        by (auto simp add: if_pred.intros(1))
    next
      case False
      hence "g (S s) (S s') \<and> Q s'"
        using assms(3)[unfolded HL_equality_def,THEN spec,THEN spec,of s s'] P run
        by (auto simp add: pred_AND_def pred_NOT_def)
      thus ?thesis
        using assms(1)[THEN spec,of s] P False
        by (auto simp add: if_pred.intros(2))
    qed
  }
  thus ?thesis
    unfolding HL_equality_def
    by auto
qed


lemma HL_ITE2:
assumes "\<forall> s . P s \<longrightarrow> (B s = B' (S s))"
    and "S:: {P && B} a \<preceq> f {Q}"
    and "S:: {P && (! B)} a \<preceq> skip {Q}"
  shows "S:: {P} a \<preceq> (IF B' THEN f FI) {Q}"
  apply (rule HL_ITE)
  using assms by auto


lemma HL_call_generic:
  fixes S  :: "'s \<Rightarrow> '\<sigma>\<^sub>C \<times> '\<sigma>\<^sub>C\<^sub>C"
    and S' :: "'s \<Rightarrow> '\<sigma>\<^sub>L \<times> '\<sigma>\<^sub>C"
    and t  :: "'\<sigma>\<^sub>C\<^sub>C \<Rightarrow> '\<sigma>\<^sub>C"
  assumes "snd o S' = fst o S"
      and "S' :: {P} run_until_pred (F' || F) \<preceq> skip {P'}"
      and "S' :: {P'} run_until_pred F \<preceq> f {Q}"
    shows "S  :: {P} run_until_pred F \<preceq> call f {Q}"
proof-                                     
  {
    fix s s'
    assume P: "P s"
       and "run_until_pred F s s'"
    then obtain s'' where s'': "run_until_pred (F' || F) s s'' \<and> run_until_pred F s'' s'"
      using compose[of F F',unfolded seq_def]
      by meson
    hence 1: "run_until_pred (F' || F) s s'' \<and> P' s'' \<and> S' s'' = S' s"
      using assms(2)[unfolded HL_equality_def,THEN spec,THEN spec,of s s''] P
      by (auto simp add: skip_def)
    hence 2: "f (fst (S' s), snd (S' s)) (fst (S' s'), snd (S' s')) \<and> Q s'"
      using assms(3)[unfolded HL_equality_def,THEN spec,THEN spec,of s'' s'] s''
      by auto
    hence "f (fst (S' s), fst (S s)) (fst (S' s'), fst (S s'))"
      using assms(1)
      apply (cases "S' s";cases "S' s'";auto simp add: comp_def)
      by (metis snd_conv)
    hence "(call f) (S s) (S s') \<and> Q s'"
      using 2
      unfolding call_def
      by auto
  }
  thus ?thesis
    unfolding HL_equality_def
    by auto
qed


lemma HL_call\<^sub>1_generic:
  fixes S  :: "'s \<Rightarrow> '\<sigma>\<^sub>C \<times> '\<sigma>\<^sub>C\<^sub>C"
    and S' :: "'s \<Rightarrow> '\<sigma>\<^sub>L \<times> '\<sigma>\<^sub>C"
    and t  :: "'\<sigma>\<^sub>C\<^sub>C \<Rightarrow> '\<sigma>\<^sub>C"
  assumes "snd o S' = fst o S"
      and "S' :: {P} run_until_pred (F' || F) \<preceq> skip {P'}"
      and "S' :: {P'} run_until_pred F \<preceq> (\<lambda> \<sigma> \<sigma>' . f (p1 (\<C> \<sigma>)) \<sigma> \<sigma>') {Q}"
    shows "S  :: {P} run_until_pred F \<preceq> call\<^sub>1 f p1 {Q}"
proof-                                     
  {
    fix s s'
    assume P: "P s"
       and "run_until_pred F s s'"
    then obtain s'' where s'': "run_until_pred (F' || F) s s'' \<and> run_until_pred F s'' s'"
      using compose[of F F',unfolded seq_def]
      by meson
    hence 1: "run_until_pred (F' || F) s s'' \<and> P' s'' \<and> S' s'' = S' s"
      using assms(2)[unfolded HL_equality_def,THEN spec,THEN spec,of s s''] P
      by (auto simp add: skip_def)
    hence 2: "f (p1 (snd (S' s))) (fst (S' s), snd (S' s)) (fst (S' s'), snd (S' s')) \<and> Q s'"
      using assms(3)[unfolded HL_equality_def,THEN spec,THEN spec,of s'' s'] s''
      by auto
    hence "f (p1 (snd (S' s))) (fst (S' s), fst (S s)) (fst (S' s'), fst (S s'))"
      using assms(1)
      apply (cases "S' s";cases "S' s'";auto simp add: comp_def)
      by (metis snd_conv)
    moreover
    have "snd (S' s) = fst (S s)"
      using assms(1)
      apply (auto simp add: comp_def)
      by meson
    ultimately
    have "(call\<^sub>1 f p1)(S s) (S s') \<and> Q s'"
      using 2 
      unfolding call\<^sub>1_def
      by auto
  }
  thus ?thesis
    unfolding HL_equality_def
    by auto
qed

lemma HL_call\<^sub>2_generic:
  fixes S  :: "'s \<Rightarrow> '\<sigma>\<^sub>C \<times> '\<sigma>\<^sub>C\<^sub>C"
    and S' :: "'s \<Rightarrow> '\<sigma>\<^sub>L \<times> '\<sigma>\<^sub>C"
    and t  :: "'\<sigma>\<^sub>C\<^sub>C \<Rightarrow> '\<sigma>\<^sub>C"
  assumes "snd o S' = fst o S"
      and "S' :: {P} run_until_pred (F' || F) \<preceq> skip {P'}"
      and "S' :: {P'} run_until_pred F \<preceq> (\<lambda> \<sigma> \<sigma>' . f (p1 (\<C> \<sigma>)) (p2 (\<C> \<sigma>)) \<sigma> \<sigma>') {Q}"
    shows "S  :: {P} run_until_pred F \<preceq> call\<^sub>2 f p1 p2 {Q}"
proof-                                     
  {
    fix s s'
    assume P: "P s"
       and "run_until_pred F s s'"
    then obtain s'' where s'': "run_until_pred (F' || F) s s'' \<and> run_until_pred F s'' s'"
      using compose[of F F',unfolded seq_def]
      by meson
    hence 1: "run_until_pred (F' || F) s s'' \<and> P' s'' \<and> S' s'' = S' s"
      using assms(2)[unfolded HL_equality_def,THEN spec,THEN spec,of s s''] P
      by (auto simp add: skip_def)
    hence 2: "f (p1 (snd (S' s))) (p2 (snd (S' s))) (fst (S' s), snd (S' s)) (fst (S' s'), snd (S' s')) \<and> Q s'"
      using assms(3)[unfolded HL_equality_def,THEN spec,THEN spec,of s'' s'] s''
      by auto
    hence "f (p1 (snd (S' s))) (p2 (snd (S' s))) (fst (S' s), fst (S s)) (fst (S' s'), fst (S s'))"
      using assms(1)
      apply (cases "S' s";cases "S' s'";auto simp add: comp_def)
      by (metis snd_conv)
    moreover
    have "snd (S' s) = fst (S s)"
      using assms(1)
      apply (auto simp add: comp_def)
      by meson
    ultimately
    have "(call\<^sub>2 f p1 p2)(S s) (S s') \<and> Q s'"
      using 2 
      unfolding call\<^sub>2_def
      by auto
  }
  thus ?thesis
    unfolding HL_equality_def
    by auto
qed


lemma step_seq_run:
  shows "((\<lambda>s. (=) (step s)) ; run_until_pred F) \<sigma> = run_until_pred F (step \<sigma>)"
  by (auto simp add: seq_def)


lemma weaken:
  assumes "\<turnstile> P \<longmapsto> P'"
    and "S:: {P'} a \<preceq> f {Q}"
  shows "S:: {P} a \<preceq> f {Q}"
  using assms
  unfolding HL_equality_def
  by (auto simp add: pred_logic)

lemma strengthen:
  assumes "\<turnstile> Q' \<longmapsto> Q"
    and "S:: {P} a \<preceq> f {Q'}"
  shows "S:: {P} a \<preceq> f {Q}"
  using assms
  unfolding HL_equality_def
  by (auto simp add: pred_logic)

lemma skip:
assumes "\<turnstile> P \<longmapsto> F && Q"
  shows "S':: {P} run_until_pred F \<preceq> skip {Q}"
  using assms
  apply (auto simp add: HL_equality_def skip_def pred_logic)
  using det_step.run_until_pred.cases 
  by fastforce+



lemma refinement_abstraction:
  assumes "S :: {P} a \<preceq> f {Q}"
      and "{P'} f {Q'}"
    shows "P s \<longrightarrow> P' (S s) \<longrightarrow> a s s' \<longrightarrow> Q' (S s')"
  using assms
  apply (auto simp add: HL_equality_def Valid_def)
  done

end

end