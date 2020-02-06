(*

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
 
 *)

theory SymbolicRewriting
  imports "HOL-Word.Word"
begin

section "Symbolic Rewriting"



text {*
  We introduce a let' which does \emph{exactly} the same as @{term Let}.
  However, for our own let' we can do controlled simplification.
  Assume the current goal considers a let' of the form:\\
  \begin{tabular}{ll}
  let' & $a = x$;\\
       & $b = y$;\\
       & $c = z$ in\\
       & $f$
  \end{tabular}\\
  We rewrite these line by line, as follows:\\
    apply (simp add: $\ldots$ cong: Let'\_weak\_cong, subst inline\_Let')\\
    apply (simp add: $\ldots$ cong: Let'\_weak\_cong, subst inline\_Let')\\
    apply (simp add: $\ldots$ cong: Let'\_weak\_cong, subst inline\_Let')\\

  The congruence rule instructs simp to simplify $x$ without touching $y$ or $z$.
  Then, the actual substitution happens, i.e., term y is rewritten to $y[a := x]$. 
*}

nonterminal let'binds and let'bind
syntax
  "_bind'"  :: "[pttrn, 'a] \<Rightarrow> let'bind"            ("(2_ =/ _)" 10)
  ""        :: "let'bind \<Rightarrow> let'binds"              ("_")
  "_binds'" :: "[let'bind, let'binds] \<Rightarrow> let'binds" ("_;/ _")
  "_Let'"   :: "[let'binds, 'a] \<Rightarrow> 'a"              ("(let' (_)/ in (_))" [0, 10] 10)

definition "Let' \<equiv> Let"
translations
  "_Let' (_binds' b bs) e"  \<rightleftharpoons> "_Let' b (_Let' bs e)"
  "let' x = a in e"        \<rightleftharpoons> "CONST Let' a (\<lambda>x. e)"

lemma Let'_weak_cong:
  assumes "x = y"
  shows "Let' x f = Let' y f"
  using assms
  by (rule arg_cong)

lemma inline_Let':
  shows "Let' x f = f x"
  unfolding Let'_def
  by auto



text {*
  Thanks to Peter Lammich: repeat a method n times
*}
method_setup repeat_n = \<open>let
in
  Scan.lift Parse.nat -- Method.text_closure >>
    (fn (n,text) => fn ctxt => fn using => fn st =>
      let
        val method = Method.evaluate_runtime text ctxt using;
        fun compose m1 m2 = Seq.THEN (Seq.filter_results o m1, m2)
        fun method_n_times 0 = (Method.succeed using)
          | method_n_times i = compose method (method_n_times (i-1))
      in
        (method_n_times n) st
      end)
end\<close>



text {*
  Convert Suc (Suc $\ldots$)) to a numeral.
  Works only if you do:
   apply (simp only: nat\_to\_numeral)
*}
lemma nat_to_numeral1:
  "Suc 0 = 1"  
  "Suc (numeral n) = numeral (Num.inc n)"
  by (auto simp: add_One)

lemma if_not_true:
  shows "(\<not> True \<longrightarrow> b) = True"
  by auto

lemmas nat_to_numeral = nat_to_numeral1 Num.inc.simps Suc_eq_plus1_left one_add_one add_0_right

text {*
  Split an if statement into two subgoals.
*}
lemma ifI:
  assumes "b \<Longrightarrow> P"
      and "\<not>b \<Longrightarrow> Q"
    shows "((b \<longrightarrow> P) \<and> (\<not>b \<longrightarrow> Q))"
  using assms
  by (auto)


end