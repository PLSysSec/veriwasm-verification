theory TNIv1ndnl

  imports Main "HOL-Word.WordBitwise"

begin

(* 'CA is a deterministic action *)

locale thread_non_inteference_non_deterministic = fixes
    dom           :: "'A \<Rightarrow> 'T" (* Function dom in Oheimb Model with 'T being the security domain *)
and view          :: "'S \<Rightarrow> 'T \<Rightarrow> 'V" (* Function output in Oheimb Model with 'O being the output of a given state for a domain  *)
and step          :: "'S \<Rightarrow> 'A \<Rightarrow> 'S set"

(* The simple version of the non-deterministic case of Von Oheimb is apropropriate as we do not require weak consistency.
Weak consistency allows for transitive non-inteference by defining a relation on which a security domain can influence another domain. 
This effectively is/would be modeled as a "read" view relation. *)

assumes step_consistent:"( ((dom a) = u) \<and>
                            (s' \<in> (step s a)) \<and> 
                            (view s u) = (view t u) 
                          )  
                          \<longrightarrow> 
                          ( (\<exists> t' . (t' \<in> (step t a))) \<and>
                            ((view s' u) = (view t' u))
                          )" (* Von Oheimb Non-deterministic Step Consistent *)


assumes locally_respects_left: 
                         "(((dom a) \<noteq> u) \<and> 
                             ((view s u) = (view t u)) \<and>
                             (s' \<in> (step s a))) 
                              \<longrightarrow> ((view s' u) = (view t u))" (* Locally Respects Left *)

assumes locally_respects_right:
                        "(  ((dom a) \<noteq> u) \<and> 
                             ((view s u) = (view t u))) 
                              \<longrightarrow> (\<exists> t' . (t' \<in> (step t a)) \<and> (view s u) = (view t' u))" (* Locally Respects Right *)
begin

fun tpurge :: " 'A list \<Rightarrow> 'T \<Rightarrow>  'A list"
  where "tpurge [] d = []" |
        "tpurge (a#aa) d = (case (dom a = d) of 
                              True \<Rightarrow> (a # tpurge aa d) | 
                              False \<Rightarrow> (tpurge aa d))" 

fun run :: " 'S \<Rightarrow> 'A list \<Rightarrow> 'S set"
  where "run s [] = {s}" |
        "run s (a#\<alpha>) = {t . \<exists> s'. s' \<in> (step s a) \<and> t \<in> (run s' \<alpha>)}"



lemma noninteference: (* One Directional *)
  assumes "s' \<in> (run s \<alpha>)"
  and "(tpurge \<alpha> u) = (tpurge \<beta> u)"
shows "\<exists> t'. t' \<in> (run s \<beta>) \<and> ((view s' u) = (view t' u))"
using assms
  sorry

end
(*
proof (induct \<alpha> arbitrary: s t)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a \<alpha>)
  then show 
?case 
    proof (cases "dom a = sc")
      case True
      then show ?thesis 
        using assms Cons step_consistency[where s=s and t=t and a=a and sc=sc]
        by (simp)
      next
      case False
      then show ?thesis 
        using Cons locally_respects[where s=s and a=a and u=sc]
        by (simp) 
    qed
  qed       

end
*)
(*




lemma view_partitioned:
  assumes " view s sc = view t sc"
  shows "((view (run s \<alpha>) sc) = (view (run t (purge \<alpha> sc)) sc))"
using assms
proof (induct \<alpha> arbitrary: s t)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a \<alpha>)
  then show 
?case 
    proof (cases "dom a = sc")
      case True
      then show ?thesis 
        using assms Cons step_consistency[where s=s and t=t and a=a and sc=sc]
        by (simp)
      next
      case False
      then show ?thesis 
        using Cons locally_respects[where s=s and a=a and u=sc]
        by (simp) 
    qed
  qed                  

*)

end