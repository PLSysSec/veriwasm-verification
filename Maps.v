Definition total_map (A B:Type) := 
  A -> B.

Definition t_update {A B : Type} (eq_dec:forall (x y:A),{x=y}+{x<>y}) (f:total_map A B) (x:A) (v:B) : total_map A B :=
  fun y => if eq_dec x y then v else f y.

Definition t_get {A} {B} (f:total_map A B) (x:A) : B := 
  f x.

Definition t_empty {A} {B} (v:B) : total_map A B :=
  fun (_ : A) => v.


Lemma t_apply_empty: forall A B x v, @t_empty A B v x = v.
Proof.
  intros.
  unfold t_empty. reflexivity.
Qed.

(*
Lemma t_update_eq : forall A B eq_dec (m: total_map A B) x v,
  (t_update eq_dec m x v) x = v.
Proof.
  intros.
  unfold t_update.
  rewrite <- beq_id_refl.
  reflexivity.
Qed.

Theorem t_update_neq : forall (X:Type) v x1 x2
                         (m : total_map X),
  x1 <> x2 ->
  (t_update m x1 v) x2 = m x2.
Proof.
  intros.
  apply false_beq_id in H.
  unfold t_update.
  rewrite -> H.
  reflexivity.
Qed.

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    t_update (t_update m x v1) x v2
  = t_update m x v2.
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality_dep.
  intros.
  destruct (beq_id x x0).
  + reflexivity.
  + reflexivity.
Qed.

Theorem t_update_same : forall X x (m : total_map X),
  t_update m x (m x) = m.
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality_dep.
  intros.
  destruct (beq_idP x x0).
  + rewrite -> e. reflexivity.
  + reflexivity.
Qed.

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
    (t_update (t_update m x2 v2) x1 v1)
  = (t_update (t_update m x1 v1) x2 v2).
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality_dep.
  intros.
  destruct (beq_idP x1 x).
  - destruct (beq_idP x2 x).
    + exfalso. apply H. rewrite e, e0. reflexivity.
    + reflexivity.
  - destruct (beq_idP x2 x).
    + reflexivity.
    + reflexivity.
Qed.
*)

Definition partial_map (A B:Type) := total_map A (option B).

Definition empty {A B: Type} : partial_map A B :=
  t_empty None.

Definition update {A B: Type} (eq_dec:forall (x y:A),{x=y}+{x<>y}) (m: partial_map A B) (k: A) (v: B) :=
  t_update eq_dec m k (Some v).

Definition member {A B: Type} (m : partial_map A B) (k: A) :=
match (m k) with
| Some _ => true
| None => false
end.

Lemma apply_empty : forall A B x, @empty A B x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty. reflexivity.
Qed.

(*
Lemma update_eq : forall A B eq_dec (m: partial_map A B) x v,
  (update eq_dec m x v) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq. reflexivity.
Qed.

Lemma update_neq : forall A (m: partial_map A) x1 x2 v,
  x2 <> x1 ->
  (update m x2 v) x1 = m x1.
Proof.
  intros. unfold update. rewrite t_update_neq.
  - reflexivity.
  - apply H.
Qed.

Lemma update_shadow : forall A (m: partial_map A) x v1 v2,
  update (update m x v1) x v2 = update m x v2.
Proof.
  intros. unfold update. rewrite t_update_shadow. reflexivity.
Qed.

Lemma update_same : forall A (m: partial_map A) x v,
  m x = Some v ->
  update m x v = m.
Proof.
  intros. unfold update. rewrite <- H. rewrite t_update_same. reflexivity.
Qed.

Lemma update_permute : forall A (m: partial_map A) x1 x2 v1 v2,
  x2 <> x1 ->
  (update (update m x2 v2) x1 v1) =
  (update (update m x1 v1) x2 v2).
Proof.
  intros. unfold update. rewrite t_update_permute.
  - reflexivity.
  - apply H.
Qed.
*)
