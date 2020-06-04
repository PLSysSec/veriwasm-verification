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
