Require Import VerifiedVerifier.Lattice.

Inductive BoundedSet : Set :=
| top
| bounded
| bottom.

Inductive BoundedRel : BoundedSet -> BoundedSet -> Prop :=
| bot_rel x : BoundedRel bottom x
| self_rel x : BoundedRel x x
| bounded_top_rel : BoundedRel bounded top.

Program Instance BoundedOrder : Order BoundedSet := { ord := BoundedRel }.
Next Obligation.
  unfold RelationClasses.Reflexive.
  apply self_rel.
Defined.
Next Obligation. Proof.
  induction x; induction y; auto; inversion H; inversion H0.
Defined.
Next Obligation. Proof.
  unfold RelationClasses.Transitive.
  induction x; induction y; induction z; auto; intros; try apply self_rel;
    try inversion H; try inversion H0.
  apply bot_rel.
Defined.

Definition meet_BoundedSet (a : BoundedSet) (b : BoundedSet) : BoundedSet :=
  match a with
  | top => b
  | bounded =>
      match b with
      | top => bounded
      | _ => b
      end
  | bottom => bottom
  end.

Definition join_BoundedSet (a : BoundedSet) (b : BoundedSet) : BoundedSet :=
  match a with
  | bottom => b
  | bounded =>
      match b with
      | bottom => bounded
      | _ => b
      end
  | top => top
  end.

Program Instance BoundedLattice : Lattice BoundedSet :=
  {
    meet := meet_BoundedSet;
    join := join_BoundedSet;

    (*meet_commutative : forall a b, a ⊓ b = b ⊓ a;
    meet_associative : forall a b c, (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c);
    meet_absorptive  : forall a b, a ⊓ (a ⊔ b) = a;
    meet_idempotent  : forall a, a ⊓ a = a;

    join_commutative : forall a b, a ⊔ b = b ⊔ a;
    join_associative : forall a b c, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c);
    join_absorptive  : forall a b, a ⊔ (a ⊓ b) = a;
    join_idempotent  : forall a, a ⊔ a = a*)
  }.
Next Obligation.
  unfold meet_BoundedSet; induction a; induction b; auto.
Defined.
Next Obligation. Proof.
  unfold meet_BoundedSet; induction a; induction b; induction c; auto.
Defined.
Next Obligation. Proof.
  unfold meet_BoundedSet; unfold join_BoundedSet; induction a; induction b; auto.
Defined.
Next Obligation. Proof.
  unfold meet_BoundedSet; induction a; auto.
Defined.
Next Obligation. Proof.
  unfold join_BoundedSet; induction a; induction b; auto.
Defined.
Next Obligation. Proof.
  unfold join_BoundedSet; induction a; induction b; induction c; auto.
Defined.
Next Obligation. Proof.
  unfold join_BoundedSet; unfold meet_BoundedSet; induction a; induction b; auto.
Defined.
Next Obligation. Proof.
  unfold join_BoundedSet; induction a; auto.
Defined.

Program Instance BoundedLOSet : LOSet BoundedOrder BoundedLattice.
Next Obligation.
  split.
  - intros. induction a; induction b; auto; unfold meet_BoundedSet; inversion H.
  - intros. induction a; induction b; auto; unfold meet_BoundedSet in H; inversion H;
    try apply bot_rel; try apply self_rel; try apply bounded_top_rel.
Defined.
Next Obligation. Proof.
  split.
  - intros. induction a; induction b; auto; unfold join_BoundedSet; inversion H.
  - intros. induction a; induction b; auto; unfold join_BoundedSet in H; inversion H;
    try apply bot_rel; try apply self_rel; try apply bounded_top_rel.
Defined.
