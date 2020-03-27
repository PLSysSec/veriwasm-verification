Require Import VerifiedVerifier.Lattice.

Inductive BinarySet : Set :=
| top 
| bottom.

Definition BinarySet_eq_dec : forall (x y : BinarySet), {x=y} + {x<>y}.
Proof.
  decide equality.
Qed.

Definition BinarySet_eqb (a : BinarySet) (b : BinarySet) : bool :=
  if BinarySet_eq_dec a b
  then true
  else false.

Inductive BinaryRel : BinarySet -> BinarySet -> Prop :=
| bot_rel x : BinaryRel bottom x
| top_rel x : BinaryRel x top.

Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.
Next Obligation.
  unfold RelationClasses.Reflexive.
  intros x. destruct x. apply top_rel. apply bot_rel. 
Defined.
Next Obligation. Proof.
  induction x; induction y; auto; inversion H; inversion H0.
Defined.
Next Obligation. Proof.
  unfold RelationClasses.Transitive.
  induction x; induction y; induction z; auto; intros; try apply self_rel;
    try inversion H; try inversion H0.
Defined.

Definition meet_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet :=
  match a with
  | top => b
  | bottom => bottom
  end.

Definition join_BinarySet (a : BinarySet) (b : BinarySet) : BinarySet :=
  match a with
  | bottom => b
  | top => top
  end.

Program Instance BinaryLattice : Lattice BinarySet :=
  {
    meet := meet_BinarySet;
    join := join_BinarySet;

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
  unfold meet_BinarySet; induction a; induction b; auto.
Defined.
Next Obligation. Proof.
  unfold meet_BinarySet; induction a; induction b; induction c; auto.
Defined.
Next Obligation. Proof.
  unfold meet_BinarySet; unfold join_BinarySet; induction a; induction b; auto.
Defined.
Next Obligation. Proof.
  unfold meet_BinarySet; induction a; auto.
Defined.
Next Obligation. Proof.
  unfold join_BinarySet; induction a; induction b; auto.
Defined.
Next Obligation. Proof.
  unfold join_BinarySet; induction a; induction b; induction c; auto.
Defined.
Next Obligation. Proof.
  unfold join_BinarySet; unfold meet_BinarySet; induction a; induction b; auto.
Defined.
Next Obligation. Proof.
  unfold join_BinarySet; induction a; auto.
Defined.

Program Instance BinaryLOSet : LOSet BinaryOrder BinaryLattice.
Next Obligation.
  split.
  - intros. induction a; induction b; auto; unfold meet_BinarySet; inversion H.
  - intros. induction a; induction b; auto; unfold meet_BinarySet in H; inversion H;
    try apply bot_rel; try apply top_rel.
Defined.
Next Obligation. Proof.
  split.
  - intros. induction a; induction b; auto; unfold join_BinarySet; inversion H.
  - intros. induction a; induction b; auto; unfold join_BinarySet in H; inversion H;
    try apply bot_rel; try apply top_rel.
Defined.
