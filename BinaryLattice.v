Require Import VerifiedVerifier.Lattice.
Require Import VerifiedVerifier.Ltac.

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
Hint Constructors BinaryRel.

Program Instance BinaryOrder : Order BinarySet := { ord := BinaryRel }.
Next Obligation.
  unfold RelationClasses.Reflexive.
  intros x. destruct x; auto.
Defined.
Next Obligation.
  destruct x, y; auto; inversion H; inversion H0.
Defined.
Next Obligation.
  unfold RelationClasses.Transitive.
  destruct x, y, z; auto; inversion H; inversion H0.
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
Next Obligation. destruct a, b; auto. Defined.
Next Obligation. destruct a, b, c; auto. Defined.
Next Obligation. destruct a, b; auto. Defined.
Next Obligation. destruct a; auto. Defined.
Next Obligation. destruct a, b; auto. Defined.
Next Obligation. destruct a, b, c; auto. Defined.
Next Obligation. destruct a, b; auto. Defined.
Next Obligation. destruct a; auto. Defined.

Program Instance BinaryLOSet : LOSet BinaryOrder BinaryLattice.
Next Obligation. split; intros H; destruct a, b; auto; inversion H. Defined.
Next Obligation. split; intros H; destruct a, b; auto; inversion H. Defined.
