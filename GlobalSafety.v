Require Import VerifiedVerifier.Machine.
Require Import VerifiedVerifier.Bits.
Require Import VerifiedVerifier.Maps.
Require Import VerifiedVerifier.Safety.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import VerifiedVerifier.BinaryLattice.
Require Import VerifiedVerifier.AbstractAnalysis.
Require Import VerifiedVerifier.Semantics.
Require Import Lia.


(* TODO: Don't really know how to encode this*)
(*
Definition function_safety (f : function_ty) :=
*)

Definition program_safety (p : program_ty) : Prop :=
  forall fuel,
    (run_program p fuel).(error) = false.

Definition function_safety (p : program_ty) : Prop :=
  forall fuel,
    (run_function

Theorem program_maintains_error :
  forall s,
    s.(error) = true ->
    forall p cfg n fuel,
      (run_program' p cfg n s fuel).(error) = true.
Proof.
  intros. induction fuel.
  simpl. assumption.
  simpl. destruct (next_node cfg s n).
  - admit.
  - admit.
Admitted.

Theorem verified_function :
  forall f p,
    verify_program p = true -> program_safety

Theorem verified_program :
  forall p,
    verify_program p = true -> program_safety p.
Proof.
  admit.
Admitted.
