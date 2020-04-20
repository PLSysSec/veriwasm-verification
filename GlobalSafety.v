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

(* NOTE: This probably isn't a useful definition *)
(*
Definition function_safety (p : program_ty) (f : function_ty) : Prop :=
  forall fuel s,
    s.(error) = false ->
    (run_function p f s fuel).(error) = false.
*)

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

Definition function_safety (f : function_ty) : Prop :=
  forall f cfg p n s fuel,
    well_formed_program p ->
    s.(error) = false ->
    In f p.(fun_list) ->
    cfg = fst f ->
    In n cfg.(nodes) ->
    (run_program' p cfg n s fuel).(error) = false.

Theorem verified_function :
  forall f,
    verify_function f = true ->
    function_safety f.
Proof.
  admit.
Admitted.

(* NOTE: This probably isn't the correct forumlation *)
(*
Theorem function_safety_implies_program_safety :
  forall p f,
    well_formed_program p ->
    In f p.(fun_list) ->
    function_safety f ->
    program_safety p.
Proof.
  unfold program_safety. intros. unfold run_program. unfold run_program'.
*)



Theorem function_safety_something :
  forall p f n bb fun_name s fuel s' n',
    well_formed_program p ->
    verify_program p = true ->
    In f p.(fun_list) ->
    In n (fst f).(nodes) ->
    bb = fst n ->
    Direct_Call fun_name = last bb Ret ->
    s' = run_program' p (fst f) n s fuel ->
    s.(error) = false ->
    s'.(error) = false ->
    Some n' = next_node (fst f) s' n ->
    (run_program' p (fst f) n' s' fuel).(error) = false.
Proof.


Theorem verified_program :
  forall p,
    well_formed_program p ->
    verify_program p = true ->
    program_safety p.
Proof.
  intros. unfold program_safety. intros. unfold run_program.
  unfold run_program'. induction fuel.
  simpl. reflexivity. fold run_program'. fold run_program' in IHfuel.
  destruct (next_node (fst (main p)) (start_state p) (start_node (fst (main p)))).
  -
    + destruct (last (fst (start_node (fst (main p)))) Ret). unfold run_basic_block.
  -


  induction p.(fun_list).
  - unfold run_program'. induction fuel.
    + simpl. reflexivity.
    + destruct (next_node (fst (main p)) (start_state p) (start_node (fst (main p)))).
      *
