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
    (fst (run_program_stream p fuel)).(error) = false.

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

Theorem program_stream_maintains_error :
  forall p fuel,
    (fst (run_program_stream p fuel)).(error) = true ->
    (fst (run_program_stream p (fuel + 1))).(error) = true.
Proof.
  admit.
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

(* NOTE: This probably isn't the correct formulation *)
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

(* Theorems TODO list:
   - cf_check implies that indirect calls are safe
   - program well-formedness implies getting the next instructions is safe
*)


Theorem well_formed_find_edge_ret :
  forall cfg n p f ,
    well_formed_program p ->
    In f p.(fun_list) ->
    cfg = fst f ->
    In n cfg.(nodes) ->
    (last (fst n) Ret) = Ret ->
    forall b,
      find_edge cfg n b = None.
Proof.
  admit.
Admitted.

Theorem well_formed_find_edge_branch :
  forall cfg n p f c,
    well_formed_program p ->
    In f p.(fun_list) ->
    cfg = fst f ->
    In n cfg.(nodes) ->
    (last (fst n) Ret) = Branch c ->
    exists n' n'',
      find_edge cfg n True_Branch = Some n' /\
      find_edge cfg n False_Branch = Some n'' /\
      find_edge cfg n Non_Branch = None.
Proof.
  admit.
Admitted.

(* TODO: Might have to change how the conditional is handled *)
Theorem well_formed_find_edge_non_branch :
  forall cfg n p f c,
    well_formed_program p ->
    In f p.(fun_list) ->
    cfg = fst f ->
    In n cfg.(nodes) ->
      (last (fst n) Ret) <> Ret ->
      (last (fst n) Ret) <> Branch c ->
      exists n',
        find_edge cfg n True_Branch = None /\
        find_edge cfg n False_Branch = None /\
        find_edge cfg n Non_Branch = Some n'.
Proof.
  admit.
Admitted.

Theorem verified_function_lookup :
  forall p,
    well_formed_program p ->
    verify_program p = true ->
    forall s istream fuel r hd_i,
      (s, istream) = run_program_stream p fuel ->
      s.(error) = false ->
      Some hd_i = hd_error istream ->
      hd_i.(instr) = Indirect_Call r ->
      (fst (run_program_stream p (fuel + 1))).(error) = false.
Proof.
  admit.
Admitted.

(* NOTE: shouldn't even need to run the verifier for this one, just well-formedness *)
Theorem verified_function_call :
  forall p,
    well_formed_program p ->
    forall s istream fuel hd_i f_name,
      (s, istream) = run_program_stream p fuel ->
      s.(error) = false ->
      Some hd_i = hd_error istream ->
      hd_i.(instr) = Direct_Call f_name ->
      (fst (run_program_stream p (fuel + 1))).(error) = false.
Proof.
  admit.
Admitted.

Theorem verify_get_instrs_till_terminal :
  forall cfg n fuel p f,
    well_formed_program p ->
    In f p.(fun_list) ->
    cfg = fst f ->
    In n cfg.(nodes) ->
    snd (get_instrs_till_terminal cfg n fuel) <> error_return.
Proof.
  intros. unfold get_instrs_till_terminal.
  induction fuel. unfold snd. discriminate.
  fold get_instrs_till_terminal. fold get_instrs_till_terminal in IHfuel.
  assert ((fst n) <> nil). unfold well_formed_program in H. destruct H. destruct H3. destruct H4. destruct H5.
  - specialize H6 with f. apply H6 in H0. unfold well_formed_fun in H0. unfold well_formed_cfg in H0.
    destruct H0. destruct H7. destruct H8. unfold non_empty_nodes in H8. specialize H8 with n. symmetry in H1.
    rewrite H1 in H8. apply H8. apply H2.
  - admit.
    (* case (last (fst n) Ret); intros. *)
Admitted.

Theorem verify_get_next_instrs :
  forall p cfg n i s fuel,
    well_formed_program p ->
    exists f,
      In f p.(fun_list) ->
      cfg = fst f ->
      In n cfg.(nodes) ->
      In i (fst n) ->
      verify_program p = true ->
      snd (get_next_instrs p cfg n i s fuel) <> error_return.
Proof.
  admit.
Admitted.

Theorem verified_program :
  forall p,
    well_formed_program p ->
    verify_program p = true ->
    program_safety p.
Proof.
  intros. unfold program_safety. intros. unfold run_program_stream.
  pose proof verify_get_instrs_till_terminal as Hterminal.
  specialize Hterminal with (fst (main p)) (start_node (fst (main p))) fuel p (main p).
  assert (snd (get_instrs_till_terminal (fst (main p)) (start_node (fst (main p))) fuel) <> error_return).
  apply Hterminal; auto.
  unfold well_formed_program in H. destruct H. destruct H1. destruct H2. destruct H3. assumption.
  unfold well_formed_program in H. destruct H. destruct H1. destruct H2. destruct H3.
  specialize H4 with (main p). apply H4 in H3. unfold well_formed_fun in H3.
  unfold well_formed_cfg in H3. destruct H3. destruct H5. destruct H6. assumption.

  destruct (get_instrs_till_terminal (fst (main p)) (start_node (fst (main p))) fuel).
  unfold snd in H1. case r. auto. admit.
  unfold run_program_stream'. induction fuel.
  simpl. reflexivity.
  fold run_program_stream'. fold run_program_stream' in IHfuel.
  simpl (error (start_state p)). simpl (exit (start_state p)). destruct (false || false)%bool. auto.
  induction l. auto.
  pose proof verify_get_instrs_till_terminal as Hterminal'.
  pose proof verify_get_next_instrs as Hnext.
  specialize Hnext with p (cfg a) (node a) (instr a) (run_instr p (instr a) (start_state p)) (S fuel).
  destruct (get_next_instrs p (cfg a) (node a) (instr a) (run_instr p (instr a) (start_state p)) (S fuel)).
  destruct r0.
  - unfold run_instr. destruct (instr a); auto.
    + destruct (function_lookup p (get_register (start_state p) r0)).
      auto. admit.
    + admit.
  - admit.
  - unfold run_program_stream'.


  case (get_instrs_till_terminal (fst (main p)) (start_node (fst (main p))) fuel).
  intros. case r. auto. admit.
Admitted.


Theorem function_safety_independent :
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


(* NOTE: old version *)
(*
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
*)
