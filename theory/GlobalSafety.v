Require Import VerifiedVerifier.Machine.
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
    (fst (run_program_stream p (S fuel))).(error) = true.
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
      (run_instr p hd_i.(instr) s).(error) = false.
Proof.
  admit.
Admitted.

(* NOTE: shouldn't even need to run the verifier for this one, just well-formedness *)
Theorem verified_function_call :
  forall p,
    well_formed_program p ->
    verify_program p = true ->
    forall s istream fuel hd_i f_name,
      (s, istream) = run_program_stream p fuel ->
      s.(error) = false ->
      Some hd_i = hd_error istream ->
      hd_i.(instr) = Direct_Call f_name ->
      (run_instr p hd_i.(instr) s).(error) = false.
Proof.
  admit.
Admitted.

Theorem verified_heap_read :
  forall p,
    well_formed_program p ->
    verify_program p = true ->
    forall s istream fuel hd_i r_dst r_src r_base,
      (s, istream) = run_program_stream p fuel ->
      s.(error) = false ->
      Some hd_i = hd_error istream ->
      hd_i.(instr) = Heap_Read r_dst r_src r_base ->
      (run_instr p hd_i.(instr) s).(error) = false.
Proof.
  admit.
Admitted.

Theorem verified_heap_write :
  forall p,
    well_formed_program p ->
    verify_program p = true ->
    forall s istream fuel hd_i r_dst r_val r_base,
      (s, istream) = run_program_stream p fuel ->
      s.(error) = false ->
      Some hd_i = hd_error istream ->
      hd_i.(instr) = Heap_Write r_dst r_val r_base ->
      (run_instr p hd_i.(instr) s).(error) = false.
Proof.
  admit.
Admitted.
Proof.

Theorem verified_stack_contract :
  forall p,
    well_formed_program p ->
    verify_program p = true ->
    forall s istream fuel hd_i i,
      (s, istream) = run_program_stream p fuel ->
      s.(error) = false ->
      Some hd_i = hd_error istream ->
      hd_i.(instr) = Stack_Contract i ->
      (run_instr p hd_i.(instr) s).(error) = false.
  admit.
Admitted.

Theorem verified_stack_read :
  forall p,
    well_formed_program p ->
    verify_program p = true ->
    forall s istream fuel hd_i r i,
      (s, istream) = run_program_stream p fuel ->
      s.(error) = false ->
      Some hd_i = hd_error istream ->
      hd_i.(instr) = Stack_Read r i ->
      (run_instr p hd_i.(instr) s).(error) = false.
Proof.
  admit.
Admitted.

Theorem verified_stack_write :
  forall p,
    well_formed_program p ->
    verify_program p = true ->
    forall s istream fuel hd_i i r,
      (s, istream) = run_program_stream p fuel ->
      s.(error) = false ->
      Some hd_i = hd_error istream ->
      hd_i.(instr) = Stack_Write i r ->
      (run_instr p hd_i.(instr) s).(error) = false.
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

Theorem run_program_stream_equiv :
  forall p istream s fuel s' istream',
    well_formed_program p ->
    (s', istream') = run_program_stream' p istream s fuel ->
    fst (run_program_stream' p istream s (S fuel)) = fst (run_program_stream' p istream' s' 1).
Proof.
  admit.
Admitted.

Theorem function_safety_run :
  forall p s fuel,
    well_formed_program p ->
    verify_program p = true ->
    s = run_program_stream p fuel ->
    (fst s).(error) = false ->
    (fst (run_program_stream p (S fuel))).(error) = false.
Proof.
  intros. unfold run_program_stream.
  admit.
Admitted.

(* TODO: find official lemmas for these *)
Lemma distribute_fst {A : Type} {B : Type} :
  forall (c : bool) (x: A) (y : A) (a : B) (b : B),
    fst (if c then (x, a) else (y, b)) = if c then x else y.
Proof.
  intros. case c; auto.
Qed.

Lemma error_set_exit :
  forall s,
    s.(error) = (set_exit_state s).(error).
Proof.
  auto.
Qed.

Lemma distribute_error :
  forall (c : bool) s s',
    error (if c then s else s') = if c then (error s) else (error s').
Proof.
  intros. case c; auto.
Qed.

Lemma if_eq :
  forall (A : Type) (c : bool) (a : A),
    (if c then a else a) = a.
Proof.
  intros. case c; auto.
Qed.

Lemma tuple_eq :
  forall (x : (state * list instr_data)),
    (fst x, snd x) = x.
Proof.
  intros. destruct x. simpl. auto.
Qed.

(* TODO: Generalize these *)
Lemma tuple_eq' :
  forall (x y : (state * list instr_data)),
    x = y ->
    fst x = fst y /\ snd x = snd y.
Proof.
  intros.
  pose proof surjective_pairing as H1. specialize H1 with state (list instr_data) x.
  rewrite H1 in H. destruct y. inversion H. rewrite H2. rewrite H3.
  unfold fst. unfold snd. auto.
Qed.

Lemma tuple_split :
  forall (a : state) (b : list instr_data) (x : (state * list instr_data)),
    (a, b) = x ->
    a = fst x /\ b = snd x.
Proof.
  intros. destruct x. pose proof tuple_eq'.
  specialize H0 with (a, b) (s, l). apply H0 in H. inversion H.
  split; auto.
Qed.

Lemma tuple_ret_eq' :
  forall (x y : (list instr_data * return_state)),
    x = y ->
    fst x = fst y /\ snd x = snd y.
Proof.
  intros.
  pose proof surjective_pairing as H1. specialize H1 with (list instr_data) return_state x.
  rewrite H1 in H. destruct y. inversion H. rewrite H2. rewrite H3.
  unfold fst. unfold snd. auto.
Qed.

Lemma tuple_ret_split :
  forall (a : list instr_data) (b : return_state) (x : (list instr_data * return_state)),
    (a, b) = x ->
    a = fst x /\ b = snd x.
Proof.
  intros. destruct x. pose proof tuple_ret_eq'.
  specialize H0 with (a, b) (l, r). apply H0 in H. inversion H.
  split; auto.
Qed.

Lemma prog_stream_eq :
  forall p fuel start_stream,
    snd (get_instrs_till_terminal (fst (main p)) (start_node (fst (main p))) fuel) = normal_return ->
    fst (get_instrs_till_terminal (fst (main p)) (start_node (fst (main p))) fuel) = start_stream ->
    run_program_stream p fuel = run_program_stream' p start_stream (start_state p) fuel.
Proof.
  intros. unfold run_program_stream.
  remember (get_instrs_till_terminal (fst (main p)) (start_node (fst (main p))) fuel) as g.
  destruct g. pose proof tuple_ret_split.
  specialize H1 with l r (get_instrs_till_terminal (fst (main p)) (start_node (fst (main p))) fuel).
  apply H1 in Heqg. inversion Heqg. simpl in H. simpl in H0. rewrite H. rewrite H0. reflexivity.
Qed.

Theorem function_safety_run_other :
  forall p s istream fuel start_stream s',
    well_formed_program p ->
    verify_program p = true ->
    (snd (get_instrs_till_terminal (fst (main p)) (start_node (fst (main p))) fuel)) = normal_return ->
    start_stream = (fst (get_instrs_till_terminal (fst (main p)) (start_node (fst (main p))) fuel)) ->
    (s, istream) = run_program_stream' p start_stream (start_state p) fuel ->
    s.(error) = false ->
    s' = fst (run_program_stream' p start_stream (start_state p) (S fuel)) ->
    s'.(error) = false.
Proof.
  intros. assert (Hwell := H).
  pose proof run_program_stream_equiv as Hequiv.
  specialize Hequiv with p start_stream (start_state p) fuel s istream.
  apply Hequiv in H.
  - rewrite H in H5. rewrite H5. induction istream.
    + unfold run_program_stream'.
      case (error s || exit s)%bool. assumption. assumption.
    + unfold run_program_stream'. case (error s || exit s)%bool. assumption.
      destruct (get_next_instrs p (cfg a) (node a) (instr a) s 1).
      destruct r. auto. admit.
      remember (run_instr p (instr a) s) as s''.

      assert ((fst (if (error s'' || exit s'')%bool
                        then (s'', l ++ istream)
                        else (set_exit_state s'', l ++ istream))) =
                  (if (error s'' || exit s'')%bool
                   then s''
                   else set_exit_state s'')) as Hdist.
      case (error s'' || exit s'')%bool; auto.

      rewrite Hdist.
      pose proof distribute_error as Herr.
      specialize Herr with (error s'' || exit s'')%bool s'' (set_exit_state s'').
      rewrite Herr.
      pose proof error_set_exit as Hexit. specialize Hexit with s''. symmetry in Hexit.
      rewrite Hexit.
      pose proof if_eq as Hif. specialize Hif with bool (error s'' || exit s'')%bool (error s'').
      rewrite Hif. rewrite Heqs''.
      remember (instr a) as instr_a.
      destruct instr_a; auto.
      * pose proof verified_heap_read as Hinstr.
        specialize Hinstr with p s (a :: istream) fuel a r r0 r1.
        assert (instr a = Heap_Read r r0 r1). symmetry in Heqinstr_a. assumption.
        rewrite H6 in Hinstr. apply Hinstr; auto. pose proof prog_stream_eq.
        specialize H7 with p fuel start_stream.
        symmetry in H7. rewrite H7 in H3. assumption. assumption. symmetry in H2. assumption.
      * pose proof verified_heap_write as Hinstr.
        specialize Hinstr with p s (a :: istream) fuel a r r0 r1.
        assert (instr a = Heap_Write r r0 r1). symmetry in Heqinstr_a. assumption.
        rewrite H6 in Hinstr. apply Hinstr; auto. pose proof prog_stream_eq.
        specialize H7 with p fuel start_stream.
        symmetry in H7. rewrite H7 in H3. assumption. assumption. symmetry in H2. assumption.
      * simpl. destruct (function_lookup p (get_register s r)); auto.
      * pose proof verified_stack_contract as Hinstr.
        specialize Hinstr with p s (a :: istream) fuel a n.
        assert (instr a = Stack_Contract n). symmetry in Heqinstr_a. assumption.
        rewrite H6 in Hinstr. apply Hinstr; auto. pose proof prog_stream_eq.
        specialize H7 with p fuel start_stream.
        symmetry in H7. rewrite H7 in H3. assumption. assumption. symmetry in H2. assumption.
      * pose proof verified_stack_read as Hinstr.
        specialize Hinstr with p s (a :: istream) fuel a r n.
        assert (instr a = Stack_Read r n). symmetry in Heqinstr_a. assumption.
        rewrite H6 in Hinstr. apply Hinstr; auto. pose proof prog_stream_eq.
        specialize H7 with p fuel start_stream.
        symmetry in H7. rewrite H7 in H3. assumption. assumption. symmetry in H2. assumption.
      * pose proof verified_stack_write as Hinstr.
        specialize Hinstr with p s (a :: istream) fuel a n r.
        assert (instr a = Stack_Write n r). symmetry in Heqinstr_a. assumption.
        rewrite H6 in Hinstr. apply Hinstr; auto. pose proof prog_stream_eq.
        specialize H7 with p fuel start_stream.
        symmetry in H7. rewrite H7 in H3. assumption. assumption. symmetry in H2. assumption.
  - assumption.
Admitted.

Theorem get_instrs_till_terminal_ret :
  forall cfg n fuel,
    snd (get_instrs_till_terminal cfg n fuel) = normal_return ->
    get_instrs_till_terminal cfg n fuel = get_instrs_till_terminal cfg n (S fuel).
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


  destruct (get_instrs_till_terminal (fst (main p)) (start_node (fst (main p))) fuel) eqn:Htest.
  (*
  assert (l = fst (get_instrs_till_terminal (fst (main p)) (start_node (fst (main p))) fuel)). admit.
  assert (r = snd (get_instrs_till_terminal (fst (main p)) (start_node (fst (main p))) fuel)). admit.
  *)
  (* TODO: I don't know why the context forgets this information *)
  unfold snd in H1. destruct r. auto. contradiction.
  induction fuel.
  simpl. reflexivity.
  pose proof function_safety_run_other as Hstream'.
  remember (run_program_stream' p l (start_state p) fuel) as s.
  remember (run_program_stream' p l (start_state p) (S fuel)) as s'.
  specialize Hstream' with p (fst (run_program_stream' p l (start_state p) fuel)) (snd s) fuel l (fst s').
  pose proof get_instrs_till_terminal_ret as Hget. (*assert (r = normal_return). admit.*)
  specialize Hget with (fst (main p)) (start_node (fst (main p))) fuel. symmetry in Hget.
  apply Hstream'; auto.
  - rewrite Hget. admit. admit.
  - rewrite Hget. admit. admit.
  - pose proof tuple_eq as Htup. specialize Htup with (run_program_stream' p l (start_state p) fuel).
    rewrite Heqs. rewrite Htup. auto.
  - admit.
  - pose proof tuple_eq' as Htup'. specialize Htup' with s' (run_program_stream' p l (start_state p) (S fuel)).
    apply Htup' in Heqs'. inversion Heqs'. assumption.
Admitted.


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
