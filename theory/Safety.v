Require Import VerifiedVerifier.Machine.
Require Import VerifiedVerifier.Maps.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import VerifiedVerifier.BinaryLattice.
Require Import VerifiedVerifier.AbstractAnalysis.
Require Import VerifiedVerifier.Semantics.
Require Import VerifiedVerifier.Coqlib.
Require Import Lia.

Definition is_heap_base_data (s : state) (i : data_ty) : BinarySet :=
if (Nat.eqb i s.(heap_base)) then bottom else top.

Definition is_heap_bounded_data (s : state) (i : data_ty) : BinarySet :=
if (ltb i (above_heap_guard_size s)) then bottom else top.

Definition is_cf_bounded_data (s : state) (i : data_ty) : BinarySet :=
if (ltb i (List.length (program s).(Funs))) then bottom else top.

Definition is_globals_base_data (s : state) (i : data_ty) : BinarySet :=
if (Nat.eqb i s.(globals_base)) then bottom else top.

Definition is_above_stack_bounded_data (s : state) (i : data_ty) : BinarySet :=
if (Nat.eqb i (above_stack_guard_size s)) then bottom else top.

Definition is_below_stack_bounded_data (s : state) (i : data_ty) : BinarySet :=
if (Nat.eqb i (below_stack_guard_size s)) then bottom else top.

Definition abstractify_data (s : state) (i : data_ty) : info :=
{| is_heap_base := is_heap_base_data s i;
   heap_bounded := is_heap_bounded_data s i;
   cf_bounded := is_cf_bounded_data s i;
   is_globals_base := is_globals_base_data s i;
   above_stack_bounded := is_above_stack_bounded_data s i;
   below_stack_bounded := is_below_stack_bounded_data s i;
|}.

Definition abstractify_list (s : state) (l : list data_ty) : list info :=
  map (abstractify_data s) l.

Definition abstractify_registers (s : state) (f : registers_ty) : abs_registers_ty :=
  fun r => (abstractify_data s (f r)).

Definition abstractify (s : state) : abs_state :=
{| abs_regs := abstractify_registers s s.(regs);
   abs_stack := abstractify_list s s.(stack);
   abs_lifted_state := sub_state;
   abs_heap_base := (heap_base s);
   abs_below_stack_guard_size := (below_stack_guard_size s);
   abs_above_stack_guard_size := (above_stack_guard_size s);
   abs_above_heap_guard_size := (above_heap_guard_size s);
   abs_globals_size := (globals_size s);
   abs_globals_base := (globals_base s);
   abs_program := Some s.(program);
   abs_frame_size := s.(frame_size);
   abs_call_stack := s.(call_stack);
   abs_rsp := get_register s rsp;
   abs_stack_base := s.(stack_base);
   abs_stack_size := s.(stack_size);
   abs_max_stack_size := s.(max_stack_size);
|}.

Lemma BinarySet_eqb_eq: forall a b,
  BinarySet_eqb a b = true <-> a = b.
Proof.
  intros. split.
  - intros. unfold BinarySet_eqb in H. destruct (BinarySet_eq_dec a b) eqn:H'; auto; inversion H.
  - intros. unfold BinarySet_eqb. inversion H. destruct (BinarySet_eq_dec b b); auto; inversion H.
Qed.

Lemma leq_abs_state_is_heap_base: forall abs_st abs_st' r,
  leq_abs_state abs_st' abs_st ->
  is_heap_base (get_register_info abs_st r) = bottom ->
  is_heap_base (get_register_info abs_st' r) = bottom.
Proof.
  intros abs_st abs_st' r Hleq H. inversion Hleq. auto. subst. inversion H. subst.
  specialize H6 with r. inversion H6. rewrite H20. auto.
  subst. inversion H18. auto. rewrite H in H18. inversion H18. auto.
Qed.

Lemma leq_abs_state_is_globals_base: forall abs_st abs_st' r,
  leq_abs_state abs_st' abs_st ->
  is_globals_base (get_register_info abs_st r) = bottom ->
  is_globals_base (get_register_info abs_st' r) = bottom.
Proof.
  intros abs_st abs_st' r Hleq H. inversion Hleq. auto. subst. inversion H. subst.
  specialize H6 with r. inversion H6. rewrite H20. auto.
  subst. inversion H21. auto. rewrite H in H21. inversion H21. auto.
Qed.

Lemma leq_abs_state_heap_bounded: forall abs_st abs_st' r,
  leq_abs_state abs_st' abs_st ->
  heap_bounded (get_register_info abs_st r) = bottom ->
  heap_bounded (get_register_info abs_st' r) = bottom.
Proof.
  intros abs_st abs_st' r Hleq H. inversion Hleq. auto. subst. inversion H. subst.
  specialize H6 with r. inversion H6. rewrite H20. auto.
  subst. inversion H19. auto. rewrite H in H19. inversion H19. auto.
Qed.

Lemma leq_abs_state_cf_bounded: forall abs_st abs_st' r,
  leq_abs_state abs_st' abs_st ->
  cf_bounded (get_register_info abs_st r) = bottom ->
  cf_bounded (get_register_info abs_st' r) = bottom.
Proof.
  intros abs_st abs_st' r Hleq H. inversion Hleq. auto. subst. inversion H. subst.
  specialize H6 with r. inversion H6. rewrite H20. auto.
  subst. inversion H20. auto. rewrite H in H20. inversion H20. auto.
Qed.

Lemma if_thn_true: forall (cond : bool),
  (if cond then bottom else top) = bottom ->
  cond = true.
Proof.
  intros. destruct cond; auto; inversion H.
Qed.

Definition first_block f :=
match (V f) with
| nil => nil
| h :: t => h
end.

Definition run_function p f :=
(first_block f, start_state p).

Lemma leq_abs_state_verifies : forall i abs_st abs_st',
  leq_abs_state abs_st' abs_st ->
  instr_class_verifier i abs_st = true ->
  instr_class_verifier i abs_st' = true.
Proof.
  intros i abs_st abs_st' Hleq Hv. inversion Hleq. auto. rewrite <- H0 in Hv. inversion Hv.
  destruct i eqn:Hi; unfold instr_class_verifier in *; rewrite H0 in Hv; rewrite H; eauto.
  - apply andb_prop in Hv as [Hbase Hv].
    apply andb_prop in Hv as [Hindex Hoffset]. apply BinarySet_eqb_eq in Hbase. apply BinarySet_eqb_eq in Hindex.
    apply BinarySet_eqb_eq in Hoffset. repeat (apply andb_true_intro; split; try (apply BinarySet_eqb_eq)).
    + eapply leq_abs_state_is_heap_base. apply Hleq. auto.
    + eapply leq_abs_state_heap_bounded. apply Hleq. auto.
    + eapply leq_abs_state_heap_bounded. apply Hleq. auto.
  - apply andb_prop in Hv as [Hbase Hv].
    apply andb_prop in Hv as [Hindex Hoffset]. apply BinarySet_eqb_eq in Hbase. apply BinarySet_eqb_eq in Hindex.
    apply BinarySet_eqb_eq in Hoffset. repeat (apply andb_true_intro; split; try (apply BinarySet_eqb_eq)).
    + eapply leq_abs_state_is_heap_base. apply Hleq. auto.
    + eapply leq_abs_state_heap_bounded. apply Hleq. auto.
    + eapply leq_abs_state_heap_bounded. apply Hleq. auto.
  - apply andb_prop in Hv. destruct Hv as [Hv1 Hv3]. apply PeanoNat.Nat.ltb_lt in Hv3.
    apply andb_prop in Hv1. destruct Hv1 as [Hv1 Hv2].
    apply PeanoNat.Nat.ltb_lt in Hv1. apply PeanoNat.Nat.ltb_lt in Hv2.
    repeat (apply andb_true_intro; split; try (apply BinarySet_eqb_eq)); apply PeanoNat.Nat.ltb_lt.
    + rewrite H2. rewrite H7. assumption.
    + rewrite H12. rewrite H11. assumption.
    + rewrite H11. rewrite H12. rewrite H13. assumption.
  - apply andb_prop in Hv. destruct Hv as [Hv1 Hv3]. apply PeanoNat.Nat.ltb_lt in Hv3.
    apply andb_prop in Hv1. destruct Hv1 as [Hv1 Hv2].
    apply PeanoNat.Nat.ltb_lt in Hv1. apply PeanoNat.Nat.ltb_lt in Hv2.
    repeat (apply andb_true_intro; split; try (apply BinarySet_eqb_eq)); apply PeanoNat.Nat.ltb_lt.
    + rewrite H7. assumption.
    + rewrite H12. rewrite H11. assumption.
    + rewrite H11. rewrite H12. rewrite H14. assumption.
  - apply andb_prop in Hv. destruct Hv as [Hv1 Hv2].
    apply BinarySet_eqb_eq in Hv1. apply BinarySet_eqb_eq in Hv2.
    repeat (apply andb_true_intro; split; try (apply BinarySet_eqb_eq)).
    + specialize H5 with r. inversion H5.
      * rewrite H21. assumption.
      * inversion H21; auto.
        rewrite Hv1 in H27. discriminate.
    + specialize H5 with rdi. inversion H5.
      * rewrite H21. assumption.
      * inversion H19; auto.
        rewrite Hv2 in H27. discriminate.
  - apply andb_prop in Hv. destruct Hv as [Hv1 Hv2]. apply BinarySet_eqb_eq in Hv2.
    repeat (apply andb_true_intro; split; try (apply BinarySet_eqb_eq)).
    + unfold AbstractAnalysis.get_function in *. rewrite H8. assumption.
    + specialize H5 with rdi. inversion H5.
      * rewrite H21. assumption.
      * inversion H19; auto.
        rewrite Hv2 in H27. discriminate.
  - apply andb_prop in Hv. destruct Hv as [Hv1 Hv2].
    repeat (apply andb_true_intro; split).
    + unfold get_bb. unfold AbstractAnalysis.get_function.
      unfold get_bb in Hv1. unfold AbstractAnalysis.get_function in Hv1.
      rewrite H8. rewrite H10. assumption.
    + unfold get_bb. unfold AbstractAnalysis.get_function.
      unfold get_bb in Hv2. unfold AbstractAnalysis.get_function in Hv2.
      rewrite H8. rewrite H10. assumption.
  - unfold get_bb in *. unfold AbstractAnalysis.get_function in *.
    rewrite H8. rewrite H10. assumption.
  - apply BinarySet_eqb_eq. apply BinarySet_eqb_eq in Hv.
    eapply leq_abs_state_is_heap_base. eapply Hleq. auto.
  - apply andb_prop in Hv. destruct Hv as [Hv1 Hv2]. apply BinarySet_eqb_eq in Hv1.
    apply PeanoNat.Nat.ltb_lt in Hv2. apply andb_true_intro; split.
    + apply BinarySet_eqb_eq. pose proof leq_abs_state_is_globals_base as Hglobal.
      specialize Hglobal with abs_st abs_st' r.
      apply Hglobal; auto.
    + apply PeanoNat.Nat.ltb_lt. rewrite H15. auto.
  - apply andb_prop in Hv. destruct Hv as [Hv1 Hv2]. apply BinarySet_eqb_eq in Hv1.
    apply PeanoNat.Nat.ltb_lt in Hv2. apply andb_true_intro; split.
    + apply BinarySet_eqb_eq. pose proof leq_abs_state_is_globals_base as Hglobal.
      specialize Hglobal with abs_st abs_st' r.
      apply Hglobal; auto.
    + apply PeanoNat.Nat.ltb_lt. rewrite H15. auto.
Qed.

Lemma unfold_binaryset_eqb: forall b1 b2 b3 b4,
  (BinarySet_eqb b1 b2 && BinarySet_eqb b3 b4)%bool = true ->
  b1 = b2 /\ b3 = b4.
Proof.
  intros. apply andb_prop in H as [H1 H2].
  apply BinarySet_eqb_eq in H1. apply BinarySet_eqb_eq in H2. auto.
Qed.

Lemma unfold_binaryset_eqb_3: forall b1 b2 b3 b4 b5 b6,
  (BinarySet_eqb b1 b2 && BinarySet_eqb b3 b4 && BinarySet_eqb b5 b6)%bool = true ->
  b1 = b2 /\ b3 = b4 /\ b5 = b6.
Proof.
  intros. apply andb_prop in H as [H1 H2]. apply unfold_binaryset_eqb in H1 as [H1 H1'].
  apply BinarySet_eqb_eq in H2. auto.
Qed.

Theorem get_function_concrete_abstract :
  forall s n f,
    Semantics.get_function s n = Some f ->
    AbstractAnalysis.get_function (abstractify s) n = Some f.
Proof.
  intros. unfold AbstractAnalysis.get_function. unfold get_function in H.
  unfold abstractify. unfold abs_program. apply H.
Qed.

Theorem get_function_abstract_concrete :
  forall s n f,
    AbstractAnalysis.get_function (abstractify s) n = Some f ->
    Semantics.get_function s n = Some f.
Proof.
  intros. unfold AbstractAnalysis.get_function in H. unfold get_function.
  unfold abstractify in H. unfold abs_program in H. apply H.
Qed.

Theorem get_bb_abstract_concrete :
  forall s n bb,
    get_bb (abstractify s) n = Some bb ->
    get_basic_block s n = Some bb.
Proof.
  intros. unfold get_basic_block. unfold get_bb in H. unfold abstractify in H.
  unfold abs_call_stack in H. unfold AbstractAnalysis.get_function in H.
  unfold abs_program in H. unfold get_function. apply H.
Qed.

Lemma verified_impl_istep : forall i is st,
  instr_class_verifier i.(instr) (abstractify st) = true ->
  exists is' st', (i :: is) / st i--> is' / st'.
Proof.
  intros. destruct i eqn:Hibase; destruct instr eqn:Hi; unfold instr_class_verifier in H; simpl in H.
  - apply andb_prop in H as [Hbase Hv]. apply andb_prop in Hv as [Hindex Hoffset].
    apply BinarySet_eqb_eq in Hbase. apply BinarySet_eqb_eq in Hindex.
    apply BinarySet_eqb_eq in Hoffset.
    remember ((get_register st r2) + (get_register st r1) + (get_register st r0)) as index.
    remember (ltb index ((heap_base st) + (max_heap_size st))) as valid_index.
    destruct valid_index.
    + apply eq_sym, PeanoNat.Nat.ltb_lt in Heqvalid_index. repeat eexists. eapply I_Heap_Read.
      apply Heqindex. unfold is_heap_base, get_register_info, abstractify in *. simpl in *.
      unfold is_heap_base_data, is_heap_bounded_data in *.
      apply if_thn_true, EqNat.beq_nat_true in Hbase. Search (_ <? _).
      apply if_thn_true, PeanoNat.Nat.ltb_lt in Hindex. apply if_thn_true, PeanoNat.Nat.ltb_lt in Hoffset.
      unfold get_register in *. lia. auto.
    + Search (_ <? _). apply eq_sym, PeanoNat.Nat.ltb_nlt in Heqvalid_index. repeat eexists. eapply I_Heap_Read_Guard.
      apply Heqindex. lia. unfold is_heap_base, get_register_info, abstractify in *. simpl in *.
      unfold is_heap_base_data, is_heap_bounded_data in *.
      apply if_thn_true, EqNat.beq_nat_true in Hbase. Search (_ <? _).
      apply if_thn_true, PeanoNat.Nat.ltb_lt in Hindex. apply if_thn_true, PeanoNat.Nat.ltb_lt in Hoffset.
      unfold get_register in *. pose proof (heap_size_eq_guard st) as H. lia.
  - apply andb_prop in H as [Hbase Hv]. apply andb_prop in Hv as [Hindex Hoffset].
    apply BinarySet_eqb_eq in Hbase. apply BinarySet_eqb_eq in Hindex.
    apply BinarySet_eqb_eq in Hoffset.
    remember ((get_register st r) + (get_register st r0) + (get_register st r1)) as index.
    remember (ltb index ((heap_base st) + (max_heap_size st))) as valid_index.
    destruct valid_index.
    + apply eq_sym, PeanoNat.Nat.ltb_lt in Heqvalid_index. repeat eexists. eapply I_Heap_Write.
      auto. unfold is_heap_base, get_register_info, abstractify in *. simpl in *.
      unfold is_heap_base_data, is_heap_bounded_data in *.
      apply if_thn_true, EqNat.beq_nat_true in Hbase. Search (_ <? _).
      apply if_thn_true, PeanoNat.Nat.ltb_lt in Hindex. apply if_thn_true, PeanoNat.Nat.ltb_lt in Hoffset.
      unfold get_register in *. lia. lia.
    + Search (_ <? _). apply eq_sym, PeanoNat.Nat.ltb_nlt in Heqvalid_index. repeat eexists. eapply I_Heap_Write_Guard.
      auto. lia. unfold is_heap_base, get_register_info, abstractify in *. simpl in *.
      unfold is_heap_base_data, is_heap_bounded_data in *.
      apply if_thn_true, EqNat.beq_nat_true in Hbase. Search (_ <? _).
      apply if_thn_true, PeanoNat.Nat.ltb_lt in Hindex. apply if_thn_true, PeanoNat.Nat.ltb_lt in Hoffset.
      unfold get_register in *. pose proof (heap_size_eq_guard st) as H. lia.
  - repeat eexists. apply I_Heap_Check.
  - destruct (get_register st r <? List.length (program st).(Funs)) eqn:valid_function.
    + repeat eexists. eapply I_Call_Check. apply PeanoNat.Nat.ltb_lt. auto.
    + repeat eexists. eapply I_Call_Check_Bad. apply PeanoNat.Nat.ltb_nlt in valid_function. apply Compare_dec.not_lt. auto.
  - repeat eexists. apply I_Reg_Move.
  - repeat eexists. apply I_Reg_Write.
  - repeat eexists. apply I_Stack_Expand_Static.
  - destruct (n + (stack_size st) <=? (max_stack_size st)) eqn:valid_expansion.
    + repeat eexists. eapply I_Stack_Expand_Dynamic. Search (_ <=? _). apply Compare_dec.leb_complete. auto.
    + repeat eexists. eapply I_Stack_Expand_Dynamic_Guard. apply Compare_dec.leb_complete_conv. auto.
  - repeat eexists. apply I_Stack_Contract.
  - repeat eexists. apply andb_prop in H. destruct H. apply andb_prop in H. destruct H.
    apply PeanoNat.Nat.ltb_lt in H. apply PeanoNat.Nat.ltb_lt in H1. apply PeanoNat.Nat.ltb_lt in H0.
    apply I_Stack_Read; auto.
  - repeat eexists. apply andb_prop in H. destruct H. apply andb_prop in H. destruct H.
    apply PeanoNat.Nat.ltb_lt in H. apply PeanoNat.Nat.ltb_lt in H1. apply PeanoNat.Nat.ltb_lt in H0.
    apply I_Stack_Write; auto.
  - repeat eexists. apply I_Op.
  - apply andb_prop in H as [Hcf Hheap]. apply BinarySet_eqb_eq in Hcf. apply BinarySet_eqb_eq in Hheap.
    unfold is_cf_bounded_data in Hcf. unfold is_heap_base_data in Hheap.
    apply if_thn_true in Hcf. apply if_thn_true in Hheap. apply PeanoNat.Nat.ltb_lt in Hcf.
    pose proof Coqlib.nth_error_lt as Hnth.
    specialize Hnth with ControlFlowGraph (get_register st r) (Funs (program st)).
    unfold get_register in Hnth. apply Hnth in Hcf. destruct Hcf.
    repeat eexists. apply I_Indirect_Call. unfold get_function. apply H.
  - apply andb_prop in H. destruct H.
    destruct (AbstractAnalysis.get_function (abstractify st) n) eqn: Hget.
    pose proof get_function_abstract_concrete as Habs.
    specialize Habs with st n f. apply Habs in Hget.
    repeat eexists. apply I_Direct_Call. apply Hget. inversion H.
  - case (run_conditional st c) eqn:Hcond.
    + apply andb_prop in H. destruct H. destruct (get_bb (abstractify st) l) eqn:Hget1; try inversion H.
      destruct (get_bb (abstractify st) l0) eqn:Hget2; try inversion H0.
      pose proof I_Branch_True. specialize H1 with st is c l l0 b b0 addr.
      repeat eexists. apply H1; auto.
    + apply andb_prop in H. destruct H. destruct (get_bb (abstractify st) l) eqn:Hget1; try inversion H.
      destruct (get_bb (abstractify st) l0) eqn:Hget2; try inversion H0.
      pose proof I_Branch_False. specialize H1 with st is c l l0 b b0 addr.
      repeat eexists. apply H1; auto.
  - destruct (get_bb (abstractify st) l) eqn: Hget; try inversion H.
    pose proof get_bb_abstract_concrete as Habs.
    specialize Habs with st l b. apply Habs in Hget.
    repeat eexists. apply I_Jmp. apply Hget.
  - apply BinarySet_eqb_eq in H. repeat eexists. eapply I_Get_Globals_Base.
    unfold is_heap_base_data in H. destruct (regs st r =? heap_base st) eqn:Hbase.
    + apply EqNat.beq_nat_true in Hbase. auto.
    + discriminate.
  - apply andb_prop in H as [Hbase Hindex]. apply BinarySet_eqb_eq in Hbase.
    apply PeanoNat.Nat.ltb_lt in Hindex. repeat eexists. eapply I_Globals_Read.
    unfold is_globals_base_data in Hbase. destruct (regs st r =? globals_base st) eqn:Hglobal.
    + apply EqNat.beq_nat_true in Hglobal. auto.
    + discriminate.
    + auto.
  - apply andb_prop in H as [Hbase Hindex]. apply BinarySet_eqb_eq in Hbase.
    apply PeanoNat.Nat.ltb_lt in Hindex. repeat eexists. eapply I_Globals_Write.
    unfold is_globals_base_data in Hbase. destruct (regs st r =? globals_base st) eqn:Hglobal.
    + apply EqNat.beq_nat_true in Hglobal. auto.
    + discriminate.
    + auto.
  - repeat eexists. apply I_Ret. apply EqNat.beq_nat_true in H. assumption.
Qed.

Lemma verified_program_impl_verified_function : forall p f,
  program_verifier p (abstractify (start_state p)) = true ->
  In f p.(Funs) ->
  function_verifier f (abstractify (start_state p)) = true.
Proof.
  intros. unfold program_verifier in H. rewrite forallb_forall in H.
  specialize H with f. apply H. apply H0.
Qed.

(* NOTE: This is, in general, a true statement about abstract analyses. It is
   admitted here because we assume the abstract analysis is implemented
   correctly and instead focus on proving facts about whether or not we have
   enough information to guarantee sfi properties. *)
(* TODO: update this to use the verifier fixpoint when we update the verifier
   to associate fixpoints with functions. *)
Theorem verifier_fixpoint_relation :
forall i,
  exists fixpoint,
  forall p f is st fuel,
    program_verifier p (abstractify (start_state p)) = true ->
    In f p.(Funs) ->
    imultistep_fuel ((run_function p f), fuel) (i :: is, st, 0) ->
    (leq_abs_state (abstractify st) fixpoint /\
     instr_class_verifier i.(instr) fixpoint = true).
Admitted.

Theorem verified_program_step :
  forall p f fuel is1 st1,
    program_verifier p (abstractify (start_state p)) = true ->
    In f p.(Funs) ->
    imultistep_fuel ((run_function p f), fuel) (is1, st1, 0) ->
    exists is' st',
      imultistep_fuel ((run_function p f), S fuel) (is', st', 0).
Proof.
  intros.
  unfold run_function. unfold run_function in H1.
  pose proof imultistep_finish' as Hfinish.
  destruct (first_block f) eqn:Hfirst.
  - repeat eexists. constructor. apply IFuel_End.
  - destruct is1 eqn:Hstream.
    + exists nil. exists st1.
      eapply imultistep_finish'. apply H1.
      constructor. apply IFuel_End.
    + pose proof verified_impl_istep as Hstep.
      specialize Hstep with i0 l0 st1.
      pose proof verifier_fixpoint_relation as Hfixpoint.
      specialize Hfixpoint with i0. destruct Hfixpoint as [fixpoint Hfixpoint].
      pose proof leq_abs_state_verifies as Hleq.
      specialize Hleq with i0.(instr) fixpoint (abstractify st1).
      specialize Hfixpoint with p f l0 st1 fuel.
      apply Hfixpoint in H as [].
      apply Hleq in H.
      apply Hstep in H. rewrite <- Hstream in H. destruct H as []. destruct H as [].
      eexists ?[is']. eexists ?[st'].
      specialize Hfinish with fuel (first_block f) (start_state p) is1 st1 ?is' ?st'.
      rewrite <- Hfirst. apply Hfinish. rewrite Hfirst. rewrite Hstream. apply H1.
      constructor. apply IFuel_Step.
      apply H.
      auto. auto. auto.
      unfold run_function. rewrite Hfirst. apply H1.
Qed.

Theorem verified_program :
  forall p f fuel,
    program_verifier p (abstractify (start_state p)) = true ->
    In f p.(Funs) ->
    exists is' st',
      imultistep_fuel ((run_function p f), fuel) (is', st', 0).
Proof.
  intros. induction fuel.
  - repeat eexists. constructor. apply IFuel_Base.
  - destruct IHfuel. destruct H1.
    eapply verified_program_step; auto.
    eapply H1.
Qed.
