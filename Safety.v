Require Import VerifiedVerifier.Machine.
Require Import VerifiedVerifier.Bits.
Require Import VerifiedVerifier.Maps.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import VerifiedVerifier.BinaryLattice.
Require Import VerifiedVerifier.AbstractAnalysis.
Require Import VerifiedVerifier.Semantics.
Require Import Lia.

Definition is_heap_base_data (s : state) (i : data_ty) : BinarySet :=
if (eqb i s.(heap_base)) then bottom else top.

Definition is_heap_bounded_data (s : state) (i : data_ty) : BinarySet :=
if (ltb i (above_heap_guard_size s)) then bottom else top.

Definition is_cf_bounded_data (s : state) (i : data_ty) : BinarySet :=
if (ltb i (List.length (prog s))) then bottom else top.

Definition is_above_stack_bounded_data (s : state) (i : data_ty) : BinarySet :=
if (eqb i (above_stack_guard_size s)) then bottom else top.

Definition is_below_stack_bounded_data (s : state) (i : data_ty) : BinarySet :=
if (eqb i (below_stack_guard_size s)) then bottom else top.

Definition abstractify_data (s : state) (i : data_ty) : info :=
{| is_heap_base := is_heap_base_data s i;
   heap_bounded := is_heap_bounded_data s i;
   cf_bounded := is_cf_bounded_data s i; 
   above_stack_bounded := is_above_stack_bounded_data s i;
   below_stack_bounded := is_below_stack_bounded_data s i;
|}.

Definition abstractify_list (s : state) (l : list data_ty) : list info :=
  map (abstractify_data s) l.

Definition abstractify_registers (s : state) (f : registers_ty) : abs_registers_ty :=
  fun r => (abstractify_data s (f r)).

Fixpoint firstn_default {A} (n:nat)(l:list A) (d : A) : list A :=
match n with
| 0 => nil
| S n => match l with
  | nil => repeat d (S n)
  | a::l => a::(firstn_default n l d)
  end
end.

Lemma firstn_default_len: forall A n l (d: A),
  length (firstn_default n l d) = n.
Proof.
  intros. generalize dependent l. induction n.
  - intros. auto.
  - intros. destruct l. simpl. rewrite repeat_length. auto. 
    simpl. rewrite IHn. auto.
Qed.

Definition abstractify (s : state) : abs_state :=
if (andb (eqb (get_register s rsp) ((stack_base s) + (stack_size s))) ((frame_size s) <=? (stack_size s)))
then
{| abs_regs := abstractify_registers s s.(regs);
   abs_stack := abstractify_list s (firstn_default (frame_size s) s.(stack) 0);
   abs_lifted_state := sub_state;
   abs_heap_base := (heap_base s);
   abs_below_stack_guard_size := (below_stack_guard_size s);
   abs_above_stack_guard_size := (above_stack_guard_size s);
   abs_above_heap_guard_size := (above_heap_guard_size s);
   abs_prog := (prog s);
   abs_func := (func s);
|} else top_abs_state.

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
  specialize H8 with r. inversion H8. rewrite H13. auto.
  subst. inversion H11. auto. rewrite H in H11. inversion H11. auto.
Qed.

Lemma leq_abs_state_heap_bounded: forall abs_st abs_st' r,
  leq_abs_state abs_st' abs_st ->
  heap_bounded (get_register_info abs_st r) = bottom ->
  heap_bounded (get_register_info abs_st' r) = bottom.
Proof.
  intros abs_st abs_st' r Hleq H. inversion Hleq. auto. subst. inversion H. subst.
  specialize H8 with r. inversion H8. rewrite H13. auto.
  subst. inversion H12. auto. rewrite H in H12. inversion H12. auto.
Qed.

Lemma leq_abs_state_cf_bounded: forall abs_st abs_st' r,
  leq_abs_state abs_st' abs_st ->
  cf_bounded (get_register_info abs_st r) = bottom ->
  cf_bounded (get_register_info abs_st' r) = bottom.
Proof.
  intros abs_st abs_st' r Hleq H. inversion Hleq. auto. subst. inversion H. subst.
  specialize H8 with r. inversion H8. rewrite H13. auto.
  subst. inversion H13. auto. rewrite H in H13. inversion H13. auto.
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
  - repeat apply andb_prop in Hv as [Hv].
    apply BinarySet_eqb_eq in Hv.
    apply BinarySet_eqb_eq in H14.
    apply BinarySet_eqb_eq in H13.
    repeat (apply andb_true_intro; split; try (apply BinarySet_eqb_eq)).
    + eapply leq_abs_state_is_heap_base. apply Hleq. auto.
    + eapply leq_abs_state_heap_bounded. apply Hleq. auto.
    + eapply leq_abs_state_heap_bounded. apply Hleq. auto.
    + auto. 
  - repeat apply andb_prop in Hv as [Hv].
    apply BinarySet_eqb_eq in Hv.
    apply BinarySet_eqb_eq in H13.
    apply BinarySet_eqb_eq in H12.
    repeat (apply andb_true_intro; split; try (apply BinarySet_eqb_eq)).
    + eapply leq_abs_state_is_heap_base. apply Hleq. auto.
    + eapply leq_abs_state_heap_bounded. apply Hleq. auto.
    + eapply leq_abs_state_heap_bounded. apply Hleq. auto.
  - apply andb_prop in Hv as [Hr Hdst]. apply andb_true_intro; split; eauto.
  - apply andb_prop in Hv as [Hr Hrdi]. apply BinarySet_eqb_eq in Hr. apply BinarySet_eqb_eq in Hrdi.
    apply andb_true_intro; split; apply BinarySet_eqb_eq.
    * eapply leq_abs_state_cf_bounded. apply Hleq. apply Hr.
    * eapply leq_abs_state_is_heap_base. apply Hleq. apply Hrdi.
  - apply andb_prop in Hv as [Hindex Hrdi]. apply BinarySet_eqb_eq in Hrdi. apply andb_true_intro; split; try apply BinarySet_eqb_eq.
    rewrite H5. auto. eapply leq_abs_state_is_heap_base.
    apply Hleq. auto.
  - rewrite <- H6 in Hv. auto.
  - rewrite <- H6 in Hv. auto.
Qed.

Definition safe_instr_class (i : instr_class) (st : state) : Prop :=
(* I'm not sure what the right implementation is here *)
(* we might need to add a match for every top=>false bot=>true *)
match i with
| Heap_Read _ r_dst r_offset r_index r_base =>
  (get_register st r_base) = (heap_base st) /\
  (get_register st r_index) < (above_heap_guard_size st) /\
  (get_register st r_offset) < (above_heap_guard_size st) /\
  r_dst <> rsp
| Heap_Write _ r_offset r_index r_base _ =>
  (get_register st r_base) = (heap_base st) /\
  (get_register st r_index) < (above_heap_guard_size st) /\
  (get_register st r_offset) < (above_heap_guard_size st) 
| Heap_Check _ r_src => 
  r_src <> rsp
| Call_Check _ _ => 
  True
| Reg_Move _ r_dst _ => 
  r_dst <> rsp
| Reg_Write _ r_dst _ =>
  r_dst <> rsp
| Stack_Expand_Static _ i => 
  i <= (above_stack_guard_size st)
| Stack_Expand_Dynamic _ i =>
  True
| Stack_Contract _ i =>
  i <= (frame_size st)
| Stack_Read _ r_dst i =>
  (get_register st rsp) = (stack_base st) + (stack_size st) /\
  i <= (frame_size st) + (below_stack_guard_size st) /\
  r_dst <> rsp /\
  frame_size st <= stack_size st 
| Stack_Write _ i _ =>
  (get_register st rsp) = (stack_base st) + (stack_size st) /\
  i < (frame_size st)
| Op _ _ rs_dst _ =>
  ~ In rsp rs_dst
| Indirect_Call _ reg =>
  (get_register st rdi) = (heap_base st) /\
  (get_register st reg) < (length (prog st))
| Direct_Call _ fname =>
  (get_register st rdi) = (heap_base st) /\
  fname < (length (prog st))
| Branch _ _ t_label f_label =>
  t_label < (length (V (func st))) /\ f_label < (length (V (func st)))
| Jmp _ j_label =>
  j_label < (length (V (func st)))
| Ret _ =>
  (frame_size st) = 0
end.

Lemma verifier_impl_safe_instr: forall st i,
  instr_class_verifier i (abstractify st) = true ->
  safe_instr_class i st.
Proof.
intros. destruct (andb (eqb (get_register st rsp) ((stack_base st) + (stack_size st))) ((frame_size st) <=? (stack_size st))) eqn:Habs.
apply andb_prop in Habs as [Habs Habs']; unfold instr_class_verifier, abstractify in H; rewrite Habs, Habs' in H; simpl in H.
+ destruct i eqn:Hinstr; unfold safe_instr_class; eauto.
  - repeat apply andb_prop in H as [H].
    apply BinarySet_eqb_eq in H.
    apply BinarySet_eqb_eq in H1.
    apply BinarySet_eqb_eq in H2.
    apply Bool.negb_true_iff, register_eqb_false in H0.
    repeat split; eauto. 
    * unfold is_heap_base_data in H. apply if_thn_true, EqNat.beq_nat_true in H. eauto. 
    * unfold is_heap_bounded_data in H2. apply if_thn_true, PeanoNat.Nat.ltb_lt in H2. eauto. 
    * unfold is_heap_bounded_data in H1. apply if_thn_true, PeanoNat.Nat.ltb_lt in H1. eauto.
  - repeat apply andb_prop in H as [H].
    apply BinarySet_eqb_eq in H.
    apply BinarySet_eqb_eq in H1.
    apply BinarySet_eqb_eq in H0.
    repeat split; eauto. 
    * unfold is_heap_base_data in H. apply if_thn_true, EqNat.beq_nat_true in H. eauto. 
    * unfold is_heap_bounded_data in H1. apply if_thn_true, PeanoNat.Nat.ltb_lt in H1. eauto. 
    * unfold is_heap_bounded_data in H0. apply if_thn_true, PeanoNat.Nat.ltb_lt in H0. eauto.
  - apply Bool.negb_true_iff, register_eqb_false in H. eauto.
  - apply Bool.negb_true_iff, register_eqb_false in H. eauto.
  - apply Bool.negb_true_iff, register_eqb_false in H. eauto.
  - apply PeanoNat.Nat.leb_le in H. eauto.
  - unfold abstractify_list in H. apply PeanoNat.Nat.leb_le in H.
    rewrite map_length in H. rewrite firstn_default_len in H. lia.
  - split. apply EqNat.beq_nat_true in Habs. auto. apply andb_prop in H as []. unfold abstractify_list in H.
    apply PeanoNat.Nat.leb_le in H. rewrite map_length in H. rewrite firstn_default_len in H. split. lia. 
    apply Bool.negb_true_iff, register_eqb_false in H0. split; eauto. apply PeanoNat.Nat.leb_le in Habs'. auto.
  - split. apply EqNat.beq_nat_true in Habs. auto. unfold abstractify_list in H. apply PeanoNat.Nat.leb_le in H.
    rewrite map_length in H. rewrite firstn_default_len in H. lia.
  - Search (forallb). rewrite forallb_forall in H. unfold not. intros.
    apply H in H0. inversion H0.
  - apply andb_prop in H as []. apply BinarySet_eqb_eq in H. apply BinarySet_eqb_eq in H0. split.
    * unfold is_heap_base_data in H0. apply if_thn_true, EqNat.beq_nat_true in H0. eauto.
    * unfold is_cf_bounded_data in H. apply if_thn_true, PeanoNat.Nat.ltb_lt in H. eauto.
  - apply andb_prop in H as []. apply BinarySet_eqb_eq in H0. unfold is_heap_base_data in H0. apply if_thn_true, EqNat.beq_nat_true in H0.
    split. eauto. apply PeanoNat.Nat.ltb_lt. auto.
  - apply andb_prop in H as []. apply PeanoNat.Nat.ltb_lt in H. apply PeanoNat.Nat.ltb_lt in H0. eauto.
  - apply PeanoNat.Nat.ltb_lt in H. eauto.
  - unfold abstractify_list in H. apply EqNat.beq_nat_true in H.
    rewrite map_length in H. rewrite firstn_default_len in H. lia.
+ unfold abstractify in H. rewrite Habs in H. inversion H.
Qed.

Lemma safe_instr_always_isteps: forall st i is,
  safe_instr_class i st ->
  exists is' st', (i :: is) / st i--> is' / st'.
Proof.
  intros. unfold safe_instr_class in H. destruct i eqn:Hinstr.
  - destruct H as [Hindex [Hoffset [Hbase Hrsp]]].
    remember ((get_register st r2) + (get_register st r1) + (get_register st r0)) as index.
    destruct (ltb index ((heap_base st) + (max_heap_size st))) eqn:Heqvalid_index.
    + apply PeanoNat.Nat.ltb_lt in Heqvalid_index. repeat eexists. eapply I_Heap_Read; eauto.
      unfold is_heap_base_data, is_heap_bounded_data in *. lia.
    + apply PeanoNat.Nat.ltb_nlt in Heqvalid_index. repeat eexists. eapply I_Heap_Read_Guard; eauto.
      lia. pose proof (heap_size_eq_guard st) as H'. lia.
  - destruct H as [Hindex [Hoffset Hbase]].
    remember ((get_register st r1) + (get_register st r0) + (get_register st r)) as index.
    destruct (ltb index ((heap_base st) + (max_heap_size st))) eqn:Heqvalid_index.
    + apply PeanoNat.Nat.ltb_lt in Heqvalid_index. repeat eexists. eapply I_Heap_Write; eauto.
      unfold is_heap_base_data, is_heap_bounded_data in *. lia.
    + apply PeanoNat.Nat.ltb_nlt in Heqvalid_index. repeat eexists. eapply I_Heap_Write_Guard; eauto.
      lia. pose proof (heap_size_eq_guard st) as H'. lia.
  - repeat eexists. apply I_Heap_Check. auto.
  - destruct (get_register st r <? List.length (prog st)) eqn:valid_function.
    + repeat eexists. eapply I_Call_Check. apply PeanoNat.Nat.ltb_lt. auto.
    + repeat eexists. eapply I_Call_Check_Bad. apply PeanoNat.Nat.ltb_nlt in valid_function. apply Compare_dec.not_lt. auto.
  - repeat eexists. apply I_Reg_Move. auto.
  - repeat eexists. apply I_Reg_Write. auto.
  - repeat eexists. apply I_Stack_Expand_Static.
  - destruct (n + (stack_size st) <=? (max_stack_size st)) eqn:valid_expansion.
    + repeat eexists. eapply I_Stack_Expand_Dynamic. apply Compare_dec.leb_complete. auto.
    + repeat eexists. eapply I_Stack_Expand_Dynamic_Guard. apply Compare_dec.leb_complete_conv. auto.
  - repeat eexists. apply I_Stack_Contract.
  - destruct H as [Hrsp1 [Hindex [Hrsp2 Hframe]]]. remember ((get_register st rsp) - n) as index.
    destruct ((stack_base st) <? index) eqn:Habove_base;
    destruct (index <? (stack_base st) + (stack_size st)) eqn:Hbelow_top.
    + apply PeanoNat.Nat.ltb_lt in Habove_base. apply PeanoNat.Nat.ltb_lt in Hbelow_top. subst. repeat eexists. eapply I_Stack_Read; auto.
    + apply PeanoNat.Nat.ltb_lt in Habove_base. apply PeanoNat.Nat.ltb_ge in Hbelow_top. rewrite Hrsp1 in Heqindex. rewrite Heqindex in Habove_base, Hbelow_top. admit.
    + apply PeanoNat.Nat.ltb_ge in Habove_base. apply PeanoNat.Nat.ltb_lt in Hbelow_top. rewrite Hrsp1 in Heqindex. rewrite Heqindex in Habove_base. admit.
    + apply PeanoNat.Nat.ltb_ge in Habove_base. apply PeanoNat.Nat.ltb_ge in Hbelow_top. rewrite Hrsp1 in Heqindex. rewrite Heqindex in Habove_base, Hbelow_top. admit.
  - admit.
  - repeat eexists. apply I_Op. auto.
  - unfold get_function. Search (nth_error). destruct H as [].
    apply Coqlib.nth_error_lt in H0 as []. repeat eexists. apply I_Indirect_Call. 
    unfold get_function. apply H0.
  - unfold get_function. Search (nth_error). destruct H as [].
    apply Coqlib.nth_error_lt in H0 as []. repeat eexists. apply I_Direct_Call. apply H0.
  - destruct H as []. destruct (run_conditional st c) eqn:Hcond.
    + repeat eexists. eapply I_Branch_True. unfold get_basic_block; apply nth_error_nth'; eauto. unfold get_basic_block; apply nth_error_nth'; eauto. auto.
    + repeat eexists. eapply I_Branch_False. unfold get_basic_block; apply nth_error_nth'; eauto. unfold get_basic_block. apply nth_error_nth'. eauto. auto.
  - repeat eexists. eapply I_Jmp. unfold get_basic_block; apply nth_error_nth'; eauto.
  - repeat eexists. apply I_Ret. eauto.
Admitted.

(*
Inductive good_stream : program -> list instr_class -> Prop :=
| good_stream_nil: forall p,
  good_stream p nil
| good_stream_cons: forall p f bb i is,
  In f p ->
  In bb (V f) ->
  In i bb ->
  good_stream p is ->
  good_stream p (i :: is).
*)


Inductive good_stream : program -> list instr_class -> Prop :=
| good_stream_nil: forall p,
  good_stream p nil
| good_stream_bb: forall p bb,
  (exists f, In f p /\ In bb (V f)) ->
  good_stream p bb
| good_stream_app: forall p is1 is2,
  good_stream p is1 ->
  good_stream p is2 ->
  good_stream p (is1 ++ is2).

(*| good_stream_cons: forall p is i,
  (exists f bb, In f p /\ In bb (V f) /\ In i bb) ->
  good_stream p is ->
  good_stream p (i :: is). *)

(*| good_stream_cons: forall p i is,
  (exists f bb, In f p /\ In bb (V f) /\ In i bb) -> 
  good_stream p is ->
  good_stream p (i :: is). *)

(*Lemma good_stream_app: forall p s1 s2,
  good_stream p s1 ->
  good_stream p s2 ->
  good_stream p (s1 ++ s2).
Proof.
  intros. induction s1.
  - auto.
  - inversion H. subst. simpl. apply good_stream_cons. auto. auto.
Qed.*)

Lemma good_stream_tl: forall p i is,
  good_stream p (i :: is) ->
  good_stream p is.
Proof.
Admitted.

Lemma basic_block_good_stream: forall p f bb,
  In f p ->
  In bb (V f) ->
  good_stream p bb.
Proof.
  intros. apply good_stream_bb. eauto.

(*  intros. induction bb.
  - intros. apply good_stream_nil.
  - apply good_stream_cons. intros. 
 auto.
 apply good_stream_bb. exists f; auto. *)
Qed.

Lemma first_block_good_stream: forall p f,
  In f p ->
  good_stream p (first_block f).
Proof.
  intros. unfold first_block. destruct (V f) eqn:Hdestruct. apply good_stream_nil. eapply basic_block_good_stream.
  eauto. rewrite Hdestruct. apply in_eq.
Qed.

Lemma get_function_good_stream: forall st fname f,
  get_function st fname = Some f ->
  good_stream (prog st) (first_block f).
Proof.
  intros. unfold get_function in H. apply Coqlib.nth_error_in in H. destruct (V f) eqn:Hfirst.
  - unfold first_block. rewrite Hfirst. apply good_stream_nil.
  - unfold first_block. rewrite Hfirst. assert (In b (V f)). rewrite Hfirst. apply in_eq.
    apply good_stream_bb. exists f; auto.
Qed.

Lemma get_basic_block_good_stream: forall st label bb,
  get_basic_block st label = Some bb ->
  good_stream (prog st) bb.
Proof.
  intros. unfold get_basic_block in H. inversion H.
  Admitted.

Lemma istep_in_cfg: forall p is is' st st',
  (prog st) = p ->
  good_stream p is ->
  is / st i--> is' / st' ->
  good_stream p is'.
Proof.
  intros. inversion H1; subst; 
    try (apply good_stream_tl in H0; auto);
    try (apply good_stream_nil).
    apply good_stream_app; eauto; eapply get_basic_block_good_stream; eauto.
    apply good_stream_app; eauto; eapply get_basic_block_good_stream; eauto.
    apply good_stream_app; eauto; eapply get_basic_block_good_stream; eauto.
    apply good_stream_app; eauto; eapply get_function_good_stream; eauto.
    apply good_stream_app; eauto; eapply get_function_good_stream; eauto.
Qed.

Lemma multistep_in_cfg: forall p is is' st st',
  (prog st) = p ->
  good_stream p is ->
  is / st -->* is' / st' ->
  good_stream p is'.
Proof.
Admitted.
(*  intros. generalize dependent st. generalize dependent is'. induction is.
  - intros. inversion H1. auto. subst. inversion H2.
  - intros. inversion H1. auto. subst. destruct y. assert (prog s = prog st).
  { inversion H2; eauto. unfold run_op. admit. }
  eapply IHis. eapply good_stream_tl. apply H0. apply H. *)

Lemma good_stream_impl_in_cfg: forall p i is,
  good_stream p (i :: is) ->
  exists f bb, In f p /\ In bb (V f) /\ In i bb.
Proof.
Admitted.

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

Lemma negb_register_eqb_neq: forall r1 r2,
  negb (register_eqb r1 r2) = true ->
  r1 <> r2.
Proof.
  intros. apply Bool.negb_true_iff, register_eqb_false in H. auto.
Qed.

Lemma verified_impl_istep : forall i is st,
  instr_class_verifier i (abstractify st) = true ->
  exists is' st', (i :: is) / st i--> is' / st'.
Proof.
  intros. apply safe_instr_always_isteps. apply verifier_impl_safe_instr. auto.
Qed.

Axiom verified_program_impl_verified_instr_class: forall p entry_f f bb i is st,
  program_verifier p (abstractify (start_state p entry_f)) = true ->
  In entry_f p ->
  In f p ->
  In bb (V f) ->
  In i bb ->
  (exists fixpoint,
    instr_class_verifier i fixpoint = true /\
      ((first_block entry_f) / (start_state p entry_f) -->* (i :: is) / st ->
        leq_abs_state (abstractify st) fixpoint)).

Theorem verified_fixpoint_impl_istep: forall p entry_f f bb i is st,
  program_verifier p (abstractify (start_state p entry_f)) = true ->
  In entry_f p ->
  In f p ->
  In bb (V f) ->
  In i bb ->
  (first_block entry_f) / (start_state p entry_f) -->* (i :: is) / st ->
  exists is' st', (i :: is) / st i--> is' / st'.
Proof.
  intros. pose proof (verified_program_impl_verified_instr_class p entry_f f bb i is st) as soundness.
  destruct soundness; auto.
  destruct H5 as [fixpoint soundness]. apply verified_impl_istep; auto.
  eapply leq_abs_state_verifies; eauto.
Qed.

Theorem verified_fixpoint_impl_istep_final: forall p entry_f i is st,
  program_verifier p (abstractify (start_state p entry_f)) = true ->
  In entry_f p ->
  (first_block entry_f) / (start_state p entry_f) -->* (i :: is) / st ->
  exists is' st', (i :: is) / st i--> is' / st'.
Proof.
  intros. pose proof (multistep_in_cfg p (first_block entry_f) (i :: is) (start_state p entry_f) st).
  assert (prog (start_state p entry_f) = p). auto. apply H2 in H3. apply good_stream_impl_in_cfg in H3.
  destruct H3 as [f [bb [H4 []]]]. eapply verified_fixpoint_impl_istep; eauto. apply first_block_good_stream.
  auto. auto.
Qed.
