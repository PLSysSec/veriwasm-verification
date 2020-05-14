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
if (ltb i (List.length (program s).(Funs))) then bottom else top.

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

Definition abstractify (s : state) : abs_state :=
{| abs_regs := abstractify_registers s s.(regs);
   abs_stack := abstractify_list s s.(stack);
   abs_lifted_state := sub_state;
   abs_heap_base := (heap_base s);
   abs_below_stack_guard_size := (below_stack_guard_size s);
   abs_above_stack_guard_size := (above_stack_guard_size s);
   abs_above_heap_guard_size := (above_heap_guard_size s);
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
  specialize H6 with r. inversion H6. rewrite H11. auto.
  subst. inversion H9. auto. rewrite H in H9. inversion H9. auto.
Qed.

Lemma leq_abs_state_heap_bounded: forall abs_st abs_st' r,
  leq_abs_state abs_st' abs_st ->
  heap_bounded (get_register_info abs_st r) = bottom ->
  heap_bounded (get_register_info abs_st' r) = bottom.
Proof.
  intros abs_st abs_st' r Hleq H. inversion Hleq. auto. subst. inversion H. subst.
  specialize H6 with r. inversion H6. rewrite H11. auto.
  subst. inversion H10. auto. rewrite H in H10. inversion H10. auto.
Qed.

Lemma leq_abs_state_cf_bounded: forall abs_st abs_st' r,
  leq_abs_state abs_st' abs_st ->
  cf_bounded (get_register_info abs_st r) = bottom ->
  cf_bounded (get_register_info abs_st' r) = bottom.
Proof.
  intros abs_st abs_st' r Hleq H. inversion Hleq. auto. subst. inversion H. subst.
  specialize H6 with r. inversion H6. rewrite H11. auto.
  subst. inversion H11. auto. rewrite H in H11. inversion H11. auto.
Qed.

(*
Lemma leq_abs_state_eq_above_stack_guard: forall abs_st abs_st' i,
  leq_abs_state abs_st' abs_st ->
  (abs_above_stack_guard_size abs_st) = i ->
  (abs_above_stack_guard_size abs_st') = i.
Proof.
  intros. inversion H. subst. auto.
  Admitted.
*)

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
  - apply andb_prop in Hv as [Hr Hrdi]. apply BinarySet_eqb_eq in Hr. apply BinarySet_eqb_eq in Hrdi.
    apply andb_true_intro; split; apply BinarySet_eqb_eq.
    * eapply leq_abs_state_cf_bounded. apply Hleq. apply Hr.
    * eapply leq_abs_state_is_heap_base. apply Hleq. apply Hrdi.
  - apply BinarySet_eqb_eq in Hv. apply BinarySet_eqb_eq. eapply leq_abs_state_is_heap_base.
    apply Hleq. apply Hv.
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

Lemma verified_impl_istep : forall i is st,
  instr_class_verifier i (abstractify st) = true ->
  exists is' st', (i :: is) / st i--> is' / st'.
Proof.
  intros. destruct i eqn:Hi ; unfold instr_class_verifier in H; simpl in H.
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
  - destruct (get_register st r <? List.length (program st)) eqn:valid_function.
    + repeat eexists. eapply I_Call_Check. apply PeanoNat.Nat.ltb_lt. auto.
    + repeat eexists. eapply I_Call_Check_Bad. apply PeanoNat.Nat.ltb_nlt in valid_function. apply Compare_dec.not_lt. auto.
  - repeat eexists. apply I_Reg_Move.
  - repeat eexists. apply I_Reg_Write.
  - repeat eexists. apply I_Stack_Expand_Static.
  - destruct (n + (stack_size st) <=? (max_stack_size st)) eqn:valid_expansion.
    + repeat eexists. eapply I_Stack_Expand_Dynamic. Search (_ <=? _). apply Compare_dec.leb_complete. auto.
    + repeat eexists. eapply I_Stack_Expand_Dynamic_Guard. apply Compare_dec.leb_complete_conv. auto.
  - repeat eexists. apply I_Stack_Contract.
  - admit.
  - admit.
  - repeat eexists. apply I_Op.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma verified_program_impl_verified_instr_class: forall p f bb i is st,
  program_verifier p (abstractify (start_state p)) = true ->
  In f p ->
  In bb (V f) ->
  In i bb ->
  (exists fixpoint,
    instr_class_verifier i fixpoint = true /\
      (imultistep (run_function p f) ((i :: is), st) ->
        leq_abs_state (abstractify st) fixpoint)).
Admitted.

Lemma verified_program_only_steps_to_verified_instr: forall p f i is st,
  program_verifier p (abstractify (start_state p)) = true ->
  In f p ->

  imultistep (run_function p f) ((i :: is), st) ->
  instr_class_verifier i (abstractify st) = true.
Proof.
  intros.
Admitted.
(*
Theorem verified_fixpoint_impl_istep: forall p f bb i is st,
  program_verifier p (abstractify (start_state p)) = true ->

  In f p ->
  In bb (V f) ->
  In i bb ->

  imultistep (run_function p f) ((i :: is), st) ->
  exists is' st', (i :: is) / st i--> is' / st'.
Proof.
  intros. pose proof (verified_program_impl_verified_instr_class p f bb i is st) as soundness.
  destruct soundness; auto.
  destruct abstract_analysis_sound as [fixpoint abstract_analysis_sound].
  eexists. intros. apply verified_impl_istep.
  eapply leq_abs_state_verifies. apply abstract_analysis_sound; auto. eauto.
Admitted.
*)

Theorem verified_fixpoint_impl_istep_final: forall p f i is st,
  exists fixpoint,
  instr_class_verifier i fixpoint = true ->
  imultistep (run_function p f) ((i :: is), st) ->
  exists st', (i :: is) / st i--> is / st'.
Proof.
  intros.
assert (
  exists fixpoint,
  (imultistep (run_function p f) ((i :: is), st) ->
  leq_abs_state (abstractify st) fixpoint)) as abstract_analysis_sound. { admit. }
  destruct abstract_analysis_sound as [fixpoint abstract_analysis_sound].
eexists. intros.
  (*apply verified_impl_istep.
  eapply leq_abs_state_verifies. apply abstract_analysis_sound. apply H0. apply H.*)
Admitted.

Lemma verified_program_impl_verified_function : forall p f,
  program_verifier p (abstractify (start_state p)) = true ->
  In f p ->
  function_verifier f (abstractify (start_state p)) = true.
Proof.
  intros. unfold program_verifier in H. rewrite forallb_forall in H.
  specialize H with f. apply H. apply H0.
Qed.

Theorem multistep_fuel_associativity :
  forall l st fuel l' st' fuel',
    imultistep_fuel (l, st, S fuel) (l', st', fuel') ->
    exists l1 st1,
      (imultistep_fuel (l, st, 1) (l1, st1, 0) /\
       imultistep_fuel (l1, st1, fuel) (l', st', fuel')).
Admitted.

Lemma istep_fuel_independence :
  forall fuel fuel' l l' st st' fuel1 fuel1',
    istep_fuel (l, st, fuel) (l', st', fuel1) ->
    istep_fuel (l, st, fuel') (l', st', fuel1').
Admitted.

Lemma imultistep_finish :
  forall fuel is st is1 st1 is' st',
    imultistep_fuel (is, st, S fuel) (is', st', 0) ->
    imultistep_fuel (is, st, fuel) (is1, st1, 0) ->
    imultistep_fuel (is1, st1, 1) (is', st', 0).
Admitted.

Lemma imultistep_finish' :
  forall fuel is st is1 st1 is' st',
    imultistep_fuel (is, st, fuel) (is1, st1, 0) ->
    imultistep_fuel (is1, st1, 1) (is', st', 0) ->
    imultistep_fuel (is, st, S fuel) (is', st', 0).
Admitted.

(* TODO: This needs to change once we introduce instruction addresses so we can actually talk about
 * how an abstract state represents a join-fixpoint of all the concrete states at that point *)
Theorem program_proof_tmp :
  forall p f fuel i is st,
    program_verifier p (abstractify (start_state p)) = true ->
    In f p ->
    imultistep_fuel ((run_function p f), fuel) (i :: is, st, 0) ->
    instr_class_verifier i (abstractify st) = true.
Admitted.

Theorem verified_program_step :
  forall p f fuel is1 st1,
    program_verifier p (abstractify (start_state p)) = true ->
    In f p ->
    imultistep_fuel ((run_function p f), fuel) (is1, st1, 0) ->
    exists is' st',
      imultistep_fuel ((run_function p f), S fuel) (is', st', 0).
Proof.
  intros.
  eexists ?[is']. eexists ?[st'].
  unfold run_function. unfold run_function in H1.
  pose proof imultistep_finish' as Hfinish.
  specialize Hfinish with fuel (first_block f) (start_state p) is1 st1 ?is' ?st'.
  apply Hfinish. auto.
  constructor.
  case is1; eauto.
  - admit.
  - intros.
    pose proof verified_impl_istep as Hstep.
    specialize Hstep with i l st1.
    apply IFuel_Step; auto.
    destruct Hstep. admit.
    destruct H2. eapply H2.


Admitted.

Theorem verified_program :
  forall p f fuel,
    program_verifier p (abstractify (start_state p)) = true ->
    In f p ->
    exists is' st',
      imultistep_fuel ((run_function p f), fuel) (is', st', 0).
Proof.
  intros. induction fuel.
  - admit. (* TODO: constructor messes the next goal up for some reason *)
  - eapply verified_program_step; auto.
    admit. (* TODO: Not sure how to introduce this, but should be trivial *)
Admitted.

(*
Lemma instr_class_verifier_shows_instr_class_safety: forall st abs_st i,
  leq_abs_state abs_st

Theorem verifier_shows_safety: forall p f bb,
  program_verifier p = true ->
  In f p ->
  hd_error (V f) = Some bb ->
  exists st, bb / (start_state p) -->* nil / st.
Proof.
  intros. induction bb.
  - eexists. apply multi_refl.
  - eexists. eapply multi_step.
    + destruct a.
      *
    +



assert (basic_block_verifier bb init_abs_state = true).
  { unfold program_verifier in H. rewrite forallb_forall in H.
  specialize H with f. apply H in H0. unfold function_verifier in H0.
  destruct (least_fixpoint f).
  - unfold forall2b in H0. rewrite forallb_forall in H0.
; inversion H0.


admit. inversion H0. apply H. apply H0.

apply verified_program_impl_verified_function in H.
  unfold program_verifier in H. unfold function_verifier in H.



Definition is_mem_bounded (s : state) (r_offset : register) (r_index : register) (r_base : register) : bool :=
  andb (eqb (get_register s r_base) (proj1_sig (heap_base s)))
    (ltb ((get_register s r_offset) + (get_register s r_index)) ((max_heap_size s) + (proj1_sig (above_heap_guard_size s)))).

Definition is_stack_contract_safe (s : state) (i : nat) : bool :=
  leb i (frame_size s).

Definition is_stack_index_safe (s : state) (i : nat) : bool :=
  ltb i (length s.(stack)).

Definition is_return_safe (s : state) : bool :=
  eqb (length s.(stack)) 0.

Definition is_rdi_heapbase (s : state) : bool :=
  Word.eq (get_register s rdi) s.(heap_base).

Definition is_function_index_safe (s : state) (r : register) : bool :=
  member s.(function_table) (get_register s r).

Definition is_instr_class_safe (s : state) (i : instr_class) : bool :=
  match i with
| Heap_Read r_dst r_src r_base => is_mem_bounded s r_src r_base
| Heap_Write r_dst r_val r_base => is_mem_bounded s r_dst r_base
| Stack_Contract i => is_stack_contract_safe s i
| Stack_Read _ i => is_stack_index_safe s i
| Stack_Write i _ => is_stack_index_safe s i
| Direct_Call _=> is_rdi_heapbase s
| Indirect_Call r => andb (is_rdi_heapbase s) (is_function_index_safe s r)
| Ret => is_return_safe s
| _ => true
end.

Inductive safe_instr_class : instr_class -> state -> Prop :=
| I_Heap_Read_Safe: forall r_dst r_src r_base st,
  Word.eq (get_register st r_base) (st.(heap_base)) = true ->
  Word.lt (get_register st r_src) fourGB =  true ->
  safe_instr_class (Heap_Read r_dst r_src r_base) st
| I_Heap_Write_Safe: forall r_dst r_val r_base st,
  Word.eq (get_register st r_base) (st.(heap_base)) = true ->
  Word.lt (get_register st r_dst) fourGB =  true ->
  safe_instr_class (Heap_Write r_dst r_val r_base) st
| I_Heap_Check_Safe: forall reg st,
  safe_instr_class (Heap_Check reg) st
| I_Call_Check_Safe: forall reg st,
  safe_instr_class (Call_Check reg) st
| I_Reg_Move_Safe: forall r_dst r_src st,
  safe_instr_class (Reg_Move r_dst r_src) st
| I_Reg_Write_Safe: forall r_dst val st,
  safe_instr_class (Reg_Write r_dst val) st
| I_Stack_Expand_Safe: forall st i,
  safe_instr_class (Stack_Expand i) st
| I_Stack_Contract_Safe: forall st i,
  i <= length st.(stack) ->
  safe_instr_class (Stack_Contract i) st
| I_Stack_Read_Safe: forall st i r_dst,
  i < length st.(stack) ->
  safe_instr_class (Stack_Read r_dst i) st
| I_Stack_Write_Safe: forall st i r_src,
  i < length st.(stack) ->
  safe_instr_class (Stack_Write i r_src) st
| I_Indirect_Call_Safe: forall st reg,
  Word.eq (get_register st rdi) st.(heap_base) = true ->
  member st.(function_table) (get_register st reg) = true ->
  safe_instr_class (Indirect_Call reg) st
| I_Direct_Call_Safe: forall st name,
  Word.eq (get_register st rdi) st.(heap_base) = true ->
  safe_instr_class (Direct_Call name) st
| I_Branch_Safe: forall st c,
  safe_instr_class (Branch c) st
| I_Op_Safe: forall st op rs_dst rs_src,
  safe_instr_class (Op op rs_dst rs_src) st
| I_Ret_Safe: forall st,
  length st.(stack) = 0 ->
  safe_instr_class (Ret) st.
Hint Constructors safe_instr_class.

(*
Fixpoint is_basic_block_safe (s : state) (bb : basic_block) : bool :=
match bb with
| nil => true
| i :: bb' => andb (is_instr_class_safe s i) (is_basic_block_safe (run_instr i s) bb')
end.
*)

Inductive safe_basic_block : basic_block -> state -> Prop :=
| I_Basic_Block_Empty_Safe : forall st,
  safe_basic_block nil st
| I_Basic_Block_Cons_Safe : forall i bb st st',
  safe_instr_class i st ->
  instr_class_istep i st st' ->
  safe_basic_block bb st' ->
  safe_basic_block (i :: bb) st.

Definition is_heap_base_int64 (s : state) (i : int64) : BinarySet :=
if (Word.eq i s.(heap_base)) then bottom else top.

Definition is_heap_bounded_int64 (s : state) (i : int64) : BinarySet :=
if (Word.lt i fourGB) then bottom else top.

Definition is_cf_bounded_int64 (s : state) (i : int64) : BinarySet :=
if (member s.(function_table) i) then bottom else top.


Definition abstractify_int64 (s : state) (i : int64) : info :=
{| abs_heap_base := is_heap_base_int64 s i;
   abs_heap_bound := is_heap_bounded_int64 s i;
   abs_cf_bound := is_cf_bounded_int64 s i; |}.

Definition abstractify_list (s : state) (l : list int64) : list info :=
  map (abstractify_int64 s) l.

Definition abstractify_registers (s : state) (f : registers_ty) : abs_registers_ty :=
  fun r => (abstractify_int64 s (f r)).

Definition abstractify (s : state) : abs_state :=
{| abs_regs := abstractify_registers s s.(regs);
   abs_stack := abstractify_list s s.(stack);
   abs_error := s.(error) |}.
(*Notation " α st " := ( abstractify st ) (at level 200). *)

Inductive leq_info : info -> info -> Prop :=
| leq_info_refl : forall i,
  leq_info i i
| leq_info_rule : forall x y,
  BinaryRel (abs_heap_base x) (abs_heap_base y) ->
  BinaryRel (abs_heap_bound x) (abs_heap_bound y) ->
  BinaryRel (abs_cf_bound x) (abs_cf_bound y) ->
  leq_info x y.

Lemma leq_info_empty : forall i,
  leq_info i empty_info.
Proof.
  intros [[] [] []]; apply leq_info_rule; apply top_rel.
Qed.

(* TODO: This doesn't consider flags or memory *)
Reserved Notation " st ≤ st' "
                  (at level 45, st' at level 44).
Inductive leq_state : abs_state -> abs_state -> Prop :=
| leq_state_rule: forall st st',
  (forall reg, leq_info (get_register_info st reg) (get_register_info st' reg)) ->
  (forall i, leq_info (get_stack_info st i) (get_stack_info st' i)) ->
  length (abs_stack st) = length (abs_stack st') ->
  st ≤ st'
where " st ≤ st' " := (leq_state st st').

Lemma leq_state_ge_stack_length:
forall st1 st2,
st1 ≤ st2 ->
length (abs_stack st1) >= length (abs_stack st2).
Proof.
intros st1 st2 Hleq. inversion Hleq. subst. lia.
Qed. (* this is not possible to prove because we can always get an empty state so we need to add this constraint to the definition*)


Lemma leq_state_vstep :
forall i st1 st2 st2',
st1 ≤ st2 ->
i / st2 v--> st2' ->
exists st1', i / st1 v--> st1'.
Proof.
intros i st1 st2 st2' Hleq Hstep. inversion Hstep; subst; eexists; auto.
- eapply V_Heap_Read.
  + inversion Hleq. subst. specialize H1 with r_base.
  inversion H1. subst. rewrite H6. auto. subst. rewrite H in H4. inversion H4. auto.
  + inversion Hleq. subst. specialize H1 with r_src.
  inversion H1. subst. rewrite H6. auto. subst. rewrite H0 in H5. inversion H5. auto.
- eapply V_Heap_Write.
  + inversion Hleq. subst. specialize H1 with r_base.
  inversion H1. subst. rewrite H6. auto. subst. rewrite H in H4. inversion H4. auto.
  + inversion Hleq. subst. specialize H1 with r_dst.
  inversion H1. subst. rewrite H6. auto. subst. rewrite H0 in H5. inversion H5. auto.
- eapply V_Stack_Contract.
  inversion Hleq. subst. lia.
- eapply V_Stack_Read.
  inversion Hleq. subst. lia.
- eapply V_Stack_Write.
  inversion Hleq. subst. lia.
- eapply V_Indirect_Call; inversion Hleq; subst.
  + specialize H1 with reg. inversion H1. subst. rewrite <- H6 in H. auto.
    rewrite H in H6. inversion H6. auto.
  + specialize H1 with rdi. inversion H1. subst. rewrite <- H6 in H0. auto.
    rewrite H0 in H4. inversion H4. auto.
- eapply V_Direct_Call; inversion Hleq; subst.
  + specialize H0 with rdi. inversion H0. subst. rewrite <- H5 in H. auto.
    rewrite H in H3. inversion H3. auto.
- eapply V_Ret.
  inversion Hleq. subst. Search (length). inversion H. rewrite H4 in H2. simpl in H2.
  destruct (abs_stack st1). unfold empty. auto. inversion H2.
Qed.

Lemma safe_mem_base : forall s i,
  (abstractify_int64 s i).(abs_heap_base) = bottom ->
  Word.eq i s.(heap_base) = true.
Proof.
  intros s i H. unfold abstractify_int64 in H. inversion H. unfold is_heap_base_int64 in H1.
  remember (Word.eq i (heap_base s)) as goal. destruct goal.
  + auto.
  + inversion H1.
Qed.

Lemma safe_mem_bound : forall s i,
  (abstractify_int64 s i).(abs_heap_bound) = bottom ->
  Word.lt i fourGB = true.
Proof.
  intros s i H. unfold abstractify_int64 in H. inversion H. unfold is_heap_bounded_int64 in H1.
  remember (Word.lt i fourGB) as goal. destruct goal.
  + auto.
  + inversion H1.
Qed.

Lemma safe_function_index : forall s i,
  (abstractify_int64 s i).(abs_cf_bound) = bottom ->
  member s.(function_table) i = true.
Proof.
  intros s i H. unfold abstractify_int64 in H. inversion H. unfold is_cf_bounded_int64 in H1.
  remember (member (function_table s) i) as goal. destruct goal.
  + auto.
  + inversion H1.
Qed.

(*
Lemma safe_function_return : forall s i,
  abstractify_int64 s i = cf_bounded ->
  member s.(function_table) i = true.
Proof.
  intros s i H. unfold abstractify_int64 in H. remember (member (function_table s) i) as goal. destruct goal.
  + auto.
  + remember (Word.eq i (heap_base s)) as not_goal. destruct not_goal.
    * inversion H.
    * remember (Word.lt i fourGB) as not_goal. destruct not_goal; inversion H.
Qed.
*)

Theorem instr_class_vstep_safe : forall i abs_st abs_st' st,
  abs_st = abstractify st ->
  i / abs_st v--> abs_st' ->
  safe_instr_class i st.
Proof.
  intros i abs_st abs_st' st Hst Hstep. induction Hstep; subst; auto.
- apply I_Heap_Read_Safe.
  + inversion H0. unfold abstractify_registers, abstractify_int64 in H2. apply safe_mem_base; auto.
  + inversion H0. unfold abstractify_registers, abstractify_int64 in H2. apply safe_mem_bound in H2; auto.
- apply I_Heap_Write_Safe.
  + inversion H0. unfold abstractify_registers, abstractify_int64 in H2. apply safe_mem_base; auto.
  + inversion H0. unfold abstractify_registers, abstractify_int64 in H2. apply safe_mem_bound in H2; auto.
- apply I_Stack_Contract_Safe.
  unfold abstractify, abstractify_list in H. simpl in H.
  rewrite <- map_length with (f := abstractify_int64 st). auto.
- apply I_Stack_Read_Safe. unfold abstractify, abstractify_list in H. simpl in H.
  rewrite <- map_length with (f := abstractify_int64 st). auto.
- apply I_Stack_Write_Safe. unfold abstractify, abstractify_list in H. simpl in H.
  rewrite <- map_length with (f := abstractify_int64 st). auto.
- apply I_Indirect_Call_Safe.
  + inversion H0. unfold abstractify_registers, abstractify_int64 in H2. apply safe_mem_base; auto.
  + inversion H. unfold abstractify_registers, abstractify_int64 in H2. apply safe_function_index; auto.
- apply I_Direct_Call_Safe.
  inversion H. unfold abstractify_registers, abstractify_int64 in H1. apply safe_mem_base; auto.
- apply I_Ret_Safe.
  inversion H. unfold abstractify_list in H1. apply map_eq_nil in H1. rewrite H1. auto.
Qed.

Theorem safe_instr :
  forall i abs_st abs_st' st,
    abs_st = abstractify st ->
    instr_class_vstep i abs_st abs_st' ->
    is_instr_class_safe st i = true.
Proof.
  intros i abs_st abst_st' st Hst Hstep. unfold is_instr_class_safe, is_mem_bounded. induction Hstep; subst; auto.
- apply andb_true_intro. split.
  + unfold get_register_info, abstractify, abstractify_registers in H.
    simpl in H. apply safe_mem_base. auto.
  + unfold get_register_info, abstractify, abstractify_registers in H0.
    simpl in H0. apply safe_mem_bound in H0. auto.
- apply andb_true_intro. split.
  + unfold get_register_info, abstractify, abstractify_registers in H.
    apply safe_mem_base. auto.
  + unfold get_register_info, abstractify, abstractify_registers in H0.
    apply safe_mem_bound in H0. auto.
- unfold is_stack_contract_safe. apply PeanoNat.Nat.leb_le. unfold abs_stack, abstractify, abstractify_list in H.
  rewrite map_length in H. auto.
- unfold is_stack_index_safe. simpl in H. unfold abstractify_list in H.
  rewrite map_length in H. apply PeanoNat.Nat.ltb_lt. auto.
- unfold is_stack_index_safe. simpl in H. unfold abstractify_list in H.
  rewrite map_length in H. apply PeanoNat.Nat.ltb_lt. auto.
- apply andb_true_intro. split.
  + unfold get_register_info, abstractify, abstractify_registers in H0.
    apply safe_mem_base in H0. auto.
  +unfold get_register_info, abstractify, abstractify_registers in H.
    apply safe_function_index. auto.
- unfold get_register_info, abstractify, abstractify_registers in H. simpl in H.
  apply safe_mem_base. auto.
- unfold is_return_safe. simpl in H. unfold abstractify_list, empty in H.
  apply map_eq_nil in H. apply PeanoNat.Nat.eqb_eq. rewrite H. auto.
Qed.

(*
Lemma basic_helper : forall a bb abs_st abs_st' abs_st'',
multi basic_block_flow_function (a :: bb, abs_st) (nil, abs_st'') ->
   basic_block_flow_function (a :: bb, abs_st) (bb, abs_st')
/\ multi basic_block_flow_function (bb, abs_st') (nil, abs_st'').
Proof.

  intros. eapply multi_step in H. induction a.
- inversion H. inversion H0. inversion H1. subst. split.

 inversion H. inversion H0. inversion H1. subst. induction a; inversion H; subst.
- inversion H0. inversion H1. subst. split. apply I_Basic_Block. inversion H8. subst. auto.
  +
*)

Lemma eq_thn_cond_true : forall {A} (cond : bool) (thn : A) (els : A),
  (if cond then thn else els) = thn ->
  thn <> els ->
  cond = true.
Proof.
  intros A cond thn els. destruct cond; auto.
Qed.

Theorem instr_class_istep_abstractify_vstep: forall i st st' abs_st',
  i / abstractify st v--> abs_st' ->
  i / st i--> st' ->
  abstractify st' ≤ abs_st'.
Proof.
  intros i st st' abs_st' Hv Hi. inversion Hv; subst. inversion Hi; subst.
- inversion H; inversion H0. unfold is_heap_base_int64, is_heap_bounded_int64 in *.
  apply eq_thn_cond_true in H2. apply eq_thn_cond_true in H3. apply leq_state_rule.
  + intros reg. destruct (register_eq_dec reg r_dst).
    * subst. simpl. rewrite register_get_after_set_eq. apply leq_info_empty.
    * simpl. rewrite register_get_after_set_neq; auto. remember (read_heap st (Word.add (get_register st r_src) (get_register st r_base))) as v_dst.
      simpl. unfold abstractify_registers. rewrite register_get_after_set_neq; auto.
      unfold set_register. unfold abstractify_int64. unfold is_heap_base_int64, is_heap_bounded_int64, is_cf_bounded_int64.
      simpl. apply leq_info_refl.
  + intros i. apply leq_info_refl.
  + auto.
  + intros Hfalse. inversion Hfalse.
  + intros Hfalse. inversion Hfalse.
- inversion Hi. subst. inversion Hv. subst. unfold abstractify. simpl.
  unfold abstractify_registers, abstractify_list. unfold abstractify_int64. simpl.
  unfold is_heap_base_int64, is_heap_bounded_int64, is_cf_bounded_int64. simpl. apply leq_state_rule.
  simpl. intros reg. apply leq_info_refl. intros i. apply leq_info_refl. auto.
- inversion Hi. subst. inversion Hv. subst. apply leq_state_rule.
  + intros reg. destruct (register_eq_dec reg r_src).
    * subst. simpl. rewrite register_get_after_set_eq. unfold abs_heap_bounded_info.
      unfold abstractify_registers. unfold abstractify_int64. unfold is_heap_base_int64, is_heap_bounded_int64, is_cf_bounded_int64.
      simpl. rewrite register_get_after_set_eq. apply leq_info_rule; try apply top_rel.
      simpl. Search (Word.lt). admit. (*this is clearly true. i gotta dig around for a useful lemma *)
    * simpl. rewrite register_get_after_set_neq. unfold abs_heap_bounded_info.
      unfold abstractify_registers. unfold abstractify_int64. unfold is_heap_base_int64, is_heap_bounded_int64, is_cf_bounded_int64.
      simpl. rewrite register_get_after_set_neq. apply leq_info_refl. apply n. apply n.
  + intros i. apply leq_info_refl.
  + auto.
- inversion Hi. subst. admit.
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
- inversion Hi. apply leq_state_rule. intros reg. apply leq_info_refl. intro i. apply leq_info_refl. auto.
Admitted.

Theorem basic_block_vstep_safe :
  forall bb abs_st abs_st' st,
  abs_st = abstractify st ->
  multi_basic_block_vstep (bb, abs_st) (nil, abs_st') ->
  safe_basic_block bb st.
Proof.
  intros bb abs_st abs_st' st Hst Hstep. generalize dependent abs_st. generalize dependent st. induction bb.
- intros st abs_st Hst Hstep. apply I_Basic_Block_Empty_Safe.
- intros st abs_st Hst Hstep. inversion Hstep; subst.  inversion H; subst.
  assert (exists st'', a / st i--> st'').
{ apply instr_class_always_isteps. }
  inversion H1.
  apply I_Basic_Block_Cons_Safe with (st' := x).
  + apply instr_class_vstep_safe with (abs_st := abstractify st) (abs_st' := st'); auto.
  + auto.
  + apply IHbb with (abs_st := st').
    * eapply instr_class_istep_abstractify_vstep. apply H5. apply H2.
    * auto.
Qed.
*)
