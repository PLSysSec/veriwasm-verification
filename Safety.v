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

Definition is_mem_bounded (s : state) (r_src : register) (r_base : register) : bool :=
  andb (Word.eq (get_register s r_base) s.(heap_base)) (Word.lt (get_register s r_src) fourGB).

Definition is_stack_contract_safe (s : state) (i : nat) : bool :=
  leb i (length s.(stack)).

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
    * admit. (*eapply instr_class_istep_abstractify_vstep. apply H5. apply H2.*)
    * auto.
Admitted.

Theorem contract_stack_never_changes_error :
  forall i s,
    s.(error) = (contract_stack s i).(error).
Proof.
  intros i. induction i. auto.
  simpl. intros.
  specialize IHi with {| regs := regs s; flags := flags s;
                                stack := removelast (stack s);
                                heap := heap s;
                                heap_base := heap_base s;
                                function_table := function_table s;
                                error := error s;
                                exit := exit s |}.
  apply IHi.
Qed.

Theorem run_instr_maintains_error :
  forall s,
    s.(error) = true ->
    forall i,
      (run_instr i s).(error) = true.
Proof.
  intros. induction i; auto.
  simpl. rewrite contract_stack_never_changes_error with n s in H. assumption.
Qed.

Theorem run_bb_any_state_error :
  forall s bb,
    s.(error) = true ->
    forall s',
      s'.(error) = true ->
      (run_basic_block bb s).(error) = (run_basic_block bb s').(error).
Proof.
  intros s bb H. induction bb.
  - simpl. intros. rewrite H. rewrite H0. reflexivity.
  - intros. simpl. assert (IHbb' := IHbb).
    specialize IHbb with (run_instr a s').
    specialize IHbb' with (run_instr a s).
    destruct IHbb.
    apply run_instr_maintains_error.
    apply H0.
    destruct IHbb'.
    apply run_instr_maintains_error.
    apply H.
    reflexivity.
Qed.

Theorem run_bb_maintains_error :
  forall s,
    s.(error) = true ->
    forall bb,
      (run_basic_block bb s).(error) = true.
Proof.
  intros. induction bb. auto.
  simpl. pose proof run_bb_any_state_error as H0.
  specialize H0 with (run_instr a s) bb s.
  pose proof run_instr_maintains_error as H1.
  specialize H1 with s a.
  assert (H' := H).
  apply H1 in H'. apply H0 in H'.
  rewrite IHbb in H'. assumption. assumption.
Qed.

Theorem bb_safety : (n : node_ty) (f : function_ty) (p : program_ty) : Prop :=
  well_formed_program p ->
  In n (fst f).(nodes) ->
  In f p.(fun_l ist) ->
  forall s n',
    In n' get_parent_nodes n (fst f).(edges) ->
  exists fuel,
    run_program'

Theorem verify_bb :
  forall f bb,
    s.(error)
