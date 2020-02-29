Require Import Semantics.
Require Import Machine.
Require Import Bits.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import AbstractAnalysis.

Definition member (s : set int64) (i : int64) :=
  set_mem int64_eq_dec i s.

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
| Direct_Call => is_rdi_heapbase s
| Indirect_Call r => andb (is_rdi_heapbase s) (is_function_index_safe s r)
| Ret => is_return_safe s
| _ => true
end.

Fixpoint is_basic_block_safe (s : state) (bb : basic_block) : bool :=
match bb with
| nil => true
| i :: bb' => andb (is_instr_class_safe s i) (is_basic_block_safe (run_instr i s) bb') 
end.

Definition abstractify_int64 (s : state) (i : int64) : info :=
if (Word.eq i s.(heap_base)) then mem_base else
if (member s.(function_table) i) then cf_bounded else
if (Word.lt i fourGB) then mem_bounded else unbounded.

Definition abstractify_list (s : state) (l : list int64) : list info :=
  map (abstractify_int64 s) l.

Definition abstractify_registers (s : state) (f : registers_ty) : abs_registers_ty :=
  fun r => (abstractify_int64 s (f r)).

Definition abstractify (s : state) : abs_state :=
{| abs_regs := abstractify_registers s s.(regs);
   abs_stack := abstractify_list s s.(stack) |}.

Lemma safe_mem_base : forall s i,
  abstractify_int64 s i = mem_base ->
  Word.eq i s.(heap_base) = true.
Proof.
  intros s i H. unfold abstractify_int64 in H. remember (Word.eq i (heap_base s)) as goal. destruct goal.
  + auto.
  + remember (member (function_table s) i) as not_goal. destruct not_goal.
    * inversion H.
    * remember (Word.lt i fourGB) as not_goal. destruct not_goal; inversion H.
Qed.

Lemma safe_mem_bound : forall s i,
  abstractify_int64 s i = mem_bounded ->
  Word.lt i fourGB = true.
Proof.
  intros s i H. unfold abstractify_int64 in H. remember (Word.lt i fourGB) as goal. destruct goal.
  + auto.
  + remember (Word.eq i (heap_base s)) as not_goal. destruct not_goal.
    * inversion H.
    * remember (member (function_table s) i) as not_goal. destruct not_goal; inversion H.
Qed.

Lemma safe_function_index : forall s i, 
  abstractify_int64 s i = cf_bounded ->
  member s.(function_table) i = true.
Proof.
  intros s i H. unfold abstractify_int64 in H. remember (member (function_table s) i) as goal. destruct goal.
  + auto.
  + remember (Word.eq i (heap_base s)) as not_goal. destruct not_goal.
    * inversion H.
    * remember (Word.lt i fourGB) as not_goal. destruct not_goal; inversion H.
Qed.

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

Theorem safe_instr : 
  forall i abs_st abs_st' st,
    abs_st = abstractify st ->
    instr_class_flow_function i abs_st abs_st' ->
    is_instr_class_safe st i = true.
Proof.
  intros i abs_st abst_st' st Hst Hstep. unfold is_instr_class_safe, is_mem_bounded. induction Hstep; subst; auto.
- apply andb_true_intro. split. 
  + unfold get_register_info, map_get, abstractify, abstractify_registers in H.
    simpl in H. apply safe_mem_base. auto.
  + unfold get_register_info, map_get, abstractify, abstractify_registers in H0.
    simpl in H0. apply safe_mem_bound in H0. auto.
- apply andb_true_intro. split.
  + unfold get_register_info, map_get, abstractify, abstractify_registers in H.
    apply safe_mem_base. auto.
  + unfold get_register_info, map_get, abstractify, abstractify_registers in H0.
    apply safe_mem_bound in H0. auto.
- unfold is_stack_contract_safe. apply PeanoNat.Nat.leb_le. unfold abs_stack, abstractify, abstractify_list in H.
  rewrite map_length in H. auto.
- unfold is_stack_index_safe. simpl in H. unfold abstractify_list in H.
  rewrite map_length in H. apply PeanoNat.Nat.ltb_lt. auto.
- unfold is_stack_index_safe. simpl in H. unfold abstractify_list in H.
  rewrite map_length in H. apply PeanoNat.Nat.ltb_lt. auto.
- apply andb_true_intro. split.
  + unfold get_register_info, map_get, abstractify, abstractify_registers in H0.
    apply safe_mem_base in H0. auto.
  +unfold get_register_info, map_get, abstractify, abstractify_registers in H.
    apply safe_function_index. auto.
- unfold get_register_info, map_get, abstractify, abstractify_registers in H. simpl in H.
  apply safe_mem_base. auto.
- unfold is_return_safe. simpl in H. unfold abstractify_list, empty in H.
  apply map_eq_nil in H. apply PeanoNat.Nat.eqb_eq. rewrite H. auto.
Qed.

Theorem safe_basic_block : 
  forall bb abs_st abs_st' st,
  abs_st = abstractify st ->
  multi_basic_block_flow_function (bb, abs_st) (nil, abs_st') ->
  is_basic_block_safe st bb = true.
Proof.
  intros bb abs_st abs_st' st Hst Hstep. generalize dependent abs_st. generalize dependent st. induction bb.
  - auto.
  - simpl. intros st abs_st Hst Hstep. apply andb_true_intro. split.
    + inversion Hstep. inversion H. eapply safe_instr. apply Hst. apply H7.
    + inversion Hstep. apply IHbb with (st := (run_instr a st)) (abs_st := abstractify (run_instr a st)).
      * unfold abstractify. unfold abstractify_registers, abstractify_list. simpl. 

 apply Hst. apply IHbb'. inversion Hstep. apply IHbb. 

