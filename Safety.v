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

Lemma length_same_after_map : forall l f,
  length l = length (map f l).

Theorem safe_instr : 
  forall i abs_st st,
    abs_st = abstractify st ->
    exists abs_st', instr_class_flow_function i abs_st abs_st' ->
    is_instr_class_safe st i = true.
Proof.
  intros i abs_st st Hst. eexists. intros Hstep. unfold is_instr_class_safe, is_mem_bounded. induction Hstep; auto.
- apply andb_true_intro. split. 
  + rewrite Hst in H. unfold get_register_info, map_get, abstractify, abstractify_registers in H.
    simpl in H. apply safe_mem_base. auto.
  + rewrite Hst in H0. unfold get_register_info, map_get, abstractify, abstractify_registers in H0.
    simpl in H0. apply safe_mem_bound in H0. auto.
- apply andb_true_intro. split.
  + rewrite Hst in H. unfold get_register_info, map_get, abstractify, abstractify_registers in H.
    simpl in H. apply safe_mem_base. auto.
  + rewrite Hst in H0. unfold get_register_info, map_get, abstractify, abstractify_registers in H0.
    simpl in H0. apply safe_mem_bound in H0. auto.
- admit.
- unfold is_stack_index_safe. rewrite Hst in H. simpl in H. unfold abstractify_list in H. 
  induction (length (map (

Search ( andb _  _ = true).  