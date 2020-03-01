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
| I_CF_Check_Safe: forall reg st,
  safe_instr_class (CF_Check reg) st
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
| I_Direct_Call_Safe: forall st,
  Word.eq (get_register st rdi) st.(heap_base) = true ->
  safe_instr_class (Direct_Call) st
| I_Ret_Safe: forall st,
  length st.(stack) = 0 ->
  safe_instr_class (Ret) st.

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

Theorem instr_class_vstep_safe : forall i abs_st abs_st' st,
  abs_st = abstractify st ->
  i / abs_st v--> abs_st' -> 
  safe_instr_class i st.
Proof.
  intros i abs_st abs_st' st Hst Hstep. induction Hstep; subst.
- apply I_Heap_Read_Safe. 
  + inversion H0. unfold abstractify_registers, abstractify_int64 in H2. apply safe_mem_base; auto.
  + inversion H0. unfold abstractify_registers, abstractify_int64 in H2. apply safe_mem_bound in H2; auto.
- apply I_Heap_Write_Safe.
  + inversion H0. unfold abstractify_registers, abstractify_int64 in H2. apply safe_mem_base; auto.
  + inversion H0. unfold abstractify_registers, abstractify_int64 in H2. apply safe_mem_bound in H2; auto.
- apply I_Heap_Check_Safe.
- apply I_CF_Check_Safe.
- apply I_Reg_Move_Safe.
- apply I_Reg_Write_Safe.
- apply I_Stack_Expand_Safe.
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

Theorem instr_class_istep_abstractify_vstep: forall i st st' abs_st',
  i / abstractify st v--> abs_st' ->
  i / st i--> st' ->
  abs_st' = abstractify st'.
Proof.
  intros i st st' abs_st' Hv Hi. induction i; inversion Hv; inversion Hi; subst.
- unfold get_register_info, set_register_info in *. unfold map_get, map_set in *.
  unfold set_register, abstractify, abstractify_registers. simpl. unfold map_set. simpl. unfold abstractify_list.
  simpl. unfold abstractify_int64. simpl. admit.
- admit.
- unfold abstractify. simpl. unfold set_register_info. simpl.
unfold set_register, set_register_info, abstractify. simpl. unfold abstractify_registers. unfold map_set. simpl.
  unfold abstractify_int64. simpl.
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