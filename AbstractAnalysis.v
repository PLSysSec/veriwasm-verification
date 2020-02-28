Require Import Machine.
Require Import Coq.Lists.List. 

Inductive info : Set :=
| unbounded
| mem_bounded
| cf_bounded
| mem_base.

Definition abs_registers_ty := fmap register info.

Definition abs_stack_ty := list info.

(* Definition heap_ty := list info.*)

(* Definition flags_ty := fmap flag abs_state. *)

Record abs_state := {
  abs_regs : abs_registers_ty;
(*  flags : flags_ty; *)
  abs_stack : abs_stack_ty;
(*  heap : heap_ty; *)
}.

Definition abs_empty_abs_state :=
{| abs_regs := fun r => if register_eq_dec r rdi then mem_base else unbounded;
   abs_stack := nil;
(*   heap := nil *)|}.

(*
Inductive value : Set :=
| A_Reg : register -> value
| A_Const : word64 -> value
| A_MultPlus : word64 -> value -> value -> value.
*)

(*
Fixpoint value_to_word64 (s : machine) (v :value) : word64 :=
match v with
| A_Reg r => (abs_regs s) r
| A_Const c => c
| A_MultPlus m v1 v2 => wmult m (wplus (value_to_word64 s v1) (value_to_word64 s v2))
end.
*)

(*
Definition read_register (s : machine) (r : register) : word64 :=
  get register word64 s.(abs_regs) r.
*)

(*
Definition write_register (s : machine) (r : register) (v : word64) : machine :=
{| abs_regs := set register register_eq_dec word64 s.(abs_regs) r v;
   flags := s.(flags);
   abs_stack := s.(stack);
   heap := s.(heap) |}.
*)

(*
Definition set_flags (s : machine) (f : flags_ty) : machine :=
{| abs_regs := s.(abs_regs);
   flags := f;
   abs_stack := s.(stack);
   heap := s.(heap) |}. 
*)

Definition expand_abs_stack (s : abs_state) (i : nat) : abs_state :=
{| abs_regs := s.(abs_regs);
(*   flags := s.(flags); *)
   abs_stack := s.(abs_stack) ++ (repeat unbounded i);
(*   heap := s.(heap) *)|}.

Fixpoint contract_abs_stack (s : abs_state) (i : nat) : abs_state :=
match i with
| 0 => s
| S n =>
contract_abs_stack {| abs_regs := s.(abs_regs);
(*   flags := s.(flags); *)
   abs_stack := removelast s.(abs_stack);
(*   heap := s.(heap) *) |} n
end.

(*
Definition read_stack_word (s : machine) (i : nat) : word8 :=
match nth_error s.(stack) i with
| Some v => v
| None => wzero8 (* we might want to do something else here *)
end.
*)

(*
Program Fixpoint read_abs_stack (s : machine) (i : nat) (sz : nat) : word (8 * sz):=
match sz with
| 0 => WO
| S sz' => combine (read_stack_word s i) (read_abs_stack s (i+1) (sz'))
end.
Next Obligation. rewrite <- plus_n_O. repeat (rewrite <- plus_n_Sm). reflexivity.
Qed.
*)

(*
Definition read_heap_word (s : machine) (key :  word64) : word8 :=
 s.(heap) key.
*)

(*
Program Fixpoint read_heap (s : machine) (key : word64) (sz : nat) : word (8 * sz):=
match sz with
| 0 => WO
| S sz' => combine (read_heap_word s key) (read_heap s (wplus key (wone 64)) (sz'))
end.
Next Obligation. rewrite <- plus_n_O. repeat (rewrite <- plus_n_Sm). reflexivity.
Qed.
*)

Definition get_register_info (s : abs_state) (r : register) : info :=
  map_get s.(abs_regs) r.

Definition set_register_info (s : abs_state) (r : register) (i : info) : abs_state :=
{| abs_regs := map_set register_eq_dec s.(abs_regs) r i;
   abs_stack := s.(abs_stack);
(*   heap := s.(heap) *) |}.

Definition get_stack_info (s : abs_state) (index : nat) : info :=
nth index s.(abs_stack) unbounded.

(* this needs to be updated *)
Definition set_stack_info (s : abs_state) (index : nat) (i : info) : abs_state :=
{| abs_regs := s.(abs_regs);
   abs_stack := update s.(abs_stack) index i;
 (*  heap := s.(heap) *) |}.

Definition empty {A} (l : list A) :=
  l = nil.

Reserved Notation " st '|-' i '⟶' st' "
                  (at level 40, st' at level 39).
Inductive instr_class_flow_function : instr_class -> abs_state -> abs_state -> Prop := 
| I_Heap_Read: forall st r_base r_src r_dst,
    (* r_base <> r_src -> *) (* not sure if we need this to make the proofs easier *)
    get_register_info st r_base = mem_base ->
    get_register_info st r_src = mem_bounded ->
    st |- (Heap_Read r_dst r_src r_base) ⟶ (set_register_info st r_dst unbounded) 
| I_Heap_Write: forall st r_base r_src r_dst,
    (* r_base <> r_src -> *) (* not sure if we need this to make the proofs easier *)
    get_register_info st r_base = mem_base ->
    get_register_info st r_dst = mem_bounded -> 
    st |- (Heap_Write r_dst r_src r_base) ⟶ st
| I_Heap_Check: forall st r_src,
    st |- (Heap_Check r_src) ⟶ (set_register_info st r_src mem_bounded)
| I_CF_Check: forall st r_src,
    st |- (CF_Check r_src) ⟶ (set_register_info st r_src cf_bounded)
| I_Reg_Move: forall st r_src r_dst,
    st |- (Reg_Move r_dst r_src) ⟶ (set_register_info st r_dst (get_register_info st r_src))
| I_Reg_Write: forall st r_dst val,
    st |- (Reg_Write r_dst val) ⟶ (set_register_info st r_dst unbounded)
| I_Stack_Expand: forall st i,
    st |- (Stack_Expand i) ⟶ (expand_abs_stack st i)
| I_Stack_Contract: forall st i,
    i <= (length st.(abs_stack)) ->
    st |- (Stack_Contract i) ⟶ (contract_abs_stack st i)
| I_Stack_Read: forall st i r_dst,
    i < (length st.(abs_stack)) ->
    st |- (Stack_Read r_dst i) ⟶ (set_register_info st r_dst (get_stack_info st i))
| I_Stack_Write: forall st i r_src,
    i < (length st.(abs_stack)) ->
    st |- (Stack_Write i r_src) ⟶ (set_stack_info st i (get_register_info st r_src))
| I_Indirect_Call: forall st reg,
    get_register_info st reg = cf_bounded ->
    get_register_info st rdi = mem_base ->
    st |- (Indirect_Call reg) ⟶  st
| I_Direct_Call: forall st,
    get_register_info st rdi = mem_base ->
    st |- (Direct_Call) ⟶  st
| I_Ret: forall st,
    empty st.(abs_stack) ->
    st |- (Ret) ⟶  st
  where " st '|-' i '⟶' st' " := (instr_class_flow_function i st st').

Reserved Notation " st '|-' is '\longrightarrow*' st' "
                  (at level 40, st' at level 39).
Inductive instr_class_multi : instr_class -> abs_state -> abs_state -> Prop := .

Definition basic_block := list instr_class.

Record cfg_ty := {
  nodes : list basic_block;
  edges : list (basic_block * basic_block)
}.

Lemma register_get_after_set_eq : forall (abs_regs : abs_registers_ty) reg v,
    map_get (map_set register_eq_dec abs_regs reg v) reg = v.
Proof.
  intros abs_regs reg v. unfold map_get. unfold map_set. destruct (register_eq_dec reg reg).
  - reflexivity.
  - exfalso. apply n. reflexivity.
Qed.

Lemma register_get_after_set_neq : forall (abs_regs : abs_registers_ty) reg1 reg2 v,
    reg1 <> reg2 ->
    map_get (map_set register_eq_dec abs_regs reg2 v) reg1 = map_get abs_regs reg1.
Proof.
  intros abs_regs reg1 reg2 v Heq. unfold map_get. unfold map_set. destruct (register_eq_dec reg2 reg1).
  - exfalso. apply Heq. auto.
  - reflexivity.
Qed.

Definition safe_stack_read (st : abs_state) (r_base : register) (r_src : register) (r_dst : register) : Prop :=
  r_base <> r_src /\ get_register_info st r_base = mem_base /\ get_register_info st r_src = mem_bounded.

Lemma read_after_check_is_safe: forall r_base r_src r_dst st, exists st' st'',
  r_base <> r_src ->
  get_register_info st r_base = mem_base ->
  st |- (Heap_Check r_src) ⟶ st' /\ st' |- (Heap_Read r_dst r_src r_base) ⟶ st''.
Proof.
  intros r_base r_src r_dst st. 
  eexists. eexists. intros Hneq Hbase.
  split.
  - apply I_Heap_Check.
  - apply I_Heap_Read.
    + unfold get_register_info in *. unfold set_register_info. simpl. rewrite register_get_after_set_neq; auto.
    + unfold get_register_info in *. unfold set_register_info. simpl. rewrite register_get_after_set_eq; auto.
Qed.
