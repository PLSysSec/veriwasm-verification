Require Import VerifiedVerifier.Machine.
Require Import VerifiedVerifier.BoundedLattice.
Require Import VerifiedVerifier.BinaryLattice.
Require Import VerifiedVerifier.Maps.
Require Import Coq.Lists.List.

Record info := {
  abs_heap_base : BinarySet;
  abs_heap_bound : BinarySet;
  abs_cf_bound : BinarySet;
}.

Definition empty_info :=
  {| abs_heap_base := top;
     abs_heap_bound := top;
     abs_cf_bound := top; |}.

Definition abs_heap_base_info :=
  {| abs_heap_base := bottom;
     abs_heap_bound := top;
     abs_cf_bound := top; |}.

Definition abs_heap_bounded_info :=
  {| abs_heap_base := top;
     abs_heap_bound := bottom;
     abs_cf_bound := top; |}.

Definition abs_cf_bounded_info :=
  {| abs_heap_base := top;
     abs_heap_bound := top;
     abs_cf_bound := bottom; |}.

(*
Record absStateLattice := {
  abs_heap_base         : BoundedSet;
  heap              : BoundedSet;
  fn_table          : BoundedSet;
}.

Definition unbounded_lattice :=
  {| abs_heap_base := top;
     heap := top;
     fn_table := top; |}.

Definition abs_heap_base_bounded_lattice :=
  {| abs_heap_base := bounded;
     heap := top;
     fn_table := top; |}.

Definition abs_heap_bounded_lattice :=
  {| abs_heap_base := top;
     heap := bounded;
     fn_table := top; |}.

Definition fn_table_bounded_lattice :=
  {| abs_heap_base := top;
     heap := top;
     fn_table := bounded; |}.

Definition absStateLattice_join (a : absStateLattice) (b : absStateLattice) : absStateLattice :=
  {| abs_heap_base := join_BoundedSet a.(abs_heap_base) b.(abs_heap_base);
     heap := join_BoundedSet a.(heap) b.(heap);
     fn_table := join_BoundedSet a.(fn_table) b.(fn_table) |}.

Definition absStateLattice_meet (a : absStateLattice) (b : absStateLattice) : absStateLattice :=
  {| abs_heap_base := meet_BoundedSet a.(abs_heap_base) b.(abs_heap_base);
     heap := meet_BoundedSet a.(heap) b.(heap);
     fn_table := meet_BoundedSet a.(fn_table) b.(fn_table) |}.
*)

Definition abs_registers_ty := total_map register info.

Definition abs_stack_ty := list info.

(* Definition heap_ty := list lattice.*)

(* Definition flags_ty := fmap flag abs_state. *)

Record abs_state := {
  abs_regs : abs_registers_ty;
(*  flags : flags_ty; *)
  abs_stack : abs_stack_ty;
(*  heap : heap_ty; *)
}.

Definition abs_empty_state :=
{| abs_regs := fun r => if register_eq_dec r rdi
                          then abs_heap_base_info
                          else empty_info;
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
   abs_stack := s.(abs_stack) ++ (repeat empty_info i);
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
  s.(abs_regs) r.

Definition set_register_info (s : abs_state) (r : register) (i : info) : abs_state :=
{| abs_regs := t_update register_eq_dec s.(abs_regs) r i;
   abs_stack := s.(abs_stack);
(*   heap := s.(heap) *) |}.

Definition get_stack_info (s : abs_state) (index : nat) : info :=
nth index s.(abs_stack) empty_info.

(* this needs to be updated *)
Definition set_stack_info (s : abs_state) (index : nat) (i : info) : abs_state :=
{| abs_regs := s.(abs_regs);
   abs_stack := Machine.update s.(abs_stack) index i;
 (*  heap := s.(heap) *) |}.

Definition empty {A} (l : list A) :=
  l = nil.

(* TODO: Start using the heap *)
(* TODO: Add check instructions for everything else *)
Reserved Notation " i '/' st 'v-->' st' "
                  (at level 40, st' at level 39).
Inductive instr_class_vstep : instr_class -> abs_state -> abs_state -> Prop := 
| V_Heap_Read: forall st r_base r_src r_dst,
    (* r_base <> r_src -> *) (* not sure if we need this to make the proofs easier *)
    (get_register_info st r_base).(abs_heap_base) = bottom ->
    (get_register_info st r_src).(abs_heap_bound) = bottom ->
    Heap_Read r_dst r_src r_base / st v--> (set_register_info st r_dst empty_info) 
| V_Heap_Write: forall st r_base r_src r_dst,
    (* r_base <> r_src -> *) (* not sure if we need this to make the proofs easier *)
    (get_register_info st r_base).(abs_heap_base) = bottom ->
    (get_register_info st r_dst).(abs_heap_bound) = bottom -> 
    Heap_Write r_dst r_src r_base / st v--> st
| V_Heap_Check: forall st r_src,
    Heap_Check r_src / st v--> (set_register_info st r_src abs_heap_bounded_info)
| V_Call_Check: forall st r_src,
    Call_Check r_src / st v--> (set_register_info st r_src abs_cf_bounded_info)
| V_Reg_Move: forall st r_src r_dst,
    Reg_Move r_dst r_src / st v--> (set_register_info st r_dst (get_register_info st r_src))
| V_Reg_Write: forall st r_dst val,
    Reg_Write r_dst val / st v--> (set_register_info st r_dst empty_info)
| V_Stack_Expand: forall st i,
    Stack_Expand i / st v--> (expand_abs_stack st i)
| V_Stack_Contract: forall st i,
    i <= (length st.(abs_stack)) ->
    Stack_Contract i / st v--> (contract_abs_stack st i)
| V_Stack_Read: forall st i r_dst,
    i < (length st.(abs_stack)) ->
    Stack_Read r_dst i / st v--> (set_register_info st r_dst (get_stack_info st i))
| V_Stack_Write: forall st i r_src,
    i < (length st.(abs_stack)) ->
    Stack_Write i r_src / st v--> (set_stack_info st i (get_register_info st r_src))
| V_Indirect_Call: forall st reg,
    (get_register_info st reg).(abs_cf_bound) = bottom ->
    (get_register_info st rdi).(abs_heap_base) = bottom ->
    Indirect_Call reg / st v-->  st
| V_Direct_Call: forall st str,
    (get_register_info st rdi).(abs_heap_base) = bottom ->
    Direct_Call str / st v-->  st
| V_Branch: forall st cond, 
    Branch cond / st v--> st
| V_UniOp: forall st op r_dst,
    UniOp op r_dst / st v--> (set_register_info st r_dst empty_info)
| V_BinOp: forall st op r_dst r_src,
    BinOp op r_dst r_src / st v--> (set_register_info st r_dst empty_info)
| V_DivOp: forall st r_dst,
    DivOp r_dst / st v--> (set_register_info (set_register_info st rax empty_info) r_dst empty_info)
| V_Ret: forall st,
    empty st.(abs_stack) ->
    Ret / st v-->  st
  where " i '/' st 'v-->' st'" := (instr_class_vstep i st st').

Theorem instr_class_vstep_deterministic: forall init_st st st' i,
  i / init_st v--> st ->
  i / init_st v--> st' ->
  st = st'.
Proof.
  intros init_st st st' i H1 H2. inversion H1; inversion H2; subst; 
  try (inversion H8; auto);
  try (inversion H7; auto);
  try (inversion H6; auto);
  try (inversion H5; auto);
  try (inversion H4; auto).
Qed.

Inductive basic_block_vstep : (basic_block * abs_state) -> (basic_block * abs_state) -> Prop :=
| I_Basic_Block : forall i is st st',
  instr_class_vstep i st st' ->
  basic_block_vstep (i :: is, st) (is , st').

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Definition multi_basic_block_vstep := multi basic_block_vstep.

Lemma multi_basic_block_test :  exists abs_st,
  multi_basic_block_vstep (
Heap_Check rax ::
Heap_Read rbx rax rdi ::
nil, abs_empty_state) (nil, abs_st).
Proof.
  eexists. eapply multi_step.
  - apply I_Basic_Block. apply V_Heap_Check.
  - eapply multi_step.
    + apply I_Basic_Block. apply V_Heap_Read; auto.
    + apply multi_refl.
Qed.

Lemma register_get_after_set_eq : forall (abs_regs : abs_registers_ty) reg v,
  (t_update register_eq_dec abs_regs reg v) reg = v.
Proof.
  intros abs_regs reg v. unfold t_update. destruct (register_eq_dec reg reg).
  - reflexivity.
  - exfalso. apply n. reflexivity.
Qed.

Lemma register_get_after_set_neq : forall (abs_regs : abs_registers_ty) reg1 reg2 v,
    reg1 <> reg2 ->
    (t_update register_eq_dec abs_regs reg2 v) reg1 = abs_regs reg1.
Proof.
  intros abs_regs reg1 reg2 v Heq. unfold t_update. destruct (register_eq_dec reg2 reg1).
  - exfalso. apply Heq. auto.
  - reflexivity.
Qed.

Definition safe_stack_read (st : abs_state) (r_base : register) (r_src : register) (r_dst : register) : Prop :=
  r_base <> r_src /\ (get_register_info st r_base).(abs_heap_base) = bottom
                  /\ (get_register_info st r_src).(abs_heap_bound) = bottom.

Lemma read_after_check_is_safe: forall r_base r_src r_dst st, exists st' st'',
  r_base <> r_src ->
  (get_register_info st r_base).(abs_heap_base) = bottom ->
  Heap_Check r_src / st v--> st' /\ Heap_Read r_dst r_src r_base / st' v--> st''.
Proof.
  intros r_base r_src r_dst st. 
  eexists. eexists. intros Hneq Hbase.
  split.
  - apply V_Heap_Check.
  - apply V_Heap_Read.
    + unfold get_register_info in *. unfold set_register_info. simpl.
      rewrite register_get_after_set_neq; auto.
    + unfold get_register_info in *. unfold set_register_info. simpl.
      rewrite register_get_after_set_eq; auto.
Qed.


