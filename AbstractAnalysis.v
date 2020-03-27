Require Import VerifiedVerifier.Machine.
Require Import VerifiedVerifier.BoundedLattice.
Require Import VerifiedVerifier.BinaryLattice.
Require Import VerifiedVerifier.Maps.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

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

Definition abs_registers_ty := total_map register info.

Definition abs_stack_ty := list info.

Record abs_state := {
  abs_regs : abs_registers_ty;
(*  flags : flags_ty; *)
  abs_stack : abs_stack_ty;
  error : bool;
}.

Definition abs_empty_state :=
{| abs_regs := fun r => if register_eq_dec r rdi
                          then abs_heap_base_info
                          else empty_info;
   abs_stack := nil;
   error := false; |}.

Definition expand_abs_stack (s : abs_state) (i : nat) : abs_state :=
{| abs_regs := s.(abs_regs);
(*   flags := s.(flags); *)
   abs_stack := s.(abs_stack) ++ (repeat empty_info i);
   error := s.(error); |}.

Fixpoint contract_abs_stack (s : abs_state) (i : nat) : abs_state :=
match i with
| 0 => s
| S n =>
contract_abs_stack {| abs_regs := s.(abs_regs);
(*   flags := s.(flags); *)
   abs_stack := removelast s.(abs_stack);
   error := s.(error); |} n
end.

Definition get_register_info (s : abs_state) (r : register) : info :=
  s.(abs_regs) r.

Definition set_register_info (s : abs_state) (r : register) (i : info) : abs_state :=
{| abs_regs := t_update register_eq_dec s.(abs_regs) r i;
   abs_stack := s.(abs_stack);
   error := s.(error); |}.

(* TODO: make stack indexing 64-bit *)
Definition get_stack_info (s : abs_state) (index : nat) : info :=
nth index s.(abs_stack) empty_info.

(* this needs to be updated *)
Definition set_stack_info (s : abs_state) (index : nat) (i : info) : abs_state :=
{| abs_regs := s.(abs_regs);
   abs_stack := Machine.update s.(abs_stack) index i;
   error := s.(error); |}.

Definition is_abs_error (s : abs_state) : bool :=
  s.(error).

Definition set_error_state (s : abs_state) : abs_state :=
{| abs_regs := s.(abs_regs);
   abs_stack := s.(abs_stack);
   error := true; |}.

Definition empty {A} (l : list A) :=
  l = nil.

Definition initialize_worklist (cfg : cfg_ty) : total_map node_ty abs_state :=
  t_empty abs_empty_state.

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

(* TODO: The semantics for operations might be opcode-dependent; this should get fixed
 * when opcodes return lists of modified registers *)
(* TODO: This can be combined with the inductive definition for instr_class_vstep *)
(* TODO: Can infer bounds for any literals on Reg_Write *)
Definition flow_function (st : abs_state) (i : instr_class) : abs_state :=
  match i with
  | Heap_Read r_dst r_src r_base =>
    if andb (BinarySet_eqb (get_register_info st r_base).(abs_heap_base) bottom)
            (BinarySet_eqb (get_register_info st r_src).(abs_heap_bound) bottom)
    then set_register_info st r_dst empty_info
    else set_error_state st
  | Heap_Write r_dst _ r_base =>
    if andb (BinarySet_eqb (get_register_info st r_base).(abs_heap_base) bottom)
            (BinarySet_eqb (get_register_info st r_dst).(abs_heap_bound) bottom)
    then st
    else set_error_state st
  | Heap_Check r => set_register_info st r abs_heap_bounded_info
  | Call_Check r => set_register_info st r abs_cf_bounded_info
  | Reg_Move r_dst r_src => set_register_info st r_dst (get_register_info st r_src)
  | Reg_Write r _ => set_register_info st r empty_info
  | Stack_Expand i => expand_abs_stack st i
  | Stack_Contract i =>
    if leb i (length st.(abs_stack))
    then contract_abs_stack st i
    else set_error_state st
  | Stack_Read r i => if ltb i (length st.(abs_stack))
    then set_register_info st r (get_stack_info st i)
    else set_error_state st
  | Stack_Write i r => if ltb i (length st.(abs_stack))
    then set_stack_info st i (get_register_info st r)
    else set_error_state st
  | Indirect_Call r =>
    if andb (BinarySet_eqb (get_register_info st r).(abs_cf_bound) bottom)
            (BinarySet_eqb (get_register_info st rdi).(abs_heap_base) bottom)
    then st
    else set_error_state st
  | Direct_Call _ =>
    if BinarySet_eqb (get_register_info st rdi).(abs_heap_base) bottom
    then st
    else set_error_state st
  | Branch _ => st
  | UniOp _ r => set_register_info st r empty_info
  | BinOp _ r_dst r_src => set_register_info st r_dst empty_info
  | DivOp r => set_register_info (set_register_info st rax empty_info) r empty_info
  | Ret => if eqb (length st.(abs_stack)) 0
    then st
    else set_error_state st
  end.

Definition worklist (cfg : cfg_ty) (map : total_map node_ty BinarySet) (fuel : nat) : total_map node_ty BinarySet :=
  match fuel with
  | S fuel' => t_empty bottom
  | _ => t_empty bottom
  end.

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
