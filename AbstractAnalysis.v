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

Definition bottom_info :=
  {| abs_heap_base := bottom;
     abs_heap_bound := bottom;
     abs_cf_bound := bottom; |}.

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
  abs_error : bool;
}.

Definition abs_state_eq_dec : forall (x y : abs_state), {x=y} + {x<>y}.
intros x y. decide equality; subst; try decide equality; try decide equality; try decide equality.
admit. (* funcational extensionality we can get rid of making this an axiim if we use a different implementation of map *)
Admitted.

Definition abs_state_eqb (a : abs_state) (b : abs_state) : bool :=
  if abs_state_eq_dec a b
  then true
  else false.

Definition abs_empty_state :=
{| abs_regs := fun r => if register_eq_dec r rdi
                          then abs_heap_base_info
                          else empty_info;
   abs_stack := nil;
   abs_error := false; |}.

Definition abs_bottom_state :=
{| abs_regs := t_empty bottom_info;
   abs_stack := nil;
   abs_error := false; |}.

Definition expand_abs_stack (s : abs_state) (i : nat) : abs_state :=
{| abs_regs := s.(abs_regs);
(*   flags := s.(flags); *)
   abs_stack := s.(abs_stack) ++ (repeat empty_info i);
   abs_error := s.(abs_error); |}.

Fixpoint contract_abs_stack (s : abs_state) (i : nat) : abs_state :=
match i with
| 0 => s
| S n =>
contract_abs_stack {| abs_regs := s.(abs_regs);
(*   flags := s.(flags); *)
   abs_stack := removelast s.(abs_stack);
   abs_error := s.(abs_error); |} n
end.

Definition get_register_info (s : abs_state) (r : register) : info :=
  s.(abs_regs) r.

Definition set_register_info (s : abs_state) (r : register) (i : info) : abs_state :=
{| abs_regs := t_update register_eq_dec s.(abs_regs) r i;
   abs_stack := s.(abs_stack);
   abs_error := s.(abs_error); |}.

(* TODO: make stack indexing 64-bit *)
Definition get_stack_info (s : abs_state) (index : nat) : info :=
nth index s.(abs_stack) empty_info.

(* this needs to be updated *)
Definition set_stack_info (s : abs_state) (index : nat) (i : info) : abs_state :=
{| abs_regs := s.(abs_regs);
   abs_stack := Machine.update s.(abs_stack) index i;
   abs_error := s.(abs_error); |}.

Definition is_abs_error (s : abs_state) : bool :=
  s.(abs_error).

Definition set_error_state (s : abs_state) : abs_state :=
{| abs_regs := s.(abs_regs);
   abs_stack := s.(abs_stack);
   abs_error := true; |}.

Definition meet_info (i1 : info) (i2 : info) : info :=
{| abs_heap_base := meet_BinarySet i1.(abs_heap_base) i2.(abs_heap_base);
   abs_heap_bound := meet_BinarySet i1.(abs_heap_bound) i2.(abs_heap_bound);
   abs_cf_bound := meet_BinarySet i1.(abs_cf_bound) i2.(abs_cf_bound); |}.

(*Definition abs_registers_ty := total_map register info.*)
Definition meet_abs_regs (r1 : abs_registers_ty) (r2 : abs_registers_ty) : abs_registers_ty :=
  fun r => meet_info (r1 r) (r2 r).

(* NOTE: We don't set and error state here if stacks are different lengths
 * because that is done in meet_abs_state *)
Fixpoint meet_abs_stack (s1 : abs_stack_ty) (s2 : abs_stack_ty) : abs_stack_ty :=
  match s1 with
  | i1 :: s1' =>
    match s2 with
    | i2 :: s2' => meet_info i1 i2 :: meet_abs_stack s1' s2'
    | _ => nil
    end
  | _ => nil
  end.

Definition meet_abs_state (s1 : abs_state) (s2 : abs_state) : abs_state :=
{| abs_regs := meet_abs_regs s1.(abs_regs) s2.(abs_regs);
   abs_stack := meet_abs_stack s1.(abs_stack) s2.(abs_stack);
   abs_error := orb (orb s1.(abs_error) s2.(abs_error))
                    (negb (eqb (length s1.(abs_stack)) (length s2.(abs_stack))));
|}.

(* TODO: need to add a bottom state; currently abs_bottom_state has a stack
 * of length 0, which means that meet_abs_state will return an error state
 * for any meet with a non zero length stack. *)
Fixpoint meet_abs_states (ss : list abs_state) : abs_state :=
  match ss with
  | s :: ss' => meet_abs_state s (meet_abs_states ss')
  | _ => abs_bottom_state
  end.

Definition get_parent_states (n : node_ty) (m : total_map node_ty abs_state) (cfg : cfg_ty) : list abs_state :=
  map m (get_parent_nodes n cfg.(edges)).

Fixpoint get_terminal_nodes (ns : list node_ty) (es : list edge_ty) : list node_ty :=
  match ns with
  | n :: ns' => if eqb (length (get_parent_nodes n es)) 0
      then n :: get_terminal_nodes ns' es
      else get_terminal_nodes ns' es
  | _ => nil
  end.

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
| V_Op: forall st op rs_dst rs_src,
    Op op rs_dst rs_src / st v--> fold_left (fun s r => set_register_info s r empty_info) rs_dst st
| V_Ret: forall st,
    empty st.(abs_stack) ->
    Ret / st v-->  st
  where " i '/' st 'v-->' st'" := (instr_class_vstep i st st').
Hint Constructors instr_class_vstep.

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
  | Op _ rs_dst rs_src => fold_left (fun s r => set_register_info s r empty_info) rs_dst st
  | Ret => if eqb (length st.(abs_stack)) 0
    then st
    else set_error_state st
  end.

Fixpoint bb_flow_function (st : abs_state) (bb : basic_block) : abs_state :=
  match bb with
  | i :: bb' => bb_flow_function (flow_function st i) bb'
  | _ => st
  end.

(* TODO: This shouldn't need fuel because we can prove it converges *)
(* TODO: Might wnat to return an error state if we run out of fuel *)
Fixpoint worklist (cfg : cfg_ty) (queue : list node_ty) (m : total_map node_ty abs_state)
                    (fuel : nat) : total_map node_ty abs_state :=
  match fuel with
  | S fuel' =>
    match queue with
    | n :: queue' =>
      let in_state := meet_abs_states (get_parent_states n m cfg) in
      let prev_out_state := m n in
      let new_out_state := bb_flow_function in_state (fst n) in
      if abs_state_eqb prev_out_state new_out_state
        then worklist cfg queue' m fuel'
        else
          let new_queue := queue' ++ get_child_nodes n cfg.(edges) in
          let new_map := t_update node_ty_eq_dec m n new_out_state in
          worklist cfg new_queue new_map fuel'
    | _ => m
    end
  | _ => t_empty abs_empty_state
  end.

(* TODO: This can be removed when we get the proof about worklist termination *)
Definition default_fuel := 100000.

Definition empty_state_map : total_map node_ty abs_state := t_empty abs_empty_state.

Definition run_worklist (f : function_ty) : abs_state :=
  let state_map := worklist (fst f) ((fst f).(start_node) :: nil) empty_state_map default_fuel in
  let terminal_states := map state_map (get_terminal_nodes (fst f).(nodes) (fst f).(edges)) in
  fold_left meet_abs_state terminal_states abs_empty_state.

Definition verify_function (f : function_ty) : bool :=
  abs_error (run_worklist f).

(* TODO: make sure abs_registers is complete *)
Definition verify_program (p : program_ty) : bool :=
  let worklist_terminal_states := map run_worklist p.(fun_list) in
  let worklist_errors := map abs_error worklist_terminal_states in
  fold_left orb worklist_errors false.

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
