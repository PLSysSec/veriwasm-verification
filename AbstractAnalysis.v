Require Import VerifiedVerifier.Machine.
Require Import VerifiedVerifier.BoundedLattice.
Require Import VerifiedVerifier.BinaryLattice.
Require Import VerifiedVerifier.Maps.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.

Record info := {
  abs_heap_base : BinarySet;
  abs_heap_bound : BinarySet;
  abs_cf_bound : BinarySet;
}.

Definition top_info :=
  {| abs_heap_base := top;
     abs_heap_bound := top;
     abs_cf_bound := top; |}.

Definition bot_info :=
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

Record abs_state' := {
  abs_regs : abs_registers_ty;
(*  flags : flags_ty; *)
  abs_stack : abs_stack_ty;
(*  abs_error : bool; *)
}.

Inductive abs_state :=
| top_state : abs_state
| bot_state : abs_state
| sub_state : abs_state' -> abs_state.

Definition abs_state'_eq_dec : forall (x y : abs_state'), {x=y} + {x<>y}.
intros x y. decide equality; subst; try decide equality; try decide equality; try decide equality.
admit. (* funcational extensionality we can get rid of making this an axiim if we use a different implementation of map *)
Admitted.

Definition abs_state_eq_dec : forall (x y : abs_state), {x=y} + {x<>y}.
intros x y; decide equality; apply abs_state'_eq_dec.
Qed.

Definition abs_state_eqb (a : abs_state) (b : abs_state) : bool :=
  if abs_state_eq_dec a b
  then true
  else false.

Definition abs_top_state := top_state.
(* {| abs_regs := fun r => if register_eq_dec r rdi
                          then abs_heap_base_info
                          else empty_info;
   abs_stack := nil;
   abs_error := false; |}. *)

Definition abs_bot_state := bot_state.
(* {| abs_regs := t_empty bottom_info;
   abs_stack := nil;
   abs_error := false; |}. *)

Definition init_state' :=
 {| abs_regs := fun r => if register_eq_dec r rdi
                          then abs_heap_base_info
                          else top_info;
   abs_stack := nil; |}.

Definition init_state := sub_state init_state'.

Definition expand_abs_stack (s : abs_state') (i : nat) : abs_state' :=
 {| abs_regs := s.(abs_regs);
    abs_stack := s.(abs_stack) ++ (repeat top_info i); |}.

Fixpoint contract_abs_stack (s : abs_state') (i : nat) : abs_state' :=
  match i with
  | 0 => s
  | S n =>
    contract_abs_stack {| abs_regs := s.(abs_regs);
                                     abs_stack := removelast s.(abs_stack) |} n
  end.

Definition get_register_info (s : abs_state') (r : register) : info :=
  s.(abs_regs) r.

Definition set_register_info (s : abs_state') (r : register) (i : info) : abs_state' :=
{| abs_regs := t_update register_eq_dec s.(abs_regs) r i;
   abs_stack := s.(abs_stack); |}.

Definition clear_registers_info (s : abs_state') : abs_state' :=
{| abs_regs := (fun _ => top_info) ;
   abs_stack := s.(abs_stack); |}.


(* TODO: make stack indexing 64-bit *)
Definition get_stack_info (s : abs_state') (index : nat) : info :=
nth index s.(abs_stack) top_info.

(* this needs to be updated *)
Definition set_stack_info (s : abs_state') (index : nat) (i : info) : abs_state' :=
{| abs_regs := s.(abs_regs);
   abs_stack := Machine.update s.(abs_stack) index i; |}.

(*
Definition is_abs_error (s : abs_state) : bool :=
  s.(abs_error).


Definition set_error_state (s : abs_state) : abs_state :=
{| abs_regs := s.(abs_regs);
   abs_stack := s.(abs_stack);
   abs_error := true; |}.
*)

Definition join_info (i1 : info) (i2 : info) : info :=
{| abs_heap_base := join_BinarySet i1.(abs_heap_base) i2.(abs_heap_base);
   abs_heap_bound := join_BinarySet i1.(abs_heap_bound) i2.(abs_heap_bound);
   abs_cf_bound := join_BinarySet i1.(abs_cf_bound) i2.(abs_cf_bound); |}.

Definition join_abs_regs (r1 : abs_registers_ty) (r2 : abs_registers_ty) : abs_registers_ty :=
  fun r => join_info (r1 r) (r2 r).

Fixpoint join_abs_stack (s1 : abs_stack_ty) (s2 : abs_stack_ty) : abs_stack_ty :=
  match s1 with
  | i1 :: s1' =>
    match s2 with
    | i2 :: s2' => join_info i1 i2 :: join_abs_stack s1' s2'
    | _ => nil
    end
  | _ => nil
  end.

Definition join_abs_state' (s1 : abs_state') (s2 : abs_state') : abs_state' :=
{| abs_regs := join_abs_regs s1.(abs_regs) s2.(abs_regs);
   abs_stack := join_abs_stack s1.(abs_stack) s2.(abs_stack); |}.

Definition join_abs_state (s1 : abs_state) (s2 : abs_state) : abs_state :=
match s1, s2 with
| top_state, _ | _, top_state => top_state
| sub_state s1', sub_state s2' => if (abs_state'_eq_dec s1' s2') then sub_state s1' else top_state
| sub_state s1', _ => sub_state s1'
| _, sub_state s2' => sub_state s2'
| _, _ => bot_state
end.

Fixpoint join_abs_states (ss : list abs_state) : abs_state :=
  fold_left join_abs_state ss bot_state.

(*
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

Definition meet_abs_state' (s1 : abs_state') (s2 : abs_state') : abs_state' :=
{| abs_regs := meet_abs_regs s1.(abs_regs) s2.(abs_regs);
   abs_stack := meet_abs_stack s1.(abs_stack) s2.(abs_stack); |}.


Definition meet_abs_state (s1 : abs_state) (s2 : abs_state) : abs_state :=
match s1 with
| bot_state => bot_state
| 
{| abs_regs := meet_abs_regs s1.(abs_regs) s2.(abs_regs);
   abs_stack := meet_abs_stack s1.(abs_stack) s2.(abs_stack); |}.



(* TODO: need to add a bottom state; currently abs_bottom_state has a stack
 * of length 0, which means that meet_abs_state will return an error state
 * for any meet with a non zero length stack. *)
Fixpoint meet_abs_states (ss : list abs_state) : abs_state :=
  match ss with
  | s :: ss' => meet_abs_state s (meet_abs_states ss')
  | _ => abs_bottom_state
  end.


Fixpoint get_parent_nodes (n : node_ty) (es : list edge_ty) : list node_ty :=
  match es with
  | e :: es' => if node_ty_eqb n (snd (fst e))
    then fst (fst e) :: get_parent_nodes n es'
    else get_parent_nodes n es'
  | _ => nil
  end.

Fixpoint get_child_nodes (n : node_ty) (es : list edge_ty) : list node_ty :=
  match es with
  | e :: es' => if node_ty_eqb n (fst (fst e))
    then snd (fst e) :: get_child_nodes n es'
    else get_child_nodes n es'
  | _ => nil
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
*)
(* TODO: Add check instructions for everything else *)
Reserved Notation " i '/' st 'v-->' st' "
                  (at level 40, st' at level 39).

Definition instr_class_flow_function (i : instr_class) (s : abs_state') : abs_state' :=
match i with 
| Heap_Read r_dst _ _ => set_register_info s r_dst top_info
| Heap_Write _ _ _ => s
| Heap_Check r_src => set_register_info s r_src abs_heap_bounded_info
| Call_Check r_src => set_register_info s r_src abs_cf_bounded_info
| Reg_Move r_dst r_src => set_register_info s r_dst (get_register_info s r_src)
| Reg_Write r_dst _ => set_register_info s r_dst top_info
| Stack_Expand i => expand_abs_stack s i
| Stack_Contract i => contract_abs_stack s i
| Stack_Read r_dst i => set_register_info s r_dst (get_stack_info s i)
| Stack_Write i r_src => set_stack_info s i (get_register_info s r_src)
| Op op rs_dst rs_src => fold_left (fun s r => set_register_info s r top_info) rs_dst s
| Indirect_Call reg => clear_registers_info s
| Direct_Call fname => clear_registers_info s
| Branch _ _ _ => s
| Jmp _ => s
| Ret => s
end.

Fixpoint basic_block_flow_function (bb : basic_block) (s : abs_state) : abs_state :=
match bb with
| nil => s
| i :: bb' => 
  match s with
  | top_state => top_state
  | bot_state => bot_state
  | sub_state s' => basic_block_flow_function bb' (sub_state (instr_class_flow_function i s'))
  end
end.

Fixpoint map2 {A B C} (f : A -> B -> C) (aa : list A) (bb : list B) : list C :=
match aa, bb with
| a :: aa', b :: bb' => (f a b) :: (map2 f aa' bb')
| _, _ => nil
end.

Fixpoint eq_list (l1 : list abs_state) (l2 : list abs_state) : bool :=
match l1, l2 with 
| nil, nil => true
| a :: aa, b :: bb => andb (abs_state_eqb a b) (eq_list aa bb)
| _, _ => false
end.

Fixpoint get_incoming_edges (E: list (nat * nat) ) (i : nat) :=
match E with
| nil => nil
| (src, dst) :: E' => 
  let incoming_edges := get_incoming_edges E' i in
  if (eqb i dst) then src :: incoming_edges else incoming_edges 
end.  

Fixpoint get_outgoing_edges (E: list (nat * nat) ) (i : nat) :=
match E with
| nil => nil
| (src, dst) :: E' => 
  let incoming_edges := get_incoming_edges E' i in
  if (eqb i src) then dst :: incoming_edges else incoming_edges 
end.

Definition nth_state (n : nat) (l : list abs_state) :=
nth n l bot_state.

Definition nth_block (n : nat) (l : list basic_block) :=
nth n l nil.

Require Import FunInd.
Require Import Recdef.

Inductive leq_info : info -> info -> Prop :=
| leq_info_refl : forall i,
  leq_info i i
| leq_info_rule : forall x y,
  BinaryRel (abs_heap_base x) (abs_heap_base y) ->
  BinaryRel (abs_heap_bound x) (abs_heap_bound y) ->
  BinaryRel (abs_cf_bound x) (abs_cf_bound y) ->
  leq_info x y.

Inductive leq_abs_state' : abs_state' -> abs_state' -> Prop :=
| leq_abs_state'_rule: forall st st',
  (forall reg, leq_info (get_register_info st reg) (get_register_info st' reg)) ->
  (forall i, leq_info (get_stack_info st i) (get_stack_info st' i)) -> 
  length (abs_stack st) = length (abs_stack st') ->
  leq_abs_state' st st'.

Inductive leq_abs_state : abs_state -> abs_state -> Prop :=
| leq_bot_state: forall s, 
  leq_abs_state bot_state s
| leq_top_state: forall s, 
  leq_abs_state s top_state
| leq_sub_state: forall s1 s2,
  leq_abs_state' s1 s2 ->
  leq_abs_state (sub_state s1) (sub_state s2).

Definition ge_abs_state s1 s2 := leq_abs_state s2 s1.

Inductive ge_abs_states : list abs_state -> list abs_state -> Prop :=
| ge_abs_states_nil: 
  ge_abs_states nil nil
| ge_abs_states_cons: forall s1 s2 ss1 ss2,
  ge_abs_state s1 s2 ->
  ge_abs_states ss1 ss2 ->
  ge_abs_states (s1 :: ss1) (s2 :: ss2).

Require Import Recdef.

(*Function div2_Fun (n:nat)
        {wf lt }
        : nat :=
match n with
| S (S k) => S (div2_Fun k)
| _ => 0
end.*)

Function worklist' (queue : list nat) (f : function) (ss : list abs_state) { wf ge_abs_states ss } : list abs_state :=
match queue with
| nil => ss
| i :: queue' => 
  let in_edges := get_incoming_edges (E f) i in
  let in_states := map (fun i => nth_state i ss) in_edges in
  let in_state := join_abs_states in_states in
  let out_state := basic_block_flow_function (nth_block i (V f)) in_state in 
  let out_edges := get_outgoing_edges (E f) i in
  let updated_edges := filter (fun i => abs_state_eqb (nth_state i ss) out_state) out_edges in
  let new_queue := queue' ++ updated_edges in
  let new_ss := fold_left (fun ss' i' => Machine.update ss' i' (join_abs_state (nth_state i ss') out_state)) updated_edges ss in
  worklist' new_queue f new_ss
end.
Proof.
Admitted.

Fixpoint worklist (f : function) (ss : list abs_state) : list abs_state :=
  worklist' (seq 0 (length f)) f ss.

Definition greatest_fixpoint (f: function) : list abs_state :=  
worklist f ((init_state :: nil) ++ (repeat bot_state (length (V f) - 1))).

Definition instr_class_verifier (i : instr_class) (s : abs_state') : Prop :=
(* I'm not sure what the right implementation is here *)
(* we might need to add a match for every top=>false bot=>true *)
  match i with
  | Heap_Read _ r_src r_base => 
    (get_register_info s r_base).(abs_heap_base) = bottom /\ (get_register_info s r_src).(abs_heap_bound) = bottom
  | Heap_Write r_dst _ r_base =>
    (get_register_info s r_base).(abs_heap_base) = bottom /\ (get_register_info s r_dst).(abs_heap_bound) = bottom
  | Stack_Contract i =>
    i <= (length s.(abs_stack))
  | Stack_Read _ i =>
    i < (length s.(abs_stack))
  | Stack_Write i _ =>
    i < (length s.(abs_stack))
  | Indirect_Call reg =>
    (get_register_info s reg).(abs_cf_bound) = bottom /\ (get_register_info s rdi).(abs_heap_base) = bottom
  | Direct_Call fname =>
    (get_register_info s rdi).(abs_heap_base) = bottom (* TODO: do we need to check that the function name is defined *)
  | Ret =>
    length s.(abs_stack) = 0
  | _ => True
end.

Fixpoint basic_block_verifier (bb : basic_block) (s : abs_state) : Prop :=
match bb with
| nil => True
| i :: bb' => 
  match s with
  | top_state => False
  | bot_state => True
  | sub_state s' => instr_class_verifier i s' /\ basic_block_verifier bb' (sub_state (instr_class_flow_function i s'))
  end
end.

(*
Definition function_verifier (f : function) : Prop :=
Forall2 basic_block_verifier (f.V) (greatest_fixpoint f).

Definition program_verifier (p : program) : Prop :=
Forall function_verifier p.
*)

(*
Inductive instr_class_vstep : instr_class -> abs_state' -> abs_state' -> Prop := 
| V_Heap_Read: forall st r_base r_src r_dst,
    (* r_base <> r_src -> *) (* not sure if we need this to make the proofs easier *)
    (get_register_info st r_base).(abs_heap_base) = bottom ->
    (get_register_info st r_src).(abs_heap_bound) = bottom ->
    Heap_Read r_dst r_src r_base / st v--> (set_register_info st r_dst top_info) 
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
    Reg_Write r_dst val / st v--> (set_register_info st r_dst top_info)
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
| V_Op: forall st op rs_dst rs_src,
    Op op rs_dst rs_src / st v--> fold_left (fun s r => set_register_info s r top_info) rs_dst st
| V_Indirect_Call: forall st reg,
    (get_register_info st reg).(abs_cf_bound) = bottom ->
    (get_register_info st rdi).(abs_heap_base) = bottom ->
    Indirect_Call reg / st v-->  st
| V_Direct_Call: forall st str,
    (get_register_info st rdi).(abs_heap_base) = bottom ->
    Direct_Call str / st v-->  st
| V_Branch: forall st cond t_label f_label, 
    Branch cond t_label f_label / st v--> st
| V_Jmp: forall st j_label,
    Jmp j_label / st v--> st
| V_Ret: forall st,
    length st.(abs_stack) = 0 ->
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
  | i :: bb' => bb_flow_function (instr_class_flow_function st i) bb'
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

(* TODO: make sure abs_registers is complete *)
Definition is_program_safe (p : program_ty) : bool :=
  let worklist_terminal_states := map run_worklist p.(funs) in
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
*)