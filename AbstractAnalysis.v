Require Import VerifiedVerifier.Machine.
Require Import VerifiedVerifier.BoundedLattice.
Require Import VerifiedVerifier.BinaryLattice.
Require Import VerifiedVerifier.Maps.
Require Import VerifiedVerifier.RecordUpdate.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.

Record info := mk_info {
  is_heap_base : BinarySet;
  heap_bounded : BinarySet;
  cf_bounded : BinarySet;
  above_stack_bounded: BinarySet;
  below_stack_bounded: BinarySet;
}.

Instance etaInfo : Settable _ := settable! mk_info
<
  is_heap_base;
  heap_bounded;
  cf_bounded;
  above_stack_bounded;
  below_stack_bounded
>.

Definition top_info :=
{| is_heap_base := top;
   heap_bounded := top;
   cf_bounded := top; 
   above_stack_bounded := top;
   below_stack_bounded := top;
|}.

Definition bot_info :=
{| is_heap_base := bottom;
   heap_bounded := bottom;
   cf_bounded := bottom; 
   above_stack_bounded := bottom;
   below_stack_bounded := bottom;
|}.

Definition abs_heap_base_info :=
top_info <| is_heap_base := bottom |>.

Definition abs_heap_bounded_info :=
top_info <| heap_bounded := bottom |>.

Definition abs_cf_bounded_info :=
top_info <| cf_bounded := bottom |>.

Definition abs_registers_ty := total_map register info.

Definition abs_stack_ty := list info.

Inductive abs_lifted_state_ty :=
| top_state
| bot_state
| sub_state.

Record abs_state := mk_abs_state {
  abs_regs : abs_registers_ty;
  abs_stack : abs_stack_ty;
  abs_lifted_state : abs_lifted_state_ty;

  abs_heap_base: nat;
  abs_below_stack_guard_size : nat;
  abs_above_stack_guard_size : nat;
  abs_above_heap_guard_size : nat; 
}.

Instance etaAbsState : Settable _ := settable! mk_abs_state 
<
  abs_regs;
  abs_stack;
  abs_lifted_state;

  abs_heap_base;
  abs_below_stack_guard_size;
  abs_above_stack_guard_size;
  abs_above_heap_guard_size 
>.

Definition abs_state_eq_dec : forall (x y : abs_state), {x=y} + {x<>y}.
intros x y; decide equality; admit.
Admitted.

Definition abs_state_eqb (a : abs_state) (b : abs_state) : bool :=
  if abs_state_eq_dec a b
  then true
  else false.

Definition bot_abs_state := {|
  abs_regs := t_empty bot_info;
  abs_stack := nil;
  abs_lifted_state := bot_state;

  abs_heap_base := 0;
  abs_below_stack_guard_size := 0;
  abs_above_stack_guard_size := 0;
  abs_above_heap_guard_size := 0; 
|}.

Definition top_abs_state := {|
  abs_regs := t_empty top_info;
  abs_stack := nil;
  abs_lifted_state := top_state;

  abs_heap_base := 0;
  abs_below_stack_guard_size := 0;
  abs_above_stack_guard_size := 0;
  abs_above_heap_guard_size := 0; 
|}.

Definition init_abs_state heap_base below_stack above_stack above_heap := {| 
(* Definition init_abs_state := {| *)
  abs_regs := t_update register_eq_dec (t_empty top_info) rdx abs_heap_base_info;
  abs_stack := nil;
  abs_lifted_state := sub_state;

  abs_heap_base := heap_base;
  abs_below_stack_guard_size := below_stack;
  abs_above_stack_guard_size := above_stack;
  abs_above_heap_guard_size := above_heap; 
|}.

Definition expand_abs_stack (s : abs_state) (i : nat) : abs_state :=
s <| abs_stack := (abs_stack s) ++ (repeat top_info i) |>.

Lemma expand_abs_stack_correct : forall s i,
  abs_stack (expand_abs_stack s i) = (abs_stack s) ++ (repeat top_info i).
Proof.
  intros. unfold expand_abs_stack. simpl. reflexivity.
Qed.

Fixpoint contract_abs_stack (s : abs_state) (i : nat) : abs_state :=
  match i with
  | 0 => s
  | S n =>
    contract_abs_stack (s <| abs_stack := removelast (abs_stack s) |>) n
  end.

Definition get_register_info (s : abs_state) (r : register) : info :=
  s.(abs_regs) r.

Definition set_register_info (s : abs_state) (r : register) (i : info) : abs_state :=
s <| abs_regs := t_update register_eq_dec s.(abs_regs) r i |>.

Definition clear_registers_info (s : abs_state) : abs_state :=
s <| abs_regs := t_empty top_info |>.

(* TODO: make stack indexing 64-bit *)
Definition get_stack_info (s : abs_state) (index : nat) : info :=
nth index s.(abs_stack) top_info.

(* this needs to be updated *)
Definition set_stack_info (s : abs_state) (index : nat) (i : info) : abs_state :=
s <| abs_stack := Machine.update s.(abs_stack) index i |>.

(*
Definition is_abs_error (s : abs_state) : bool :=
  s.(abs_error).


Definition set_error_state (s : abs_state) : abs_state :=
{| abs_regs := s.(abs_regs);
   abs_stack := s.(abs_stack);
   abs_error := true; |}.
*)

Definition join_info (i1 : info) (i2 : info) : info :=
{| is_heap_base := join_BinarySet i1.(is_heap_base) i2.(is_heap_base);
   heap_bounded := join_BinarySet i1.(heap_bounded) i2.(heap_bounded);
   cf_bounded := join_BinarySet i1.(cf_bounded) i2.(cf_bounded);
   above_stack_bounded := join_BinarySet i1.(above_stack_bounded) i2.(above_stack_bounded);
   below_stack_bounded := join_BinarySet i1.(below_stack_bounded) i2.(below_stack_bounded);
 |}.

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

Definition join_abs_state (s1 : abs_state) (s2 : abs_state) : abs_state :=
match (abs_lifted_state s1), (abs_lifted_state s2) with
| top_state, _ | _, top_state => top_abs_state
| sub_state, sub_state => if (abs_state_eq_dec s1 s2) then s1 else top_abs_state
| sub_state, _ => s1
| _, sub_state => s2
| _, _ => bot_abs_state
end.

Fixpoint join_abs_states (ss : list abs_state) : abs_state :=
  fold_left join_abs_state ss bot_abs_state.

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

Definition instr_class_flow_function (i : instr_class) (s : abs_state) : abs_state :=
match (abs_lifted_state s) with
| sub_state =>
  match i with 
  | Heap_Read r_dst _ _ _ => set_register_info s r_dst top_info
  | Heap_Write _ _ _ _ => s
  | Heap_Check r_src => set_register_info s r_src abs_heap_bounded_info
  | Call_Check r_src => set_register_info s r_src abs_cf_bounded_info
  | Reg_Move r_dst r_src => set_register_info s r_dst (get_register_info s r_src)
  | Reg_Write r_dst _ => set_register_info s r_dst top_info
  | Stack_Expand_Static i => expand_abs_stack s i
  | Stack_Expand_Dynamic i => expand_abs_stack s i
  | Stack_Contract i => contract_abs_stack s i
  | Stack_Read r_dst i => set_register_info s r_dst (get_stack_info s i)
  | Stack_Write i r_src => set_stack_info s i (get_register_info s r_src)
  | Op op rs_dst rs_src => fold_left (fun s r => set_register_info s r top_info) rs_dst s
  | Indirect_Call reg => clear_registers_info s
  | Direct_Call fname => clear_registers_info s
  | Branch _ _ _ => s
  | Jmp _ => s
  | Ret => s
  end
| _ => s
end.

Fixpoint basic_block_flow_function (bb : basic_block) (s : abs_state) : abs_state :=
fold_left (fun s' i => instr_class_flow_function i s') bb s.

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
nth n l bot_abs_state.

Definition nth_block (n : nat) (l : list basic_block) :=
nth n l nil.

Require Import FunInd.
Require Import Recdef.

Inductive leq_info : info -> info -> Prop :=
| leq_info_refl : forall i,
  leq_info i i
| leq_info_rule : forall x y,
  BinaryRel (is_heap_base x) (is_heap_base y) ->
  BinaryRel (heap_bounded x) (heap_bounded y) ->
  BinaryRel (cf_bounded x) (cf_bounded y) ->
  leq_info x y.

Inductive leq_abs_state : abs_state -> abs_state -> Prop :=
| leq_bot_state: forall s,
  leq_abs_state bot_abs_state s
| leq_top_state: forall s, 
  leq_abs_state s top_abs_state
| leq_sub_state: forall s1 s2,
  (abs_lifted_state s1) = sub_state ->
  (abs_lifted_state s2) = sub_state ->
  (abs_heap_base s1) = (abs_heap_base s2) ->
  (abs_below_stack_guard_size s1) = (abs_below_stack_guard_size s2) ->
  (abs_above_stack_guard_size s1) = (abs_above_stack_guard_size s2) ->
  (abs_above_heap_guard_size s1) = (abs_above_heap_guard_size s2) ->
  (forall reg, leq_info (get_register_info s1 reg) (get_register_info s2 reg)) ->
  (forall i, leq_info (get_stack_info s1 i) (get_stack_info s2 i)) -> 
  length (abs_stack s1) = length (abs_stack s2) ->
  leq_abs_state s1 s2.

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

(*Function worklist' (queue : list nat) (f : function) (ss : list abs_state) { wf ge_abs_states ss } : list abs_state :=
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
- intros.
Admitted.
*)
Fixpoint worklist (fuel : nat ) (queue : list nat) (f : function) (ss : list abs_state) : option (list abs_state) :=
match fuel with
| 0 => None
| S new_fuel =>
match queue with
| nil => Some ss
| i :: queue' => 
  let in_edges := get_incoming_edges (E f) i in
  let in_states := map (fun i => nth_state i ss) in_edges in
  let in_state := join_abs_states in_states in
  let out_state := basic_block_flow_function (nth_block i (V f)) in_state in 
  let out_edges := get_outgoing_edges (E f) i in
  let updated_edges := filter (fun i => abs_state_eqb (nth_state i ss) out_state) out_edges in
  let new_queue := queue' ++ updated_edges in
  let new_ss := fold_left (fun ss' i' => Machine.update ss' i' (join_abs_state (nth_state i ss') out_state)) updated_edges ss in
  worklist new_fuel new_queue f new_ss
end
end.

(*
Definition worklist (f : function) (ss : list abs_state) : list abs_state :=
  worklist' (seq 0 (length f)) f ss.
*)


Definition least_fixpoint (abs_st : abs_state) (f: function) : option (list abs_state) :=  
worklist 1000  (seq 0 (length (V f))) f ((abs_st :: nil) ++ (repeat bot_abs_state (length (V f) - 1))).


Definition instr_class_verifier (i : instr_class) (s : abs_state) : bool :=
(* I'm not sure what the right implementation is here *)
(* we might need to add a match for every top=>false bot=>true *)
match (abs_lifted_state s) with
| bot_state => true
| top_state => false
| sub_state =>
  match i with
  | Heap_Read _ r_offset r_index r_base => 
    andb (BinarySet_eqb (get_register_info s r_base).(is_heap_base) bottom)
      (andb (BinarySet_eqb (get_register_info s r_index).(heap_bounded) bottom)
        (BinarySet_eqb (get_register_info s r_offset).(heap_bounded) bottom))
  | Heap_Write r_offset r_index r_base _ =>
    andb (BinarySet_eqb (get_register_info s r_base).(is_heap_base) bottom)
      (andb (BinarySet_eqb (get_register_info s r_index).(heap_bounded) bottom)
        (BinarySet_eqb (get_register_info s r_offset).(heap_bounded) bottom))
  | Heap_Check _ => true
  | Call_Check _ => true
  | Reg_Move _ _ => true
  | Reg_Write _ _ => true
  | Stack_Expand_Static i => leb i (abs_above_stack_guard_size s)
  | Stack_Expand_Dynamic i => true
  | Stack_Contract i =>
    leb i (length s.(abs_stack))
  | Stack_Read _ i =>
    ltb i ((length s.(abs_stack)) + (abs_below_stack_guard_size s))
  | Stack_Write i _ =>
    ltb i (length s.(abs_stack))
  | Op _ _ _ => true
  | Indirect_Call reg =>
    andb (BinarySet_eqb (get_register_info s reg).(cf_bounded) bottom) 
      (BinarySet_eqb (get_register_info s rdi).(is_heap_base) bottom)
  | Direct_Call fname =>
    BinarySet_eqb (get_register_info s rdi).(is_heap_base) bottom (* TODO: do we need to check that the function name is defined *)
  | Branch _ _ _ => true
  | Jmp _ => true
  | Ret =>
    eqb (length s.(abs_stack)) 0
end
end.

Fixpoint basic_block_verifier (bb : basic_block) (s : abs_state) : bool :=
match bb with
| nil => true
| i :: bb' => andb (instr_class_verifier i s) (basic_block_verifier bb' (instr_class_flow_function i s))
end.

Fixpoint forall2b {A B} (f : A -> B -> bool) (aa : list A) (bb : list B) : bool :=
match aa, bb with
| nil, nil => true
| a :: aa', b :: bb' => (f a b) && (forall2b f aa' bb')
| _, _ => false
end.

Lemma forall2b_Forall2{A B}(p: A -> B -> bool)(xs: list A)(ys: list B):
  forall2b p xs ys = true ->
  Forall2 (fun x y => p x y = true) xs ys.
revert ys.
induction xs; intros; destruct ys; simpl in *; try discriminate; constructor.
- apply Bool.andb_true_iff in H.
  tauto.
- apply IHxs.
  apply Bool.andb_true_iff in H.
  tauto.
Qed.

Lemma Forall2_forall2 : forall {A B : Type} P l1 l2,
  Forall2 P l1 l2 <-> length l1 = length l2 /\
                      forall (a : A) (b : B) n x1 x2, n < length l1 -> nth n l1 a = x1 -> nth n l2 b = x2 -> P x1 x2.
Proof.
intros A B P l1. induction l1; intro l2.
* split; intro H.
  + inversion_clear H. split; simpl; auto. intros. Omega.omega.
  + destruct H as [H _]. destruct l2; try discriminate. constructor.
* split; intro H.
  + inversion_clear H. rewrite IHl1 in H1. destruct H1. split; simpl; auto.
    intros. destruct n; subst; trivial. eapply H1; eauto. Omega.omega.
  + destruct H as [Hlen H].
    destruct l2; simpl in Hlen; try discriminate. constructor.
    apply (H a b 0); trivial; simpl; try Omega.omega.
    rewrite IHl1. split; try Omega.omega.
    intros. eapply (H a0 b0 (S n)); simpl; eauto. simpl; Omega.omega.
Qed.

Definition function_verifier (f : function) (abs_st : abs_state) : bool :=
match (least_fixpoint abs_st f) with
| None => false
| Some ss => forall2b basic_block_verifier (V f) ss
end.

Definition program_verifier (p : program) (abs_st : abs_state) : bool :=
forallb (fun f => function_verifier f abs_st) p.

Lemma program_verifier_impl_function_verifier: forall abs_st p f,
  In f p ->
  program_verifier p abs_st = true ->
  function_verifier f abs_st = true.
Proof.
  intros. unfold program_verifier in H0. rewrite forallb_forall in H0.
  apply H0. apply H.
Qed.

Lemma function_verifier_impl_basic_block_verifier: forall abs_st abs_st' f bb,
  In bb (V f) ->
  function_verifier f abs_st = true ->
  (exists fixpoint_list, 
    In abs_st' fixpoint_list ->
    basic_block_verifier bb abs_st' = true).
Proof.
Admitted.
(*
  intros. unfold function_verifier in H0. destruct (least_fixpoint abs_st f) eqn:Hfix.
  - exists l. apply forall2b_Forall2 in H0. apply Forall2_forall2 in H0 as [Hlen Hforall].
    intros. eapply Hforall. Search (In).
    * eapply In_nth in H. specialize  destruct H. destruct H. eapply H. apply In_nth in H.

 induction H0.
    + intros. inversion H0.
    + intros. Search (Forall2). apply IHForall2.
      * Search (In _ _).
   apply in_cons in H. Search (In _ _).
  - inversion H0.

 Search (option -> bool). inversion H0.
*)


Lemma basic_block_verifier_impl_instr_class_verifier: forall abs_st abs_st' bb i,
  In i bb ->
  basic_block_verifier bb abs_st = true ->

  (exists fixpoint_list, 
    In abs_st' fixpoint_list ->
    instr_class_verifier i abs_st' = true).
Proof.
  intros. unfold basic_block_verifier in H0. induction bb.
  - Search (In _ nil). apply in_nil in H. eauto.
  - simpl in H0. admit.
Admitted.

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