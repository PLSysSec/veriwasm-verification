Require Import VerifiedVerifier.Machine.
Require Import VerifiedVerifier.BinaryLattice.
Require Import VerifiedVerifier.Maps.
Require Import VerifiedVerifier.RecordUpdate.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.

Record info := mk_info {
  is_heap_base : BinarySet;
  heap_bounded : BinarySet;
  cf_bounded : BinarySet;
  is_globals_base : BinarySet;
  above_stack_bounded: BinarySet;
  below_stack_bounded: BinarySet;
}.

Instance etaInfo : Settable _ := settable! mk_info
<
  is_heap_base;
  heap_bounded;
  cf_bounded;
  is_globals_base;
  above_stack_bounded;
  below_stack_bounded
>.

Definition top_info :=
{| is_heap_base := top;
   heap_bounded := top;
   cf_bounded := top;
   is_globals_base := top;
   above_stack_bounded := top;
   below_stack_bounded := top;
|}.

Definition bot_info :=
{| is_heap_base := bottom;
   heap_bounded := bottom;
   cf_bounded := bottom;
   is_globals_base := bottom;
   above_stack_bounded := bottom;
   below_stack_bounded := bottom;
|}.

Definition abs_heap_base_info :=
top_info <| is_heap_base := bottom |>.

Definition abs_heap_bounded_info :=
top_info <| heap_bounded := bottom |>.

Definition abs_cf_bounded_info :=
top_info <| cf_bounded := bottom |>.

Definition abs_globals_base_info :=
top_info <| is_globals_base := bottom |>.

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

  abs_globals_size : nat;
  abs_globals_base : nat;

  abs_program : option program;
  abs_frame_size : nat;
  abs_call_stack : list nat;
  abs_rsp : nat;
  abs_stack_base : nat;
  abs_stack_size : nat;
  abs_max_stack_size : nat;
}.

Instance etaAbsState : Settable _ := settable! mk_abs_state
<
  abs_regs;
  abs_stack;
  abs_lifted_state;

  abs_heap_base;
  abs_below_stack_guard_size;
  abs_above_stack_guard_size;
  abs_above_heap_guard_size;

  abs_globals_size;
  abs_globals_base;

  abs_program;
  abs_frame_size;
  abs_call_stack;
  abs_rsp;
  abs_stack_base;
  abs_stack_size;
  abs_max_stack_size
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

  abs_globals_size := 4096;
  abs_globals_base := 0;

  abs_program := None;
  abs_frame_size := 0;
  abs_call_stack := nil;
  abs_rsp := 0;
  abs_stack_base := 0;
  abs_stack_size := 0;
  abs_max_stack_size := 0;
|}.

Definition top_abs_state := {|
  abs_regs := t_empty top_info;
  abs_stack := nil;
  abs_lifted_state := top_state;

  abs_heap_base := 0;
  abs_below_stack_guard_size := 0;
  abs_above_stack_guard_size := 0;
  abs_above_heap_guard_size := 0;

  abs_globals_size := 4096;
  abs_globals_base := 0;

  abs_program := None;
  abs_frame_size := 0;
  abs_call_stack := nil;
  abs_rsp := 0;
  abs_stack_base := 0;
  abs_stack_size := 0;
  abs_max_stack_size := 0;
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

  abs_globals_size := 0;
  abs_globals_base := 0;

  abs_program := None;
  abs_frame_size := 0;
  abs_call_stack := nil;
  abs_rsp := 0;
  abs_stack_base := 0;
  abs_stack_size := 0;
  abs_max_stack_size := 0;
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

Definition get_stack_info (s : abs_state) (index : nat) : info :=
nth index s.(abs_stack) top_info.

(* this needs to be updated *)
Definition set_stack_info (s : abs_state) (index : nat) (i : info) : abs_state :=
s <| abs_stack := Machine.update s.(abs_stack) index i |>.

Definition join_info (i1 : info) (i2 : info) : info :=
{| is_heap_base := join_BinarySet i1.(is_heap_base) i2.(is_heap_base);
   heap_bounded := join_BinarySet i1.(heap_bounded) i2.(heap_bounded);
   cf_bounded := join_BinarySet i1.(cf_bounded) i2.(cf_bounded);
   is_globals_base := join_BinarySet i1.(is_globals_base) i2.(is_globals_base);
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

Reserved Notation " i '/' st 'v-->' st' "
                  (at level 40, st' at level 39).

Definition instr_class_flow_function (i : instr_ty) (s : abs_state) : abs_state :=
match (abs_lifted_state s) with
| sub_state =>
  match i.(instr) with
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
  | Get_Globals_Base r_base r_dst => set_register_info s r_dst abs_globals_base_info
  | Globals_Read _ _ r_dst => set_register_info s r_dst top_info
  | Globals_Write _ _ _ => s
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
  BinaryRel (is_globals_base x) (is_globals_base y) ->
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
  (abs_program s1) = (abs_program s2) ->
  (abs_frame_size s1) = (abs_frame_size s2) ->
  (abs_call_stack s1) = (abs_call_stack s2) ->
  (abs_rsp s1) = (abs_rsp s2) ->
  (abs_stack_base s1) = (abs_stack_base s2) ->
  (abs_stack_size s1) = (abs_stack_size s2) ->
  (abs_max_stack_size s1) = (abs_max_stack_size s2) ->
  (abs_globals_size s1) = (abs_globals_size s2) ->
  (abs_globals_base s1) = (abs_globals_base s2) ->
  leq_abs_state s1 s2.

Definition ge_abs_state s1 s2 := leq_abs_state s2 s1.

Inductive ge_abs_states : list abs_state -> list abs_state -> Prop :=
| ge_abs_states_nil:
  ge_abs_states nil nil
| ge_abs_states_cons: forall s1 s2 ss1 ss2,
  ge_abs_state s1 s2 ->
  ge_abs_states ss1 ss2 ->
  ge_abs_states (s1 :: ss1) (s2 :: ss2).

Definition get_function st fname : option function :=
  match st.(abs_program) with
  | Some p => nth_error p.(Funs) fname
  | None => None
  end.

Definition get_bb st i : option basic_block :=
  match (abs_call_stack st) with
  | nil => None
  | fname :: _ =>
    match (get_function st fname) with
    | None => None
    | Some f => nth_error (V f) i
    end
  end.

Require Import Recdef.

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

Definition least_fixpoint (abs_st : abs_state) (f: function) : option (list abs_state) :=
worklist 1000  (seq 0 (length (V f))) f ((abs_st :: nil) ++ (repeat bot_abs_state (length (V f) - 1))).

Definition instr_class_verifier (i : instr_class) (s : abs_state) : bool :=
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
    (andb
      (andb
        (ltb i ((length s.(abs_stack)) + (abs_below_stack_guard_size s)))
        (ltb (s.(abs_stack_base)) ((s.(abs_rsp) - i))))
      (ltb (s.(abs_rsp) - i) (s.(abs_stack_base) + s.(abs_stack_size))))
  | Stack_Write i _ =>
    (andb
      (andb
        (ltb i (length s.(abs_stack)))
        (ltb (s.(abs_stack_base)) ((s.(abs_rsp) - i))))
      (ltb (s.(abs_rsp) - i) (s.(abs_stack_base) + s.(abs_max_stack_size))))
  | Op _ _ _ => true
  | Indirect_Call reg =>
    andb (BinarySet_eqb (get_register_info s reg).(cf_bounded) bottom)
      (BinarySet_eqb (get_register_info s rdi).(is_heap_base) bottom)
  | Direct_Call fname =>
    andb (match get_function s fname with
          | Some _ => true
          | _ => false
          end)
         (BinarySet_eqb (get_register_info s rdi).(is_heap_base) bottom)
  | Branch _ l1 l2 =>
    andb (match get_bb s l1 with
          | Some _ => true
          | _ => false
          end)
         (match get_bb s l2 with
          | Some _ => true
          | _ => false
          end)
  | Jmp l =>
    match get_bb s l with
    | Some _ => true
    | _ => false
    end
  | Get_Globals_Base r_base _ => BinarySet_eqb (get_register_info s r_base).(is_heap_base) bottom
  | Globals_Read r_base i _ => andb (BinarySet_eqb (get_register_info s r_base).(is_globals_base) bottom)
                                    (ltb i s.(abs_globals_size))
  | Globals_Write r_base i _ => andb (BinarySet_eqb (get_register_info s r_base).(is_globals_base) bottom)
                                     (ltb i s.(abs_globals_size))
  | Ret =>
    eqb s.(abs_frame_size) 0
end
end.

Fixpoint basic_block_verifier (bb : basic_block) (s : abs_state) : bool :=
match bb with
| nil => true
| i :: bb' => andb (instr_class_verifier i.(instr) s) (basic_block_verifier bb' (instr_class_flow_function i s))
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
forallb (fun f => function_verifier f abs_st) p.(Funs).

Lemma program_verifier_impl_function_verifier: forall abs_st p f,
  In f p.(Funs) ->
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

Lemma basic_block_verifier_impl_instr_class_verifier: forall abs_st abs_st' bb i,
  In i bb ->
  basic_block_verifier bb abs_st = true ->

  (exists fixpoint_list,
    In abs_st' fixpoint_list ->
    instr_class_verifier i.(instr) abs_st' = true).
Proof.
  intros. unfold basic_block_verifier in H0. induction bb.
  - Search (In _ nil). apply in_nil in H. eauto.
  - simpl in H0. admit.
Admitted.

