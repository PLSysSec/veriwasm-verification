Require Import Coq.FSets.FMapList.
Require Import Coq.Lists.List.
(*Require Import Coq.Vectors.Vector.*)
(*Require Import SFI.Machine.Bits.*)
(*Require Import bbv.Word.*)

(*Notation word1 := (word 1).
Notation word8 := (word 8).
Notation word64 := (word 64).
Notation wzero8 := (wzero 8).*)

Inductive register : Set :=
| rax
| rbx
| rcx
| rdx
| rbp
| rsp
| rsi
| rdi
| rip
| r8
| r9
| r10
| r11
| r12
| r13
| r14
| r15.

Definition register_eq_dec : forall (x y:register), {x=y} + {x<>y}.
  intros ; decide equality.
Defined.

Inductive flag : Set :=
| of
| sf
| zf
| pf
| cf.

Inductive info : Set :=
| unbounded
| mem_bounded
| cf_bounded
| heap_base.

Definition fmap (A B:Type) := 
  A -> B.

Definition set A (eq_dec:forall (x y:A),{x=y}+{x<>y}) B (f:fmap A B) (x:A) (v:B) : fmap A B :=
  fun y => if eq_dec x y then v else f y.

Definition get A B (f:fmap A B) (x:A) : B := 
  f x.

Definition registers_ty := fmap register info.

Definition frame_ty := list info.

Definition stack_ty := list frame_ty.

(* Definition heap_ty := list info.*)

(* Definition flags_ty := fmap flag state. *)

Record state := {
  regs : registers_ty;
(*  flags : flags_ty; *)
  frame : frame_ty;
  stack : stack_ty;
(*  heap : heap_ty; *)
}.

Definition empty_state :=
{| regs := fun r => if register_eq_dec r rdi then heap_base else unbounded;
   frame := nil;
   stack := nil;
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
| A_Reg r => (regs s) r
| A_Const c => c
| A_MultPlus m v1 v2 => wmult m (wplus (value_to_word64 s v1) (value_to_word64 s v2))
end.
*)

(*
Definition read_register (s : machine) (r : register) : word64 :=
  get register word64 s.(regs) r.
*)

(*
Definition write_register (s : machine) (r : register) (v : word64) : machine :=
{| regs := set register register_eq_dec word64 s.(regs) r v;
   flags := s.(flags);
   stack := s.(stack);
   heap := s.(heap) |}.
*)

(*
Definition set_flags (s : machine) (f : flags_ty) : machine :=
{| regs := s.(regs);
   flags := f;
   stack := s.(stack);
   heap := s.(heap) |}. 
*)

Definition expand_stack (s : state) (i : nat) : state :=
{| regs := s.(regs);
(*   flags := s.(flags); *)
   frame := s.(frame) ++ (repeat unbounded i);
   stack := s.(stack);
(*   heap := s.(heap) *)|}.

Fixpoint contract_stack (s : state) (i : nat) : state :=
match i with
| 0 => s
| S n =>
contract_stack {| regs := s.(regs);
(*   flags := s.(flags); *)
   frame := removelast s.(frame);
   stack := s.(stack);
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
Program Fixpoint read_stack (s : machine) (i : nat) (sz : nat) : word (8 * sz):=
match sz with
| 0 => WO
| S sz' => combine (read_stack_word s i) (read_stack s (i+1) (sz'))
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

Definition get_register_info (s : state) (r : register) : info :=
  get register info s.(regs) r.

Definition set_register_info (s : state) (r : register) (i : info) : state :=
{| regs := set register register_eq_dec info s.(regs) r i;
   frame := s.(frame);
   stack := s.(stack);
(*   heap := s.(heap) *) |}.

Definition get_stack_info (s : state) (index : nat) : info :=
nth index s.(frame) unbounded.

Definition pop_frame (s : state) : state :=
{| regs := s.(regs);
   frame := last s.(stack) nil;
   stack := tail s.(stack);
(*   heap := s.(heap) *) |}.

Definition push_frame (s : state) : state :=
{| regs := s.(regs);
   frame := nil;
   stack := s.(frame) :: s.(stack);
(*   heap := s.(heap) *) |}.

Fixpoint update {A} (l : list A) (i : nat) (v : A) : list A :=
match l, i with
| nil , _ => l
| h :: t, 0 => v :: t
| h :: t, S i' => update t i' v
end.

(* this needs to be updated *)
Definition set_stack_info (s : state) (index : nat) (i : info) : state :=
{| regs := s.(regs);
   frame := update s.(frame) index i;
   stack := s.(stack);
 (*  heap := s.(heap) *) |}.

Inductive instr_class := 
| Heap_Read : register -> register -> register -> instr_class
| Heap_Write : register -> register -> register -> instr_class
| Heap_Check : register -> instr_class
(*| Branch : flags_ty -> instr_class*)
| CF_Check : register -> instr_class
| Reg_Move : register -> register -> instr_class
| Reg_Write : register (*-> register *)-> instr_class
| Stack_Expand : nat -> instr_class
| Stack_Contract : nat -> instr_class
| Stack_Read : register -> nat -> instr_class
| Stack_Write : nat -> register -> instr_class
| Ret : instr_class
| Call : instr_class.

Reserved Notation " st '|-' i  '-->' st' "
                  (at level 40, st' at level 39).
Inductive instr_class_step : instr_class -> state -> state -> Prop := 
| I_Heap_Read: forall st r_base r_src r_dst,
    get_register_info st r_base = heap_base ->
    get_register_info st r_src = mem_bounded ->
      instr_class_step (Heap_Read r_dst r_src r_base) st (set_register_info st r_dst unbounded) 
| I_Heap_Write: forall st r_base r_src r_dst,
    get_register_info st r_base = heap_base ->
    get_register_info st r_src = mem_bounded -> 
      instr_class_step (Heap_Write r_dst r_src r_base) st st
| I_Heap_Check: forall st r_src,
      instr_class_step (Heap_Check r_src) st (set_register_info st r_src mem_bounded)
| I_CF_Check: forall st r_src,
      instr_class_step (CF_Check r_src) st (set_register_info st r_src cf_bounded)
| I_Reg_Move: forall st r_src r_dst,
  st |- (Reg_Move r_dst r_src) --> (set_register_info st r_dst (get_register_info st r_src))
| I_Reg_Write: forall st r_dst,
      instr_class_step (Reg_Write r_dst) st (set_register_info st r_dst unbounded)
| I_Stack_Expand: forall st i,
      instr_class_step (Stack_Expand i) st (expand_stack st i)
| I_Stack_Contract: forall st i,
      instr_class_step (Stack_Contract i) st (contract_stack st i)
| I_Stack_Read: forall st i r_dst,
      instr_class_step (Stack_Read r_dst i) st (set_register_info st r_dst (get_stack_info st i))
| I_Stack_Write: forall st i r_src,
      instr_class_step (Stack_Write i r_src) st (set_stack_info st i (get_register_info st r_src))
| I_Ret: forall st,
      instr_class_step (Ret) st (pop_frame st)
| I_Call: forall st,
  get_register_info st rdi = heap_base ->
      instr_class_step (Call) st (push_frame st)
  where " st '|-' i '-->' st' " := (instr_class_step i st st').

Definition cfg_node := list instr_class.

Record cfg_ty := {
  nodes : list cfg_node;
  edges : list (cfg_node * cfg_node)
}.

Theorem sfi_property: forall (cfg : cfg_ty) exists st,
  (* local properties -> *)
 empty |- cfg --> st.

Definition terminates (instrs : list instr_class) : Prop :=
  exists st, fold_left instr_class_step empty_state instrs = st.

