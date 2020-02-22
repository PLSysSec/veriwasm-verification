Require Import Coq.FSets.FMapList.
Require Import Coq.Lists.List.
(* Require Import Coq.Vectors.Vector.*)
(*Require Import SFI.Machine.Bits.*)
Require Import bbv.Word.

Notation word1 := (word 1).
Notation word8 := (word 8).
Notation word64 := (word 64).
Notation wzero8 := (wzero 8).

Inductive register : Set :=
| Rax
| Rbx
| Rcx
| Rdx
| Rbp
| Rsp
| Rsi
| Rdi
| Rip
| R8
| R9
| R10
| R11
| R12
| R13
| R14
| R15.

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
| cf_bounded.

Definition fmap (A B:Type) := 
  A -> B.

Definition set A (eq_dec:forall (x y:A),{x=y}+{x<>y}) B (f:fmap A B) (x:A) (v:B) : fmap A B :=
  fun y => if eq_dec x y then v else f y.

Definition get A B (f:fmap A B) (x:A) : B := 
  f x.

Definition registers_ty := fmap register info.

Definition stack_ty := list info.

Definition heap_ty := list info.

(* Definition flags_ty := fmap flag state. *)

Record state := {
  regs : registers_ty;
(*  flags : flags_ty; *)
  stack : stack_ty;
  heap : heap_ty;
}.
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
   stack := s.(stack) ++ (repeat unbounded i);
   heap := s.(heap) |}.

Fixpoint contract_stack (s : state) (i : nat) : state :=
match i with
| 0 => s
| S n =>
contract_stack {| regs := s.(regs);
(*   flags := s.(flags); *)
   stack := removelast s.(stack);
   heap := s.(heap) |} n
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
   stack := s.(stack);
   heap := s.(heap) |}.

Definition get_stack_info (s : state) (index : nat) : info :=
nth index s.(stack) unbounded.

(* this needs to be updated *)
Definition set_stack_info (s : state) (index : nat) (i : info) : state :=
s.


Inductive instr_class := 
| Heap_Read : register -> register -> instr_class
| Heap_Write : register -> register -> instr_class
| Heap_Bounds_Check : register -> instr_class
(*| Branch : flags_ty -> instr_class*)
| CF_Bounds_Check : register -> instr_class
| Reg_Write : register -> register -> instr_class
| Stack_Expand : nat -> instr_class
| Stack_Contract : nat -> instr_class
| Stack_Read : register -> nat -> instr_class
| Stack_Write : nat -> register -> instr_class
| Ret : instr_class
| Call : instr_class.


Inductive instr_class_step : instr_class -> state -> state -> Prop := 
| I_Heap_Read: ∀st,
     instr_class_step (Heap_Read r_dst r_src) st 
| I_Heap_Write r_dst r_src => s
| I_Heap_Bounds_Check r_src => s
| I_CF_Bounds_Check r_src =>
| I_Reg_Write r_dst r_src => s
| I_Stack_Expand i => expand_stack s i
| I_Stack_Contract i => contract_stack s i
| I_Stack_Read r_dst i => write_register s r  
| I_Stack_Write i r_src => s
| I_Ret => s
| I_Call => s
end.


Definition run_instr (inst : instr_class) (s : machine) : machine := 
  match inst with 
| Heap_Read r_dst r_src => s
| Heap_Write r_dst r_src => s
| Heap_Bounds_Check r_src => s
| CF_Bounds_Check r_src =>
| Reg_Write r_dst r_src => s
| Stack_Expand i => expand_stack s i
| Stack_Contract i => contract_stack s i
| Stack_Read r_dst i => write_register s r  
| Stack_Write i r_src => s
| Ret => s
| Call => s
end.
