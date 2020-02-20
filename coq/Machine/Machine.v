Require Import Coq.FSets.FMapList.
Require Import Coq.Lists.List.
Require Import SFI.Machine.Bits.

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

Definition fmap (A B:Type) := 
  A -> B.

Definition set A (eq_dec:forall (x y:A),{x=y}+{x<>y}) B (f:fmap A B) (x:A) (v:B) : fmap A B :=
  fun y => if eq_dec x y then v else f y.

Definition get A B (f:fmap A B) (x:A) : B := 
  f x.

Definition registers_ty := fmap register int64.

Definition stack_ty := list int8.

Definition heap_ty := fmap int64 int8.

Definition flags_ty := fmap flag int1.

Record state := {
  regs : registers_ty;
  flags : flags_ty;
  stack : stack_ty;
  heap : heap_ty;
}.

Inductive value : Set :=
| A_Reg : register -> value
| A_Const : int64 -> value
| A_MultPlus : int64 -> value -> value -> value.

Fixpoint value_to_int64 (s : state) (v :value) : int64 :=
match v with
| A_Reg r => (regs s) r
| A_Const c => c
| A_MultPlus m v1 v2 => Word.mul m (Word.add (value_to_int64 s v1) (value_to_int64 s v2))
end.

Definition get_register (s : state) (r : register) : int64 :=
  get register int64 s.(regs) r.

Definition set_register (s : state) (r : register) (v : int64) : state :=
{| regs := set register register_eq_dec int64 s.(regs) r v;
   flags := s.(flags);
   stack := s.(stack);
   heap := s.(heap) |}.

Definition set_flags (s : state) (f : flags_ty) : state :=
{| regs := s.(regs);
   flags := f;
   stack := s.(stack);
   heap := s.(heap) |}. 

Definition expand_stack (s : state) (i : nat) : state :=
{| regs := s.(regs);
   flags := s.(flags);
   stack := s.(stack) ++ (repeat Word.zero i);
   heap := s.(heap) |}.

Fixpoint contract_stack (s : state) (i : nat) : state :=
match i with
| 0 => s
| S n =>
contract_stack {| regs := s.(regs);
   flags := s.(flags);
   stack := removelast s.(stack);
   heap := s.(heap) |} n
end.

Definition read_stack (s : state) (i : nat) : int64 :=
nth_default Word.zero s.(stack) i.


Inductive instr_class := 
| Heap_Read : register -> value -> flags_ty -> instr_class (* read memory location stored in value and write its value to register *)
| Heap_Write : register -> value -> flags_ty -> instr_class (* update location stored in register to value *)
| Bounds_Check : register -> flags_ty -> instr_class
| Branch : flags_ty -> instr_class
| Reg_Write : register -> value -> flags_ty -> instr_class
| Stack_Expand : nat -> flags_ty -> instr_class
| Stack_Contract : nat -> flags_ty -> instr_class
| Stack_Read : register -> nat -> flags_ty -> instr_class
| Stack_Write : nat -> value -> flags_ty -> instr_class
| Ret : flags_ty -> instr_class
| Call : flags_ty -> instr_class.

Definition run_instr (inst : instr_class) (s : state) : state := 
  match inst with 
| Heap_Read r v f => set_register s r (value_to_int64 s v)
| Heap_Write r v f => s
| Bounds_Check r f => s
| Branch f => s
| Reg_Write r v f => s
| Stack_Expand i f => expand_stack s i
| Stack_Contract i f => contract_stack s i
| Stack_Read r i f => set_register s r (value_to_int64 
| Stack_Write i v f => s
| Ret f => s
| Call f => s
end.
