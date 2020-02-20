Require Import Coq.FSets.FMapList.
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

Definition Registers := fmap register int64.

Definition Stack := list int8.

Definition Heap := fmap int64 int8.

Definition Flags := fmap flag int1.

Record State := {
  regs : Registers;
  flags : Flags;
  stack : Stack;
  heap : Heap;
}.

Inductive Value : Set :=
| A_Reg : register -> Value
| A_Const : int64 -> Value
| A_MultPlus : int64 -> Value -> Value -> Value.

Fixpoint value_to_int64 (v : Value) (s : State) : int64 :=
match v with
| A_Reg r => (regs s) r
| A_Const c => c
| A_MultPlus m v1 v2 => Word.mul m (Word.add (value_to_int64 v1 s) (value_to_int64 v2 s))
end.

Inductive InstrClass := 
| Mem_Read : register -> Value -> Flags -> InstrClass
| Mem_Write : register -> Value -> Flags -> InstrClass
| Bounds_Check : register -> Flags -> InstrClass
| Branch : Flags -> InstrClass
| Reg_Write : register -> Value -> Flags -> InstrClass
| Stack_Expand : Value -> Flags -> InstrClass
| Stack_Contract : Value -> Flags -> InstrClass
| Stack_Read : register -> Value -> Flags -> InstrClass
| Stack_Write : Value -> Value -> Flags -> InstrClass
| Ret : Flags -> InstrClass
| Call : Flags -> InstrClass.

Definition run_instr (inst : InstrClass) (s : State) : State := 
  match inst with 
| Mem_Read r v f => 
| _ => s
end.
