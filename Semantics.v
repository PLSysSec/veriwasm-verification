Require Import Coq.Lists.List.
Require Import BinInt.
Require Import Machine.
Require Import Bits.

(*TODO: figure out if we need uints vs ints*)
Definition registers_ty := fmap register int64.

Definition stack_ty := list int64.

Definition heap_ty := fmap int64 int64.

Definition flags_ty := fmap flag int1.

Record state := {
  regs : registers_ty;
  flags : flags_ty;
  stack : stack_ty;
  heap : heap_ty;
}.

Fixpoint value_to_int64 (s : state) (v :value) : int64 :=
match v with
| A_Reg r => (regs s) r
| A_Const c => c
| A_MultPlus m v1 v2 => Word.mul m (Word.add (value_to_int64 s v1) (value_to_int64 s v2))
end.

Definition get_register (s : state) (r : register) : int64 :=
  get s.(regs) r.

Definition set_register (s : state) (r : register) (v : int64) : state :=
{| regs := set register_eq_dec s.(regs) r v;
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

Definition write_stack (s : state) (i : nat) (val : int64) : state :=
{| regs := s.(regs);
   flags := s.(flags);
   stack := update s.(stack) i val;
   heap := s.(heap) |}.

Definition int64_eq_dec : forall x y : int64, { eq x y } + { ~ eq x y }.
Proof.
	intros. case_eq (Word.eq x y); intros.
		- left. inversion H. admit.  (*unfold eq; int_to_Z_tac. omega.*)
		- right. unfold Word.eq in H. admit. (*unfold eq; int_to_Z_tac. omega.*)
Admitted.

Definition read_heap (s : state) (i : int64) : int64 :=
s.(heap) i.

Definition write_heap (s : state) (i : int64) (v : int64) : state :=
{| regs := s.(regs);
	 flags := s.(flags);
	 stack := s.(stack);
	 heap := set int64_eq_dec s.(heap) i v |}.

Definition run_instr (inst : instr_class) (s : state) : state := 
  match inst with 
| Heap_Read r_dst r_src r_base => set_register s r_dst (read_heap s (Word.add (get_register s r_src) (get_register s r_base)))
| Heap_Write r_dst r_val r_base => write_heap s (Word.add (get_register s r_dst) (get_register s r_base)) (get_register s r_val)
| Heap_Check r => set_register s r (Word.modu (get_register s r) (Word.shl (Word.repr 2) (Word.repr 32)))
| CF_Check r => s (*TODO: Figure out wtf to do.*)
| Reg_Write r v => set_register s r (value_to_int64 s v)
| Reg_Move r_dst r_src => set_register s r_dst (get_register s r_src)
| Stack_Expand i => expand_stack s i
| Stack_Contract i => contract_stack s i
| Stack_Read r i => set_register s r (read_stack s i)
| Stack_Write i r => write_stack s i (get_register s r)
(*TODO: Make sure calls are right*)
| Indirect_Call r => s
| Direct_Call => s
| Ret => s
end.
