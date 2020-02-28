Require Import Semantics.
Require Import Machine.
Require Import Bits.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.ListSet.
Require Import AbstractAnalysis.

Definition is_mem_bounded (s : state) (r_src : register) (r_base : register) : bool :=
  andb (Word.eq (get_register s r_base) s.(heap_base)) (Word.lt (get_register s r_src) fourGB).

Definition is_stack_contract_safe (s : state) (i : nat) : bool :=
  leb i (length s.(stack)).

Definition is_stack_index_safe (s : state) (i : nat) : bool :=
  ltb i (length s.(stack)).

Definition is_return_safe (s : state) : bool :=
  eqb (length s.(stack)) 0.

Definition is_rdi_heapbase (s : state) : bool :=
  Word.eq (get_register s rdi) s.(heap_base).

Definition is_function_index_safe (s : state) (r : register) : bool :=
  set_mem int64_eq_dec (get_register s r) s.(function_table).

Definition is_instr_class_safe (s : state) (i : instr_class) : bool :=
  match i with
| Heap_Read r_dst r_src r_base => is_mem_bounded s r_src r_base
| Heap_Write r_dst r_val r_base => is_mem_bounded s r_dst r_base
| Stack_Contract i => is_stack_contract_safe s i
| Stack_Read _ i => is_stack_index_safe s i
| Stack_Write i _ => is_stack_index_safe s i
| Direct_Call => is_rdi_heapbase s
| Indirect_Call r => andb (is_rdi_heapbase s) (is_function_index_safe s r)
| Ret => is_return_safe s
| _ => true
end.

Theorem safe_instr : 
  forall i st,
    exists st', instr_class_flow_function i st st' ->
    is_instr_class_safe st i = true.