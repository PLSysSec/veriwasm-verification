Require Import Semantics.
Require Import Machine.
Require Import Bits.

Definition is_mem_bounded (s : state) (r_src : register) (r_base : register) : bool :=
  andb (Word.eq (get_register s r_base) s.(heap_base)) (Word.lt (get_register s r_src) fourGB).

Definition is_stack_index_safe (s : state) (i : nat) : bool :=
  gtb (length s.(stack)) i.

Definition is_instr_class_safe (s : state) (i : instr_class) : bool :=
  match i with
| Heap_Read r_dst r_src r_base => is_mem_bounded s r_src r_base
| Heap_Write r_dst r_val r_base => is_mem_bounded s r_dst r_base
| Stack_Contract i => is_stack_index_safe s i
| Stack_Read : register -> nat -> instr_class
| Stack_Write : nat -> register -> instr_class
| Indirect_Call : register -> instr_class
| _ => true
end.

(*
| Stack_Expand : nat -> instr_class
| Stack_Contract : nat -> instr_class
| Stack_Read : register -> nat -> instr_class
| Stack_Write : nat -> register -> instr_class
| Indirect_Call : register -> instr_class
| Direct_Call : instr_class
| Ret : instr_class.
*)

Inductive instr_class := 
| Heap_Read : register -> register -> register -> instr_class
| Heap_Write : register -> register -> register -> instr_class
| Heap_Check : register -> instr_class
(*| Branch : flags_ty -> instr_class*)
| CF_Check : register -> instr_class
| Reg_Move : register -> register -> instr_class
| Reg_Write : register -> value -> instr_class
| Stack_Expand : nat -> instr_class
| Stack_Contract : nat -> instr_class
| Stack_Read : register -> nat -> instr_class
| Stack_Write : nat -> register -> instr_class
| Indirect_Call : register -> instr_class
| Direct_Call : instr_class
| Ret : instr_class.

