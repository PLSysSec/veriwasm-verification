Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import BinInt.
Require Import Machine.
Require Import Bits.

(*TODO: figure out if we need uints vs ints*)
Definition registers_ty := fmap register int64.

Definition stack_ty := list int64.

Definition heap_ty := fmap int64 int64.

Definition flags_ty := fmap flag int1.

Definition function_table_ty := set int64.

Record state := {
  regs : registers_ty;
  flags : flags_ty;
  stack : stack_ty;
  heap : heap_ty;
  heap_base : int64;
  function_table : function_table_ty;
}.

Fixpoint value_to_int64 (s : state) (v :value) : int64 :=
match v with
| A_Reg r => (regs s) r
| A_Const c => c
| A_MultPlus m v1 v2 => Word.mul m (Word.add (value_to_int64 s v1) (value_to_int64 s v2))
end.

Definition get_register (s : state) (r : register) : int64 :=
  map_get s.(regs) r.

Definition set_register (s : state) (r : register) (v : int64) : state :=
{| regs := map_set register_eq_dec s.(regs) r v;
   flags := s.(flags);
   stack := s.(stack);
   heap := s.(heap);
   heap_base := s.(heap_base);
   function_table := s.(function_table) |}.

Definition set_flags (s : state) (f : flags_ty) : state :=
{| regs := s.(regs);
   flags := f;
   stack := s.(stack);
   heap := s.(heap);
   heap_base := s.(heap_base) ;
   function_table := s.(function_table) |}.

Definition expand_stack (s : state) (i : nat) : state :=
{| regs := s.(regs);
   flags := s.(flags);
   stack := s.(stack) ++ (repeat Word.zero i);
   heap := s.(heap);
   heap_base := s.(heap_base) ;
   function_table := s.(function_table) |}.

Fixpoint contract_stack (s : state) (i : nat) : state :=
match i with
| 0 => s
| S n =>
contract_stack {| regs := s.(regs);
   flags := s.(flags);
   stack := removelast s.(stack);
   heap := s.(heap);
   heap_base := s.(heap_base) ;
   function_table := s.(function_table) |}
 n
end.

Definition read_stack (s : state) (i : nat) : int64 :=
nth_default Word.zero s.(stack) i.

Definition write_stack (s : state) (i : nat) (val : int64) : state :=
{| regs := s.(regs);
   flags := s.(flags);
   stack := update s.(stack) i val;
   heap := s.(heap);
   heap_base := s.(heap_base) ;
   function_table := s.(function_table) |}.

Definition read_heap (s : state) (i : int64) : int64 :=
s.(heap) i.



Definition write_heap (s : state) (i : int64) (v : int64) : state :=
{| regs := s.(regs);
	 flags := s.(flags);
	 stack := s.(stack);
	 heap := map_set int64_eq_dec s.(heap) i v;
   heap_base := s.(heap_base);
   function_table := s.(function_table) |}.

Definition fourGB : int64 := (Word.shl (Word.repr 2) (Word.repr 32)).

(*TODO: This doesn't handle signed/unsigned conversions correctly*)
Definition run_conditional (c : conditional) (s : state) : bool :=
  match c with
| Not_Equal r1 r2 => negb (Word.eq (get_register s r1) (get_register s r2))
| Equal r1 r2 => Word.eq (get_register s r1) (get_register s r2)
| Greater r1 r2 => Word.lt (get_register s r2) (get_register s r1)
| Greater_Equal r1 r2 => orb (Word.lt (get_register s r2) (get_register s r1)) (Word.eq (get_register s r1) (get_register s r2))
| Above r1 r2 => Word.ltu (get_register s r2) (get_register s r1)
| Above_Equal r1 r2 => orb (Word.ltu (get_register s r2) (get_register s r1)) (Word.eq (get_register s r1) (get_register s r2))
| Lesser r1 r2 => Word.lt (get_register s r1) (get_register s r2)
| Lesser_Equal r1 r2 => orb (Word.lt (get_register s r1) (get_register s r2)) (Word.eq (get_register s r1) (get_register s r2))
| Below r1 r2 => Word.ltu (get_register s r1) (get_register s r2)
| Below_Equal r1 r2 => orb (Word.ltu (get_register s r1) (get_register s r2)) (Word.eq (get_register s r1) (get_register s r2))
| Counter_Register_Zero => Word.eq (get_register s rcx) (Word.repr 0)
end.

Definition run_instr (inst : instr_class) (s : state) : state := 
  match inst with 
| Heap_Read r_dst r_src r_base => set_register s r_dst (read_heap s (Word.add (get_register s r_src) (get_register s r_base)))
| Heap_Write r_dst r_val r_base => write_heap s (Word.add (get_register s r_dst) (get_register s r_base)) (get_register s r_val)
| Heap_Check r => set_register s r (Word.modu (get_register s r) fourGB)
| Call_Check r => s (*TODO: Figure out wtf to do.*)
| Reg_Write r v => set_register s r (value_to_int64 s v)
| Reg_Move r_dst r_src => set_register s r_dst (get_register s r_src)
| Stack_Expand i => expand_stack s i
| Stack_Contract i => contract_stack s i
| Stack_Read r i => set_register s r (read_stack s i)
| Stack_Write i r => write_stack s i (get_register s r)
| Branch c => s
(*TODO: Make sure calls are right*)
| Indirect_Call r => s
| Direct_Call => s
| Ret => s
end.

Theorem run_instr_deterministic : forall init_st st st' i, 
  run_instr i init_st = st ->
  run_instr i init_st = st' ->
  st = st'.
Proof.
  intros init_st st st' i H1 H2. rewrite <- H1, H2. auto.
Qed.

Reserved Notation " i '/' st 'i-->' st' "
                  (at level 40, st' at level 39).
Inductive instr_class_istep : instr_class -> state -> state -> Prop := 
| I_Heap_Read: forall st r_base r_src r_dst,
    Heap_Read r_dst r_src r_base / st i--> set_register st r_dst (read_heap st (Word.add (get_register st r_src) (get_register st r_base)))
| I_Heap_Write: forall st r_base r_val r_dst,
    Heap_Write r_dst r_val r_base / st i--> write_heap st (Word.add (get_register st r_dst) (get_register st r_base)) (get_register st r_val)
| I_Heap_Check: forall st r_src,
    Heap_Check r_src / st i--> set_register st r_src (Word.modu (get_register st r_src) fourGB)
| I_Call_Check: forall st r_src,
    Call_Check r_src / st i--> st (* probably wrong *)
| I_Reg_Move: forall st r_src r_dst,
    Reg_Move r_dst r_src / st i--> set_register st r_dst (get_register st r_src)
| I_Reg_Write: forall st r_dst val,
    Reg_Write r_dst val / st i--> set_register st r_dst (value_to_int64 st val)
| I_Stack_Expand: forall st i,
    Stack_Expand i / st i--> expand_stack st i
| I_Stack_Contract: forall st i,
    Stack_Contract i / st i--> contract_stack st i
| I_Stack_Read: forall st i r_dst,
    Stack_Read r_dst i / st i--> set_register st r_dst (read_stack st i)
| I_Stack_Write: forall st i r_src,
    Stack_Write i r_src / st i--> write_stack st i (get_register st r_src)
(* those calls might also be wrong *)
| I_Branch: forall st cond,
    Branch cond / st i--> st
| I_Indirect_Call: forall st reg,
    Indirect_Call reg / st i-->  st
| I_Direct_Call: forall st,
    Direct_Call / st i-->  st
| I_Ret: forall st,
    Ret / st i-->  st
  where " i '/' st 'i-->' st'" := (instr_class_istep i st st').

Theorem instr_class_istep_deterministic : forall init_st st st' i, 
  i / init_st i--> st ->
  i / init_st i--> st' ->
  st = st'.
Proof.
  intros init_st st st' i H1 H2. inversion H1; inversion H2; subst; 
  try (inversion H8; auto);
  try (inversion H7; auto);
  try (inversion H6; auto);
  try (inversion H5; auto);
  try (inversion H4; auto).
Qed.

Theorem instr_class_always_isteps : forall st i,
  exists st', i / st i--> st'.
Proof.
  intros st i. induction i; eexists.
- apply I_Heap_Read.
- apply I_Heap_Write.
- apply I_Heap_Check.
- apply I_Call_Check.
- apply I_Reg_Move.
- apply I_Reg_Write. 
- apply I_Stack_Expand.
- apply I_Stack_Contract.
- apply I_Stack_Read.
- apply I_Stack_Write.
- apply I_Branch.
- apply I_Indirect_Call.
- apply I_Direct_Call.
- apply I_Ret.
Qed.

Definition run_basic_block (bb : basic_block) (s : state) : state :=
  fold_left (fun s i => run_instr i s) bb s.
