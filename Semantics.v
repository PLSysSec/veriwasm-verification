Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Strings.String.
Require Import BinInt.
Require Import VerifiedVerifier.Machine.
Require Import VerifiedVerifier.Bits.
Require Import VerifiedVerifier.Maps.

Type map.
(*TODO: figure out if we need uints vs ints*)
Definition registers_ty := total_map register int64.

Definition stack_ty := list int64.

Definition heap_ty := total_map int64 int64.

Definition flags_ty := total_map flag int1.

Definition function_table_ty := partial_map int64 string.

(* TODO: We make an exit flag so we can keep track of error exits
   (through sfi-violating properties) vs safe exits (like traps or
   running out of fuel because of non-termination) *)
Record state := {
  regs : registers_ty;
  flags : flags_ty;
  stack : stack_ty;
  heap : heap_ty;
  heap_base : int64;
  function_table : function_table_ty;
  error : bool;
  exit : bool;
}.

Fixpoint value_to_int64 (s : state) (v :value) : int64 :=
match v with
| Const c => c
end.

Definition get_register (s : state) (r : register) : int64 :=
  s.(regs) r.

Definition set_register (s : state) (r : register) (v : int64) : state :=
{| regs := t_update register_eq_dec s.(regs) r v;
   flags := s.(flags);
   stack := s.(stack);
   heap := s.(heap);
   heap_base := s.(heap_base);
   function_table := s.(function_table);
   error := s.(error);
   exit := s.(exit); |}.

Definition set_flags (s : state) (f : flags_ty) : state :=
{| regs := s.(regs);
   flags := f;
   stack := s.(stack);
   heap := s.(heap);
   heap_base := s.(heap_base) ;
   function_table := s.(function_table);
   error := s.(error);
   exit := s.(exit); |}.

Definition expand_stack (s : state) (i : nat) : state :=
{| regs := s.(regs);
   flags := s.(flags);
   stack := s.(stack) ++ (repeat Word.zero i);
   heap := s.(heap);
   heap_base := s.(heap_base);
   function_table := s.(function_table);
   error := s.(error);
   exit := s.(exit); |}.

Fixpoint contract_stack (s : state) (i : nat) : state :=
match i with
| 0 => s
| S n =>
contract_stack {| regs := s.(regs);
   flags := s.(flags);
   stack := removelast s.(stack);
   heap := s.(heap);
   heap_base := s.(heap_base) ;
   function_table := s.(function_table);
   error := s.(error);
   exit := s.(exit); |}
 n
end.

(* TODO: we don't actually return 0 for default here, we should
 * signal a trap (and exit?) *)
(* TODO: Make stack indexing 64-bit *)
Definition read_stack (s : state) (i : nat) : int64 :=
nth_default Word.zero s.(stack) i.

Definition write_stack (s : state) (i : nat) (val : int64) : state :=
{| regs := s.(regs);
   flags := s.(flags);
   stack := Machine.update s.(stack) i val;
   heap := s.(heap);
   heap_base := s.(heap_base) ;
   function_table := s.(function_table);
   error := s.(error);
   exit := s.(exit); |}.

Definition read_heap (s : state) (i : int64) : int64 :=
s.(heap) i.

Definition write_heap (s : state) (i : int64) (v : int64) : state :=
{| regs := s.(regs);
	 flags := s.(flags);
	 stack := s.(stack);
	 heap := t_update int64_eq_dec s.(heap) i v;
   heap_base := s.(heap_base);
   function_table := s.(function_table);
   error := s.(error);
   exit := s.(exit); |}.

Definition set_error_state (s : state) : state :=
{| regs := s.(regs);
	 flags := s.(flags);
	 stack := s.(stack);
	 heap := s.(heap);
   heap_base := s.(heap_base);
   function_table := s.(function_table);
   error := true;
   exit := s.(exit); |}.

Definition set_exit_state (s : state) : state :=
{| regs := s.(regs);
	 flags := s.(flags);
	 stack := s.(stack);
	 heap := s.(heap);
   heap_base := s.(heap_base);
   function_table := s.(function_table);
   error := s.(error);
   exit := true; |}.

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

(* TODO: Implement Op *)
(* TODO: Can we index the stack from registers (probably), or only constants *)
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
(*TODO: Make sure calls are right*)
| Indirect_Call r => s
| Direct_Call name => s
| Branch c => s
| Op op rs_dst rs_src => s
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
| I_Indirect_Call: forall st reg,
    Indirect_Call reg / st i-->  st
| I_Direct_Call: forall st name,
    Direct_Call name / st i-->  st
| I_Branch: forall st c,
    (Branch c) / st i--> st
| I_Op: forall st op rs_dst rs_src,
    (Op op rs_dst rs_src) / st i--> st
| I_Ret: forall st,
    Ret / st i-->  st
  where " i '/' st 'i-->' st'" := (instr_class_istep i st st').
Hint Constructors instr_class_istep.

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
  intros st i. induction i; eexists; auto.
Qed.

Definition run_basic_block (bb : basic_block) (s : state) : state :=
  fold_left (fun s i => run_instr i s) bb s.

(* TODO: Not sure why this is necessary, but it won't go through
 * if I try to inline node_ty_eqb_dec *)
Definition node_ty_eqb (a : node_ty) (b : node_ty) : bool :=
  if node_ty_eq_dec a b
  then true
  else false.

(* TODO: Not sure why this is necessary, but it won't go through
 * if I try to inline edge_class_eqb_dec *)
Definition edge_class_eqb (a : edge_class) (b : edge_class) : bool :=
  if edge_class_eq_dec a b
  then true
  else false.

Definition find_edge (cfg : cfg_ty) (n : node_ty) (e : edge_class) : option node_ty :=
  match find (fun x => andb (node_ty_eqb (fst (fst x)) n)
                            (edge_class_eqb (snd x) e))
             cfg.(edges) with
  | Some edge => Some (snd (fst edge))
  | None => None
  end.

Definition next_node (cfg : cfg_ty) (s : state) (n : node_ty) : option node_ty :=
  match last (fst n) Ret with
  | Branch c => if run_conditional c s
                then find_edge cfg n True_Branch
                else find_edge cfg n False_Branch
  | Ret => None
  | _ => find_edge cfg n Non_Branch
  end.

Definition get_function_from_name (p : program_ty) (name : string) : option function_ty :=
  find (fun x => eqb (snd x) name) p.(fun_list).

(* TODO: Might return "trap" function name instead of None *)
Definition function_lookup (p : program_ty) (i : int64) : option function_ty :=
  p.(fun_table) i.

Fixpoint run_function' (p : program_ty) (f : function_ty) (n : node_ty) (s : state) (fuel : nat) :
                       (state * option function_ty) :=
  match fuel with
  | 0 => (set_exit_state s, None)
  | S fuel' =>
    let bb := fst n in
    let s' := run_basic_block bb s in
    let (s'', f') :=
      match last bb Ret with
      | Direct_Call name =>
          match get_function_from_name p name with
          | Some next_f => (s, Some f)
          | None => (set_error_state s', None)
          end
      | Indirect_Call r =>
          match function_lookup p (get_register s r) with
          | Some next_f => (s, Some f)
          | None => (set_error_state s', None)
          end
      | _ => (s', f)
      end in
    match next_node (fst f) s n with
    | Some n' => run_function' f n' s'' fuel'
    | None => (s'', None)
    end
  end.

(* NOTE: Thsi is just an arbitrary number; it shouldn't really matter *)
Definition function_fuel := 100000.

Fixpoint run_function (p : program_ty) (f : function_ty) (s : state) : (state * option function_ty) :=
  run_function' p f f.(start_node) s function_fuel.

(* NOTE: This should be equivalent to run_program' *)
Fixpoint run_program_function' (p : program_ty) (f : function_ty) (s : state) (fuel : nat) : state :=
  let (s', f_opt) := run_function' p f s in
  match f_opt with
  | Some f' => run_program_function' p f' s'
  | None => s'
  end.

(* TODO: Make sure we are handling errors correctly *)
(* TODO: Allow read-only access to earlier stack values up to some constant *)
(* TODO: Trapping is going to be really weird here *)
(* NOTE: Our method of returning an error state for every unsafe operation is equivalent
   to a dynamic check at every memory operation *)
Fixpoint run_program' (p : program_ty) (cfg : cfg_ty) (n : node_ty) (s : state) (fuel : nat) : state :=
  match fuel with
  | 0 => set_exit_state s
  | S fuel' =>
    let bb := fst n in
    let s' := run_basic_block bb s in
    let s'' := match last bb Ret with
               | Direct_Call name =>
                   match get_function_from_name p name with
                   | Some f => run_program' p (fst f) (fst f).(start_node) s' fuel'
                   | None => set_error_state s'
                   end
               | Indirect_Call r =>
                   match function_lookup p (get_register s r) with
                   | Some f => run_program' p (fst f) (fst f).(start_node) s' fuel'
                   | None => set_error_state s'
                   end
               | _ => s'
               end in
    match next_node cfg s n with
    | Some n' => run_program' p cfg n' s'' fuel'
    | None => s''
    end
  end.

(* TODO: Some of these are configurable (e.g. heap_base) *)
(* TODO: Make sure these initial values are correct *)
(* TODO: Prove that this correctly sets up the function table *)
Definition start_state (p : program_ty) : state :=
  let heap_base_val := Word.repr 4096 in
  {| regs := fun r => if register_eq_dec r rdi
                        then heap_base_val
                        else Word.repr 0;
    flags := fun f => Word.repr 0;
    stack := nil;
    heap := fun a => Word.repr 0;
    heap_base := heap_base_val;
    function_table := fun a => match p.(fun_table) a with
                               | Some f => Some (snd f)
                               | None => None
                               end;
    error := false;
    exit := false; |}.

Definition run_program (p : program_ty) (fuel : nat) : state :=
  let main := fst p.(main) in
  run_program' p main main.(start_node) (start_state p) fuel.

Definition run_program_function (p : program_ty) (fuel : nat) : state :=
  let main := fst p.(main) in
  run_program_function' p main (start_state p) fuel.
