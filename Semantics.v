Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import BinInt.
Require Import VerifiedVerifier.Machine.
Require Import VerifiedVerifier.Bits.
Require Import VerifiedVerifier.Maps.
Require Import VerifiedVerifier.RecordUpdate.

(*TODO: figure out if we need uints vs ints*)
Definition address_ty := nat.
Definition data_ty := nat.

Definition registers_ty := total_map register data_ty.

Definition stack_ty := list data_ty.

Definition heap_ty := total_map address_ty data_ty.

(*Definition flags_ty := total_map flag int1.*)

(*Definition function_table_ty := partial_map address_ty string.*)

Record state := mkState {
  regs : registers_ty;
(*  flags : flags_ty; *)

  stack : stack_ty;
  below_stack_guard_size : nat;
  stack_base : address_ty;
  max_stack_size : nat;
  above_stack_guard_size : nat;
  stack_base_gt_guard : stack_base > below_stack_guard_size;

  heap : heap_ty;
  below_heap_guard_size : nat;
  heap_base : address_ty;
  max_heap_size : nat;
  above_heap_guard_size : nat;
  heap_base_gt_guard : heap_base > below_heap_guard_size;
  heap_size_eq_guard : max_heap_size = above_heap_guard_size; 
(*  function_table : function_table_ty; *)
  error : bool;

  prog : program;
  func : function;
  call_stack : list function;
  (* func_in_prog: In func prog; *)

  stack_size : nat;
  frame_size : nat;
  frames : list nat;
}.

Instance etaState : Settable _ := settable! mkState 
<
  regs;
(*  flags : flags_ty; *)

  stack;
  below_stack_guard_size;
  stack_base;
  max_stack_size;
  above_stack_guard_size;
  stack_base_gt_guard;

  heap;
  below_heap_guard_size;
  heap_base;
  max_heap_size;
  above_heap_guard_size;
  heap_base_gt_guard;
  heap_size_eq_guard;
(*  function_table; *)
  error;

  prog;
  func;
  call_stack;
  (* func_in_prog; *)
  stack_size;
  frame_size;
  frames
>.

Eval compute in (Z.to_nat (-1%Z)).

Definition fourGB : address_ty :=
pow 2 32.

Definition zero : data_ty :=
0.

Program Definition start_state p f : state :=
{|
  regs := t_empty zero;
(*  flags : flags_ty; *)

  stack := nil;
  below_stack_guard_size := fourGB;
  stack_base := 1 + fourGB;
  max_stack_size := fourGB;
  above_stack_guard_size := fourGB;

  heap := t_empty zero;
  below_heap_guard_size := fourGB;
  heap_base := 1 + fourGB;
  max_heap_size := fourGB;
  above_heap_guard_size := fourGB;

(*  function_table := empty; *)
  error := false;

  prog := p;
  func := f;
  (* func_in_prog := f_in_p; *)

  call_stack := nil;
  stack_size := 0;
  frame_size := 0;
  frames := nil;
|}.

Fixpoint value_to_data (s : state) (v :value) : data_ty :=
match v with
| Const c => c
end.

Definition get_register (s : state) (r : register) : data_ty :=
  s.(regs) r.

Definition set_register (s : state) (r : register) (v : data_ty) : state :=
s <| regs := t_update register_eq_dec s.(regs) r v |>.

Definition set_error_state (s : state) : state :=
s <| error := true |>.

Definition expand_stack (s : state) (i : nat) : state :=
  set_register 
(s <| stack ::= app (repeat 0 i) |> <| frame_size ::= add i |> <| stack_size ::= add i |>)
  rsp (i + (get_register s rsp)).

Fixpoint removelast_n {A} (n : nat) (l : list A) : list A :=
match n with
| 0 => l
| S n' => removelast_n n' (removelast l)
end.

Definition contract_stack (s : state) (i : nat) : state :=
set_register
  (s <| stack ::= removelast_n i |> <| frame_size := (frame_size s) - i |> <| stack_size := (stack_size s) - i |>)
  rsp ((get_register s rsp) - i).

(* TODO: we don't actually return 0 for default here, we should
 * signal a trap (and exit?) *)
(* TODO: Make stack indexing 64-bit *)
Definition read_stack (s : state) (i : nat) : data_ty :=
nth_default 0 s.(stack) ((get_register s rsp) - (stack_base s) - (stack_size s) + i).

Definition write_stack (s : state) (i : nat) (val : data_ty) : state :=
s <| stack := Machine.update s.(stack) ((get_register s rsp) - (stack_base s) - (stack_size s) + i) val |>.

Definition cons_stack (s : state) (val : data_ty) : state :=
write_stack (expand_stack s 1) 0 val.

Lemma cons_stack_correct : forall s val, 
  (get_register s rsp) = (stack_base s) + (stack_size s) ->
(stack (cons_stack s val)) = val :: (stack s).
Proof.
  intros. simpl. pose proof stack_base_gt_guard. specialize H0 with s. destruct (stack_base s).
  - inversion H0.
  - rewrite <- plus_n_O. rewrite H. Search (S _ + _). rewrite Nat.add_succ_comm. Search (_ + _ - _).
    rewrite Minus.minus_plus. Search (_ - _). rewrite Nat.sub_diag. reflexivity.
Qed.

Definition push_frame st f : state :=
  st <| frame_size := 0 |> <| frames ::= cons (frame_size st) |> 
    <| func := f |> <| call_stack ::= cons (func st) |>  (*<| func_in_prog := f_in_p |> *).

Program Definition empty_func :=
{| V := nil; E := nil |}.
Next Obligation. inversion H. Qed.

Definition pop_frame st : state :=
  st <| frame_size := hd 0 (frames st) |> <| frames := tl (frames st) |>
    <| func := hd empty_func (call_stack st) |> <| call_stack := tl (call_stack st) |>.

Definition read_heap (s : state) (i : address_ty) : data_ty :=
s.(heap) i.

Definition write_heap (s : state) (i : address_ty) (v : data_ty) : state :=
s <| heap := t_update Nat.eq_dec s.(heap) i v |>.

(*Definition fourGB : int64 := (Word.shl (Word.repr 2) (Word.repr 32)). *)

(*TODO: This doesn't handle signed/unsigned conversions correctly*)
Definition run_conditional (s : state) (c : conditional) : bool :=
  match c with
| Not_Equal r1 r2 => negb (eqb (get_register s r1) (get_register s r2))
| Equal r1 r2 => eqb (get_register s r1) (get_register s r2)
| Greater r1 r2 => ltb (get_register s r2) (get_register s r1)
| Greater_Equal r1 r2 => orb (ltb (get_register s r2) (get_register s r1)) (eqb (get_register s r1) (get_register s r2))
| Above r1 r2 => ltb (get_register s r2) (get_register s r1)
| Above_Equal r1 r2 => orb (ltb (get_register s r2) (get_register s r1)) (eqb (get_register s r1) (get_register s r2))
| Lesser r1 r2 => ltb (get_register s r1) (get_register s r2)
| Lesser_Equal r1 r2 => orb (ltb (get_register s r1) (get_register s r2)) (eqb (get_register s r1) (get_register s r2))
| Below r1 r2 => ltb (get_register s r1) (get_register s r2)
| Below_Equal r1 r2 => orb (ltb (get_register s r1) (get_register s r2)) (eqb (get_register s r1) (get_register s r2))
| Counter_Register_Zero => eqb (get_register s rcx) 0
end.

Definition run_op (s : state) (op : opcode) (rs_dst : list register) (rs_src : list register) : state :=
fold_left (fun s r => set_register s r 0) rs_dst s.

(*
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
| Branch c t_label f_label => s
| Op op rs_dst rs_src => s
| Jmp j_label => s
| Ret => s
end.

Theorem run_instr_deterministic : forall init_st st st' i, 
  run_instr i init_st = st ->
  run_instr i init_st = st' ->
  st = st'.
Proof.
  intros init_st st st' i H1 H2. rewrite <- H1, H2. auto.
Qed.
*)


Definition run_heap_read st r_dst r_offset r_index r_base : state :=
let index := (get_register st r_offset) + (get_register st r_index) + (get_register st r_base) in
let base := heap_base st in 
if orb (andb (leb (base + (max_heap_size st)) index) (ltb index (base + (max_heap_size st) + (above_heap_guard_size st))))
      (andb (ltb index base) (leb (base - (below_heap_guard_size st)) index))
then set_error_state st
else set_register st r_dst (read_heap st index).

Definition run_heap_write st r_offset r_index r_base r_val : state :=
let index := (get_register st r_offset) + (get_register st r_index) + (get_register st r_base) in
let base := heap_base st in 
if orb (andb (leb (base + (max_heap_size st)) index) (ltb index (base + (max_heap_size st) + (above_heap_guard_size st))))
      (andb (ltb index base) (leb (base - (below_heap_guard_size st)) index))
then set_error_state st
else write_heap st index (get_register st r_val).

Definition run_call_check st r_src : state :=
(*match nth_error (program st) (get_register st r_src) with *)
if ltb (get_register st r_src) (List.length (prog st))
then st
else set_error_state st.

Definition run_stack_expand_dynamic st i : state :=
if leb i ((max_stack_size st) - (List.length (stack st)))
then expand_stack st i
else set_error_state st.

Definition run_stack_read st r_dst i : state :=
let base := stack_base st in
if orb (andb (leb (base + (max_stack_size st)) i) (ltb i (base + (max_stack_size st) + (above_stack_guard_size st))))
      (andb (ltb i base) (leb (base - (below_stack_guard_size st)) i))
then set_error_state st
else set_register st r_dst (read_stack st i).

Definition run_stack_write st i r_src : state :=
let base := stack_base st in
if orb (andb (leb (base + (max_stack_size st)) i) (ltb i (base + (max_stack_size st) + (above_stack_guard_size st))))
      (andb (ltb i base) (leb (base - (below_stack_guard_size st)) i))
then set_error_state st
else write_stack st i (get_register st r_src).

Definition get_function st fname : option function :=
nth_error (prog st) fname.

Definition get_first_block f : basic_block :=
match (V f) with
| nil => nil
| h :: t => h
end.

Definition get_basic_block st label : option basic_block := 
nth_error (V (func st)) label.

Reserved Notation " i '/' st 'i-->' i' '/' st' "
                  (at level 39, st at level 38, i' at level 38).
Inductive istep : (list instr_class * state) -> (list instr_class * state) -> Prop :=
| I_Heap_Read: forall st is pp r_base r_index r_offset r_dst index, 
  r_dst <> rsp ->
  index = (get_register st r_base) + (get_register st r_index) + (get_register st r_offset) ->
  (heap_base st) <= index ->
  index < (heap_base st) + (max_heap_size st) ->
  ((Heap_Read pp r_dst r_offset r_index r_base) :: is) / st i--> is / set_register st r_dst (read_heap st index)
| I_Heap_Read_Guard: forall st is pp r_base r_index r_offset r_dst index,
  r_dst <> rsp ->
  index = (get_register st r_base) + (get_register st r_index) + (get_register st r_offset) ->
  (heap_base st) + (max_heap_size st) <= index ->
  index < (heap_base st) + (max_heap_size st) + (above_heap_guard_size st) ->
  ((Heap_Read pp r_dst r_offset r_index r_base) :: is) / st i--> nil / set_error_state st
| I_Heap_Write: forall st is pp r_base r_index r_offset r_val index,
  index = (get_register st r_base) + (get_register st r_index) + (get_register st r_offset) ->
  (heap_base st) <= index ->
  index < (heap_base st) + (max_heap_size st) ->
  ((Heap_Write pp r_offset r_index r_base r_val) :: is) / st i--> is / write_heap st index (get_register st r_val)
| I_Heap_Write_Guard: forall st is pp r_base r_index r_offset r_val index,
  index = (get_register st r_base) + (get_register st r_index) + (get_register st r_offset) ->
  (heap_base st) + (max_heap_size st) <= index ->
  index < (heap_base st) + (max_heap_size st) + (above_heap_guard_size st) ->
  ((Heap_Write pp r_offset r_index r_base r_val) :: is) / st i--> nil / set_error_state st
| I_Heap_Check: forall st is pp r_src,
  r_src <> rsp ->
  ((Heap_Check pp r_src) :: is) / st i--> is / set_register st r_src ((get_register st r_src) mod (above_heap_guard_size st))
| I_Call_Check: forall st is pp r_src,
  get_register st r_src < List.length (prog st) ->
  ((Call_Check pp r_src) :: is) / st i--> is / st
| I_Call_Check_Bad: forall st is pp r_src,
  get_register st r_src >= List.length (prog st) ->
  ((Call_Check pp r_src) :: is) / st i--> nil / set_error_state st
| I_Reg_Move: forall st is pp r_src r_dst,
  r_dst <> rsp ->
  ((Reg_Move pp r_dst r_src) :: is) / st i--> is / set_register st r_dst (get_register st r_src)
| I_Reg_Write: forall st is pp r_dst val,
  r_dst <> rsp ->
  ((Reg_Write pp r_dst val) :: is) / st i--> is / set_register st r_dst (value_to_data st val)
| I_Stack_Expand_Static: forall st is pp i,
  ((Stack_Expand_Static pp i) :: is) / st i--> is / expand_stack st i
| I_Stack_Expand_Dynamic: forall st is pp i,
  i + (stack_size st) <= (max_stack_size st) ->
  ((Stack_Expand_Dynamic pp i) :: is) / st i--> is / expand_stack st i
| I_Stack_Expand_Dynamic_Guard: forall st is pp i,
  i + (stack_size st) > (max_stack_size st) ->
  ((Stack_Expand_Dynamic pp i) :: is) / st i--> nil / set_error_state st
| I_Stack_Contract: forall st is pp i,
  ((Stack_Contract pp i) :: is) / st i--> is / contract_stack st i
| I_Stack_Read: forall st is pp i r_dst,
  r_dst <> rsp ->
  (stack_base st) < (get_register st rsp) - i ->
  (get_register st rsp) - i < (stack_base st) + (stack_size st) ->
  ((Stack_Read pp r_dst i) :: is) / st i--> is / set_register st r_dst (read_stack st i)
| I_Stack_Read_Below_Guard: forall st is pp i r_dst,
  r_dst <> rsp ->
  (stack_base st) - (below_stack_guard_size st) < (get_register st rsp) - i ->
  (get_register st rsp) - i < (stack_base st) ->
  ((Stack_Read pp r_dst i) :: is) / st i--> is / set_error_state st
| I_Stack_Read_Above_Guard: forall st is pp i r_dst,
  r_dst <> rsp ->
  (stack_base st) + (max_stack_size st) < (get_register st rsp) - i ->
  (get_register st rsp) - i < (stack_base st) + (max_stack_size st) + (above_stack_guard_size st) ->
  ((Stack_Read pp r_dst i) :: is) / st i--> is / set_error_state st
| I_Stack_Write: forall st is pp i r_src,
  (stack_base st) < (get_register st rsp) - i ->
  (get_register st rsp) - i < (stack_base st) + (max_stack_size st) ->
  ((Stack_Write pp i r_src) :: is) / st i--> is / write_stack st i (get_register st r_src)
| I_Stack_Write_Below_Guard: forall st is pp i r_src,
  (stack_base st) - (below_stack_guard_size st) < (get_register st rsp) - i ->
  (get_register st rsp) - i < (stack_base st) ->
  ((Stack_Write pp i r_src) :: is) / st i--> is / set_error_state st
| I_Stack_Write_Above_Guard: forall st is pp i r_src,
  (stack_base st) + (max_stack_size st) < (get_register st rsp) - i ->
  (get_register st rsp) - i < (stack_base st) + (max_stack_size st) + (above_stack_guard_size st) ->
  ((Stack_Write pp i r_src) :: is) / st i--> is / set_error_state st
| I_Op: forall st is pp op rs_dst rs_src,
  ~ In rsp rs_dst ->
  ((Op pp op rs_dst rs_src) :: is) / st i--> is / run_op st op rs_dst rs_src
| I_Branch_True: forall st is pp c t_label f_label t_bb f_bb,
  get_basic_block st t_label = Some t_bb ->
  get_basic_block st f_label = Some f_bb ->
  run_conditional st c = true ->
  ((Branch pp c t_label f_label) :: is) / st i--> (t_bb ++ is) / st
| I_Branch_False: forall st is pp c t_label f_label t_bb f_bb,
  get_basic_block st t_label = Some t_bb ->
  get_basic_block st f_label = Some f_bb ->
  run_conditional st c = false ->
  ((Branch pp c t_label f_label) :: is) / st i--> (f_bb ++ is) / st
| I_Jmp: forall st is pp j_label j_bb,
  get_basic_block st j_label = Some j_bb ->
  ((Jmp pp j_label) :: is) / st i--> (j_bb ++ is) / st
| I_Indirect_Call: forall st is pp reg f,
  get_function st (get_register st reg) = Some f ->
  ((Indirect_Call pp reg) :: is) / st i--> ((get_first_block f) ++ is) / push_frame (cons_stack st 1) f
| I_Direct_Call: forall st is pp fname f,
  get_function st fname = Some f ->
  ((Direct_Call pp fname) :: is) / st i--> ((get_first_block f) ++ is) / push_frame (cons_stack st 1) f
| I_Ret: forall st is pp,
  (read_stack st 0) = 1 ->
  ((Ret pp) :: is) / st i--> is / pop_frame st

(*| I_Indirect_Call_Good: forall st is reg fname f,
    (get_register st reg) = fname ->
    get_function st fname = Some f ->
    ((Indirect_Call reg) :: is) / st i--> ((get_first_block f) ++ is) / st'
| I_Indirect_Call_Bad: forall st st' reg fname i,
    (get_register st reg) = fname ->
    get_function st fname = None ->
    i / st i--> st' ->
    Indirect_Call reg / st i-->  st'
| I_Direct_Call_Good: forall st st' fname f,
    get_function st fname = Some f ->
    function_istep f (cons_stack st fname) st' ->
    Direct_Call fname / st i-->  st'
| I_Direct_Call_Bad : forall st st' fname i,
    get_function st fname = None ->
    i / st i--> st' ->
    Direct_Call fname / st i-->  st'
| I_Branch_True_Good: forall st t_st f_st c t_label f_label t_bb f_bb,
    get_basic_block st t_label = Some t_bb ->
    get_basic_block st f_label = Some f_bb ->
    basic_block_istep t_bb st t_st ->
    basic_block_istep f_bb st f_st ->
    run_conditional st c = true ->
    (Branch c t_label f_label) / st i--> t_st
| I_Branch_False_Good: forall st t_st f_st c t_label f_label t_bb f_bb,
    get_basic_block st t_label = Some t_bb ->
    get_basic_block st f_label = Some f_bb ->
    basic_block_istep t_bb st t_st ->
    basic_block_istep f_bb st f_st ->
    run_conditional st c = false ->
    (Branch c t_label f_label) / st i--> f_st
| I_Branch_True_Bad: forall st st' c t_label f_label i,
    get_basic_block st t_label = None ->
    i / st i--> st' ->
    (Branch c t_label f_label) / st i--> st'
| I_Branch_False_Bad: forall st st' c t_label f_label i,
    get_basic_block st f_label = None ->
    i / st i--> st' ->
    (Branch c t_label f_label) / st i--> st'
| I_Jmp_Good: forall st st' j_label bb,
    get_basic_block st j_label = Some bb ->
    basic_block_istep bb st st' ->
    (Jmp j_label) / st i--> st'
| I_Jmp_Bad: forall st st' j_label,
    get_basic_block st j_label = None ->
    (Jmp j_label) / st i--> st'
| I_Ret_Good: forall st st' fname stack',
    st' = st <| stack := stack' |> ->
    (stack st) = fname :: stack' ->
    fname < List.length (stack st) ->
    Ret / st i--> st'
| I_Ret_Bad_Function: forall st st' fname stack' i,
    (stack st) = fname :: stack' ->
    fname >= List.length (stack st) ->
    i / st i--> st' ->
    Ret / st i--> st'
| I_Ret_Bad_Stack: forall st st' i,
    (stack st) = nil ->
    i / st i--> st' ->
    Ret / st i--> st'
*)
  where " i '/' st 'i-->' i' '/' st' " := (istep (i,st) (i',st')).

Lemma get_set_reg : forall st r1 r2 v,
  r1 <> r2 ->
  get_register (set_register st r2 v) r1 = get_register st r1.
Proof.
  intros. simpl. apply register_get_after_set_neq. auto.
Qed.

Lemma istep_preserves_stack_eq_invariant : forall i is is' st st',
  (i :: is) / st i--> is' / st' ->
  (get_register st rsp) = (stack_size st) ->
  (get_register st' rsp) = (stack_size st').
Proof.
  intros. inversion H; 
  try (subst);
  try (rewrite get_set_reg);
  try (simpl; rewrite register_get_after_set_eq); eauto.
  admit.
Admitted.

Inductive istep_fuel : ((list instr_class * state) * nat) -> ((list instr_class * state) * nat) -> Prop :=
| IFuel_Base : forall i s,
    istep_fuel ((i, s), 0) ((i, s), 0)
| IFuel_Step : forall i s i' s' fuel fuel',
    istep (i, s) (i', s') ->
    fuel = S fuel' ->
    istep_fuel ((i, s), fuel) ((i', s'), fuel').

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Definition imultistep := multi istep.

Notation " i '/' st '-->*' i' '/' st' " :=
   (multi istep  (i,st) (i',st'))
   (at level 39, st at level 38, i' at level 38).

Inductive imultistep_fuel : ((list instr_class * state) * nat) -> ((list instr_class * state) * nat) -> Prop :=
| multi_base : forall i s i' s' fuel fuel',
    istep_fuel (i, s, fuel) (i', s', fuel') ->
    imultistep_fuel (i, s, fuel) (i', s', fuel')
| multi_transitive : forall i1 s1 fuel1 i2 s2 fuel2 i3 s3 fuel3,
    istep_fuel (i1, s1, fuel1) (i2, s2, fuel2) ->
    imultistep_fuel (i2, s2, fuel2) (i3, s3, fuel3) ->
    imultistep_fuel (i1, s1, fuel1) (i3, s3, fuel3).

(*
Reserved Notation " i '/' st 'i-->' st' "
                  (at level 40, st' at level 39).
Inductive instr_class_istep : instr_class -> state -> state -> Prop := 
| I_Heap_Read: forall st r_base r_index r_offset r_dst,
    Heap_Read r_dst r_offset r_index r_base / st i--> run_heap_read st r_dst r_offset r_index r_base
| I_Heap_Write: forall st r_base r_val r_index r_offset,
    Heap_Write r_offset r_index r_base r_val / st i--> run_heap_write st r_offset r_index r_base r_val
| I_Heap_Check: forall st r_src,
    Heap_Check r_src / st i--> set_register st r_src ((get_register st r_src) mod fourGB)
| I_Call_Check: forall st r_src,
    Call_Check r_src / st i--> run_call_check st r_src
| I_Reg_Move: forall st r_src r_dst,
    Reg_Move r_dst r_src / st i--> set_register st r_dst (get_register st r_src)
| I_Reg_Write: forall st r_dst val,
    Reg_Write r_dst val / st i--> set_register st r_dst (value_to_data st val)
| I_Stack_Expand_Static: forall st i,
    Stack_Expand_Static i / st i--> expand_stack st i
| I_Stack_Expand_Dynamic: forall st i,
    Stack_Expand_Dynamic i / st i--> run_stack_expand_dynamic st i

(* i forgot how this case should be handled *)
| I_Stack_Contract_Good: forall st i,
    i <= List.length (stack st) ->
    Stack_Contract i / st i--> contract_stack st i
| I_Stack_Contract_Bad: forall st i,
    i > List.length (stack st) ->
    Stack_Contract i / st i--> set_error_state st

| I_Stack_Read: forall st i r_dst,
    Stack_Read r_dst i / st i--> run_stack_read st r_dst i
| I_Stack_Write: forall st i r_src,
    Stack_Write i r_src / st i--> run_stack_write st i r_src
| I_Op: forall st op rs_dst rs_src,
    (Op op rs_dst rs_src) / st i--> run_op st op rs_dst rs_src

(* those calls might also be wrong *)
| I_Indirect_Call_Good: forall st st' reg fname f,
    (get_register st reg) = fname ->
    get_function st fname = Some f ->
    function_istep f (cons_stack st fname) st' ->
    Indirect_Call reg / st i-->  st'
| I_Indirect_Call_Bad: forall st st' reg fname i,
    (get_register st reg) = fname ->
    get_function st fname = None ->
    i / st i--> st' ->
    Indirect_Call reg / st i-->  st'
| I_Direct_Call_Good: forall st st' fname f,
    get_function st fname = Some f ->
    function_istep f (cons_stack st fname) st' ->
    Direct_Call fname / st i-->  st'
| I_Direct_Call_Bad : forall st st' fname i,
    get_function st fname = None ->
    i / st i--> st' ->
    Direct_Call fname / st i-->  st'
| I_Branch_True_Good: forall st t_st f_st c t_label f_label t_bb f_bb,
    get_basic_block st t_label = Some t_bb ->
    get_basic_block st f_label = Some f_bb ->
    basic_block_istep t_bb st t_st ->
    basic_block_istep f_bb st f_st ->
    run_conditional st c = true ->
    (Branch c t_label f_label) / st i--> t_st
| I_Branch_False_Good: forall st t_st f_st c t_label f_label t_bb f_bb,
    get_basic_block st t_label = Some t_bb ->
    get_basic_block st f_label = Some f_bb ->
    basic_block_istep t_bb st t_st ->
    basic_block_istep f_bb st f_st ->
    run_conditional st c = false ->
    (Branch c t_label f_label) / st i--> f_st
| I_Branch_True_Bad: forall st st' c t_label f_label i,
    get_basic_block st t_label = None ->
    i / st i--> st' ->
    (Branch c t_label f_label) / st i--> st'
| I_Branch_False_Bad: forall st st' c t_label f_label i,
    get_basic_block st f_label = None ->
    i / st i--> st' ->
    (Branch c t_label f_label) / st i--> st'
| I_Jmp_Good: forall st st' j_label bb,
    get_basic_block st j_label = Some bb ->
    basic_block_istep bb st st' ->
    (Jmp j_label) / st i--> st'
| I_Jmp_Bad: forall st st' j_label,
    get_basic_block st j_label = None ->
    (Jmp j_label) / st i--> st'
| I_Ret_Good: forall st st' fname stack',
    st' = st <| stack := stack' |> ->
    (stack st) = fname :: stack' ->
    fname < List.length (stack st) ->
    Ret / st i--> st'
| I_Ret_Bad_Function: forall st st' fname stack' i,
    (stack st) = fname :: stack' ->
    fname >= List.length (stack st) ->
    i / st i--> st' ->
    Ret / st i--> st'
| I_Ret_Bad_Stack: forall st st' i,
    (stack st) = nil ->
    i / st i--> st' ->
    Ret / st i--> st'
  where " i '/' st 'i-->' st'" := (instr_class_istep i st st')

with basic_block_istep : basic_block -> state -> state -> Prop :=
| I_Basic_Block_Nil: forall st,
  basic_block_istep nil st st
| I_Basic_Block_Trap: forall bb st,
  error st = true ->
  basic_block_istep bb st st
| I_Basic_Block_Cons: forall i is st st' st'',
  i / st i--> st' ->
  basic_block_istep is st' st'' ->
  basic_block_istep (i :: is) st st'

with function_istep : function -> state -> state -> Prop :=
| I_Function_Some: forall f bb st st',
  head (V f) = Some bb ->
  basic_block_istep bb st st' ->
  function_istep f st st'
| I_Function_None: forall f st,
  head (V f) = None ->
  function_istep f st st
.
*)
(*
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
  find (fun x => eqb (snd x) name) p.(funs).

Definition function_lookup (p : program_ty) (s : state) (i : int64) : option function_ty :=
match (s.(function_table) i) with
| Some name => get_function_from_name p name
| None => get_function_from_name p "trap"
end.

(* TODO: Make sure we are handling errors correctly *)
(* TODO: Allow read-only access to earlier stack values up to some constant *)
Fixpoint run_program (p : program_ty) (cfg : cfg_ty) (n : node_ty) (s : state) (fuel : nat) : state :=
  match fuel with
  | 0 => set_error_state s
  | S fuel' =>
    let bb := fst n in
    let s' := run_basic_block bb s in
    let s'' := match last bb Ret with
               | Direct_Call name =>
                   match get_function_from_name p name with
                   | Some f => run_program p (fst f) (fst f).(start_node) s' fuel'
                   | None => set_error_state s'
                   end
               | Indirect_Call r =>
                   match function_lookup p s' (get_register s r) with
                   | Some f => run_program p (fst f) (fst f).(start_node) s' fuel'
                   | None => set_error_state s'
                   end
               | _ => s'
               end in
    match next_node cfg s n with
    | Some n' => run_program p cfg n' s'' fuel'
    | None => s''
    end
  end.
*)
