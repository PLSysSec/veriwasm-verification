Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import BinInt.
Require Import VerifiedVerifier.Machine.
Require Import VerifiedVerifier.Maps.
Require Import VerifiedVerifier.RecordUpdate.

Definition address_ty := nat.
Definition data_ty := nat.

Definition registers_ty := total_map register data_ty.

Definition stack_ty := list data_ty.

Definition heap_ty := total_map address_ty data_ty.

Definition globals_ty := list data_ty.

Record state := mkState {
  regs : registers_ty;

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
  error : bool;

  globals : globals_ty;
  globals_size : nat;
  globals_base : address_ty;

  program : program;
  call_stack : list nat;
  stack_size : nat;
  frame_size : nat;
  frames : list nat;
}.

Instance etaState : Settable _ := settable! mkState 
<
  regs;

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
  error;

  globals;
  globals_size;
  globals_base;

  program;
  call_stack;
  stack_size;
  frame_size;
  frames
>.

Eval compute in (Z.to_nat (-1%Z)).

Definition fourGB : address_ty :=
pow 2 32.

Definition fourKB : address_ty :=
pow 2 12.

Definition zero : data_ty :=
0.

Program Definition start_state p : state :=
{|
  regs := t_empty zero;

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

  error := false;

  globals := seq 0 4096;
  globals_size := fourKB;
  globals_base := zero;

  program := p;
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
  (s <| stack ::= removelast_n i |> <| frame_size ::= sub i |> <| stack_size ::= sub i |>)
  rsp (get_register s rsp).

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
  - rewrite <- plus_n_O. rewrite H. rewrite Nat.add_succ_comm.
    rewrite Minus.minus_plus. rewrite Nat.sub_diag. reflexivity.
Qed.

Definition push_call st fname : state :=
  st <| call_stack ::= cons fname |>.

Definition pop_call st : state :=
  st <| call_stack := tl (call_stack st) |>.

Definition push_frame st : state :=
  st <| frame_size := 0 |> <| frames ::= cons (frame_size st) |>.

Definition pop_frame st : state :=
  st <| frame_size := hd 0 (frames st) |> <| frames := tl (frames st) |>.

Definition read_heap (s : state) (i : address_ty) : data_ty :=
s.(heap) i.

Definition write_heap (s : state) (i : address_ty) (v : data_ty) : state :=
s <| heap := t_update Nat.eq_dec s.(heap) i v |>.

Definition set_error_state (s : state) : state :=
s <| error := true |>.

Definition read_globals (s : state) (i : nat) : data_ty :=
  nth_default 0 s.(globals) i.

Definition write_globals (s : state) (i : nat) (val : data_ty) : state :=
  s <| globals := Machine.update s.(globals) i val |>.

(*NOTE: This doesn't handle signed/unsigned conversions correctly*)
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
if ltb (get_register st r_src) (List.length (program st).(Funs))
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

Definition run_globals_read st r_dst i : state :=
  let max_size := globals_size st in
  if leb max_size i
  then set_error_state st
  else set_register st r_dst (read_globals st i).

Definition run_globals_write st i r_src : state :=
  let max_size := globals_size st in
  if leb max_size i
  then set_error_state st
  else write_globals st i (get_register st r_src).

Definition get_function st fname : option function :=
nth_error (program st).(Funs) fname.

Definition get_first_block f : basic_block :=
match (V f) with
| nil => nil
| h :: t => h
end.

Definition get_basic_block st label : option basic_block :=
match (call_stack st) with
| nil => None
| fname :: _ =>
  match (get_function st fname) with
  | None => None
  | Some f => nth_error (V f) label
  end
end.

Reserved Notation " i '/' st 'i-->' i' '/' st' "
                  (at level 39, st at level 38, i' at level 38).
Inductive istep : (list instr_ty * state) -> (list instr_ty * state) -> Prop :=
| I_Heap_Read: forall st is r_base r_index r_offset r_dst index n,
  index = (get_register st r_base) + (get_register st r_index) + (get_register st r_offset) ->
  (heap_base st) <= index ->
  index < (heap_base st) + (max_heap_size st) ->
  ({| instr := (Heap_Read r_dst r_offset r_index r_base);
      addr := n |}
     :: is) / st i--> is / set_register st r_dst (read_heap st index)
| I_Heap_Read_Guard: forall st is r_base r_index r_offset r_dst index n,
  index = (get_register st r_base) + (get_register st r_index) + (get_register st r_offset) ->
  (heap_base st) + (max_heap_size st) <= index ->
  index < (heap_base st) + (max_heap_size st) + (above_heap_guard_size st) ->
  ({| instr := (Heap_Read r_dst r_offset r_index r_base);
      addr := n |}
     :: is) / st i--> nil / set_error_state st
| I_Heap_Write: forall st is r_base r_index r_offset r_val index n,
  index = (get_register st r_base) + (get_register st r_index) + (get_register st r_offset) ->
  (heap_base st) <= index ->
  index < (heap_base st) + (max_heap_size st) ->
  ({| instr := (Heap_Write r_offset r_index r_base r_val);
      addr := n |}
     :: is) / st i--> is / write_heap st index (get_register st r_val)
| I_Heap_Write_Guard: forall st is r_base r_index r_offset r_val index n,
  index = (get_register st r_base) + (get_register st r_index) + (get_register st r_offset) ->
  (heap_base st) + (max_heap_size st) <= index ->
  index < (heap_base st) + (max_heap_size st) + (above_heap_guard_size st) ->
  ({| instr := (Heap_Write r_offset r_index r_base r_val);
      addr := n |}
     :: is) / st i--> nil / set_error_state st
| I_Heap_Check: forall st is r_src n,
    ({| instr := (Heap_Check r_src);
        addr := n|}
       :: is) / st i--> is / set_register st r_src ((get_register st r_src) mod (above_heap_guard_size st))
| I_Call_Check: forall st is r_src n,
  get_register st r_src < List.length (program st).(Funs) ->
  ({| instr := (Call_Check r_src);
      addr := n |}:: is) / st i--> is / st
| I_Call_Check_Bad: forall st is r_src n,
  get_register st r_src >= List.length (program st).(Funs) ->
  ({| instr := (Call_Check r_src);
      addr := n |}
     :: is) / st i--> nil / set_error_state st
| I_Reg_Move: forall st is r_src r_dst n,
    ({|instr := (Reg_Move r_dst r_src);
       addr := n |}
       :: is) / st i--> is / set_register st r_dst (get_register st r_src)
| I_Reg_Write: forall st is r_dst val n,
    ({| instr := (Reg_Write r_dst val);
        addr := n |}
       :: is) / st i--> is / set_register st r_dst (value_to_data st val)
| I_Stack_Expand_Static: forall st is i n,
    ({| instr := (Stack_Expand_Static i);
        addr := n |}
       :: is) / st i--> is / expand_stack st i
| I_Stack_Expand_Dynamic: forall st is i n,
  i + (stack_size st) <= (max_stack_size st) ->
  ({| instr := (Stack_Expand_Dynamic i);
      addr := n |}
     :: is) / st i--> is / expand_stack st i
| I_Stack_Expand_Dynamic_Guard: forall st is i n,
  i + (stack_size st) > (max_stack_size st) ->
  ({| instr := (Stack_Expand_Dynamic i);
      addr := n |}
     :: is) / st i--> nil / set_error_state st
| I_Stack_Contract: forall st is i n,
    ({| instr := (Stack_Contract i);
        addr := n |}
       :: is) / st i--> is / contract_stack st i
| I_Stack_Read: forall st is i r_dst n,
  (stack_base st) < (get_register st rsp) - i ->
  (get_register st rsp) - i < (stack_base st) + (stack_size st) ->
  ({| instr := (Stack_Read r_dst i);
      addr := n |}
     :: is) / st i--> is / set_register st r_dst (read_stack st i)
| I_Stack_Read_Below_Guard: forall st is i r_dst n,
  (stack_base st) - (below_stack_guard_size st) < (get_register st rsp) - i ->
  (get_register st rsp) - i < (stack_base st) ->
  ({| instr := (Stack_Read r_dst i);
      addr := n |}
     :: is) / st i--> is / set_error_state st
| I_Stack_Read_Above_Guard: forall st is i r_dst n,
  (stack_base st) + (max_stack_size st) < (get_register st rsp) - i ->
  (get_register st rsp) - i < (stack_base st) + (max_stack_size st) + (above_stack_guard_size st) ->
  ({| instr := (Stack_Read r_dst i);
      addr := n |}
     :: is) / st i--> is / set_error_state st
| I_Stack_Write: forall st is i r_dst n,
  (stack_base st) < (get_register st rsp) - i ->
  (get_register st rsp) - i < (stack_base st) + (max_stack_size st) ->
  ({| instr := (Stack_Write i r_dst);
      addr := n |}
     :: is) / st i--> is / set_register st r_dst (read_stack st i)
| I_Stack_Write_Below_Guard: forall st is i r_dst n,
  (stack_base st) - (below_stack_guard_size st) < (get_register st rsp) - i ->
  (get_register st rsp) - i < (stack_base st) ->
  ({| instr := (Stack_Write i r_dst);
      addr := n |}
     :: is) / st i--> is / set_error_state st
| I_Stack_Write_Above_Guard: forall st is i r_dst n,
  (stack_base st) + (max_stack_size st) < (get_register st rsp) - i ->
  (get_register st rsp) - i < (stack_base st) + (max_stack_size st) + (above_stack_guard_size st) ->
  ({| instr := (Stack_Write i r_dst);
      addr := n |}
     :: is) / st i--> is / set_error_state st
| I_Get_Globals_Base: forall st is r_base r_dst n,
    get_register st r_base = heap_base st ->
    ({| instr := (Get_Globals_Base r_base r_dst);
        addr :=  n |}
       :: is) / st i--> is / set_register st r_dst (globals_base st)
| I_Globals_Read: forall st is i n r_base r_dst,
    get_register st r_base = globals_base st ->
    i < globals_size st ->
    ({| instr := (Globals_Read r_base i r_dst);
        addr :=  n |}
      :: is) / st i--> is / set_register st r_dst (read_globals st i)
| I_Globals_Write: forall st is i n r_base r_src,
    get_register st r_base = globals_base st ->
    i < globals_size st ->
    ({| instr := (Globals_Write r_base i r_src);
        addr :=  n |}
      :: is) / st i--> is / write_globals st i (get_register st r_src)
| I_Op: forall st is op rs_dst rs_src n,
    ({| instr := (Op op rs_dst rs_src);
        addr := n |}
       :: is) / st i--> is / run_op st op rs_dst rs_src
| I_Branch_True: forall st is c t_label f_label t_bb f_bb n,
  get_basic_block st t_label = Some t_bb ->
  get_basic_block st f_label = Some f_bb ->
  run_conditional st c = true ->
  ({| instr := (Branch c t_label f_label);
      addr := n |}
     :: is) / st i--> (t_bb ++ is) / st
| I_Branch_False: forall st is c t_label f_label t_bb f_bb n,
  get_basic_block st t_label = Some t_bb ->
  get_basic_block st f_label = Some f_bb ->
  run_conditional st c = false ->
  ({| instr := (Branch c t_label f_label);
      addr := n |}
     :: is) / st i--> (f_bb ++ is) / st
| I_Jmp: forall st is j_label j_bb n,
  get_basic_block st j_label = Some j_bb ->
  ({| instr := (Jmp j_label);
      addr := n |}
     :: is) / st i--> (j_bb ++ is) / st
| I_Indirect_Call: forall st is reg f n,
  get_function st (get_register st reg) = Some f ->
  ({| instr := (Indirect_Call reg);
      addr := n |}
     :: is) / st i--> ((get_first_block f) ++ is) / push_frame (push_call st (get_register st reg))
| I_Direct_Call: forall st is fname f n,
  get_function st fname = Some f ->
  ({| instr := (Direct_Call fname);
      addr := n |}
     :: is) / st i--> ((get_first_block f) ++ is) / push_frame (push_call st fname)
| I_Ret: forall st is n,
  st.(frame_size) = 0 ->
  ({| instr := Ret;
     addr := n; |}
    :: is) / st i--> is / pop_frame st
  where " i '/' st 'i-->' i' '/' st' " := (istep (i,st) (i',st')).

Inductive istep_fuel : ((list instr_ty * state) * nat) -> ((list instr_ty * state) * nat) -> Prop :=
| IFuel_Base : forall i s,
    istep_fuel ((i, s), 0) ((i, s), 0)
| IFuel_Step : forall i s i' s' fuel fuel',
    istep (i, s) (i', s') ->
    fuel = S fuel' ->
    istep_fuel ((i, s), fuel) ((i', s'), fuel')
| IFuel_End : forall s fuel,
    istep_fuel (nil, s, fuel) (nil, s, 0).

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

Inductive imultistep_fuel : ((list instr_ty * state) * nat) -> ((list instr_ty * state) * nat) -> Prop :=
| multi_base : forall i s i' s' fuel fuel',
    istep_fuel (i, s, fuel) (i', s', fuel') ->
    imultistep_fuel (i, s, fuel) (i', s', fuel')
| multi_transitive : forall i1 s1 fuel1 i2 s2 fuel2 i3 s3 fuel3,
    istep_fuel (i1, s1, fuel1) (i2, s2, fuel2) ->
    imultistep_fuel (i2, s2, fuel2) (i3, s3, fuel3) ->
    imultistep_fuel (i1, s1, fuel1) (i3, s3, fuel3).

Lemma imultistep_finish' :
  forall fuel is st is1 st1 is' st',
    imultistep_fuel (is, st, fuel) (is1, st1, 0) ->
    imultistep_fuel (is1, st1, 1) (is', st', 0) ->
    imultistep_fuel (is, st, S fuel) (is', st', 0).
Admitted.

