(*Require Import Coq.FSets.FMaps.*)
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Require Import VerifiedVerifier.Bits.
Require Import VerifiedVerifier.Maps.
(*Require Import Coq.Vectors.Vector.*)
(*Require Import SFI.Machine.Bits.*)
(*Require Import bbv.Word.*)

(*Notation word1 := (word 1).
Notation word8 := (word 8).
Notation word64 := (word 64).
Notation wzero8 := (wzero 8).*)

Inductive register : Set :=
| rax
| rbx
| rcx
| rdx
| rbp
| rsp
| rsi
| rdi
| rip
| r8
| r9
| r10
| r11
| r12
| r13
| r14
| r15.

Inductive value : Set :=
| Const : int64 -> value.

Inductive opcode : Set := 
| Add : opcode
| Sub : opcode
| Mult : opcode
| Div : opcode.

Fixpoint update {A} (l : list A) (i : nat) (v : A) : list A :=
match l, i with
| nil , _ => l
| h :: t, 0 => v :: t
| h :: t, S i' => update t i' v
end.

(* List from https://en.wikibooks.org/wiki/X86_Assembly/Control_Flow#Jump_if_Zero *)
Inductive conditional :=
| Not_Equal : register -> register -> conditional
| Equal : register -> register -> conditional
| Greater : register -> register -> conditional       (*signed*)
| Greater_Equal : register -> register -> conditional (*signed*)
| Above : register -> register -> conditional         (*unsigned*)
| Above_Equal : register -> register -> conditional   (*unsigned*)
| Lesser : register -> register -> conditional        (*signed*)
| Lesser_Equal : register -> register -> conditional  (*signed*)
| Below : register -> register -> conditional         (*unsigned*)
| Below_Equal : register -> register -> conditional   (*unsigned*)
(*TODO: Flags need to be set for these
| Overflow
| Not_Overflow
| Zero
| Not_Zero
| Signed
| Not_Signed
*)
| Counter_Register_Zero.

Inductive instr_class := 
| Heap_Read : register -> register -> register -> instr_class
| Heap_Write : register -> register -> register -> instr_class
| Heap_Check : register -> instr_class
| Call_Check : register -> instr_class
| Reg_Move : register -> register -> instr_class
| Reg_Write : register -> value -> instr_class
| Stack_Expand : nat -> instr_class
| Stack_Contract : nat -> instr_class
| Stack_Read : register -> nat -> instr_class
| Stack_Write : nat -> register -> instr_class
| Indirect_Call : register -> instr_class
| Direct_Call : string -> instr_class
| Branch : conditional -> instr_class
| Op : opcode -> list register -> list register -> instr_class
| Ret : instr_class.

Definition basic_block := list instr_class.

Inductive edge_class : Set :=
| True_Branch
| False_Branch
| Non_Branch.

Definition node_ty := prod basic_block nat.
Definition edge_ty := (prod (prod node_ty node_ty) edge_class).

Record cfg_ty := {
  nodes : list node_ty;
  edges : list edge_ty;
  start_node : node_ty
}.

Definition function_ty := prod cfg_ty string.

Record program_ty := {
  fun_table : partial_map int64 function_ty;
  fun_list : list function_ty;
  main : function_ty;
}.

Definition unique_bb (cfg : cfg_ty) : Prop :=
  forall i i',
    eq (nth i cfg.(nodes)) (nth i' cfg.(nodes)) ->
    eq i i'.

Definition edges_in_nodes (cfg : cfg_ty) : Prop :=
  forall e,
    In e cfg.(edges) ->
    In ((compose fst fst) e) cfg.(nodes) /\
    In ((compose snd fst) e) cfg.(nodes).

(* TODO: This definition is incomplete *)
Definition well_formed_cfg (cfg : cfg_ty) : Prop :=
  unique_bb cfg /\ edges_in_nodes cfg.

Definition well_formed_fun (f : function_ty) : Prop :=
  well_formed_cfg (fst f).

Definition unique_fun_name (p : program_ty) : Prop :=
  forall f f',
    In f p.(fun_list) ->
    In f' p.(fun_list) ->
    (eq f f' \/ (not (eq (snd f) (snd f')))).

Definition fun_list_table_contents (p : program_ty) : Prop :=
  forall f,
    In f p.(fun_list) ->
    exists i,
      p.(fun_table) i = Some f.

Definition fun_table_list_contents (p : program_ty) : Prop :=
  forall i f,
    p.(fun_table) i = Some f ->
    In f p.(fun_list).

Definition well_formed_program (p : program_ty) : Prop :=
  unique_fun_name p /\
  fun_list_table_contents p /\
  fun_table_list_contents p /\
  forall f,
    In f p.(fun_list) -> well_formed_fun f.

Definition register_eq_dec : forall (x y : register), {x=y} + {x<>y}.
  intros; decide equality.
Defined.

Definition conditional_eq_dec : forall (x y : conditional), {x=y} + {x<>y}.
  intros; decide equality; try apply register_eq_dec.
Defined.

Definition edge_class_eq_dec : forall (x y : edge_class), {x=y} + {x<>y}.
  intros; decide equality.
Defined.

Definition value_eq_dec : forall (x y: value), {x=y} + {x<>y}.
  intros; decide equality; try apply register_eq_dec; try apply int64_eq_dec.
Defined.

Definition instr_class_eq_dec : forall (x y : instr_class), {x=y} + {x<>y}.
  intros; decide equality; try apply register_eq_dec; try apply value_eq_dec; try apply string_dec;
  try apply conditional_eq_dec; decide equality; decide equality.
Defined.

Definition basic_block_eq_dec : forall (x y : basic_block), {x=y} + {x<>y}.
  intros; decide equality; apply instr_class_eq_dec.
Defined.

Definition node_ty_eq_dec : forall (x y : node_ty), {x=y} + {x<>y}.
  intros; decide equality; decide equality. apply instr_class_eq_dec.
Defined.

Definition edge_ty_eq_dec : forall (x y : edge_ty), {x=y} + {x<>y}.
  intros; decide equality; decide equality; decide equality; decide equality;
  apply instr_class_eq_dec.
Defined.

Definition cfg_ty_eq_dec : forall (x y : cfg_ty), {x=y} + {x<>y}.
  intros; decide equality; try apply node_ty_eq_dec.
  - decide equality. decide equality; try apply edge_class_eq_dec.
    decide equality; apply node_ty_eq_dec.
  - decide equality. apply node_ty_eq_dec.
Defined.

Definition node_ty_eqb (a : node_ty) (b : node_ty) : bool :=
  if node_ty_eq_dec a b
  then true
  else false.

Definition edge_ty_eqb (a : edge_ty) (b : edge_ty) : bool :=
  if edge_ty_eq_dec a b
  then true
  else false.

Inductive flag : Set :=
| of
| sf
| zf
| pf
| cf.


Lemma register_get_after_set_eq : forall A (abs_regs : total_map register A) reg v,
  (t_update register_eq_dec abs_regs reg v) reg = v.
Proof.
  intros A abs_regs reg v. unfold t_update. destruct (register_eq_dec reg reg).
  - reflexivity.
  - exfalso. apply n. reflexivity.
Qed.

Lemma register_get_after_set_neq : forall A (abs_regs : total_map register A) reg1 reg2 v,
    reg1 <> reg2 ->
    (t_update register_eq_dec abs_regs reg2 v) reg1 = abs_regs reg1.
Proof.
  intros A abs_regs reg1 reg2 v Heq. unfold t_update. destruct (register_eq_dec reg2 reg1).
  - exfalso. apply Heq. auto.
  - reflexivity.
Qed.

