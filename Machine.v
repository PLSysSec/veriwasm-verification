(*Require Import Coq.FSets.FMaps.*)
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Bits.
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
| A_Reg : register -> value
| A_Const : int64 -> value
| A_MultPlus : int64 -> value -> value -> value.

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
| Direct_Call : instr_class
| Ret : instr_class.

Definition basic_block := list instr_class.

Inductive edge_class : Set :=
| True_Branch
| False_Branch
| Non_Branch.

Definition node_ty := prod (prod basic_block (option conditional)) nat.

Record cfg_ty := {
  nodes : list node_ty;
  edges : list ((node_ty * node_ty) * edge_class);
  start_node : node_ty
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

(* TODO: This definition is super messy *)
Definition well_formed_cfg (cfg : cfg_ty) : Prop :=
  unique_bb cfg /\ edges_in_nodes cfg.

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
  intros; decide equality; try apply register_eq_dec; try apply value_eq_dec; decide equality.
Defined.

Definition basic_block_eq_dec : forall (x y : basic_block), {x=y} + {x<>y}.
  intros; decide equality; apply instr_class_eq_dec.
Defined.

Definition node_ty_eq_dec : forall (x y : node_ty), {x=y} + {x<>y}.
  intros; decide equality; decide equality.
  - decide equality. apply conditional_eq_dec.
  - apply basic_block_eq_dec.
Defined.

Definition cfg_ty_eq_dec : forall (x y : cfg_ty), {x=y} + {x<>y}.
  intros; decide equality; try apply node_ty_eq_dec.
  - decide equality. decide equality; try apply edge_class_eq_dec.
    decide equality; apply node_ty_eq_dec.
  - decide equality. apply node_ty_eq_dec.
Defined.

Inductive flag : Set :=
| of
| sf
| zf
| pf
| cf.

Definition fmap (A B:Type) := 
  A -> B.

Definition map_set {A} (eq_dec:forall (x y:A),{x=y}+{x<>y}) {B} (f:fmap A B) (x:A) (v:B) : fmap A B :=
  fun y => if eq_dec x y then v else f y.

Definition map_get {A} {B} (f:fmap A B) (x:A) : B := 
  f x.

