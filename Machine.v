Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Logic.
Require Import Coq.Arith.PeanoNat.
Require Import VerifiedVerifier.Bits.
Require Import VerifiedVerifier.Maps.

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
| Const : nat -> value.

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
| Counter_Register_Zero.

Definition label := nat.

Inductive instr_class : Type :=
| Heap_Read : register -> register -> register -> register -> instr_class
| Heap_Write : register -> register -> register -> register -> instr_class
| Heap_Check : register -> instr_class
| Call_Check : register -> instr_class
| Reg_Move : register -> register -> instr_class
| Reg_Write : register -> value -> instr_class
| Stack_Expand_Static : nat -> instr_class
| Stack_Expand_Dynamic : nat -> instr_class
| Stack_Contract : nat -> instr_class
| Stack_Read : register -> nat -> instr_class
| Stack_Write : nat -> register -> instr_class
| Op : opcode -> list register -> list register -> instr_class
| Indirect_Call : register -> instr_class
| Direct_Call : nat -> instr_class
| Branch : conditional -> label -> label -> instr_class
| Jmp: label -> instr_class
| Ret : instr_class.

Definition terminating_instr_class i :=
match i with
| Branch _ _ _ | Jmp _ | Ret => true
| _ => false
end.

Definition nonterminating_instr_class i :=
negb (terminating_instr_class i).

Record instr_ty := {
  instr : instr_class;
  addr : nat;
}.

Definition basic_block := list instr_ty.

Definition wf_instr_ty (i : instr_ty) (nodes : list basic_block) :=
match i.(instr) with
| Branch _ t_label f_label => (t_label < length nodes) /\ (f_label < length nodes)
| Jmp j_label => j_label < length nodes
| Ret => True
| _ => False
end.

Fixpoint wf_bb (bb : basic_block) (nodes : list basic_block) :=
match bb with
| i :: bb' => wf_instr_ty i nodes /\ wf_bb bb' nodes
| nil => True
end.

Structure ControlFlowGraph := {
  V : list basic_block;
  E : list (nat * nat);
(*  E : list ({n : nat | n < length V} * {n : nat | n < length V}); *)
  wf_cfg : forall bb, In bb V -> wf_bb bb V;
}.

Definition function := ControlFlowGraph.

Structure program := {
  Funs : list ControlFlowGraph;
  wf_addrs : forall f f' v v' i i' instr instr',
      In f Funs ->
      In f' Funs ->
      In v f.(V) ->
      In v' f'.(V) ->
      Some instr = (nth_error v i) ->
      Some instr' = (nth_error v' i') ->
      instr.(addr) = instr'.(addr) ->
      (f = f' /\
       v = v' /\
       i = i');
}.

Definition register_eq_dec : forall (x y : register), {x=y} + {x<>y}.
  intros; decide equality.
Defined.

Definition conditional_eq_dec : forall (x y : conditional), {x=y} + {x<>y}.
  intros; decide equality; try apply register_eq_dec.
Defined.

Definition value_eq_dec : forall (x y: value), {x=y} + {x<>y}.
  intros; decide equality; try apply register_eq_dec; try apply Nat.eq_dec.
Defined.

Definition instr_class_eq_dec : forall (x y : instr_class), {x=y} + {x<>y}.
  intros; decide equality; try apply register_eq_dec; try apply value_eq_dec; try apply string_dec;
  try apply conditional_eq_dec; decide equality; decide equality.
Defined.

Definition instr_ty_eq_dec : forall (x y : instr_ty), {x=y} + {x<>y}.
  intros; decide equality. decide equality. apply instr_class_eq_dec.
Defined.

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
