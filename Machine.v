(*Require Import Coq.FSets.FMaps.*)

Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Logic.
Require Import Coq.Arith.PeanoNat.
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
(*TODO: Flags need to be set for these
| Overflow
| Not_Overflow
| Zero
| Not_Zero
| Signed
| Not_Signed
*)
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

Definition basic_block := list instr_class.

Definition wf_instr_class (i : instr_class) (nodes : list basic_block) :=
match i with
| Branch _ t_label f_label => (t_label < length nodes) /\ (f_label < length nodes)
| Jmp j_label => j_label < length nodes
| Ret => True
| _ => False
end.

Fixpoint wf_bb (bb : basic_block) (nodes : list basic_block) :=
match bb with
| i :: bb' => wf_instr_class i nodes /\ wf_bb bb' nodes
| nil => True
end.

Structure ControlFlowGraph := {
  V : list basic_block;
  E : list (nat * nat);
(*  E : list ({n : nat | n < length V} * {n : nat | n < length V}); *)
  wf_cfg : forall bb, In bb V -> wf_bb bb V;
}.



(*

Inductive terminating_instr_class : instr_class -> Prop :=
| T_Branch: forall cond t_lable f_label,
  terminating_instr_class (Branch cond t_lable f_label)
| T_Jmp: forall j_label,
  terminating_instr_class (Jmp j_label)
| T_Ret:
  terminating_instr_class (Ret).
Hint Constructors terminating_instr_class.

(*Definition branch_instr_class := {i : instr_class | forall cond t_label f_label, i = (Branch cond t_label f_label)}.
Definition jmp_instr_class := {i : instr_class | forall j_label, i = (Jmp j_label)}.
Definition ret_instr_class := {i : instr_class | i = (Ret)}.*)

(* Definition term_instr_class := (sum branch_instr_class (sum jmp_instr_class ret_instr_class)). *)
Definition term_instr_class := {i : instr_class | terminating_instr_class i}. 
Definition nonterm_instr_class := {i : instr_class | not (terminating_instr_class i)}.
(* Definition basic_block := {l : list instr_class | terminating_instr_class (last l)}. *)

Inductive nonterminating_instr_class : instr_class -> Prop :=
| NT_Heap_Read : forall r_dst r_src r_base,
  nonterminating_instr_class (Heap_Read r_dst r_src r_base)
| NT_Heap_Write: forall r_dst r_src r_base,
  nonterminating_instr_class (Heap_Write r_dst r_src r_base)
| NT_Heap_Check: forall reg,
  nonterminating_instr_class (Heap_Check reg)
| NT_Call_Check: forall reg,
  nonterminating_instr_class (Call_Check reg)
| NT_Reg_Move: forall r_dst r_src,
  nonterminating_instr_class (Reg_Move r_dst r_src)
| NT_Reg_Write: forall r_dst val,
  nonterminating_instr_class (Reg_Write r_dst val)
| NT_Stack_Expand: forall i,
  nonterminating_instr_class (Stack_Expand i)
| NT_Stack_Contract: forall i,
  nonterminating_instr_class (Stack_Contract i)
| NT_Stack_Read: forall r_dst i,
  nonterminating_instr_class (Stack_Read r_dst i)
| NT_Stack_Write: forall i r_src,
  nonterminating_instr_class (Stack_Write i r_src)
| NT_Indirect_Call: forall reg,
  nonterminating_instr_class (Indirect_Call reg)
| NT_Direct_Call: forall fname,
  nonterminating_instr_class (Direct_Call fname)
| NT_Op: forall op rs_dst rs_src,
  nonterminating_instr_class (Op op rs_dst rs_src).
Hint Constructors nonterminating_instr_class.

Lemma instr_class_term_or_nonterm: forall i,
  terminating_instr_class i \/ nonterminating_instr_class i.
Proof.
  destruct i; auto.
Qed.

Lemma instr_class_not_term_and_nonterm: forall i,
  ~ (terminating_instr_class i /\ nonterminating_instr_class i).
Proof.
  destruct i; intros H; inversion H; try inversion H0; try inversion H1.
Qed.

Inductive basic_block' : Type:=
| Basic_Block_One: 
  term_instr_class -> basic_block'
| Basic_Block_Many:
  nonterm_instr_class -> basic_block' -> basic_block'.

Fixpoint last (bb : basic_block') : term_instr_class :=
match bb with
| Basic_Block_One i => i
| Basic_Block_Many i bb' => last bb'
end.

Program Definition branch_block := {bb : basic_block' | forall cond t_label f_label, last bb = (Branch cond t_label f_label)}.
Program Definition jmp_block := {bb : basic_block' | forall j_label, last bb = (Jmp j_label)}.
Program Definition ret_block := {bb : basic_block' | last bb = Ret}.

Definition basic_block := branch_block + jmp_block + ret_block.

Definition bb_last (bb : basic_block) : term_instr_class :=
match bb with
| inl (inl branch) => last (proj1_sig branch)
| inl (inr jmp) => last (proj1_sig jmp)
| inr ret => last (proj1_sig ret)
end.

Definition wf_bb (bb : basic_block) (nodes : list basic_block) :=
match proj1_sig (bb_last bb) with
| Branch _ t_label f_label => (t_label < length nodes) /\ (f_label < length nodes)
| Jmp j_label => j_label < length nodes
| Ret => True
| _ => False
end.

Structure ControlFlowGraph := {
  V : list basic_block;
  E : list ({src : basic_block | In src V} * {dst : basic_block | In dst V});
  wf_cfg : forall bb, In bb V -> wf_bb bb V;
}.
*)

Definition function := ControlFlowGraph.

Definition program := list ControlFlowGraph.

(* Definition basic_block := list instr_class. *)
(*
Inductive edge_class : Set :=
| True_Branch
| False_Branch
| Non_Branch.

Compute (head (1 :: 2 :: nil)).


Definition node_ty := prod label basic_block.
Definition edge_ty := (prod (prod node_ty node_ty) edge_class).

Structure DiGraph := {
  V :> nat ; (* The number of vertices. So the vertices are numbers 0, 1, ..., V-1. *)
  E :> nat -> nat -> Prop ; (* The edge relation *)
  E_decidable : forall x y : nat, ({E x y} + {~ E x y}) ;
}.

Definition cfg

Record cfg_ty := {
  nodes : list node_ty;
  edges : list edge_ty;
  start_node : node_ty
}.

Definition function_ty := prod cfg_ty string.

Record program_ty := {
  funs : list function_ty;
  main : function_ty
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
*)


(*
Definition well_formed_fun (f : function) : Prop :=
  well_formed_cfg (fst f).

Definition unique_fun_name (p : program) : Prop :=
  forall f f',
    In f p.(funs) ->
    In f' p.(funs) ->
    (eq f f' \/ (not (eq (snd f) (snd f')))).

Definition well_formed_program (p : program) : Prop :=
  unique_fun_name p /\
  forall f,
    In f p.(funs) -> well_formed_fun f.
*)
Definition register_eq_dec : forall (x y : register), {x=y} + {x<>y}.
  intros; decide equality.
Defined.

Definition conditional_eq_dec : forall (x y : conditional), {x=y} + {x<>y}.
  intros; decide equality; try apply register_eq_dec.
Defined.

(*
Definition edge_class_eq_dec : forall (x y : edge_class), {x=y} + {x<>y}.
  intros; decide equality.
Defined.
*)
Definition value_eq_dec : forall (x y: value), {x=y} + {x<>y}.
  intros; decide equality; try apply register_eq_dec; try apply Nat.eq_dec.
Defined.

Definition instr_class_eq_dec : forall (x y : instr_class), {x=y} + {x<>y}.
  intros; decide equality; try apply register_eq_dec; try apply value_eq_dec; try apply string_dec;
  try apply conditional_eq_dec; decide equality; decide equality.
Defined.

(*
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
*)
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

