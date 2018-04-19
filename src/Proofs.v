Require Import ZArith.
Require Import Coq.Lists.List.
Require Import LiterateCoq.Tactics.
Require Coq.Program.Wf.

Import ListNotations.
Open Scope list_scope.


Inductive Expr : Set := 
| Num : Z -> Expr
| Plus : Expr -> Expr -> Expr 
| Minus : Expr -> Expr -> Expr.

Fixpoint eval_Expr (e : Expr) : Z := 
  match e with
  | Num n => n                               
  | Plus e1 e2 => eval_Expr e1 + eval_Expr e2
  | Minus e1 e2 => eval_Expr e1 - eval_Expr e2
  end.

Inductive Op : Set :=
| Push : Z -> Op
| Add : Op
| Sub : Op
| OpCount : Op.
              
Fixpoint compile_Expr (e : Expr) : list Op :=
  match e with
  | Num n => [Push n]
  | Plus e1 e2 => compile_Expr e1 ++ compile_Expr e2 ++ [Add]
  | Minus e1 e2 => compile_Expr e1 ++ compile_Expr e2 ++ [Sub]
  end.

Fixpoint eval_Op (s : list Z) (ops : list Op) : option Z :=
  match (ops, s) with
  | ([], [n]) => Some n
  | (Push z :: rest, _) => eval_Op (z :: s) rest 
  | (Add :: rest, n2 :: n1 :: ns) => eval_Op (n1 + n2 :: ns)%Z rest
  | (Sub :: rest, n2 :: n1 :: ns) => eval_Op (n1 - n2 :: ns)%Z rest
  | (OpCount :: rest, _) => eval_Op (Z.of_nat (length rest) :: s) rest
  | _ => None
  end.

Lemma eval_step : forall a : Expr, forall s : list Z, forall xs : list Op,
      eval_Op s (compile_Expr a ++ xs) = eval_Op (eval_Expr a :: s) xs.
Proof.
  hint_rewrite List.app_assoc_reverse.
  induction a; intros; iauto; simpl;
  hint_rewrite IHa2, IHa1;
  iauto'.
Qed.

Lemma eval_step' : forall a : Expr, forall s : list Z,
      eval_Op s (compile_Expr a) = eval_Op (eval_Expr a :: s) [].
Proof.
  intros.
  assert (H: compile_Expr a = compile_Expr a ++ []) by (rewrite app_nil_r; reflexivity); rewrite H; clear H.
  hint eval_step.
  iauto.
Qed.
  
Theorem compiler_correctness : forall a : Expr,
    eval_Op [] (compile_Expr a) = Some (eval_Expr a).
Proof.
  hint_rewrite eval_step.
  hint_simpl.
  induction a; iauto'.
Qed.
  
Definition equiv_Expr (e1 e2 : Expr) : Prop := eval_Expr e1 = eval_Expr e2.
Definition equiv_Op (p1 p2 : list Op) : Prop := eval_Op [] p1 = eval_Op [] p2.

Inductive ExprCtxt : Set := 
| Hole : ExprCtxt
| Plus1 : ExprCtxt -> Expr -> ExprCtxt
| Plus2 : Expr -> ExprCtxt -> ExprCtxt 
| Minus1 : ExprCtxt -> Expr -> ExprCtxt
| Minus2 : Expr -> ExprCtxt -> ExprCtxt .

Fixpoint link_Expr (c : ExprCtxt) (e : Expr) : Expr :=
  match c with
  | Hole => e
  | Plus1 c' e' => Plus (link_Expr c' e) e'
  | Plus2 e' c' => Plus e' (link_Expr c' e)
  | Minus1 c' e' => Minus (link_Expr c' e) e'
  | Minus2 e' c' => Minus e' (link_Expr c' e)
  end.

Definition ctxtequiv_Expr (e1 e2 : Expr) : Prop :=
  forall c : ExprCtxt, eval_Expr (link_Expr c e1) = eval_Expr (link_Expr c e2).

Inductive OpCtxt : Set :=
| PushAdd : Z -> OpCtxt
| PushSub : Z -> OpCtxt
| Empty : OpCtxt.

Definition link_Op  (c : OpCtxt) (p : list Op) : list Op :=
  match c with
  | PushAdd n => Push n :: p ++ [Add]
  | PushSub n => Push n :: p ++ [Sub]
  | Empty => p
  end.


Definition ctxtequiv_Op (p1 p2 : list Op) : Prop :=
  forall c : OpCtxt, eval_Op [] (link_Op c p1) = eval_Op [] (link_Op c p2).

Lemma equivalence_reflection :
  forall e1 e2 : Expr,
  forall p1 p2 : list Op,
  forall comp1 : compile_Expr e1 = p1,
  forall comp2 : compile_Expr e2 = p2,
  forall eqtarget : ctxtequiv_Op p1 p2,
    ctxtequiv_Expr e1 e2.
Proof.
  unfold ctxtequiv_Expr, ctxtequiv_Op in *.
  intros.
  induction c; simpl; try solve [hint_rewrite IHc; iauto];
    (* NOTE(dbp 2018-04-16): Only the base case, for Hole, remains *)
    [idtac].
  (* NOTE(dbp 2018-04-16): In the hole case, we specialize the target ctxt equiv hypothesis to empty *)
  specialize (eqtarget Empty);
    simpl in eqtarget; repeat rewrite app_nil_r in eqtarget.
  unfold link_Op in eqtarget.
  
  (* NOTE(dbp 2018-04-16): At this point, we know e1 -> p1, e2 -> p2, & p1 ≈ p2,
  and want e1 ≈ e2, which follows from compiler correctness *)
  rewrite <- comp1 in eqtarget. rewrite <- comp2 in eqtarget.
  repeat rewrite compiler_correctness in eqtarget.

  inversion eqtarget.
  reflexivity.
Qed.

Lemma equivalence_preservation :
  forall e1 e2 : Expr,
  forall p1 p2 : list Op,
  forall comp1 : compile_Expr e1 = p1,
  forall comp2 : compile_Expr e2 = p2,
  forall eqsource : ctxtequiv_Expr e1 e2,
    ctxtequiv_Op p1 p2.
Proof.
Abort.

Example src_equiv : ctxtequiv_Expr (Plus (Num 1) (Num 1)) (Num 2).
Proof.
  unfold ctxtequiv_Expr.
  induction c; simpl; try rewrite IHc; iauto.
Qed.

Example target_not_equiv :
  eval_Op [] (OpCount :: compile_Expr (Plus (Num 1) (Num 1)) ++ [Add]) <>
  eval_Op [] (OpCount :: compile_Expr (Num 2) ++ [Add]).
Proof.
  simpl.
  congruence.
Qed.

Definition backtranslate (c : OpCtxt) : ExprCtxt :=
  match c with
  | PushAdd n => Plus2 (Num n) Hole
  | PushSub n => Minus2 (Num n) Hole
  | Empty => Hole
  end.

Lemma back_translation_equiv :
  forall c : OpCtxt,
  forall p : list Op,
  forall e : Expr,
  forall c' : ExprCtxt, 
    compile_Expr e = p ->
    backtranslate c = c' ->
    eval_Op [] (link_Op c p) = Some (eval_Expr (link_Expr c' e)).
Proof.
  hint_rewrite eval_step, eval_step'.
  intros.
  match goal with
  | [ c : OpCtxt |- _] => destruct c
  end; 
    match goal with
    | [ H : backtranslate _ = _ |- _] => invert H
    end; simpl; iauto. 
Qed.

 
Lemma equivalence_preservation :
  forall e1 e2 : Expr,
  forall p1 p2 : list Op,
  forall comp1 : compile_Expr e1 = p1,
  forall comp2 : compile_Expr e2 = p2,
  forall eqsource : ctxtequiv_Expr e1 e2,
    ctxtequiv_Op p1 p2.
Proof.
  unfold ctxtequiv_Expr, ctxtequiv_Op in *.
  intros.

  remember (backtranslate c) as c'.
  destruct c; iauto;

  erewrite back_translation_equiv with (e := e1) (c' := c'); iauto;
  erewrite back_translation_equiv with (e := e2) (c' := c'); iauto;
  specialize (eqsource c'); simpl in *; congruence.
Qed.