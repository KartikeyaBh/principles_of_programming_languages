(* -------------------------------------- Homework 4 --------------------------------------
 *
 *)

Require Import Frap.


(* --- SECTION 1: Adding pairs to STLC  --- *)

(* In this section, we'll add programming constructs for manipulating
 * pairs to the simply typed lambda calculus.  As is typical, there
 * will be constructs for building up pairs and also constructs for
 * taking them apart.
*)

Module StlcWithPairs.
  Inductive exp : Set :=
  | Var (x : var)
  | Const (n : nat)
  | Plus (e1 e2 : exp)
  | Mult (e1 e2 : exp)
  | Abs (x : var) (e1 : exp)
  | App (e1 e2 : exp)

  (* Here we add syntax for the new language features:
   *   - `MkPair` is syntax for constructing the pair of `e1` and `e2`. Like `(e1,e2)` in Coq.
   *   - `Fst` is syntax for projecting out the first element of a pair.
   *   - `Snd` is syntax for projecting out the second element of a pair.
   *)
  | MkPair (e1 e2 : exp)
  | Fst (e : exp)
  | Snd (e : exp).

  Inductive value : exp -> Prop :=
  | VConst : forall n, value (Const n)
  | VAbs : forall x e1, value (Abs x e1)

  (* A pair is a value if both its components are values. *)
  | VMkPair : forall v1 v2, value v1 -> value v2 -> value (MkPair v1 v2).

  (* PROBLEM 1 [4 points, ~3 LOC]
   * Extend the definition of substitution to handle the new language features.
   *
   * Hint: You'll need one new case per new constructor of `exp`.
   *
   * Hint: You'll know you got this right if you can prove the Lemma `substitution` below.
   *)
  Fixpoint subst (e1 : exp) (x : string) (e2 : exp) : exp :=
    match e2 with
      | Var y => if y ==v x then e1 else Var y
      | Const n => Const n
      | Plus e2' e2'' => Plus (subst e1 x e2') (subst e1 x e2'')
      | Mult e2' e2'' => Mult (subst e1 x e2') (subst e1 x e2'')
      | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
      | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
      | MkPair e2' e2'' => MkPair (subst e1 x e2') (subst e1 x e2'')
      | Fst e2' => Fst (subst e1 x e2')
      | Snd e2' => Snd (subst e1 x e2')
    end.

  Inductive context : Set :=
  | Hole : context
  | Plus1 : context -> exp -> context
  | Plus2 : exp -> context -> context
  | Mult1 : context -> exp -> context
  | Mult2 : exp -> context -> context
  | App1 : context -> exp -> context
  | App2 : exp -> context -> context

  (* We extend the definition of evaluation contexts to include the new features. *)
  | MkPair1 : context -> exp -> context
  | MkPair2 : exp -> context -> context
  | CFst : context -> context
  | CSnd : context -> context.

  Inductive plug : context -> exp -> exp -> Prop :=
  | PlugHole : forall e, plug Hole e e
  | PlugPlus1 : forall e e' C e2,
    plug C e e'
    -> plug (Plus1 C e2) e (Plus e' e2)
  | PlugPlus2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (Plus2 v1 C) e (Plus v1 e')
  | PlugMult1 : forall e e' C e2,
    plug C e e'
    -> plug (Mult1 C e2) e (Mult e' e2)
  | PlugMult2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (Mult2 v1 C) e (Mult v1 e')
  | PlugApp1 : forall e e' C e2,
    plug C e e'
    -> plug (App1 C e2) e (App e' e2)
  | PlugApp2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (App2 v1 C) e (App v1 e')

  (* PROBLEM 2 [4 points, ~15 LOC]
   * Extend the definition of `plug` to handle the new language features.
   *
   * Hint: You'll need two new constructors for `MkPair` (similar to the constructors for `App` above).
   *
   * Hint: You'll need one new constructor for each of `Fst` and `Snd`.
   *
   * Hint: You'll know you got this right if you can prove the Lemma `generalize_plug` below.
   *)
  | PlugMkPair1 : forall e e' C e2,
    plug C e e'
    -> plug (MkPair1 C e2) e (MkPair e' e2)
  | PlugMkPair2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (MkPair2 v1 C) e (MkPair v1 e')
  | PlugCFst : forall e e' C,
    plug C e e'
    -> plug (CFst C) e (Fst e')
  | PlugCSnd : forall e e' C,
    plug C e e'
    -> plug (CSnd C) e (Snd e').

  Inductive step0 : exp -> exp -> Prop :=
  | Beta : forall x e v,
    value v
    -> step0 (App (Abs x e) v) (subst v x e)
  | Add : forall n1 n2,
    step0 (Plus (Const n1) (Const n2)) (Const (n1 + n2))
  | Multiply : forall n1 n2,
      step0 (Mult (Const n1) (Const n2)) (Const (n1 * n2))
  (* PROBLEM 3 [4 points, ~10 LOC]
   * Extend the definition of `step0` to handle the new language features.
   *
   * Hint: You'll need two new constructors: one for stepping `fst (v1, v2)` and one for `snd (v1, v2)`.
   *
   * Hint: You'll know you got this right if you can prove the Lemma `preservation0` below.
   *)
  | First : forall v1 v2,
      step0 (Fst (MkPair v1 v2)) v1
  | Second : forall v1 v2,
      step0 (Snd (MkPair v1 v2)) v2.

  Inductive step : exp -> exp -> Prop :=
  | StepRule : forall C e1 e2 e1' e2',
    plug C e1 e1'
    -> plug C e2 e2'
    -> step0 e1 e2
    -> step e1' e2'.

  Definition trsys_of (e : exp) := {|
    Initial := {e};
    Step := step
  |}.


  Inductive type :=
  | Nat                  (* Numbers *)
  | Fun (dom ran : type) (* Functions *)

  (* Here is a type for a pair whose first component has type t1 and whose second component has type t2. *)
  | Pair (t1 t2 : type)  (* Pairs *).

  Inductive hasty : fmap var type -> exp -> type -> Prop :=
  | HtVar : forall G x t,
    G $? x = Some t
    -> hasty G (Var x) t
  | HtConst : forall G n,
    hasty G (Const n) Nat
  | HtPlus : forall G e1 e2,
    hasty G e1 Nat
    -> hasty G e2 Nat
    -> hasty G (Plus e1 e2) Nat
  | HtMult : forall G e1 e2,
    hasty G e1 Nat
    -> hasty G e2 Nat
    -> hasty G (Mult e1 e2) Nat

  | HtAbs : forall G x e1 t1 t2,
    hasty (G $+ (x, t1)) e1 t2
    -> hasty G (Abs x e1) (Fun t1 t2)
  | HtApp : forall G e1 e2 t1 t2,
    hasty G e1 (Fun t1 t2)
    -> hasty G e2 t1
    -> hasty G (App e1 e2) t2

  (* PROBLEM 4 [4 points, ~10 LOC]
   * Extend the definition of `hasty` to handle the new language features.
   *
   * Hint: You'll need one new constructor per new constructor of `exp`.
   *
   * Hint: You'll know you got this right if you can prove all the examples and lemmas below.
   *)
  | HtMkPair : forall G e1 e2 t1 t2,
    hasty G e1 t1
    -> hasty G e2 t2
    -> hasty G (MkPair e1 e2) (Pair t1 t2)
  | HtFst : forall G e t1 t2,
    hasty G e (Pair t1 t2)
    -> hasty G (Fst e) t1
  | HtSnd : forall G e t1 t2,
    hasty G e (Pair t1 t2)
    -> hasty G (Snd e) t2.

  Hint Constructors value plug step0 step hasty.

  Infix "-->" := Fun (at level 60, right associativity).
  Coercion Const : nat >-> exp.
  Infix "^+^" := Plus (at level 50).
  Coercion Var : var >-> exp.
  Notation "\ x , e" := (Abs x e) (at level 51).
  Infix "@" := App (at level 49, left associativity).


  Example one_plus_one : hasty $0 (1 ^+^ 1) Nat.
  Proof.
    repeat (econstructor; simplify).
  Qed.

  Example add : hasty $0 (\"n", \"m", "n" ^+^ "m") (Nat --> Nat --> Nat).
  Proof.
    repeat (econstructor; simplify).
  Qed.

  Example eleven : hasty $0 ((\"n", \"m", "n" ^+^ "m") @ 7 @ 4) Nat.
  Proof.
    repeat (econstructor; simplify).
  Qed.

  Example seven_the_long_way : hasty $0 ((\"x", "x") @ (\"x", "x") @ 7) Nat.
  Proof.
    repeat (econstructor; simplify).
  Qed.

  (* PROBLEM 5 [2 points, ~3 tactics]
   * Prove that the following expression has the given type.
   *
   * Hint: If your definitions are right, the same proof as the examples just above here should work.
   *)
  Example pair_of_one_and_the_increment_function : hasty $0 (MkPair 1 (\"x", "x" ^+^ 1)) (Pair Nat (Nat --> Nat)).
  Proof.
    repeat (econstructor; simplify).
  Qed.

  (* PROBLEM 6 [2 points, ~3 tactics]
   * Prove that the following expression has the given type.
   *
   * Hint: If your definitions are right, the same proof as the examples just above here should work.
   *)
  Example swap_pair_nats : hasty $0 (\"p", MkPair (Fst "p") (Snd "p"))  (Pair Nat Nat --> Pair Nat Nat).
  Proof.
    repeat (econstructor; simplify).
  Qed.

  Definition unstuck e := value e
    \/ (exists e' : exp, step e e').

  (* PROBLEM 7 [4 points, ~30 tactics]
   * Extend the proof of `progress` to handle the new language constructs.
   *
   * Hint: It will help to step through a few of the existing cases in the proof
   * to see how they usually work.
   *)
  Lemma progress : forall e t,
    hasty $0 e t
    -> unstuck e.
  Proof.
    unfold unstuck; induct 1; simplify; try equality.
    - left.
      constructor.
    - propositional.
      + right.
        match goal with
        | [ H1 : value e1, H2 : hasty $0 e1 _ |- _ ] => invert H1; invert H2
        end.
        match goal with
        | [ H1 : value e2, H2 : hasty $0 e2 _ |- _ ] => invert H1; invert H2
        end.
        exists (Const (n + n0)).
        eapply StepRule with (C := Hole).
        eauto.
        eauto.
        constructor.
      + match goal with
        | [ H : exists x, _ |- _ ] => invert H
        end.
        match goal with
        | [ H : step _ _ |- _ ] => invert H
        end.
        right.
        eauto.
      + match goal with
        | [ H : exists x, _ |- _ ] => invert H
        end.
        match goal with
        | [ H : step _ _ |- _ ] => invert H
        end.
        right.
        eauto.
      + match goal with
        | [ H : exists x, step e1 _ |- _ ] => invert H
        end.
        match goal with
        | [ H : step _ _ |- _ ] => invert H
        end.
        right.
        exists (Plus x e2).
        eapply StepRule with (C := Plus1 C e2).
        eauto.
        eauto.
        assumption.
    - propositional.
      + right.
        match goal with
        | [ H1 : value e1, H2 : hasty $0 e1 _ |- _ ] => invert H1; invert H2
        end.
        match goal with
        | [ H1 : value e2, H2 : hasty $0 e2 _ |- _ ] => invert H1; invert H2
        end.
        exists (Const (n * n0)).
        eapply StepRule with (C := Hole).
        eauto.
        eauto.
        constructor.
      + match goal with
        | [ H : exists x, _ |- _ ] => invert H
        end.
        match goal with
        | [ H : step _ _ |- _ ] => invert H
        end.
        right.
        eauto.
      + match goal with
        | [ H : exists x, _ |- _ ] => invert H
        end.
        match goal with
        | [ H : step _ _ |- _ ] => invert H
        end.
        right.
        eauto.
      + match goal with
        | [ H : exists x, step e1 _ |- _ ] => invert H
        end.
        match goal with
        | [ H : step _ _ |- _ ] => invert H
        end.
        right.
        exists (Mult x e2).
        eapply StepRule with (C := Mult1 C e2).
        eauto.
        eauto.
        assumption.
    - left.
      constructor.
    - propositional.
      + right.
        match goal with
        | [ H1 : value e1, H2 : hasty $0 e1 _ |- _ ] => invert H1; invert H2
        end.
        exists (subst e2 x e0).
        eapply StepRule with (C := Hole).
        eauto.
        eauto.
        constructor.
        assumption.
      + match goal with
        | [ H : exists x, _ |- _ ] => invert H
        end.
        match goal with
        | [ H : step _ _ |- _ ] => invert H
        end.
        right.
        eauto.
      + match goal with
        | [ H : exists x, _ |- _ ] => invert H
        end.
        match goal with
        | [ H : step _ _ |- _ ] => invert H
        end.
        right.
        eauto.
      + match goal with
        | [ H : exists x, step e1 _ |- _ ] => invert H
        end.
        match goal with
        | [ H : step _ _ |- _ ] => invert H
        end.
        right.
        exists (App x e2).
        eapply StepRule with (C := App1 C e2).
        eauto.
        eauto.
        assumption.
    - propositional.
      + left.
        econstructor; assumption.
      + right.
        invert H3.
        invert H2.
        eauto.
      + right.
        invert H1.
        invert H2.
        eauto.
      + right.
        invert H1.
        invert H2.
        invert H3.
        invert H2.
        eauto.
    - propositional.
      + right.
        invert H0; invert H.
        assert (step (Fst (MkPair v1 v2)) v1).
        * econstructor; constructor.
        * eexists.
          apply H.
      + right.
        invert H0.
        invert H1.
        eauto.
    - propositional.
      + right.
        invert H0; invert H.
        assert (step (Snd (MkPair v1 v2)) v2).
        * econstructor; constructor.
        * eexists.
          apply H.
      + right.
        invert H0.
        invert H1.
        eauto.
  Qed.

  Lemma weakening_override : forall (G G' : fmap var type) x t,
    (forall x' t', G $? x' = Some t' -> G' $? x' = Some t')
    -> (forall x' t', G $+ (x, t) $? x' = Some t'
                      -> G' $+ (x, t) $? x' = Some t').
  Proof.
    simplify.
    cases (x ==v x'); simplify; eauto.
  Qed.

  (* PROBLEM 8 [4 points, ~4 tactics]
   * Extend the proof of `weakening` to handle the new language constructs.
   *
   * Hint: It will help to step through a few of the existing cases in the proof
   * to see how they usually work.
   *)
  Lemma weakening : forall G e t,
    hasty G e t
    -> forall G', (forall x t, G $? x = Some t -> G' $? x = Some t)
      -> hasty G' e t.
  Proof.
    induct 1; simplify.
    - constructor.
      apply H0.
      assumption.
    - constructor.
    - constructor.
      apply IHhasty1.
      assumption.
      apply IHhasty2.
      assumption.
    - constructor.
      apply IHhasty1.
      assumption.
      apply IHhasty2.
      assumption.
    - constructor.
      apply IHhasty.
      apply weakening_override.
      assumption.
    - econstructor.
      apply IHhasty1.
      assumption.
      apply IHhasty2.
      assumption.
    - constructor.
      apply IHhasty1.
      assumption.
      apply IHhasty2.
      assumption.
    - econstructor.
      apply IHhasty.
      assumption.
    - econstructor.
      apply IHhasty.
      assumption.
  Qed.

  Lemma substitution : forall G x t' e t e',
    hasty (G $+ (x, t')) e t
    -> hasty $0 e' t'
    -> hasty G (subst e' x e) t.
  Proof.
    induct 1; simplify.
    - cases (x0 ==v x).
      + simplify.
        invert H.
        eapply weakening.
        eassumption.
        simplify.
        equality.
      + simplify.
        constructor.
        assumption.
    - constructor.
    - constructor.
      eapply IHhasty1; equality.
      eapply IHhasty2; equality.
    - constructor.
      eapply IHhasty1; equality.
      eapply IHhasty2; equality.
    - cases (x0 ==v x).
      + constructor.
        eapply weakening.
        eassumption.
        simplify.
        cases (x0 ==v x1).
        * simplify.
          assumption.
        * simplify.
          assumption.
      + constructor.
        eapply IHhasty.
        maps_equal.
        assumption.
    - econstructor.
      eapply IHhasty1; equality.
      eapply IHhasty2; equality.
    - constructor.
      + eapply IHhasty1; equality.
      + eapply IHhasty2; equality.
    - econstructor.
      apply IHhasty; equality.
    - econstructor.
      apply IHhasty; equality.
  Qed.

  (* PROBLEM 10 [4 points, ~7 tactics]
   * Extend the proof of `preservation0` to handle the new language constructs.
   *
   * Hint: It will help to step through a few of the existing cases in the proof
   * to see how they usually work.
   *)
  Lemma preservation0 : forall e1 e2,
    step0 e1 e2
    -> forall t, hasty $0 e1 t
      -> hasty $0 e2 t.
  Proof.
    invert 1; simplify.
    - invert H.
      invert H4.
      eapply substitution.
      + eassumption.
      + assumption.
    - invert H.
      constructor.
    - invert H.
      constructor.
    - invert H.
      invert H2.
      assumption.
    - invert H.
      invert H2.
      assumption.
  Qed.

  (* PROBLEM 11 [4 points, ~15 tactics]
   * Extend the proof of `generalize_plug` to handle the new language constructs.
   *
   * Hint: It will help to step through a few of the existing cases in the proof
   * to see how they usually work.
   *)
  Lemma generalize_plug : forall e1 C e1',
    plug C e1 e1'
    -> forall e2 e2', plug C e2 e2'
      -> (forall t, hasty $0 e1 t -> hasty $0 e2 t)
      -> (forall t, hasty $0 e1' t -> hasty $0 e2' t).
  Proof.
    induct 1; simplify.
    - invert H.
      apply H0.
      assumption.
    - invert H0.
      invert H2.
      constructor.
      + eapply IHplug.
        * eassumption.
        * assumption.
        * assumption.
      + assumption.
    - invert H1.
      invert H3.
      constructor.
      + assumption.
      + eapply IHplug.
        * eassumption.
        * assumption.
        * assumption.
    - invert H0.
      invert H2.
      constructor.
      + eapply IHplug.
        * eassumption.
        * assumption.
        * assumption.
      + assumption.
    - invert H1.
      invert H3.
      constructor.
      + assumption.
      + eapply IHplug.
        * eassumption.
        * assumption.
        * assumption.
    - invert H0.
      invert H2.
      econstructor.
      + eapply IHplug.
        * eassumption.
        * assumption.
        * eassumption.
      + assumption.
    - invert H1.
      invert H3.
      econstructor.
      + eassumption.
      + eapply IHplug.
        * eassumption.
        * assumption.
        * eassumption.
    - invert H0.
      invert H2.
      econstructor.
      + eapply IHplug.
        * eassumption.
        * assumption.
        * eassumption.
      + assumption.
    - invert H1.
      invert H3.
      econstructor.
      + eassumption.
      + eapply IHplug.
        * eassumption.
        * assumption.
        * eassumption.
    - invert H0.
      invert H2.
      econstructor.
      + eapply IHplug.
        * eassumption.
        * assumption.
        * eassumption.
    - invert H0.
      invert H2.
      econstructor.
      + eapply IHplug.
        * eassumption.
        * assumption.
        * eassumption.
  Qed.

  (* This proof should go through without modifications. *)
  Lemma preservation : forall e1 e2,
    step e1 e2
    -> forall t, hasty $0 e1 t
      -> hasty $0 e2 t.
  Proof.
    invert 1; simplify.

    eapply generalize_plug with (e1' := e1).
    - eassumption.
    - eassumption.
    - simplify.
      eapply preservation0.
      + eassumption.
      + assumption.
    - assumption.
  Qed.

  (* This proof should go through without modifications. *)
  Theorem safety : forall e t, hasty $0 e t
    -> invariantFor (trsys_of e) unstuck.
  Proof.
    simplify.
    apply invariant_weaken with (invariant1 := fun e' => hasty $0 e' t).
    - apply invariant_induction; simplify.
      + equality.

      + eapply preservation.
        * eassumption.
        * assumption.
    - simplify.
      eapply progress.
      eassumption.
  Qed.
End StlcWithPairs.


(* This language doesn't have any support for recursion, and, unlike in the
 * untyped lambda calculus, we can't use the Y combinator to get recursion for
 * free. In fact, one can prove (using methods beyond the scope of this course)
 * that all well typed programs in STLC or STLC-with-pairs terminate. Since there
 * are programs that use general recursion or the Y combinator to loop for ever,
 * we know no such thing can be expressed in these languages.
 *)

(* PROBLEM 12 [4 points, ~1 sentences]
 * Is there a program in STLC (or STLC-with-pairs) of type Nat --> Nat that
 * implements the factorial function? If so, write it down. If not, why not?
 * Either way, your answer can be informal.
 *
 * Hint: Notice that the factorial function always terminates. So it would not
 * be correct to say "there is no such program because all programs in STLC
 * terminate but factorial doesn't".
 *)

(* No, because the type system could not infer a type on a recursive function.
   Factorial has a "base case" that leads to termination, but the type system
   cannot perceive this. *)

(* In any case, in order to get full-blown recursion (and potential nontermination)
 * we can add a new feature to the language. *)

(* --- SECTION 2: Adding recursion to STLC via `fix`  --- *)

Module StlcWithFix.
  Inductive exp : Set :=
  | Var (x : var)
  | Const (n : nat)
  | Plus (e1 e2 : exp)
  | Mult (e1 e2 : exp)
  | Abs (x : var) (e1 : exp)
  | App (e1 e2 : exp)

  (* Here we add syntax for recursion. The program `Fix e` evaluates
   * e to a function and then calls that function with the argument `Fix e`. q*)
  | Fix (e : exp)

  (* Let's also add a few other features so that we can write some more interesting programs. *)
  | IfZero (e1 e2 e3 : exp)  (* if e1 evaluates to 0, then evaluate e2, else evaluate e3 *)
  | Minus (e1 e2 : exp)
  .

  Inductive value : exp -> Prop :=
  | VConst : forall n, value (Const n)
  | VAbs : forall x e1, value (Abs x e1).

  (* PROBLEM 13 [4 points, ~2 LOC]
   * Extend the definition of substitution to handle the new language features.
   *
   * We've given you the case for Fix.
   *
   * Hint: You'll need one new case per new constructor of `exp` besides `Fix`.
   *
   * Hint: You'll know you got this right if you can prove the Lemma `substitution` below.
   *)
  Fixpoint subst (e1 : exp) (x : string) (e2 : exp) : exp :=
    match e2 with
      | Var y => if y ==v x then e1 else Var y
      | Const n => Const n
      | Plus e2' e2'' => Plus (subst e1 x e2') (subst e1 x e2'')
      | Mult e2' e2'' => Mult (subst e1 x e2') (subst e1 x e2'')
      | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
      | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')

      (* there's nothing special about substituting into a Fix *)
      | Fix e2' => Fix (subst e1 x e2')

      (* YOUR CODE HERE *)
      | IfZero e2' e2'' e2''' => IfZero (subst e1 x e2') (subst e1 x e2'') (subst e1 x e2''')
      | Minus e2' e2'' => Minus (subst e1 x e2') (subst e1 x e2'')
    end.

  Inductive context : Set :=
  | Hole : context
  | Plus1 : context -> exp -> context
  | Plus2 : exp -> context -> context
  | Mult1 : context -> exp -> context
  | Mult2 : exp -> context -> context
  | App1 : context -> exp -> context
  | App2 : exp -> context -> context

  (* We extend the definition of evaluation contexts to include evaluating under `fix`. *)
  | CFix : context -> context
  | CIfZero : context -> exp -> exp -> context
  | Minus1 : context -> exp -> context
  | Minus2 : exp -> context -> context
  .

  Inductive plug : context -> exp -> exp -> Prop :=
  | PlugHole : forall e, plug Hole e e
  | PlugPlus1 : forall e e' C e2,
    plug C e e'
    -> plug (Plus1 C e2) e (Plus e' e2)
  | PlugPlus2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (Plus2 v1 C) e (Plus v1 e')
  | PlugMult1 : forall e e' C e2,
    plug C e e'
    -> plug (Mult1 C e2) e (Mult e' e2)
  | PlugMult2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (Mult2 v1 C) e (Mult v1 e')
  | PlugApp1 : forall e e' C e2,
    plug C e e'
    -> plug (App1 C e2) e (App e' e2)
  | PlugApp2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (App2 v1 C) e (App v1 e')

  (* There's nothing special about plugging into a Fix. *)
  | PlugFix : forall e e' C,
      plug C e e' ->
      plug (CFix C) e (Fix e')

  (* PROBLEM 14 [4 points, ~10 LOC]
   * Extend the definition of `plug` to handle the new language features.
   *
   * We've added the constructor for Fix above. You just need to handle the other features.
   *
   * Hint: You'll need one new constructor corresponding to IfZero, and two for Minus.
   *
   * Hint: You'll know you got this right if you can prove the Lemma `generalize_plug` below.
   *)
  | PlugIfZero : forall C e e' e2 e3,
    plug C e e'
    -> plug (CIfZero C e2 e3) e (IfZero e' e2 e3)
  | PlugMinus1 : forall e e' C e2,
    plug C e e'
    -> plug (Minus1 C e2) e (Minus e' e2)
  | PlugMinus2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (Minus2 v1 C) e (Minus v1 e').

  Inductive step0 : exp -> exp -> Prop :=
  | Beta : forall x e v,
    value v
    -> step0 (App (Abs x e) v) (subst v x e)
  | Add : forall n1 n2,
    step0 (Plus (Const n1) (Const n2)) (Const (n1 + n2))
  | Multiply : forall n1 n2,
      step0 (Mult (Const n1) (Const n2)) (Const (n1 * n2))

  (* Here's how we evaluate fix: substitute it in itself! :mindblown: *)
  | FixUnroll : forall x e,
      step0 (Fix (Abs x e)) (subst (Fix (Abs x e)) x e)

  (* And here's how we evaluate IfZero. *)
  | IfZeroZero : forall e2 e3,
      step0 (IfZero (Const 0) e2 e3) e2
  | IfZeroNonZero : forall n e2 e3,
      step0 (IfZero (Const (S n)) e2 e3) e3

  (* PROBLEM 15 [4 points, ~2 LOC]
   * Extend the definition of `step0` to handle Minus.
   *
   * Hint: It's like the rule for Plus, but it subtracts instead of adds.
   *)
  | Subtract : forall n1 n2,
    step0 (Minus (Const n1) (Const n2)) (Const (n1 - n2)).

  Inductive step : exp -> exp -> Prop :=
  | StepRule : forall C e1 e2 e1' e2',
    plug C e1 e1'
    -> plug C e2 e2'
    -> step0 e1 e2
    -> step e1' e2'.

  Definition trsys_of (e : exp) := {|
    Initial := {e};
    Step := step
  |}.


  Inductive type :=
  | Nat                  (* Numbers *)
  | Fun (dom ran : type) (* Functions *).

  Inductive hasty : fmap var type -> exp -> type -> Prop :=
  | HtVar : forall G x t,
    G $? x = Some t
    -> hasty G (Var x) t
  | HtConst : forall G n,
    hasty G (Const n) Nat
  | HtPlus : forall G e1 e2,
    hasty G e1 Nat
    -> hasty G e2 Nat
    -> hasty G (Plus e1 e2) Nat
  | HtMult : forall G e1 e2,
    hasty G e1 Nat
    -> hasty G e2 Nat
    -> hasty G (Mult e1 e2) Nat

  | HtAbs : forall G x e1 t1 t2,
    hasty (G $+ (x, t1)) e1 t2
    -> hasty G (Abs x e1) (Fun t1 t2)
  | HtApp : forall G e1 e2 t1 t2,
    hasty G e1 (Fun t1 t2)
    -> hasty G e2 t1
    -> hasty G (App e1 e2) t2

  (* PROBLEM 16 [4 points, ~3 LOC]
   * Extend the definition of `hasty` to handle fix.
   *
   * Hint: You'll need one new constructor for fix.
   *
   * Hint: Translate the following typing rule into code:
   *
   *            G |- e : t -> t
   *         ---------------------
   *            G |- fix e : t
   *
   * In other words, if e is a function from t to t, then fix e has type t.
   *)
  | HtFix : forall G e t,
    hasty G e (Fun t t)
    -> hasty G (Fix e) t


  (* PROBLEM 17 [4 points, ~10 LOC]
   * Extend the definition of `hasty` to handle IfZero and Minus.
   *
   * Hint: You'll need one new constructor for IfZero and one for Minus.
   *
   * Hint: For IfZero, translate the following typing rule into code:
   *
   *            G |- e1 : Nat       G |- e2 : t        G |- e3 : t
   *     ---------------------------------------------------------------
   *                          G |- IfZero e1 e2 e3 : t
   *
   * Hint: Minus is similar to Plus.
   *)
  | HtIfZero : forall G e1 e2 e3 t,
    hasty G e1 Nat
    -> hasty G e2 t
    -> hasty G e3 t
    -> hasty G (IfZero e1 e2 e3) t
  | HtMinus : forall G e1 e2,
    hasty G e1 Nat
    -> hasty G e2 Nat
    -> hasty G (Minus e1 e2) Nat.


  Hint Constructors value plug step0 step hasty.

  Infix "-->" := Fun (at level 60, right associativity).
  Coercion Const : nat >-> exp.
  Infix "^+^" := Plus (at level 50).
  Infix "^*^" := Mult (at level 50).
  Infix "^-^" := Minus (at level 50).
  Coercion Var : var >-> exp.
  Notation "\ x , e" := (Abs x e) (at level 51).
  Infix "@" := App (at level 49, left associativity).

  Example one_plus_one : hasty $0 (1 ^+^ 1) Nat.
  Proof.
    repeat (econstructor; simplify).
  Qed.

  Example add : hasty $0 (\"n", \"m", "n" ^+^ "m") (Nat --> Nat --> Nat).
  Proof.
    repeat (econstructor; simplify).
  Qed.

  Example eleven : hasty $0 ((\"n", \"m", "n" ^+^ "m") @ 7 @ 4) Nat.
  Proof.
    repeat (econstructor; simplify).
  Qed.

  Example seven_the_long_way : hasty $0 ((\"x", "x") @ (\"x", "x") @ 7) Nat.
  Proof.
    repeat (econstructor; simplify).
  Qed.

  (* Here's a program that uses all the new features we added to implement factorial. *)
  Definition factorial_exp : exp :=
    Fix (\"rec", (\"n", IfZero "n" 1 ("n" ^*^ ("rec" @ ("n" ^-^ 1))))).

  (* PROBLEM 18 [4 points, ~3 tactics]
   * Prove that the following expression has the given type.
   *
   * Hint: If your definitions are right, the same proof as the examples just above here should work.
   *)
  Example factorial_ht :
    hasty $0 factorial_exp (Nat --> Nat).
  Proof.
    repeat (econstructor; simplify).
  Qed.

  (* Here's a proof that the above factorial expression applied to 5 evaluates to 120. *)
  Example factorial_of_5 :
    trc step (factorial_exp @ 5) 120.
  Proof.
    (* Uncomment this proof once you've added constructors to step0 for Minus. *)
    unfold factorial_exp.
    repeat (econstructor; [now eauto 20|simplify]).
    apply TrcRefl.
  Qed.

  (* PROBLEM 19 [4 points, ~2 LOC]
   * Implement an expression `fib` that returns the nth Fibonacci number.
   *)
  Definition fib_exp : exp :=
    Fix
      (\"rec",
        (\"n",
          IfZero
            "n"
            1
            (IfZero
              ("n" ^-^ 1)
              1
              (("rec" @ ("n" ^-^ 1)) ^+^ ("rec" @ ("n" ^-^ 2)))
        ))).

  (* PROBLEM 20 [4 points, ~3 tactics]
   * Prove that your definition of fib is well typed.
   *
   * Hint: If your definitions are right, the same proof as the examples just above here should work.
   *)
  Example fib_ht :
    hasty $0 fib_exp (Nat --> Nat).
  Proof.
    repeat (econstructor; simplify).
  Qed.

  (* PROBLEM 21 [4 points, ~5 tactics]
   * Prove that your definition of fib correctly computes that the 5th fibonacci
   * number is 5. (We pass 4 as the argument because the argument is 0-indexed.)
   *
   * Hint: If your definitions are right, the same proof as factorial_of_5 should work.
   *)
  Example fib_of_4 :
    trc step (fib_exp @ 4) 5.
  Proof.
    unfold fib_exp.
    repeat (econstructor; [now eauto 20|simplify]).
    apply TrcRefl.
  Qed.

  Definition unstuck e := value e
    \/ (exists e' : exp, step e e').

  (* PROBLEM 22 [4 points, ~35 tactics]
   * Extend the proof of `progress` to handle the new language constructs.
   *
   * Hint: It will help to step through a few of the existing cases in the proof
   * to see how they usually work.
   *)
  Lemma progress : forall e t,
    hasty $0 e t
    -> unstuck e.
  Proof.
    unfold unstuck; induct 1; simplify; try equality.
    - left.
      constructor.
    - propositional.
      + right.
        match goal with
        | [ H1 : value e1, H2 : hasty $0 e1 _ |- _ ] => invert H1; invert H2
        end.
        match goal with
        | [ H1 : value e2, H2 : hasty $0 e2 _ |- _ ] => invert H1; invert H2
        end.
        exists (Const (n + n0)).
        eapply StepRule with (C := Hole).
        eauto.
        eauto.
        constructor.
      + match goal with
        | [ H : exists x, _ |- _ ] => invert H
        end.
        match goal with
        | [ H : step _ _ |- _ ] => invert H
        end.
        right.
        eauto.
      + match goal with
        | [ H : exists x, _ |- _ ] => invert H
        end.
        match goal with
        | [ H : step _ _ |- _ ] => invert H
        end.
        right.
        eauto.
      + match goal with
        | [ H : exists x, step e1 _ |- _ ] => invert H
        end.
        match goal with
        | [ H : step _ _ |- _ ] => invert H
        end.
        right.
        exists (Plus x e2).
        eapply StepRule with (C := Plus1 C e2).
        eauto.
        eauto.
        assumption.
    - propositional.
      + right.
        match goal with
        | [ H1 : value e1, H2 : hasty $0 e1 _ |- _ ] => invert H1; invert H2
        end.
        match goal with
        | [ H1 : value e2, H2 : hasty $0 e2 _ |- _ ] => invert H1; invert H2
        end.
        exists (Const (n * n0)).
        eapply StepRule with (C := Hole).
        eauto.
        eauto.
        constructor.
      + match goal with
        | [ H : exists x, _ |- _ ] => invert H
        end.
        match goal with
        | [ H : step _ _ |- _ ] => invert H
        end.
        right.
        eauto.
      + match goal with
        | [ H : exists x, _ |- _ ] => invert H
        end.
        match goal with
        | [ H : step _ _ |- _ ] => invert H
        end.
        right.
        eauto.
      + match goal with
        | [ H : exists x, step e1 _ |- _ ] => invert H
        end.
        match goal with
        | [ H : step _ _ |- _ ] => invert H
        end.
        right.
        exists (Mult x e2).
        eapply StepRule with (C := Mult1 C e2).
        eauto.
        eauto.
        assumption.
    - left.
      constructor.
    - propositional.
      + right.
        match goal with
        | [ H1 : value e1, H2 : hasty $0 e1 _ |- _ ] => invert H1; invert H2
        end.
        exists (subst e2 x e0).
        eapply StepRule with (C := Hole).
        eauto.
        eauto.
        constructor.
        assumption.
      + match goal with
        | [ H : exists x, _ |- _ ] => invert H
        end.
        match goal with
        | [ H : step _ _ |- _ ] => invert H
        end.
        right.
        eauto.
      + match goal with
        | [ H : exists x, _ |- _ ] => invert H
        end.
        match goal with
        | [ H : step _ _ |- _ ] => invert H
        end.
        right.
        eauto.
      + match goal with
        | [ H : exists x, step e1 _ |- _ ] => invert H
        end.
        match goal with
        | [ H : step _ _ |- _ ] => invert H
        end.
        right.
        exists (App x e2).
        eapply StepRule with (C := App1 C e2).
        eauto.
        eauto.
        assumption.
    (* YOUR CODE HERE *)
  Admitted. (* Change to Qed when done *)

  Lemma weakening_override : forall (G G' : fmap var type) x t,
    (forall x' t', G $? x' = Some t' -> G' $? x' = Some t')
    -> (forall x' t', G $+ (x, t) $? x' = Some t'
                      -> G' $+ (x, t) $? x' = Some t').
  Proof.
    simplify.
    cases (x ==v x'); simplify; eauto.
  Qed.

  (* PROBLEM 23 [4 points, ~4 tactics]
   * Extend the proof of `weakening` to handle the new language constructs.
   *
   * Hint: It will help to step through a few of the existing cases in the proof
   * to see how they usually work.
   *)
  Lemma weakening : forall G e t,
    hasty G e t
    -> forall G', (forall x t, G $? x = Some t -> G' $? x = Some t)
      -> hasty G' e t.
  Proof.
    induct 1; simplify.
    - constructor.
      apply H0.
      assumption.
    - constructor.
    - constructor.
      apply IHhasty1.
      assumption.
      apply IHhasty2.
      assumption.
    - constructor.
      apply IHhasty1.
      assumption.
      apply IHhasty2.
      assumption.
    - constructor.
      apply IHhasty.
      apply weakening_override.
      assumption.
    - econstructor.
      apply IHhasty1.
      assumption.
      apply IHhasty2.
      assumption.
    (* YOUR CODE HERE *)
  Admitted. (* Change to Qed when done *)

  (* PROBLEM 24 [4 points, ~4 tactics]
   * Extend the proof of `substitution` to handle the new language constructs.
   *
   * Hint: It will help to step through a few of the existing cases in the proof
   * to see how they usually work.
   *)
  Lemma substitution : forall G x t' e t e',
    hasty (G $+ (x, t')) e t
    -> hasty $0 e' t'
    -> hasty G (subst e' x e) t.
  Proof.
    induct 1; simplify.
    - cases (x0 ==v x).
      + simplify.
        invert H.
        eapply weakening.
        eassumption.
        simplify.
        equality.
      + simplify.
        constructor.
        assumption.
    - constructor.
    - constructor.
      eapply IHhasty1; equality.
      eapply IHhasty2; equality.
    - constructor.
      eapply IHhasty1; equality.
      eapply IHhasty2; equality.
    - cases (x0 ==v x).
      + constructor.
        eapply weakening.
        eassumption.
        simplify.
        cases (x0 ==v x1).
        * simplify.
          assumption.
        * simplify.
          assumption.
      + constructor.
        eapply IHhasty.
        maps_equal.
        assumption.
    - econstructor.
      eapply IHhasty1; equality.
      eapply IHhasty2; equality.
    (* YOUR CODE HERE *)
  Admitted. (* Change to Qed when done *)

  (* PROBLEM 25 [4 points, ~15 tactics]
   * Extend the proof of `preservation0` to handle the new language constructs.
   *
   * Hint: It will help to step through a few of the existing cases in the proof
   * to see how they usually work.
   *)
  Lemma preservation0 : forall e1 e2,
    step0 e1 e2
    -> forall t, hasty $0 e1 t
      -> hasty $0 e2 t.
  Proof.
    invert 1; simplify.

    - invert H.
      invert H4.
      eapply substitution.
      + eassumption.
      + assumption.
    - invert H.
      constructor.
    - invert H.
      constructor.
    (* YOUR CODE HERE *)
  Admitted. (* Change to Qed when done *)

  (* PROBLEM 26 [4 points, ~15 tactics]
   * Extend the proof of `generalize_plug` to handle the new language constructs.
   *
   * Hint: It will help to step through a few of the existing cases in the proof
   * to see how they usually work.
   *)
  Lemma generalize_plug : forall e1 C e1',
    plug C e1 e1'
    -> forall e2 e2', plug C e2 e2'
      -> (forall t, hasty $0 e1 t -> hasty $0 e2 t)
      -> (forall t, hasty $0 e1' t -> hasty $0 e2' t).
  Proof.
    induct 1; simplify.
    - invert H.
      apply H0.
      assumption.
    - invert H0.
      invert H2.
      constructor.
      + eapply IHplug.
        * eassumption.
        * assumption.
        * assumption.
      + assumption.
    - invert H1.
      invert H3.
      constructor.
      + assumption.
      + eapply IHplug.
        * eassumption.
        * assumption.
        * assumption.
    - invert H0.
      invert H2.
      constructor.
      + eapply IHplug.
        * eassumption.
        * assumption.
        * assumption.
      + assumption.
    - invert H1.
      invert H3.
      constructor.
      + assumption.
      + eapply IHplug.
        * eassumption.
        * assumption.
        * assumption.
    - invert H0.
      invert H2.
      econstructor.
      + eapply IHplug.
        * eassumption.
        * assumption.
        * eassumption.
      + assumption.
    - invert H1.
      invert H3.
      econstructor.
      + eassumption.
      + eapply IHplug.
        * eassumption.
        * assumption.
        * eassumption.
    (* YOUR CODE HERE *)
  Admitted. (* Change to Qed when done *)

  (* This proof should go through without modifications. *)
  Lemma preservation : forall e1 e2,
    step e1 e2
    -> forall t, hasty $0 e1 t
      -> hasty $0 e2 t.
  Proof.
    invert 1; simplify.

    eapply generalize_plug with (e1' := e1).
    - eassumption.
    - eassumption.
    - simplify.
      eapply preservation0.
      + eassumption.
      + assumption.
    - assumption.
  Qed.

  (* This proof should go through without modifications. *)
  Theorem safety : forall e t, hasty $0 e t
    -> invariantFor (trsys_of e) unstuck.
  Proof.
    simplify.
    apply invariant_weaken with (invariant1 := fun e' => hasty $0 e' t).
    - apply invariant_induction; simplify.
      + equality.

      + eapply preservation.
        * eassumption.
        * assumption.
    - simplify.
      eapply progress.
      eassumption.
  Qed.
End StlcWithFix.
