(* -------------------------------------- Homework 3 --------------------------------------
 *
 *)

Require Import Frap.

(* --- SECTION 1: An alternate defenition of trc --- *)

(* Consider the following alternative definition of trc. *)

Inductive different_trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| DiffTrcRefl : forall x, different_trc R x x
| DiffTrcBack : forall x y z,
    different_trc R x y ->
    R y z ->
    different_trc R x z.

(* PROBLEM 1 [5 points, ~2 sentences]
 * Describe what's different between `trc` and `different_trc`.  Then explain briefly
 * and intuitively why they are equivalent.
 *
 * Hint: To have a coherent answer, you'll probably need to look at the definition of
 * `trc` again.
 *
 * Hint: The names of the constructors are useful to think about.
 *)
(* trc's TrcFront differs from different_trc's DiffTrcBack.  TrcFront states
   that if x can *step to* y, and if y can *reach* z, then x can reach z.
   DiffTrcBack flips this -- it states that if x can *reach* y, and y can
   *reach* z, then x can reach z.

   These are the same; they just reverse the order of induction.  TrcFront has
   one induct *forwards* from x, toward z.  DiffTrcBack has one induct *backwards*
   from z, toward x. *)


(* Now we have an intuitive understanding of why `trc` and `different_trc` are
 * equivalent. Let's prove it!
 *)

(* PROBLEM 2 [5 points, ~10 tactics]
 * Prove the first half of the equivalence, that `different_trc` implies `trc`.
 *
 * Hint: Proceed by induction on the evidence of `different_trc`.
 *
 * Hint: Remember the rules of thumb for working with inductive predicates.
 * In the goal, you might find `constructor` or `econstructor` useful,
 * or you can use `apply`/`eapply` with the name of the constructor.
 *
 * Hint: You might find the lemma `trc_trans` useful with `eapply`.
 *)
Lemma R_x_y_implies_trc_R_x_y :
  forall A (R : A -> A -> Prop) x y,
    R x y -> trc R x y.
Proof.
  intros.
  assert (trc R y y).
  - apply TrcRefl.
  - eapply TrcFront.
    + apply H.
    + apply TrcRefl.
Qed.

Theorem different_trc_implies_trc :
  forall A (R : A -> A -> Prop) x y,
    different_trc R x y ->
    trc R x y.
Proof.
  induct 1.
  + apply TrcRefl.
  + eapply trc_trans.
    - apply IHdifferent_trc.
    - apply R_x_y_implies_trc_R_x_y.
      assumption.
Qed.

(* PROBLEM 3 [5 points, ~20 tactics]
 * Now prove the second half of the equivalence, that `trc` implies `different_trc`.
 *
 * Hint: Proceed by induction on the evidence of `trc`.
 *
 * Hint: `trc_trans` was useful in the previous problem. You might consider proving
 * an analogous helper lemma for `different_trc`. Be *extremely* careful stating this
 * lemma deciding how to prove it, since there are lots of pitfalls.
 *
 * Hint: There's more than one way to do it, so feel free to explore approaches that
 * are not analogous to your proof of the previous problem.
 *
 * Hint: Ask for help if you're stuck!!
 *)

Theorem different_trc_trans :
  forall {A} (R : A -> A -> Prop) y z,
    different_trc R y z ->
      forall x,
        different_trc R x y ->
          different_trc R x z.
Proof.
  induct 1.
  - intros. assumption.
  - intros. eapply DiffTrcBack.
    + apply IHdifferent_trc.
      assumption.
    + assumption.
Qed.

Lemma R_x_y_implies_different_trc_R_x_y :
  forall A (R : A -> A -> Prop) x y,
    R x y -> different_trc R x y.
Proof.
  intros.
  assert (different_trc R y y).
  - apply DiffTrcRefl.
  - eapply DiffTrcBack.
    + apply DiffTrcRefl.
    + apply H.
Qed.

Theorem trc_implies_different_trc_implies :
  forall A (R : A -> A -> Prop) x y,
    trc R x y ->
    different_trc R x y.
Proof.
  induct 1.
  + apply DiffTrcRefl.
  + eapply different_trc_trans.
    - apply IHtrc.
    - apply R_x_y_implies_different_trc_R_x_y.
      assumption.
Qed.


(* --- SECTION 2: Inductive predicates for "and" and "or" --- *)

(* Very very few things are "built in" to Coq. We have already seen that numbers and booleans
 * are not built in, but defined in the standard library as inductive types. In fact, even
 * basic logical connectives such as "and" and "or" are not built in, but are also defined
 * in the standard library as inductive predicates. Let's explore these definitions a bit.
 *)

(* Here is an inductive definition of "and" (called `my_and` just so it doesn't conflict
 * with the definition of `and` from the standard library).
 *)
Inductive my_and (A B : Prop) : Prop :=
| MakeAnd : A -> B -> my_and A B.

(* And here's a simple proof about `my_and`, which says "if you give me evidence of
 * `my_and A B`, I can give you evidence of A".
 *)
Lemma my_and_project1 :
  forall A B : Prop,
    my_and A B ->
    A.
Proof.
  simplify.

  (* rule of thumb: (non-recursive) inductively defined predicate above the line, use `invert` *)
  invert H.

  (* now we have a hypothesis showing `A`! *)
  assumption.
Qed.

(* PROBLEM 4 [5 points, ~2 sentences]
 * Using your mental model for what `invert` does, explain why `invert H` adds two hypotheses,
 * one for `A` and one for `B`.
 *)
(* `invert` determines what facts are implied (in the logical sense of implication)
   by a hypothesis, and adds them as hypotheses.  In this case, my_and A B is implied
   by A and B, so `invert` deduces that they must be true as well. *)

(* PROBLEM 5 [2 points, ~4 tactics]
 * Prove the analogous property about `my_and` and its second argument.
 *
 * Hint: Similar to above. It's supposed to be easy :)
 *)
Lemma my_and_project2 :
  forall A B : Prop,
    my_and A B ->
    B.
Proof.
  simplify.
  invert H.
  assumption.
Qed.


(* PROBLEM 6 [3 points, ~6 tactics]
 * Prove that you can swap arguments to `my_and`.
 *
 * Hint: You'll need to use the rules of thumb for inductive predicates above the line
 * (like the previous problem) *and* below the line (described in the hints to
 * problem `different_trc_implies_trc`).
 *)
Lemma my_and_swap :
  forall A B : Prop,
    my_and A B ->
    my_and B A.
Proof.
  intros.
  invert H.
  constructor.
  - assumption.
  - assumption.
Qed.

(* Here's a defenition of "or". *)
Inductive my_or (A B : Prop) : Prop :=
| OrFirst : A -> my_or A B
| OrSecond : B -> my_or A B.

(* PROBLEM 7 [5 points, ~3 sentences]
 * Explain why the proof we used for `my_and_project1` doesn't work for `my_or`.
 *
 * Structure your explanation in two parts: (1) a low-level explanation of why `invert`
 * behaves differently with `my_or` compared to `my_and`; (2) a high-level explanation
 * of why the lemma statement of `my_or_project1` is just not provable.
 *
 * Hint: Start by trying to use the same proof from `my_and_project1` and see where
 * you get stuck. Then base your low-level explanation on that experience.
 *)
Lemma my_or_project1 :
  forall A B : Prop,
    my_or A B ->
    A.
Proof.
  simplify.
  invert H.
  + assumption.
  + 
Abort.
(* my_or has two constructors, unlike my_and.  We know by hypothesis that my_or A B
   is true, but we don't know which constructor was used to prove it.  `invert`
   therefore requires that we prove that A follows *regardless* of which constructor
   was used.  And that cannot be proven for OrSecond.

   At a higher level, that this cannot be proven is obvious.  We are asked to prove
   that if (A || B) is true, A must be true.  Manifestly, though, (A || B) can be
   true when A is false and B is true, a counterexample. *)


(* PROBLEM 8 [2 points, ~7 tactics]
 * Prove that you can swap arguments to `my_or`.
 *
 * Hint: Use your rules of thumb.
 *)
Lemma my_or_swap :
  forall A B : Prop,
    my_or A B ->
    my_or B A.
Proof.
  intros.
  invert H.
  + apply OrSecond. assumption.
  + apply OrFirst. assumption.
Qed.

(* PROBLEM 9 [3 points, ~15 tactics]
 * Prove the following relationship between `my_and` and `my_or`.
 *
 * Hint: Use your rules of thumb.
 *)
Lemma and_or_distr :
  forall A B C : Prop,
    my_and A (my_or B C) ->
    my_or (my_and A B) (my_and A C).
Proof.
  intros.
  invert H.
  invert H1.
  - apply OrFirst. constructor.
    + assumption.
    + assumption.
  - apply OrSecond. constructor.
    + assumption.
    + assumption.
Qed.


(* --- SECTION 3: Transition systems and inductive invariants --- *)

(* In lecture 5 we looked at some transition systems that incremented numbers.
 * In the next two sections, we'll look at a transition the decrements two numbers.
 *
 * Consider the following pseudocode:
 *
 *     // initially x can be any non-negative number
 *     y = 42
 *     done = false
 *     while x > 0:
 *         x = x - 1
 *     while y > 0:
 *         y = y - 1
 *     done = true
 *     assert x == 0
 *
 * After initializing y and done, it decrements x until x is 0. Then, it decrements y
 * until it's 0. We'd like to prove that the assert at the end is always true.
 *
 * Let's encode this as a transition system. We need to define the state, initial predicate,
 * and step relation.
 *)

(* Our state will consist of the values of the three variables x, y, and done. *)
Record decr_state : Type := {
  var_x : nat;
  var_y : nat;
  var_done: bool
}.

(* Initially, x is arbitrary, y is 42, and done is false. *)
Inductive decr_init : decr_state -> Prop :=
| DecrInit :  forall nx, decr_init {| var_x := nx; var_y := 42; var_done := false |}.

(* PROBLEM 10 [3 points, ~4 LOC]
 * Give an alternate definition of decr_init using Definition instead of Inductive.
 *)
Definition decr_init_alternative (s : decr_state) : Prop :=
  exists nx,
    s = {| var_x := nx; var_y := 42; var_done := false |}.

(* PROBLEM 11 [5 points, ~10 tactics]
 * Prove your alternative definition equivalent to the original.
 *)
Lemma decr_init_alternative_ok :
  forall s,
    decr_init_alternative s <-> decr_init s.
Proof.
  intros.
  unfold decr_init_alternative.
  constructor.
  + propositional.
    invert H.
    constructor.
  + propositional.
    invert H.
    eexists.
    equality.
Qed.

(* Ok, back to encoding that program as a transition system. We're ready for the step relation.
 * There are three steps:
 *   - if x is not yet 0, we can decrement it
 *   - if x is 0, but y isn't, we can decrement y, leaving x alone
 *   - if y is 0, we set done to true
 * This is encoded with the following inductive definition.
 *)
Inductive decr_step : decr_state -> decr_state -> Prop :=
| decr_x : forall n_x n_y, decr_step {| var_x := S n_x; var_y := n_y; var_done := false |}
                                {| var_x := n_x; var_y := n_y; var_done := false|}
| decr_y : forall n_y, decr_step {| var_x := 0; var_y := S n_y; var_done := false |}
                            {| var_x := 0; var_y := n_y; var_done := false|}
| decr_var_done : forall n_x, decr_step {| var_x := n_x; var_y := 0; var_done := false |}
                                   {| var_x := n_x; var_y := 0; var_done := true |}.

(* Packaging things up into a transition system . *)
Definition decr_sys : trsys decr_state := {|
  Initial := decr_init;
  Step := decr_step
|}.

(* The safety property we want to prove is that when done is true, x is 0. *)
Definition decr_safe (s : decr_state) : Prop :=
  match s with
  | {| var_x := nx; var_y := ny; var_done := true |} => nx = 0
  | _ => True
  end.

(* PROBLEM 12 [15 points, ~30 tactics total, including 1 helper lemma]
 * Prove this transition system safe.
 *
 * Hint: First try to proceed directly by induction (using `apply invariant_induction`).
 * Think about how you get stuck in the inductive case.
 *
 * Hint: State your strengthened invariant and prove it as a helper lemma by induction.
 * Then use `invariant_weaken` to show decr_safe is also an invariant.
 *
 * Hint: As always, finding the right strengthened invariant is the hard part. It took
 * me a couple tries to get it right. Ask for help if you're stuck!
 *)
Definition decr_safe_strong (s : decr_state) : Prop :=
  match s with
  | {| var_x := nx; var_y := 0; var_done := _|} => nx = 0
  | {| var_x := nx; var_y := S _; var_done := true|} => False
  | _ => True
  end.

Theorem decr_ok_strong :
  invariantFor decr_sys decr_safe_strong.
Proof.
  apply invariant_induction.
  + intros. invert H. unfold decr_safe_strong. trivial.
  + intros. invert H0.
    - unfold decr_safe_strong. cases n_y.
      * invert H.
      * trivial.
    - unfold decr_safe_strong. cases n_y.
      * equality.
      * trivial.
    - unfold decr_safe_strong. invert H. trivial.
Qed.

Theorem decr_ok :
  invariantFor decr_sys decr_safe.
Proof.
  apply invariant_weaken with (invariant1 := decr_safe_strong).
  + apply decr_ok_strong.
  + intros.
    unfold decr_safe.
    unfold decr_safe_strong in H.
    cases s.
    cases var_done0.
    - cases var_y0.
      * assumption.
      * equality.
    - trivial.
Qed.


(* --- SECTION 4: Abstraction and model checking --- *)

(* Let' prove this invariant a different way, by using abstraction and model checking
 * to avoid having to come up with the strengthening ourselves.
 *
 * Notice that the system only really distinguishes zero and nonzero numbers. We can
 * use that to build a boolean abstraction of x and y, that just remembers whether they
 * are 0 or not.
 *
 * Here's the definition of an abstract transition system.
 *)

Record decr_bool_state : Type := {
  var_x_bool : bool;
  var_y_bool : bool;
  var_done_bool : bool
}.

(* There are now five steps, since when decrementing a variable, we distinguish between
 * whether the new value is zero or nonzero, so we get two steps for each decrement step
 * in the original system.
 *)
Inductive decr_bool_step : decr_bool_state -> decr_bool_state -> Prop :=
| decr_bool_x_more : forall b_y, decr_bool_step
                              {| var_x_bool := false; var_y_bool := b_y; var_done_bool := false |}
                              {| var_x_bool := false; var_y_bool := b_y; var_done_bool := false|}
| decr_bool_x_done : forall b_y, decr_bool_step
                              {| var_x_bool := false; var_y_bool := b_y; var_done_bool := false |}
                              {| var_x_bool := true; var_y_bool := b_y; var_done_bool := false|}
| decr_bool_y_more : decr_bool_step
                       {| var_x_bool := true; var_y_bool := false; var_done_bool := false |}
                       {| var_x_bool := true; var_y_bool := false; var_done_bool := false|}
| decr_bool_y_done : decr_bool_step
                       {| var_x_bool := true; var_y_bool := false; var_done_bool := false |}
                       {| var_x_bool := true; var_y_bool := true; var_done_bool := false|}
| decr_bool_done : forall b_x, decr_bool_step
                            {| var_x_bool := b_x; var_y_bool := true; var_done_bool := false |}
                            {| var_x_bool := b_x; var_y_bool := true; var_done_bool := true |}.

Inductive decr_bool_init : decr_bool_state -> Prop :=
| DecrBoolInit :  forall bx, decr_bool_init {| var_x_bool := bx; var_y_bool := false; var_done_bool := false |}.

Definition decr_bool_sys := {|
  Initial := decr_bool_init;
  Step := decr_bool_step
|}.

(* Our next task is to prove that this actually *is* an abstraction of the original.
 * For that, we'll use a simulation argument, so we need to define a simulation relation.
 *
 * The core of this abstraction is that the boolean version of x captures whether x is 0.
 * We formalize this as follows.
 *)
Inductive decr_R_var : nat -> bool -> Prop :=
| decr_R_var_O : decr_R_var O true
| decr_R_var_S : forall n, decr_R_var (S n) false.

(* PROBLEM 13 [3 points, ~6 tactics]
 * Prove the following lemma about decr_R_var, which says that for any natural number n,
 * n is abstracted by the boolean `Nat.eqb n 0`. (Nat.eqb is a function that compares
 * two natural numbers for equality, returning a boolean.)
 *
 * Hint: Proceed by *case analysis* on whether `n` is zero or not.
 *)
Lemma decr_R_var_eqb :
  forall n,
    decr_R_var n (Nat.eqb n 0).
Proof.
  intros.
  cases n.
  - simplify. constructor.
  - simplify. constructor.
Qed.


(* A state of the original system is related to an abstract state if x and y are related
 * by decr_R_var and the value of done is identical.
 *)
Inductive decr_R : decr_state -> decr_bool_state -> Prop :=
| Decr_R : forall n_x n_y b_x b_y done,
    decr_R_var n_x b_x ->
    decr_R_var n_y b_y ->
    decr_R {| var_x := n_x; var_y := n_y; var_done := done |}
           {| var_x_bool := b_x; var_y_bool := b_y; var_done_bool := done |}.


(* PROBLEM 14 [7 points, ~65 tactics]
 * Prove that decr_R is a simulation relation for these two systems.
 *)
Lemma decr_sim :
  simulates decr_R decr_sys decr_bool_sys.
Proof.
  constructor.
  - intros.
    cases st1.
    cases var_x0.
    + eexists.
      constructor.
      * constructor.
        -- constructor.
        -- invert H. constructor.
      * assert (var_done0 = false).
        -- invert H. equality.
        -- rewrite H0. constructor.
    + eexists.
      constructor.
      * constructor.
        -- constructor.
        -- invert H. constructor.
      * assert (var_done0 = false).
        -- invert H. equality.
        -- rewrite H0. constructor.
- intros.
    cases st1.
    cases var_x0; cases var_y0; cases var_done0.
    + invert H0.
    + eexists.
      propositional; invert H0; invert H; invert H4; invert H5; constructor; constructor.
    + invert H0.
    + cases var_y0; eexists;
      propositional; invert H0; invert H; invert H4; invert H5; constructor; constructor.
    + invert H0.
    + cases var_x0; simplify; propositional; invert H0; eexists;
      propositional; invert H; invert H4; invert H5; constructor; constructor.
    + invert H0.
    + cases var_x0; cases var_y0; eexists;
      propositional; invert H; invert H5; invert H6; invert H0; constructor; constructor.
Qed.

(* Ok, the tedious part is over. Now we can prove the original system safe
 * using model checking on the abstract system. But first, we need to express
 * the initial states of the abstract system as a finite set.
 *)
Lemma decr_bool_sys_init_set :
  decr_bool_init = { {| var_x_bool := true; var_y_bool := false; var_done_bool := false |},
                     {| var_x_bool := false; var_y_bool := false; var_done_bool := false |}
                   }.
Proof.
  apply sets_equal; simplify.
  propositional; subst.
  - invert H. destruct bx; equality.
  - constructor.
  - constructor.
Qed.

(* This line registers the lemma so that the model checker knows about it. *)
Hint Rewrite decr_bool_sys_init_set.

(* PROBLEM 15 [3 points, ~20 additional tactics]
 * Prove the system safe again, this time using model checking and abstraction.
 *)
Theorem decr_ok_via_simulation :
  invariantFor decr_sys decr_safe.
Proof.
  eapply invariant_weaken with (invariant1 := invariantViaSimulation decr_R _).
  - apply invariant_simulates with (sys2 := decr_bool_sys).
    + apply decr_sim.
    + model_check_infer.
  - intros.
    invert H. invert H1.
    + invert H0. constructor.
    + invert H0.
      invert H1; invert H2; invert H; invert H0;
      try cases done; try constructor; invert H; invert H0.
Qed.


(* --- SECTION 5: Operational semantics for expressions --- *)

(* To practice with operational semantics, let's explore using them to define the meaning
 * of arithmetic expressions, instead of using an interpreters.
 *)

(* Here's a copy of our old friend again. *)
Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

Definition valuation := fmap var nat.

(* And here's the interpreter again. *)
Fixpoint interp (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    match v $? x with
    | None => 0
    | Some n => n
    end
  | Plus e1 e2 => interp e1 v + interp e2 v
  | Minus e1 e2 => interp e1 v - interp e2 v
  | Times e1 e2 => interp e1 v * interp e2 v
  end.

(* First, let's see how give meaning to arithmetic expressions via a big-step operational semantics. *)

(* PROBLEM 16 [3 points, ~20 LOC]
 * Complete the definition of arith_eval. The final definition will need one constructor
 * for every constructor of `arith`. We have filled in the first one for you.
 *
 * Hint: Notice how similar the case we did for you is to the corresponding case in `interp`.
 * They should all be that similar.
 *
 * Hint: It is hard to know if you got this definition right except by trying to prove the
 * problems before.
 *)
Inductive arith_eval : valuation -> arith -> nat -> Prop := (* this semantics relates a valuation and an expression to its value (a nat) *)
| ArithEvalConst : forall v n, arith_eval v (Const n) n  (* think of this as: "in any valuation, Const n evaluates to n" *)
| ArithEvalVar : forall v x, arith_eval v (Var x) (interp (Var x) v)
| ArithEvalPlus :
  forall v e1 e2 n1 n2,
    arith_eval v e1 n1 -> arith_eval v e2 n2 -> arith_eval v (Plus e1 e2) (n1 + n2)
| ArithEvalMinus :
  forall v e1 e2 n1 n2,
    arith_eval v e1 n1 -> arith_eval v e2 n2 -> arith_eval v (Minus e1 e2) (n1 - n2)
| ArithEvalTimes :
  forall v e1 e2 n1 n2,
    arith_eval v e1 n1 -> arith_eval v e2 n2 -> arith_eval v (Times e1 e2) (n1 * n2)
.
(* TODO: Is this right? *)

(* Now we have two different semantics for arithmetic expressions: `interp` and `arith_eval`.
 * Let's prove that these two semantics agree.
 *)

(* PROBLEM 17 [2 points, ~25 tactics, or many fewer using semicolons]
 * Prove the first half of the equivalence, that `interp` implies `arith_eval`.
 *
 * Hint: Proceed by induction on e.
 *)
Lemma interp_eval :
  forall v e n,
    interp e v = n ->
    arith_eval v e n.
Proof.
  induct e; intros; simplify; invert H.
  + constructor.
  + cases (v $? x).
    - assert (n = interp (Var x) v).
      * simplify. rewrite Heq. equality.
      * rewrite H. constructor.
    - assert (0 = interp (Var x) v).
      * simplify. rewrite Heq. equality.
      * rewrite H. constructor.
  + econstructor.
    - apply IHe1. equality.
    - apply IHe2. equality.
  + econstructor.
    - apply IHe1. equality.
    - apply IHe2. equality.
  + econstructor.
    - apply IHe1. equality.
    - apply IHe2. equality.
Qed.


(* PROBLEM 18 [3 points, ~10 tactics, or many fewer using semicolons]
 * Prove the second half of the equivalence, that `arith_eval` implies `interp`.
 *
 * Hint: Proceed by induction on e.
 *)
Lemma eval_interp :
  forall v e n,
    arith_eval v e n ->
    interp e v = n.
Proof.
  induct e; intros; simplify; invert H.
  + equality.
  + simplify. equality.
  + f_equal.
    - apply IHe1 in H3. assumption.
    - apply IHe2 in H5. assumption.
  + f_equal.
    - apply IHe1 in H3. assumption.
    - apply IHe2 in H5. assumption.
  + f_equal.
    - apply IHe1 in H3. assumption.
    - apply IHe2 in H5. assumption.
Qed.


(* We can also give a small-step operational semantics to arithmetic expressions. *)
(* PROBLEM 19 [5 points, ~30 LOC]
 * Fill in the definition of `arith_step`. In this semantics, an expression is "done"
 * running when it is a `Const`.
 *
 * Hint: You'll need a constructor saying how to finish evaluating a Var.
 *
 * Hint: You'll need two more constructors for Plus, one for "making progress on the left"
 * and one for "making progress on the right". These should be vaguely similar to `StepSeq1`
 * in OperationalSemantics.v.
 *
 * Hint: Minus and Times are analogous to Plus.
 *
 * Hint: You don't need a constructor corresponding to Const (for the same reason we don't
 * have a constructor corresponding to Skip in OperationalSemantics.v).
 *
 * Hint: It is hard to know if you got this definition right except by trying to prove the
 * problems before.
 *)
Inductive arith_step : valuation -> arith -> arith -> Prop := (* this semantics relates a valuation and an expression to a "next" expression *)

| ArithStepPlus : forall v n1 n2,
    arith_step v (Plus (Const n1) (Const n2)) (Const (n1 + n2))
| ArithStepPlusLeft : forall v e1 e2 e1',
    arith_step v e1 e1' -> arith_step v (Plus e1 e2) (Plus e1' e2)
| ArithStepPlusRight : forall v n1 e2 e2',
    arith_step v e2 e2' -> arith_step v (Plus (Const n1) e2) (Plus (Const n1) e2')
| ArithStepMinus : forall v n1 n2,
    arith_step v (Minus (Const n1) (Const n2)) (Const (n1 - n2))
| ArithStepMinusLeft : forall v e1 e2 e1',
    arith_step v e1 e1' -> arith_step v (Minus e1 e2) (Minus e1' e2)
| ArithStepMinusRight : forall v n1 e2 e2',
    arith_step v e2 e2' -> arith_step v (Minus (Const n1) e2) (Minus (Const n1) e2')
| ArithStepTimes : forall v n1 n2,
    arith_step v (Times (Const n1) (Const n2)) (Const (n1 * n2))
| ArithStepTimesLeft : forall v e1 e2 e1',
    arith_step v e1 e1' -> arith_step v (Times e1 e2) (Times e1' e2)
| ArithStepTimesRight : forall v n1 e2 e2',
    arith_step v e2 e2' -> arith_step v (Times (Const n1) e2) (Times (Const n1) e2')
| ArithStepVar : forall v x,
    arith_step v (Var x) (Const (interp (Var x) v))
.
(* TODO: Is this right? *)

(* Let's prove the small step semantics equivalent to the big step. *)

(* PROBLEM 20 [8 points, ~90 tactics total, including 6 helper lemmas]
 * Prove the first half of the equivalence, that the big step implies the
 * (transitive-reflexive closure of) the small step.
 *)
Lemma arith_eval_step :
  forall v e n,
    arith_eval v e n ->
    (arith_step v)^* e (Const n).
Proof.
  induct 1.
  - constructor.
  - econstructor.
    + econstructor.
    + econstructor.
  - econstructor.
    + admit.
    + econstructor.
  - econstructor.
    + admit.
    + econstructor.
  - econstructor.
    + admit.
    + econstructor.
Admitted. (* Change to Qed when done *)


(* PROBLEM 21 [8 points, ~65 tactics total, including 2 helper lemmas]
 * Prove the second half of the equivalence, that the (transitive-reflexive closure of)
 * the small step implies the big step.
 *)
Lemma arith_step_eval :
  forall v e n,
    trc (arith_step v) e (Const n) ->
    arith_eval v e n.
Proof.
  induct 1.
  - econstructor.
  - invert H. invert H0.
      + econstructor.
      + invert H. 
      + invert H0. invert H1. invert H. invert H2. econstructor. invert H.
Admitted. (* Change to Qed when done *)
