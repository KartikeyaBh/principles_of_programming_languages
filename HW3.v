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
(* YOUR DESCRIPTION AND EXPLANATION HERE *)

(* The definition of trc is :
Inductive trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| TrcRefl : forall x, trc R x x
| TrcFront : forall x y z,
  R x y
  -> trc R y z
  -> trc R x z.

trc goes from y to all reachable states from y, and then concludes that those states
are reachable from x as well.
different_trc goes from x to all reachable states from x, and then transitions from them.
And concludes that all states are reachable from x.

Both do transitive reflexive closure.
*)

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


Theorem different_trc_implies_trc :
  forall A (R : A -> A -> Prop) x y,
    different_trc R x y ->
    trc R x y.
Proof.
  induct 1; simplify.
  - econstructor.
  - eapply trc_trans.
    + eapply IHdifferent_trc.
    +
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

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
Theorem trc_implies_different_trc_implies :
  forall A (R : A -> A -> Prop) x y,
    trc R x y ->
    different_trc R x y.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


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
(* YOUR EXPLANATION HERE *)

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
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


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
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

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
Abort.
(* YOUR EXPLANATION HERE *)


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
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

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
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


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
Definition decr_init_alternative (s : decr_state) : Prop.
(* insert `:=` on the previous line before the `.`, then add your solution here. *)
Admitted. (* delete this *)

(* PROBLEM 11 [5 points, ~10 tactics]
 * Prove your alternative definition equivalent to the original.
 *)
Lemma decr_init_alternative_ok :
  forall s,
    decr_init_alternative s <-> decr_init s.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

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
Theorem decr_ok :
  invariantFor decr_sys decr_safe.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


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
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


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
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

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
    + (* uncomment this tactic to run the model checker! *) (* model_check_infer. *) 
      (* delete this line *) admit.
  - (* Now complete the proof by analyzing all states found by the model checker. *)
    (* REST OF YOUR PROOF HERE. *)
Admitted. (* Change to Qed when done *)


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
(* REST OF YOUR DEFINITION HERE *)
.

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
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


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
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


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

(* YOUR DEFINITION HERE *)
.

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
  (* YOUR CODE HERE *)
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
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)
