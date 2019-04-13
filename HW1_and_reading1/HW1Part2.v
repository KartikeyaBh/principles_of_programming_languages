(* --- Homework 1, Part 2: Introduction to Coq, continued with Frap --- *)

(*
 * In this part of the homework, we get some practice with lists and other data structures
 * and use Frap tactics.
 *
 * Step through this file with CoqIDE (or another IDE for Coq), and complete the problems.
 * (Search for "PROBLEM" to be sure you find them all.)
 *
 * Throughout, we include the approximate lines of code (LOC) or number of tactics
 * for each of our solutions to these problems.  These are rough guidelines to help
 * you figure out if you are getting off-track.
 *
 * There is no penalty for writing a shorter or longer solution! However, if you find
 * yourself writing a much longer solution, see if you can figure out a simpler way.
 *
 *)

(* --- Making sure Frap is installed --- *)

(*
 * PROBLEM 0 [0 points, 0 LOC]
 * Set up Frap as described in README.md
 *
 * Once Coq is installed according to directions, you should be able to step over
 * the following line in your IDE.
 *)

Require Import Frap.
Set Implicit Arguments.

(* --- More arithmetic --- *)

(* This module creates a namespace where we can travel back in time to part 1.
 * Later in part 2, we're going to start using the Coq standard library version of
 * nat, so we hide our own definitions in this namespace so we can close it later.
 *)
Module leftover_from_part_1.

(*
 * Here are some definitions again from part 1 of the homework.
 *)
Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Fixpoint add (n1 : nat) (n2 : nat) : nat :=
  match n1 with
  | O => n2
  | S m1 => S (add m1 n2)
  end.

Fixpoint mult (n1 : nat) (n2 : nat) : nat :=
  match n1 with
  | O => O
  | S m1 => add n2 (mult m1 n2)
  end.

(*
 * PROBLEM 1 [8 points, ~10 tactics, plus 3-4 helper lemmas, each needing <10 tactics]
 * Prove that multiplication is commutative, as stated by the lemma below.
 *
 * This was a challenge problem on part 1. If you already did it, feel free to
 * copy-paste your solution here.
 *
 * Hints from last time are reproduced below.
 *
 * Hint: Proceed by induction.
 *
 * Hint: Don't use more than one induction inside a single proof.  Instead, figure out
 * lemmas that might be useful, and then prove those separately (by induction, probably).
 *
 * Hint: It might be useful to review all the lemmas about `add` in part 1.
 * Feel free to copy them over if you need to use them. You might need to state and prove
 * some analogous lemmas about `mult`.
 *
 * Hint: In order to prove your helpers about `mult`, you might need 1 or 2 additional
 * facts about `add`.  Try to keep these simple, based on facts you know from math, and
 * prove them by induction.
 *)

Lemma mult_comm :
  forall n1 n2,
    mult n1 n2 = mult n2 n1.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * PROBLEM 2 [10 points, 5-10 tactics, plus 1-3 helper lemmas, each needing 5-10 tactics]
 * State and prove that the `mult` function is associative.
 *
 * Hint: Feel free to look up what associative means.
 *
 * Hint: You'll probably need 1-2 more lemmas about mult and/or add.
 *)
(* YOUR LEMMA STATEMENT AND PROOF HERE *)

End leftover_from_part_1. (* close the namespace *)

(*
 * Now that you've seen how nat, add, and mult are defined under the hood,
 * from now on we'll use the versions in Coq's standard library. These come
 * with nice notations like `1 + 3 * 4`, and with lots of free lemmas.
 *
 * There are also some useful tactics for working with arithmetic. Please
 * see FRAP section 2.4 for a discussion.
 *
 * Here are some automated proofs that the Coq standard library versions
 * of add and mult are commutative. (These lemmas are also in the standard
 * library, but we prove them from scratch just to demonstrate the tactics.)
 *)

Lemma add_comm_again :
  forall a b, a + b = b + a.
Proof.
  intros.
  linear_arithmetic.
Qed.

Lemma mult_comm_again :
  forall a b, a * b = b * a.
Proof.
  intros.
  Fail linear_arithmetic. (* doesn't work!! *)
  ring. (* works!! *)
Qed.

(*
 * PROBLEM 3 [8 points, 2 clear yes/no answers and ~4 sentences of explanation]
 * Answer the following in ~1 sentence each.  If the bullet point starts with a yes/no question,
 * be sure to state your yes/no answer clearly before proceeding to explain.
 *
 *   - Why does `linear_arithmetic` succeed on `add_comm_again`, but fail on `mult_comm_again`?
 *   - Why does `ring` succeed on `mult_comm_again`?
 *   - Will `ring` succeed on `add_comm_again`? Why or why not?
 *   - Is `ring` always more powerful than `linear_arithmetic`? Why or why not?
 *)


(* --- Curry-Howard practice --- *)

Module curry_howard.
(*
 * In lecture, we looked at an inductive definition of the types `True` and `False`,
 * and talked about how they encode logical ideas as types.
 *
 * One of the deep connections in type theory is between logic and programming.
 * In fact, there are programming analogues to `True` and `False`.
 *)

Inductive unit : Type :=
| tt : unit.

Inductive empty : Type :=
.

(*
 * PROBLEM 4 [5 points, 1-2 sentences]
 * Explain in your own words the relationship between `unit` and `True`, and between
 * `empty` and `False`.
 *)

(*
 * Here are two ways of defining the identity function on `unit`.
 *)

Definition unit_id1 (x : unit) : unit := x.  (* first way: just return the argument *)
Definition unit_id2 (x : unit) : unit :=
  match x with (* second way: take the argument apart and put it back together again *)
  | tt => tt
  end.

(*
 * PROBLEM 5 [5 points, ~3 tactics]
 * Prove that the two definition of the identity function on `unit` are the same
 * by proving the following lemma.
 *)
Lemma unit_id_same :
  forall x,
    unit_id1 x = unit_id2 x.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * By analogy, we can also present two different proofs that True implies True.
 *)
Lemma True_implies_True1 :
  True -> True.
Proof.
  intro H. (* first way: just take the evidence of True and use it directly *)
  apply H.
Qed.

Lemma True_implies_True2 :
  True -> True.
Proof.
  intro H. (* second way: take apart the evidence of True and put it back together *)
  cases H.
  exact I.
Qed.

(*
 * We can ask Coq to print definitions using the `Print` command. This works
 * not only for things defined with Definition/Fixpoint, but also for things
 * defined via Lemma/Theorem.
 *
 * Coq prints things in a "de-sugared" form, with more type annotations, but
 * usually it's pretty easy to see how it corresponds to what you wrote.
 *)

Print unit_id1.
(*
 * This command prints `fun x : unit => x`, which is syntax for a function
 * that takes an argument `x` of type `unit` and just returns it,  which
 * is exactly what we wrote in the definition of `unit_id1`.
 *)


(*
 * We can also ask Coq to print the underlying proof term for the lemma
 * `True_implies_True1`.
 *)
Print True_implies_True1.

(*
 * We can similarly print the definitions for the second versions.
 *)
Print unit_id2.
Print True_implies_True2.

(*
 * PROBLEM 6 [8 points, 2 proofs, each with <5 tactics, and 2 definitions, each with <5 LOC]
 * Prove that False implies False in two different ways, one that just takes
 * the evidence of False and uses it directly, and one which takes it apart
 * and puts it back together again.
 *
 * For each proof, also print its proof term using the Print command. If you
 * see anything interesting or surprising, write a comment here. (worth 0 pts)
 *
 * Then, define two identity functions on `empty`, one which just returns its argument,
 * and one which takes its argument apart and puts it back together again.
 *
 * Hint: If you're stuck on the definitions, you can work by analogy to the proof terms
 * you saw by using the Print command on your proofs.
 *)
(* YOUR CODE HERE*)

End curry_howard.

(* --- List practice --- *)

(* Here are some copied definitions from FRAP. *)
Inductive list (A : Type) : Type :=
| nil
| cons (hd : A) (tl : list A).

Arguments nil [A].
Infix "::" := cons.
Notation "[ ]" := nil.
Notation "[ x1 ; .. ; xN ]" := (cons x1 (.. (cons xN nil) ..)).

Fixpoint length {A} (ls : list A) : nat :=
  match ls with
  | nil => 0
  | _ :: ls' => 1 + length ls'
  end.

Fixpoint app {A} (ls1 ls2 : list A) : list A :=
  match ls1 with
  | nil => ls2
  | x :: ls1' => x :: app ls1' ls2
  end.
Infix "++" := app.

Fixpoint rev {A} (ls : list A) : list A :=
  match ls with
  | nil => nil
  | x :: ls' => rev ls' ++ [x]
  end.

Fixpoint rev_append {A} (ls acc : list A) : list A :=
  match ls with
  | nil => acc
  | x :: ls' => rev_append ls' (x :: acc)
  end.

Definition rev' {A} (ls : list A) : list A :=
  rev_append ls [].

(*
 * PROBLEM 7 [12 points, ~6 tactics plus 1 copy-pasted helper lemma from lecture]
 * Prove the following theorem about the length of a reversed list.
 *
 * Hint: Proceed by induction on l.
 *
 * Hint: You'll need a helper lemma from lecture. Feel free to copy-paste it
 * when you find it.
 *)
Lemma length_rev :
  forall A (l : list A),
    length (rev l) = length l.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * PROBLEM 8 [10 points, (1 alternate proof and a few sentences comparing to Adam's proof)
 *                      OR (an explanation of how to come up with rev_append_ok)]
 * Go back to rev'_ok and proceed directly by induction on `ls` and assume you did
 * not have access to the lemma rev_append_ok (or had not thought of it yet).
 *
 * Can you find an alternative proof? If so, provide it, and also explain what makes it
 * better/worse/different from Adam's proof. If you can't find an alternative (or if
 * you strongly dislike all the alternatives you can find), instead explain how
 * you might "come up" with the lemma rev_append_ok based on your experience getting
 * stuck during a direct proof.
 *)

Theorem rev'_ok : forall A (ls : list A),
    rev' ls = rev ls.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(* --- Binary Tree practice --- *)

(* More definitions copied from FRAP. *)
Inductive tree (A : Type) : Type :=
| Leaf
| Node : tree A -> A -> tree A -> tree A.
Arguments Leaf [A].

Fixpoint reverse {A} (t : tree A) : tree A :=
  match t with
  | Leaf => Leaf
  | Node l d r => Node (reverse r) d (reverse l)
  end.

(*
 * Here is a function that adds up all the elements of a list of nats.
 *)
Fixpoint sum_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

(*
 * PROBLEM 9 [5 points, ~5 LOC]
 * Define a function that adds up all the elements of a tree of nats.
 *)
Fixpoint sum_tree (t : tree nat) : nat :=
0. (* YOUR CODE HERE *)

(*
 * PROBLEM 10 [5 points, ~5 tactics]
 * Prove that `reverse` has no effect on the sum of the elements in a tree.
 *)
Lemma sum_tree_reverse :
  forall t,
    sum_tree (reverse t) = sum_tree t.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * PROBLEM 11 [12 points, 5-10 tactics, plus 1 helper lemma needing ~5 tactics]
 * Prove the following similar lemma about `sum_list` and `rev`.
 *
 * Hint: Proceed by induction on l.
 *
 * Hint: You'll need a helper lemma about sum_list.
 *)
Lemma sum_list_rev :
  forall l,
    sum_list (rev l) = sum_list l.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(* --- Syntax practice --- *)

Module ArithWithConstants.
(* Copied from FRAP. *)
Inductive arith : Set :=
| Const (n : nat)
| Plus (e1 e2 : arith)
| Times (e1 e2 : arith).

(*
 * Here's a function that kind of sums up the constants in the syntax tree,
 * just like sum_tree did in the previous section. The difference is that
 * at a `Times` node, we multiply the values instead of adding them.
 *)
Fixpoint kinda_sum (e : arith) : nat :=
  match e with
  | Const n => n
  | Plus e1 e2 => kinda_sum e1 + kinda_sum e2
  | Times e1 e2 => kinda_sum e1 * kinda_sum e2
  end.

Compute kinda_sum (Plus (Const 1) (Const 1)). (* 2 *)
Compute kinda_sum (Times (Const 2) (Const 3)). (* 6 *)

(* From FRAP. *)
Fixpoint commuter (e : arith) : arith :=
  match e with
  | Const _ => e
  | Plus e1 e2 => Plus (commuter e2) (commuter e1)
  | Times e1 e2 => Times (commuter e2) (commuter e1)
  end.

(*
 * PROBLEM 12 [12 points, 5-10 tactics]
 * Prove the following theorem about kinda_sum and commuter.
 *)
Lemma kind_sum_commuter :
  forall e,
    kinda_sum e = kinda_sum (commuter e).
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


(* --- The End --- *)

(*
 * This is the end of part 2 of homework 1.
 *
 * To submit your homework, please follow the instructions at the end of the
 * README.md file in this directory.
 *
 * Please also see the README.md file to read about how we will grade this homework.
 *)

(* --- Challenge problem --- *)

(*
 * There's one more challenge problem below, which you can try if you like.
 * It will not be worth any points on this homework, or any future one,
 * but you will get to continue to play the video game called Coq.
 *
 * You already have all the techniques you need to solve it, but it is slightly
 * longer than the previous problems.
 *)

(*
 * We can define a version of constant folding from FRAP, but for arithmetic
 * without variables.
 *)

Fixpoint constantFold (e : arith) : arith :=
  match e with
  | Const _ => e
  | Plus e1 e2 =>
    let e1' := constantFold e1 in
    let e2' := constantFold e2 in
    match e1', e2' with
    | Const n1, Const n2 => Const (n1 + n2)
    | Const 0, _ => e2'
    | _, Const 0 => e1'
    | _, _ => Plus e1' e2'
    end
  | Times e1 e2 =>
    let e1' := constantFold e1 in
    let e2' := constantFold e2 in
    match e1', e2' with
    | Const n1, Const n2 => Const (n1 * n2)
    | Const 1, _ => e2'
    | _, Const 1 => e1'
    | Const 0, _ => Const 0
    | _, Const 0 => Const 0
    | _, _ => Times e1' e2'
    end
  end.

(*
 * PROBLEM 13 [0 points, ~15 tactics if taking advantage of `repeat match goal`,
 *                      many more tactics otherwise]
 *
 * Hint: You may want to copy some useful `repeat match goal` techniques from
 * the other FRAP proofs about constantFold.
 *)
Lemma kinda_sum_constantFold :
  forall e,
    kinda_sum (constantFold e) = kinda_sum e.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

End ArithWithConstants.
