(* --- Homework 1, Part 1: Introduction to Coq --- *)

(*
 * This part of homework 1 is a tutorial introduction to Coq.
 * It does not correspond to any chapter in FRAP, and does not require FRAP to be installed.
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
 * Every problem on this homework is designed to be conceptually straightforward;
 * the hard part is just getting up to speed on Coq.
 *)


(* --- Setting up Coq --- *)

(*
 * PROBLEM 0 [0 points, 0 LOC]
 * Set up Coq 8.9 as described in README.md
 *
 * Once Coq is installed according to directions, you should be able to step through
 * this file in your IDE.
 *)

(* --- Boolean practice --- *)

(*
 * Here are some definitions about booleans from lecture.
 *)

Inductive bool : Type :=
| true : bool
| false : bool.

Definition notb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

(*
 * PROBLEM 1 [10 points, ~4 LOC]
 * Write a function called `orb` that implements boolean disjunction.
 *
 * Hint: Kinda like `andb`, but different.
 *)
Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | false => b2
  | true => true
  end.

(*
 * Remember that `Compute` just runs programs. We can use it for simple testing.
 *)
Compute orb true true.   (* should be true. *)
Compute orb true false.  (* should be true. *)
Compute orb false true.  (* should be true. *)
Compute orb false false. (* should be false. *)

(*
 * PROBLEM 2 [10 points, ~10 tactics, or fewer if using semicolons]
 * Prove the following theorem, that `orb` is commutative.
 *
 * Hint: Kinda like `andb_comm` from lecture.
 *)
Lemma orb_comm :
  forall b1 b2,
    orb b1 b2 = orb b2 b1.
Proof.
  destruct b1; destruct b2; auto.
Qed. (* Change to Qed when done *)

(*
 * PROBLEM 3 [10 points, ~10 tactics, or fewer if using semicolons]
 * Prove the following theorem about `notb`, `orb`, and `andb`.
 *
 * Hint: All these proofs start to look the same after a while...
 *)
Lemma notb_andb_is_orb_notb :
  forall b1 b2,
    notb (andb b1 b2) = orb (notb b1) (notb b2).
Proof.
  destruct b1; destruct b2; auto.
Qed. (* Change to Qed when done *)

(* --- Natural numbers practice --- *)

(*
 * Here are some more definitions from lecture, this time about natural numbers.
 *)

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Fixpoint add (n1 : nat) (n2 : nat) : nat :=
  match n1 with
  | O => n2
  | S m1 => S (add m1 n2)
  end.

(*
 * PROBLEM 4 [10 points, ~4 basic tactics, or 1 powerful tactic]
 * Prove the following theorem about add.
 *
 * Hint: Do you think you'll need induction? Hmm...
 *)
Lemma S_add :
  forall n1 n2,
    add (S n1) n2 = S (add n1 n2).
Proof.
  induction n1; intro n2; simpl.
  - reflexivity.
  - reflexivity.
Qed. (* Change to Qed when done *)

(*
 * PROBLEM 5 [15 points, 1-2 sentences of English]
 * Consider the following theorem, superficially similar to the previous one.
 *
 * Before trying to prove it, describe whether you expect it to be less difficult than,
 * more difficult than, or about the same difficulty as the previous theorem.
 *
 * Please explain your answer in 1 to 2 sentences, using your mental model for what
 * kinds of things different tactics are good at.
 *
 * Hint: If you don't know, it's okay to try to prove it (the next problem below),
 * and then come back and explain the outcome.
 *)
(*
 * This seems to be more difficult than the previous one.
 * It is because of how add is defined. It is recursive on the first argument and
 * not the second one.
 *)
Lemma add_S :
  forall n1 n2,
    add n1 (S n2) = S (add n1 n2).
Proof.
  induction n1; intro n2; simpl.
  - reflexivity.
  - rewrite IHn1. reflexivity.
Abort.
  (* This looks more difficult.  For the first version, the S on the left side
     was applied to the first operand, which naturally meshes with how pattern-matching
     works.  Here, I suspect we'll need to do more work to move it out. *)


(*
 * PROBLEM 6 [20 points, ~8 tactics, or fewer using semicolons]
 * Prove the following theorem about add.
 *
 * Hint: Do you think you'll need induction? Hmm...
 *)
Lemma add_S :
  forall n1 n2,
    add n1 (S n2) = S (add n1 n2).
Proof.
    induction n1; intro n2; simpl.
  - reflexivity.
  - rewrite IHn1. reflexivity.
Qed. (* Change to Qed when done *)

Lemma add_O :
  forall n,
    add n O = n.
Proof.
  induction n.
  -auto.
  - simpl. rewrite IHn. reflexivity.
Qed.

(*
 * PROBLEM 7 [25 points, ~10 tactics]
 * Prove the following theorem about add.
 *
 * Hint: Proceed by induction.
 *
 * Hint: Don't forget to reuse previously proved Lemmas by using the `rewrite` tactic.
 *
 * Hint: It's okay to copy-paste lemmas we proved in lecture if you need them.
 *)
Lemma add_comm :
  forall n1 n2,
    add n1 n2 = add n2 n1.
Proof.
  induction n1; intro n2; simpl.
  - rewrite add_O. reflexivity.
  - rewrite add_S. rewrite IHn1. reflexivity.
Qed. (* Change to Qed when done *)

(* --- The End --- *)

(*
 * This is the end of part 1 of the homework.
 *
 * To submit your homework, please follow the instructions at the end of the
 * README.md file in this directory.
 *
 * Please also see the README.md file to read about how we will grade this homework.
 *)

(* --- Challenge problem --- *)

(*
 * There's one more challenge problem below, which you can try if you like.
 * It will appear as a regular problem on part 2 of the homework.
 *
 * You already have all the techniques you need to solve it, but it is slightly longer than the
 * previous problems.
 *
 * The problem is about multiplication, which can define by repeated addition as follows.
 *)

Fixpoint mult (n1 : nat) (n2 : nat) : nat :=
  match n1 with
  | O => O
  | S m1 => add n2 (mult m1 n2)
  end.

(*
 * We can use Compute to convince ourselves that this is actually multiplication.
 *)
Compute mult (S O) (S O).               (* should be S O, aka 1 *)
Compute mult (S (S O)) (S (S (S O))).   (* should be S (S (S (S (S (S O))))), aka 6 *)

(*
 * PROBLEM 8 [0 points for now, will be worth some points on part 2,
 *          ~10 tactics, plus 3-4 helper lemmas, each needing <10 tactics]
 * Prove that multiplication is commutative, as stated by the lemma below.
 *
 * Hint: Proceed by induction.
 *
 * Hint: Don't use more than one induction inside a single proof.  Instead, figure out
 * lemmas that might be useful, and then prove those separately (by induction, probably).
 *
 * Hint: It might be useful to review all the lemmas about `add` in this file.
 * You might need some analogous lemmas about `mult`.
 *
 * Hint: In order to prove your helpers about `mult`, you might need 1 or 2 additional
 * facts about `add`.  Try to keep these simple, based on facts you know from math, and
 * prove them by induction.
 *)

Lemma add_one_2nd_arg:
  forall n1 n2,
    S (add n1 n2) = add n1 (S n2).
Proof.
  induction n1; intro n2.
  - simpl. reflexivity.
  - simpl. rewrite IHn1. reflexivity.
Qed.

Lemma add_swap:
  forall n1 n2 n3,
    add n1 (add n2 n3) = add n2 (add n1 n3).
Proof.
  induction n1; intro n2.
  - simpl. reflexivity.
  - simpl. intro n3. rewrite IHn1. rewrite add_one_2nd_arg. reflexivity.
Qed.

Lemma mult_zero:
  forall n1,
    mult n1 O = O.
Proof.
  induction n1.
  - simpl. reflexivity.
  - simpl. rewrite IHn1. reflexivity.
Qed.

Lemma mult_add_one:
  forall n1 n2,
    add n1 (mult n1 n2) = mult n1 (S n2).
Proof.
  induction n1; intro n2.
  - simpl. reflexivity.
  - simpl. rewrite add_swap. rewrite IHn1. reflexivity.
Qed.

Lemma mult_comm :
  forall n1 n2,
    mult n1 n2 = mult n2 n1.
Proof.
  induction n1; intro n2.
  - simpl. rewrite mult_zero. reflexivity.
  - simpl. rewrite IHn1. rewrite mult_add_one. reflexivity.
Qed.
