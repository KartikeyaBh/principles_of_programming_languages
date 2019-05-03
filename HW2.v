(* -------------------------------------- Homework 2 --------------------------------------
 *
 * This homework has 3 fairly independent sections. Feel free to skip around.
 *   - Section 1 shows an alternate implementation of finite maps using assocation lists.
 *   - Section 2 represents infinite streams of data in Coq using step functions.
 *   - Section 3 gives more practice reasoning about programs via interpreters.
 *)

Require Import Frap.

(* --- Section 1: Finite maps via assocation lists --- *)

(*
 * Frap defines a finite map type `fmap`, which we used in lecture to define the
 * `valuation` type for our little programming languages.
 *
 * Because Frap's fmap type is designed to support easy proofs, it uses features
 * under the hood that make it impossible for Coq to actually *evaluate* expressions
 * containing fmaps.
 *
 * The first section of this homework asks you to implement another finite maps type
 * that does support evaluation.
 *)

(* A basic interface for finite maps. *)
Module Type MAP.
  Set Implicit Arguments.
  Parameter key : Type.
  Parameter t : Type -> Type.

  Parameter empty : forall V, t V.
  Arguments empty [V].
  Parameter lookup : forall V, t V -> key -> option V.
  Parameter add : forall V, t V -> key -> V -> t V.
  Parameter remove : forall V, t V -> key -> t V.

  Axiom lookup_empty : forall V k, lookup (V := V) empty k = None.
  Axiom lookup_add_eq : forall V k1 k2 v (m : t V), k1 = k2 -> lookup (add m k1 v) k2 = Some v.
  Axiom lookup_add_ne : forall V k1 k2 v (m : t V), k1 <> k2 -> lookup (add m k1 v) k2 = lookup m k2.
  Axiom lookup_remove_eq : forall V k1 k2 (m : t V), k1 = k2 -> lookup (remove m k1) k2 = None.
  Axiom lookup_remove_ne : forall V k1 k2 (m : t V), k1 <> k2 -> lookup (remove m k1) k2 = lookup m k2.
End MAP.

(* An interface for types that support boolean equality. (from Frap) *)
Module Type SET_WITH_EQUALITY.
  Parameter t : Type.
  Parameter equal : t -> t -> bool.

  Axiom equal_ok : forall a b, if equal a b then a = b else a <> b.
End SET_WITH_EQUALITY.

(* Now we'll give an implementation of MAP using "assocation lists" (lists of key-value pairs). *)
Module MapAssocList (K : SET_WITH_EQUALITY) <: MAP.
  Definition key := K.t.
  Definition t (V : Type) : Type := list (key * V).

  (* The empty map is represented by the empty association list. *)
  Definition empty {V} : t V := [].

  (* To lookup a key in our implementation, we walk the association list, looking
   * for a pair with a matching key, and returning its value. *)
  Fixpoint lookup {V} (m : t V) (k : key) : option V :=
    match m with
    | [] => None
    | (k2,v2) :: m' =>
      if K.equal k k2
      then Some v2
      else lookup m' k
    end.

  (* PROBLEM 0 [5 points, ~1 tactic]
   * Prove the following theorem about looking up keys in the empty map.
   *
   * Hint: Don't use induction unless you can convince yourself you need it.
   *
   * Hint: Don't use case analysis unless you can convince yourself you need it.
   *)
  Lemma lookup_empty : forall V k, lookup (V := V) empty k = None.
  Proof.
    auto.
  Qed.

  (* PROBLEM 1 [5 points, ~7 LOC]
   * Define the function `add` with the following type.
   *
   * Hint: There are two natural ways of defining add. One is recursive (using Fixpoint),
   * and one is not recursive (using Definition). Feel free to use either one, but be
   * aware that they may have consequences for your proofs!
   *)
  Definition add {V} (m : t V) (k : key) (v : V) : t V := (k,v) :: m.

  (* PROBLEM 2 [5 points, ~7 LOC]
   * Define the function `remove` with the following type.
   *
   * Hint: You'll need to change `Definition` to `Fixpoint`.
   *)
  Fixpoint remove {V} (m : t V) (k : key) : t V :=
    match m with
    | [] => []
    | (k2, v2) :: m' =>
      if K.equal k k2
      then remove m' k
      else (k2, v2) :: remove m' k
    end.


  (* PROBLEM 3 [5 points, ~20 tactics per proof]
   * Prove the following two facts about looking up keys in a map returned by `add`.
   *
   * Hint: It might help to look at the proof of `member_add_eq` in the module
   * `ListSet` in DataAbstraction.v from Frap. Pay special attention to how
   * SE.equal_ok is used in proofs. Something similar will be useful with K.equal_ok.
   *
   * Hint: You may find it useful to use the `cases` tactic to make progress
   * through expressions of the form "let (a, s) := ... in ..."
   *)
  Lemma lookup_add_eq : forall V k1 k2 v (m : t V), k1 = k2 -> lookup (add m k1 v) k2 = Some v.
  Proof.
    simplify.
    pose proof (K.equal_ok k2 k1).
    cases(K.equal k2 k1).
    - equality.
    - equality.
  Qed.

  Lemma lookup_add_ne : forall V k1 k2 v (m : t V), k1 <> k2 -> lookup (add m k1 v) k2 = lookup m k2.
  Proof.
    simplify.
    pose proof (K.equal_ok k2 k1).
    cases(K.equal k2 k1).
    - equality.
    - equality.
  Qed.

  (* PROBLEM 4 [5 points, ~20 tactics per proof]
   * Prove the following two facts about looking up keys in a map returned by `remove`.
   *
   * Hint: Think carefully about what `lookup_remove_eq` is saying. First, convince yourself
   * that your implementation of `remove` really has this property, and adjust your
   * implementation if you realize it does not.
   *)
  Lemma lookup_remove_eq : forall V k1 k2 (m : t V), k1 = k2 -> lookup (remove m k1) k2 = None.
  Proof.
    intros.
    induct m.
    - simplify. equality.
    - destruct a.
      simplify.
      cases (K.equal k1 k).
      + apply IHm. apply H.
      + simplify.
        cases (K.equal k2 k).
        * equality.
        * apply IHm. apply H.
  Qed.

  Lemma lookup_remove_ne : forall V k1 k2 (m : t V), k1 <> k2 -> lookup (remove m k1) k2 = lookup m k2.
  Proof.
    intros.
    induct m.
    - simplify. equality.
    - destruct a.
      simplify.
      cases (K.equal k1 k); cases (K.equal k2 k);
        pose proof (K.equal_ok k1 k); rewrite Heq in H0;
        pose proof (K.equal_ok k2 k); rewrite Heq0 in H1.
      + equality.
      + equality.
      + rewrite <- H1. simplify. cases (K.equal k2 k2).
        * equality.
        * equality.
      + simplify. cases (K.equal k2 k).
        * equality.
        * apply IHm. equality.
  Qed.
End MapAssocList.

(* Here's a little utility module from Frap to show nats have equality. *)
Module NatWithEquality <: SET_WITH_EQUALITY with Definition t := nat.
  Definition t := nat.

  Fixpoint equal (a b : nat) : bool :=
    match a, b with
    | 0, 0 => true
    | S a', S b' => equal a' b'
    | _, _ => false
    end.

  Theorem equal_ok : forall a b, if equal a b then a = b else a <> b.
  Proof.
    induct a; simplify; cases b; try equality.
    specialize (IHa b).
    cases (equal a b); equality.
  Qed.
End NatWithEquality.

Module NatMap := MapAssocList(NatWithEquality).

(* Here's the big win of our implementation: we can compute with these maps!
 *
 * Note: This line won't work correctly until you've implemented `add` above.
 *)

Compute NatMap.lookup (NatMap.add NatMap.empty 0 1) 0.  (* should evaluate to `Some 1` *)








(* --- Section 2: Infinite streams as step functions --- *)

(* All the data types we've looked at so far in Coq have been some kind of finite tree.
 * But it is often useful to represent and manipulate conceptually infinite collections
 * of data, as supported by generators, iterators, or streams in some languages.
 *
 * In Coq, one way to represent these collections is as a kind of stateful process,
 * described by a "step function".
 *)
Module StreamsAsSteppers.

  (* Here we define the type of step functions that manipulate internal state of
   * of type T and produce an infinite stream of elements of type A. These functions
   * take the current state (of type T), and return an element (of type A) and a
   * new state.
   *)
  Definition stepper (T : Type) (A : Type) :=
    T -> A * T.

  (* The idea is that, given some initial state t, we can apply the step function
   * to get the first element of the stream and a new state t'.  Calling the step
   * function again on t' produces the next element and another state, and so on.
   *)

  (* We can formalize this idea with the following function that collects the
   * first `n` elements of such a stream into a list.
   *)
  Fixpoint run_stepper {T A} (step : stepper T A) (n : nat) (s : T) : list A :=
    match n with
    | O => []
    | S n' =>
      let (a, s) := step s in
      a :: run_stepper step n' s
    end.

  (* PROBLEM 5 [5 points, ~7 tactics]
   * Prove the following theorem showing that `run_stepper` always returns
   * the right number of elements.
   *
   * Hint: You may find it useful to use the `cases` tactic to make progress
   * through expressions of the form "let (a, s) := ... in ..."
   *)
  Lemma run_stepper_length :
    forall T A (step : stepper T A) n s,
      length (run_stepper step n s) = n.
  Proof.
    intros.
    induct n.
    - equality.
    - simplify.
      cases (step s).
      simplify.
      rewrite IHn.
      equality.
  Qed.

  (* Now here's an example of a stream: the stream of all natural numbers.
   * Both its element type and internal state type are `nat`. At each step,
   * it produces the current state as the next element, and then increments
   * that number to get the new state.
   *)
  Example nats : stepper nat nat := fun n => (n, n + 1).

  (* Running `nats` for 10 steps starting from 0 produces the first 10
   * natural numbers, as expected.
   *)
  Compute run_stepper nats 10 0.

  (* PROBLEM 6 [10 points, ~4 tactics + 1 helper lemma needing ~7 tactics]
   * Prove the following theorem about `run_stepper` on `nats`, which says
   * that if we run from a non-zero state `s`, that's the same as adding
   * `s` to all the elements from running starting at 0.
   *
   * Hint: The first thing to try is to proceed by induction.
   *
   * Hint: You'll get stuck. There at least two ways to unstick yourself,
   * both involving an additional lemma. You can either generalize the
   * statement of run_stepper_nats to replace the 0 in the RHS with a variable,
   * or you can prove a lemma (or find one in stdlib) about mapping two
   * functions back to back.
   *)
  Lemma add_zero :
    forall n,
      n + 0 = n.
  Proof.
    auto.
  Qed.

  Lemma s_plus_a_plus_1_associativity :
    forall s a,
      s + a + 1 = s + (a + 1).
  Proof.
    intros.
    linear_arithmetic.
  Qed.

  Lemma run_stepper_nats_helper :
    forall n s a,
      run_stepper nats n (s + a) =
      List.map (fun x => s + x) (run_stepper nats n a).
  Proof.
    intro n.
    induct n.
    - simplify. equality.
    - simplify. rewrite <- IHn. rewrite s_plus_a_plus_1_associativity. equality.
  Qed.

  Lemma run_stepper_nats :
    forall s n,
      run_stepper nats n s =
      List.map (fun x => s + x) (run_stepper nats n 0).
  Proof.
    intros.
    pose proof run_stepper_nats_helper.
    rewrite <- (add_zero s) at 1.
    apply H with (a := 0).
  Qed.


  (* PROBLEM 7 [5 points, ~2 LOC]
   * Define another example stream of your choice.  For example, you could define
   * the constant stream of zeroes, or a stream of booleans that alternates between
   * true and false, or the stream of prime numbers.
   *
   * Brownie (i.e. not real) points for creativity!
   *
   * Also, use the `Compute` command to give at least one example of running your
   * stream for a few steps from its initial state.
   *)
  Example zeroes : stepper nat nat := fun n => (0, 10).

  Compute run_stepper zeroes 10 0.

  Example fibonacci : stepper (nat * nat) nat := fun state =>
    let (n1, n2) := state in (n1 + n2, (n2, n1 + n2)).

  Compute run_stepper fibonacci 10 (0, 1).


  (* In addition to specific examples, we can define stream transformers,
   * or in other words, functions that take and return streams. Here's a simple
   * transformer on nat streams that adds one to every element of the stream.
   *)
  Definition inc_stepper {T} (step : stepper T nat) : stepper T nat :=
    fun s =>
      let (n, s') := step s in
      (n + 1, s').

  Compute run_stepper (inc_stepper nats) 10 1.
  Compute run_stepper nats 10 2.

  (* PROBLEM 8 [5 points, 1 line of specification and ~7 tactics of proof]
   * Complete the statement of the following theorem that explains what
   * inc_stepper does to the `nats` stream. Then prove your resulting theorem.
   *)
  Lemma run_inc_stepper_nats :
    forall n s,
      run_stepper (inc_stepper nats) n s =
        run_stepper nats n (s + 1).
  Proof.
    intro n.
    induct n.
    - simplify. equality.
    - simplify. rewrite <- IHn. equality.
  Qed.

  (* Generalizing from inc_stepper, a common way to transform streams is
   * to apply some function to each element. We call this `map_stepper`
   * by analogy to the List.map function described in lecture.
   *
   * PROBLEM 9 [5 points, 1-2 LOC for defn, ~10 tactics for proof]
   * Complete the definition of map_stepper. Then prove the lemma below.
   *)
  (* insert `:=` on the next line before the '.', then add your solution. *)
  Definition map_stepper {T A B} (f : A -> B) (step : stepper T A) : stepper T B
    := fun s =>
      let (e, s') := step s in
      ((f e), s').

  Compute run_stepper (map_stepper (fun n => 7 * n + 3) nats) 10 0.
  (* should be: [3; 10; 17; 24; 31; 38; 45; 52; 59; 66] *)
  (* Note: This line won't work correctly until you've implemented `map_stepper` above. *)

  Lemma map_run_stepper :
    forall T A B (step : stepper T A) (f : A -> B) n s,
      run_stepper (map_stepper f step) n s = List.map f (run_stepper step n s).
  Proof.
    induct n.
    - simplify. equality.
    - simplify.
      cases (map_stepper f step s).
      cases (step s).
      simplify.
      rewrite IHn.
      unfold map_stepper in Heq.
      rewrite Heq0 in Heq.
      equality.
  Qed.

  (* Here's another stream transformer. *)
  Definition mystery_transformer {T A} (step: stepper T A) : stepper T A :=
    fun s =>
      let (a, s') := step s in
      let (_, s'') := step s' in
      (a, s'').
  (* PROBLEM 10 [5 points, 1 sentence of English]
   * Briefly describe what this transformer does.
   *)
  (* It emits an element for the current state, then advances the state *two*
     steps.  The element for the second step is skipped. *)

  Fixpoint list_skip A (l : list A) : list A :=
    match l with
    | [] => []
    | x' :: l' =>
      match l' with
      | [] => [x']
      | x'' :: l'' => x' :: list_skip A l''
      end
  end.

  Compute list_skip nat (1::2::3::4::5::6::[]).
  Compute run_stepper nats 6 1.
  Compute list_skip nat (run_stepper nats 6 1).
  Compute run_stepper (mystery_transformer nats) 3 1.

  (* PROBLEM 11 [10 points]
   * State and prove a lemma characterizing mystery_transformer in terms of
   * a list transformation.
   *
   * Hint: If the standard library does not contain a corresponding list
   * transfromation, you may need to define it yourself!
   *)
  Lemma run_stepper_mystery_transformer :
    forall T A (step : stepper T A) n s,
      run_stepper (mystery_transformer step) n s =
      list_skip A (run_stepper step (n + n) s).
  Proof.
    induct n.
    - simplify. equality.
    - simplify.  
      cases(mystery_transformer step s). cases(step s). rewrite IHn.
      unfold mystery_transformer in Heq. rewrite Heq0 in Heq.
      cases(list_skip A).
      + simplify.
  Admitted.

  (* Above, we defined a function map_stepper by analogy to List.map.
   * What about an analogue to List.filter?
   *)

  (* PROBLEM 12 [5 points, ~1 LOC OR ~1 sentence]
   * Define filter_stepper or explain intuitively why it cannot be defined.
   *)
  Definition filter_stepper {T A} (f : A -> bool) (step : stepper T A) : stepper T A.
  (* filter_stepper is not guaranteed to ever halt (for example, if the predicate always
     returns False). *)
  Admitted.
End StreamsAsSteppers.








(* --- Section 3: Practice with interpreters --- *)

Module MoreInterpreters.

  (* Here are a bunch of copied definitions from Frap's Interpreters.v *)

  Inductive arith : Set :=
  | Const (n : nat)
  | Var (x : var)
  | Plus (e1 e2 : arith)
  | Minus (e1 e2 : arith)
  | Times (e1 e2 : arith).

  Definition valuation := fmap var nat.

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

  Inductive cmd :=
  | Skip
  | Assign (x : var) (e : arith)
  | Sequence (c1 c2 : cmd)
  | Repeat (e : arith) (body : cmd).

  Fixpoint selfCompose {A} (f : A -> A) (n : nat) : A -> A :=
    match n with
    | O => fun x => x
    | S n' => fun x => selfCompose f n' (f x)
    end.

  Fixpoint exec (c : cmd) (v : valuation) : valuation :=
    match c with
    | Skip => v
    | Assign x e => v $+ (x, interp e v)
    | Sequence c1 c2 => exec c2 (exec c1 v)
    | Repeat e body => selfCompose (exec body) (interp e v) v
    end.

  Coercion Const : nat >-> arith.
  Coercion Var : var >-> arith.
  Infix "+" := Plus : arith_scope.
  Infix "-" := Minus : arith_scope.
  Infix "*" := Times : arith_scope.
  Delimit Scope arith_scope with arith.
  Notation "x <- e" := (Assign x e%arith) (at level 75).
  Infix ";" := Sequence (at level 76).
  Notation "'repeat' e 'doing' body 'done'" := (Repeat e%arith body) (at level 75).

  (* End of copied stuff :) *)


  (* Here's a command to compute fibonacci numbers based on the value of "input". *)
  Definition fibonacci :=
    "current" <- 1;
    "next" <- 1;
    "tmp" <- 1;
    repeat "input" doing
      "tmp" <- "next" + "current";
      "current" <- "next";
      "next" <- "tmp"
    done;
    "output" <- "current".

  (* And here's a functional implementation in Coq that closely matches the
   * control flow of the above command's main loop. *)
  Fixpoint fib_tail (n a b : nat) : nat :=
    match n with
    | O => b
    | S n' => fib_tail n' (a + b) a
    end.


  (* PROBLEM 13 [25 points, ~5 tactics + 1 helper lemma requiring ~10 LOC to state and ~10 tactics to prove]
   * Prove that the `fibonacci` command agrees with the functional implementation fib_tail.
   *
   * Hint: Your final proof should not use induction. Instead, state and prove (by induction) a
   * lemma about the body of the command's main loop. The hard part of this problem is getting
   * the statement of your helper lemma correct. It needs to imply fibonacci_ok and be strong
   * enough to be proved by induction.
   *
   * Hint: It may help to review the proof of `factorial` in Interpreters.v, especially
   * the lemma about the body of its main loop.
   *)
  Definition fibonacci_body :=
    "tmp" <- "next" + "current";
    "current" <- "next";
    "next" <- "tmp".

  Lemma fibonacci_ok' : forall count current next v,
    v $? "current" = Some current
    -> v $? "next" = Some next
    -> v $? "tmp" = Some next
    -> selfCompose (exec fibonacci_body) count v
       = v $+ ("current", fib_tail count next current)
           $+ ("next", (fib_tail (count + 1) next current))
           $+ ("tmp", (fib_tail (count + 1) next current)).
  Proof.
    induct count; simplify.
    - maps_equal.
      + trivial.
      + rewrite H0. equality.
      + rewrite H. equality.
    - rewrite H0. rewrite H.
      rewrite (IHcount next (next + current)).
      maps_equal.
      + simplify. equality.
      + simplify. equality.
      + simplify. equality.
  Qed.

  Theorem fibonacci_ok :
    forall v input,
      v $? "input" = Some input ->
      exec fibonacci v $? "output" = Some (fib_tail input 1 1).
  Proof.
    simplify.
    rewrite H.
    rewrite (fibonacci_ok' input 1 1).
    + simplify. equality.
    + simplify. equality.
    + simplify. equality.
    + simplify. equality.
  Qed.

End MoreInterpreters.

(* --- The End --- *)

(*
 * This is the end of homework 2.
 *
 * To submit your homework, please follow the instructions at the end of the
 * README.md file in this directory.
 *
 * Please also see the README.md file to read about how we will grade this homework.
 *)

(* --- Challenge problem --- *)

(*
 * There's one more challenge problem below, which you can try if you like.
 * It will not be worth any points, now or ever.
 *
 * You already have all the techniques you need to solve it, but it does require
 * some thought.
 *)

(* Above, we defined `fib_tail` as a purely functional specification of the
 * command `fibonacci`.  But `fib_tail` is perhaps not the most natural way
 * of specifying the Fibonacci numbers.  Instead, we might expect the
 * following textbook definition.
 *)
Fixpoint fib (n : nat) :=
  match n with
  | O => 1
  | S n' =>
    match n' with
    | O => 1
    | S n'' => fib n' + fib n''
    end
  end.
Compute fib 4.

Fixpoint fib_tail (n a b : nat) : nat :=
  match n with
  | O => b
  | S n' => fib_tail n' (a + b) a
  end.
Compute fib_tail 4 1 1.

(* PROBLEM 14 [0 points, ~6 tactics + 1 helper lemma needing ~10 tactics]
 * Prove that fib and fib_tail agree, as follows.
 *
 * Hint: As you might expect by this point, it's not provable directly by induction,
 * so you'll need a helper lemma or two.  I have seen several totally different ways
 * to prove this fact, so be creative and try to find something that makes sense to you!
 *)
Theorem fib_tail_ok :
  forall n,
    fib_tail n 1 1 = fib n.
Proof.
  (* YOUR CODE HERE *)
Admitted.
