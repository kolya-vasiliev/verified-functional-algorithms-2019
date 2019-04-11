(** * Selection:  Selection Sort, With Specification and Proof of Correctness*)
(**
  This sorting algorithm works by choosing (and deleting) the smallest
  element, then doing it again, and so on.  It takes O(N^2) time.

  You should never* use a selection sort.  If you want a simple
  quadratic-time sorting algorithm (for small input sizes) you should
  use insertion sort.  Insertion sort is simpler to implement, runs
  faster, and is simpler to prove correct.   We use selection sort here
  only to illustrate the proof techniques.

     *Well, hardly ever.  If the cost of "moving" an element is _much_
  larger than the cost of comparing two keys, then selection sort is
  better than insertion sort.  But this consideration does not apply in our
  setting, where the elements are  represented as pointers into the
  heap, and only the pointers need to be moved.

  What you should really never use is bubble sort.  Bubble sort
  would be the wrong way to go.  Everybody knows that!
  https://www.youtube.com/watch?v=k4RRi_ntQc8
*)

(* ################################################################# *)
(** * The Selection-Sort Program  *)

Require Export Coq.Lists.List.
From VFA Require Import Perm.

(** Find (and delete) the smallest element in a list. *)

Fixpoint select (x: nat) (l: list nat) : nat * list nat :=
match l with
|  nil => (x, nil)
|  h::t => if x <=? h
               then let (j, l') := select x t in (j, h::l')
               else let (j,l') := select h t in (j, x::l')
end.

(** Now, selection-sort works by repeatedly extracting the smallest element,
   and making a list of the results. *)

(* Uncomment this function, and try it.
Fixpoint selsort l :=
match l with
| i::r => let (j,r') := select i r
               in j :: selsort r'
| nil => nil
end.
*)

(** _Error: Recursive call to selsort has principal argument equal
  to [r'] instead of [r]_.  That is, the recursion is not _structural_, since
  the list r' is not a structural sublist of (i::r).  One way to fix the
  problem is to use Coq's [Function] feature, and prove that
  [length(r')<length(i::r)].  Later in this chapter, we'll show that approach.

  Instead, here we solve this problem is by providing "fuel", an additional
  argument that has no use in the algorithm except to bound the
  amount of recursion.  The [n] argument, below, is the fuel. *)

Fixpoint selsort l n {struct n} :=
match l, n with
| x::r, S n' => let (y,r') := select x r
               in y :: selsort r' n'
| nil, _ => nil
| _::_, O => nil  (* Oops!  Ran out of fuel! *)
end.

(** What happens if we run out of fuel before we reach the end
   of the list?  Then WE GET THE WRONG ANSWER. *)

Example out_of_gas: selsort [3;1;4;1;5] 3 <> [1;1;3;4;5].
Proof.
simpl.
intro. inversion H.
Qed.

(** What happens if we have have too much fuel?  No problem. *)

Example too_much_gas: selsort [3;1;4;1;5] 10 = [1;1;3;4;5].
Proof.
simpl.
auto.
Qed.

(** The selection_sort algorithm provides just enough fuel. *)

Definition selection_sort l := selsort l (length l).

Example sort_pi: selection_sort [3;1;4;1;5;9;2;6;5;3;5] = [1;1;2;3;3;4;5;5;5;6;9].
Proof.
unfold selection_sort.
simpl.
reflexivity.
Qed.

(** Specification of correctness of a sorting algorithm:
   it rearranges the elements into a list that is totally ordered. *)

Inductive sorted: list nat -> Prop :=
 | sorted_nil: sorted nil
 | sorted_1: forall i, sorted (i::nil)
 | sorted_cons: forall i j l, i <= j -> sorted (j::l) -> sorted (i::j::l).

Definition is_a_sorting_algorithm (f: list nat -> list nat) :=
  forall al, Permutation al (f al) /\ sorted (f al).

(* ################################################################# *)
(** * Proof of Correctness of Selection sort *)

(** Here's what we want to prove. *)

Definition selection_sort_correct : Prop :=
    is_a_sorting_algorithm selection_sort.

(** We'll start by working on part 1, permutations. *)

(** **** Exercise: 3 stars (select_perm)  *)
Lemma select_perm: forall x l,
  let (y,r) := select x l in
   Permutation (x::l) (y::r).
Proof.

(** NOTE: If you wish, you may [Require Import Multiset] and use the  multiset
  method, along with the theorem [contents_perm].  If you do,
  you'll still leave the statement of this theorem unchanged. *)

  intros x l; revert x.
  induction l; intros.
  - simpl in *. apply Permutation_refl.
  - unfold select. 
    bdestruct (x <=? a); fold select.
    + specialize (IHl x).   
      destruct (select x l) eqn:Seq.
      apply perm_trans with (a :: n :: l0);
        try apply perm_swap.
      apply perm_trans with (a :: x :: l);
        try apply perm_swap.
      apply perm_skip.
      apply IHl.
    + specialize (IHl a).
      destruct (select a l) eqn:Seq.
      apply perm_trans with (x :: n :: l0);
        try apply perm_swap.
      apply perm_skip. apply IHl.
Qed.      

(** [] *)

(** **** Exercise: 3 stars (selection_sort_perm)  *)
Lemma selsort_perm:
  forall n,
  forall l, length l = n -> Permutation l (selsort l n).
Proof.

(** NOTE: If you wish, you may [Require Import Multiset] and use the  multiset
  method, along with the theorem [same_contents_iff_perm]. *)
  
  induction n.
  - intros. rewrite length_zero_iff_nil in H.
    subst. apply Permutation_refl.
  - intros. destruct l. inversion H.
    simpl. 
    destruct (select n0 l) eqn:Seq.
    apply perm_trans with (n1 :: l0).
    
    pose (select_perm n0 l).
    rewrite Seq in y.
    apply y.

    apply perm_skip.
    apply IHn.

    assert (length (n0::l) = (length (n1::l0))).
    { 
      apply Permutation_length.
      pose (select_perm n0 l).
      rewrite Seq in y.
      apply y.
    }

    inversion H0. inversion H. reflexivity.
Qed.

Theorem selection_sort_perm:
  forall l, Permutation l (selection_sort l).
Proof. unfold selection_sort. intros. 
  apply selsort_perm. reflexivity. Qed.

(** [] *)

(** **** Exercise: 3 stars (select_smallest)  *)
Lemma select_smallest_aux:
  forall x al y bl,
    Forall (fun z => y <= z) bl ->
    select x al = (y,bl) ->
    y <= x.
Proof. intros. pose (select_perm x al).
  rewrite H0 in y0.
  apply (Permutation_in x) in y0; try (left; constructor).
  destruct y0. 
  - subst. constructor.
  - rewrite Forall_forall in H. 
    auto.
Qed.


Theorem select_smallest:
  forall x al y bl, select x al = (y,bl) ->
     Forall (fun z => y <= z) bl.
Proof with (try assumption). intros x al; revert x; induction al; intros.
  - simpl in *. inversion H. constructor.
  - simpl in *.
    bdestruct (x <=? a).
    + destruct (select x al) eqn:?H.
      inversion H. subst n. subst bl.
      constructor. 
      apply le_trans with x...
      apply select_smallest_aux with al l...
      apply IHal with x...
      apply IHal with x...
    + destruct (select a al) eqn:?H.
      inversion H. subst n. subst bl.
      constructor.
      assert (y <= a).
      apply select_smallest_aux with al l...
      apply IHal with a...
      omega.
      apply IHal with a...
Qed.

(** [] *)

(** **** Exercise: 3 stars (selection_sort_sorted)  *)
Lemma selection_sort_sorted_aux:
  forall  y bl,
   sorted (selsort bl (length bl)) ->
   Forall (fun z : nat => y <= z) bl ->
   sorted (y :: selsort bl (length bl)).
Proof. destruct bl as [| a bl].
  constructor.
  intros. simpl in H. simpl.
  destruct (select a bl) eqn:Seq.
  constructor; try assumption. 
  rewrite Forall_forall in H0.
  apply H0.
  apply Permutation_in with (n::l).
  pose (select_perm a bl). 
  rewrite Seq in y0. apply Permutation_sym. assumption.
  constructor. reflexivity.
Qed.
 
Theorem selection_sort_sorted: forall al, sorted (selection_sort al).
Proof. intros.
  unfold selection_sort. remember (length al) as n.
  generalize dependent al. induction n; intros;
    destruct al; try constructor.
    unfold selsort. fold selsort.
    destruct (select n0 al) eqn:Seq.
    pose (select_perm n0 al). rewrite Seq in y.
    apply Permutation_length in y. 
    rewrite <- Heqn in y. inversion y.
    apply selection_sort_sorted_aux.
    rewrite <- H0. apply IHn. assumption.
    eapply select_smallest. eassumption.
Qed.
   
(* Hint: do induction on the [length] of al.
    In the inductive case, use [select_smallest], [select_perm],
    and [selection_sort_sorted_aux]. *)

(** [] *)

(** Now we wrap it all up.  *)

Theorem selection_sort_is_correct: selection_sort_correct.
Proof.
split. apply selection_sort_perm. apply selection_sort_sorted.
Qed.

(* ################################################################# *)
(** * Recursive Functions That are Not Structurally Recursive *)

(** [Fixpoint] in Coq allows for recursive functions where some
  parameter is structurally recursive: in every call, the argument
  passed at that parameter position is an immediate substructure
  of the corresponding formal parameter.  For recursive functions
  where that is not the case -- but for which you can still prove
  that they terminate -- you can use a more advanced feature of
  Coq, called [Function]. *)

Require Import Recdef.  (* needed for [Function] feature *)

Function selsort' l {measure length l} :=
match l with
| x::r => let (y,r') := select x r
               in y :: selsort' r'
| nil => nil
end.

(** When you use [Function] with [measure], it's your
  obligation to prove that the measure actually decreases,
  before you can use the function. *)

Proof.
intros.
pose proof (select_perm x r).
rewrite teq0 in H.
apply Permutation_length in H.
simpl in *; omega.
Defined.  (* Use [Defined] instead of [Qed], otherwise you
  can't compute with the function in Coq. *)

(** **** Exercise: 3 stars (selsort'_perm)  *)
Lemma selsort'_perm:
  forall n,
  forall l, length l = n -> Permutation l (selsort' l).
Proof. 
  induction n.
  - intros. rewrite length_zero_iff_nil in H.
    subst. apply Permutation_refl.
  - intros. destruct l. inversion H.
    rewrite selsort'_equation. 
    destruct (select n0 l) eqn:Seq.
    apply perm_trans with (n1 :: l0).
    
    pose (select_perm n0 l).
    rewrite Seq in y.
    apply y.

    apply perm_skip.
    apply IHn.

    assert (length (n0::l) = (length (n1::l0))).
    { 
      apply Permutation_length.
      pose (select_perm n0 l).
      rewrite Seq in y.
      apply y.
    }

    inversion H0. inversion H. reflexivity.
Qed.

(** NOTE: If you wish, you may [Require Import Multiset]
  and use the  multiset method, along with the
  theorem [same_contents_iff_perm]. *)

(** Important!  Don't unfold [selsort'], or in general, never
  unfold anything defined with [Function]. Instead, use the
  recursion equation [selsort'_equation] that is automatically
  defined by the [Function] command. *)

(** [] *)

Eval compute in selsort' [3;1;4;1;5;9;2;6;5].

(** $Date$ *)
