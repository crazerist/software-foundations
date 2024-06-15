(** * BagPerm:  Insertion Sort With Bags *)

(** We have seen how to specify algorithms on "collections", such as
    sorting algorithms, using [Permutation]s.  Instead of using
    permutations, another way to specify these algorithms is to use
    _bags_ (also called _multisets_), which we introduced in [Lists].
    A _set_ of values is like a list with no repeats where
    the order does not matter.  A _multiset_ is like a list, possibly
    with repeats, where the order does not matter.  Whereas the principal
    query on a set is whether a given element appears in it, the
    principal query on a bag is _how many_ times a given element appears 
    in it. *)

From Coq Require Import Strings.String. (* for manual grading *)
From Coq Require Import Setoid Morphisms.
From VFA Require Import Perm.
From VFA Require Import Sort.

(** To keep this chapter more self-contained, 
we restate the critical definitions from [Lists].  *)
Definition bag := list nat.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: t =>
      (if h =? v then 1 else 0) + count v t
  end.

(** We will say two bags are _equivalent_ if they have the same number
    of copies of every possible element. *)

Definition bag_eqv (b1 b2: bag) : Prop :=
  forall n, count n b1 = count n b2. 

(** **** Exercise: 2 stars, standard (bag_eqv_properties) *)

(* It is easy to prove [bag_eqv] is an equivalence relation. *)

Lemma bag_eqv_refl : forall b, bag_eqv b b.
Proof.
  unfold bag_eqv; intros. reflexivity.
Qed.

Lemma bag_eqv_sym: forall b1 b2, bag_eqv b1 b2 -> bag_eqv b2 b1. 
Proof.
  unfold bag_eqv; intros. rewrite H. reflexivity.
Qed.

Lemma bag_eqv_trans: forall b1 b2 b3, bag_eqv b1 b2 -> bag_eqv b2 b3 -> bag_eqv b1 b3.
Proof.
  unfold bag_eqv; intros. rewrite H, H0. reflexivity.
Qed.

(** The following little lemma is handy in a couple of places. *)

Lemma bag_eqv_cons : forall x b1 b2, bag_eqv b1 b2 -> bag_eqv (x::b1) (x::b2).
Proof.
  unfold bag_eqv; intros. simpl. rewrite H. reflexivity.
Qed.

Lemma bag_eqv_cons_comm :
  forall x1 x2 b,
  bag_eqv (x1 :: x2 :: b) (x2 :: x1 :: b).
Proof.
  unfold bag_eqv; intros; simpl. lia.
Qed.
(** [] *)

(* ################################################################# *)
(** * Correctness *)

(** A sorting algorithm must rearrange the elements into a list that
    is totally ordered.  But let's say that a different way: the
    algorithm must produce a list _with the same multiset of values_,
    and this list must be totally ordered. *)

Definition is_a_sorting_algorithm' (f: list nat -> list nat) :=
  forall al, bag_eqv al (f al) /\ sorted (f al).

(** **** Exercise: 3 stars, standard (insert_bag)

    First, prove the auxiliary lemma [insert_bag], which will be
    useful for proving [sort_bag] below.  Your proof will be by
    induction.  *)

Lemma insert_bag: forall x l, bag_eqv (x::l) (insert x l).
Proof.
  induction l; intros; simpl.
  - apply bag_eqv_refl.
  - destruct (x <=? a) eqn : E.
    + apply bag_eqv_refl.
    + apply bag_eqv_trans with (a :: x :: l).
      apply bag_eqv_cons_comm. apply bag_eqv_cons.
      apply IHl.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (sort_bag)

    Now prove that sort preserves bag contents. *)
Theorem sort_bag: 
  forall l, bag_eqv l (sort l).
Proof.
  induction l; simpl.
  - apply bag_eqv_refl.
  - eapply bag_eqv_trans with (a :: (sort l)).
    + apply bag_eqv_cons. apply IHl.
    + apply insert_bag.
Qed.
(** [] *)

(** Now we wrap it all up.  *)

Theorem insertion_sort_correct:
  is_a_sorting_algorithm' sort.
Proof.
split. apply sort_bag. apply sort_sorted.
Qed.

(** **** Exercise: 1 star, standard (permutations_vs_multiset)

    Compare your proofs of [insert_perm, sort_perm] with your proofs
    of [insert_bag, sort_bag].  Which proofs are simpler?

      - [ ] easier with permutations,
      - [ ] easier with multisets
      - [ ] about the same.

   Regardless of "difficulty", which do you prefer / find easier to
   think about?
      - [ ] permutations or
      - [ ] multisets

   Put an X in one box in each list. *)
(* Do not modify the following line: *)
Definition manual_grade_for_permutations_vs_multiset : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Permutations and Multisets *)

(** The two specifications of insertion sort are equivalent.  One
    reason is that permutations and multisets are closely related.
    We're going to prove:

       [Permutation al bl <-> bag_eqv al bl.] *)

(** **** Exercise: 3 stars, standard (perm_bag)

    The forward direction is straighforward, by induction on the evidence for
    [Permutation]: *)
Lemma perm_bag:
  forall al bl : list nat,
   Permutation al bl -> bag_eqv al bl. 
Proof.
  intros. induction H.
  - apply bag_eqv_refl.
  - apply bag_eqv_cons. apply IHPermutation.
  - apply bag_eqv_cons_comm.
  - eapply bag_eqv_trans. apply IHPermutation1. assumption.
Qed.
(** [] *)

(** The other direction,
    [bag_eqv al bl -> Permutation al bl],
    is surprisingly difficult.  
    This proof approach is due to Zhong Sheng Hu.
    The first three lemmas are used to prove the fourth one. *)

(** **** Exercise: 2 stars, advanced (bag_nil_inv) *)
Lemma bag_nil_inv : forall b, bag_eqv [] b -> b = []. 
Proof.
  intros. destruct b; try reflexivity.
  unfold bag_eqv in H. specialize H with n; simpl in H.
  rewrite Nat.eqb_refl in H. inversion H.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (bag_cons_inv) *)
Lemma bag_cons_inv : forall l x n,
    S n = count x l ->
    exists l1 l2,
      l = l1 ++ x :: l2
      /\ count x (l1 ++ l2) = n.
Proof.
  induction l; intros; simpl in *.
  - inversion H.
  - destruct (a =? x) eqn : E.
    + apply Nat.eqb_eq in E; subst. injection H; intros.
      exists [], l. simpl. split. reflexivity. 
      symmetry. apply H0.
    + simpl in H. apply IHl in H. destruct H as [l1 [l2 [H1 H2]]].
      subst. exists (a :: l1), l2. split. reflexivity.
      simpl. rewrite E. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, advanced (count_insert_other) *)
Lemma count_insert_other : forall l1 l2 x y,
    y <> x -> count y (l1 ++ x :: l2) = count y (l1 ++ l2).
Proof.
  induction l1; intros; simpl.
  - apply not_eq_sym in H. apply Nat.eqb_neq in H. 
    rewrite H. reflexivity.
  - f_equal. apply IHl1. apply H.
Qed.

Lemma count_insert_same :
  forall x l1 l2,
  count x (l1 ++ x :: l2) = S (count x (l1 ++ l2)).
Proof.
  induction l1; intros; simpl.
  - rewrite Nat.eqb_refl. reflexivity.
  - rewrite plus_n_Sm. f_equal. apply IHl1.
Qed.

Lemma count_app_comm :
  forall n l1 l2,
  count n (l1 ++ l2) = count n (l2 ++ l1).
Proof.
  induction l1; intros; simpl.
  - rewrite app_nil_r. apply bag_eqv_refl.
  - unfold bag_eqv; intros; simpl. destruct (a =? n) eqn : E.
    + apply Nat.eqb_eq in E; subst. rewrite count_insert_same.
      simpl. f_equal. apply IHl1.
    + apply Nat.eqb_neq in E. apply not_eq_sym in E. 
      rewrite (count_insert_other _ _ _ _ E).
      rewrite Nat.add_0_l. apply IHl1.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (bag_perm) *)
Lemma bag_perm:
  forall al bl, bag_eqv al bl -> Permutation al bl.
Proof.
  induction al; intros.
  - apply bag_nil_inv in H; subst. constructor.
  - unfold bag_eqv in H. specialize H with a as H0.
    simpl in H0. rewrite Nat.eqb_refl in H0. simpl in H0.
    apply bag_cons_inv in H0. destruct H0 as [l1 [l2 [H1 H2]]].
    subst. 
    assert (forall n, count n al = count n (l2 ++ l1)).
    { intros. specialize H with n. rewrite count_app_comm in H.
      simpl in H. apply Nat.add_cancel_l in H. assumption. }
    apply (IHal (l2 ++ l1)) in H0. rewrite Permutation_app_comm.
    simpl. constructor. apply H0.
Qed.
(** [] *)

(* ################################################################# *)
(** * The Main Theorem: Equivalence of Multisets and Permutations *)
Theorem bag_eqv_iff_perm:
  forall al bl, bag_eqv al bl <-> Permutation al bl.
Proof.
  intros. split. apply bag_perm. apply perm_bag.
Qed.

(** Therefore, it doesn't matter whether you prove your sorting
    algorithm using the Permutations method or the multiset method. *)

Corollary sort_specifications_equivalent:
    forall sort, is_a_sorting_algorithm sort <->  is_a_sorting_algorithm' sort.
Proof.
  unfold is_a_sorting_algorithm, is_a_sorting_algorithm'.
  split; intros;
  destruct (H al); split; auto;
  apply bag_eqv_iff_perm; auto.
Qed.

(** Date *)

(* 2023-06-15 15:02 *)
