(** * Multiset:  Insertion Sort Verified With Multisets *)

(** Our specification of [sorted] in [Sort] was based in
    part on permutations, which enabled us to express the idea that
    sorting rearranges list elements but does not add or remove any.

    Another way to express that idea is to use multisets, aka bags.  A
    _set_ is like a list in which element order is irrelevant, and in
    which no duplicate elements are permitted. That is, an element can
    either be _in_ the set or not in the set, but it can't be in the
    set multiple times.  A _multiset_ relaxes that restriction: an
    element can be in the multiset multiple times.  The number of
    times the element occurs in the multiset is the element's
    _multiplicity_. *)

(** For example:

    - [{1, 2}] is a set, and is the same as set [{2, 1}].

    - [[1; 1; 2]] is a list, and is different than list [[2; 1; 1]].

    - [{1, 1, 2}] is a multiset and the same as multiset [{2, 1, 1}].

    In this chapter we'll explore using multisets to specify
    sortedness. *)

From Coq Require Import Strings.String.  (* for manual grading *)
From Coq Require Import FunctionalExtensionality.
From VFA Require Import Perm.
From VFA Require Import Sort.

(* ################################################################# *)
(** * Multisets *)

(** We will represent multisets as functions: if [m] is a
    multiset, then [m n] will be the multiplicity of [n] in [m].
    Since we are sorting lists of natural numbers, the type of
    multisets would be [nat -> nat]. The input is the value, the output is
    its multiplicity.  To help avoid confusion between those two uses
    of [nat], we'll introduce a synonym, [value]. *)

Definition value := nat.

Definition multiset := value -> nat.

(** The [empty] multiset has multiplicity [0] for every value. *)

Definition empty : multiset :=
  fun x => 0.

(** Multiset [singleton v] contains only [v], and exactly once. *)

Definition singleton (v: value) : multiset :=
  fun x => if x =? v then 1 else 0.

(** The union of two multisets is their _pointwise_ sum. *)

Definition union (a b : multiset) : multiset :=
  fun x => a x + b x.

(** **** Exercise: 1 star, standard (union_assoc) *)

(** Prove that multiset union is associative.

    To prove that one multiset equals another we use the axiom of
    functional extensionality, which was introduced in
    [Logic]. We begin the proof below by using Coq's tactic
    [extensionality], which applies that axiom.*)

Lemma union_assoc: forall a b c : multiset,
   union a (union b c) = union (union a b) c.
Proof.
  intros.
  extensionality x.
  unfold union. lia.
Qed.

(** [] *)

(** **** Exercise: 1 star, standard (union_comm) *)

(** Prove that multiset union is commutative. *)

Lemma union_comm: forall a b : multiset,
   union a b = union b a.
Proof.
  intros. extensionality x.
  unfold union. lia.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (union_swap) *)

(** Prove that the multisets in a nested union can be swapped.
    You do not need [extensionality] if you use the previous
    two lemmas. *)

Lemma union_swap : forall a b c : multiset,
    union a (union b c) = union b (union a c).
Proof.
  intros. repeat rewrite union_assoc.
  rewrite union_comm with a b. reflexivity.
Qed.

(** [] *)

(** Note that this is not an efficient implementation of multisets.
    We wouldn't want to use it for programs with high performance
    requirements.  But we are using multisets for specifications, not
    for programs.  We don't intend to build large multisets, only to
    use them in verifying algorithms such as insertion sort.  So this
    inefficiency is not a problem. *)

(* ################################################################# *)
(** * Specification of Sorting *)

(** A sorting algorithm must rearrange the elements into a list
    that is totally ordered.  Using multisets, we can restate that as:
    the algorithm must produce a list _with the same multiset of
    values_, and this list must be totally ordered. Let's formalize
    that idea. *)

(** The _contents_ of a list are the elements it contains, without
    any notion of order. Function [contents] extracts the contents
    of a list as a multiset. *)

Fixpoint contents (al: list value) : multiset :=
  match al with
  | [] => empty
  | a :: bl => union (singleton a) (contents bl)
  end.

(** The insertion-sort program [sort] from [Sort] preserves
    the contents of a list.  Here's an example of that: *)

Example sort_pi_same_contents:
  contents (sort [3;1;4;1;5;9;2;6;5;3;5]) = contents [3;1;4;1;5;9;2;6;5;3;5].
Proof.  
  extensionality x. 
  repeat (destruct x; try reflexivity).
  (* Why does this work? Try it step by step, without [repeat]. *)
Qed.

(** A sorting algorithm must preserve contents and totally order the
    list. *)

Definition is_a_sorting_algorithm' (f: list nat -> list nat) := forall al,
    contents al = contents (f al) /\ sorted (f al).

(** That definition is similar to [is_a_sorting_algorithm] from [Sort],
    except that we're now using [contents] instead of [Permutation]. *)

(* ################################################################# *)
(** * Verification of Insertion Sort *)

(** The following series of exercises will take you through a
    verification of insertion sort using multisets. *)

(** **** Exercise: 3 stars, standard (insert_contents) *)

(** Prove that insertion sort's [insert] function produces the same
    contents as merely prepending the inserted element to the front of
    the list.

    Proceed by induction.  You do not need [extensionality] if you
    make use of the above lemmas about [union]. *)

Lemma insert_contents: forall x l,
     contents (insert x l) = contents (x :: l).
Proof with simpl.
  intros. induction l; try reflexivity...
  destruct (x <=? a); try reflexivity...
  rewrite IHl... apply union_swap.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard (sort_contents) *)

(** Prove that insertion sort preserves contents. Proceed by
    induction.  Make use of [insert_contents]. *)

Theorem sort_contents: forall l,
    contents l = contents (sort l).
Proof.
  intros. induction l; try reflexivity.
  simpl. rewrite IHl. rewrite insert_contents.
  reflexivity.
Qed.

(** [] *)

(** **** Exercise: 1 star, standard (insertion_sort_correct) *)

(** Finish the proof of correctness! *)

Theorem insertion_sort_correct :
  is_a_sorting_algorithm' sort.
Proof.
  split. apply sort_contents. apply sort_sorted.
Qed.

(** [] *)

(** **** Exercise: 1 star, standard (permutations_vs_multiset)

    Compare your proofs of [insert_perm, sort_perm] with your proofs
    of [insert_contents, sort_contents].  Which proofs are simpler?

      - [ ] easier with permutations
      - [ ] easier with multisets
      - [ ] about the same

   Regardless of "difficulty", which do you prefer or find easier to
   think about?
      - [ ] permutations
      - [ ] multisets

   Put an X in one box in each list. *)

(* Do not modify the following line: *)
Definition manual_grade_for_permutations_vs_multiset : option (nat*string) := None.

(** [] *)

(* ################################################################# *)
(** * Equivalence of Permutation and Multiset Specifications *)

(** We have developed two specifications of sorting, one based
    on permutations ([is_a_sorting_algorithm]) and one based on
    multisets ([is_a_sorting_algorithm']).  These two specifications
    are actually equivalent, which will be the final theorem in this
    chapter.

    One reason for that equivalence is that permutations and multisets
    are closely related.  We'll begin by proving:

        Permutation al bl <-> contents al = contents bl

    The forward direction is relatively easy, but the backward
    direction is surprisingly difficult.
 *)

(* ================================================================= *)
(** ** The Forward Direction *)

(** **** Exercise: 3 stars, standard (perm_contents) *)

(** The forward direction is the easier one. Proceed by induction on
    the evidence for [Permutation al bl]: *)

Lemma perm_contents: forall al bl : list nat,
    Permutation al bl -> contents al = contents bl.
Proof.
  intros. induction H.
  - reflexivity.
  - simpl. rewrite IHPermutation. reflexivity.
  - simpl. rewrite union_swap. reflexivity.
  - rewrite IHPermutation1. assumption.
Qed.

(** [] *)

(* ================================================================= *)
(** ** The Backward Direction (Advanced) *)

(** The backward direction is surprisingly difficult.  This proof
    approach is due to Zhong Sheng Hu.  The first three lemmas are
    used to prove the fourth one.  Don't forget that [union],
    [singleton], and [empty] must be explicitly unfolded to access
    their definitions. *)

(** **** Exercise: 2 stars, advanced (contents_nil_inv) *)
Lemma contents_nil_inv : forall l, (forall x, 0 = contents l x) -> l = nil.
Proof.
  intro. destruct l; intros; try reflexivity.
  exfalso. specialize H with v. simpl in H. 
  unfold union in H. unfold singleton in H.
  rewrite Nat.eqb_refl in H. simpl in H. inversion H.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (contents_cons_inv) *)
Lemma contents_cons_inv : forall l x n,
    S n = contents l x ->
    exists l1 l2,
      l = l1 ++ x :: l2
      /\ contents (l1 ++ l2) x = n.
Proof.
  induction l; intros; try discriminate.
  simpl in H. unfold union in H. unfold singleton in H.
  destruct (x =? a) eqn : E.
  - injection H; intros. exists [], l. split.
    + rewrite Nat.eqb_eq in E; subst. reflexivity.
    + simpl. symmetry. assumption.
  - rewrite Nat.add_0_l in H. apply IHl in H.
    destruct H as [l1 [l2 [H1 H2]]]. exists (a :: l1), l2. split.
    + subst. reflexivity.
    + simpl. unfold union. unfold singleton.
      rewrite E. rewrite Nat.add_0_l. assumption.
Qed.
(** [] *)

(** **** Exercise: 2 stars, advanced (contents_insert_other) *)
Lemma contents_insert_other : forall l1 l2 x y,
    y <> x -> contents (l1 ++ x :: l2) y = contents (l1 ++ l2) y.
Proof.
  induction l1; intros; simpl; unfold union,singleton.
  -  apply Nat.eqb_neq in H. rewrite H. 
    rewrite Nat.add_0_l. reflexivity.
  - f_equal. eapply IHl1 in H. apply H.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (contents_perm) *)
Lemma contents_insert_same : forall l1 l2 x,
    contents (l1 ++ x :: l2) x = S (contents (l1 ++ l2) x).
Proof.
  induction l1; intros; simpl; unfold union, singleton.
  - rewrite Nat.eqb_refl. reflexivity.
  - rewrite plus_n_Sm. f_equal. apply IHl1.
Qed.

Lemma contents_app_comm : forall l1 l2,
  contents (l1 ++ l2) = contents (l2 ++ l1).
Proof.
  induction l1; intros.
  - rewrite app_nil_r. reflexivity.
  - extensionality x. destruct (x =? a) eqn : E;
    simpl; unfold union,singleton.
    + rewrite E. apply Nat.eqb_eq in E; subst.
      rewrite contents_insert_same. simpl.
      rewrite IHl1. reflexivity.
    + rewrite E. apply Nat.eqb_neq in E.
      rewrite (contents_insert_other _ _ _ _ E).
      rewrite Nat.add_0_l. rewrite IHl1. reflexivity.
Qed.

Lemma contents_perm: forall al bl,
    contents al = contents bl -> Permutation al bl.
Proof.
  intros al bl H0.
  assert (H: forall x, contents al x = contents bl x).
  { rewrite H0. auto. }
  clear H0.
  generalize dependent bl. induction al; intros.
  - simpl in H. unfold empty in H. 
    apply contents_nil_inv in H; subst. constructor.
  - specialize H with a as H0. simpl in H0. 
    unfold union, singleton in H0. rewrite Nat.eqb_refl in H0.
    apply contents_cons_inv in H0.
    destruct H0 as [l1 [l2 [H1 H2]]]; subst.
    rewrite contents_app_comm in H. simpl in H.
    unfold union in H. 
    assert(forall x, contents al x = contents (l2 ++ l1) x).
    { intros. specialize H with x. unfold singleton in H.
      destruct (x =? a) eqn : E; [injection H; intros | ]; auto. }
    specialize IHal with (l1 ++ l2). rewrite contents_app_comm in H0.
    apply IHal in H0. rewrite Permutation_app_comm. simpl.
    apply perm_skip. rewrite Permutation_app_comm. assumption.
Qed.
(** [] *)

(* ================================================================= *)
(** ** The Main Theorem *)

(** With both directions proved, we can establish the correspondence
    between multisets and permutations. *)

(** **** Exercise: 1 star, standard (same_contents_iff_perm) *)

(** Use [contents_perm] (even if you haven't proved it) and
    [perm_contents] to quickly prove the next theorem. *)

Theorem same_contents_iff_perm: forall al bl,
    contents al = contents bl <-> Permutation al bl.
Proof.
  split. apply contents_perm. apply perm_contents.
Qed.

(** [] *)

(** Therefore the two specifications are equivalent. *)

(** **** Exercise: 2 stars, standard (sort_specifications_equivalent) *)

Theorem sort_specifications_equivalent: forall sort,
    is_a_sorting_algorithm sort <-> is_a_sorting_algorithm' sort.
Proof.
  intros; split; intros.
  - split; destruct H with al. apply same_contents_iff_perm in H0.
    apply H0. apply H1.
  - split; destruct H with al. apply same_contents_iff_perm in H0.
    apply H0. apply H1.
Qed.

(** [] *)

(** That means we can verify sorting algorithms using either
    permutations or multisets, whichever we find more convenient. *)

(* 2024-06-14 22:11 *)
