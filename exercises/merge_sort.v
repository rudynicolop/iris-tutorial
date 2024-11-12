From stdpp Require Export sorting.
From iris.heap_lang Require Import array lang proofmode notation par.

(* ################################################################# *)
(** * Case Study: Merge Sort *)

(* ================================================================= *)
(** ** Implementation *)

(**
  Let us implement a simple multithreaded merge sort on arrays. Merge
  sort consists of splitting the array in half until we are left with
  pieces of size [0] or [1]. Then, each pair of pieces is merged into a
  new sorted array.
*)

(**
  We begin by implementing a function which merges two arrays [a1] and
  [a2] of lengths [n1] and [n2] into an array [b] of length [n1 + n2].
*)
Definition merge : val :=
  rec: "merge" "a1" "n1" "a2" "n2" "b" :=
  (** If [a1] is empty, we simply copy the second [a2] into [b]. *)
  if: "n1" = #0 then
    array_copy_to "b" "a2" "n2"
  (** Likewise if [a2] is empty instead. *)
  else if: "n2" = #0 then
    array_copy_to "b" "a1" "n1"
  else
  (**
    Otherwise, we compare the first elements of [a1] and [a2]. The
    smallest is removed and written to [b]. Rinse and repeat.
  *)
    let: "x1" := !"a1" in
    let: "x2" := !"a2" in
    if: "x1" ≤ "x2" then
      "b" <- "x1";;
      "merge" ("a1" +ₗ #1) ("n1" - #1) "a2" "n2" ("b" +ₗ #1)
    else
      "b" <- "x2";;
      "merge" "a1" "n1" ("a2" +ₗ #1) ("n2" - #1) ("b" +ₗ #1).

(**
  To sort an array [a], we split the array in half, sort each sub-array
  recursively on separate threads, and merge the sorted sub-arrays using
  [merge], writing the elements back into the array.
*)
Definition merge_sort_inner : val :=
  rec: "merge_sort_inner" "a" "b" "n" :=
  if: "n" ≤ #1 then #()
  else
    let: "n1" := "n" `quot` #2 in
    let: "n2" := "n" - "n1" in
    ("merge_sort_inner" "b" "a" "n1" ||| "merge_sort_inner" ("b" +ₗ "n1") ("a" +ₗ "n1") "n2");;
    merge "b" "n1" ("b" +ₗ "n1") "n2" "a".

(**
  HeapLang requires array allocations to contain at least one element.
  As such, we need to treat this case separately.
*)
Definition merge_sort : val :=
  λ: "a" "n",
  if: "n" = #0 then #()
  else
    let: "b" := AllocN "n" #() in
    array_copy_to "b" "a" "n";;
    merge_sort_inner "a" "b" "n".

(**
  Our desired specification will be that [merge_sort] produces a new
  sorted array which, importantly, is a permutation of the input.
*)

(* ================================================================= *)
(** ** Specifications *)

Section proofs.
Context `{!heapGS Σ, !spawnG Σ}.

(**
  We begin by giving a specification for the [merge] function. To merge
  two arrays [a1] and [a2], we require that they are both already
  sorted. Furthermore, we need the result array [b] to have enough
  space, though we don't care what it contains.
*)
Lemma merge_spec (a1 a2 b : loc) (l1 l2 : list Z) (l : list val) :
  {{{
    a1 ↦∗ ((λ x : Z, #x) <$> l1) ∗
    a2 ↦∗ ((λ x : Z, #x) <$> l2) ∗ b ↦∗ l ∗
    ⌜StronglySorted Z.le l1⌝ ∗
    ⌜StronglySorted Z.le l2⌝ ∗
    ⌜length l = (length l1 + length l2)%nat⌝
  }}}
    merge #a1 #(length l1) #a2 #(length l2) #b
  {{{(l : list Z), RET #();
    a1 ↦∗ ((λ x : Z, #x) <$> l1) ∗
    a2 ↦∗ ((λ x : Z, #x) <$> l2) ∗
    b ↦∗ ((λ x : Z, #x) <$> l) ∗
    ⌜StronglySorted Z.le l⌝ ∗
    ⌜l1 ++ l2 ≡ₚ l⌝
  }}}.
Proof.
  iIntros (Φ) "(Ha1 & Ha2 & Hb & Hl1 & Hl2 & Hlen) HΦ".
  iLöb as "IH" forall (a1 a2 b l1 l2 l).
  iDestruct "Hl1" as %Hl1.
  iDestruct "Hl2" as %Hl2.
  iDestruct "Hlen" as %Hlen.
  wp_rec. wp_pures.
  destruct l1 as [| x1 l1].
  { rewrite bool_decide_eq_true_2 //. wp_pures.
    wp_apply (wp_array_copy_to with "[$Hb $Ha2]"); first by f_equal.
    1: by rewrite fmap_length.
    iIntros "[Hb Ha2]". iApply "HΦ". by iFrame "% ∗". }
  rewrite bool_decide_eq_false_2 //. wp_pures.
  destruct l2 as [| x2 l2].
  { rewrite bool_decide_eq_true_2 //. wp_pures. simpl in * |-.
    wp_apply (wp_array_copy_to with "[$Hb $Ha1]"); first lia.
    1: by rewrite fmap_length.
    iIntros "[Hb Ha1]". iApply "HΦ". iFrame "∗ %".
    by rewrite app_nil_r. }
  rewrite bool_decide_eq_false_2 //. wp_pures.
  destruct l as [| x l]; simpl in Hlen; first lia.
  apply StronglySorted_inv in Hl1 as [Hx1 Hl1].
  apply StronglySorted_inv in Hl2 as [Hx2 Hl2].
  injection Hlen as Hlen.
  do 2 rewrite {1}fmap_cons.
  iDestruct (array_cons with "Ha1") as "[Ha1_hd Ha1_tl]".
  iDestruct (array_cons with "Ha2") as "[Ha2_hd Ha2_tl]".
  iDestruct (array_cons with "Hb") as "[Hb_hd Hb_tl]".
  wp_load. wp_let. wp_load. wp_pures.
  destruct (decide (x1 ≤ x2)%Z) as [Hx1_le_x2 | Hx1_nle_x2].
  - rewrite bool_decide_eq_true_2 //. wp_pures.
    wp_store. wp_pures.
    iCombine "Ha2_hd Ha2_tl" as "Ha2".
    rewrite -array_cons.
    replace (Z.of_nat (S (length l1)) - 1)%Z with (Z.of_nat (length l1)) by lia.
    iSpecialize ("IH" $! (a1 +ₗ 1) a2 (b +ₗ 1) l1 (x2 :: l2) l with "Ha1_tl").
Admitted.

(**
  With this, we can prove that sort actually sorts the output.
*)
Lemma merge_sort_inner_spec (a b : loc) (l : list Z) :
  {{{
    a ↦∗ ((λ x : Z, #x) <$> l) ∗
    b ↦∗ ((λ x : Z, #x) <$> l)
  }}}
    merge_sort_inner #a #b #(length l)
  {{{(l' : list Z) vs, RET #();
    a ↦∗ ((λ x : Z, #x) <$> l') ∗
    b ↦∗ vs ∗ ⌜StronglySorted Z.le l'⌝ ∗
    ⌜l ≡ₚ l'⌝ ∗
    ⌜length vs = length l'⌝
  }}}.
Proof.
  (* exercise *)
Admitted.

(**
  Finally, we lift this result to the outer [merge_sort] function.
*)
Lemma merge_sort_spec (a : loc) (l : list Z) :
  {{{a ↦∗ ((λ x : Z, #x) <$> l)}}}
    merge_sort #a #(length l)
  {{{(l' : list Z), RET #();
    a ↦∗ ((λ x : Z, #x) <$> l') ∗
    ⌜StronglySorted Z.le l'⌝ ∗
    ⌜l ≡ₚ l'⌝
  }}}.
Proof.
  (* exercise *)
Admitted.

End proofs.
