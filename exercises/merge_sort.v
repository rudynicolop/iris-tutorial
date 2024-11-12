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

Section perm.
  Context [A : Type].
  Variable P : A → Prop.

  Lemma perm_Forall (xs ys : list A) :
    xs ≡ₚ ys → Forall P xs → Forall P ys.
  Proof.
    induction 1; inversion 1; subst; auto.
    inv H3. auto.
  Qed.

  Lemma perm_Forall_rew (xs ys : list A) :
    xs ≡ₚ ys → Forall P xs ↔ Forall P ys.
  Proof.
    split; apply perm_Forall; done.
  Qed.
End perm.

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
  injection Hlen as Hlen.
  do 2 rewrite {1}fmap_cons.
  iDestruct (array_cons with "Ha1") as "[Ha1_hd Ha1_tl]".
  iDestruct (array_cons with "Ha2") as "[Ha2_hd Ha2_tl]".
  iDestruct (array_cons with "Hb") as "[Hb_hd Hb_tl]".
  wp_load. wp_let. wp_load. wp_pures.
  destruct (decide (x1 ≤ x2)%Z) as [Hx1_le_x2 | Hx1_nle_x2].
  - rewrite bool_decide_eq_true_2 //. wp_pures.
    apply StronglySorted_inv in Hl1 as [Hx1 Hl1].
    wp_store. wp_pures.
    iCombine "Ha2_hd Ha2_tl" as "Ha2". rewrite -array_cons.
    rewrite -fmap_cons.
    replace (Z.of_nat (S (length l1)) - 1)%Z with (Z.of_nat (length l1)) by lia.
    replace (S (length l2)) with (length (x2 :: l2)) by reflexivity.
    wp_apply ("IH" with "Ha1_tl Ha2 Hb_tl"); try done.
    iIntros (zs) "(Ha1_tl & Ha2 & Hb_tl & %Hzs & %Hperm)".
    iCombine "Ha1_hd Ha1_tl" as "Ha1". rewrite -array_cons.
    iCombine "Hb_hd Hb_tl" as "Hb". rewrite -array_cons.
    do 2 rewrite -fmap_cons. iApply "HΦ". iFrame.
    iPureIntro. split.
    + apply SSorted_cons; first done.
      rewrite -(perm_Forall_rew _ _ _ Hperm) Forall_app.
      split; first done.
      constructor; first done.
      apply StronglySorted_inv in Hl2 as [Hx2 Hl2].
      apply List.Forall_impl with (2:=Hl2). lia.
    + simpl. by apply perm_skip.
  - rewrite bool_decide_eq_false_2 //.
    apply StronglySorted_inv in Hl2 as [Hx2 Hl2].
    wp_store. wp_pures.
    iCombine "Ha1_hd Ha1_tl" as "Ha1". rewrite -array_cons.
    rewrite -fmap_cons.
    replace (Z.of_nat (S (length l2)) - 1)%Z with (Z.of_nat (length l2)) by lia.
    replace (S (length l1)) with (length (x1 :: l1)) by reflexivity.
    wp_apply ("IH" with "Ha1 Ha2_tl Hb_tl"); try done.
    { iPureIntro. simpl. lia. }
    iIntros (zs) "(Ha1 & Ha2_tl & Hb_tl & %Hzs & %Hperm)".
    iCombine "Ha2_hd Ha2_tl" as "Ha2". rewrite -array_cons.
    iCombine "Hb_hd Hb_tl" as "Hb". rewrite -array_cons.
    do 2 rewrite -fmap_cons. iApply "HΦ". iFrame.
    iPureIntro. split.
    + apply SSorted_cons; first done.
      rewrite -(perm_Forall_rew _ _ _ Hperm) Forall_app.
      split; last done.
      constructor; first lia.
      apply StronglySorted_inv in Hl1 as [Hx1 Hl1].
      apply List.Forall_impl with (2:=Hl1). lia.
    + simpl in *.
      rewrite -Hperm perm_swap.
      apply perm_skip.
      by rewrite Permutation_middle.
Qed.

Lemma array_split_take (n : Z) (ℓ : loc) (dq : dfrac) (vs : list val) :
  (0 ≤ n ≤ Zlength vs)%Z →
  ℓ ↦∗{dq} vs ⊣⊢ ℓ ↦∗{dq} take (Z.to_nat n) vs ∗ (ℓ +ₗ n) ↦∗{dq} drop (Z.to_nat n) vs.
Proof.
  intros H.
  rewrite -{1}(take_drop (Z.to_nat n) vs) array_app take_length_le //.
  - rewrite Z2Nat.id //. lia.
  - rewrite Zlength_correct in H. lia.
Qed.

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
  iIntros (Φ) "(Ha & Hb) HΦ".
  remember (Z.of_nat (length l)) as n eqn:Hln.
  iRevert (Hln). iIntros "Hln".
  iLöb as "IH" forall (a b l n Φ).
  iDestruct "Hln" as %->.
  wp_rec. wp_pures.
  destruct l as [| x l].
  { simpl. wp_pures. iModIntro.
    iApply ("HΦ" $! [] []). simpl. iFrame. iPureIntro.
    repeat split; try done. constructor. }
  rewrite cons_length.
  destruct (decide (length l ≤ 0)) as [Hlen0 | Hlen0].
  { rewrite bool_decide_eq_true_2; last lia.
    wp_pures. iModIntro.
    destruct l; simpl in Hlen0; last lia.
    iApply ("HΦ" $! [x] [(#x) : val]).
    simpl. iFrame. iPureIntro.
    repeat split; try done. repeat constructor. }
  rewrite bool_decide_eq_false_2; last lia.
  wp_pures. wp_bind (par _ _).
  set (q := (S (length l) `quot` 2)%Z).
  assert (0 ≤ q ≤ Zlength (x :: l))%Z as Hdumb.
  { rewrite /q Zlength_correct /=.
    rewrite /= -{2}(Nat2Z.id (S (length l))).
    split.
    - apply Z.quot_pos; lia.
    - apply Z.quot_le_upper_bound; lia. }
  assert (0 ≤ q ≤ Zlength ((λ x0 : Z, #x0) <$> x :: l))%Z as Hdumber.
  { by rewrite /q Zlength_correct fmap_length -{3}Zlength_correct. }
  assert ((S (length l) - q)%Z = length (drop (Z.to_nat q) (x :: l))) as Hdumbdrop.
  { rewrite drop_length /= Nat2Z.inj_sub; try lia.
    replace (S (length l)) with (length (x :: l)) by done.
    rewrite /q -(Nat2Z.id (length (x :: l))) -{2}(Zlength_correct (x :: l)). lia. }
  assert (q = length (take (Z.to_nat q) (x :: l))) as Hdumbtake.
  { rewrite take_length_le; first lia.
    rewrite /q -(Nat2Z.id (length (x :: l))) -{2}(Zlength_correct (x :: l)). lia. }
  rewrite (array_split_take q a) //.
  rewrite (array_split_take q b) //.
  iDestruct "Ha" as "[Ha_take Ha_drop]".
  iDestruct "Hb" as "[Hb_take Hb_drop]".
  repeat rewrite -fmap_take.
  repeat rewrite -fmap_drop.
  set (Ψ₁ take_l v := (∃ (l' : list Z) vs, ⌜v = #()⌝ ∗ b ↦∗ ((λ x : Z, #x) <$> l') ∗ a ↦∗ vs ∗ ⌜StronglySorted Z.le l'⌝  ∗ ⌜take_l ≡ₚ l'⌝ ∗ ⌜length vs = length l'⌝)%I).
  set (Ψ₂ drop_l v := (∃ (l' : list Z) vs, ⌜v = #()⌝ ∗ (b +ₗ q) ↦∗ ((λ x : Z, #x) <$> l') ∗ (a +ₗ q) ↦∗ vs ∗ ⌜StronglySorted Z.le l'⌝  ∗ ⌜drop_l ≡ₚ l'⌝ ∗ ⌜length vs = length l'⌝)%I).
  wp_apply (wp_par (Ψ₁ (take (Z.to_nat q) (x :: l))) (Ψ₂ (drop (Z.to_nat q) (x :: l))) with "[Ha_take Hb_take] [Ha_drop Hb_drop] [HΦ]").
  - clear Ψ₂.
    wp_apply ("IH" with "Hb_take Ha_take"); last done.
    iIntros (l' vs) "(Hb & Ha & %Hl' & %Hperm & %Hlen)".
    rewrite /Ψ₁. by iFrame "∗ %".
  - clear Ψ₁. wp_pures.
    wp_apply ("IH" with "Hb_drop Ha_drop"); last done.
    iIntros (l' vs) "(Hb & Ha & %Hl' & %Hperm & %Hlen)".
    rewrite /Ψ₂. by iFrame "∗ %".
  - iIntros (v1 v2) "[HΨ₁ HΨ₂]".
    rewrite /Ψ₁. iDestruct "HΨ₁" as "(%l1' & %vs1' & -> & Hb1 & Ha1 & %HSS1 & %Hperm1 & %Hlen1)".
    rewrite /Ψ₂. iDestruct "HΨ₂" as "(%l2' & %vs2' & -> & Hb2 & Ha2 & %HSS2 & %Hperm2 & %Hlen2)".
    iNext. wp_pures.
    replace (S (length l) - q)%Z with (Z.of_nat (length l2')) by by rewrite -(Permutation_length Hperm2). 
    replace q with (Z.of_nat (length l1')) by by rewrite -(Permutation_length Hperm1).
    iCombine "Ha1 Ha2" as "Ha". rewrite -{2}Hlen1 -array_app.
    wp_apply (merge_spec with "[$Hb1 $Hb2 $Ha]"); first iFrame "%".
    1: iPureIntro; rewrite app_length; congruence.
    iIntros (l') "(Hb1 & Hb2 & Ha & %HSS & %Hperm)".
    iCombine "Hb1 Hb2" as "Hb".
    rewrite -(fmap_length (λ x: Z, #x) l1') -array_app -fmap_app.
    iApply ("HΦ" with "[$Ha $Hb]"). iPureIntro.
    rewrite map_length (Permutation_length Hperm).
    repeat split; try done.
    by rewrite -Hperm -Hperm1 -Hperm2 take_drop.
Qed.

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
