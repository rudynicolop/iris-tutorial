From iris.algebra Require Import auth excl gset numbers.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation.

(* ################################################################# *)
(** * Case Study: Ticket Lock *)

(* ================================================================= *)
(** ** Implementation *)

(**
  Let us look at another implementation of a lock, namely a ticket lock.
  Instead of having every thread fight to acquire the lock, the ticket
  lock makes them wait in line. It functions similarly to a ticketing
  system that one often finds in bakeries and pharmacies. Upon entering
  the shop, you pick a ticket with some number and wait until the number
  on the screen has reached your number. Once this happens, it becomes
  your turn to speak to the shop assistant. In our scenario, talking to
  the shop assistant corresponds to accessing the protected resources.

  To implement this, we will maintain two counters: [o] and [n]. The
  first counter, [o], represents the number on the screen – the customer
  currently being served. The second counter, [n], represents the next
  number to be dispensed by the ticketing machine.

  To acquire the lock, a thread must increment the second counter, [n],
  and keep its previous value as a ticket for a position in the queue.
  Once the ticket has been obtained, the thread must wait until the
  first counter, [o], reaches its ticket value. Once this happens, the
  thread gets access to the protected resources. The thread can then
  release the lock by incrementing the first counter.
*)

Definition mk_lock : val :=
  λ: <>, (ref #0, ref #0).

Definition wait : val :=
  rec: "wait" "n" "l" :=
  let: "o" := !(Fst "l") in
  if: "o" = "n" then #() else "wait" "n" "l".

Definition acquire : val :=
  rec: "acquire" "l" :=
  let: "n" := !(Snd "l") in
  if: CAS (Snd "l") "n" ("n" + #1) then
    wait "n" "l"
  else
    "acquire" "l".

Definition release : val :=
  λ: "l", Fst "l" <- ! (Fst "l") + #1.

Definition with_lock (l : expr) (e : expr) : expr :=
  acquire l;;
  let: "v" := e in
  release l;; "v".

(* ================================================================= *)
(** ** Representation Predicates *)

(**
  As a ticket lock is a lock, we expect it to satisfy the same
  specification as the spin-lock. This time, you have to come up with
  the necessary resource algebra and lock invariant by yourself. It
  might be instructive to first look through all required predicates and
  specifications to figure out exactly what needs to be proven.
*)

Definition RA : cmra := authR (gsetR natR).

From iris.algebra Require Import lib.excl_auth.

Section proofs.
Context `{!heapGS Σ, !inG Σ (excl_authR nat), !inG Σ (authR (gset_disjR natR)), !inG Σ (authR (max_natR))}.
Let N := nroot .@ "ticket_lock".

(**
  This time around, we know that the thread is locked by a thread with a
  specific ticket. As such, we first define a predicate [locked_by]
  which states that the lock is locked by ticket [o].
*)
Definition locked_by (γ : gname) (o : nat) : iProp Σ :=
  own γ (◯E o).

(** The lock is locked when it has been locked by some ticket. *)
Definition locked (γ : gname) : iProp Σ :=
  ∃ o, locked_by γ o.

Lemma locked_excl γ : locked γ -∗ locked γ -∗ False.
Proof.
  iIntros "[%m Hγm] [%n Hγn]".
  iCombine "Hγm Hγn" gives %Hvalid.
  by rewrite excl_auth_frag_op_valid in Hvalid.
Qed.

(**
  We will also have a predicate signifying that ticket [x] has been
  _issued_. A thread will need to have been issued ticket [x] in order
  to wait for the first counter to become [x].
*)
Definition issued (γ δ : gname) (x : nat) : iProp Σ :=
  own γ (◯ GSet {[ x ]}) ∗ own δ (◯ MaxNat (x + 1)).

Definition lock_inv (α β γ δ : gname) (lo ln : loc) (P : iProp Σ) : iProp Σ :=
  ∃ (o n : nat),
  ⌜o ≤ n⌝ ∗ lo ↦ #o ∗ ln ↦ #n ∗
  own γ (● GSet (set_seq o (n - o))) ∗
  own α (●E o) ∗ own β (● MaxNat o) ∗ own δ (● MaxNat n) ∗
  (issued γ δ o (* locked *) ∨ P ∗ locked_by α o (* unlocked *)).

Definition is_lock (α β γ δ : gname) (l : val) (P : iProp Σ) : iProp Σ :=
  ∃ lo ln : loc, ⌜l = (#lo, #ln)%V⌝ ∗ inv N (lock_inv α β γ δ lo ln P).

(* ================================================================= *)
(** ** Specifications *)

Lemma mk_lock_spec P :
  {{{ P }}} mk_lock #() {{{ α β γ δ l, RET l; is_lock α β γ δ l P }}}.
Proof.
  iIntros (Φ) "HP HΦ". wp_lam.
  wp_alloc ln as "Hln". wp_alloc lo as "Hlo".
  iMod (own_alloc (●E 0 ⋅ ◯E 0)) as (α) "[Hα● Hα◯]"; first apply excl_auth_valid.
  iMod (own_alloc (● GSet (set_seq 0 (0 - 0)) ⋅ ◯ GSet (set_seq 0 (0 - 0)))) as (γ) "[Hγ● Hγ◯]".
  { by rewrite auth_auth_valid /=. }
  iMod (own_alloc (● MaxNat 0)) as (β) "Hβ●".
  { by rewrite auth_auth_valid. }
  iMod (own_alloc (● MaxNat 0)) as (δ) "Hδ●".
  { by rewrite auth_auth_valid. }
  wp_pures.
  iMod (inv_alloc N _ (lock_inv α β γ δ lo ln P) with "[-HΦ]") as "#HInv".
  { iNext. iFrame. iSplit; first (iPureIntro; lia). iRight. iFrame. }
  iModIntro. iApply ("HΦ" $! α β γ δ). by iFrame "#".
Qed.

Lemma wait_spec α β γ δ l P x :
  {{{ is_lock α β γ δ l P ∗ issued γ δ x }}}
    wait #x l
  {{{ RET #(); locked α ∗ P }}}.
Proof.
  iIntros (Φ) "[(%lo & %ln & -> & #HInv) [Hγ◯x #Hδ◯x]] HΦ".
  iLöb as "IH". wp_lam. wp_pures. wp_bind (! _)%E.
  iInv "HInv" as (o n) "(>%Hon & >Hlo & >Hln & >Hγ● & >Hα● & >Hβ● & >Hδ● & H)" "Hclose".
  iCombine "Hγ● Hγ◯x" gives %Hvalid.
  rewrite auth_both_valid_discrete in Hvalid.
  destruct Hvalid as [Hsub Hvalid].
  rewrite gset_disj_included singleton_subseteq_l elem_of_set_seq in Hsub.
  assert (o ≤ x < n) as Hoxn by lia. wp_load.
  iMod (own_update _ _ (● (MaxNat o) ⋅ ◯ (MaxNat o)) with "Hβ●") as "[Hβ● #Hβ◯o]".
  { apply auth_update_alloc.
    apply max_nat_local_update. simpl. lia. }
  iMod (own_update _ _ (● (MaxNat n) ⋅ ◯ (MaxNat n)) with "Hδ●") as "[Hδ● #Hδ◯n]".
  { apply auth_update_alloc.
    apply max_nat_local_update. simpl. lia. }
  iMod ("Hclose" with "[-HΦ Hγ◯x]") as "_".
  { iNext. by iFrame. }
  iModIntro. wp_let. wp_bind (_ = _)%E.
  iInv "HInv" as (y z) "(>%Hyz & >Hlo & >Hln & >Hγ● & >Hα● & >Hβ● & >Hδ● & H)" "Hclose".
  destruct (decide (o = x)) as [-> | H_o_neq_x].
  - wp_pures.
    rewrite bool_decide_eq_true_2 //.
    iCombine "Hγ● Hγ◯x" gives %Hvalid'.
    rewrite auth_both_valid_discrete in Hvalid'.
    destruct Hvalid' as [Hsub' Hvalid'].
    rewrite gset_disj_included singleton_subseteq_l elem_of_set_seq in Hsub'.
    assert (y ≤ x < z) as Hyxz by lia.
    iCombine "Hβ● Hβ◯o" gives %Hvalido.
    rewrite auth_both_valid_discrete max_nat_included /= in Hvalido.
    destruct Hvalido as [Hxy _].
    iCombine "Hδ● Hδ◯n" gives %Hvalidn.
    rewrite auth_both_valid_discrete max_nat_included /= in Hvalidn.
    destruct Hvalidn as [Hnz _].
    assert (x = y) as <- by lia.
    iDestruct "H" as "[[Hγ◯x' #Hδ◯x'] | [HP Hlocked_by]]".
    + iCombine "Hγ◯x Hγ◯x'" gives %Hinvalid.
      rewrite auth_frag_op_valid gset_disj_valid_op in Hinvalid.
      set_solver.
    + iMod ("Hclose" with "[-HΦ HP Hlocked_by]") as "_".
      { iNext. by iFrame "# ∗". }
      iModIntro. wp_pures.
      iApply "HΦ". by iFrame.
  - wp_pures.
    rewrite bool_decide_eq_false_2; last by intros [= ->%Nat2Z.inj].
    iMod ("Hclose" with "[- HΦ Hγ◯x]") as "_".
    { iNext. by iFrame. }
    iModIntro. wp_pures.
    iApply ("IH" with "[$] [$]").
Qed.

Lemma acquire_spec α β γ δ l P :
  {{{ is_lock α β γ δ l P }}} acquire l {{{ RET #(); locked α ∗ P }}}.
Proof.
  iIntros (Φ) "(%lo & %ln & -> & #HInv) HΦ".
  iLöb as "IH". wp_lam. wp_pures. wp_bind (! _)%E.
  iInv "HInv" as (o n) "(>%Hon & >Hlo & >Hln & >Hγ● & >Hα● & >Hβ● & >Hδ● & H)" "Hclose".
  wp_load.
  iMod (own_update _ _ (● (MaxNat o) ⋅ ◯ (MaxNat o)) with "Hβ●") as "[Hβ● #Hβ◯o]".
  { apply auth_update_alloc.
    apply max_nat_local_update. simpl. lia. }
  iMod (own_update _ _ (● (MaxNat n) ⋅ ◯ (MaxNat n)) with "Hδ●") as "[Hδ● #Hδ◯n]".
  { apply auth_update_alloc.
    apply max_nat_local_update. simpl. lia. }
  iMod ("Hclose" with "[-HΦ]") as "_".
  { iNext. by iFrame. }
  iModIntro. wp_pures. wp_bind (CmpXchg _ _ _)%E.
  iInv "HInv" as (y z) "(>%Hyz & >Hlo & >Hln & >Hγ● & >Hα● & >Hβ● & >Hδ● & H)" "Hclose".
  destruct (decide (z = n)%nat) as [-> | H_z_neq_n].
  - wp_cmpxchg_suc.
    iMod (own_update _ _ (● GSet (set_seq y (n + 1 - y)) ⋅ ◯ GSet {[n]}) with "Hγ●") as "[Hγ● Hγ◯]".
    { apply auth_update_alloc.
      replace (seq y (n + 1 - y)) with (seq y (n - y) ++ [n]).
      2:{ replace (n + 1 - y) with (S (n - y)) by lia.
        rewrite seq_S. f_equal. f_equal. lia. }
      replace (n + 1 - y) with (S (n - y)) by lia.
      rewrite set_seq_S_end_union_L -Nat.le_add_sub //.
      apply gset_disj_alloc_empty_local_update.
      replace n with (y + (n - y)) at 1 by lia.
      apply set_seq_S_end_disjoint. }
    iMod (own_update _ _ (● MaxNat (n + 1) ⋅ ◯ MaxNat (n + 1)) with "Hδ●") as "[Hδ● #Hδ◯]".
    { eapply auth_update_alloc.
      apply max_nat_local_update.
      simpl. lia. }
    iMod ("Hclose" with "[-HΦ Hγ◯]") as "_".
    { iNext. iFrame.
      replace (Z.of_nat (n + 1)) with (Z.of_nat n + 1)%Z by lia.
      iFrame. iPureIntro. lia. }
    iModIntro. wp_pures.
    wp_apply (wait_spec with "[$HInv $Hγ◯ $Hδ◯]"); first done.
    iApply "HΦ".
  - wp_cmpxchg_fail; first by intros [= ->%Nat2Z.inj].
    iMod ("Hclose" with "[-HΦ]") as "_".
    { iNext. by iFrame. }
    iModIntro. wp_pures.
    by wp_apply "IH".
Qed.

Lemma release_spec α β γ δ l P :
  {{{ is_lock α β γ δ l P ∗ locked α ∗ P }}} release l {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "((%lo & %ln & -> & #HInv) & [%m Hα◯] & HP) HΦ".
  wp_lam. wp_pures. wp_bind (! _)%E.
  iInv "HInv" as (o n) "(>%Hon & >Hlo & >Hln & >Hγ● & >Hα● & >Hβ● & >Hδ● & H)" "Hclose".
  iCombine "Hα● Hα◯" gives %<-%excl_auth_agree_L.
  wp_load. iMod ("Hclose" with "[- HΦ Hα◯ HP]") as "_".
  { iNext. by iFrame. }
  iModIntro. wp_pures.
  iInv "HInv" as (y z) "(>%Hyz & >Hlo & >Hln & >Hγ● & >Hα● & >Hβ● & >Hδ● & H)" "Hclose".
  iCombine "Hα● Hα◯" gives %->%excl_auth_agree_L.
  wp_store.
  iMod (own_update_2 _ _ _ (●E (o+1) ⋅ ◯E (o+1)) with "Hα● Hα◯") as "[Hα● Hα◯]"; first apply excl_auth_update.
  iMod (own_update _ _ (● MaxNat (o + 1)) with "Hβ●") as "Hβ●".
  { eapply auth_update_auth.
    apply max_nat_local_update.
    simpl. lia. }
  iDestruct "H" as "[[Hγ◯ Hδ◯] | [HP' Hα◯o]]".
  2:{ iCombine "Hα◯ Hα◯o" gives %Hinvalid.
    by rewrite excl_auth_frag_op_valid in Hinvalid. }
  iCombine "Hδ● Hδ◯" gives %Hvalidzo.
  rewrite auth_both_valid_discrete max_nat_included /= in Hvalidzo.
  destruct Hvalidzo as [Hoz _].
  iMod (own_update_2 _ _ _ (●GSet (set_seq (o + 1) (z - (o + 1)))) with "Hγ● Hγ◯") as "Hγ●".
  { replace (set_seq (o + 1) (z - (o + 1))) with (set_seq o (z - o) ∖ {[o]} : gset nat).
  2:{ replace (z - o) with (1 + (z - (o + 1))) by lia.
    rewrite set_seq_add_L /= union_empty_r_L difference_union_distr_l_L difference_diag_L union_empty_l_L difference_disjoint_L; first done.
    rewrite disjoint_singleton_r elem_of_set_seq. lia. }
  apply auth_update_dealloc.
  apply gset_disj_dealloc_local_update. }
  iMod ("Hclose" with "[- HΦ]") as "_".
  { iNext. iFrame.
    replace (Z.of_nat (o + 1)) with (Z.of_nat o + 1)%Z by lia.
    iFrame "% # ∗". iRight. iFrame. }
  iModIntro. by iApply "HΦ".
Qed.

Lemma with_lock_spec [α β γ δ l e] I P Q :
  {{{ I ∗ P }}} e {{{ v, RET v; I ∗ Q v }}}
  ⊢ {{{ is_lock α β γ δ l I ∗ P }}} with_lock l e {{{ v, RET v; Q v }}}.
Proof.
  iIntros "#He %Φ !> [#Hlock HP] HΦ".
  rewrite /with_lock. wp_bind (acquire _)%E.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked HI]". wp_pures.
  wp_apply ("He" with "[$HP $HI]").
  iIntros (v) "[HI HQ]". wp_pures. wp_bind (release l)%E.
  wp_apply (release_spec with "[$Hlock $HI $Hlocked]").
  iIntros "_". wp_pures. by iApply "HΦ".
Qed.
End proofs.

From iris.heap_lang Require Import lib.par.

Module test.
  Local Definition par_add_mul : expr :=
    let: "l" := ref #2 in
    let: "lock" := mk_lock #() in
    (with_lock "lock" ("l" <- !"l" + #3)) ||| (with_lock "lock" ("l" <- !"l" * #3));;
    acquire "lock";;
    !"l".

  Section test.
    Context `{!heapGS Σ, !inG Σ (excl_authR nat), !inG Σ (authR (gset_disjR natR)), !inG Σ (authR (max_natR))}.
    Context `{!spawnG Σ, !inG Σ (excl_authR boolO)}.

    Local Definition par_inv (ℓ : loc) (γ₁ γ₂ : gname) : iProp Σ :=
      (* tᵢ represents thread 1 completeing. *)
      ∃ (t₁ t₂ : bool) (z : Z),
      ℓ ↦ #z ∗ own γ₁ (●E t₁) ∗ own γ₂ (●E t₂) ∗
      match t₁, t₂ with
      | false, false => ⌜z = 2%Z⌝
      | true,  false => ⌜z = 5%Z⌝
      | false, true  => ⌜z = 6%Z⌝
      | true,  true  => ⌜z = 15%Z⌝ ∨ ⌜z = 9%Z⌝
      end.

    Local Lemma par_add_mul_spec :
      {{{ True }}} par_add_mul {{{ (z : Z), RET #z; ⌜z = 15%Z⌝ ∨ ⌜z = 9%Z⌝ }}}.
    Proof.
      iIntros (Φ) "_ HΦ". rewrite /par_add_mul.
      wp_alloc ℓ as "Hℓ". wp_pures.
      iMod (own_alloc ((●E false) ⋅ (◯E false))) as (γ₁) "[Hγ₁● Hγ₁◯]"; first apply excl_auth_valid.
      iMod (own_alloc ((●E false) ⋅ (◯E false))) as (γ₂) "[Hγ₂● Hγ₂◯]"; first apply excl_auth_valid.
      iAssert (par_inv ℓ γ₁ γ₂) with "[Hℓ Hγ₁● Hγ₂●]" as "HI"; first by iFrame.
      wp_apply (mk_lock_spec with "HI") as (α β γ δ lock) "#Hlock".
      wp_pures.
      wp_apply (wp_par
      (λ _, own γ₁ (◯E true))%I
      (λ _, own γ₂ (◯E true))%I
      with "[Hγ₁◯] [Hγ₂◯] [HΦ]").
      - wp_apply (with_lock_spec _ (own γ₁ (◯E false)) (λ _, own γ₁ (◯E true)) with "[] [$Hγ₁◯ $Hlock]"); last (iIntros "_ Hγ₁◯"; by iFrame).
        iIntros (Ψ) "!> [(%t₁ & %t₂ & %z & Hℓz & Hγ₁● & Hγ₂● & H) Hγ₁◯] HΨ".
        wp_load. wp_pures. wp_store.
        iCombine "Hγ₁● Hγ₁◯" gives %->%excl_auth_agree_L.
        iMod (own_update_2 _ _ _ (●E true ⋅ ◯E true) with "Hγ₁● Hγ₁◯") as "[Hγ₁● Hγ₁◯]"; first apply excl_auth_update.
        destruct t₂; iDestruct "H" as %->; simpl.
        + iApply "HΨ". iModIntro. iFrame. iRight.
          iPureIntro. lia.
        + iApply "HΨ". iModIntro. iFrame.
          iPureIntro. lia.
      - wp_apply (with_lock_spec _ (own γ₂ (◯E false)) (λ _, own γ₂ (◯E true)) with "[] [$Hγ₂◯ $Hlock]"); last (iIntros "_ Hγ₂◯"; by iFrame).
        iIntros (Ψ) "!> [(%t₁ & %t₂ & %z & Hℓz & Hγ₁● & Hγ₂● & H) Hγ₂◯] HΨ".
        wp_load. wp_pures. wp_store.
        iCombine "Hγ₂● Hγ₂◯" gives %->%excl_auth_agree_L.
        iMod (own_update_2 _ _ _ (●E true ⋅ ◯E true) with "Hγ₂● Hγ₂◯") as "[Hγ₂● Hγ₂◯]"; first apply excl_auth_update.
        destruct t₁; iDestruct "H" as %->; simpl.
        + iApply "HΨ". iModIntro. iFrame. iLeft.
          iPureIntro. lia.
        + iApply "HΨ". iModIntro. iFrame.
          iPureIntro. lia.
      - iIntros (v1 v2) "[Hγ₁◯ Hγ₂◯] !>". wp_pures. clear v1 v2.
        wp_apply (acquire_spec with "Hlock") as "[[%o Ho] (%t₁ & %t₂ & %z & Hℓz & Hγ₁● & Hγ₂● & H)]".
        iCombine "Hγ₁● Hγ₁◯" gives %->%excl_auth_agree_L.
        iCombine "Hγ₂● Hγ₂◯" gives %->%excl_auth_agree_L.
        wp_pures. wp_load. iModIntro.
        by iApply "HΦ".
      Qed.
  End test.
End test.
