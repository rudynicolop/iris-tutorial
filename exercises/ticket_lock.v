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
Definition issued (γ : gname) (x : nat) : iProp Σ :=
  own γ (◯ GSet {[ x ]}).

Definition lock_inv (α β γ δ : gname) (lo ln : loc) (P : iProp Σ) : iProp Σ :=
  ∃ (o n : nat),
  ⌜o ≤ n⌝ ∗ lo ↦ #o ∗ ln ↦ #n ∗
  own γ (● GSet (list_to_set (seq o (n - o)))) ∗
  own α (●E o) ∗ own β (● MaxNat o) ∗ own δ (● MaxNat n) ∗
  (issued γ o (* locked *) ∨ P ∗ locked_by α o (* unlocked *)).

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
  iMod (own_alloc (● GSet (list_to_set (seq 0 (0 - 0))) ⋅ ◯ GSet (list_to_set (seq 0 (0 - 0))))) as (γ) "[Hγ● Hγ◯]".
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
  {{{ is_lock α β γ δ l P ∗ issued γ x }}}
    wait #x l
  {{{ RET #(); locked α ∗ P }}}.
Proof.
  iIntros (Φ) "[(%lo & %ln & -> & #HInv) Hγ◯x] HΦ".
  iLöb as "IH". wp_lam. wp_pures. wp_bind (! _)%E.
  iInv "HInv" as (o n) "(>%Hon & >Hlo & >Hln & >Hγ● & >Hα● & >Hβ● & >Hδ● & H)" "Hclose".
  iCombine "Hγ● Hγ◯x" gives %Hvalid.
  rewrite auth_both_valid_discrete in Hvalid.
  destruct Hvalid as [Hsub Hvalid].
  rewrite gset_disj_included singleton_subseteq_l elem_of_list_to_set elem_of_seq in Hsub.
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
    rewrite gset_disj_included singleton_subseteq_l elem_of_list_to_set elem_of_seq in Hsub'.
    assert (y ≤ x < z) as Hyxz by lia.
    iCombine "Hβ● Hβ◯o" gives %Hvalido.
    rewrite auth_both_valid_discrete max_nat_included /= in Hvalido.
    destruct Hvalido as [Hxy _].
    iCombine "Hδ● Hδ◯n" gives %Hvalidn.
    rewrite auth_both_valid_discrete max_nat_included /= in Hvalidn.
    destruct Hvalidn as [Hnz _].
    assert (x = y) as <- by lia.
    iDestruct "H" as "[Hissuedx | [HP Hlocked_by]]".
    + iCombine "Hγ◯x Hissuedx" gives %Hinvalid.
      rewrite auth_frag_op_valid gset_disj_valid_op in Hinvalid.
      set_solver.
    + iMod ("Hclose" with "[-HΦ HP Hlocked_by]") as "_".
      { iNext. by iFrame. }
      iModIntro. wp_pures.
      iApply "HΦ". by iFrame.
  - wp_pures.
    rewrite bool_decide_eq_false_2; last by intros [= ->%Nat2Z.inj].
    iMod ("Hclose" with "[- HΦ Hγ◯x]") as "_".
    { iNext. by iFrame. }
    iModIntro. wp_pures.
    iApply ("IH" with "[$] [$]").
Qed.

Lemma acquire_spec γ l P :
  {{{ is_lock γ l P }}} acquire l {{{ RET #(); locked γ ∗ P }}}.
Proof.
  (* exercise *)
Admitted.

Lemma release_spec γ l P :
  {{{ is_lock γ l P ∗ locked γ ∗ P }}} release l {{{ RET #(); True }}}.
Proof.
  (* exercise *)
Admitted.

End proofs.
