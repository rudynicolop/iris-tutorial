From iris.algebra Require Import cmra.
From iris.heap_lang.lib Require Export par.
From iris.heap_lang Require Import proofmode notation.

(* ################################################################# *)
(** * Custom Resource Algebra *)

(* ================================================================= *)
(** ** A Motivating Example *)

(**
  In this chapter, we will define a new resource algebra from scratch.
  To motivate the resource algebra, we will look at the following
  program:
*)
Definition prog : expr :=
  let: "l" := ref #4 in
  ("l" <- !"l" + #1) ||| ("l" <- !"l" + #1);;
  !"l".

(**
  We wish to show that the program terminates with a number that is at
  least [5]. To do this, we will use an invariant separated into the
  different abstract states of our program. At the outset, the location
  will map to [4]. During the execution of the threads, the location
  will be changed to either [5] or [6]. However, we just care about it
  becoming greater than [4]. As such, we will have the following states.
*)

Inductive state :=
  (** The starting state. *)
  | Start
  (** The state after the location has been increased. *)
  | Final
  (**
    An invalid state we will use to restrict the operations on the
    state.
  *)
  | Invalid.

(**
  The [state] data structure will be our carrier for the RA. To use
  [state] as a resource algebra, we need to turn it into a resource
  algebra, meaning we need it to adhere to [RAMixin]. As such, we must
  define an equivalence relation, composition, the core, and valid
  elements, and prove that these definitions satisfy the fields in
  [RAMixin].
*)

(* ================================================================= *)
(** ** Defining the State RA *)

Section state.

(**
  First, we define an equivalence relation on the state. We just want
  states to be equivalent exactly when they are equal.
*)
Global Instance state_equiv_instance : Equiv state := eq.
Global Instance state_equiv_equivalence : Equivalence (≡@{state}) := _.
(**
  To help convert between equivalence and equality, we can tell Iris
  that they coincide, which in this case is trivial.
*)
Global Instance state_leibniz_equiv : LeibnizEquiv state := _.

(**
  Recall that resource algebras are discrete cameras and that cameras
  build on OFEs (Ordered family of equivalences). As such, to define a
  resources algebra, we must first define its OFE. An OFE encodes a kind
  of time dependence, but when the camera is _discrete_ and hence a
  resource algebra, it does not depend on time. To quickly define a
  discrete OFE, we can use [discrete_ofe_mixin]. This will produce a
  warning because we are reusing a definition in a canonical projection.
  However, this warning can be safely ignored in this case.
*)
Canonical stateO := Ofe state (discrete_ofe_mixin _).

(**
  Next, we define how elements of [state] can be combined. We define
  [Final ⋅ Final] as [Final], and make every other combination
  [Invalid]. In particular, this means that [Start] will be exclusive,
  while [Final] can be shared.
*)
Local Instance state_op_instance : Op state := λ s1 s2,
  match s1, s2 with
  | Final, Final => Final
  | _, _ => Invalid
  end.

(**
  The core then simply reflects that [Start] is exclusive.
*)
Local Instance state_pcore_instance : PCore state := λ s,
  match s with
  | Start => None
  | _ => Some s
  end.

(**
  Finally, we have to define which elements of [state] are valid.
  Naturally, we define everything except for [Invalid] as valid.
*)
Local Instance state_valid_instance : Valid state := λ s,
  match s with
  | Start | Final => True
  | Invalid => False
  end.

(**
  With everything defined, we can move on to prove [RAMixin] for
  [state].
*)
Lemma state_ra_mixin : RAMixin state.
Proof.
  split.
  - solve_proper.
  - naive_solver.
  - solve_proper.
  - by intros [] [] [].
  - by intros [] [].
  - by intros [] [].
  - by intros [] [].
  - intros [] _ [] [[] ->] e; try done.
    all: eexists; split; first done.
    all: try by exists Invalid.
    by exists Final.
  - by intros [] [].
Qed.

(**
  The final step is to package this into a CMRA structure, allowing us
  to use the resource algebra in proofs (using Coq's Context mechanism).
*)
Canonical Structure stateR := discreteR state state_ra_mixin.

(**
  To help the Iris Proof Mode, we will register [stateR] as a discrete
  CMRA.
*)
Global Instance state_cmra_discrete : CmraDiscrete state.
Proof. apply discrete_cmra_discrete. Qed.

End state.

(* ================================================================= *)
(** ** Properties of State *)

(**
  To alleviate working with the State RA, we here show some useful facts
  about the resource algebra. Firstly, [Start] is exclusive and [Final]
  is shareable.
*)

Global Instance Start_exclusive : Exclusive Start.
Proof. by intros []. Qed.

Global Instance Final_core_id : CoreId Final.
Proof. red. done. Qed.

(**
  We want the ability to change the state from [Start] to [Final].
  However, we will instead prove a more general fact: That any state can
  update to [Final].
*)
Lemma state_update s : s ~~> Final.
Proof.
  (**
    As we are working with a discrete CMRA, we can simplify this
    statement as follows.
  *)
  rewrite cmra_discrete_update.
  intros mz H.
  by destruct s, mz as [[| |]|].
Qed.

(**
  Next, we give lemmas that help working with the State RA _in Iris_.
*)

Section properties.
Context `{!inG Σ stateR}.

(**
  Our first lemma shows how a new State resource is created. We can
  create new resources via the basic update modality [|==> P]. This
  operation states that P holds after an update of resources. To work
  with the update modality, we can use two facts:
  - [P ⊢ |==> P]
  - [(P ⊢ |==> Q) ⊢ (|==> P ⊢ |==> Q)]
  Rather than working with these facts directly, we can use
  [iModIntro] and [iMod] respectively.
*)
Lemma alloc_Start : ⊢ |==> ∃ γ, own γ Start.
Proof.
  (** To allocate a new resource, we use [own_alloc]. *)
  iApply own_alloc.
  (**
    We are naturally only allowed to allocate valid resources, but since
    [Start] is valid, this is no problem.
  *)
  done.
Qed.

(**
  Likewise, owning a resource means that it is valid.
  A quick note: [✓ _] and [⌜✓ _⌝] are different – they only coincide
  when the CMRA is discrete.
*)
Lemma state_valid γ (s : state) : own γ s ⊢ ⌜✓ s⌝.
Proof.
  iIntros "H".
  iPoseProof (own_valid with "H") as "%H".
  done.
Qed.

(**
  Next, we can lift [state_update] to ownership using [own_update].
  As a shorthand for [_ -∗ |==> _] we write [_ ==∗ _].
*)
Lemma state_bupd γ (s : state) : own γ s ==∗ own γ Final.
Proof.
  iApply own_update.
  apply state_update.
Qed.

End properties.

(* ================================================================= *)
(** ** Using the State RA in Proofs *)

(**
  Let us return to the motivating example from the first section of this
  chapter. We will be using the State RA to prove that [prog] terminates
  with a value that is at least [5].
*)

Section proofs.

Context `{!heapGS Σ, !spawnG Σ, !inG Σ stateR}.

Let N := nroot .@ "state".

(**
  We can now define the invariant we hinted at in the beginning.
*)
Definition state_inv γ (l : loc) (x : Z) : iProp Σ :=
  ∃ y : Z, l ↦ #y ∗ (own γ Start ∗ ⌜x = y⌝ ∨ own γ Final ∗ ⌜x < y⌝%Z).

(**
  Rather than proving the entire program at once, we will split it into
  three pieces, starting with the two threads.

  Note that WP contains an update modality, meaning we can update
  resources in between steps.
*)
Lemma thread_spec γ l (x : Z) : {{{inv N (state_inv γ l x)}}} #l <- !#l + #1 {{{RET #(); own γ Final}}}.
Proof.
  iIntros (Φ) "#HInv HΦ".
  wp_bind (! _)%E.
  iInv "HInv" as (y) "[>Hly H]" "Hclose". wp_load.
  iAssert (⌜x =@{Z} y⌝ ∨ ⌜(x<y)%Z⌝)%I as %Hor.
  { iDestruct "H" as "[[_ ->] | [_ %Hxy]]"; iPureIntro; lia. }
  iMod ("Hclose" with "[$Hly $H]") as "_".
  iModIntro. wp_pures.
  iInv "HInv" as (z) "[>Hlz [[Hγ >->] | [#Hγ >%Hxz]]]" "Hclose".
  all: wp_store.
  1: iMod (state_bupd with "Hγ") as "#Hγ".
  all: iMod ("Hclose" with "[$Hlz]") as "_"; first by (iNext; iRight; iFrame "#"; iPureIntro; lia).
  all: by iApply "HΦ".
Qed.

Lemma body_spec l (x : Z) : {{{l ↦ #x}}} (#l <- !#l + #1) ||| (#l <- !#l + #1);; !#l {{{(y : Z), RET #y; ⌜x < y⌝%Z}}}.
Proof.
  iIntros (Φ) "Hlx HΦ".
  iMod alloc_Start as (γ) "Hγ".
  iMod (inv_alloc N _ (state_inv γ l x) with "[$Hlx Hγ]") as "#HInv".
  { iNext. iLeft. by iFrame. }
  wp_pures. wp_bind (par _ _).
  set (Ψ v := (⌜v = #()⌝ ∗ own γ Final)%I).
  wp_apply (wp_par Ψ Ψ with "[] [] [HΦ]") as (v1 v2) "[[-> #Hγ1] [-> #Hγ2]]".
  1, 2: wp_apply (thread_spec with "HInv") as "Hγ".
  1, 2: by iFrame.
  iNext. wp_pures.
  iInv "HInv" as (z) ">[Hlz [[Hγ ->] | [#Hγ %Hxz]]]" "Hclose".
  1: iCombine "Hγ Hγ1" gives %Hinvalid.
  1: by rewrite /op /cmra_op /= /valid /cmra_valid /= in Hinvalid.
  wp_load. iMod ("Hclose" with "[$Hlz]") as "_".
  { iNext. iRight. iFrame "# %". }
  iModIntro. by iApply "HΦ".
Qed.

Lemma prog_spec : {{{True}}} prog {{{(y : Z), RET #y; ⌜5 ≤ y⌝%Z}}}.
Proof.
  iIntros (Φ) "_ HΦ". rewrite /prog.
  wp_alloc ℓ as "Hℓ". wp_let.
  wp_apply (body_spec with "Hℓ") as (y) "%Hy".
  iApply "HΦ". iPureIntro. lia.
Qed.

End proofs.

(**
  Iris ships with a bunch of different CMRAs that you can use out of the
  box. Rather than creating new resources for every new situation, we
  can instead compose existing CMRAs. For instance, our State resource
  algebra corresponds to [csum (excl ()) (agree ())].

  Some of the available CMRAs can be found here:

  <<https://gitlab.mpi-sws.org/iris/iris/-/tree/master/iris/algebra>>
*)
