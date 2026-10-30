(** * Section 4.5 The sign homomorphism

    Part of Chapter 4 ([group.tex]); see [Group.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Counting over finite types uses the library's [Finite] and [finadd]
      (sums of natural numbers over a finite type); we add [finadd_add]
      and a parity function [even] with [even_add], [even_double].
    - [BSG2] ([BΣ_2], the component of [Fin 2] in [Set]); for [T : BSG2]
      the underlying set [el2 T] has decidable equality, and two elements
      different from a third are equal ([el2_two]).
    - The parity relation [parity P] on [∏_{e:E} P(e)], for a finite [E]
      and [P : E → BΣ_2], via the number [ndis f g] of points where [f]
      and [g] disagree.
    - Lemma [lem:parityequiv]: [∼] is an equivalence relation
      ([parity_refl], [parity_symm], [parity_trans]); the quotient
      [SignQ P] is a 2-element set if [E] is (merely) nonempty
      ([SignQ_two]), and contractible if [E] is empty ([SignQ_empty]).
      Instead of the book's Venn diagram we use that, pointwise,
      [d(f,g) + d(g,h) = d(f,h) + 2·d(f,g)·d(g,h)] for the disagreement
      counts ([dis_trans]), so that parities add up ([parity_sum]).  For
      a given [f₀], [[g] ↦ even(ndis f₀ g)] is an equivalence
      [SignQ P ≃ Bool] ([phi], [SignQ_eqv_Bool]); surjectivity uses
      [f₀] changed at a single point ([flip]).
    - Definition [def:mu_E]: [mu_E : Hom(Σ_2^E, Σ_2)], with [Σ_2^E] the
      product [PiG] of Section 4.2, by deciding whether [E] is merely
      inhabited.  The pointing path identifies the class of the constant
      function [fin2_0] with [true] and then with an element of [Fin 2].
    - Definition [def:sign-ordering]: for a finite [A], [EA] (2-element
      subsets as [S : A → Bool] with two elements), [PA],
      [LocalOrdering] and [SignOrdering].

    - The unpointed map [Bsgn : BΣ_n → BΣ_2], [Bsgn(A) :≡ Bμ_{E(A)}(P)]
      ([Bsgn]); given a pointing [p], the sign homomorphism [sgn n p]
      (definition [def:sgn]) and the alternating group [AG], with [BAG]
      and [shAG] (definition [def:alternating-groups], given proofs that
      [BAG] is a connected groupoid); definition [def:sgn-permutation]
      ([sign], via [Bsgn] and [two_element_loops_Bool]).
    - The exercise after [def:mu_E] ([xca_Umu_product], statement
      [xca_Umu_product_stmt]): [Uμ_E(s)] is [+1] iff the number of [e]
      with [s(e) = -1] is even.  Placed at the end, since it uses
      [loops2_Bool].  Instead of computing the pointing path we use that
      a loop of a 2-element set is trivial iff it has a fixed point
      ([fix_refl]), and that [Uμ_E(s)] has one iff the action of [s] on
      sign orderings fixes a class ([sact_fix]).
    - Lemma [lem:sign-properties] ([lem_sign_properties]: parts
      [sign_transp], [sign_kcycle], [identity_even]) and corollary
      [cor:sign-defined] ([cor_sign_defined]), for any finite set [A];
      placed at the end, with statements [lem_sign_properties_stmt] and
      [cor_sign_defined_stmt] at the anchors.  [sign] is multiplicative
      ([sign_comp]).  Transport along [perm_of A σ] acts on sign
      orderings as [σ] acts on local orderings ([actLO], [trp_sign]), so
      [sign σ] is the parity of the number of 2-element subsets on which
      [g] and [σ·g] disagree, for any local ordering [g] ([sign_ndis]).
      Deviation: for part [it:sign-transposition] the book uses the
      standard local ordering of [{1,…,n}] and the transposition [(1 2)];
      we take any transposition [(a b)] of any [A] and a local ordering
      that chooses [a] where possible, and else [b] where possible
      ([gab]).  It disagrees with its image under [(a b)] only at
      [{a, b}] ([dis_gab]).

    - Exercise [xca:sign-by-crossings] ([xca_sign_by_crossings], with
      [inversions]): with the standard local ordering [gmin], the
      2-element subsets where [gmin] and [σ⁻¹·gmin] disagree are the
      inversions of [σ] ([inversions_ndis]).
    - The exercise on even permutations ([even_perms_count]): for
      [n ≥ 2] there are [n!/2] of them, since composing with a
      transposition exchanges even and odd permutations ([Ev_Od]).
      Both exercises are placed at the end, with statements at the
      anchors.

    Left out (statements only, no proofs yet)
    - The pointing of [Bsgn] by the standard sign ordering of [Fin n]
      ([Bsgn_pt_stmt]) and that [BAG] is a connected groupoid
      ([BAG_isConn_stmt]).
    - Exercise [xca:isos_A3_C3] ([xca_isos_A3_C3_stmt]), which needs
      both. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Types.Sum Types.Unit Truncations.Core Spaces.Nat.Core
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite Spaces.List.Core Colimits.Quotient.
From SymmetryBook Require Export Group.S04_Homomorphisms.

Local Open Scope uf_scope.

(** ** 4.5 The sign homomorphism *)

(** ** Finite sums of natural numbers

    We count with the library's [finadd] over a finite type ([Finite], the
    library's notion, equivalent to [isFinSet] by [isFinSet_Finite]). *)

Definition sigma_sum_distrib {X : Type} (Y Z : X -> Type)
  : {x : X & Y x + Z x} ≃ ({x : X & Y x} + {x : X & Z x}).
Proof.
  refine (mkEqv (fun w => match snd w with
                          | inl y => inl (fst w; y)
                          | inr z => inr (fst w; z) end)
                (fun s => match s with
                          | inl w => (fst w; inl (snd w))
                          | inr w => (fst w; inr (snd w)) end) _ _).
  - intros [x [y|z]]; exact refl.
  - intros [[x y]|[x z]]; exact refl.
Defined.

Definition finadd_add `{Funext} {X : Type} `{Finite X} (f g : X -> nat)
  : finadd (fun x => (f x + g x)%nat) = (finadd f + finadd g)%nat.
Proof.
  refine (_ @ (fcard_sigma (fun x => Fin (f x) + Fin (g x)))^ @ _).
  - apply ap. apply path_forall. intro x. exact (fcard_sum (Fin (f x)) (Fin (g x)))^.
  - refine (fcard_equiv' (Equiv_of_Eqv (sigma_sum_distrib _ _)) @ _).
    exact (fcard_sum _ _).
Defined.

(** Parity: [even n] is [yes] for even [n]. *)
Fixpoint even (n : nat) : Bool
  := match n with O => true | S n' => negb (even n') end.

Definition even_add (a b : nat) : even (a + b)%nat = (if even a then even b else negb (even b)).
Proof.
  induction a as [|a IH]; cbn.
  - exact refl.
  - rewrite IH. destruct (even a), (even b); exact refl.
Defined.

Definition even_double (k : nat) : even (k + k)%nat = true.
Proof.
  rewrite even_add. destruct (even k); exact refl.
Defined.

(** ** The parity relation *)

(** [BΣ_2], the component of [Fin 2] in [Set]: the 2-element sets. *)
Definition BSG2 : Type := component SetU (FinSetU 2).

Definition el2 (T : BSG2) : Type := fst (fst T).

Definition el2_isSet (T : BSG2) : isSet (el2 T) := snd (fst T).

Definition el2_Fin2 (T : BSG2) : ptrunc (Fin 2 = el2 T)
  := ptrunc_rec ptrunc_isProp (fun p => trunc (ap fst p)) (snd T).

Definition el2_isDecSet `{Funext} (T : BSG2) : isDecSet (el2 T)
  := ptrunc_rec (isDecSet_isProp _)
       (fun p : Fin 2 = el2 T => trp isDecSet p (Fin_isDecSet 2)) (el2_Fin2 T).

Definition el2_dec `{Funext} (T : BSG2) (x y : el2 T) : isDecidable (x = y)
  := snd (el2_isDecSet T x y).

(** In a 2-element set, two elements different from a third are equal. *)
Definition el2_two `{Funext} (T : BSG2) (x y z : el2 T)
  : x ≠ y -> y ≠ z -> x = z.
Proof.
  intros nxy nyz.
  refine (ptrunc_rec (el2_isSet T x z) _ (el2_Fin2 T)). intro p.
  revert x y z nxy nyz. destruct p. intros x y z nxy nyz.
  destruct (Fin2_elems x) as [ex|ex], (Fin2_elems y) as [ey|ey], (Fin2_elems z) as [ez|ez];
    first [ exact (ex @ ez^) | destruct (nxy (ex @ ey^)) | destruct (nyz (ey @ ez^)) ].
Defined.

Section Parity.

  Context `{Funext} {E : Type} `{Finite E} (P : E -> BSG2).

  Local Notation Pi := (forall e, el2 (P e)).

  (** The number of points at which [f] and [g] disagree. *)
  Definition dis (f g : Pi) (e : E) : nat
    := match el2_dec (P e) (f e) (g e) with inl _ => 0 | inr _ => 1 end%nat.

  Definition ndis (f g : Pi) : nat := finadd (dis f g).

  (** The parity relation [f ∼ g]: [f] and [g] disagree in an even number
      of points. *)
  Definition parity (f g : Pi) : Type := even (ndis f g) = true.

  Definition parity_isProp (f g : Pi) : isProp (parity f g)
    := fun a b => isSet_bool _ _ a b.

  Definition dis_refl (f : Pi) (e : E) : dis f f e = 0%nat.
  Proof.
    unfold dis. destruct (el2_dec (P e) (f e) (f e)) as [r|n].
    - exact refl.
    - destruct (n refl).
  Defined.

  Definition dis_symm (f g : Pi) (e : E) : dis f g e = dis g f e.
  Proof.
    unfold dis.
    destruct (el2_dec (P e) (f e) (g e)) as [r|n], (el2_dec (P e) (g e) (f e)) as [r'|n'];
      try exact refl.
    - destruct (n' r⁻¹).
    - destruct (n r'⁻¹).
  Defined.

  (** Both disagree. *)
  Definition dis2 (f g h : Pi) (e : E) : nat
    := match el2_dec (P e) (f e) (g e), el2_dec (P e) (g e) (h e) with
       | inr _, inr _ => 1 | _, _ => 0 end%nat.

  Definition dis_trans (f g h : Pi) (e : E)
    : (dis f g e + dis g h e)%nat = (dis f h e + (dis2 f g h e + dis2 f g h e))%nat.
  Proof.
    unfold dis, dis2.
    destruct (el2_dec (P e) (f e) (g e)) as [r1|n1],
      (el2_dec (P e) (g e) (h e)) as [r2|n2],
      (el2_dec (P e) (f e) (h e)) as [r3|n3]; try exact refl.
    - destruct (n3 (r2 ⋅ r1)).
    - destruct r1. destruct (n2 r3).
    - destruct r2. destruct (n1 r3).
    - destruct (n3 (el2_two (P e) _ _ _ n1 n2)).
  Defined.

  (** Lemma [lem:parityequiv], first part: [∼] is an equivalence relation. *)
  Definition parity_refl (f : Pi) : parity f f.
  Proof.
    unfold parity, ndis.
    rewrite (path_forall _ _ (dis_refl f)).
    rewrite (finadd_const E 0).
    rewrite nat_mul_zero_r. exact refl.
  Defined.

  Definition parity_symm (f g : Pi) : parity f g -> parity g f.
  Proof.
    unfold parity, ndis. rewrite (path_forall _ _ (dis_symm f g)). exact idmap.
  Defined.

  Definition parity_trans (f g h : Pi) : parity f g -> parity g h -> parity f h.
  Proof.
    unfold parity, ndis. intros a b.
    pose (e := ap even (finadd_add (dis f g) (dis g h))^
               @ ap (fun k => even (finadd k)) (path_forall _ _ (dis_trans f g h))
               @ ap even (finadd_add _ _)
               @ ap even (ap (nat_add _) (finadd_add (dis2 f g h) (dis2 f g h)))).
    rewrite even_add, even_add, even_double, a, b in e. cbn in e.
    destruct (even (finadd (dis f h))); [exact refl | exact e^].
  Defined.

End Parity.

(** ** The quotient by the parity relation *)
Section ParityQuotient.

  Context `{Univalence} {E : Type} `{Finite E} (P : E -> BSG2).

  Local Notation Pi := (forall e, el2 (P e)).

  (** Parities add up. *)
  Definition parity_sum (f g h : Pi)
    : even (ndis P f h)
      = (if even (ndis P f g) then even (ndis P g h) else negb (even (ndis P g h))).
  Proof.
    unfold ndis.
    pose (e := ap even (finadd_add (dis P f g) (dis P g h))^
               @ ap (fun k => even (finadd k)) (path_forall _ _ (dis_trans P f g h))
               @ ap even (finadd_add _ _)
               @ ap even (ap (nat_add _) (finadd_add (dis2 P f g h) (dis2 P f g h)))).
    rewrite even_add, even_add, even_double in e.
    refine (_ @ e^).
    destruct (even (finadd (dis P f h))); exact refl.
  Defined.

  Definition ndis_symm (f g : Pi) : ndis P f g = ndis P g f
    := ap finadd (path_forall _ _ (dis_symm P f g)).

  (** Sign orderings (in the general setting): [∏_e P(e) / ∼]. *)
  Definition SignQ : Type := Quotient (parity P).

  Definition SignQ_isSet : isSet SignQ := IsHSet_isSet _.

  (** Given [f₀], classes are determined by the parity of the distance to
      [f₀]. *)
  Definition phi (f0 : Pi) : SignQ -> Bool.
  Proof.
    refine (Quotient_rec _ Bool (fun g => even (ndis P f0 g)) _).
    intros g g' a. unfold parity in a.
    refine (_ @ (parity_sum f0 g g')^).
    rewrite a. destruct (even (ndis P f0 g)); exact refl.
  Defined.

  Definition phi_class (f0 g : Pi) : phi f0 (class_of _ g) = even (ndis P f0 g) := refl.

  Definition phi_inj (f0 : Pi) (x y : SignQ) : phi f0 x = phi f0 y -> x = y.
  Proof.
    revert x y.
    refine (Quotient_ind2_hprop _ _ _). intros g g' e.
    apply qglue. unfold parity.
    refine (parity_sum g f0 g' @ _).
    rewrite (ndis_symm g f0). change (even (ndis P f0 g) = even (ndis P f0 g')) in e.
    rewrite e. destruct (even (ndis P f0 g')); exact refl.
  Defined.

  (** Changing [f₀] at one point [e₀]. *)
  Definition flip (f0 : Pi) (e0 : E) (y : el2 (P e0)) : Pi
    := fun e => match dec_paths e e0 with
                | inl r => trp (fun e => el2 (P e)) r⁻¹ y
                | inr _ => f0 e end.

  Definition delta (e0 e : E) : nat := match dec_paths e e0 with inl _ => 1 | inr _ => 0 end%nat.

  Definition dis_flip (f0 : Pi) (e0 : E) (y : el2 (P e0)) (n : y ≠ f0 e0)
    : dis P f0 (flip f0 e0 y) = delta e0.
  Proof.
    apply path_forall. intro e. unfold dis, flip, delta.
    destruct (dec_paths e e0) as [r|r].
    - destruct r. change (match el2_dec (P e) (f0 e) y with inl _ => 0 | inr _ => 1 end%nat = 1%nat).
      destruct (el2_dec (P e) (f0 e) y) as [q|q].
      + destruct (n q⁻¹).
      + exact refl.
    - destruct (el2_dec (P e) (f0 e) (f0 e)) as [q|q].
      + exact refl.
      + destruct (q refl).
  Defined.

  Definition delta_eqv (e0 e : E) : Fin (delta e0 e) <~> (e = e0).
  Proof.
    unfold delta. destruct (dec_paths e e0) as [r|r].
    - refine (Equiv_of_Eqv (Eqv_of_props Fin1_isProp _ (fun _ => r) (fun _ => fin1_0))).
      intros a b. apply path_ishprop.
    - refine (Equiv_of_Eqv (Eqv_of_props (fun x : Fin 0 => match x with end) _
                (fun x : Fin 0 => match x with end) (fun q => match r q with end))).
      intros a b. apply path_ishprop.
  Defined.

  Definition finadd_delta (e0 : E) : finadd (delta e0) = 1%nat.
  Proof.
    unfold finadd.
    refine (fcard_equiv' (Y := Unit) _ @ _).
    - refine (equiv_compose' (@equiv_contr_unit _ _) (equiv_functor_sigma_id (delta_eqv e0))).
    - exact refl.
  Defined.

  (** An element of [P(e₀)] different from a given one. *)
  Definition el2_other (T : BSG2) (x : el2 T) : ptrunc {y : el2 T & y ≠ x}.
  Proof.
    refine (ptrunc_rec ptrunc_isProp _ (el2_Fin2 T)). intro p.
    revert x. destruct p. intro x.
    destruct (Fin2_elems x) as [ex|ex]; destruct ex^.
    - exact (trunc (fin2_1; fun q => inl_ne_inr _ _ q^)).
    - exact (trunc (fin2_0; fun q => inl_ne_inr _ _ q)).
  Defined.

  (** For [E] nonempty, [φ_{f₀}] is an equivalence. *)
  Definition phi_isEquiv (f0 : Pi) (ne : ptrunc E) : isEquiv (phi f0).
  Proof.
    refine (inj_surj_isEquiv (cancel_isInj isSet_bool (phi_inj f0)) _).
    intros [].
    - apply trunc. refine (class_of _ f0; _).
      exact (parity_refl P f0)^.
    - refine (ptrunc_rec ptrunc_isProp _ ne). intro e0.
      refine (ptrunc_rec ptrunc_isProp _ (el2_other (P e0) (f0 e0))). intros [y0 ny].
      apply trunc. refine (class_of _ (flip f0 e0 y0); _).
      change (no = even (finadd (dis P f0 (flip f0 e0 y0)))).
      rewrite (dis_flip f0 e0 y0 ny), finadd_delta. exact refl.
  Defined.

  Definition SignQ_eqv_Bool (f0 : Pi) (ne : ptrunc E) : SignQ ≃ Bool
    := (phi f0; phi_isEquiv f0 ne).

  (** Lemma [lem:parityequiv], second part: if [E] is nonempty, the
      quotient is a 2-element set. *)
  Definition SignQ_two (ne : ptrunc E) : ptrunc (Fin 2 = SignQ).
  Proof.
    (* an element [f₀] of [∏_e P(e)], by finite choice *)
    refine (ptrunc_rec ptrunc_isProp _
              (@finite_choice E _ (fun e => el2 (P e)) (fun _ => tt)
                 (fun e => ptrunc_rec ptrunc_isProp
                             (fun p : Fin 2 = el2 (P e) => tr (trp idmap p fin2_0))
                             (el2_Fin2 (P e))))).
    intro f0. apply trunc.
    exact (etop (Eqv_inv (SignQ_eqv_Bool f0 ne)) ⋅ Fin2_Bool_path).
  Defined.

  Definition SignQ_BSG2 (ne : ptrunc E) : BSG2
    := ((SignQ; SignQ_isSet);
        ptrunc_rec ptrunc_isProp
          (fun p : Fin 2 = SignQ =>
             trunc (path_sigma_prop (fun X => isSet_isProp X)
                      (u := FinSetU 2) (v := (SignQ; SignQ_isSet)) p))
          (SignQ_two ne)).

  (** If [E] is empty, the quotient is contractible. *)
  Definition SignQ_empty (ne : ¬ E) : isContr SignQ.
  Proof.
    pose (f0 := fun e => match ne e with end : el2 (P e)).
    refine (class_of _ f0; _).
    refine (Quotient_ind_hprop _ _ _). intro g.
    apply qglue.
    assert (r : f0 = g) by (apply path_forall; intro e; destruct (ne e)).
    destruct r. exact (parity_refl P f0).
  Defined.

End ParityQuotient.

(** Definition [def:mu_E]: [μ_E : Hom(Σ_2^E, Σ_2)], by deciding whether
    [E] is nonempty.  The classifying type of [Σ_2^E] is [E → BΣ_2],
    pointed at the constant family [Fin 2]; for [E] nonempty, [Bμ_E(P) :≡
    (∏_e P(e))/∼], pointed via [φ] at the constant function [fin2_0]. *)
Section Mu.

  Context `{Univalence} {E : Type} (hE : isFinSet E).

  #[local] Instance FE : Finite E := isFinSet_Finite hE.

  Definition P0 : E -> BSG2 := fun _ => sh (SG 2).

  Definition Bmu_pt (ne : ptrunc E) : sh (SG 2) = SignQ_BSG2 P0 ne.
  Proof.
    refine (path_sigma_prop (fun _ => ptrunc_isProp) _).
    refine (path_sigma_prop (fun X => isSet_isProp X) (u := FinSetU 2)
              (v := (SignQ P0; SignQ_isSet P0)) _).
    exact (etop (Eqv_inv (SignQ_eqv_Bool P0 (fun _ => fin2_0) ne)) ⋅ Fin2_Bool_path).
  Defined.

  Definition mu_E : Hom (PiG hE (fun _ => SG 2)) (SG 2).
  Proof.
    destruct (decidable_merely_finite E) as [ne|ne].
    - exact (@mkhom (PiG hE (fun _ => SG 2)) (SG 2)
               ((fun P => SignQ_BSG2 P ne); Bmu_pt ne)).
    - exact (@mkhom (PiG hE (fun _ => SG 2)) (SG 2) ((fun _ => sh (SG 2)); refl)).
  Defined.

End Mu.

(** Definition [def:sign-ordering]: for a finite set [A], the set [E(A)]
    of 2-element subsets (as decidable subsets [S : A → Bool] with two
    elements), the family [P] of their underlying 2-element sets, local
    orderings [∏_{e:E(A)} P(e)] and sign orderings
    [(∏_{e:E(A)} P(e))/∼]. *)
Section SignOrdering.

  Context `{Univalence} (A : Type) `{Finite A}.

  #[local] Instance Bool_Finite : Finite Bool
    := finite_equiv' (Fin 2) (Equiv_of_Eqv Fin2_Bool) _.

  Definition sub_el (S : A -> Bool) : Type := {a : A & S a = true}.

  Definition EA : Type := {S : A -> Bool & fcard (sub_el S) = 2%nat}.

  #[local] Instance EA_Finite : Finite EA.
  Proof.
    apply finite_sigma; [exact _ |]. intro S.
    apply finite_decidable_hprop; exact _.
  Defined.

  Definition sub_el_isSet (S : A -> Bool) : isSet (sub_el S) := IsHSet_isSet _.

  Definition PA (e : EA) : BSG2.
  Proof.
    refine ((sub_el (fst e); sub_el_isSet (fst e)); _).
    refine (Trunc_functor (-1) _ (merely_equiv_fin (sub_el (fst e)))). intro f.
    refine (path_sigma_prop (fun X => isSet_isProp X) (u := FinSetU 2)
              (v := (sub_el (fst e); sub_el_isSet (fst e))) _).
    refine ((etop (Eqv_of_Equiv f))⁻¹ ⋅ _).
    exact (ap Fin (snd e)⁻¹).
  Defined.

  Definition LocalOrdering : Type := forall e : EA, el2 (PA e).

  Definition SignOrdering : Type := SignQ PA.

End SignOrdering.

(** ** Left-out results of this section

    Definition [def:sgn] needs a pointing of [Bsgn], from the standard
    sign ordering of [Fin n]; we define the unpointed map [Bsgn] and state
    the rest relative to a pointing [p] (statements only). *)
Section Sign.

  Context `{Univalence}.

  Definition comp_isFinSet {n : ℕ} (A : utype (BG (SG n))) : isFinSet (fst (fst A))
    := ptrunc_rec ptrunc_isProp (fun p => trunc (n; (ap fst p)⁻¹)) (snd A).

  Definition comp_Finite {n : ℕ} (A : utype (BG (SG n))) : Finite (fst (fst A))
    := isFinSet_Finite (comp_isFinSet A).

  (** Definition [def:sgn], without the pointing:
      [Bsgn(A) :≡ Bμ_{E(A)}(P)]. *)
  Definition Bsgn (n : ℕ) (A : utype (BG (SG n))) : utype (BG (SG 2))
    := fst (Bf (mu_E (Finite_isFinSet (@EA_Finite _ (fst (fst A)) (comp_Finite A)))))
         (@PA _ (fst (fst A)) (comp_Finite A)).

  (** The pointing of [Bsgn] from the standard ordering of [Fin n]. *)
  Definition Bsgn_pt_stmt : Type := forall n : ℕ, sh (SG 2) = Bsgn n (sh (SG n)).

  (** The sign homomorphism, given a pointing. *)
  Definition sgn (n : ℕ) (p : sh (SG 2) = Bsgn n (sh (SG n))) : Hom (SG n) (SG 2)
    := mkhom ((Bsgn n; p) : BG (SG n) →* BG (SG 2)).

  (** Definition [def:alternating-groups]: [BA_n :≡ ∑_{A:BΣ_n} Bsgn(A)],
      pointed at [(Fin n, p(fin2_0))]; that it is connected (so that
      [A_n] is a group) is stated only. *)
  Definition BAG (n : ℕ) : Type := {A : utype (BG (SG n)) & el2 (Bsgn n A)}.

  Definition shAG (n : ℕ) (p : sh (SG 2) = Bsgn n (sh (SG n))) : BAG n
    := (sh (SG n); trp el2 p (fin2_0 : el2 (sh (SG 2)))).

  Definition BAG_isConn_stmt : Type := forall n : ℕ, isConn (BAG n) × isGrpd (BAG n).

  Definition AG (n : ℕ) (p : sh (SG 2) = Bsgn n (sh (SG n))) (c : isConn (BAG n))
    (g : isGrpd (BAG n)) : Group
    := mkgroup (BAG n; (shAG n p; (c; g))).

  (** Exercise [xca:isos_A3_C3]. *)
  Definition xca_isos_A3_C3_stmt : Type
    := forall p c g, {i : Iso (AG 3 p c g) (CG 3) & {j : Iso (AG 3 p c g) (CG 3) & i ≠ j}}.

  (** The identification of the symmetries of a [2]-element set with
      [Bool] ([+1] is [yes]). *)
  Definition loops2_Bool (T : utype (BG (SG 2))) : el2 T = el2 T -> Bool
    := ptoe (two_element_loops_Bool
               (fst T; ptrunc_rec ptrunc_isProp (fun q => trunc (ap fst q)) (snd T))).

  (** Definition [def:sgn-permutation]: the sign of a permutation [σ] of
      an [n]-element set [A], as the effect of [Bsgn] on [σ]. *)
  Definition sign {n : ℕ} {A : utype (BG (SG n))} (σ : A = A) : Bool
    := loops2_Bool (Bsgn n A) (ap (fun B => el2 (Bsgn n B)) σ).

  (** A permutation of an element of [BΣ_n] from an equivalence. *)
  Definition perm_of {n : ℕ} (A : utype (BG (SG n))) (e : fst (fst A) ≃ fst (fst A)) : A = A
    := path_sigma_prop (fun _ => ptrunc_isProp) (u := A) (v := A)
         (path_sigma_prop (fun X => isSet_isProp X) (u := fst A) (v := fst A) (etop e)).

  (** Lemma [lem:sign-properties]: parts [it:sign-transposition],
      [it:sign-cycle] and [it:identity-even], in this order (proved
      below, [lem_sign_properties]). *)
  Definition lem_sign_properties_stmt : Type
    := (forall n (A : utype (BG (SG n))) (a b : fst (fst A)) (ne : a ≠ b),
          sign (perm_of A (transpEqv (finset_isDecSet (comp_isFinSet A)) a b)) = no)
       × (forall n (A : utype (BG (SG n))) (k : ℕ) (σ : fst (fst A) ≃ fst (fst A)),
            isKCycle (finset_isDecSet (comp_isFinSet A)) k σ ->
            sign (perm_of A σ) = even (pred k))
       × (forall n (A : utype (BG (SG n))) (l : list (fst (fst A) × fst (fst A))),
            all_pairs_ne l ->
            (forall x, transpsL (finset_isDecSet (comp_isFinSet A)) l x = x) ->
            even (length l) = true).

  (** Corollary [cor:sign-defined] (proved below, [cor_sign_defined]). *)
  Definition cor_sign_defined_stmt : Type
    := forall n (A : utype (BG (SG n))) (σ : fst (fst A) ≃ fst (fst A))
              (l l' : list (fst (fst A) × fst (fst A))),
         all_pairs_ne l -> all_pairs_ne l' ->
         (forall x, fst σ x = transpsL (finset_isDecSet (comp_isFinSet A)) l x) ->
         (forall x, fst σ x = transpsL (finset_isDecSet (comp_isFinSet A)) l' x) ->
         (even (length l) = even (length l')) × (sign (perm_of A σ) = even (length l)).

  (** Exercise [xca:sign-by-crossings]: the sign is [(-1)^{inv(σ)}],
      counting inversions through [Fin n ≃ {k | k < n}] (proved below,
      [xca_sign_by_crossings]). *)
  Definition inversions (n : ℕ) (σ : Fin n ≃ Fin n) : ℕ
    := finadd (fun ij : Fin n * Fin n =>
         let i := fst (equiv_fin_finnat n (Overture.fst ij)) in
         let j := fst (equiv_fin_finnat n (Overture.snd ij)) in
         let si := fst (equiv_fin_finnat n (fst σ (Overture.fst ij))) in
         let sj := fst (equiv_fin_finnat n (fst σ (Overture.snd ij))) in
         if dec ((i < j)%nat * (sj < si)%nat) then 1%nat else 0%nat).

  Definition xca_sign_by_crossings_stmt : Type
    := forall (n : ℕ) (σ : Fin n ≃ Fin n),
         sign (perm_of (sh (SG n)) σ) = even (inversions n σ).

  (** The number of even permutations is [n!/2] for [n ≥ 2] (proved
      below, [even_perms_count]). *)
  Definition even_perms_count_stmt : Type
    := forall n : ℕ, (2 <= n)%nat ->
         {h : isFinSet {σ : sh (SG n) = sh (SG n) & sign σ = yes} &
           mul 2 (cardF h) = fact n}.

  (** The statement of the exercise after [def:mu_E] (proved below,
      [xca_Umu_product]). *)
  Definition xca_Umu_product_stmt : Type
    := forall (E : Type) (hE : isFinSet E) (s : E -> USym (SG 2)),
         loops2_Bool (sh (SG 2))
           (ap (fun B => el2 B)
              (USymf (mu_E hE) (eqinv (snd (USym_PiG hE (fun _ => SG 2))) s)))
         = even (@finadd E (isFinSet_Finite hE)
                   (fun e => if loops2_Bool (sh (SG 2)) (ap (fun B => el2 B) (s e))
                             then 0%nat else 1%nat)).

End Sign.

(** ** The exercise after [def:mu_E]

    We do not compute the pointing path [Bmu_pt]: a loop of a 2-element
    set is trivial iff it has a fixed point ([fix_refl]), and the loop
    [Uμ_E(s)] has a fixed point iff the action [g ↦ s·g] of [s] on
    sign orderings fixes a class [[g]] ([sact_fix]), i.e. iff [g] and
    [s·g] differ in an even number of points. *)
Section UmuProduct.

  Context `{Univalence}.

  Definition T2' (T : utype (BG (SG 2))) : FinSet_n 2
    := (fst T; ptrunc_rec ptrunc_isProp (fun q => trunc (ap fst q)) (snd T)).

  Definition loops2_Bool_loop (T : utype (BG (SG 2))) (q : el2 T = el2 T)
    : loops2_Bool T q = loop_Bool (T2' T) q
    := ap (fun e => fst e q) (ptoe_etop (loop_Bool (T2' T); loop_Bool_isEquiv (T2' T))).

  Definition loop2_dec (T : utype (BG (SG 2))) (q : el2 T = el2 T) : (q = refl) ⨿ (q ≠ refl)
    := loop_refl_dec (T2' T) q.

  Definition loops2_yes (T : utype (BG (SG 2))) (q : el2 T = el2 T) (r : q = refl)
    : loops2_Bool T q = yes.
  Proof.
    refine (loops2_Bool_loop T q @ _). unfold loop_Bool.
    destruct (loop_refl_dec (T2' T) q) as [_|n]; [exact refl | destruct (n r)].
  Defined.

  Definition loops2_no (T : utype (BG (SG 2))) (q : el2 T = el2 T) (n : q ≠ refl)
    : loops2_Bool T q = no.
  Proof.
    refine (loops2_Bool_loop T q @ _). unfold loop_Bool.
    destruct (loop_refl_dec (T2' T) q) as [r|_]; [destruct (n r) | exact refl].
  Defined.

  (** A loop of a 2-element set with a fixed point is trivial. *)
  Definition fix_refl (T : BSG2) (q : el2 T = el2 T) (x : el2 T) (h : ptoe q x = x)
    : q = refl.
  Proof.
    refine ((etop_ptoe q)^ @ _ @ etop_id _).
    apply ap. apply path_Eqv. apply ptw_inv. intro y.
    destruct (el2_dec T y x) as [r|n].
    - destruct r^. exact h.
    - refine (el2_two T _ x _ _ (fun r => n r⁻¹)).
      intro r. apply n. apply (Eqv_inj (idtoeqv q)). exact (r @ h^).
  Defined.

  Definition ptoe_ap_trans {A : Type} (f : A -> Type) {a b c : A} (r : a = b) (q : b = c) (x : f a)
    : ptoe (ap f (q ⋅ r)) x = ptoe (ap f q) (ptoe (ap f r) x).
  Proof. destruct q. exact refl. Defined.

  Definition ptoe_ap_inv {A : Type} (f : A -> Type) {a b : A} (q : a = b) (x : f b)
    : ptoe (ap f q) (ptoe (ap f q⁻¹) x) = x.
  Proof. destruct q. exact refl. Defined.

  Definition ptoe_ap_inv' {A : Type} (f : A -> Type) {a b : A} (q : a = b) (x : f a)
    : ptoe (ap f q⁻¹) (ptoe (ap f q) x) = x.
  Proof. destruct q. exact refl. Defined.

  Context {E : Type} (hE : isFinSet E).

  #[local] Instance FE' : Finite E := isFinSet_Finite hE.

  Definition sact (s : forall e : E, USym (SG 2)) (g : forall e, el2 (P0 (E := E) e))
    : forall e, el2 (P0 (E := E) e)
    := fun e => ptoe (ap el2 (s e)) (g e).

  Definition nsw (s : forall e : E, USym (SG 2)) : nat
    := @finadd E (isFinSet_Finite hE)
         (fun e => if loops2_Bool (sh (SG 2)) (ap (fun B => el2 B) (s e)) then 0%nat else 1%nat).

  Definition dis_sact (s : forall e : E, USym (SG 2)) (g : forall e, el2 (P0 (E := E) e)) (e : E)
    : dis (P0 (E := E)) g (sact s g) e
      = (if loops2_Bool (sh (SG 2)) (ap (fun B => el2 B) (s e)) then 0%nat else 1%nat).
  Proof.
    unfold dis, sact.
    destruct (loop2_dec (sh (SG 2)) (ap el2 (s e))) as [r|n].
    - rewrite (loops2_yes _ _ r).
      destruct (el2_dec (P0 (E := E) e) (g e) (ptoe (ap el2 (s e)) (g e))) as [_|m].
      + exact refl.
      + destruct (m (ap (fun q => ptoe q (g e)) r)^).
    - rewrite (loops2_no _ _ n).
      destruct (el2_dec (P0 (E := E) e) (g e) (ptoe (ap el2 (s e)) (g e))) as [m|_].
      + destruct (n (fix_refl (P0 (E := E) e) _ (g e) m^)).
      + exact refl.
  Defined.

  Definition ndis_sact (s : forall e : E, USym (SG 2)) (g : forall e, el2 (P0 (E := E) e))
    : ndis (P0 (E := E)) g (sact s g) = nsw s
    := ap finadd (path_forall _ _ (dis_sact s g)).

  Definition trp_SignQ (ne : ptrunc E) {P P' : E -> BSG2} (p : P = P') (g : forall e, el2 (P e))
    : ptoe (ap (fun P => el2 (SignQ_BSG2 P ne)) p) (class_of _ g)
      = class_of _ (fun e => ptoe (ap el2 (apD10 p e)) (g e)).
  Proof. destruct p. exact refl. Defined.

  (** The action of [s] on sign orderings fixes a point iff the number of
      nontrivial [s(e)] is even. *)
  Definition sact_fix (ne : ptrunc E) (s : forall e : E, USym (SG 2))
    (p : P0 (E := E) = P0 (E := E)) (hp : apD10 p = s) (y : SignQ (P0 (E := E)))
    : (ptoe (ap (fun P => el2 (SignQ_BSG2 P ne)) p) y = y) <-> (even (nsw s) = true).
  Proof.
    revert y. refine (Quotient_ind_hprop _ _ _). intro g.
    rewrite trp_SignQ, hp.
    change (class_of (parity (P0 (E := E))) (sact s g) = class_of (parity (P0 (E := E))) g
            <-> even (nsw s) = true).
    split.
    - intro r. refine (trp (fun k => even k = true) (ndis_sact s g) _).
      pose (r' := ap (phi (P0 (E := E)) g) r). exact (r' @ parity_refl (P0 (E := E)) g).
    - intro r. apply qglue. apply parity_symm.
      exact (trp (fun k => even k = true) (ndis_sact s g)^ r).
  Defined.

  Definition ptoe_ap_compose {A B : Type} (f : A -> B) (h : B -> Type) {a b : A} (q : a = b) (z : h (f a))
    : ptoe (ap h (ap f q)) z = ptoe (ap (fun x => h (f x)) q) z.
  Proof. destruct q. exact refl. Defined.

  Context (s : forall e : E, USym (SG 2)) (p : P0 (E := E) = P0 (E := E)) (hp : apD10 p = s).

  Definition Umu_product_ne (ne : ptrunc E)
    : loops2_Bool (sh (SG 2))
        (ap (fun B => el2 B) ((Bmu_pt hE ne)⁻¹ ⋅ (ap (fun P => SignQ_BSG2 P ne) p ⋅ Bmu_pt hE ne)))
      = even (nsw s).
  Proof.
    pose (B := Bmu_pt hE ne).
    pose (x := fin2_0 : el2 (sh (SG 2))).
    pose (y := ptoe (ap el2 B) x).
    pose (T := ptoe (ap (fun P => el2 (SignQ_BSG2 P ne)) p)).
    assert (hL : forall z, ptoe (ap el2 (B⁻¹ ⋅ (ap (fun P => SignQ_BSG2 P ne) p ⋅ B))) z
                           = ptoe (ap el2 B⁻¹) (T (ptoe (ap el2 B) z))).
    { intro z. refine (ptoe_ap_trans _ _ _ _ @ _). apply ap.
      exact (ptoe_ap_trans _ _ _ _ @ ptoe_ap_compose (fun P => SignQ_BSG2 P ne) el2 p _). }
    destruct (sact_fix ne s p hp y) as [f1 f2].
    destruct (loop2_dec (sh (SG 2)) (ap el2 (B⁻¹ ⋅ (ap (fun P => SignQ_BSG2 P ne) p ⋅ B)))) as [r|n].
    - refine (loops2_yes _ _ r @ _). symmetry. apply f1.
      refine ((ptoe_ap_inv el2 B (T y))^ @ _). apply ap.
      exact ((hL x)^ @ ap (fun q => ptoe q x) r).
    - refine (loops2_no _ _ n @ _). revert f1 f2. destruct (even (nsw s)); intros f1 f2.
      + destruct (n (fix_refl (sh (SG 2)) _ x (hL x @ ap (ptoe (ap el2 B⁻¹)) (f2 refl)
                                                  @ ptoe_ap_inv' el2 B x))).
      + exact refl.
  Defined.

  Definition Umu_product_empty (ne : ¬ ptrunc E)
    : loops2_Bool (sh (SG 2))
        (ap (fun B => el2 B) (refl⁻¹ ⋅ (ap (fun _ : E -> BSG2 => sh (SG 2)) p ⋅ refl)))
      = even (nsw s).
  Proof.
    refine (loops2_yes _ _ (ap (fun q => ap el2 (refl⁻¹ ⋅ (q ⋅ refl))) (ap_const p _)) @ _).
    unfold nsw.
    assert (r : (fun e => if loops2_Bool (sh (SG 2)) (ap (fun B => el2 B) (s e)) then 0%nat else 1%nat)
                = (fun _ : E => 0%nat)).
    { apply path_forall. intro e. destruct (ne (trunc e)). }
    rewrite r, (finadd_const E 0), nat_mul_zero_r. exact refl.
  Defined.

End UmuProduct.

(** The exercise after [def:mu_E]: [Uμ_E] maps [s : E → {±1}] to the
    product of its values, i.e. [Uμ_E(s)] is [+1] iff the number of [e]
    with [s(e) = -1] is even.  (Placed here since it uses [loops2_Bool].) *)
Definition xca_Umu_product `{Univalence} : xca_Umu_product_stmt.
Proof.
  intros E hE s.
  pose (p := eqinv (snd (USym_PiG hE (fun _ => SG 2))) s).
  pose (hp := eqinv_r (snd (USym_PiG hE (fun _ => SG 2))) s : apD10 p = s).
  change (loops2_Bool (sh (SG 2)) (ap (fun B => el2 B) (USymf (mu_E hE) p)) = even (nsw hE s)).
  unfold USymf, mu_E. destruct (@decidable_merely_finite E (FE hE)) as [ne|ne].
  - exact (Umu_product_ne hE s p hp ne).
  - exact (Umu_product_empty hE s p ne).
Defined.


(** ** Lemma [lem:sign-properties] and corollary [cor:sign-defined]

    The book's proof uses that [sgn] is a homomorphism and computes the
    sign of a transposition relative to the standard local ordering of
    [{1,…,n}].  We work with an arbitrary finite set [A]:
    - [sign] is multiplicative ([sign_comp]), since a loop of a 2-element
      set is trivial iff it fixes a point ([loops2_at], [loops2_trans]);
    - transport along [perm_of A σ] acts on sign orderings by
      [[g] ↦ [σ·g]], with [(σ·g)(S) :≡ σ(g(σ⁻¹S))] ([actLO], [trp_sign]);
      hence [sign σ] is the parity of the number of 2-element subsets on
      which [g] and [σ·g] disagree, for any local ordering [g]
      ([sign_ndis]);
    - for the transposition [(a b)] we take a local ordering [g] that
      chooses [a] in every subset containing [a], and [b] in every subset
      containing [b] but not [a] ([gab]); then [g] and [(a b)·g]
      disagree only at [{a, b}] ([dis_gab]), so the sign is [-1]
      ([sign_transp]).  No ordering of [A] is needed. *)

Section SignHom.
  Context `{Univalence}.

  (** Whether a loop of a 2-element set is trivial, decided at any point. *)
  Definition loops2_at (T : utype (BG (SG 2))) (q : el2 T = el2 T) (x : el2 T)
    : loops2_Bool T q = (match el2_dec T (ptoe q x) x with inl _ => yes | inr _ => no end).
  Proof.
    destruct (loop2_dec T q) as [r|n].
    - refine (loops2_yes T q r @ _).
      destruct (el2_dec T (ptoe q x) x) as [_|m]; [exact refl|].
      destruct (m (ap (fun q => ptoe q x) r)).
    - refine (loops2_no T q n @ _).
      destruct (el2_dec T (ptoe q x) x) as [m|_]; [|exact refl].
      destruct (n (fix_refl T q x m)).
  Defined.

  Definition ptoe_trans {X Y Z : Type} (r : X = Y) (q : Y = Z) (x : X)
    : ptoe (q ⋅ r) x = ptoe q (ptoe r x).
  Proof. destruct q. exact refl. Defined.

  (** Multiplication in [{±1}], with [+1] as [yes]. *)
  Definition bmul (b c : Bool) : Bool := if b then c else negb c.

  (** [loops2_Bool] is a homomorphism. *)
  Definition loops2_trans (T : utype (BG (SG 2))) (q r : el2 T = el2 T)
    : loops2_Bool T (q ⋅ r) = bmul (loops2_Bool T q) (loops2_Bool T r).
  Proof.
    refine (ptrunc_rec (isSet_bool _ _) _ (el2_Fin2 T)). intro w.
    pose (x0 := trp idmap w fin2_0).
    rewrite (loops2_at T (q ⋅ r) x0), (loops2_at T r x0), (loops2_at T q (ptoe r x0)).
    rewrite (ptoe_trans r q x0).
    destruct (el2_dec T (ptoe r x0) x0) as [e1|n1],
      (el2_dec T (ptoe q (ptoe r x0)) (ptoe r x0)) as [e2|n2],
      (el2_dec T (ptoe q (ptoe r x0)) x0) as [e3|n3]; try exact refl.
    - destruct (n3 (e2 @ e1)).
    - destruct (n2 (e3 @ e1^)).
    - destruct (n1 (e2^ @ e3)).
    - destruct (n3 (el2_two T _ _ _ n2 n1)).
  Defined.
End SignHom.

Section PermOf.
  Context `{Univalence}.

  (** Identifications in a sum with proposition-valued second component
      are determined by their first component. *)
  Definition path_sigma_prop_eta {A : Type} {P : A -> Type} (hP : forall a, isProp (P a))
    {u v : {a : A & P a}} (w : u = v) : w = path_sigma_prop hP (ap fst w).
  Proof.
    destruct w. destruct u as [a b]. unfold path_sigma_prop. cbn.
    assert (r : hP a b b = refl) by apply (prop_is_set (hP a)).
    rewrite r. exact refl.
  Defined.

  Definition ap_fst_sigma_prop {A : Type} {P : A -> Type} (hP : forall a, isProp (P a))
    {u v : {a : A & P a}} (e : fst u = fst v) : ap fst (path_sigma_prop hP e) = e
    := ap_fst_pathpair e _.

  (** [perm_of] turns composition into concatenation, so that [sign] is
      multiplicative ([sign_comp]). *)
  Definition path_sigma_prop_trans {A : Type} {P : A -> Type} (hP : forall a, isProp (P a))
    {u v w : {a : A & P a}} (e : fst u = fst v) (e' : fst v = fst w)
    : path_sigma_prop hP (u := u) (v := w) (e' ⋅ e)
      = path_sigma_prop hP e' ⋅ path_sigma_prop hP e.
  Proof.
    refine (_ @ (path_sigma_prop_eta hP _)^).
    apply ap. refine (_ @ (ap_trans fst _ _)^).
    exact (ap011 trans (ap_fst_sigma_prop hP e)^ (ap_fst_sigma_prop hP e')^).
  Defined.

  Definition path_sigma_prop_refl {A : Type} {P : A -> Type} (hP : forall a, isProp (P a))
    (u : {a : A & P a}) : path_sigma_prop hP (u := u) (v := u) refl = refl
    := (path_sigma_prop_eta hP refl)^.

  Context {n : ℕ} (A : utype (BG (SG n))).

  Definition perm_of_comp (σ τ : fst (fst A) ≃ fst (fst A))
    : perm_of A (Eqv_comp σ τ) = perm_of A τ ⋅ perm_of A σ.
  Proof.
    unfold perm_of. rewrite etop_comp.
    rewrite (path_sigma_prop_trans (fun X => isSet_isProp X) (u := fst A) (v := fst A) (w := fst A)).
    exact (path_sigma_prop_trans _ _ _).
  Defined.

  Definition perm_of_id : perm_of A (idEqv _) = refl.
  Proof.
    unfold perm_of. rewrite etop_id.
    rewrite (path_sigma_prop_refl (fun X => isSet_isProp X) (fst A)).
    exact (path_sigma_prop_refl _ _).
  Defined.

  Definition perm_of_ext (σ τ : fst (fst A) ≃ fst (fst A)) (h : forall x, fst σ x = fst τ x)
    : perm_of A σ = perm_of A τ
    := ap (perm_of A) (path_Eqv σ τ (ptw_inv h)).

  Definition sign_trans (q r : A = A) : sign (q ⋅ r) = bmul (sign q) (sign r).
  Proof.
    unfold sign. rewrite ap_trans. exact (loops2_trans _ _ _).
  Defined.

  Definition sign_refl : sign (refl : A = A) = yes
    := loops2_yes _ _ refl.

  Definition sign_comp (σ τ : fst (fst A) ≃ fst (fst A))
    : sign (perm_of A (Eqv_comp σ τ)) = bmul (sign (perm_of A τ)) (sign (perm_of A σ))
    := ap sign (perm_of_comp σ τ) @ sign_trans _ _.
End PermOf.

Section Action.
  Context `{Univalence}.

  (** Pulling back a 2-element subset along an equivalence. *)
  Definition pullEA {X Y : Type} {FX : Finite X} {FY : Finite Y} (e : X ≃ Y)
    (E : EA Y) : EA X.
  Proof.
    refine (fun x => fst E (fst e x); _).
    refine (_ @ snd E).
    exact (fcard_equiv' (equiv_functor_sigma' (Equiv_of_Eqv e) (fun x => equiv_idmap _))).
  Defined.

  (** The action of an equivalence on local orderings,
      [(e·g)(S) :≡ e(g(e⁻¹ S))]. *)
  Definition actLO {X Y : Type} {FX : Finite X} {FY : Finite Y} (e : X ≃ Y)
    (g : LocalOrdering X) : LocalOrdering Y
    := fun E => (fst e (fst (g (pullEA e E))); snd (g (pullEA e E))).

  Definition LO_irr {X : Type} {FX : Finite X} (g : LocalOrdering X)
    (E E' : EA X) (r : fst E = fst E') : fst (g E) = fst (g E')
    := ap (fun E => fst (g E)) (path_sigma_prop (fun _ => ℕ_isSet _ _) r).

  Context {n : ℕ}.

  (** For [B : BΣ_n]: local orderings [LOB B], sign orderings [SOB B],
      and the map [iota B] from sign orderings to [Bsgn(B)] (the
      identity if [B] has a 2-element subset, as in [mu_E]). *)
  Definition hEB (B : utype (BG (SG n))) : isFinSet (EA (fst (fst B)) (H0 := comp_Finite B))
    := Finite_isFinSet (@EA_Finite _ _ (comp_Finite B)).

  Definition PB (B : utype (BG (SG n))) := @PA _ (fst (fst B)) (comp_Finite B).

  Definition LOB (B : utype (BG (SG n))) := @LocalOrdering _ (fst (fst B)) (comp_Finite B).

  Definition SOB (B : utype (BG (SG n))) : Type
    := @SignQ _ _ (FE (hEB B)) (PB B).

  Definition iota (B : utype (BG (SG n))) : SOB B -> el2 (Bsgn n B).
  Proof.
    intro y. unfold Bsgn, mu_E.
    destruct (@decidable_merely_finite _ _) as [ne|ne].
    - exact y.
    - exact fin2_0.
  Defined.

  Definition iota_inj (B : utype (BG (SG n))) (ne : ptrunc (EA (fst (fst B)) (H0 := comp_Finite B)))
    (y y' : SOB B) : iota B y = iota B y' -> y = y'.
  Proof.
    unfold iota, Bsgn, mu_E.
    destruct (@decidable_merely_finite _ _) as [ne'|ne'].
    - exact idmap.
    - destruct (ne' ne).
  Defined.

  (** Transport along [p : A = B] in [Bsgn] acts on sign orderings via
      the equivalence [ptoe p]. *)
  Definition trp_sign {A B : utype (BG (SG n))} (p : A = B) (g : LOB A)
    : trp (fun B => el2 (Bsgn n B)) p (iota A (class_of _ g))
      = iota B (class_of _ (actLO (idtoeqv (ap (fun B => fst (fst B)) p)) g)).
  Proof.
    destruct p. apply (ap (fun g => iota A (class_of _ g))).
    apply path_forall. intro E.
    refine (path_sigma_prop (fun x => isSet_bool _ _) _).
    exact (LO_irr g E (pullEA (idEqv _) E) refl).
  Defined.
End Action.

Section SignNdis.
  Context `{Univalence} {n : ℕ}.

  Definition ptoe_ap {A : Type} (f : A -> Type) {a b : A} (p : a = b) (x : f a)
    : ptoe (ap f p) x = trp f p x.
  Proof. destruct p. exact refl. Defined.

  Definition ap_fst_fst_perm_of (A : utype (BG (SG n))) (σ : fst (fst A) ≃ fst (fst A))
    : ap (fun B => fst (fst B)) (perm_of A σ) = etop σ.
  Proof.
    refine (ap_compose fst fst _ @ _). unfold perm_of.
    rewrite ap_fst_sigma_prop. exact (ap_fst_sigma_prop _ _).
  Defined.

  (** The sign of [σ] is the parity of the number of 2-element subsets
      on which a local ordering [g] and [σ·g] disagree. *)
  Definition sign_ndis (A : utype (BG (SG n))) (σ : fst (fst A) ≃ fst (fst A))
    (ne : ptrunc (EA (fst (fst A)) (H0 := comp_Finite A))) (g : LOB A)
    : sign (perm_of A σ) = even (@ndis _ _ (FE (hEB A)) (PB A) g (actLO σ g)).
  Proof.
    unfold sign. rewrite (loops2_at _ _ (iota A (class_of _ g))).
    assert (e : ptoe (ap (fun B => el2 (Bsgn n B)) (perm_of A σ)) (iota A (class_of _ g))
                = iota A (class_of _ (actLO σ g))).
    { refine (ptoe_ap (fun B => el2 (Bsgn n B)) (perm_of A σ) _ @ trp_sign _ g @ _).
      refine (ap (fun q => iota A (class_of _ (actLO (idtoeqv q) g))) (ap_fst_fst_perm_of A σ) @ _).
      exact (ap (fun e => iota A (class_of _ (actLO e g))) (ptoe_etop σ)). }
    destruct (el2_dec _ (ptoe (ap (fun B => el2 (Bsgn n B)) (perm_of A σ)) (iota A (class_of _ g)))
                (iota A (class_of _ g))) as [r|m].
    - pose (r' := ap (@phi _ _ (FE (hEB A)) (PB A) g) (iota_inj A ne _ _ (e^ @ r))).
      exact ((@phi_class _ _ (FE (hEB A)) (PB A) g _)^ @ r'
                   @ @phi_class _ _ (FE (hEB A)) (PB A) g g
                   @ @parity_refl _ _ (FE (hEB A)) (PB A) g)^.
    - assert (k : even (@ndis _ _ (FE (hEB A)) (PB A) g (actLO σ g)) ≠ true).
      { intro k. apply m. refine (e @ _). apply ap. apply qglue.
        exact (@parity_symm _ _ (FE (hEB A)) (PB A) g _ k). }
      revert k. destruct (even (@ndis _ _ (FE (hEB A)) (PB A) g (actLO σ g))); intro k.
      + destruct (k refl).
      + exact refl.
  Defined.
End SignNdis.

Definition not_true_false {b : Bool} (k : b ≠ true) : b = false
  := match b as b' return (b' ≠ true -> b' = false) with
     | true => fun k => match k refl with end
     | false => fun _ => refl
     end k.

Section Transposition.
  Context `{Univalence} {n : ℕ} (A : utype (BG (SG n))).

  Local Notation X := (fst (fst A)).
  Local Notation dA := (finset_isDecSet (comp_isFinSet A)).

  Context (a b : X) (nab : a ≠ b).

  #[local] Instance FinA : Finite X := comp_Finite A.

  Definition transp_a : transp dA a b a = b.
  Proof.
    unfold transp. destruct (deceq dA a a) as [_|m]; [exact refl | destruct (m refl)].
  Defined.

  Definition transp_b : transp dA a b b = a.
  Proof.
    unfold transp. destruct (deceq dA b a) as [r|_]; [destruct (nab r^)|].
    destruct (deceq dA b b) as [_|m]; [exact refl | destruct (m refl)].
  Defined.

  Definition transp_ne (x : X) (na : x ≠ a) (nb : x ≠ b) : transp dA a b x = x.
  Proof.
    unfold transp. destruct (deceq dA x a) as [r|_]; [destruct (na r)|].
    destruct (deceq dA x b) as [r|_]; [destruct (nb r) | exact refl].
  Defined.

  (** The 2-element subset [{a, b}]. *)
  Definition Sab (x : X) : Bool
    := match deceq dA x a with
       | inl _ => true
       | inr _ => match deceq dA x b with inl _ => true | inr _ => false end
       end.

  Definition Sab_a : Sab a = true.
  Proof. unfold Sab. destruct (deceq dA a a) as [_|m]; [exact refl | destruct (m refl)]. Defined.

  Definition Sab_b : Sab b = true.
  Proof.
    unfold Sab. destruct (deceq dA b a) as [_|_]; [exact refl|].
    destruct (deceq dA b b) as [_|m]; [exact refl | destruct (m refl)].
  Defined.

  Definition Sab_ne (x : X) (na : x ≠ a) (nb : x ≠ b) : Sab x = false.
  Proof.
    unfold Sab. destruct (deceq dA x a) as [r|_]; [destruct (na r)|].
    destruct (deceq dA x b) as [r|_]; [destruct (nb r) | exact refl].
  Defined.

  Definition sub_el_path {S : X -> Bool} (u v : sub_el X S) (r : fst u = fst v) : u = v
    := path_sigma_prop (fun x => isSet_bool _ _) r.

  Definition Sab_eqv : sub_el X Sab ≃ Fin 2.
  Proof.
    refine (mkEqv (fun u => match deceq dA (fst u) a with inl _ => fin2_0 | inr _ => fin2_1 end)
                  (fun i => match i with inl _ => (a; Sab_a) | inr _ => (b; Sab_b) end) _ _).
    - intros [x r]. cbn. destruct (deceq dA x a) as [e|m].
      + apply sub_el_path. exact e^.
      + apply sub_el_path. cbn.
        destruct (deceq dA x b) as [e|m']; [exact e^|].
        destruct (false_ne_true ((Sab_ne x m m')^ @ r)).
    - intros [[[]|[]]|[]]; cbn.
      + destruct (deceq dA a a) as [_|m]; [exact refl | destruct (m refl)].
      + destruct (deceq dA b a) as [e|_]; [destruct (nab e^) | exact refl].
  Defined.

  Local Notation EAX := (EA X (H0 := comp_Finite A)).

  Definition e_ab : EAX.
  Proof.
    refine (Sab; _).
    exact (@fcard_equiv' _ _ (Equiv_of_Eqv Sab_eqv) _ (finite_fin 2)).
  Defined.

  Local Notation τ := (transpEqv dA a b).

  (** A local ordering choosing [a] in subsets containing [a], and [b] in
      subsets containing [b] but not [a]. *)
  Definition gab (h : LOB A) : LOB A
    := fun E => match dec_paths (fst E a) true with
                | inl r => (a; r)
                | inr _ => match dec_paths (fst E b) true with
                           | inl r => (b; r)
                           | inr _ => h E
                           end
                end.

  Definition gab_a (h : LOB A) (E : EAX) (ra : fst E a = true) : fst (gab h E) = a.
  Proof.
    unfold gab. destruct (dec_paths (fst E a) true) as [r0|m]; [exact refl | destruct (m ra)].
  Defined.

  Definition gab_b (h : LOB A) (E : EAX) (na : fst E a ≠ true) (rb : fst E b = true)
    : fst (gab h E) = b.
  Proof.
    unfold gab. destruct (dec_paths (fst E a) true) as [r|_]; [destruct (na r)|].
    destruct (dec_paths (fst E b) true) as [r0|m]; [exact refl | destruct (m rb)].
  Defined.

  Definition gab_h (h : LOB A) (E : EAX) (na : fst E a ≠ true) (nb : fst E b ≠ true)
    : fst (gab h E) = fst (h E).
  Proof.
    unfold gab. destruct (dec_paths (fst E a) true) as [r|_]; [destruct (na r)|].
    destruct (dec_paths (fst E b) true) as [r|_]; [destruct (nb r) | exact refl].
  Defined.

  (** A 2-element subset containing [a] and [b] is [{a, b}]. *)
  Definition both_e_ab (E : EAX) (ra : fst E a = true) (rb : fst E b = true) : E = e_ab.
  Proof.
    refine (path_sigma_prop (fun _ => ℕ_isSet _ _) (path_forall _ _ _)). intro x.
    destruct (deceq dA x a) as [r|na]; [exact (ap (fst E) r @ ra @ Sab_a^ @ (ap Sab r)^)|].
    destruct (deceq dA x b) as [r|nb]; [exact (ap (fst E) r @ rb @ Sab_b^ @ (ap Sab r)^)|].
    refine (_ @ (Sab_ne x na nb)^). apply not_true_false. intro rx.
    refine (nb (ap fst (el2_two (PB A E) (x; rx) (a; ra) (b; rb) _ _))).
    - intro q. exact (na (ap fst q)).
    - intro q. exact (nab (ap fst q)).
  Defined.

  (** [gab h] and [(a b)·gab h] disagree only at [{a, b}]. *)
  Definition dis_gab (h : LOB A) (E : EAX)
    : dis (PB A) (gab h) (actLO τ (gab h)) E = @delta _ _ (FE (hEB A)) e_ab E.
  Proof.
    unfold delta. destruct (dec_paths E e_ab) as [r|r].
    - refine (trp (fun E => dis (PB A) (gab h) (actLO τ (gab h)) E = 1%nat) r^ _).
      unfold dis.
      destruct (el2_dec (PB A e_ab) (gab h e_ab) (actLO τ (gab h) e_ab)) as [q|_]; [|exact refl].
      apply Empty_rec. apply nab.
      refine ((gab_a h e_ab Sab_a)^ @ ap fst q @ _).
      change (transp dA a b (fst (gab h (pullEA τ e_ab))) = b).
      exact (ap (transp dA a b) (gab_a h (pullEA τ e_ab) (ap Sab transp_a @ Sab_b)) @ transp_a).
    - unfold dis.
      destruct (el2_dec (PB A E) (gab h E) (actLO τ (gab h) E)) as [_|q]; [exact refl|].
      apply Empty_rec. apply q. apply sub_el_path.
      change (fst (gab h E) = transp dA a b (fst (gab h (pullEA τ E)))).
      destruct (dec_paths (fst E a) true) as [ra|na], (dec_paths (fst E b) true) as [rb|nb].
      + destruct (r (both_e_ab E ra rb)).
      + refine (gab_a h E ra @ _ @ ap (transp dA a b) (gab_b h (pullEA τ E) _ _)^).
        * exact transp_b^.
        * exact (fun k => nb (ap (fst E) transp_a^ @ k)).
        * exact (ap (fst E) transp_b @ ra).
      + refine (gab_b h E na rb @ _ @ ap (transp dA a b) (gab_a h (pullEA τ E) _)^).
        * exact transp_a^.
        * exact (ap (fst E) transp_a @ rb).
      + refine (gab_h h E na nb @ _ @ ap (transp dA a b) (gab_h h (pullEA τ E) _ _)^).
        * pose (y := fst (h E)).
          refine ((transp_ne y _ _)^ @ ap (transp dA a b) (LO_irr h E (pullEA τ E) _)).
          -- intro e. apply na. exact (ap (fst E) e^ @ snd (h E)).
          -- intro e. apply nb. exact (ap (fst E) e^ @ snd (h E)).
          -- apply path_forall. intro x. change (fst E x = fst E (transp dA a b x)).
             destruct (deceq dA x a) as [e|xa].
             { refine (ap (fst E) e @ _ @ ap (fst E) (ap (transp dA a b) e @ transp_a)^).
               exact (not_true_false na @ (not_true_false nb)^). }
             destruct (deceq dA x b) as [e|xb].
             { refine (ap (fst E) e @ _ @ ap (fst E) (ap (transp dA a b) e @ transp_b)^).
               exact (not_true_false nb @ (not_true_false na)^). }
             exact (ap (fst E) (transp_ne x xa xb))^.
        * exact (fun k => nb (ap (fst E) transp_a^ @ k)).
        * exact (fun k => na (ap (fst E) transp_b^ @ k)).
  Defined.

  Definition ndis_gab (h : LOB A)
    : @ndis _ _ (FE (hEB A)) (PB A) (gab h) (actLO τ (gab h)) = 1%nat
    := ap (@finadd _ (FE (hEB A))) (path_forall _ _ (dis_gab h)) @ finadd_delta e_ab.

  (** Part [it:sign-transposition] of [lem:sign-properties]: the sign of
      a transposition is [-1]. *)
  Definition sign_transp : sign (perm_of A τ) = no.
  Proof.
    refine (ptrunc_rec (isSet_bool _ _) _
              (@finite_choice EAX (FE (hEB A)) (fun e => el2 (PB A e)) (fun _ => tt)
                 (fun e => ptrunc_rec ptrunc_isProp
                             (fun p : Fin 2 = el2 (PB A e) => tr (trp idmap p fin2_0))
                             (el2_Fin2 (PB A e))))).
    intro h.
    exact (sign_ndis A τ (trunc e_ab) (gab h) @ ap even (ndis_gab h)).
  Defined.
End Transposition.

(** [τ(l)] as an equivalence. *)
Fixpoint transpsLE `{Funext} {X : Type} (dA : isDecSet X) (l : list (X × X)) : X ≃ X
  := match l with
     | nil => idEqv X
     | cons p l' => Eqv_comp (transpEqv dA (fst p) (snd p)) (transpsLE dA l')
     end.

Definition transpsLE_fst `{Funext} {X : Type} (dA : isDecSet X) (l : list (X × X)) (x : X)
  : fst (transpsLE dA l) x = transpsL dA l x.
Proof. revert x. induction l as [|p l IH]; intro x; [exact refl | exact (IH _)]. Defined.

Definition pairsL_ne {X : Type} (a : X) (r : list X) (h : notin a r) : all_pairs_ne (pairsL a r).
Proof.
  induction r as [|b r IH]; [exact tt | exact (fst h; IH (snd h))].
Defined.

Definition length_pairsL {X : Type} (a : X) (r : list X) : length (pairsL a r) = length r.
Proof. induction r as [|b r IH]; [exact refl | exact (ap S IH)]. Defined.

Section SignProperties.
  Context `{Univalence} {n : ℕ} (A : utype (BG (SG n))).

  Local Notation X := (fst (fst A)).
  Local Notation dA := (finset_isDecSet (comp_isFinSet A)).

  (** The sign of a composite of [k] transpositions is [(-1)^k]. *)
  Definition sign_transpsL (l : list (X × X)) (h : all_pairs_ne l)
    : sign (perm_of A (transpsLE dA l)) = even (length l).
  Proof.
    induction l as [|p l IH].
    - exact (ap sign (perm_of_id A) @ sign_refl A).
    - refine (sign_comp A _ _ @ _).
      rewrite (IH (snd h)), (sign_transp A (fst p) (snd p) (fst h)).
      cbn. destruct (even (length l)); exact refl.
  Defined.

  Definition sign_of_transpsL (σ : X ≃ X) (l : list (X × X)) (h : all_pairs_ne l)
    (hσ : forall x, fst σ x = transpsL dA l x)
    : sign (perm_of A σ) = even (length l)
    := ap sign (perm_of_ext A σ (transpsLE dA l) (fun x => hσ x @ (transpsLE_fst dA l x)^))
       @ sign_transpsL l h.

  (** Part [it:sign-cycle] of [lem:sign-properties], via exercise
      [xca:perm-prod-transpositions]: the sign of a [k]-cycle is [(-1)^{k-1}]. *)
  Definition sign_kcycle (k : ℕ) (σ : X ≃ X) (c : isKCycle dA k σ)
    : sign (perm_of A σ) = even (pred k).
  Proof.
    refine (ptrunc_rec (isSet_bool _ _) _ c). intros [a1 [r [[len d] hσ]]].
    refine (sign_of_transpsL σ (pairsL a1 r) (pairsL_ne a1 r (fst d)) _ @ _).
    - intro x. exact (hσ x @ cyc_transps dA a1 r d x @ transps_pairsL dA a1 r x).
    - exact (ap even (length_pairsL a1 r @ len)).
  Defined.

  (** Part [it:identity-even] of [lem:sign-properties]: the identity is
      only a composite of an even number of transpositions. *)
  Definition identity_even (l : list (X × X)) (h : all_pairs_ne l)
    (hl : forall x, transpsL dA l x = x)
    : even (length l) = true
    := (sign_of_transpsL (idEqv X) l h (fun x => (hl x)^))^
       @ ap sign (perm_of_id A) @ sign_refl A.
End SignProperties.

(** Lemma [lem:sign-properties]. *)
Definition lem_sign_properties `{Univalence} : lem_sign_properties_stmt.
Proof.
  refine ((_; _); _).
  - intros n A a b ne. exact (sign_transp A a b ne).
  - intros n A k σ c. exact (sign_kcycle A k σ c).
  - intros n A l h hl. exact (identity_even A l h hl).
Defined.

(** Corollary [cor:sign-defined]: two ways of writing [σ] as a composite
    of transpositions have the same parity, which gives the sign. *)
Definition cor_sign_defined `{Univalence} : cor_sign_defined_stmt.
Proof.
  intros n A σ l l' h h' hl hl'.
  pose (s := sign_of_transpsL A σ l h hl).
  exact (s^ @ sign_of_transpsL A σ l' h' hl'; s).
Defined.

(** ** Exercise [xca:sign-by-crossings]

    By [sign_ndis] for [σ⁻¹] and the standard local ordering [gmin]
    (the least element of each 2-element subset of [Fin n]), [sgn(σ)]
    is the parity of the number of subsets [{i, j}] with [i < j] on
    which [gmin] and [σ⁻¹·gmin] disagree, i.e. with [σ(j) < σ(i)]
    ([inv_dis], [dis_inv]).  These subsets correspond to the inversions
    of [σ] ([inv_to_dis], [inversions_ndis]). *)

(** The least element of a decidable subset of [Fin m], for the order
    of [fin_to_nat]. *)
Definition minF (m : ℕ) (S : Fin m -> Bool)
  : {x : Fin m & (S x = true) × (forall y, S y = true -> (fin_to_nat x <= fin_to_nat y)%nat)}
    + (forall y, S y = false).
Proof.
  induction m as [|m IH].
  - right. intros [].
  - destruct (IH (fun x => S (inl x))) as [[x [rx hx]] | k].
    + left. refine (inl x; (rx; _)). intros [y|[]] ry.
      * exact (hx y ry).
      * exact (leq_succ_l (is_bounded_fin_to_nat x)).
    + destruct (dec_paths (S (inr tt)) true) as [r|k'].
      * left. refine (inr tt; (r; _)). intros [y|[]] ry.
        -- destruct (false_ne_true ((k y)^ @ ry)).
        -- exact (leq_refl _).
      * right. intros [y|[]]; [exact (k y) | exact (not_true_false k')].
Defined.

Definition lt_ne {a b : ℕ} (l : (a < b)%nat) : a ≠ b
  := fun e => lt_irrefl b (trp (fun z => (z < b)%nat) e l).

Definition lt_leq_absurd {a b : ℕ} (l : (a < b)%nat) (l' : (b <= a)%nat) : Empty
  := lt_irrefl b (lt_leq_lt_trans l' l).

Definition bmul_yes (u v : Bool) (e : bmul u v = yes) : v = u.
Proof. destruct u, v; first [exact refl | destruct (false_ne_true e) | destruct (false_ne_true e)]. Defined.

Section Crossings.
  Context `{Univalence} (n : ℕ).

  Local Notation A := (sh (SG n)).
  Local Notation EAX := (EA (fst (fst (sh (SG n)))) (H0 := comp_Finite (sh (SG n)))).

  Definition fcode (x : Fin n) : ℕ := fst (equiv_fin_finnat n x).

  Definition cd_inj (x y : Fin n) (e : fcode x = fcode y) : x = y
    := (eissect (equiv_fin_finnat n) x)^
       @ ap (equiv_fin_finnat n)^-1 (path_sigma_hprop (equiv_fin_finnat n x) (equiv_fin_finnat n y) e)
       @ eissect (equiv_fin_finnat n) y.

  (** The standard local ordering: the least element of each 2-element
      subset. *)
  Definition gmin : LOB A.
  Proof.
    intro E. destruct (minF n (fst E)) as [w|k].
    - exact (fst w; fst (snd w)).
    - apply Empty_rec.
      refine (ptrunc_rec (fun (x y : Empty) => match x with end) _ (el2_Fin2 (PB A E))). intro p.
      pose (z := trp idmap p fin2_0 : sub_el _ (fst E)).
      exact (false_ne_true ((k (fst z))^ @ snd z)).
  Defined.

  Definition gmin_min (E : EAX) (y : Fin n) (ry : fst E y = true)
    : (fcode (fst (gmin E)) <= fcode y)%nat.
  Proof.
    unfold gmin. destruct (minF n (fst E)) as [w|k].
    - exact (snd (snd w) y ry).
    - destruct (false_ne_true ((k y)^ @ ry)).
  Defined.

  Definition gmin_eq (E : EAX) (x y : Fin n) (rx : fst E x = true) (ry : fst E y = true)
    (l : (fcode x < fcode y)%nat) : fst (gmin E) = x.
  Proof.
    destruct (dec_paths (fst (gmin E)) x) as [e|ne]; [exact e|].
    apply Empty_rec.
    pose (my := ap fst (el2_two (PB A E) (gmin E) (x; rx) (y; ry)
                          (fun q => ne (ap fst q)) (fun q => lt_ne l (ap fcode (ap fst q))))).
    exact (lt_leq_absurd l (trp (fun z => (fcode z <= fcode x)%nat) my (gmin_min E x rx))).
  Defined.

  Context (σ : Fin n ≃ Fin n).

  Local Notation ρ := (Eqv_inv σ).

  Definition comp_inv_pt {Y : Type} (τ : Y ≃ Y) (x : Y)
    : fst (Eqv_comp τ (Eqv_inv τ)) x = fst (idEqv Y) x
    := eqinv_l (snd τ) x.

  Definition sign_inv : sign (perm_of A σ) = sign (perm_of A ρ).
  Proof.
    apply bmul_yes. refine ((sign_comp A σ ρ)^ @ _).
    refine (ap sign (perm_of_ext A (Eqv_comp σ ρ) (idEqv _) (comp_inv_pt σ)) @ _).
    exact (ap sign (perm_of_id A) @ sign_refl A).
  Defined.

  Local Notation pullρ E := (pullEA (FX := comp_Finite A) (FY := comp_Finite A) ρ E).

  Local Notation dis' := (dis (PB A) gmin (actLO ρ gmin)).

  Definition dis_ne (E : EAX) (k : Fin (dis' E)) : fst (gmin E) ≠ fst (actLO ρ gmin E).
  Proof.
    revert k. unfold dis. destruct (el2_dec (PB A E) (gmin E) (actLO ρ gmin E)) as [q|q].
    - intros [].
    - intros _ e. exact (q (path_sigma_prop (fun x => isSet_bool _ _) e)).
  Defined.

  Definition ne_dis (E : EAX) (ne : fst (gmin E) ≠ fst (actLO ρ gmin E)) : Fin (dis' E).
  Proof.
    unfold dis. destruct (el2_dec (PB A E) (gmin E) (actLO ρ gmin E)) as [q|q].
    - destruct (ne (ap fst q)).
    - exact (inr tt).
  Defined.

  Definition dis_isProp (E : EAX) : isProp (Fin (dis' E)).
  Proof.
    unfold dis. destruct (el2_dec (PB A E) (gmin E) (actLO ρ gmin E)).
    - intros [].
    - exact Fin1_isProp.
  Defined.

  Definition ρσ (x : Fin n) : fst ρ (fst σ x) = x := eqinv_l (snd σ) x.

  Section Pair.
    Context (i j : Fin n) (l : (fcode i < fcode j)%nat).

    Definition nij : i ≠ j := fun e => lt_ne l (ap fcode e).

    Local Notation Eij := (e_ab A i j nij).

    Definition g_ij : fst (gmin Eij) = i := gmin_eq Eij i j (Sab_a A i j) (Sab_b A i j) l.

    Definition pull_σ (x : Fin n) (r : Sab A i j x = true)
      : fst (pullρ Eij) (fst σ x) = true
      := ap (Sab A i j) (ρσ x) @ r.

    Definition σij_ne : fcode (fst σ i) ≠ fcode (fst σ j)
      := fun e => nij ((ρσ i)^ @ ap (fst ρ) (cd_inj _ _ e) @ ρσ j).

    (** [{i, j}] counts iff [(i, j)] is an inversion of [σ]. *)
    Definition inv_dis (l' : (fcode (fst σ j) < fcode (fst σ i))%nat) : Fin (dis' Eij).
    Proof.
      apply ne_dis. refine (trp (fun z => z ≠ _) g_ij^ _).
      change (i ≠ fst ρ (fst (gmin (pullρ Eij)))).
      rewrite (gmin_eq (pullρ Eij) (fst σ j) (fst σ i)
                 (pull_σ j (Sab_b A i j)) (pull_σ i (Sab_a A i j)) l').
      rewrite ρσ. exact nij.
    Defined.

    Definition dis_inv (k : Fin (dis' Eij)) : (fcode (fst σ j) < fcode (fst σ i))%nat.
    Proof.
      destruct (nat_trichotomy (fcode (fst σ j)) (fcode (fst σ i))) as [[l'|e]|l'].
      - exact l'.
      - destruct (σij_ne e^).
      - apply Empty_rec. apply (dis_ne Eij k). refine (g_ij @ _).
        change (i = fst ρ (fst (gmin (pullρ Eij)))).
        rewrite (gmin_eq (pullρ Eij) (fst σ i) (fst σ j)
                   (pull_σ i (Sab_a A i j)) (pull_σ j (Sab_b A i j)) l').
        exact (ρσ i)^.
    Defined.
  End Pair.

  (** The summands of [inversions n σ]. *)
  Definition indf (ij : Fin n * Fin n) : ℕ
    := let i := fst (equiv_fin_finnat n (Overture.fst ij)) in
       let j := fst (equiv_fin_finnat n (Overture.snd ij)) in
       let si := fst (equiv_fin_finnat n (fst σ (Overture.fst ij))) in
       let sj := fst (equiv_fin_finnat n (fst σ (Overture.snd ij))) in
       if dec ((i < j)%nat * (sj < si)%nat) then 1%nat else 0%nat.

  Definition ind_prop (ij : Fin n * Fin n) (k : Fin (indf ij))
    : (fcode (Overture.fst ij) < fcode (Overture.snd ij))%nat
      * (fcode (fst σ (Overture.snd ij)) < fcode (fst σ (Overture.fst ij)))%nat.
  Proof.
    revert k. unfold indf. cbv zeta. destruct (dec _) as [p|_].
    - intros _. exact p.
    - intros [].
  Defined.

  Definition prop_ind (i j : Fin n) (l : (fcode i < fcode j)%nat) (l' : (fcode (fst σ j) < fcode (fst σ i))%nat)
    : Fin (indf (i, j)).
  Proof.
    unfold indf. cbv zeta. destruct (dec _) as [_|np].
    - exact (inr tt).
    - destruct (np (l, l')).
  Defined.

  Definition ind_isProp (ij : Fin n * Fin n) : isProp (Fin (indf ij)).
  Proof.
    unfold indf. cbv zeta. destruct (dec _).
    - exact Fin1_isProp.
    - intros [].
  Defined.

  Definition Sab_true (a b x : Fin n) (r : Sab A a b x = true) : (x = a) + (x = b).
  Proof.
    revert r. unfold Sab.
    destruct (deceq (finset_isDecSet (comp_isFinSet A)) x a) as [e|_]; [intros _; exact (inl e)|].
    destruct (deceq (finset_isDecSet (comp_isFinSet A)) x b) as [e|_];
      [intros _; exact (inr e) | intro r; destruct (false_ne_true r)].
  Defined.

  (** Inversions of [σ] correspond to 2-element subsets on which [gmin]
      and [σ⁻¹·gmin] disagree. *)
  Definition inv_to_dis (w : {ij : Fin n * Fin n & Fin (indf ij)}) : {E : EAX & Fin (dis' E)}
    := (e_ab A (Overture.fst (fst w)) (Overture.snd (fst w))
          (nij _ _ (Overture.fst (ind_prop _ (snd w))));
        inv_dis _ _ (Overture.fst (ind_prop _ (snd w))) (Overture.snd (ind_prop _ (snd w)))).

  Definition inv_to_dis_inj (u u' : {ij : Fin n * Fin n & Fin (indf ij)}) (e : inv_to_dis u = inv_to_dis u') : u = u'.
  Proof.
    destruct u as [[i j] k], u' as [[i' j'] k'].
    pose (l := Overture.fst (ind_prop _ k)). pose (l' := Overture.fst (ind_prop _ k')).
    pose (e1 := ap fst e : e_ab A i j (nij i j l) = e_ab A i' j' (nij i' j' l')).
    pose (ii := (g_ij i j l)^ @ ap (fun E => fst (gmin E)) e1 @ g_ij i' j' l').
    pose (jS := (ap (fun E : EAX => fst E j) e1)^ @ Sab_b A i j : Sab A i' j' j = true).
    refine (path_sigma_prop ind_isProp (u := ((i, j); k)) (v := ((i', j'); k')) (path_prod' ii _)).
    destruct (Sab_true i' j' j jS) as [e2|e2].
    - destruct (nij i j l (ii @ e2^)).
    - exact e2.
  Defined.

  Definition e_ab_irr (a b : Fin n) (n1 n2 : a ≠ b) : e_ab A a b n1 = e_ab A a b n2.
  Proof. unfold e_ab. apply (ap (fun c => (Sab A a b; c))). apply ℕ_isSet. Defined.

  Definition inv_to_dis_surj : isSurj inv_to_dis.
  Proof.
    intros [E k].
    refine (ptrunc_rec ptrunc_isProp _ (el2_other (PB A E) (gmin E))). intros [y ny].
    pose (x0 := fst (gmin E)). pose (y0 := fst y).
    assert (ne0 : x0 ≠ y0).
    { intro e. apply ny. exact (path_sigma_prop (fun x => isSet_bool _ _) e^). }
    assert (l : (fcode x0 < fcode y0)%nat).
    { destruct (nat_trichotomy (fcode x0) (fcode y0)) as [[l|e]|l].
      - exact l.
      - destruct (ne0 (cd_inj _ _ e)).
      - destruct (lt_leq_absurd l (gmin_min E y0 (snd y))). }
    pose (rE := both_e_ab A x0 y0 (nij x0 y0 l) E (snd (gmin E)) (snd y)).
    pose (l' := dis_inv x0 y0 l (trp (fun E => Fin (dis' E)) rE k)).
    apply trunc. refine (((x0, y0); prop_ind x0 y0 l l'); _).
    refine (path_sigma_prop dis_isProp _).
    exact (rE @ e_ab_irr _ _ _ _).
  Defined.

  Definition inversions_ndis
    : inversions n σ = @ndis _ _ (FE (hEB A)) (PB A) gmin (actLO ρ gmin).
  Proof.
    unfold inversions, ndis, finadd.
    exact (fcard_equiv' (Equiv_of_Eqv (inv_to_dis; inj_surj_isEquiv
                                              (cancel_isInj (IsHSet_isSet _) inv_to_dis_inj) inv_to_dis_surj))).
  Defined.
End Crossings.

(** For [n ≤ 1] both sides are trivial. *)
Definition sign_crossings_small `{Univalence} (n : ℕ) (σ : Fin n ≃ Fin n)
  (h : forall x y : Fin n, x = y)
  : sign (perm_of (sh (SG n)) σ) = even (inversions n σ).
Proof.
  refine (ap sign (perm_of_ext (sh (SG n)) σ (idEqv _) (fun x => h _ _))
          @ ap sign (perm_of_id (sh (SG n))) @ sign_refl (sh (SG n)) @ _).
  assert (r : indf n σ = fun _ => 0%nat).
  { apply path_forall. intro ij. unfold indf. cbv zeta. destruct (dec _) as [p|_].
    - destruct (lt_ne (Overture.fst p) (ap (fcode n) (h _ _))).
    - exact refl. }
  change (yes = even (finadd (indf n σ))).
  rewrite r, (finadd_const (Fin n * Fin n) 0), nat_mul_zero_r. exact refl.
Defined.

(** Exercise [xca:sign-by-crossings]. *)
Definition xca_sign_by_crossings `{Univalence} : xca_sign_by_crossings_stmt.
Proof.
  intros n σ. destruct n as [|[|m]].
  - exact (sign_crossings_small 0 σ (fun x => match x with end)).
  - refine (sign_crossings_small 1 σ _). intros [[]|[]] [[]|[]]. exact refl.
  - pose (ne := trunc (e_ab (sh (SG m.+2)) (inr tt) (inl (inr tt)) (fun q => inl_ne_inr _ _ q^))).
    refine (sign_inv _ σ @ sign_ndis (sh (SG m.+2)) (Eqv_inv σ) ne (gmin _) @ _).
    exact (ap even (inversions_ndis _ σ)^).
Defined.


(** ** The exercise on the number of even permutations (after the remark
    following [xca:sign-by-crossings])

    Composing with a transposition exchanges the even and the odd
    permutations ([Ev_Od]), and there are [n!] permutations ([fcard_aut]);
    the symmetries of [Fin n] in [BΣ_n] are the permutations
    ([perm_of_isEquiv]). *)

Section EvenCount.
  Context `{Univalence}.

  (** [perm_of] is an equivalence. *)
  Definition perm_of_isEquiv {n : ℕ} (A : utype (BG (SG n))) : isEquiv (perm_of A).
  Proof.
    refine (iso_to_isEquiv _ (fun w => idtoeqv (ap (fun B => fst (fst B)) w)) _ _).
    - intro σ. exact (ap idtoeqv (ap_fst_fst_perm_of A σ) @ ptoe_etop σ).
    - intro w.
      refine (ap (fun q => path_sigma_prop (fun _ => ptrunc_isProp) (u := A) (v := A)
                            (path_sigma_prop (fun X => isSet_isProp X) (u := fst A) (v := fst A) q))
                 (etop_ptoe (ap (fun B => fst (fst B)) w) @ ap_compose fst fst w) @ _).
      refine (ap (path_sigma_prop (fun _ => ptrunc_isProp) (u := A) (v := A))
                 (path_sigma_prop_eta (fun X => isSet_isProp X) (ap fst w))^ @ _).
      exact (path_sigma_prop_eta (fun _ => ptrunc_isProp) w)^.
  Defined.

  (** A type splits along a map to [Bool]. *)
  Definition split_Bool_eqv {X : Type} (f : X -> Bool)
    : X <~> ({x : X & f x = true} + {x : X & f x = false}).
  Proof.
    refine (equiv_adjointify
              (fun x => match dec_paths (f x) true with
                        | inl r => inl (x; r)
                        | inr k => inr (x; not_true_false k) end)
              (fun s => match s with inl w => fst w | inr w => fst w end) _ _).
    - intros [[x r]|[x r]]; cbn; destruct (dec_paths (f x) true) as [r'|k].
      + exact (ap inl (path_sigma_hprop (x; r') (x; r) refl)).
      + destruct (k r).
      + destruct (false_ne_true (r^ @ r')).
      + exact (ap inr (path_sigma_hprop (x; not_true_false k) (x; r) refl)).
    - intro x. cbn. destruct (dec_paths (f x) true); exact refl.
  Defined.

  Definition Equiv_comp_pt {X : Type} (σ : X <~> X) (τ : X ≃ X) (x : X)
    : fst (Eqv_of_Equiv (σ oE Equiv_of_Eqv τ)) x = fst (Eqv_comp τ (Eqv_of_Equiv σ)) x
    := refl.

  Context (n : ℕ).

  Local Notation A := (sh (SG n)).
  Local Notation dA := (finset_isDecSet (comp_isFinSet A)).

  Definition sgnE (σ : Fin n <~> Fin n) : Bool := sign (perm_of A (Eqv_of_Equiv σ)).

  Definition EvP : Type := {σ : Fin n <~> Fin n & sgnE σ = true}.
  Definition OdP : Type := {σ : Fin n <~> Fin n & sgnE σ = false}.

  (** Composing with a transposition exchanges even and odd permutations. *)
  Context (a b : Fin n) (nab : a ≠ b).

  Definition tauE : Fin n <~> Fin n := Equiv_of_Eqv (transpEqv dA a b).

  Definition sgnE_tau (σ : Fin n <~> Fin n) : sgnE (σ oE tauE) = negb (sgnE σ).
  Proof.
    unfold sgnE.
    refine (ap sign (perm_of_ext A _ (Eqv_comp (transpEqv dA a b) (Eqv_of_Equiv σ))
                       (Equiv_comp_pt σ (transpEqv dA a b))) @ _).
    refine (sign_comp A _ _ @ _).
    rewrite (sign_transp A a b nab).
    destruct (sign (perm_of A (Eqv_of_Equiv σ))); exact refl.
  Defined.

  Definition tau_invol (σ : Fin n <~> Fin n) : (σ oE tauE) oE tauE = σ.
  Proof.
    apply path_equiv. apply path_forall. intro x.
    exact (ap σ (transp_invol dA a b x)).
  Defined.

  Definition Ev_Od : EvP <~> OdP.
  Proof.
    refine (equiv_adjointify
              (fun w : EvP => (fst w oE tauE; sgnE_tau (fst w) @ ap negb (snd w)) : OdP)
              (fun w : OdP => (fst w oE tauE; sgnE_tau (fst w) @ ap negb (snd w)) : EvP) _ _).
    - intro w. apply path_sigma_hprop. exact (tau_invol (fst w)).
    - intro w. apply path_sigma_hprop. exact (tau_invol (fst w)).
  Defined.

  Definition fcard_Ev : (fcard EvP + fcard EvP)%nat = fact n.
  Proof.
    refine (ap (nat_add _) (fcard_equiv' Ev_Od) @ _).
    refine ((fcard_sum EvP OdP)^ @ _).
    refine ((fcard_equiv' (split_Bool_eqv sgnE))^ @ _).
    exact (fcard_aut (Fin n)).
  Defined.
End EvenCount.

Definition mul2 (k : ℕ) : mul 2 k = (k + k)%nat.
Proof. cbn. rewrite nat_add_zero_r. exact refl. Defined.

Definition loops_EvP `{Univalence} (n : ℕ)
  : EvP n <~> {σ : sh (SG n) = sh (SG n) & sign σ = yes}
  := equiv_functor_sigma'
       (equiv_compose' (Equiv_of_Eqv (perm_of (sh (SG n)); perm_of_isEquiv (sh (SG n))))
                       (Equiv_of_Eqv (Equiv_Eqv_eqv (Fin n) (Fin n))))
       (fun σ => equiv_idmap).

(** The exercise: for [n ≥ 2] there are [n!/2] even permutations. *)
Definition even_perms_count `{Univalence} : even_perms_count_stmt.
Proof.
  intros n l.
  destruct n as [|[|m]].
  - destruct (not_lt_zero_r _ l).
  - destruct (lt_irrefl _ l).
  - pose (e := loops_EvP m.+2).
    refine (Finite_isFinSet (finite_equiv' _ e _); _).
    refine (ap (mul 2) (cardF_fcard _ @ (fcard_equiv' e)^) @ mul2 _ @ _).
    exact (fcard_Ev m.+2 (inr tt) (inl (inr tt)) (fun q => inl_ne_inr _ _ q^)).
Defined.
