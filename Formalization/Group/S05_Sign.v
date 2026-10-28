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

    Left out (statements only, no proofs yet)
    - The pointing of [Bsgn] by the standard sign ordering of [Fin n]
      ([Bsgn_pt_stmt]) and that [BAG] is a connected groupoid
      ([BAG_isConn_stmt]).
    - [lem:sign-properties] ([lem_sign_properties_stmt]) and
      [cor:sign-defined] ([cor_sign_defined_stmt]), and the exercises
      that need them: [xca:isos_A3_C3] ([xca_isos_A3_C3_stmt]),
      [xca:sign-by-crossings] ([xca_sign_by_crossings_stmt], with
      [inversions]) and the count [n!/2] of even permutations
      ([even_perms_count_stmt]). *)

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
    := forall p c g, {i : Iso (AG 3 p c g) (CG 2) & {j : Iso (AG 3 p c g) (CG 2) & i ≠ j}}.

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
      [it:sign-cycle] and [it:identity-even], in this order. *)
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

  (** Corollary [cor:sign-defined]. *)
  Definition cor_sign_defined_stmt : Type
    := forall n (A : utype (BG (SG n))) (σ : fst (fst A) ≃ fst (fst A))
              (l l' : list (fst (fst A) × fst (fst A))),
         all_pairs_ne l -> all_pairs_ne l' ->
         (forall x, fst σ x = transpsL (finset_isDecSet (comp_isFinSet A)) l x) ->
         (forall x, fst σ x = transpsL (finset_isDecSet (comp_isFinSet A)) l' x) ->
         (even (length l) = even (length l')) × (sign (perm_of A σ) = even (length l)).

  (** Exercise [xca:sign-by-crossings]: the sign is [(-1)^{inv(σ)}],
      counting inversions through [Fin n ≃ {k | k < n}]. *)
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

  (** The number of even permutations is [n!/2] for [n ≥ 2]. *)
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
