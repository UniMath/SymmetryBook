(** * Section 2.15 Propositions, sets and groupoids

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Own definitions, since the library's [IsHProp], [IsHSet], [IsTrunc]
      are defined via contractibility: [isProp], [isSet], [isGrpd] and
      [is_ntype n] (for [n ≥ 0]); [¬ := not] and [≠].
    - Every proposition is a set, following the book's argument; [Bool]
      is a set, via Simon Huber's proof.
    - All six parts of [lem:prop-utils], plus the fact that [True ⨿ True]
      is not a proposition.
    - [lem:level-n-utils], which the book states without proof, by
      comparing [is_ntype] with Coq-HoTT's [IsTrunc].
    - [isContr], [isProp], [isSet], [isGrpd], [is_ntype n] and [isEquiv f]
      are propositions; the [isContr] case follows the book's proof.  A
      type is a proposition iff all its identity types are contractible.
    - The diagrams remark has no formal content.
    - The instance [UnivalenceUF] derived from Coq-HoTT's [Univalence].
    - Bridges: equivalences between propositions ([Eqv_of_props]),
      [isContr X ≃ Contr X], [isProp P ≃ IsHProp P], [isSet X ≃ IsHSet X],
      [isGrpd X ≃ IsTrunc 1 X], [is_ntype n X ≃ IsTrunc n X],
      [isEquiv f ≃ IsEquiv f] and [(X <~> Y) ≃ (X ≃ Y)]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S14_HeavyTransport.

Local Open Scope uf_scope.

(** ** 2.15 Propositions, sets and groupoids *)

(** Definition [def:isSet].
    (The book introduces these notions informally at the start of the section and formalizes them later in [def:isSet]; placed first since everything in the section uses them.) *)
Definition isProp (P : Type) : Type := forall a b : P, a = b.
Definition isSet (S : Type) : Type := forall x y : S, isProp (x = y).
Definition isGrpd (G : Type) : Type := forall g h : G, isSet (g = h).

(** [n]-types for [n ≥ 0]: [X] is an [(n+1)]-type if all its identity
    types are [n]-types. *)
Fixpoint is_ntype (n : ℕ) (X : Type) : Type
  := match n with
     | O => isSet X
     | S n => forall x y : X, is_ntype n (x = y)
     end.

Definition is_ntype_1 (X : Type) : is_ntype 1 X = isGrpd X := refl.

(** Definition [def:neg-eq-ne]: negation [¬P :≡ (P -> ∅)], the library's
    [not], and inequality [a ≠ b :≡ ¬(a = b)]. *)
Definition neg (P : Type) : Type := not P.
Notation "¬ P" := (neg P) : uf_scope.

Definition ne {A : Type} (a b : A) : Type := ¬ (a = b).
Notation "a ≠ b" := (ne a b) (at level 70) : uf_scope.

Definition yes_ne_no' : yes ≠ no := yes_ne_no.

(** Lemma [lem:prop-is-set]. *)
Definition prop_is_set {X : Type} (f : isProp X) : isSet X.
Proof.
  (* [q · f(a,b) = f(a,c)] for [q : b = c], by induction on [q]. *)
  assert (K : forall a b c (q : b = c), q ⋅ f a b = f a c).
  { intros a b c q. destruct q. exact refl. }
  (* Hence [q = f(b,c) · f(b,b)⁻¹], which doesn't depend on [q]. *)
  assert (L : forall b c (q : b = c), q = f b c ⋅ (f b b)⁻¹).
  { intros b c q. destruct q. exact (trans_Vp (f b b))^. }
  intros x y p q. exact (L x y p @ (L x y q)^).
Defined.

(** Lemma [lem:isset-bool], following Simon Huber's proof. *)
Definition C_bool (b b' : Bool) : b = b' -> Type
  := match b, b' with
     | yes, yes => fun p => p = refl
     | no, no => fun p => p = refl
     | _, _ => fun _ => True
     end.

Definition C_bool_all (b b' : Bool) (p : b = b') : C_bool b b' p.
Proof. destruct p, b; exact refl. Defined.

Definition bool_loops_trivial (b : Bool) (p : b = b) : p = refl.
Proof. destruct b; exact (C_bool_all _ _ p). Defined.

Definition isSet_bool : isSet Bool.
Proof. intros b b' p q. destruct q. exact (bool_loops_trivial b p). Defined.

(** Lemma [lem:prop-utils]. *)
Section PropUtils.

  (** Part [prop-utils-false-true]. *)
  Definition False_isProp : isProp False := fun a => match a with end.

  Definition True_isProp : isProp True
    := fun a b => match a, b with triv, triv => refl end.

  (** Part [prop-utils-pi]. *)
  Definition Pi_isProp `{Funext} {A : Type} {R : A -> Type}
    (h : forall a, isProp (R a)) : isProp (forall a, R a)
    := fun p q => ptw_inv (fun a => h a (p a) (q a)).

  (** Part [prop-utils-codom]. *)
  Definition fun_isProp `{Funext} {A P : Type} (h : isProp P)
    : isProp (A -> P)
    := Pi_isProp (fun _ => h).

  (** Part [prop-utils-sum]. *)
  Definition Sigma_isProp {A : Type} {R : A -> Type} (hA : isProp A)
    (hR : forall a, isProp (R a)) : isProp {a : A & R a}.
  Proof.
    intros [a1 r1] [a2 r2].
    pose (u := hA a1 a2).
    exact (pathpair u (trp (fun T : Type => T) (po u r1 r2)^ (hR _ _ _))).
  Defined.

  (** Part [prop-utils-times]. *)
  Definition prod_isProp {P Q : Type} (hP : isProp P) (hQ : isProp Q)
    : isProp (P × Q)
    := Sigma_isProp hP (fun _ => hQ).

  Definition neg_isProp `{Funext} (A : Type) : isProp (¬ A)
    := fun_isProp False_isProp.

  (** Part [prop-utils-lem]. *)
  Definition lem_isProp `{Funext} {P : Type} (hP : isProp P)
    : isProp (P ⨿ ¬ P).
  Proof.
    intros [p|np] [q|nq].
    - exact (ap inl (hP p q)).
    - destruct (nq p).
    - destruct (np q).
    - exact (ap inr (neg_isProp P np nq)).
  Defined.

End PropUtils.

(** [𝟙 ⨿ 𝟙] is not a proposition. *)
Definition True_plus_True_not_prop : ¬ isProp (True ⨿ True)
  := fun h => inl_ne_inr triv triv (h (inl triv) (inr triv)).

(** Lemma [lem:level-n-utils], which the book states without proof.  We
    prove it by comparing [is_ntype] with Coq-HoTT's [IsTrunc]. *)
Fixpoint tr_nat (n : ℕ) : trunc_index
  := match n with O => minus_two.+2 | S n => (tr_nat n).+1 end.

Definition isProp_IsHProp {P : Type} : isProp P -> IsHProp P
  := hprop_allpath P.

Definition IsHProp_isProp {P : Type} `{IsHProp P} : isProp P
  := path_ishprop.

Definition ntype_IsTrunc (n : ℕ) {X : Type}
  : is_ntype n X -> IsTrunc (tr_nat n) X.
Proof.
  revert X. induction n as [|n IH]; intros X h; apply istrunc_S; intros x y.
  - exact (isProp_IsHProp (h x y)).
  - exact (IH _ (h x y)).
Defined.

Definition IsTrunc_ntype (n : ℕ) {X : Type}
  : IsTrunc (tr_nat n) X -> is_ntype n X.
Proof.
  revert X. induction n as [|n IH]; intros X h x y.
  - exact IsHProp_isProp.
  - exact (IH _ _).
Defined.

Section LevelNUtils.

  Context `{Funext} (n : ℕ).

  (** Part [level-n-utils-pi]. *)
  Definition Pi_ntype {A : Type} {Z : A -> Type}
    (h : forall a, is_ntype n (Z a)) : is_ntype n (forall a, Z a).
  Proof.
    pose proof (fun a => ntype_IsTrunc n (h a)).
    apply IsTrunc_ntype. exact _.
  Defined.

  (** Part [level-n-utils-codom]. *)
  Definition fun_ntype {A X : Type} (h : is_ntype n X) : is_ntype n (A -> X)
    := Pi_ntype (fun _ => h).

  (** Part [level-n-utils-sum]. *)
  Definition Sigma_ntype {A : Type} {Z : A -> Type} (hA : is_ntype n A)
    (h : forall a, is_ntype n (Z a)) : is_ntype n {a : A & Z a}.
  Proof.
    pose proof (ntype_IsTrunc n hA).
    pose proof (fun a => ntype_IsTrunc n (h a)).
    apply IsTrunc_ntype. exact _.
  Defined.

  (** Part [level-n-utils-times]. *)
  Definition prod_ntype {X Y : Type} (hX : is_ntype n X) (hY : is_ntype n Y)
    : is_ntype n (X × Y)
    := Sigma_ntype hX (fun _ => hY).

End LevelNUtils.

(** Lemma [lem:isX-is-prop]. *)
Section IsXIsProp.

  Context `{Funext}.

  (** [isContr(A)] is a proposition, following the proof in the book. *)
  Definition isContr_isProp (A : Type) : isProp (isContr A).
  Proof.
    intros [a f] [b g].
    assert (hA : isProp A) by exact (fun x y => f y ⋅ (f x)⁻¹).
    pose (e := f b).
    exact (pathpair e (trp (fun T : Type => T) (po e f g)^
                         (Pi_isProp (fun y => prop_is_set hA b y) _ _))).
  Defined.

  (** Exercise [xca:isX-is-prop]. *)
  Definition isProp_isProp (A : Type) : isProp (isProp A).
  Proof.
    intros f g.
    apply ptw_inv. intro a. apply ptw_inv. intro b.
    exact (prop_is_set f a b _ _).
  Defined.

  Definition isSet_isProp (A : Type) : isProp (isSet A)
    := Pi_isProp (fun x => Pi_isProp (fun y => isProp_isProp (x = y))).

  Definition isGrpd_isProp (A : Type) : isProp (isGrpd A)
    := Pi_isProp (fun x => Pi_isProp (fun y => isSet_isProp (x = y))).

  Definition ntype_isProp (n : ℕ) : forall A : Type, isProp (is_ntype n A).
  Proof.
    induction n as [|n IH]; intro A.
    - exact (isSet_isProp A).
    - exact (Pi_isProp (fun x => Pi_isProp (fun y => IH (x = y)))).
  Defined.

  Definition isEquiv_isProp {X Y : Type} (f : X -> Y) : isProp (isEquiv f)
    := Pi_isProp (fun y => isContr_isProp (fiber f y)).

End IsXIsProp.

(** Exercise [xca:prop-contractible=]. *)
Definition isProp_iff_paths_contr (P : Type)
  : (isProp P -> forall p q : P, isContr (p = q))
    * ((forall p q : P, isContr (p = q)) -> isProp P).
Proof.
  split.
  - intros h p q. exact (h p q; fun r => prop_is_set h p q (h p q) r).
  - intros c p q. exact (fst (c p q)).
Defined.

(** Remark [rem:diagram] introduces diagrams as notation for identity
    types (e.g. [g ∘ p = q ∘ f]); it has no further formal content. *)

(** ** Univalence from Coq-HoTT

    The book's univalence axiom follows from Coq-HoTT's [Univalence]:
    [idtoeqv] is homotopic to the composite of the library's
    [equiv_path] with the equivalence [(X <~> Y) ≃ (X ≃ Y)]. *)

Definition isEquiv_homotopic {X Y : Type} (f g : X -> Y)
  (h : forall x, f x = g x) (t : isEquiv f) : isEquiv g
  := isEquiv_of_IsEquiv g (H := isequiv_homotopic f (H := IsEquiv_of_isEquiv t) h).

Definition Eqv_of_Equiv_isEquiv `{Funext} (X Y : Type)
  : isEquiv (@Eqv_of_Equiv X Y).
Proof.
  refine (iso_to_isEquiv _ (fun e => Build_Equiv _ _ (fst e) (IsEquiv_of_isEquiv (snd e)))
            _ _).
  - intro e. apply path_equiv. exact refl.
  - intro e. apply path_Eqv. exact refl.
Defined.

Instance UnivalenceUF_from_HoTT `{Univalence} : UnivalenceUF.
Proof.
  intros X Y.
  refine (isEquiv_homotopic (comp Eqv_of_Equiv (equiv_path X Y)) _ _
            (comp_isEquiv (isEquiv_of_IsEquiv (equiv_path X Y))
                       (Eqv_of_Equiv_isEquiv X Y))).
  intro p. destruct p. apply path_Eqv. exact refl.
Defined.

(** *** Bridges to Coq-HoTT *)

Definition Eqv_of_props {P Q : Type} (hP : isProp P) (hQ : isProp Q)
  (f : P -> Q) (g : Q -> P) : P ≃ Q
  := mkEqv f g (fun p => hP _ _) (fun q => hQ _ _).

Definition isContr_Contr_eqv `{Funext} (X : Type) : isContr X ≃ Contr X
  := Eqv_of_props (isContr_isProp X) (IsHProp_isProp (P := Contr X))
       Contr_of_isContr (fun C => @isContr_of_Contr X C).

Definition isProp_eqv `{Funext} (P : Type) : isProp P ≃ IsHProp P
  := Eqv_of_props (isProp_isProp P) (IsHProp_isProp (P := IsHProp P))
       isProp_IsHProp (fun h => @IsHProp_isProp P h).

Definition is_ntype_eqv `{Funext} (n : ℕ) (X : Type)
  : is_ntype n X ≃ IsTrunc (tr_nat n) X
  := Eqv_of_props (ntype_isProp n X)
       (IsHProp_isProp (P := IsTrunc (tr_nat n) X))
       (ntype_IsTrunc n) (IsTrunc_ntype n).

Definition isSet_IsHSet {X : Type} : isSet X -> IsHSet X := ntype_IsTrunc 0.

Definition IsHSet_isSet {X : Type} : IsHSet X -> isSet X := IsTrunc_ntype 0.

Definition isSet_eqv `{Funext} (X : Type) : isSet X ≃ IsHSet X
  := is_ntype_eqv 0 X.

Definition isGrpd_IsTrunc {X : Type} : isGrpd X -> IsTrunc 1 X
  := ntype_IsTrunc 1.

Definition IsTrunc_isGrpd {X : Type} : IsTrunc 1 X -> isGrpd X
  := IsTrunc_ntype 1.

Definition isGrpd_eqv `{Funext} (X : Type) : isGrpd X ≃ IsTrunc 1 X
  := is_ntype_eqv 1 X.

Definition isEquiv_IsEquiv_eqv `{Funext} {X Y : Type} (f : X -> Y)
  : isEquiv f ≃ IsEquiv f
  := Eqv_of_props (isEquiv_isProp f) (IsHProp_isProp (P := IsEquiv f))
       IsEquiv_of_isEquiv (fun e => @isEquiv_of_IsEquiv X Y f e).

Definition Equiv_Eqv_eqv `{Funext} (X Y : Type) : (X <~> Y) ≃ (X ≃ Y)
  := (Eqv_of_Equiv; Eqv_of_Equiv_isEquiv X Y).
