(** * Section 2.25 Type families and maps

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - [lem:fst-fiber(a)=B(a)] and [lem:sum-of-fibers] (with direct
      inverses instead of [cor:contract-away]); injections into [n]-types
      have [n]-types as domains.
    - [lem:typefamiliesandfibrations]: [preim : ∑_{B:U} (B → A) ≃ (A → U)],
      by univalence, following the book's proof.
    - Exercises [xca:sum-base-path] and [xca:sum-families].
    - Construction [lem:Prop-Set-pointed-families], parts 1 - 4.  Instead
      of transporting along the path induced by [preim], we reindex the
      sum along the equivalence [preim] itself, so that
      [T(preim(B,f)) ≡ ∏_a S(f⁻¹(a))] holds by definition.
    - Corollary [cor:Inj(T)-is-set].
    - The exercise on essentially [U]-small types:
      [(∑_{A:U'} ∑_{X:U} (A ≃ X)) ≃ U], and families of [U]-small types
      versus maps in [U'] with essentially [U]-small fibers. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S24_FiniteSets.

Local Open Scope uf_scope.

(** ** 2.25 Type families and maps *)

(** Lemma [lem:fst-fiber(a)=B(a)]: [e_a(b) :≡ ((a,b), refl_a)].  We give
    the inverse directly instead of using [cor:contract-away]. *)
Definition fst_fiber_eqv {A : Type} (B : A -> Type) (a : A)
  : B a ≃ fiber (@fst A B) a.
Proof.
  refine (mkEqv (fun b => ((a; b); refl))
                (fun w => trp B (snd w)⁻¹ (snd (fst w))) (fun b => refl) _).
  intros [[x b] p]. cbn in p |- *. destruct p. exact refl.
Defined.

(** Lemma [lem:sum-of-fibers]: [e(b,a,p) :≡ a]. *)
Definition sum_of_fibers {A B : Type} (f : A -> B)
  : {b : B & fiber f b} ≃ A.
Proof.
  refine (mkEqv (fun w => fst (snd w)) (fun a => (f a; (a; refl))) _ (fun a => refl)).
  intros [b [a p]]. cbn in p |- *.
  revert b p. refine (paths_ind_r _ _ _). exact refl.
Defined.

(** If [f] is an injection, [A] is an [n]-type when [B] is. *)
Definition inj_ntype (n : ℕ) {A B : Type} {f : A -> B} (j : isInj f)
  (h : is_ntype n B) : is_ntype n A
  := is_ntype_Eqv n (sum_of_fibers f) (subtype_ntype n j h).

(** Lemma [lem:typefamiliesandfibrations]. *)
Section TypeFamiliesAndFibrations.

  Universe u.
  Context `{Univalence} (A : Type@{u}).

  Definition preim (w : {B : Type@{u} & B -> A}) : A -> Type@{u}
    := fun a => fiber (snd w) a.

  Definition preim_inv (C : A -> Type@{u}) : {B : Type@{u} & B -> A}
    := ({a : A & C a}; fst).

  Definition preim_isEquiv : isEquiv preim.
  Proof.
    refine (iso_to_isEquiv preim preim_inv _ _).
    - intros [B f].
      pose (E := sum_of_fibers f).
      refine (pathpair (Y := fun X : Type@{u} => X -> A) (etop E) _).
      refine (trp_fun_dom (etop E) fst @ _).
      apply ptw_inv. intro b. cbn.
      refine (ap fst (trp_inv_eqinv (etop E) E (ap fst (ptoe_etop E)) b) @ _).
      exact (snd (snd (eqinv (snd E) b)) @ ap f (eqinv_r (snd E) b)).
    - intro C. apply ptw_inv. intro a.
      exact (etop (Eqv_inv (fst_fiber_eqv C a))).
  Defined.

  Definition preim_eqv : {B : Type@{u} & B -> A} ≃ (A -> Type@{u})
    := (preim; preim_isEquiv).

End TypeFamiliesAndFibrations.

(** Exercise [xca:sum-base-path]. *)
Definition sum_base_path {X Y : Type} (p : Y = X) (T : X -> Type)
  : {x : X & T x} ≃ {y : Y & T (ptoe p y)}.
Proof. destruct p. exact (idEqv _). Defined.

(** Exercise [xca:sum-families]: an instance of [xca:AC-in-TT]. *)
Definition sum_families (S : Type -> Type) (X : Type)
  : (X -> {Y : Type & S Y}) ≃ {F : X -> Type & forall x, S (F x)}
  := type_theoretic_AC X Type (fun _ Y => S Y).

(** Construction [lem:Prop-Set-pointed-families].  Instead of transporting
    along the path induced by [preim] ([xca:sum-base-path]), we reindex
    the sum along the equivalence [preim] directly, so that
    [T(preim(B,f)) ≡ ∏_a S(f⁻¹(a))] holds by definition. *)
Section FamiliesStructure.

  Universe u.
  Context `{Univalence} (A : Type@{u}).

  (** Part [cnstr:families+structure]. *)
  Definition families_structure (S : Type@{u} -> Type@{u})
    : (A -> {B : Type@{u} & S B})
      ≃ {B : Type@{u} & {f : B -> A & forall a, S (fiber f a)}}.
  Proof.
    refine (Eqv_comp (sum_families S A) _).
    refine (Eqv_comp (Eqv_inv (Eqv_of_Equiv
              (equiv_functor_sigma_pb (Q := fun F : A -> Type@{u} => forall a, S (F a))
                 (Equiv_of_Eqv (preim_eqv A))))) _).
    exact (Eqv_inv (sigma_assoc Type@{u} (fun B => B -> A)
                      (fun B f => forall a, S (fiber f a)))).
  Defined.

  (** Part [lem:Prop-families]. *)
  Definition families_props
    : (A -> {B : Type@{u} & isProp B})
      ≃ {B : Type@{u} & {f : B -> A & forall a, isProp (fiber f a)}}
    := families_structure (fun B => isProp B).

  (** Part [lem:Set-families]. *)
  Definition families_sets
    : (A -> {B : Type@{u} & isSet B})
      ≃ {B : Type@{u} & {f : B -> A & forall a, isSet (fiber f a)}}
    := families_structure (fun B => isSet B).

  (** Part [cnstr:families+points]. *)
  Definition families_points
    : (A -> {B : Type@{u} & B})
      ≃ {B : Type@{u} & {f : B -> A & forall a, fiber f a}}
    := families_structure (fun B => B).

  (** Corollary [cor:Inj(T)-is-set]: subtypes correspond to predicates by
      taking fibers, and [Inj(T)] is a set. *)
  Definition Inj_eqv_predicates
    : (A -> {B : Type@{u} & isProp B}) ≃ Inj A
    := families_props.

  Definition Inj_isSet : isSet (Inj A)
    := is_ntype_Eqv 0 Inj_eqv_predicates (Pi_isSet (fun _ => PropU_isSet)).

End FamiliesStructure.

(** Exercise: families of [U]-small types versus maps in [U'] with
    essentially [U]-small fibers. *)
Section EssSmallFamilies.

  Universes u v.
  Constraint u < v.
  Context `{Univalence}.

  Definition Sess (X : Type@{v}) : Type@{v} := {Y : Type@{u} & X ≃ Y}.

  Definition Sess_fiber_isContr (Y : Type@{u}) : isContr {X : Type@{v} & X ≃ Y}
    := isContr_Eqv (tot (fun (X : Type@{v}) (p : X = Y) => idtoeqv p);
                    tot_isEquiv _ (fun X => ua X Y))
                   (singleton_contr' (Y : Type@{v})).

  Definition essSmall_total_eqv : {X : Type@{v} & Sess X} ≃ Type@{u}.
  Proof.
    refine (Eqv_comp (sigma_comm Type@{v} Type@{u} (fun X Y => X ≃ Y)) _).
    refine (mkEqv fst
              (fun Y : Type@{u} =>
                 (Y; exist (fun X : Type@{v} => X ≃ Y) Y (idEqv Y))
                 : {y : Type@{u} & {x : Type@{v} & x ≃ y}})
              _ (fun Y => refl)).
    intros [Y w].
    exact (ap (fun w' => (Y; w')) (isContr_isProp' (Sess_fiber_isContr Y) _ w)).
  Defined.

  Definition small_families_eqv (A : Type@{v})
    : (A -> Type@{u})
      ≃ {B : Type@{v} & {f : B -> A & forall a, Sess (fiber f a)}}
    := Eqv_comp (Pi_eqv (fun _ : A => Eqv_inv essSmall_total_eqv))
         (families_structure A Sess).

End EssSmallFamilies.
