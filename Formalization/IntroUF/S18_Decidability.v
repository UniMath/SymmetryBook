(** * Section 2.18 Decidability, excluded middle and propositional resizing

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Decidable propositions, LEM, double-negation elimination; LEM
      implies DNE, and exercise [xca:dne-lem] (DNE implies LEM).
    - Exercise [xca:lem-prop]: LEM holds iff [(yes = _) : Bool → Prop] is
      an equivalence (by univalence).
    - Propositional resizing for universes [u < v], and exercise
      [xca:lem-prop-sizing]: LEM in the larger universe implies it. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S17_SurjInj.

Local Open Scope uf_scope.

(** ** 2.18 Decidability, excluded middle and propositional resizing *)

(** Definition [def:decidability]. *)
Definition isDecidable (P : Type) : Type := P ⨿ ¬ P.

(** Principle [pri:lem]: the Law of Excluded Middle. *)
Definition LEM : Type := forall P : Type, isProp P -> P ⨿ ¬ P.

(** Exercise [xca:lem-prop]: LEM holds iff [(yes = _) : Bool → Prop] is an
    equivalence. *)
Section LEMProp.

  Context `{Univalence}.

  Definition yes_eq : Bool -> PropU := fun b => ((yes = b); isSet_bool yes b).

  Definition LEM_yes_eq_isEquiv (lem : LEM) : isEquiv yes_eq.
  Proof.
    pose (g := fun P : PropU =>
                 match lem (fst P) (snd P) with inl _ => yes | inr _ => no end).
    refine (iso_to_isEquiv yes_eq g _ _).
    - intros []; unfold g; cbn.
      + destruct (lem (yes = yes) _) as [e|ne].
        * exact refl.
        * destruct (ne refl).
      + destruct (lem (yes = no) _) as [e|ne].
        * destruct (yes_ne_no e).
        * exact refl.
    - intro P. unfold g.
      destruct (lem (fst P) (snd P)) as [p|np].
      + exact (path_PropU (P := yes_eq yes) (fun _ => p) (fun _ => refl)).
      + exact (path_PropU (P := yes_eq no)
                 (fun e => match yes_ne_no e with end)
                 (fun p => match np p with end)).
  Defined.

  Definition yes_eq_isEquiv_LEM (t : isEquiv yes_eq) : LEM.
  Proof.
    intros P hP.
    generalize (eqinv_r t (P; hP)). generalize (eqinv t (P; hP)).
    intros b e.
    pose (e1 := ap fst e : (yes = b) = P).
    destruct b.
    - exact (inl (ptoe e1 refl)).
    - exact (inr (fun p => yes_ne_no (ptoe e1⁻¹ p))).
  Defined.

End LEMProp.

(** Proof by contradiction: LEM implies double-negation elimination. *)
Definition DNE : Type := forall P : Type, isProp P -> ¬ ¬ P -> P.

Definition LEM_DNE (lem : LEM) : DNE
  := fun P hP nnp => match lem P hP with
                     | inl p => p
                     | inr np => match nnp np with end
                     end.

(** Exercise [xca:dne-lem]: double-negation elimination implies LEM. *)
Definition DNE_LEM `{Funext} (dne : DNE) : LEM
  := fun P hP => dne (P ⨿ ¬ P) (lem_isProp hP)
                   (fun k => k (inr (fun p => k (inl p)))).

(** Principle [pri:prop-resizing]: for universes [U : U'], the map
    [(P ↦ P) : Prop_U → Prop_U'] is an equivalence. *)
Section Resizing.

  Universes u v.
  Constraint u < v.

  Definition lift_PropU : {X : Type@{u} & isProp X} -> {X : Type@{v} & isProp X}
    := fun P => exist (fun X : Type@{v} => isProp X) (fst P) (fun a b => snd P a b).

  Definition PropResizing : Type := isEquiv lift_PropU.

  (** [True] and [False] as propositions in [U]. *)
  Definition True_u : {X : Type@{u} & isProp X}
    := exist (fun X : Type@{u} => isProp X) True (fun a b => True_isProp a b).
  Definition False_u : {X : Type@{u} & isProp X}
    := exist (fun X : Type@{u} => isProp X) False (fun a b => False_isProp a b).

  (** Exercise [xca:lem-prop-sizing]: LEM (in [U']) implies propositional
      resizing. *)
  Definition LEM_PropResizing `{Univalence}
    (lem : forall P : Type@{v}, isProp P -> P ⨿ ¬ P) : PropResizing.
  Proof.
    pose (g := fun Q : {X : Type@{v} & isProp X} =>
                 match lem (fst Q) (snd Q) with
                 | inl _ => True_u
                 | inr _ => False_u
                 end).
    refine (iso_to_isEquiv lift_PropU g _ _).
    - intro P. unfold g; cbn.
      destruct (lem (fst P) (fun a b => snd P a b)) as [p|np].
      + exact (path_PropU (P := True_u) (fun _ => p) (fun _ => triv)).
      + exact (path_PropU (P := False_u)
                 (fun x => match x with end) (fun p => match np p with end)).
    - intro Q. unfold g.
      destruct (lem (fst Q) (snd Q)) as [q|nq].
      + exact (path_PropU (P := lift_PropU True_u) (fun _ => q) (fun _ => triv)).
      + exact (path_PropU (P := lift_PropU False_u)
                 (fun x => match x with end) (fun q => match nq q with end)).
  Defined.

End Resizing.
