(** * Section 2.13 Univalence

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - The book's axiom as a class [UnivalenceUF := ∀ X Y, isEquiv
      idtoeqv], with [ptoe p] the transport in the identity family; its
      inverse is [etop] (the book's [f̄]).  The four identifications in the
      text: [etop (ptoe p) = p], [ptoe (etop f) = f], [etop id = refl] and
      [etop (g f) = etop g · etop f].
    - Exercise [xca:C2]: every [p : Bool = Bool] is [refl] or [swap]
      (the library's [negb]), [refl ≠ swap], and [swap · swap = refl].
    - A preliminary obtains from the library that [isEquiv f] is a
      proposition (the book proves this in 2.15), so that equivalences
      with equal underlying maps are equal.  An instance of
      [UnivalenceUF] is derived from Coq-HoTT's [Univalence] at the end of
      2.15. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S12_InductiveTypes.

Local Open Scope uf_scope.

(** ** Preliminaries: identifying equivalences

    Two equivalences can be identified as soon as their underlying
    functions can, because [isEquiv(f)] is a proposition (shown in the book
    in 2.15, see [isEquiv_isProp] below).  Here we obtain it from the
    library, so that 2.13 can be presented before 2.15. *)

(** [isContr(X)] is a retract of Coq-HoTT's [Contr X], which is an
    h-proposition. *)
Instance ishprop_isContr `{Funext} (X : Type) : IsHProp (isContr X).
Proof.
  apply hprop_allpath. intros a b.
  exact (ap (fun C : Contr X => (center X; contr) : isContr X)
            (path_ishprop (Build_Contr _ (fst a) (snd a))
                          (Build_Contr _ (fst b) (snd b)))).
Defined.

Instance ishprop_isEquiv `{Funext} {X Y : Type} (f : X -> Y)
  : IsHProp (isEquiv f)
  := istrunc_forall.

Definition path_Eqv `{Funext} {X Y : Type} (e e' : X ≃ Y)
  : fst e = fst e' -> e = e'
  := path_sigma_hprop e e'.

Definition idEqv (X : Type) : X ≃ X := (id X; id_isEquiv X).

(** ** 2.13 Univalence *)

(** Definition [def:idtoeq]: transport in the family [id_U]. *)
Definition ptoe {X Y : Type} (p : X = Y) : X -> Y
  := trp (fun T : Type => T) p.

Definition idtoeqv {X Y : Type} (p : X = Y) : X ≃ Y
  := (ptoe p; trp_isEquiv (fun T : Type => T) p).

Definition idtoeqv_refl (X : Type) : idtoeqv (refl X) = idEqv X := refl.

(** Principle [def:univalence]: the univalence axiom postulates
    [ua_{X,Y} : isEquiv(p ↦ ptoe p)]. *)
Class UnivalenceUF := ua : forall X Y : Type, isEquiv (@idtoeqv X Y).

Section Univalence.

  Context `{UnivalenceUF}.

  (** The inverse [f ↦ etop f] (the book's [\bar f]). *)
  Definition etop {X Y : Type} (f : X ≃ Y) : X = Y := eqinv (ua X Y) f.

  Definition etop_ptoe {X Y : Type} (p : X = Y) : etop (idtoeqv p) = p
    := eqinv_l (ua X Y) p.

  Definition ptoe_etop {X Y : Type} (f : X ≃ Y) : idtoeqv (etop f) = f
    := eqinv_r (ua X Y) f.

  Definition etop_id (X : Type) : etop (idEqv X) = refl
    := etop_ptoe refl.

  Context `{Funext}.

  (** [ptoe] turns composition of paths into composition of
      equivalences ([xca:trp-compose]).
    (Exercise [xca:trp-compose] of 2.5, for the universe; placed here since it uses univalence.) *)
  Definition idtoeqv_trans {X Y Z : Type} (p : X = Y) (q : Y = Z)
    : idtoeqv (q ⋅ p) = Eqv_comp (idtoeqv p) (idtoeqv q)
    := path_Eqv (idtoeqv (q ⋅ p)) (Eqv_comp (idtoeqv p) (idtoeqv q))
         (trp_compose (fun T : Type => T) p q).

  (** [etop (g f) = etop g · etop f]. *)
  Definition etop_comp {X Y Z : Type} (f : X ≃ Y) (g : Y ≃ Z)
    : etop (Eqv_comp f g) = etop g ⋅ etop f.
  Proof.
    refine (ap etop (ap011 Eqv_comp (ptoe_etop f)^ (ptoe_etop g)^) @ _).
    refine (ap etop (idtoeqv_trans (etop f) (etop g))^ @ _).
    exact (etop_ptoe _).
  Defined.

  (** Exercise [xca:C2]. *)
  Definition negb_isEquiv : isEquiv negb
    := iso_to_isEquiv negb negb (fun b => match b with yes | no => refl end)
         (fun b => match b with yes | no => refl end).

  Definition swapEqv : Bool ≃ Bool := (negb; negb_isEquiv).

  Definition swap : Bool = Bool :> Type := etop swapEqv.

  (** Every equivalence [Bool -> Bool] is the identity or [negb]. *)
  Definition bool_eqv_cases (f : Bool -> Bool) (t : isEquiv f)
    : (f = id Bool) + (f = negb).
  Proof.
    assert (inj : forall b b', f b = f b' -> b = b').
    { intros b b' e. exact ((eqinv_l t b)^ @ ap (eqinv t) e @ eqinv_l t b'). }
    enough (G : forall b1 b2, f yes = b1 -> f no = b2 -> (f = id Bool) + (f = negb))
      by exact (G _ _ refl refl).
    intros [] [] e1 e2.
    - destruct (yes_ne_no (inj _ _ (e1 @ e2^))).
    - left. apply ptw_inv. intros []; assumption.
    - right. apply ptw_inv. intros []; assumption.
    - destruct (yes_ne_no (inj _ _ (e1 @ e2^))).
  Defined.

  (** [Bool = Bool] has exactly two elements: [refl] and [swap]. *)
  Definition Bool_paths_cases (p : Bool = Bool :> Type)
    : (p = refl) + (p = swap).
  Proof.
    destruct (bool_eqv_cases (ptoe p) (snd (idtoeqv p))) as [e|e].
    - left.
      exact ((etop_ptoe p)^ @ ap etop (path_Eqv (idtoeqv p) (idEqv Bool) e)
             @ etop_id Bool).
    - right.
      exact ((etop_ptoe p)^ @ ap etop (path_Eqv (idtoeqv p) swapEqv e)).
  Defined.

  Definition refl_ne_swap : (refl (Bool : Type) = swap) -> False.
  Proof.
    intro e.
    pose (e' := ap (fun p => fst (idtoeqv p)) e @ ap fst (ptoe_etop swapEqv)).
    exact (yes_ne_no (ptw e' yes)).
  Defined.

  Definition swap_swap : swap ⋅ swap = refl.
  Proof.
    refine ((etop_comp swapEqv swapEqv)^ @ _ @ etop_id Bool).
    apply ap, path_Eqv, ptw_inv. intros []; exact refl.
  Defined.

End Univalence.
