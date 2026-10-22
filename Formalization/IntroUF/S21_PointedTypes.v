(** * Section 2.21 Pointed types

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Own pointed types, since the library's [pType] are records with
      pointing paths [f(pt) = pt], whereas the book uses pairs and
      [pt = f(pt)]: [U_* :≡ ∑_{A:U} A], [A_+], underlying types [utype X]
      (the book's [X_÷]), base points [pt X], pointed maps [X →* Y] as the
      fiber of [ev_{pt_X}] at [pt_Y], composition and pointed identities.
    - Exercises [xca:plusforgetadjoint] and [xca:freemaps].
    - Pointed equivalences [X ≃* Y], and exercise [xca:pointedequiv]:
      [(X = Y) ≃ (X ≃* Y)], by showing that [∑_Y (X ≃* Y)] is
      contractible (using univalence).
    - [con:identity-ptd-maps] ([ptw_*]), following the book's chain of
      equivalences, and exercise [xca:identity-ptd-maps] ([ptw_*] by
      induction).
    - Exercise [xca:filler-ptd-sum-of-fibers], with the equivalence
      [(∑_y f⁻¹(y)) ≃ X] constructed here.
    - Exercise [xca:ptd-equiv-inv]: the pointed inverse, and
      identifications of [f⁻¹ f] and [f f⁻¹] with the pointed identities;
      for the second we use the half-adjoint coherence ([eisadj]) of
      Coq-HoTT, as in Theorem 4.2.3 of the HoTT Book. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S20_Subtypes.

Local Open Scope uf_scope.

(** ** 2.21 Pointed types

    The book's pointed types are pairs, and its pointing paths have the
    form [pt_Y = f(pt_X)]; the library's [pType] is a record and its
    pointed maps have pointing paths [f(pt) = pt], so we use our own
    definitions. *)

(** Definition [def:pointedtypes]. *)
Definition Ustar : Type := {A : Type & A}.

(** The underlying type [X_÷] and the base point [pt_X]. *)
Definition utype (X : Ustar) : Type := fst X.
Definition pt (X : Ustar) : utype X := snd X.

(** [A_+ :≡ (A ⨿ True, inr triv)]. *)
Definition plus (A : Type) : Ustar := ((A ⨿ True); inr triv).

(** Pointed functions [X →* Y], the fiber of [ev_{pt_X}] at [pt_Y]. *)
Definition pmap (X Y : Ustar) : Type
  := fiber (@ev (utype X) (fun _ => utype Y) (pt X)) (pt Y).

Notation "X →* Y" := (pmap X Y) (at level 99) : uf_scope.

Definition pmap_unfold (X Y : Ustar)
  : (X →* Y) = {f : utype X -> utype Y & pt Y = f (pt X)} := refl.

(** Composition [gf :≡ (g_÷ f_÷, g_÷(f_pt) · g_pt)]. *)
Definition pcomp {X Y Z : Ustar} (g : Y →* Z) (f : X →* Y) : X →* Z
  := (fst g ∘ fst f; ap (fst g) (snd f) ⋅ snd g).

(** Definition [def:pointedidentity]. *)
Definition pid (X : Ustar) : X →* X := (id (utype X); refl).

(** Remark [rem:coerceawaypt]: we write [x : X] for [x : X_÷] (informal
    convention; here we write [utype X] explicitly). *)

(** Exercise [xca:plusforgetadjoint]. *)
Definition plus_adjoint `{Funext} (A : Type) (B : Ustar)
  : (A -> utype B) ≃ (plus A →* B).
Proof.
  refine (mkEqv
            (fun h => ((fun z => match z with
                                 | inl a => h a
                                 | inr _ => pt B
                                 end); refl))
            (fun k => fst k ∘ inl) (fun h => refl) _).
  intros [k p].
  pose (Hk := fun z : A ⨿ True =>
               match z return match z with
                              | inl a => k (inl a)
                              | inr _ => pt B
                              end = k z with
               | inl a => refl
               | inr t => match t with triv => p end
               end).
  refine (pathpair (ptw_inv Hk) _).
  refine (trptw (x := inr triv) (y := pt B) (ptw_inv Hk) refl @ trans_1p _ @ _).
  exact (ap (fun F => F (inr triv)) (eqinv_r (funext _ _) Hk)).
Defined.

(** Exercise [xca:freemaps]. *)
Definition freemaps (A : Ustar) (B : Type)
  : {b : B & A →* (B; b)} ≃ (utype A -> B).
Proof.
  refine (mkEqv (fun w => fst (snd w))
                (fun f => (f (pt A); ((f; refl) : A →* (B; f (pt A))))
                          : {b : B & A →* (B; b)})
                _ (fun f => refl)).
  intros [b [f p]]. change (utype A -> B) in f. cbn in p |- *.
  revert b p. refine (paths_ind_r _ _ _). exact refl.
Defined.

(** Definition [def:pointedequiv]. *)
Definition pEqv (X Y : Ustar) : Type := {f : X →* Y & isEquiv (fst f)}.

Notation "X ≃* Y" := (pEqv X Y) (at level 85) : uf_scope.

(** Exercise [xca:pointedequiv]. *)
Definition pdiv {X Y : Ustar} (p : X = Y) : utype X = utype Y := ap utype p.

Definition ppt {X Y : Ustar} (p : X = Y) : pt Y = ptoe (pdiv p) (pt X)
  := match p with refl => refl end.

Definition path_to_pEqv {X Y : Ustar} (p : X = Y) : X ≃* Y
  := ((ptoe (pdiv p); ppt p); trp_isEquiv (fun T : Type => T) (pdiv p)).

Definition pEqv_total_isContr `{Univalence} (X : Ustar)
  : isContr {Y : Ustar & X ≃* Y}.
Proof.
  destruct X as [A a].
  pose (fw := fun v : {Y : Ustar & (A; a) ≃* Y} =>
       ((fst (fst v); (fst (fst (snd v)); snd (snd v))) : {B : Type & A ≃ B};
        (snd (fst v); snd (fst (snd v))))
       : {w : {B : Type & A ≃ B} & {b : fst w & b = fst (snd w) a}}).
  pose (bw := fun u : {w : {B : Type & A ≃ B} & {b : fst w & b = fst (snd w) a}} =>
       (((fst (fst u); fst (snd u)) : Ustar;
        ((fst (snd (fst u)); snd (snd u)); snd (snd (fst u))))
        : {Y : Ustar & (A; a) ≃* Y})).
  assert (Re : {Y : Ustar & (A; a) ≃* Y}
               ≃ {w : {B : Type & A ≃ B} & {b : fst w & b = fst (snd w) a}}).
  { refine (mkEqv fw bw _ _).
    - intros [[B b] [[f p] e]]. exact refl.
    - intros [[B [f e]] [b p]]. exact refl. }
  refine (isContr_Eqv (Eqv_inv Re) _).
  refine (Sigma_isContr _ (fun w => singleton_contr' _)).
  exact (isContr_Eqv (tot (fun B (p : A = B) => idtoeqv p);
                      tot_isEquiv _ (fun B => ua A B))
                     (singleton_contr A)).
Defined.

Definition path_to_pEqv_isEquiv `{Univalence} (X Y : Ustar)
  : isEquiv (@path_to_pEqv X Y)
  := isEquiv_from_tot (fun Y => @path_to_pEqv X Y)
       (contr_map_isEquiv (singleton_contr X) (pEqv_total_isContr X) _) Y.

(** Construction [con:identity-ptd-maps]: [ptw_*], following the book's
    chain of equivalences. *)
Definition ptw_star `{Funext} {X Y : Ustar} (f g : X →* Y)
  : (f = g) ≃ {h : forall x, fst f x = fst g x & h (pt X) ⋅ snd f = snd g}.
Proof.
  destruct f as [f fp], g as [g gp].
  refine (Eqv_comp (Eqv_inv (path_sigma_eqv (Y := fun k => pt Y = k (pt X)))) _).
  refine (Eqv_comp (sum_equiv_base (funext f g)
                      (fun e => PathOver (fun k => pt Y = k (pt X)) e fp gp)) _).
  pose (E := fun h : forall x, f x = g x =>
               Eqv_comp (eq_l_eqv (w := gp) (trptw (ptw_inv h) fp))
                        (eq_l_eqv (w := gp) (ap (fun H : (forall x, f x = g x) => H (pt X) ⋅ fp)
                                      (eqinv_r (funext f g) h)))).
  exact (tot (fun h => fst (E h)); tot_isEquiv _ (fun h => snd (E h))).
Defined.

(** Exercise [xca:identity-ptd-maps]: [ptw_*] by induction. *)
Definition ptw_star_ind {X Y : Ustar} {f g : X →* Y} (e : f = g)
  : {h : forall x, fst f x = fst g x & h (pt X) ⋅ snd f = snd g}
  := match e with refl => ((fun x => refl); refl) end.

(** Exercise [xca:filler-ptd-sum-of-fibers]. *)
Section SumOfFibers.

  Context {X Y : Ustar} (f : X →* Y).

  Definition SumFib : Ustar
    := ({y : utype Y & fiber (fst f) y}; (pt Y; (pt X; snd f))).

  Definition sumfib_e : SumFib →* X := ((fun w => fst (snd w)); refl).

  Definition sumfib_e_isEquiv : isEquiv (fst sumfib_e).
  Proof.
    refine (iso_to_isEquiv _ (fun x => (fst f x; (x; refl))) _ (fun x => refl)).
    intros [y [x p]]. cbn in p |- *.
    revert y p. refine (paths_ind_r _ _ _). exact refl.
  Defined.

  Definition sumfib_fst : SumFib →* Y := (fst; refl).

  Definition sumfib_filler `{Funext} : sumfib_fst = pcomp f sumfib_e
    := eqinv (snd (ptw_star sumfib_fst (pcomp f sumfib_e)))
         ((fun w : utype SumFib => snd (snd w)); trans_1p (snd f)).

End SumOfFibers.

(** Exercise [xca:ptd-equiv-inv]: the pointed inverse of a pointed
    equivalence.  We take the (unpointed) inverse together with the
    half-adjoint data provided by Coq-HoTT ([eissect], [eisretr],
    [eisadj]) for [isequiv_adjointify]; its inverse function is the
    book's [f⁻¹]. *)
Section PointedInverse.

  Context {X Y : Ustar} (f : X ≃* Y).

  Let F := fst (fst f).
  Let fp : pt Y = F (pt X) := snd (fst f).
  Let E : IsEquiv F := IsEquiv_of_isEquiv (snd f).
  Let g := @equiv_inv _ _ F E.
  Let η := @eissect _ _ F E.
  Let ε := @eisretr _ _ F E.

  Definition pinv : Y ≃* X
    := ((g; (η (pt X) ⋅ ap g fp)⁻¹); eqinv_isEquiv (snd f)).

  Definition pinv_aux1 {Z : Type} {u v w : Z} (a : u = v) (b : v = w)
    : b ⋅ (a ⋅ (b ⋅ a)⁻¹) = refl.
  Proof. destruct b, a. exact refl. Defined.

  Definition pinv_left `{Funext}
    : pcomp (fst pinv) (fst f) = pid X
    := eqinv (snd (ptw_star (pcomp (fst pinv) (fst f)) (pid X)))
         (η; pinv_aux1 (ap g fp) (η (pt X))).

  Definition pinv_aux2 {u v : utype X} (p : u = v)
    : ap F p ⋅ (ap F ((p ⋅ refl)⁻¹) ⋅ refl) = refl.
  Proof. destruct p. exact refl. Defined.

  Definition pinv_aux3 (x0 : utype X)
    : forall (y : utype Y) (q : y = F x0),
      ε y ⋅ (ap F ((η x0 ⋅ ap g q)⁻¹) ⋅ q) = refl.
  Proof.
    refine (paths_ind_r _ _ _).
    refine (ap (fun e => e ⋅ (ap F ((η x0 ⋅ refl)⁻¹) ⋅ refl))
               (@eisadj _ _ F E x0) @ _).
    exact (pinv_aux2 (η x0)).
  Defined.

  Definition pinv_right `{Funext}
    : pcomp (fst f) (fst pinv) = pid Y
    := eqinv (snd (ptw_star (pcomp (fst f) (fst pinv)) (pid Y)))
         (ε; pinv_aux3 (pt X) (pt Y) fp).

End PointedInverse.
