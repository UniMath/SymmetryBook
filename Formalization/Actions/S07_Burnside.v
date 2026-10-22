(** * Section 5.7 The lemma that is not Burnside's

    Part of Chapter 5 ([actions.tex]); see [Actions.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    For a finite group [G] and a finite [G]-set [X] (finiteness in the
    sense of the library's [Finite]):
    - The fixed-point sets [Xfix g] ([X^g]) and stabilizer subsets
      [Stab x] ([UG_x]), with [∑_g X^g ≃ ∑_x UG_x] ([sumXfix_Stab_eqv]).
    - Finiteness of [X^g], [∑_g X^g] and [X/G] ([Xfix_Finite],
      [sumXfix_Finite], [Orbits_Finite]); [X/G] is the quotient of
      [X(sh_G)] by the decidable equivalence relation [∃_g (g · x = y)]
      ([orb_bar_isEquiv], using [quot_isFinSet] of Section 2.24).
    - Splitting [∑_x UG_x] over the orbits ([stab_split]).
    - For each orbit, the Lagrange construction [cor:lagrange-dep-sum]
      applied to the orbit as a subgroup ([orbit_subgrp],
      [orbit_count_eqv]); instead of choosing "least" elements, the
      choice functions are obtained (merely) by finite choice, which
      suffices since the statement is a proposition.
    - Lemma [lem:burnside] ([burnside]):
      [Card(∑_g X^g) = Card(X/G) · Card(G)].

    Left out (statements only, no proofs yet; time limit per result)
    - Example [exa:prep-burnside] ([exa_prep_burnside_stmt], with
      [bitsC4]) and Fermat's Little Theorem ([fermat_little_stmt], with
      the library's [IsPrime] and [NatDivides]); these need the
      computation of the action of [C_p] on [Fin p → Fin n].
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core HFiber
  Spaces.Finite.Fin Spaces.Finite.Finite Spaces.Nat.Core Spaces.Nat.Division Projective.
From SymmetryBook Require Export Actions.S06_Cayley.

Local Open Scope uf_scope.

(** ** 5.7 The lemma that is not Burnside's

    The section is also labelled [lem:burnsides-lemma]. *)

(** Example [exa:prep-burnside] (statement only): [C_4] acting on binary
    sequences of length [4], [X(A, f) :≡ (A → Fin 2)], has [6] orbits. *)
Definition bitsC4 `{Univalence} : GSet (CG 3)
  := fun c => ((fst (fst (fst c)) -> Fin 2); Pi_isSet (fun _ => Fin_isSet 2)).

Definition exa_prep_burnside_stmt `{Univalence} : Type := Orbits bitsC4 ≃ Fin 6.

Section Burnside.

  Context `{Univalence} {G : Group} (X : GSet G)
    (FG : Finite (USym G)) (FX : Finite (el X (sh G))).

  Local Notation S0 := (el X (sh G)).

  #[local] Instance FG' : Finite (USym G) := FG.
  #[local] Instance FX' : Finite S0 := FX.

  #[local] Instance S0_dec : DecidablePaths S0 := _.

  (** The set [X^g] of points fixed by [g], and the stabilizer subset
      [UG_x] of [x]. *)
  Definition Xfix (g : USym G) : Type := {x : S0 & act X g x = x}.

  Definition Stab (x : S0) : Type := {g : USym G & act X g x = x}.

  #[local] Instance act_eq_hprop (g : USym G) (x y : S0) : IsHProp (act X g x = y)
    := isProp_IsHProp (el_isSet X _ _ _).

  Definition Xfix_Finite (g : USym G) : Finite (Xfix g) := _.

  Definition sumXfix_Finite : Finite {g : USym G & Xfix g}
    := finite_sigma _ (H0 := Xfix_Finite).

  Definition sumXfix_Stab_eqv : {g : USym G & Xfix g} ≃ {x : S0 & Stab x}
    := sigma_comm (USym G) S0 (fun g x => act X g x = x).

  (** [X/G] is finite: it is the quotient of [X(sh_G)] by the decidable
      equivalence relation [∃_g (g · x = y)] (corollary [cor:orbit-equiv] of 5.4). *)
  Definition Rorb (x y : S0) : PropU := ptrunc_PropU {g : USym G & act X g x = y}.

  Definition Rorb_refl (x : S0) : fst (Rorb x x) := trunc (refl; refl).

  Definition Rorb_symm (x y : S0) : fst (Rorb x y) -> fst (Rorb y x)
    := Trunc_functor (-1) (fun w => ((fst w)⁻¹; ap (act X (fst w)⁻¹) (snd w)⁻¹
                                                @ act_inv_l X (fst w) x)).

  Definition act_comp {z w v : utype (BG G)} (p : z = w) (q : w = v) (a : el X z)
    : act X (q ⋅ p) a = act X q (act X p a).
  Proof. destruct q, p. exact refl. Defined.

  Definition Rorb_trans (x y z : S0) : fst (Rorb x y) -> fst (Rorb y z) -> fst (Rorb x z).
  Proof.
    intros r r'. refine (ptrunc_rec ptrunc_isProp _ r). intros [g e].
    refine (Trunc_functor (-1) _ r'). intros [h e'].
    exact (h ⋅ g; act_comp g h x @ ap (act X h) e @ e').
  Defined.

  Definition Rorb_dec (x y : S0) : isDecidable (fst (Rorb x y)).
  Proof.
    destruct (decidable_merely_finite {g : USym G & act X g x = y}) as [d|d].
    - exact (inl d).
    - exact (inr d).
  Defined.

  Definition orb_bar : quot Rorb -> Orbits X
    := fbar Rorb Rorb_refl (Orbits_isSet X) (orb X)
         (fun x y r => Overture.snd (orb_eq_iff X x y) r).

  Definition orb_bar_isEquiv : isEquiv orb_bar.
  Proof.
    refine (inj_surj_isEquiv (cancel_isInj (Orbits_isSet X) _) _).
    - refine (im_ind Rorb _ (fun a => Pi_isProp (fun b => Pi_isProp (fun _ => quot_isSet Rorb a b))) _).
      intro x.
      refine (im_ind Rorb _ (fun b => Pi_isProp (fun _ => quot_isSet Rorb _ b)) _).
      intros y e.
      exact (snd (cls_eq_iff Rorb Rorb_refl Rorb_symm Rorb_trans x y)
               (Overture.fst (orb_eq_iff X x y) e)).
    - intro O. refine (Trunc_functor (-1) _ (orb_isSurj X O)). intros [x e].
      exact (SymmetryBook.IntroUF.S22_SetOperations.cls Rorb x; e).
  Defined.

  #[local] Instance Orbits_Finite : Finite (Orbits X).
  Proof.
    apply isFinSet_Finite.
    refine (isFinSet_Eqv (Eqv_inv (orb_bar; orb_bar_isEquiv)) _).
    exact (quot_isFinSet (Finite_isFinSet FX) Rorb Rorb_refl Rorb_symm Rorb_trans Rorb_dec).
  Defined.

  (** Splitting [∑_x UG_x] over the orbits. *)
  Definition StabZ (O : Orbits X) (x : S0) : Type := (O = orb X x) × Stab x.

  Definition stab_split : {x : S0 & Stab x} ≃ {O : Orbits X & {x : S0 & StabZ O x}}.
  Proof.
    refine (Eqv_comp _ (sigma_comm S0 (Orbits X) (fun x O => StabZ O x))).
    refine (tot (fun x (s : Stab x) => ((orb X x; (refl; s)) : {O : Orbits X & StabZ O x}));
            tot_isEquiv _ (fun x => _)).
    refine (iso_to_isEquiv _ (fun w : {O : Orbits X & StabZ O x} => snd (snd w)) _ _).
    - intro s. exact refl.
    - intros [O [e s]]. revert O e. refine (paths_ind_r _ _ _). exact refl.
  Defined.

  (** The orbit of [x₀] as a subgroup, and the Lagrange construction for it. *)
  Section PerOrbit.

    Variable x0 : S0.

    Local Notation X0 := (GSet_sub X (orbit0_sub X (sh G; x0))).

    Definition orbit_subgrp : SubGrp G
      := (X0; ((x0; trunc refl); orbit0_trans X (sh G; x0))).

    Definition X0_mem_iff (x : S0)
      : fst (orbit0_sub X (sh G; x0) (sh G) x) <-> (orb X x0 = orb X x).
    Proof.
      split.
      - intro r. exact (ptrunc_rec (Orbits_isSet X _ _) (fun r => orbit0_path X r) r).
      - intro e. exact (orbit0_eff X _ _ e).
    Defined.

    Definition X0_Finite : Finite (el X0 (sh G)).
    Proof.
      refine (finite_equiv' {x : S0 & fst (Rorb x0 x)} _ _).
      refine (equiv_functor_sigma_id (fun x => Equiv_of_Eqv (Eqv_of_props ptrunc_isProp ptrunc_isProp
                (Trunc_functor (-1) (eqinv (snd (XhG_paths_eqv X x0 x))))
                (Trunc_functor (-1) (fst (XhG_paths_eqv X x0 x)))))).
    Defined.

    Definition orbit_choice
      : ptrunc (forall y : el X0 (sh G),
                  {g : USym G & act X0 g y = sg_pt orbit_subgrp})
      := @finite_choice _ X0_Finite _ (fun _ => tt) (lagrange_choice orbit_subgrp).

    (** Loops in [Tot(X₀)] are stabilizing symmetries. *)
    Definition X0_loops_eqv (x : S0) (m : fst (orbit0_sub X (sh G; x0) (sh G) x))
      : (((sh G; (x; m)) : TotG X0) = (sh G; (x; m))) ≃ Stab x.
    Proof.
      refine (Eqv_comp (XhG_paths_eqv X0 (x; m) (x; m)) _).
      refine (tot (fun g (e : act X0 g (x; m) = (x; m)) => (act_sub_fst X _ g _)^ @ ap fst e);
              tot_isEquiv _ (fun g => _)).
      refine (snd (Eqv_of_props (el_isSet X0 _ _ _) (el_isSet X _ _ _) _
                     (fun e => sub_path X _ (act_sub_fst X _ g _ @ e)))).
    Defined.

    Definition orbit_sum_eqv
      : {y : el X0 (sh G) & ((sh G; y) : TotG X0) = (sh G; y)}
        ≃ {x : S0 & StabZ (orb X x0) x}.
    Proof.
      refine (Eqv_comp (Eqv_inv (sigma_assoc S0 (fun x => fst (orbit0_sub X (sh G; x0) (sh G) x))
                (fun x m => ((sh G; (x; m)) : TotG X0) = (sh G; (x; m))))) _).
      pose (Ex := fun x =>
        Eqv_comp ((tot (fun m => fst (X0_loops_eqv x m));
                   tot_isEquiv _ (fun m => snd (X0_loops_eqv x m))))
                 (Eqv_of_Equiv (equiv_functor_sigma'
                    (Equiv_of_Eqv (Eqv_of_props ptrunc_isProp (Orbits_isSet X _ _)
                       (Overture.fst (X0_mem_iff x)) (Overture.snd (X0_mem_iff x))))
                    (fun _ => equiv_idmap)))
        : {m : fst (orbit0_sub X (sh G; x0) (sh G) x) &
             ((sh G; (x; m)) : TotG X0) = (sh G; (x; m))} ≃ StabZ (orb X x0) x).
      exact (tot (fun x => fst (Ex x)); tot_isEquiv _ (fun x => snd (Ex x))).
    Defined.

    (** Construction [cor:lagrange-dep-sum] of 5.3, for the orbit of [x₀]. *)
    Definition orbit_count_eqv
      : ptrunc (USym G ≃ {x : S0 & StabZ (orb X x0) x})
      := Trunc_functor (-1) (fun f => Eqv_comp (lagrange_dep orbit_subgrp f) orbit_sum_eqv)
           orbit_choice.

  End PerOrbit.

  Definition per_orbit_eqv (O : Orbits X)
    : ptrunc (USym G ≃ {x : S0 & StabZ O x}).
  Proof.
    refine (ptrunc_rec ptrunc_isProp _ (orb_isSurj X O)). intros [x0 e].
    exact (trp (fun O' => ptrunc (USym G ≃ {x : S0 & StabZ O' x})) e⁻¹ (orbit_count_eqv x0)).
  Defined.

  (** Lemma [lem:burnside], equation [eq:burnside]:
      [Card(∑_g X^g) = Card(X/G) · Card(G)]; the
      sets [X^g], [∑_g X^g] and [X/G] are finite ([Xfix_Finite],
      [sumXfix_Finite], [Orbits_Finite]). *)
  Definition burnside
    : @fcard _ sumXfix_Finite = (@fcard _ Orbits_Finite * fcard (USym G))%nat.
  Proof.
    refine (ptrunc_rec (ℕ_isSet _ _) _
              (@finite_choice _ Orbits_Finite _ (fun _ => tt) per_orbit_eqv)).
    intro E.
    pose (e := Eqv_comp sumXfix_Stab_eqv
                 (Eqv_comp stab_split
                    (Eqv_comp ((tot (fun O => eqinv (snd (E O)));
                                tot_isEquiv _ (fun O => eqinv_isEquiv (snd (E O))))
                               : {O : Orbits X & {x : S0 & StabZ O x}} ≃ (Orbits X × USym G))
                       (binprod_prod (Orbits X) (USym G))))).
    refine (@fcard_equiv' _ _ (Equiv_of_Eqv e) sumXfix_Finite _ @ _).
    exact (fcard_prod _ _).
  Defined.

End Burnside.

(** Fermat's Little Theorem (statement only). *)
Definition fermat_little_stmt : Type
  := forall p n : ℕ, IsPrime p -> NatDivides p (nat_pow n p - n)%nat.
