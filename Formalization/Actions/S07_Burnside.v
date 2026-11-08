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
    - Example [exa:prep-burnside] ([exa_prep_burnside], with [bitsC4]):
      [6] orbits.  The symmetries of [(Fin 4, zs)] act on [Fin 4] by maps
      commuting with [zs], hence as rotations [zs^k] ([sym_rot]), and
      [CG_gen 3] acts as [zs] ([trp_gen]); the orbits are counted with
      [orbits_by] (Section 5.4) and a classifier [c4] of the [16]
      sequences, moving each sequence to a representative ([to_rep]).
    - Fermat's Little Theorem ([fermat_little_stmt], with the library's
      [IsPrime] and [NatDivides]); proved as [fermat_little] in Section
      10.2 ([FinGroups/S02_Lagrange.v]), since the book's proof uses
      corollary [cor:cyclicgroupsaresimple].

    Nothing in this section is left out.
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core HFiber
  Spaces.Finite.Fin Spaces.Finite.Finite Spaces.Nat.Core Spaces.Nat.Division Projective.
From SymmetryBook Require Export Actions.S06_Cayley.

Local Open Scope uf_scope.

(** ** 5.7 The lemma that is not Burnside's

    The section is also labelled [lem:burnsides-lemma]. *)

(** Example [exa:prep-burnside]: [C_4] acting on binary
    sequences of length [4], [X(A, f) :≡ (A → Fin 2)], has [6] orbits. *)
Definition bitsC4 `{Univalence} : GSet (CG 3)
  := fun c => ((fst (fst (fst c)) -> Fin 2); Pi_isSet (fun _ => Fin_isSet 2)).

Definition exa_prep_burnside_stmt `{Univalence} : Type := Orbits bitsC4 ≃ Fin 6.

(** The proof of the example.  Symmetries of [sh_{C_4} ≡ (Fin 4, zs)] act
    on [Fin 4] by maps commuting with [zs] ([path_to_CycEqv]), which are
    rotations [zs^k] ([rot4_cases]); the generator [CG_gen 3] acts as
    [zs].  The orbits are then counted by a classifier [c4] of the [16]
    sequences, invariant under rotations, with a rotation to a chosen
    representative for each sequence ([rep_witness]); with
    [orbits_by] this gives [6] orbits. *)
Section PrepBurnside.

  Context `{Univalence}.

  Definition zs4 : Fin 4 -> Fin 4 := fst (finsuccEqv 3).

  Definition p40 : Fin 4 := inl (inl (inl (inr triv))).
  Definition p41 : Fin 4 := inl (inl (inr triv)).
  Definition p42 : Fin 4 := inl (inr triv).
  Definition p43 : Fin 4 := inr triv.

  Definition f4_cases (a : Fin 4) : (a = p40) + (a = p41) + (a = p42) + (a = p43).
  Proof.
    destruct a as [[[[[]|[]]|[]]|[]]|[]];
      [left; left; left | left; left; right | left; right | right]; exact refl.
  Defined.

  (** Rotations [zs^k], [k < 4]. *)
  Definition rotk (k : Fin 4) : Fin 4 -> Fin 4
    := match k with
       | inl (inl (inl (inl e))) => match e with end
       | inl (inl (inl (inr _))) => idmap
       | inl (inl (inr _)) => zs4
       | inl (inr _) => fun x => zs4 (zs4 x)
       | inr _ => fun x => zs4 (zs4 (zs4 x))
       end.

  Definition rot4_cases (h : Fin 4 -> Fin 4) (hc : forall x, h (zs4 x) = zs4 (h x))
    : {k : Fin 4 & forall x, h x = rotk k x}.
  Proof.
    assert (G : forall v : Fin 4, h p40 = v ->
              (h p40 = v) × (h p41 = zs4 v) × (h p42 = zs4 (zs4 v)) × (h p43 = zs4 (zs4 (zs4 v)))).
    { intros v e0.
      pose (e1 := hc p40 @ ap zs4 e0).
      pose (e2 := hc p41 @ ap zs4 e1).
      exact (((e0; e1); e2); hc p42 @ ap zs4 e2). }
    destruct (f4_cases (h p40)) as [[[e|e]|e]|e];
      destruct (G _ e) as [[[e0 e1] e2] e3];
      [exists p40 | exists p41 | exists p42 | exists p43];
      intros [[[[[]|[]]|[]]|[]]|[]]; assumption.
  Defined.

  Definition carrier4 (c : component Cyc (Fincyc 3)) : Type := fst (fst (fst c)).

  Definition trp_carrier_cyc {c c' : component Cyc (Fincyc 3)} (p : c = c') (x : carrier4 c)
    : trp carrier4 p x = fst (fst (path_to_CycEqv (ap fst p))) x.
  Proof. destruct p. exact refl. Defined.

  Definition sym_rot (g : USym (CG 3)) : {k : Fin 4 & forall x, trp carrier4 g x = rotk k x}.
  Proof.
    pose (w := path_to_CycEqv (ap fst g)).
    destruct (rot4_cases (fst (fst w)) (fun x => (ptw (snd w) x))) as [k E].
    exact (k; fun x => trp_carrier_cyc g x @ E x).
  Defined.

  Definition ptoe_etop_pt {X Y : Type} (f : X ≃ Y) (x : X) : ptoe (etop f) x = fst f x
    := ap (fun e : X ≃ Y => fst e x) (ptoe_etop f).

  Definition trp_gen (x : Fin 4) : trp carrier4 (CG_gen 3) x = zs4 x.
  Proof.
    refine ((ptoe_ap carrier4 (CG_gen 3) x)^ @ _).
    refine (ap (fun q : Fin 4 = Fin 4 => ptoe q x) (ap_carrier_CG_gen 3) @ _).
    exact (ptoe_etop_pt (finsuccEqv 3) x).
  Defined.

  (** The symmetry [CG_gen^k], acting as [rotk k]. *)
  Definition symk (k : Fin 4) : USym (CG 3)
    := match k with
       | inl (inl (inl (inl e))) => match e with end
       | inl (inl (inl (inr _))) => refl
       | inl (inl (inr _)) => CG_gen 3
       | inl (inr _) => CG_gen 3 ⋅ CG_gen 3
       | inr _ => CG_gen 3 ⋅ (CG_gen 3 ⋅ CG_gen 3)
       end.

  Definition trp_symk (k : Fin 4) (x : Fin 4) : trp carrier4 (symk k) x = rotk k x.
  Proof.
    destruct k as [[[[[]|[]]|[]]|[]]|[]]; cbn [symk rotk].
    - exact refl.
    - exact (trp_gen x).
    - exact (ptw (trp_compose carrier4 (CG_gen 3) (CG_gen 3)) x
             @ trp_gen _ @ ap zs4 (trp_gen x)).
    - exact (ptw (trp_compose carrier4 (CG_gen 3 ⋅ CG_gen 3) (CG_gen 3)) x @ trp_gen _
             @ ap zs4 (ptw (trp_compose carrier4 (CG_gen 3) (CG_gen 3)) x
                       @ trp_gen _ @ ap zs4 (trp_gen x))).
  Defined.

  Definition act_bits (g : USym (CG 3)) (f : Fin 4 -> Fin 2) (x : Fin 4)
    : act bitsC4 g f x = f (trp carrier4 g⁻¹ x)
    := trp_dom carrier4 (Fin 2) g f x.

  (** The symmetry [(CG_gen^k)⁻¹] acts as precomposition with [rotk k]. *)
  Definition act_symk (k : Fin 4) (f : Fin 4 -> Fin 2) (x : Fin 4)
    : act bitsC4 (symk k)⁻¹ f x = f (rotk k x)
    := act_bits _ f x @ ap (fun q : sh (CG 3) = sh (CG 3) => f (trp carrier4 q x))
                           (symm_symm (symk k))
       @ ap f (trp_symk k x).

  (** Binary sequences by their values. *)
  Definition B4 (a b c d : Fin 2) : Fin 4 -> Fin 2
    := fun y => match y with
                | inl (inl (inl (inl e))) => match e with end
                | inl (inl (inl (inr _))) => a
                | inl (inl (inr _)) => b
                | inl (inr _) => c
                | inr _ => d
                end.

  Definition b4_eta (f : Fin 4 -> Fin 2) (y : Fin 4)
    : B4 (f p40) (f p41) (f p42) (f p43) y = f y.
  Proof. destruct y as [[[[[]|[]]|[]]|[]]|[]]; exact refl. Defined.

  Definition f4_funext {f f' : Fin 4 -> Fin 2} (e0 : f p40 = f' p40) (e1 : f p41 = f' p41)
    (e2 : f p42 = f' p42) (e3 : f p43 = f' p43) : f = f'.
  Proof. apply ptw_inv. intros [[[[[]|[]]|[]]|[]]|[]]; assumption. Defined.

  Definition o60 : Fin 6 := inl (inl (inl (inl (inl (inr triv))))).
  Definition o61 : Fin 6 := inl (inl (inl (inl (inr triv)))).
  Definition o62 : Fin 6 := inl (inl (inl (inr triv))).
  Definition o63 : Fin 6 := inl (inl (inr triv)).
  Definition o64 : Fin 6 := inl (inr triv).
  Definition o65 : Fin 6 := inr triv.

  (** The classifier: all [0], all [1], one [1], two adjacent [1]s, two
      opposite [1]s, three [1]s. *)
  Definition c4 (a b c d : Fin 2) : Fin 6
    := match a, b, c, d with
       | inl (inr _), inl (inr _), inl (inr _), inl (inr _) => o60
       | inr _, inr _, inr _, inr _ => o61
       | inr _, inl (inr _), inl (inr _), inl (inr _) => o62
       | inl (inr _), inr _, inl (inr _), inl (inr _) => o62
       | inl (inr _), inl (inr _), inr _, inl (inr _) => o62
       | inl (inr _), inl (inr _), inl (inr _), inr _ => o62
       | inr _, inl (inr _), inr _, inl (inr _) => o64
       | inl (inr _), inr _, inl (inr _), inr _ => o64
       | inl (inr _), inr _, inr _, inr _ => o65
       | inr _, inl (inr _), inr _, inr _ => o65
       | inr _, inr _, inl (inr _), inr _ => o65
       | inr _, inr _, inr _, inl (inr _) => o65
       | _, _, _, _ => o63
       end.

  Definition rep4 (u : Fin 6) : Fin 4 -> Fin 2
    := match u with
       | inl (inl (inl (inl (inl (inl e))))) => match e with end
       | inl (inl (inl (inl (inl (inr _))))) => B4 fin2_0 fin2_0 fin2_0 fin2_0
       | inl (inl (inl (inl (inr _)))) => B4 fin2_1 fin2_1 fin2_1 fin2_1
       | inl (inl (inl (inr _))) => B4 fin2_1 fin2_0 fin2_0 fin2_0
       | inl (inl (inr _)) => B4 fin2_1 fin2_1 fin2_0 fin2_0
       | inl (inr _) => B4 fin2_1 fin2_0 fin2_1 fin2_0
       | inr _ => B4 fin2_1 fin2_1 fin2_1 fin2_0
       end.

  Definition c4_rot (k : Fin 4) (a b c d : Fin 2)
    : c4 (B4 a b c d (rotk k p40)) (B4 a b c d (rotk k p41))
         (B4 a b c d (rotk k p42)) (B4 a b c d (rotk k p43)) = c4 a b c d.
  Proof.
    destruct k as [[[[[]|[]]|[]]|[]]|[]];
      destruct a as [[[]|[]]|[]], b as [[[]|[]]|[]], c as [[[]|[]]|[]], d as [[[]|[]]|[]];
      exact refl.
  Defined.

  Definition rep_witness (a b c d : Fin 2)
    : {k : Fin 4 & forall x, B4 a b c d (rotk k x) = rep4 (c4 a b c d) x}.
  Proof.
    destruct a as [[[]|[]]|[]], b as [[[]|[]]|[]], c as [[[]|[]]|[]], d as [[[]|[]]|[]];
      first [ exists p40; intros [[[[[]|[]]|[]]|[]]|[]]; exact refl
            | exists p41; intros [[[[[]|[]]|[]]|[]]|[]]; exact refl
            | exists p42; intros [[[[[]|[]]|[]]|[]]|[]]; exact refl
            | exists p43; intros [[[[[]|[]]|[]]|[]]|[]]; exact refl ].
  Defined.

  Let cl (f : Fin 4 -> Fin 2) : Fin 6 := c4 (f p40) (f p41) (f p42) (f p43).

  (** Every sequence is moved to its representative. *)
  Definition to_rep (f : Fin 4 -> Fin 2) : {g : USym (CG 3) & act bitsC4 g f = rep4 (cl f)}.
  Proof.
    destruct (rep_witness (f p40) (f p41) (f p42) (f p43)) as [k E].
    exists (symk k)⁻¹.
    apply ptw_inv. intro x.
    exact (act_symk k f x @ (b4_eta f _)^ @ E x).
  Defined.

  Definition exa_prep_burnside : exa_prep_burnside_stmt.
  Proof.
    refine (orbits_by bitsC4 (Fin_isSet 6) cl _ _ _).
    - intros g f.
      destruct (sym_rot g⁻¹) as [k E].
      refine (_ @ c4_rot k (f p40) (f p41) (f p42) (f p43)).
      unfold cl.
      refine (ap011 (fun u v => c4 u v _ _) _ _ @ ap011 (fun u v => c4 _ _ u v) _ _);
        refine (act_bits g f _ @ ap f (E _) @ (b4_eta f _)^).
    - intros f f' e.
      destruct (to_rep f) as [h Eh], (to_rep f') as [h' Eh'].
      apply trunc. exists (h'⁻¹ ⋅ h).
      refine (ptw (trp_compose (el bitsC4) h h'⁻¹) f @ _).
      change (act bitsC4 h'⁻¹ (act bitsC4 h f) = f').
      refine (ap (act bitsC4 h'⁻¹) (Eh @ ap rep4 e @ Eh'^) @ _).
      exact (trp_V_p (el bitsC4) h' f').
    - intro u. apply trunc. exists (rep4 u).
      destruct u as [[[[[[[]|[]]|[]]|[]]|[]]|[]]|[]]; exact refl.
  Defined.

End PrepBurnside.

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

(** Fermat's Little Theorem (proved in Section 10.2 as [fermat_little]). *)
Definition fermat_little_stmt : Type
  := forall p n : ℕ, IsPrime p -> NatDivides p (nat_pow n p - n)%nat.
