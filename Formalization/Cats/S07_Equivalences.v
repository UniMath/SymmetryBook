(** * Section 6.7 Equivalences of categories

    Part of Chapter 6 ([cats.tex]); see [Cats.v] for an overview of the
    chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:cat-equiv] ([isCatEquiv], [CatEquiv]); the
      identity equivalence ([idCatEquiv], [idtoCatEquiv]).
    - Lemma [lem:cat-equiv-ff] ([cat_equiv_ff]; only the unit being an
      isomorphism is used).
    - Definitions [def:functor-split-eso] ([isSplitEso], [isEso]) and
      [def:we-cat] ([isWeakEquiv]); precomposition with a functor
      ([precompF]).
    - Definition [def:Rezk-completion] ([Rezk], [RezkEta]) and theorem
      [thm:Rezk-completion], first part: [η] is a weak equivalence
      ([RezkEta_isWeakEquiv]).  NOTE for the book text: for a
      precategory, [isRepr(F)] need not be a proposition, so the full
      subcategory should be taken on [‖isRepr(F)‖] ([isReprU]).  [L(C)]
      is a category ([Rezk_isUnivalent], under univalence, as a full
      subcategory of the presheaf category).
    - Lemma [lem:cat-equiv-is-prop] ([lem_cat_equiv_is_prop], from
      [cor_adj_unique]).
    - Lemma [lem:equiv-precat-is-ff-split-eso]
      ([lem_equiv_precat_is_ff_split_eso]): the inverse [fse_equiv]
      builds the adjunction by [lem:adj-via-repr] from
      [α(f) :≡ F⁻¹(i_B⁻¹ ∘ f)]; fully faithful functors reflect
      isomorphisms ([ff_reflect_iso]).
    - Theorem [thm:Rezk-completion], second part ([thm_Rezk_small],
      assuming [Replacement] and [Univalence]; deviation: replacement is
      applied to [Ob(η)], using that [L(C)] is a locally small category,
      [Cat_locSmall]), and exercise [xca:Rezk-completion-locally-small]
      ([xca_Rezk_locally_small], with [Univalence]; by Yoneda,
      [Rezk_hom_eqv]).
    - Lemma [lem:ff-eso] ([lem_ff_eso]): for [C] a category and [F] fully
      faithful, [∑_A F(A) ≅ B] is equivalent to a singleton once
      inhabited ([IsoC_postcomp_isEquiv], [fmap_iso_isEquiv]).
    - Lemma [lem:precomp-equiv-cat] ([lem_precomp_equiv_cat], following
      HoTT book 9.9: [precompF_ff], [precompF_split]).
    - Theorem [thm:ff-eso-equiv] ([thm_ff_eso_equiv]; split essential
      surjectivity from [lem:ff-eso], [ff_eso_split]).
    - Corollary [cor:Cat-ua] ([cor_Cat_ua], with [Univalence]): via
      [idtoPreCatIso] of exercise [xca:wildcat-of-precats]; between
      categories, isomorphisms of precategories and equivalences are
      logically equivalent propositions ([preiso_to_equiv],
      [equiv_to_preiso]).
    - Corollary [cor:cat-2-type] ([cor_cat_2_type], with
      [Univalence]); functors between categories form a 1-type
      ([Functor_isTrunc1]).
    - Theorem [thm:1types-are-groupoids], first part
      ([thm_1types_are_groupoids], with [Funext]; the inverse is
      [PathFun]); second part, [U^{≤1} ≃ Gpd] ([thm_1types_gpd], with
      [Univalence]; [GpdFun] and [cor:Cat-ua]).
    - Definition [def:flagged-cat] ([FlCat]).
    - Theorem [thm:flagged-cat-equiv] ([thm_flagged_cat_equiv], with
      [Univalence] and assuming that Rezk completions are categories,
      which [Rezk_isUnivalent] provides under [Univalence]; the inverse
      is [FlPre]).  NOTE for the book text: it says "sending a category
      [C]"; it should be a precategory.
    - Exercise [xca:Rezk-completion-1trunc] ([xca_Rezk_completion_1trunc],
      with [Univalence]): the path pregroupoid [TruncPathGrpd]; [Ob(η)]
      extends to an equivalence [‖A‖₁ ≃ Ob(L)] ([RT_f]).

    Left out (not formalized)
    - Remark [rem:chicken-or-egg] (informal). *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Types.Unit Truncations.Core Truncations.SeparatedTrunc Spaces.Nat.Core.
From SymmetryBook Require Export Cats.S06_Yoneda.

Local Open Scope uf_scope.

(** ** 6.7 Equivalences of categories *)

(** Definition [def:cat-equiv]: a left adjoint whose unit and counit are
    isomorphisms. *)
Definition isCatEquiv {C D : WildPreCat} (F : Functor C D) : Type
  := {adj : Adjunction C D & (ladj adj = F)
       × ((forall A, isIsoC (adj_unit adj A)) × (forall B, isIsoC (adj_counit adj B)))}.

Definition CatEquiv (C D : WildPreCat) : Type := {F : Functor C D & isCatEquiv F}.

(** Lemma [lem:cat-equiv-is-prop]. *)
Definition lem_cat_equiv_is_prop_stmt `{Funext} : Type
  := forall (C : Cat) (D : WildPreCat) (F : Functor (fst C) D), isProp (isCatEquiv F).

(** Proof: the pairs [(adj, ladj(adj) = F)] form a proposition
    ([cor_adj_unique]), and being an isomorphism is a proposition. *)
Definition lem_cat_equiv_is_prop `{Funext} : lem_cat_equiv_is_prop_stmt.
Proof.
  intros C D F.
  pose (R := fun adj : Adjunction (fst C) D =>
               (forall A, isIsoC (adj_unit adj A)) × (forall B, isIsoC (adj_counit adj B))).
  pose (g := fun x : {y : {adj : Adjunction (fst C) D & ladj adj = F} & R (fst y)} =>
               ((fst (fst x); (snd (fst x); snd x)) : isCatEquiv F)).
  assert (hS : isProp {y : {adj : Adjunction (fst C) D & ladj adj = F} & R (fst y)}).
  { refine (Sigma_isProp (cor_adj_unique C D F) (fun y => prod_isProp _ _));
      exact (Pi_isProp (fun _ => isIsoC_isProp _)). }
  intros e e'.
  exact (ap g (hS ((fst e; fst (snd e)); snd (snd e)) ((fst e'; fst (snd e')); snd (snd e')))).
Defined.

(** Lemma [lem:cat-equiv-ff]: an equivalence is fully faithful.  We use
    only that the unit is an isomorphism: [α(F f) = η_B ∘ f]. *)
Definition cat_equiv_ff {C D : WildPreCat} (F : Functor C D) (e : isCatEquiv F)
  : isFullyFaithful F.
Proof.
  destruct e as [adj [p [iu _]]]. destruct p.
  intros A B.
  pose (α := adjeqv adj A (fob (ladj adj) B)).
  refine (isEquiv_homotopic (fun f => eqinv (snd α) (adj_unit adj B ∘c f)) _ _ _).
  - intro f. refine (ap (eqinv (snd α)) _ @ eqinv_l (snd α) _).
    refine ((adjnat_pre adj f (idC _))^ @ ap (fst α) (lamC _)).
  - exact (comp_isEquiv (postcomp_isEquiv (iu B) A) (snd (Eqv_inv α))).
Defined.

(** Definition [def:functor-split-eso]. *)
Definition isSplitEso {C D : WildPreCat} (F : Functor C D) : Type
  := forall B : Ob D, {A : Ob C & IsoC (fob F A) B}.

Definition isEso {C D : WildPreCat} (F : Functor C D) : Type
  := forall B : Ob D, ptrunc {A : Ob C & IsoC (fob F A) B}.

(** Lemma [lem:equiv-precat-is-ff-split-eso]. *)
Definition lem_equiv_precat_is_ff_split_eso_stmt `{Funext} : Type
  := forall (C D : PreCat) (F : Functor (fst C) (fst D)),
       isEquiv (fun e : isCatEquiv F =>
                  ((cat_equiv_ff F e;
                    fun B => (fob (radj (fst e)) B;
                              trp (fun F1 : Functor (fst C) (fst D) =>
                                     IsoC (fob F1 (fob (radj (fst e)) B)) B)
                                  (fst (snd e))
                                  (adj_counit (fst e) B; snd (snd (snd e)) B)))
                   : isFullyFaithful F × isSplitEso F)).

(** Proof of [lem:equiv-precat-is-ff-split-eso].  The inverse
    ([fse_equiv]) takes [G(B) :≡ A_B] for the given [i_B : F(A_B) ≅ B]
    and [α(f) :≡ F⁻¹(i_B⁻¹ ∘ f)] ([fse_a]), extended to an adjunction by
    [lem:adj-via-repr]; its counit is [i_B] ([fse_counit_eq]) and its
    unit is an isomorphism since fully faithful functors reflect
    isomorphisms ([ff_reflect_iso]).  Conversely, an equivalence is
    determined by its adjunction ([catequiv_path]), and [adjeqv] agrees
    with [fse_a] ([adj_counit_factor]), so the two adjunctions are
    identified by the contractibility in [adj_via_repr]. *)
Section IsoLaws.
  Context {C : WildPreCat}.
  Definition iso_lr {A B : Ob C} (e : IsoC A B) : fst e ∘c invC e = idC B := snd (fst (snd e)).
  Definition iso_rl {A B : Ob C} (e : IsoC A B) : invC e ∘c fst e = idC A
    := ap (fun u => u ∘c fst e) (isIsoC_inv_eq (snd e))^ @ snd (snd (snd e)).
  Definition invC_isIso {A B : Ob C} (e : IsoC A B) : isIsoC (invC e)
    := ((fst e; iso_rl e); (fst e; iso_lr e)).
End IsoLaws.

(** A fully faithful functor reflects isomorphisms. *)
Definition ff_reflect_iso {C D : WildPreCat} (F : Functor C D) (ff : isFullyFaithful F)
  {A B : Ob C} (f : homC A B) (j : isIsoC (fmap F f)) : isIsoC f.
Proof.
  pose (g := eqinv (ff B A) (fst (fst j))).
  pose (h := eqinv (ff B A) (fst (snd j))).
  refine ((g; _); (h; _)).
  - refine ((eqinv_l (ff B B) _)^ @ ap (eqinv (ff B B)) _ @ eqinv_l (ff B B) _).
    refine (fcomp F g f @ ap (fun u => fmap F f ∘c u) (eqinv_r (ff B A) _) @ _).
    exact (snd (fst j) @ (fid F B)^).
  - refine ((eqinv_l (ff A A) _)^ @ ap (eqinv (ff A A)) _ @ eqinv_l (ff A A) _).
    refine (fcomp F f h @ ap (fun u => u ∘c fmap F f) (eqinv_r (ff B A) _) @ _).
    exact (snd (snd j) @ (fid F A)^).
Defined.

Section FFSplitEso.

  Context `{Funext} {C D : WildPreCat} (F : Functor C D) (ff : isFullyFaithful F)
    (s : isSplitEso F).

  Local Notation G0 B := (fst (s B)).
  Local Notation i B := (snd (s B)).
  Local Notation Finv A A' := (eqinv (ff A A')).

  Definition fse_af (B : Ob D) (A : Ob C) (f : homC (fob F A) B) : homC A (G0 B)
    := Finv A (G0 B) (invC (i B) ∘c f).

  Definition fse_ag (B : Ob D) (A : Ob C) (k : homC A (G0 B)) : homC (fob F A) B
    := fst (i B) ∘c fmap F k.

  Definition fse_a (B : Ob D) (A : Ob C) : homC (fob F A) B ≃ homC A (G0 B).
  Proof.
    refine (mkEqv (fse_af B A) (fse_ag B A) _ _).
    - intro f. unfold fse_ag, fse_af.
      refine (ap (fun u => fst (i B) ∘c u) (eqinv_r (ff A (G0 B)) _) @ alphaC _ _ _ @ _).
      exact (ap (fun u => u ∘c f) (iso_lr (i B)) @ lamC f).
    - intro k. unfold fse_ag, fse_af.
      refine (ap (Finv A (G0 B)) (alphaC _ _ _ @ ap (fun u => u ∘c fmap F k) (iso_rl (i B))
                                  @ lamC _) @ _).
      exact (eqinv_l (ff A (G0 B)) k).
  Defined.

  Definition fse_an (B : Ob D) (A A' : Ob C) (h : homC A' A) (f : homC (fob F A) B)
    : fst (fse_a B A') (f ∘c fmap F h) = fst (fse_a B A) f ∘c h.
  Proof.
    cbn. unfold fse_af.
    refine (ap (Finv A' (G0 B)) (alphaC (fmap F h) f (invC (i B))) @ _).
    refine (ap (Finv A' (G0 B)) (ap (fun u => u ∘c fmap F h) (eqinv_r (ff A (G0 B)) _)^) @ _).
    refine (ap (Finv A' (G0 B)) (fcomp F h _)^ @ _).
    exact (eqinv_l (ff A' (G0 B)) _).
  Defined.

  Definition fse_adj : Adjunction C D := avr_adj C D F (fun B => G0 B) fse_a fse_an.

  Definition fse_counit_eq (B : Ob D) : adj_counit fse_adj B = fst (i B)
    := ap (fun u => fst (i B) ∘c u) (fid F (G0 B)) @ rhoC _.

  Definition fse_unit_iso (A : Ob C) : isIsoC (adj_unit fse_adj A).
  Proof.
    apply (ff_reflect_iso F ff).
    refine (trp isIsoC ((rhoC _)^ @ (eqinv_r (ff A (G0 (fob F A))) _)^)
              (invC_isIso (i (fob F A)))).
  Defined.

  Definition fse_counit_iso (B : Ob D) : isIsoC (adj_counit fse_adj B)
    := trp isIsoC (fse_counit_eq B)^ (snd (i B)).

  Definition fse_equiv : isCatEquiv F
    := (fse_adj; (refl; (fse_unit_iso; fse_counit_iso))).

End FFSplitEso.

(** Equivalences with the same underlying adjunction are equal. *)
Definition catequiv_path `{Funext} {C D : WildPreCat} {F : Functor C D} (e e' : isCatEquiv F)
  (P : ((fst e; fst (snd e)) : {adj : Adjunction C D & ladj adj = F}) = (fst e'; fst (snd e')))
  : e = e'.
Proof.
  pose (R := fun adj : Adjunction C D =>
               (forall A, isIsoC (adj_unit adj A)) × (forall B, isIsoC (adj_counit adj B))).
  assert (Gen : forall y y' : {adj : Adjunction C D & ladj adj = F}, y = y' ->
            forall (r : R (fst y)) (r' : R (fst y')),
              ((fst y; (snd y; r)) : isCatEquiv F) = (fst y'; (snd y'; r'))).
  { intros y y' Q. destruct Q. intros r r'.
    exact (ap (fun r0 => ((fst y; (snd y; r0)) : isCatEquiv F))
              (prod_isProp (Pi_isProp (fun _ => isIsoC_isProp _))
                           (Pi_isProp (fun _ => isIsoC_isProp _)) r r')). }
  exact (Gen _ _ P (snd (snd e)) (snd (snd e'))).
Defined.

(** [ε ∘ F(α f) = f]. *)
Definition adj_counit_factor {C D : WildPreCat} (adj : Adjunction C D) {A : Ob C} {B : Ob D}
  (f : homC (fob (ladj adj) A) B)
  : adj_counit adj B ∘c fmap (ladj adj) (fst (adjeqv adj A B) f) = f.
Proof.
  refine ((eqinv_l (snd (adjeqv adj A B)) _)^ @ ap (eqinv (snd (adjeqv adj A B))) _
          @ eqinv_l (snd (adjeqv adj A B)) f).
  refine (adjnat_pre adj (fst (adjeqv adj A B) f) (adj_counit adj B) @ _).
  exact (ap (fun u => u ∘c _) (eqinv_r (snd (adjeqv adj (fob (radj adj) B) B)) _) @ lamC _).
Defined.

Definition lem_equiv_precat_is_ff_split_eso `{Funext} : lem_equiv_precat_is_ff_split_eso_stmt.
Proof.
  intros C D F.
  refine (iso_to_isEquiv _ (fun x => fse_equiv F (fst x) (snd x)) _ _).
  - intros [adj [p [iu ic]]]. destruct p. apply catequiv_path. cbn.
    pose (ffe := cat_equiv_ff (ladj adj) (adj; (refl; (iu; ic)))).
    pose (se := fun B => (fob (radj adj) B; (adj_counit adj B; ic B))
                         : {A : Ob (fst C) & IsoC (fob (ladj adj) A) B}).
    assert (r : forall A B, adjeqv adj A B = fse_a (ladj adj) ffe se B A).
    { intros A B. apply path_Eqv. apply ptw_inv; intro f. cbn. unfold fse_af.
      refine ((eqinv_l (ffe A (fob (radj adj) B)) _)^ @ ap (eqinv (ffe A (fob (radj adj) B))) _).
      refine ((lamC _)^ @ ap (fun u => u ∘c _) (iso_rl (snd (se B)))^ @ (alphaC _ _ _)^ @ _).
      exact (ap (fun u => invC (snd (se B)) ∘c u) (adj_counit_factor adj f)). }
    pose (x1 := (fse_adj (ladj adj) ffe se; (refl; (refl; fun A B => refl)))
                : AdjExt (fst C) (fst D) (ladj adj) (fun B => fob (radj adj) B)
                    (fse_a (ladj adj) ffe se)).
    pose (x2 := (adj; (refl; (refl; r)))
                : AdjExt (fst C) (fst D) (ladj adj) (fun B => fob (radj adj) B)
                    (fse_a (ladj adj) ffe se)).
    exact (ap (fun x => ((fst x; fst (snd x)) : {adj0 : Adjunction _ _ & ladj adj0 = ladj adj}))
              (isContr_isProp' (adj_via_repr (fst C) (fst D) (snd C) (ladj adj) _ _
                                  (fse_an (ladj adj) ffe se)) x1 x2)).
  - intros [ff s].
    refine (ap011 (fun x y => (x; y) : isFullyFaithful F × isSplitEso F)
              (Pi_isProp (fun A => Pi_isProp (fun B => isEquiv_isProp _)) _ ff) _).
    apply ptw_inv; intro B.
    cbn. exact (ap (fun x => (fst (s B); x) : {A : Ob (fst C) & IsoC (fob F A) B})
                   (@path_IsoC _ _ _ _ (_; _) (snd (s B)) (fse_counit_eq F ff s B))).
Defined.

(** Lemma [lem:ff-eso]. *)
Definition lem_ff_eso_stmt `{Funext} : Type
  := forall (C : Cat) (D : WildPreCat) (F : Functor (fst C) D),
       isFullyFaithful F -> forall B : Ob D, isProp {A : Ob (fst C) & IsoC (fob F A) B}.

(** Postcomposition with an isomorphism is an equivalence on
    isomorphisms. *)
Definition IsoC_postcomp_isEquiv `{Funext} {D : WildPreCat} {X Y Y' : Ob D} (j : IsoC Y Y')
  : isEquiv (fun e : IsoC X Y => IsoC_comp j e).
Proof.
  refine (iso_to_isEquiv _ (IsoC_comp (IsoC_inv j)) _ _).
  - intro e. apply path_IsoC.
    destruct j as [f [[g s] [h r]]], e as [k ik]. cbn.
    refine (alphaC _ _ _ @ ap (fun u => u ∘c k) _ @ lamC k).
    exact (ap (fun u => u ∘c f) (isIsoC_inv_eq ((g; s); (h; r)))^ @ r).
  - intro e. apply path_IsoC.
    destruct j as [f [[g s] [h r]]], e as [k ik]. cbn.
    exact (alphaC _ _ _ @ ap (fun u => u ∘c k) s @ lamC k).
Defined.

(** If [C] is a category and [F] is fully faithful, then the type of
    pairs [(A, F(A) ≅ B)] is equivalent to a singleton as soon as it is
    inhabited. *)
Definition lem_ff_eso `{Funext} : lem_ff_eso_stmt.
Proof.
  intros [C [pc uC]] D F ff B [A0 i0] y.
  refine (isContr_isProp' (isContr_Eqv (tot (fun A (p : A = A0) =>
                                              IsoC_comp i0 (fmap_iso F (idtoiso p)));
                                        tot_isEquiv _ (fun A => _))
                                       (singleton_contr' A0)) _ y).
  exact (comp_isEquiv (comp_isEquiv (uC A A0) (fmap_iso_isEquiv F ff A A0))
           (IsoC_postcomp_isEquiv i0)).
Defined.

(** Theorem [thm:ff-eso-equiv]. *)
Definition thm_ff_eso_equiv_stmt `{Funext} : Type
  := forall (C : Cat) (D : PreCat),
       isInj (fun e : CatEquiv (fst C) (fst D) => fst e)
       × (forall F : Functor (fst C) (fst D),
            ptrunc (isCatEquiv F) <-> isFullyFaithful F × isEso F).

(** For [C] a category, a fully faithful essentially surjective functor
    is split essentially surjective ([lem:ff-eso]). *)
Definition ff_eso_split `{Funext} (C : Cat) {D : WildPreCat} (F : Functor (fst C) D)
  (ff : isFullyFaithful F) (eso : isEso F) : isSplitEso F
  := fun B => ptrunc_rec (lem_ff_eso C D F ff B) idmap (eso B).

Definition thm_ff_eso_equiv `{Funext} : thm_ff_eso_equiv_stmt.
Proof.
  intros C D. refine (_; _).
  - intros F [[F1 x] p] [[F2 x'] p']. cbn in p, p'. destruct p, p'.
    exact (ap (fun y => (((F; y) : CatEquiv _ _); refl)) (lem_cat_equiv_is_prop C (fst D) F x x')).
  - intro F. split.
    + refine (ptrunc_rec (prod_isProp (Pi_isProp (fun A => Pi_isProp (fun B => isEquiv_isProp _)))
                                      (Pi_isProp (fun B => ptrunc_isProp))) _).
      intro e. refine (cat_equiv_ff F e; fun B => trunc _).
      exact (fob (radj (fst e)) B;
             trp (fun F1 : Functor (fst C) (fst D) => IsoC (fob F1 (fob (radj (fst e)) B)) B)
                 (fst (snd e)) (adj_counit (fst e) B; snd (snd (snd e)) B)).
    + intros [ff eso]. exact (trunc (fse_equiv F ff (ff_eso_split C F ff eso))).
Defined.

(** Corollary [cor:Cat-ua]. *)
Definition idAdj (C : WildPreCat) : Adjunction C C
  := Build_Adjunction C C (idF C) (idF C) (fun A B => idEqv _) (fun A' A B B' h f g => refl).

Definition idCatEquiv (C : WildPreCat) : CatEquiv C C.
Proof.
  refine (idF C; (idAdj C; (refl; ((fun A => id_isIsoC A); fun B => _)))).
  exact (trp isIsoC (eqinv_r (snd (idEqv (homC B B))) (idC B))^ (id_isIsoC B)).
Defined.

Definition idtoCatEquiv {C D : WildPreCat} (p : C = D) : CatEquiv C D
  := match p with refl => idCatEquiv C end.

Definition cor_Cat_ua_stmt : Type
  := forall C D : Cat, isEquiv (fun p : C = D => idtoCatEquiv (ap fst p)).

(** Corollary [cor:cat-2-type]. *)
Definition cor_cat_2_type_stmt : Type := IsTrunc 2 Cat.

(** Corollary [cor:Cat-ua].  Through [idtoPreCatIso] (exercise
    [xca:wildcat-of-precats]): for categories, isomorphisms of
    precategories are the same as equivalences ([preiso_to_equiv],
    [equiv_to_preiso]), both being propositions. *)
Definition toPreCat (C : Cat) : PreCat := (fst C; fst (snd C)).

Definition preiso_to_equiv `{Funext} {C D : PreCat} (F : Functor (fst C) (fst D))
  (i : isPreCatIso F) : isCatEquiv F
  := fse_equiv F (snd i) (fun B => (eqinv (fst i) B; idtoiso (eqinv_r (fst i) B))).

Definition equiv_to_preiso `{Funext} (C D : Cat) (F : Functor (fst C) (fst D))
  (e : isCatEquiv F) : isPreCatIso (C := toPreCat C) (D := toPreCat D) F.
Proof.
  refine ((_ : isEquiv (fob F)); cat_equiv_ff F e).
  pose (uD := snd (snd D)).
  apply inj_surj_isEquiv.
  - intro B.
    refine (isProp_Eqv (Eqv_inv (tot (fun A (p : B = fob F A) => idtoiso p^);
                                 tot_isEquiv _ (fun A => comp_isEquiv _ (uD (fob F A) B))))
                       (lem_ff_eso C (fst D) F (cat_equiv_ff F e) B)).
    exact (iso_to_isEquiv (fun p : B = fob F A => p^) (fun p => p^) inv_V inv_V).
  - intro B. apply trunc.
    refine (fob (radj (fst e)) B; (eqinv (uD _ B) _)^).
    exact (trp (fun F1 : Functor (fst C) (fst D) => IsoC (fob F1 (fob (radj (fst e)) B)) B)
               (fst (snd e)) (adj_counit (fst e) B; snd (snd (snd e)) B)).
Defined.

Definition Cat_ua `{Univalence} (C D : Cat)
  : isEquiv (fun p : C = D => idtoCatEquiv (ap fst p)).
Proof.
  pose (E1 := subtype_paths_eqv (Q := fun X : WildPreCat => isPreCat X × isUnivalent X)
                (fun X => prod_isProp (Pi_isProp (fun A => Pi_isProp (fun B => isSet_isProp _)))
                            (Pi_isProp (fun A => Pi_isProp (fun B => isEquiv_isProp _)))) C D).
  pose (E2 := subtype_paths_eqv (Q := isPreCat)
                (fun X => Pi_isProp (fun A => Pi_isProp (fun B => isSet_isProp _)))
                (toPreCat C) (toPreCat D)).
  pose (h := tot (fun F (i : isPreCatIso (C := toPreCat C) (D := toPreCat D) F) =>
                    preiso_to_equiv F i)).
  assert (th : isEquiv h).
  { refine (tot_isEquiv _ (fun F => iso_to_isEquiv _ (equiv_to_preiso C D F) _ _)).
    - intro i. exact (@isPreCatIso_isProp _ (toPreCat C) (toPreCat D) F _ _).
    - intro e. exact (lem_cat_equiv_is_prop C (fst D) F _ _). }
  refine (isEquiv_homotopic (fun p => h (idtoPreCatIso (eqinv (snd E2) (fst E1 p)))) _ _ _).
  - intro p. destruct p.
    refine (ap (fun q => h (idtoPreCatIso q)) (eqinv_l (snd E2) refl) @ _).
    exact (ap (fun y => ((idF (fst C); y) : CatEquiv _ _)) (lem_cat_equiv_is_prop C (fst C) _ _ _)).
  - exact (comp_isEquiv (comp_isEquiv (comp_isEquiv (snd E1) (eqinv_isEquiv (snd E2)))
                                      (idtoPreCatIso_isEquiv _ _)) th).
Defined.

Definition cor_Cat_ua `{Univalence} : cor_Cat_ua_stmt := Cat_ua.

(** Corollary [cor:cat-2-type]: functors between categories form a
    1-type ([Functor_isTrunc1]), and so do equivalences. *)
Definition issig_Functor (C D : WildPreCat)
  : {fo : Ob C -> Ob D &
     {fm : forall A B, homC A B -> homC (fo A) (fo B) &
      {fi : forall A, fm A A (idC A) = idC (fo A) &
       forall A B E (f : homC A B) (g : homC B E), fm A E (g ∘c f) = fm B E g ∘c fm A B f}}}
    <~> Functor C D
  := ltac:(issig).

Definition Functor_isTrunc1 `{Funext} (C D : Cat) : IsTrunc 1 (Functor (fst C) (fst D)).
Proof.
  pose (obD := isGrpd_IsTrunc (Ob_isGrpd D)).
  pose (hD := fun A B => isSet_IsHSet (fst (snd D) A B)).
  exact (istrunc_equiv_istrunc _ (issig_Functor (fst C) (fst D))).
Defined.

Definition cor_cat_2_type `{Univalence} : cor_cat_2_type_stmt.
Proof.
  apply istrunc_S. intros C D.
  pose (hF := Functor_isTrunc1 C D).
  pose (hE := fun F : Functor (fst C) (fst D) =>
                isProp_IsHProp (lem_cat_equiv_is_prop C (fst D) F)).
  exact (istrunc_equiv_istrunc _ (Equiv_of_Eqv (Eqv_inv (_; Cat_ua C D)))).
Defined.

(** Definition [def:we-cat]. *)
Definition isWeakEquiv {C D : WildPreCat} (F : Functor C D) : Type
  := isFullyFaithful F × isEso F.

(** Lemma [lem:precomp-equiv-cat]. *)
Definition precompF `{Funext} {C D : WildPreCat} (E : WildPreCat) (pe : isPreCat E)
  (K : Functor C D) : Functor (FunctorCat D E pe) (FunctorCat C E pe)
  := Build_Functor (FunctorCat D E pe) (FunctorCat C E pe) (fun G => compF G K)
       (fun G G' a => ((fun A => fst a (fob K A)); fun A B f => snd a _ _ (fmap K f)))
       (fun G => refl) (fun G G' G'' a b => refl).

Definition lem_precomp_equiv_cat_stmt `{Funext} : Type
  := forall (C D : PreCat) (E : Cat) (K : Functor (fst C) (fst D)),
       isWeakEquiv K -> isCatEquiv (precompF (fst E) (fst (snd E)) K).

Definition iso_cancel_r {C : WildPreCat} {A B X : Ob C} {f : homC A B} (i : isIsoC f)
  {x y : homC B X} (p : x ∘c f = y ∘c f) : x = y
  := (eqinv_l (precomp_isEquiv i X) x)^ @ ap (eqinv (precomp_isEquiv i X)) p
     @ eqinv_l (precomp_isEquiv i X) y.

(** The proof of lemma [lem:precomp-equiv-cat] follows [HoTT book,
    Lemmas 9.9.1–9.9.4]: [- ∘ H] is fully faithful ([precompF_ff]):
    for [γ : GH ⇒ G'H], the arrows [g] with [g ∘ G(k) = G'(k) ∘ γ_a] for
    all [k : H(a) ≅ b] form a contractible type ([PffT_isContr]); and it
    is split essentially surjective ([precompF_split]): [G(b)] is the
    center of the contractible type of compatible families of
    isomorphisms [F(a) ≅ c] indexed by [k : H(a) ≅ b] ([PeX_isContr],
    using that [E] is a category), and similarly for arrows
    ([PeY_isContr]). *)
Section PrecompFF.

  Context `{Funext} {C D E : WildPreCat} (pe : isPreCat E) (K : Functor C D)
    (ff : isFullyFaithful K) (eso : isEso K) (G G' : Functor D E)
    (γ : NatTrans (compF G K) (compF G' K)).

  (** [g ∘ G(k) = G'(k) ∘ γ_a] for one isomorphism [k : K(a₀) ≅ b]
      implies it for all arrows [u : K(a) → b]. *)
  Definition pff_ext {b : Ob D} (g : homC (fob G b) (fob G' b)) {a0 : Ob C}
    (k0 : IsoC (fob K a0) b) (c0 : g ∘c fmap G (fst k0) = fmap G' (fst k0) ∘c fst γ a0)
    {a : Ob C} (u : homC (fob K a) b) : g ∘c fmap G u = fmap G' u ∘c fst γ a.
  Proof.
    pose (h := eqinv (ff a a0) (invC k0 ∘c u)).
    assert (eu : fst k0 ∘c fmap K h = u).
    { refine (ap (fun v => fst k0 ∘c v) (eqinv_r (ff a a0) _) @ alphaC _ _ _ @ _).
      exact (ap (fun v => v ∘c u) (iso_lr k0) @ lamC u). }
    clearbody h. destruct eu.
    refine (ap (fun v => g ∘c v) (fcomp G _ _) @ alphaC _ _ _ @ _).
    refine (ap (fun v => v ∘c _) c0 @ (alphaC _ _ _)^ @ _).
    refine (ap (fun v => fmap G' (fst k0) ∘c v) (snd γ a a0 h)^ @ alphaC _ _ _ @ _).
    exact (ap (fun v => v ∘c fst γ a) (fcomp G' _ _)^).
  Defined.

  Definition PffT (b : Ob D) : Type
    := {g : homC (fob G b) (fob G' b) &
         forall a (k : IsoC (fob K a) b), g ∘c fmap G (fst k) = fmap G' (fst k) ∘c fst γ a}.

  Definition PffT_isSet (b : Ob D) : isSet (PffT b)
    := Sigma_isSet (pe _ _) (fun g => prop_is_set (Pi_isProp (fun a => Pi_isProp (fun k =>
                                                     pe _ _ _ _)))).

  Definition PffT_isContr (b : Ob D) : isContr (PffT b).
  Proof.
    refine (ptrunc_rec (isContr_isProp _) _ (eso b)). intros [a0 k0].
    pose (g0 := (fmap G' (fst k0) ∘c fst γ a0) ∘c fmap G (invC k0)).
    assert (c0 : g0 ∘c fmap G (fst k0) = fmap G' (fst k0) ∘c fst γ a0).
    { refine ((alphaC _ _ _)^ @ ap (fun v => _ ∘c v) (fcomp G _ _)^ @ _).
      exact (ap (fun v => _ ∘c fmap G v) (iso_rl k0) @ ap (fun v => _ ∘c v) (fid G _)
             @ rhoC _). }
    refine ((g0; fun a k => pff_ext g0 k0 c0 (fst k)); _).
    intros [g c]. apply (path_sigma_prop (fun g => Pi_isProp (fun a => Pi_isProp (fun k =>
                                                     pe _ _ _ _)))).
    exact (iso_cancel_r (fmap_isIso G (snd k0)) (c0 @ (c a0 k0)^)).
  Defined.

  Definition pff_d (b : Ob D) : homC (fob G b) (fob G' b) := fst (fst (PffT_isContr b)).

  Definition pff_d_ext (b : Ob D) {a : Ob C} (u : homC (fob K a) b)
    : pff_d b ∘c fmap G u = fmap G' u ∘c fst γ a.
  Proof.
    refine (ptrunc_rec (pe _ _ _ _) _ (eso b)). intros [a0 k0].
    exact (pff_ext (pff_d b) k0 (snd (fst (PffT_isContr b)) a0 k0) u).
  Defined.

  Definition pff_nat : NatTrans G G'.
  Proof.
    refine (pff_d; fun b b' f => _).
    refine (ptrunc_rec (pe _ _ _ _) _ (eso b)). intros [a k].
    apply (iso_cancel_r (fmap_isIso G (snd k))).
    refine ((alphaC _ _ _)^ @ ap (fun v => fmap G' f ∘c v) (pff_d_ext b (fst k)) @ _).
    refine (alphaC _ _ _ @ ap (fun v => v ∘c _) (fcomp G' _ _)^ @ (pff_d_ext b' _)^ @ _).
    exact (ap (fun v => _ ∘c v) (fcomp G _ _) @ alphaC _ _ _).
  Defined.

End PrecompFF.

Definition precompF_ff `{Funext} {C D E : WildPreCat} (pe : isPreCat E) (K : Functor C D)
  (ff : isFullyFaithful K) (eso : isEso K) : isFullyFaithful (precompF E pe K).
Proof.
  intros G G'. refine (iso_to_isEquiv _ (pff_nat pe K ff eso G G') _ _).
  - intro δ. apply (path_NatTrans pe). intro b.
    exact (ap fst (snd (PffT_isContr pe K ff eso G G' (fmap (precompF E pe K) δ) b)
                       (fst δ b; fun a k => (snd δ _ _ (fst k))^))).
  - intro γ. apply (path_NatTrans pe). intro a.
    refine ((rhoC _)^ @ ap (fun v => _ ∘c v) (fid G _)^ @ _).
    refine (pff_d_ext pe K ff eso G G' γ (fob K a) (idC _) @ _).
    exact (ap (fun v => v ∘c _) (fid G' _) @ lamC _).
Defined.

Definition comp_isIsoC {C : WildPreCat} {A B X : Ob C} {f : homC A B} {g : homC B X}
  (i : isIsoC f) (j : isIsoC g) : isIsoC (g ∘c f).
Proof.
  destruct i as [[f1 s] [f2 r]], j as [[g1 s'] [g2 r']].
  exact (snd (IsoC_comp (g; ((g1; s'); (g2; r'))) (f; ((f1; s); (f2; r))))).
Defined.

Definition iso_cancel_l {C : WildPreCat} {A B X : Ob C} {f : homC A B} (i : isIsoC f)
  {x y : homC X A} (p : f ∘c x = f ∘c y) : x = y
  := (eqinv_l (postcomp_isEquiv i X) x)^ @ ap (eqinv (postcomp_isEquiv i X)) p
     @ eqinv_l (postcomp_isEquiv i X) y.

Section FFLift.

  Context {C D : WildPreCat} (K : Functor C D) (ff : isFullyFaithful K).

  Definition ff_inj {a a' : Ob C} {f f' : homC a a'} (p : fmap K f = fmap K f') : f = f'
    := (eqinv_l (ff a a') f)^ @ ap (eqinv (ff a a')) p @ eqinv_l (ff a a') f'.

  (** The arrow [l : a → a'] with [k' ∘ K(l) = u]. *)
  Definition ff_lift {a a' : Ob C} {b : Ob D} (k' : IsoC (fob K a') b) (u : homC (fob K a) b)
    : homC a a'
    := eqinv (ff a a') (invC k' ∘c u).

  Definition ff_lift_spec {a a' : Ob C} {b : Ob D} (k' : IsoC (fob K a') b)
    (u : homC (fob K a) b) : fst k' ∘c fmap K (ff_lift k' u) = u.
  Proof.
    refine (ap (fun v => fst k' ∘c v) (eqinv_r (ff a a') _) @ alphaC _ _ _ @ _).
    exact (ap (fun v => v ∘c u) (iso_lr k') @ lamC u).
  Defined.

  (** Arrows [f, f'] with [k' ∘ K(f) = k' ∘ K(f')] are equal. *)
  Definition ff_lift_unique {a a' : Ob C} {b : Ob D} (k' : IsoC (fob K a') b)
    {f f' : homC a a'} (p : fst k' ∘c fmap K f = fst k' ∘c fmap K f') : f = f'
    := ff_inj (iso_cancel_l (snd k') p).

  Definition ff_lift_isIso {a a' : Ob C} {b : Ob D} (k' : IsoC (fob K a') b)
    (k : IsoC (fob K a) b) : isIsoC (ff_lift k' (fst k))
    := ff_reflect_iso K ff _ (trp isIsoC (eqinv_r (ff a a') _)^
                                (comp_isIsoC (snd k) (invC_isIso k'))).

End FFLift.

Section PrecompEso.

  Context `{Funext} {C D : WildPreCat} (E : Cat) (K : Functor C D)
    (ff : isFullyFaithful K) (eso : isEso K) (F : Functor C (fst E)).

  Local Notation pe := (fst (snd E)).
  Local Notation uE := (snd (snd E)).

  (** The cones under [b]: compatible families of isomorphisms
      [h_{a,k} : F(a) ≅ c] for [k : K(a) ≅ b]. *)
  Definition PeH (b : Ob D) (c : Ob (fst E)) : Type
    := {h : forall a, IsoC (fob K a) b -> IsoC (fob F a) c &
         forall a a' (k : IsoC (fob K a) b) (k' : IsoC (fob K a') b) (f : homC a a'),
           fst k' ∘c fmap K f = fst k -> fst (h a' k') ∘c fmap F f = fst (h a k)}.

  Definition PeH_cond_isProp (b : Ob D) (c : Ob (fst E))
    (h : forall a, IsoC (fob K a) b -> IsoC (fob F a) c)
    : isProp (forall a a' (k : IsoC (fob K a) b) (k' : IsoC (fob K a') b) (f : homC a a'),
                fst k' ∘c fmap K f = fst k -> fst (h a' k') ∘c fmap F f = fst (h a k))
    := Pi_isProp (fun a => Pi_isProp (fun a' => Pi_isProp (fun k => Pi_isProp (fun k' =>
         Pi_isProp (fun f => Pi_isProp (fun _ => pe _ _ _ _)))))).

  Section FixedLift.

    Context {b : Ob D} {a0 : Ob C} (k0 : IsoC (fob K a0) b).

    Definition peh_of {c : Ob (fst E)} (e : IsoC (fob F a0) c) : PeH b c.
    Proof.
      refine ((fun a k => (fst e ∘c fmap F (ff_lift K ff k0 (fst k));
                           comp_isIsoC (fmap_isIso F (ff_lift_isIso K ff k0 k)) (snd e)));
              fun a a' k k' f r => _).
      cbn. refine ((alphaC _ _ _)^ @ ap (fun v => fst e ∘c v) ((fcomp F _ _)^ @ ap (fmap F) _)).
      apply (ff_lift_unique K ff k0).
      refine (ap (fun v => _ ∘c v) (fcomp K _ _) @ alphaC _ _ _ @ _).
      refine (ap (fun v => v ∘c _) (ff_lift_spec K ff k0 (fst k')) @ r @ _).
      exact (ff_lift_spec K ff k0 (fst k))^.
    Defined.

    Definition ff_lift_id : ff_lift K ff k0 (fst k0) = idC a0.
    Proof.
      apply (ff_lift_unique K ff k0).
      exact (ff_lift_spec K ff k0 (fst k0) @ (rhoC _)^ @ ap (fun v => _ ∘c v) (fid K a0)^).
    Defined.

    Definition peh_eqv (c : Ob (fst E)) : PeH b c ≃ IsoC (fob F a0) c.
    Proof.
      refine (mkEqv (fun x => fst x a0 k0) peh_of _ _).
      - intros [h φ]. apply (path_sigma_prop (PeH_cond_isProp b c)).
        apply ptw_inv; intro a. apply ptw_inv; intro k. apply path_IsoC.
        exact (φ a a0 k k0 _ (ff_lift_spec K ff k0 (fst k))).
      - intro e. apply path_IsoC. cbn.
        exact (ap (fun v => fst e ∘c fmap F v) ff_lift_id @ ap (fun v => fst e ∘c v) (fid F a0)
               @ rhoC _).
    Defined.

  End FixedLift.

  Definition PeX_isContr (b : Ob D) : isContr {c : Ob (fst E) & PeH b c}.
  Proof.
    refine (ptrunc_rec (isContr_isProp _) _ (eso b)). intros [a0 k0].
    refine (isContr_Eqv (Eqv_inv (tot (fun c => fst (peh_eqv k0 c));
                                  tot_isEquiv _ (fun c => snd (peh_eqv k0 c)))) _).
    exact (isContr_Eqv (tot (fun c (p : fob F a0 = c) => idtoiso p);
                        tot_isEquiv _ (fun c => uE _ c)) (singleton_contr _)).
  Defined.

  Definition Gob (b : Ob D) : Ob (fst E) := fst (fst (PeX_isContr b)).

  Definition Gh (b : Ob D) : forall a, IsoC (fob K a) b -> IsoC (fob F a) (Gob b)
    := fst (snd (fst (PeX_isContr b))).

  Definition Gφ (b : Ob D) {a a'} (k : IsoC (fob K a) b) (k' : IsoC (fob K a') b)
    (f : homC a a') (r : fst k' ∘c fmap K f = fst k)
    : fst (Gh b a' k') ∘c fmap F f = fst (Gh b a k)
    := snd (snd (fst (PeX_isContr b))) a a' k k' f r.

End PrecompEso.

Section PrecompEsoMap.

  Context `{Funext} {C D : WildPreCat} (E : Cat) (K : Functor C D)
    (ff : isFullyFaithful K) (eso : isEso K) (F : Functor C (fst E)).

  Local Notation pe := (fst (snd E)).
  Local Notation G0 := (Gob E K ff eso F).
  Local Notation h := (Gh E K ff eso F).
  Local Notation φ := (Gφ E K ff eso F).

  Definition PeY {b b' : Ob D} (g : homC b b') (m : homC (G0 b) (G0 b')) : Type
    := forall a (k : IsoC (fob K a) b) a' (k' : IsoC (fob K a') b') (f : homC a a'),
         fst k' ∘c fmap K f = g ∘c fst k -> m ∘c fst (h b a k) = fst (h b' a' k') ∘c fmap F f.

  Definition PeY_isProp {b b' : Ob D} (g : homC b b') (m : homC (G0 b) (G0 b'))
    : isProp (PeY g m)
    := Pi_isProp (fun a => Pi_isProp (fun k => Pi_isProp (fun a' => Pi_isProp (fun k' =>
         Pi_isProp (fun f => Pi_isProp (fun _ => pe _ _ _ _)))))).

  Definition pey_ext {b b' : Ob D} (g : homC b b') (m : homC (G0 b) (G0 b'))
    {a a'} (k : IsoC (fob K a) b) (k' : IsoC (fob K a') b') (f0 : homC a a')
    (r0 : fst k' ∘c fmap K f0 = g ∘c fst k)
    (c0 : m ∘c fst (h b a k) = fst (h b' a' k') ∘c fmap F f0) : PeY g m.
  Proof.
    intros a1 k1 a1' k1' f1 r1.
    pose (p := ff_lift K ff k (fst k1)). pose (q := ff_lift K ff k' (fst k1')).
    assert (e : f0 ∘c p = q ∘c f1).
    { apply (ff_lift_unique K ff k').
      refine (ap (fun v => _ ∘c v) (fcomp K _ _) @ alphaC _ _ _ @ ap (fun v => v ∘c _) r0 @ _).
      refine ((alphaC _ _ _)^ @ ap (fun v => g ∘c v) (ff_lift_spec K ff k (fst k1)) @ _).
      refine (r1^ @ _).
      refine (ap (fun v => v ∘c _) (ff_lift_spec K ff k' (fst k1'))^ @ (alphaC _ _ _)^ @ _).
      exact (ap (fun v => _ ∘c v) (fcomp K _ _)^). }
    refine (ap (fun v => m ∘c v) (φ b k1 k p (ff_lift_spec K ff k (fst k1)))^ @ _).
    refine (alphaC _ _ _ @ ap (fun v => v ∘c _) c0 @ (alphaC _ _ _)^ @ _).
    refine (ap (fun v => _ ∘c v) ((fcomp F _ _)^ @ ap (fmap F) e @ fcomp F _ _) @ _).
    exact (alphaC _ _ _ @ ap (fun v => v ∘c _) (φ b' k1' k' q (ff_lift_spec K ff k' (fst k1')))).
  Defined.

  Definition PeY_isContr {b b' : Ob D} (g : homC b b') : isContr {m : homC (G0 b) (G0 b') & PeY g m}.
  Proof.
    refine (ptrunc_rec (isContr_isProp _) _ (eso b)). intros [a k].
    refine (ptrunc_rec (isContr_isProp _) _ (eso b')). intros [a' k'].
    pose (f0 := ff_lift K ff k' (g ∘c fst k)).
    pose (m0 := (fst (h b' a' k') ∘c fmap F f0) ∘c invC (h b a k)).
    assert (c0 : m0 ∘c fst (h b a k) = fst (h b' a' k') ∘c fmap F f0).
    { exact ((alphaC _ _ _)^ @ ap (fun v => _ ∘c v) (iso_rl (h b a k)) @ rhoC _). }
    refine ((m0; pey_ext g m0 k k' f0 (ff_lift_spec K ff k' _) c0); _).
    intros [m cm]. apply (path_sigma_prop (PeY_isProp g)).
    exact (iso_cancel_r (snd (h b a k)) (c0 @ (cm a k a' k' f0 (ff_lift_spec K ff k' _))^)).
  Defined.

  Definition Gmap {b b' : Ob D} (g : homC b b') : homC (G0 b) (G0 b')
    := fst (fst (PeY_isContr g)).

  Definition Gmap_spec {b b' : Ob D} (g : homC b b') : PeY g (Gmap g)
    := snd (fst (PeY_isContr g)).

  Definition Gfid (b : Ob D) : Gmap (idC b) = idC (G0 b).
  Proof.
    refine (ap fst (snd (PeY_isContr (idC b)) (idC _; _))).
    intros a1 k1 a1' k1' f1 r1. exact (lamC _ @ (φ b k1 k1' f1 (r1 @ lamC _))^).
  Defined.

  Definition Gfcomp {b b' b'' : Ob D} (g : homC b b') (g' : homC b' b'')
    : Gmap (g' ∘c g) = Gmap g' ∘c Gmap g.
  Proof.
    refine (ap fst (snd (PeY_isContr (g' ∘c g)) (Gmap g' ∘c Gmap g; _))).
    intros a1 k1 a1'' k1'' f1 r1.
    refine (ptrunc_rec (pe _ _ _ _) _ (eso b')). intros [a' k'].
    pose (fa := ff_lift K ff k' (g ∘c fst k1)). pose (fb := ff_lift K ff k1'' (g' ∘c fst k')).
    assert (e : fb ∘c fa = f1).
    { apply (ff_lift_unique K ff k1'').
      refine (ap (fun v => _ ∘c v) (fcomp K _ _) @ alphaC _ _ _ @ _).
      refine (ap (fun v => v ∘c _) (ff_lift_spec K ff k1'' _) @ (alphaC _ _ _)^ @ _).
      refine (ap (fun v => g' ∘c v) (ff_lift_spec K ff k' _) @ alphaC _ _ _ @ r1^). }
    refine ((alphaC _ _ _)^ @ ap (fun v => Gmap g' ∘c v)
              (Gmap_spec g a1 k1 a' k' fa (ff_lift_spec K ff k' _)) @ _).
    refine (alphaC _ _ _ @ ap (fun v => v ∘c _)
              (Gmap_spec g' a' k' a1'' k1'' fb (ff_lift_spec K ff k1'' _)) @ _).
    exact ((alphaC _ _ _)^ @ ap (fun v => _ ∘c v) ((fcomp F _ _)^ @ ap (fmap F) e)).
  Defined.

  Definition PeG : Functor D (fst E)
    := Build_Functor D (fst E) G0 (fun b b' g => Gmap g) Gfid (fun b b' b'' g g' => Gfcomp g g').

  Definition pe_nt : NatTrans F (compF PeG K).
  Proof.
    refine ((fun a => fst (h (fob K a) a (idIsoC _))); fun a a' f => _).
    exact (Gmap_spec (fmap K f) a (idIsoC _) a' (idIsoC _) f (lamC _ @ (rhoC _)^)).
  Defined.

End PrecompEsoMap.

Definition precompF_split `{Funext} {C D : WildPreCat} (E : Cat) (K : Functor C D)
  (ff : isFullyFaithful K) (eso : isEso K) : isSplitEso (precompF (fst E) (fst (snd E)) K).
Proof.
  intro F. refine (PeG E K ff eso F; IsoC_inv _).
  exact (pe_nt E K ff eso F;
         components_natiso C (fst E) (fst (snd E)) (pe_nt E K ff eso F)
           (fun a => snd (Gh E K ff eso F (fob K a) a (idIsoC _)))).
Defined.

Definition lem_precomp_equiv_cat `{Funext} : lem_precomp_equiv_cat_stmt.
Proof.
  intros C D E K [ff eso].
  exact (fse_equiv _ (precompF_ff (fst (snd E)) K ff eso) (precompF_split E K ff eso)).
Defined.

(** Definition [def:Rezk-completion]: the full subcategory of presheaves
    on the (merely) representable ones.  NOTE for the book text: for a
    precategory [C], the type [isRepr(F)] of pairs [(C₀, α)] need not be a
    proposition (corollary [cor:repr-prop] needs [C] to be a category),
    so the full subcategory should be taken on [‖isRepr(F)‖]. *)
Section Rezk.

  Context `{Funext} (C : WildPreCat) (pc : isPreCat C).

  Definition isReprU (F : Ob (PSh C)) : PropU := (ptrunc (isRepr C pc F); ptrunc_isProp).

  Definition Rezk : WildPreCat := FullSub (PSh C) isReprU.

  Definition RezkEta : Functor C Rezk
    := Build_Functor C Rezk
         (fun C0 => (yo_ob C pc C0; trunc (C0; idIsoC (yo_ob C pc C0))) : Ob Rezk)
         (fun A B f => yo_map C pc f) (fun A => yo_fid C pc A)
         (fun A B E f g => yo_fcomp C pc f g).

  (** Theorem [thm:Rezk-completion], first part: [η] is a weak
      equivalence. *)
  Definition RezkEta_ff : isFullyFaithful RezkEta := yo_ff C pc.

  Definition RezkEta_eso : isEso RezkEta.
  Proof.
    intros [F r]. refine (ptrunc_rec ptrunc_isProp _ r). intros [C0 i].
    exact (trunc (C0; i)).
  Defined.

  Definition RezkEta_isWeakEquiv : isWeakEquiv RezkEta := (RezkEta_ff; RezkEta_eso).

  (** That [L(C)] is a category: a full subcategory of the presheaf
      category, which is a category when [Set] is one. *)
  Definition Rezk_isUnivalent_stmt : Type := isUnivalent Rezk.

  Definition Rezk_isUnivalent_from (us : isUnivalent SetCat) : Rezk_isUnivalent_stmt
    := FullSub_isUnivalent (PSh C) isReprU (PSh_isUnivalent C us).

End Rezk.

Definition Rezk_isUnivalent `{Univalence} (C : WildPreCat) (pc : isPreCat C)
  : Rezk_isUnivalent_stmt C pc
  := Rezk_isUnivalent_from C pc (snd SetCat_isCat).

(** Theorem [thm:Rezk-completion], second part, and exercise
    [xca:Rezk-completion-locally-small]: smallness of [L(C)]. *)
Definition isEssSmallCat (C : WildPreCat) : Type
  := essSmall (Ob C) × (forall A B : Ob C, essSmall (homC A B)).

Definition isLocSmallCat (C : WildPreCat) : Type := forall A B : Ob C, essSmall (homC A B).

Definition thm_Rezk_small_stmt `{Funext} : Type
  := forall (C : WildPreCat) (pc : isPreCat C), isEssSmallCat C -> isEssSmallCat (Rezk C pc).

Definition xca_Rezk_locally_small_stmt `{Funext} : Type
  := forall (C : WildPreCat) (pc : isPreCat C), isLocSmallCat C -> isLocSmallCat (Rezk C pc).

(** Exercise [xca:Rezk-completion-locally-small] (with [Univalence], so
    that essential smallness is a proposition): for representations
    [yo(A) ≅ F] and [yo(B) ≅ G], [Hom(F,G) ≃ Hom(yo A, yo B) ≃ hom(A,B)]
    ([Rezk_hom_eqv]). *)
Definition Rezk_hom_eqv `{Funext} (C : WildPreCat) (pc : isPreCat C) {F G : Ob (PSh C)}
  {A B : Ob C} (i : IsoC (C := PSh C) (yo_ob C pc A) F)
  (j : IsoC (C := PSh C) (yo_ob C pc B) G)
  : homC (w := PSh C) F G ≃ homC A B.
Proof.
  refine (Eqv_comp (Eqv_comp ((fun k => k ∘c fst i); precomp_isEquiv (snd i) G)
                             ((fun k => invC j ∘c k); postcomp_isEquiv (invC_isIso j) _)) _).
  exact (Eqv_inv (fmap (RezkEta C pc); RezkEta_ff C pc A B)).
Defined.

Definition xca_Rezk_locally_small `{Univalence} : xca_Rezk_locally_small_stmt.
Proof.
  intros C pc ls [F r] [G s].
  refine (ptrunc_rec (essSmall_isProp _) _ r). intros [A i].
  refine (ptrunc_rec (essSmall_isProp _) _ s). intros [B j].
  exact (essSmall_Eqv (Rezk_hom_eqv C pc i j) (ls A B)).
Defined.

Definition essSmall_Sigma {A : Type} {B : A -> Type} (sA : essSmall A)
  (sB : forall a, essSmall (B a)) : essSmall {a : A & B a}
  := ({x : fst sA & fst (sB (eqinv (snd (snd sA)) x))};
      Eqv_comp (tot (fun a => fst (snd (sB a))); tot_isEquiv _ (fun a => snd (snd (sB a))))
               (sum_equiv_base (snd (snd sA)) (fun a => fst (sB a)))).

(** In a category with essentially small hom-sets, the identity types
    of objects are essentially small. *)
Definition Cat_locSmall `{Funext} (C : WildPreCat) (u : isUnivalent C)
  (ls : forall A B : Ob C, essSmall (homC A B)) : locSmall (Ob C).
Proof.
  intros A B. refine (essSmall_Eqv (idtoiso; u A B) _).
  refine (essSmall_Sigma (ls A B) (fun k => essSmall_Sigma _ (fun _ => _))).
  - exact (essSmall_Sigma (ls B A) (fun g => essSmall_locSmall (ls B B) _ _)).
  - exact (essSmall_Sigma (ls B A) (fun g => essSmall_locSmall (ls A A) _ _)).
Defined.

(** [Ob(L(C))] is the image of [Ob(η)], since [η] is essentially
    surjective and [L(C)] is a category. *)
Definition Rezk_Ob_im `{Univalence} (C : WildPreCat) (pc : isPreCat C)
  : Ob (Rezk C pc) ≃ im (fob (RezkEta C pc)).
Proof.
  assert (ex : forall y, Ex (fun x => y = fob (RezkEta C pc) x)).
  { intro y. refine (ptrunc_rec ptrunc_isProp _ (RezkEta_eso C pc y)). intros [A i].
    exact (trunc (A; (eqinv (Rezk_isUnivalent C pc _ y) i)^)). }
  refine (mkEqv (fun y => (y; ex y)) fst (fun y => refl) _).
  intro w. exact (ap (fun e => (fst w; e) : im _) (ptrunc_isProp _ _)).
Defined.

(** Theorem [thm:Rezk-completion], second part, assuming the
    replacement principle (and [Univalence]).  Deviation from the book's
    proof: replacement is applied to [Ob(η) : Ob(C) → Ob(L(C))] rather
    than to [Ob(yo)] into [Set_U^{C^op}], using that [L(C)] is a
    locally small category ([Cat_locSmall]); this avoids resizing the
    hom-sets of [C] into [U]. *)
Definition thm_Rezk_small `{Univalence} (rep : Replacement) : thm_Rezk_small_stmt.
Proof.
  intros C pc [so sh]. refine ((_ : essSmall (Ob (Rezk C pc))); xca_Rezk_locally_small C pc sh).
  exact (essSmall_Eqv (Rezk_Ob_im C pc)
           (rep (Ob C) (Ob (Rezk C pc)) (fob (RezkEta C pc)) so
                (Cat_locSmall (Rezk C pc) (Rezk_isUnivalent C pc)
                              (xca_Rezk_locally_small C pc sh)))).
Defined.

(** Theorem [thm:1types-are-groupoids], first part (with [Funext]): for [1]-types
    [A] and [B], the projection [[A, B] → (A → B)] from functors between
    the path groupoids is an equivalence. *)
Definition thm_1types_are_groupoids_stmt : Type
  := forall (A B : Type), isGrpd A -> isGrpd B ->
       isEquiv (fun F : Functor (PathGrpd A) (PathGrpd B) => fob F).

(** The inverse is [f ↦ PathFun f]: a functor between path groupoids
    acts on paths by [ap], by path induction and [F_id]. *)
Definition thm_1types_are_groupoids `{Funext} : thm_1types_are_groupoids_stmt.
Proof.
  intros A B gA gB.
  refine (iso_to_isEquiv _ PathFun _ (fun f => refl)).
  intro F. refine (path_Functor (PathGrpd_isPreCat B gB) (PathFun (fob F)) F refl _). cbn.
  apply ptw_inv; intro x; apply ptw_inv; intro y; apply ptw_inv; intro p.
  destruct p. exact (fid F x)^.
Defined.

(** Exercise [xca:Rezk-completion-1trunc]: the path
    pregroupoid with [hom(x,y) :≡ ‖x = y‖₀], whose Rezk completion is the
    [1]-truncation. *)
Section TruncPath.

  Context `{Funext} (A : Type).

  Definition tp_comp {x y z : A} (q : strunc (y = z)) (p : strunc (x = y)) : strunc (x = z)
    := strunc_rec strunc_isSet (fun q0 => strunc_rec strunc_isSet (fun p0 => settrunc (q0 ⋅ p0)) p) q.

  Definition tp_lam {x y : A} (p : strunc (x = y)) : tp_comp (settrunc refl) p = p
    := strunc_ind_prop (fun p => tp_comp (settrunc refl) p = p) (fun _ => strunc_isSet _ _)
         (fun p0 => refl) p.

  Definition tp_rho {x y : A} (p : strunc (x = y)) : tp_comp p (settrunc refl) = p
    := strunc_ind_prop (fun p => tp_comp p (settrunc refl) = p) (fun _ => strunc_isSet _ _)
         (fun p0 => ap settrunc (trans_1p p0)) p.

  Definition tp_alpha {x y z w : A} (p : strunc (x = y)) (q : strunc (y = z)) (r : strunc (z = w))
    : tp_comp r (tp_comp q p) = tp_comp (tp_comp r q) p.
  Proof.
    revert p. refine (strunc_ind_prop _ (fun _ => strunc_isSet _ _) _). intro p0.
    revert q. refine (strunc_ind_prop _ (fun _ => strunc_isSet _ _) _). intro q0.
    revert r. refine (strunc_ind_prop _ (fun _ => strunc_isSet _ _) _). intro r0.
    exact (ap settrunc (trans_assoc p0 q0 r0)).
  Defined.

  Definition TruncPathGrpd : WildPreCat
    := Build_WildPreCat A (fun x y => strunc (x = y)) (fun x => settrunc refl)
         (fun x y z => @tp_comp x y z) (fun x y => @tp_lam x y) (fun x y => @tp_rho x y)
         (fun x y z w => @tp_alpha x y z w).

  Definition TruncPathGrpd_isPreCat : isPreCat TruncPathGrpd := fun x y => strunc_isSet.

End TruncPath.

Definition xca_Rezk_completion_1trunc_stmt `{Funext} : Type
  := forall A : Type, Ob (Rezk (TruncPathGrpd A) (TruncPathGrpd_isPreCat A)) ≃ Trunc 1 A.

(** The solution (with [Univalence]): [Ob(η)] extends to
    [f : ‖A‖₁ → Ob(L)] ([RT_f]), which is surjective since [η] is
    essentially surjective, and an embedding: on [|x|, |y|], [ap f]
    corresponds to [‖x = y‖₀ ≃ hom(ηx, ηy) ≃ Iso(ηx, ηy)] ([RT_claim],
    [RT_Psi]; all arrows of the path pregroupoid are isomorphisms,
    [TP_isPreGrpd]). *)
Section RezkTrunc.

  Context `{Univalence} (A : Type).

  Local Notation TP := (TruncPathGrpd A).
  Local Notation tpc := (TruncPathGrpd_isPreCat A).
  Local Notation L := (Rezk TP tpc).
  Local Notation η := (RezkEta TP tpc).

  Definition RT_cat : Cat
    := (L; (FullSub_isPreCat _ _ (FunctorCat_isPreCat _ _ _); Rezk_isUnivalent TP tpc)).

  Definition TP_isPreGrpd : isPreGrpd TP.
  Proof.
    intros x y. refine (strunc_ind_prop _ (fun k => isIsoC_isProp (C := TP) k) _).
    intro p. destruct p. exact ((settrunc refl; refl); (settrunc refl; refl)).
  Defined.

  Definition RT_f : Trunc 1 A -> Ob L
    := Trunc_rec (n := 1) (IsTrunc0 := isGrpd_IsTrunc (Ob_isGrpd RT_cat)) (fob η).

  Definition RT_Psi (x y : A) : homC (w := TP) x y -> IsoC (C := L) (fob η x) (fob η y)
    := fun k => (fmap η k; fmap_isIso η (TP_isPreGrpd x y k)).

  Definition RT_Psi_isEquiv (x y : A) : isEquiv (RT_Psi x y).
  Proof.
    refine (iso_to_isEquiv _ (fun j => eqinv (RezkEta_ff TP tpc x y) (fst j)) _ _).
    - intro k. exact (eqinv_l (RezkEta_ff TP tpc x y) k).
    - intro j. apply (path_IsoC (C := L)). exact (eqinv_r (RezkEta_ff TP tpc x y) (fst j)).
  Defined.

  Definition RT_path_Tr (x y : A) (p : x = y) : equiv_path_Tr (n := 0) x y (tr p) = ap tr p.
  Proof. exact refl. Defined.

  Definition RT_claim0 (x y : A) (p : x = y)
    : idtoiso (C := L) (ap (fob η) p) = RT_Psi x y (settrunc p).
  Proof.
    destruct p. apply (path_IsoC (C := L) (e := idIsoC (C := L) _) (e' := RT_Psi x x (settrunc refl))).
    exact (fid η x)^.
  Defined.

  Definition RT_ap (x y : A) (p : x = y) : ap RT_f (ap (tr (n := 1)) p) = ap (fob η) p
    := match p with refl => refl end.

  Definition RT_claim (x y : A) (z : Tr 0 (x = y))
    : idtoiso (C := L) (ap RT_f (equiv_path_Tr (n := 0) x y z)) = RT_Psi x y z.
  Proof.
    revert z.
    refine (strunc_ind_prop
              (fun z => idtoiso (C := L) (ap RT_f (equiv_path_Tr (n := 0) x y z)) = RT_Psi x y z)
              (fun z => IsoC_isSet (fst (snd RT_cat)) _ _ _ _) _).
    intro p.
    refine (ap (fun q => idtoiso (C := L) (ap RT_f q)) (RT_path_Tr x y p) @ _).
    exact (ap (idtoiso (C := L)) (RT_ap x y p) @ RT_claim0 x y p).
  Defined.

  Definition RT_ap_isEquiv (u v : Trunc 1 A) : isEquiv (@ap _ _ RT_f u v).
  Proof.
    revert u. refine (@Trunc_ind 1 _ (fun u => isEquiv (@ap _ _ RT_f u v))
                        (fun u => @istrunc_hprop (-1) _ (isProp_IsHProp (isEquiv_isProp _))) _).
    intro x. revert v. refine (@Trunc_ind 1 _ (fun v => isEquiv (@ap _ _ RT_f (tr x) v))
                        (fun v => @istrunc_hprop (-1) _ (isProp_IsHProp (isEquiv_isProp _))) _).
    intro y. pose (e := equiv_path_Tr (n := 0) x y).
    pose (uL := Rezk_isUnivalent TP tpc (fob η x) (fob η y)).
    pose (ei := Eqv_of_Equiv (equiv_inverse e)).
    refine (isEquiv_homotopic (comp (eqinv uL) (comp (RT_Psi x y) (fst ei))) _ _
              (comp_isEquiv (comp_isEquiv (snd ei) (RT_Psi_isEquiv x y)) (eqinv_isEquiv uL))).
    intro q. refine (ap (eqinv uL) (RT_claim x y (fst ei q))^ @ eqinv_l uL _ @ _).
    exact (ap (ap RT_f) (eisretr e q)).
  Defined.

  Definition RT_f_isEquiv : isEquiv RT_f.
  Proof.
    refine (inj_surj_isEquiv (ap_isEquiv_isInj RT_ap_isEquiv) _).
    intro y. refine (ptrunc_rec ptrunc_isProp _ (RezkEta_eso TP tpc y)). intros [x i].
    exact (trunc (tr x; (eqinv (Rezk_isUnivalent TP tpc _ y) i)^)).
  Defined.

End RezkTrunc.

Definition xca_Rezk_completion_1trunc `{Univalence} : xca_Rezk_completion_1trunc_stmt
  := fun A => Eqv_inv (RT_f A; RT_f_isEquiv A).

(** Definition [def:flagged-cat]. *)
Definition FlCat : Type := {C : Cat & {A : Type & {f : A -> Ob (fst C) & isSurj f}}}.

(** Theorem [thm:flagged-cat-equiv], assuming that the
    Rezk completion is a category.  NOTE for the book text: the theorem
    says "sending a category [C]"; it should be a precategory. *)
Definition thm_flagged_cat_equiv_stmt `{Funext} : Type
  := forall (u : forall (C : WildPreCat) (pc : isPreCat C), isUnivalent (Rezk C pc)),
       isEquiv (fun C : PreCat =>
                  (((Rezk (fst C) (snd C);
                     (FullSub_isPreCat _ _ (FunctorCat_isPreCat _ _ _); u (fst C) (snd C))) : Cat);
                   (Ob (fst C); (fob (RezkEta (fst C) (snd C));
                     fun B => ptrunc_rec ptrunc_isProp
                                (fun w => trunc (fst w; (eqinv (u _ _ _ B) (snd w))^))
                                (RezkEta_eso (fst C) (snd C) B))))
                  : FlCat).

(** The proof (with [Univalence]): the inverse sends [(D, A, f)] to the
    precategory [FlPre] on [A] with [hom(a,b) :≡ hom_D(f(a), f(b))].
    For a precategory [C], [η] is an isomorphism [C ≅ FlPre(L(C), Ob C, η)]
    ([flag_rt1]).  For a flagged category, [K : FlPre(D,A,f) → D] is a
    weak equivalence, so by [lem:precomp-equiv-cat] [K ≅ G ∘ η] for some
    [G : L → D] ([flG], [flα]), which is fully faithful and essentially
    surjective, hence an equivalence; [cor:Cat-ua] turns it into a path
    along which [Ob(η)] becomes [f] ([flag_rt2], [flag_path]). *)
(** The precategory on [A] with [hom(a,b) :≡ hom_D(f(a), f(b))]. *)
Definition FlPre (X : FlCat) : PreCat.
Proof.
  destruct X as [D [A [f s]]].
  refine (Build_WildPreCat A (fun a b => homC (f a) (f b)) (fun a => idC (f a))
            (fun a b c g h => g ∘c h) (fun a b h => lamC h) (fun a b h => rhoC h)
            (fun a b c d h g k => alphaC h g k); _).
  exact (fun a b => fst (snd D) (f a) (f b)).
Defined.

(** A path of categories acts on objects by its equivalence. *)
Definition flag_path `{Funext} {C D : Cat} (P : C = D) (A : Type) (g : A -> Ob (fst C)) (s : isSurj g)
  (f : A -> Ob (fst D)) (s' : isSurj f)
  (E : forall a, fob (fst (idtoCatEquiv (ap fst P))) (g a) = f a)
  : ((C; (A; (g; s))) : FlCat) = (D; (A; (f; s'))).
Proof.
  destruct P. destruct (ptw_inv E : g = f).
  exact (ap (fun t => ((C; (A; (g; t))) : FlCat)) (Pi_isProp (fun _ => ptrunc_isProp) s s')).
Defined.

Section Flagged.

  Context `{Univalence} (u : forall (C : WildPreCat) (pc : isPreCat C), isUnivalent (Rezk C pc)).

  Definition RezkCat (C : PreCat) : Cat
    := (Rezk (fst C) (snd C); (FullSub_isPreCat _ _ (FunctorCat_isPreCat _ _ _); u (fst C) (snd C))).

  Definition FlOf (C : PreCat) : FlCat
    := (RezkCat C;
        (Ob (fst C); (fob (RezkEta (fst C) (snd C));
          fun B => ptrunc_rec ptrunc_isProp
                     (fun w => trunc (fst w; (eqinv (u _ _ _ B) (snd w))^))
                     (RezkEta_eso (fst C) (snd C) B)))).

  Definition flag_rt1 (C : PreCat) : FlPre (FlOf C) = C.
  Proof.
    pose (η := RezkEta (fst C) (snd C)).
    refine (eqinv (idtoPreCatIso_isEquiv C (FlPre (FlOf C)))
              (Build_Functor (fst C) (fst (FlPre (FlOf C))) idmap (fun a b h => fmap η h)
                 (fun a => fid η a) (fun a b c g h => fcomp η g h);
               (id_isEquiv _; RezkEta_ff (fst C) (snd C))))^.
  Defined.

  Section RT2.

    Context (D : Cat) (A : Type) (f : A -> Ob (fst D)) (s : isSurj f).

    Local Notation C := (FlPre (D; (A; (f; s)))).
    Local Notation η := (RezkEta (fst C) (snd C)).
    Local Notation pd := (fst (snd D)).

    Definition flK : Functor (fst C) (fst D)
      := Build_Functor (fst C) (fst D) f (fun a b h => h) (fun a => refl) (fun a b c g h => refl).

    Definition flK_eso : isEso flK
      := fun d => ptrunc_rec ptrunc_isProp
                    (fun w : {a : A & d = f a} => trunc ((fst w; idtoiso (snd w)^)
                                                          : {a : Ob (fst C) & IsoC (fob flK a) d}))
                    (s d).

    Definition flG : Functor (fst (RezkCat C)) (fst D)
      := fst (precompF_split D η (RezkEta_ff _ _) (RezkEta_eso _ _) flK).

    Definition flα : IsoC (C := FunctorCat (fst C) (fst D) pd) (compF flG η) flK
      := snd (precompF_split D η (RezkEta_ff _ _) (RezkEta_eso _ _) flK).

    Definition flαc (a : A) : IsoC (fob flG (fob η a)) (f a)
      := (fst (fst flα) a; natiso_components (fst C) (fst D) pd (fst flα) (snd flα) a).

    Definition flG_ff : isFullyFaithful flG.
    Proof.
      intros X Y. refine (ptrunc_rec (isEquiv_isProp _) _ (RezkEta_eso _ _ X)). intros [a i].
      refine (ptrunc_rec (isEquiv_isProp _) _ (RezkEta_eso _ _ Y)). intros [b j].
      destruct (eqinv (u _ _ _ X) i), (eqinv (u _ _ _ Y) j).
      pose (conj := fun h : homC (f a) (f b) => invC (flαc b) ∘c (h ∘c fst (flαc a))).
      refine (isEquiv_homotopic (comp conj (eqinv (RezkEta_ff _ _ a b))) _ _
                (comp_isEquiv (eqinv_isEquiv _)
                   (comp_isEquiv (precomp_isEquiv (snd (flαc a)) _)
                                 (postcomp_isEquiv (invC_isIso (flαc b)) _)))).
      intro k. unfold comp.
      refine (_ @ ap (fmap flG) (eqinv_r (RezkEta_ff _ _ a b) k)).
      refine (ap (fun v => invC (flαc b) ∘c v) (snd (fst flα) a b _) @ alphaC _ _ _ @ _).
      exact (ap (fun v => v ∘c _) (iso_rl (flαc b)) @ lamC _).
    Defined.

    Definition flG_eso : isEso flG
      := fun d => ptrunc_rec ptrunc_isProp
                    (fun w : {a : A & d = f a} =>
                       trunc (fob η (fst w); IsoC_comp (idtoiso (snd w)^) (flαc (fst w))))
                    (s d).

    Definition flG_equiv : isCatEquiv flG
      := fse_equiv flG flG_ff (ff_eso_split (RezkCat C) flG flG_ff flG_eso).

    Definition flag_rt2 : FlOf C = (D; (A; (f; s))).
    Proof.
      pose (t := Cat_ua (RezkCat C) D).
      refine (flag_path (eqinv t (flG; flG_equiv)) A (fob η) _ f s _).
      intro a.
      exact (ap (fun e : CatEquiv _ _ => fob (fst e) (fob η a)) (eqinv_r t (flG; flG_equiv))
             @ eqinv (snd (snd D) _ _) (flαc a)).
    Defined.

  End RT2.

End Flagged.

Definition thm_flagged_cat_equiv `{Univalence} : thm_flagged_cat_equiv_stmt.
Proof.
  intro u. refine (iso_to_isEquiv (FlOf u) FlPre (flag_rt1 u) _).
  intros [D [A [f s]]]. exact (flag_rt2 u D A f s).
Defined.

(** Theorem [thm:1types-are-groupoids], second part:
    the path groupoid construction is an equivalence [U^{≤1} ≃ Gpd]. *)
Definition Gpd : Type := {C : Cat & isPreGrpd (fst C)}.

Definition PathGrpdGpd `{Funext} (X : {X : Type & isGrpd X}) : Gpd
  := ((PathGrpd (fst X); (PathGrpd_isPreCat (fst X) (snd X); PathGrpd_isUnivalent (fst X)));
      PathGrpd_isPreGrpd (fst X)).

Definition thm_1types_gpd_stmt `{Funext} : Type := isEquiv PathGrpdGpd.

(** The functor [PathGrpd(C₀) → C] from the path groupoid on the objects
    of a category, acting by [idtoiso]. *)
Definition GpdFun (C : Cat) : Functor (PathGrpd (Ob (fst C))) (fst C).
Proof.
  refine (Build_Functor (PathGrpd (Ob (fst C))) (fst C) idmap
            (fun A B p => fst (idtoiso p)) (fun A => refl) _).
  intros A B E p q. destruct p, q. exact (lamC _)^.
Defined.

Definition GpdFun_isPreCatIso `{Univalence} (G : Gpd)
  : isPreCatIso (C := toPreCat (fst (PathGrpdGpd (Ob (fst (fst G)); Ob_isGrpd (fst G)))))
                (D := toPreCat (fst G)) (GpdFun (fst G)).
Proof.
  refine (id_isEquiv _; fun A B => comp_isEquiv (snd (snd (fst G)) A B) _).
  apply inj_surj_isEquiv.
  - exact (fst_isInj (fun f => isIsoC_isProp f)).
  - intro f. exact (trunc ((f; snd G A B f); refl)).
Defined.

(** The proof (with [Univalence]): the inverse sends a groupoid to its
    type of objects; [GpdFun] is an isomorphism of precategories, so
    [cor:Cat-ua] identifies [PathGrpd(C₀)] with [C]. *)
Definition thm_1types_gpd `{Univalence} : thm_1types_gpd_stmt.
Proof.
  refine (iso_to_isEquiv _ (fun G : Gpd => (Ob (fst (fst G)); Ob_isGrpd (fst G))) _ _).
  - intros [X gX]. exact (ap (fun g => (X; g) : {X : Type & isGrpd X}) (isGrpd_isProp X _ _)).
  - intro G.
    refine (path_sigma_prop (fun C => Pi_isProp (fun A => Pi_isProp (fun B =>
                               Pi_isProp (fun f => isIsoC_isProp f)))) _).
    exact (eqinv (Cat_ua (fst (PathGrpdGpd (Ob (fst (fst G)); Ob_isGrpd (fst G)))) (fst G)) (GpdFun (fst G); preiso_to_equiv _ (GpdFun_isPreCatIso G))).
Defined.
