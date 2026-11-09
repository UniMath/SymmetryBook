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
    - Lemma [lem:ff-eso] ([lem_ff_eso]): for [C] a category and [F] fully
      faithful, [∑_A F(A) ≅ B] is equivalent to a singleton once
      inhabited ([IsoC_postcomp_isEquiv], [fmap_iso_isEquiv]).
    - Theorem [thm:1types-are-groupoids], first part
      ([thm_1types_are_groupoids], with [Funext]; the inverse is
      [PathFun]).
    - Definition [def:flagged-cat] ([FlCat]); the path pregroupoid of
      exercise [xca:Rezk-completion-1trunc] ([TruncPathGrpd]).

    Left out (statements only, no proofs yet)
    - Lemmas [lem:precomp-equiv-cat], theorem [thm:ff-eso-equiv],
      corollaries [cor:Cat-ua] and [cor:cat-2-type] (the [..._stmt]
      definitions).
    - The smallness
      part of theorem [thm:Rezk-completion] ([thm_Rezk_small_stmt]) and
      exercise [xca:Rezk-completion-locally-small]
      ([xca_Rezk_locally_small_stmt]).
    - Exercise [xca:Rezk-completion-1trunc]
      ([xca_Rezk_completion_1trunc_stmt]).
    - Theorem [thm:flagged-cat-equiv] ([thm_flagged_cat_equiv_stmt],
      assuming that Rezk completions are categories).  NOTE for the book
      text: it says "sending a category [C]"; it should be a precategory.

    - The second part of [thm:1types-are-groupoids], [U^{≤1} ≃ Gpd]
      ([thm_1types_gpd_stmt], with [Gpd] and [PathGrpdGpd]).

    Left out (not formalized)
    - Remark [rem:chicken-or-egg] (informal). *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Types.Unit Truncations.Core Spaces.Nat.Core.
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

(** Theorem [thm:ff-eso-equiv] (statement only). *)
Definition thm_ff_eso_equiv_stmt `{Funext} : Type
  := forall (C : Cat) (D : PreCat),
       isInj (fun e : CatEquiv (fst C) (fst D) => fst e)
       × (forall F : Functor (fst C) (fst D),
            ptrunc (isCatEquiv F) <-> isFullyFaithful F × isEso F).

(** Corollary [cor:Cat-ua] (statement only). *)
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

(** Corollary [cor:cat-2-type] (statement only). *)
Definition cor_cat_2_type_stmt : Type := IsTrunc 2 Cat.

(** Definition [def:we-cat]. *)
Definition isWeakEquiv {C D : WildPreCat} (F : Functor C D) : Type
  := isFullyFaithful F × isEso F.

(** Lemma [lem:precomp-equiv-cat] (statement only). *)
Definition precompF `{Funext} {C D : WildPreCat} (E : WildPreCat) (pe : isPreCat E)
  (K : Functor C D) : Functor (FunctorCat D E pe) (FunctorCat C E pe)
  := Build_Functor (FunctorCat D E pe) (FunctorCat C E pe) (fun G => compF G K)
       (fun G G' a => ((fun A => fst a (fob K A)); fun A B f => snd a _ _ (fmap K f)))
       (fun G => refl) (fun G G' G'' a b => refl).

Definition lem_precomp_equiv_cat_stmt `{Funext} : Type
  := forall (C D : PreCat) (E : Cat) (K : Functor (fst C) (fst D)),
       isWeakEquiv K -> isCatEquiv (precompF (fst E) (fst (snd E)) K).

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
    [xca:Rezk-completion-locally-small] (statements only): smallness of
    [L(C)]. *)
Definition isEssSmallCat (C : WildPreCat) : Type
  := essSmall (Ob C) × (forall A B : Ob C, essSmall (homC A B)).

Definition isLocSmallCat (C : WildPreCat) : Type := forall A B : Ob C, essSmall (homC A B).

Definition thm_Rezk_small_stmt `{Funext} : Type
  := forall (C : WildPreCat) (pc : isPreCat C), isEssSmallCat C -> isEssSmallCat (Rezk C pc).

Definition xca_Rezk_locally_small_stmt `{Funext} : Type
  := forall (C : WildPreCat) (pc : isPreCat C), isLocSmallCat C -> isLocSmallCat (Rezk C pc).

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

(** Exercise [xca:Rezk-completion-1trunc] (statement only): the path
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

(** Definition [def:flagged-cat]. *)
Definition FlCat : Type := {C : Cat & {A : Type & {f : A -> Ob (fst C) & isSurj f}}}.

(** Theorem [thm:flagged-cat-equiv] (statement only), assuming that the
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

(** Theorem [thm:1types-are-groupoids], second part (statement only):
    the path groupoid construction is an equivalence [U^{≤1} ≃ Gpd]. *)
Definition Gpd : Type := {C : Cat & isPreGrpd (fst C)}.

Definition PathGrpdGpd `{Funext} (X : {X : Type & isGrpd X}) : Gpd
  := ((PathGrpd (fst X); (PathGrpd_isPreCat (fst X) (snd X); PathGrpd_isUnivalent (fst X)));
      PathGrpd_isPreGrpd (fst X)).

Definition thm_1types_gpd_stmt `{Funext} : Type := isEquiv PathGrpdGpd.
