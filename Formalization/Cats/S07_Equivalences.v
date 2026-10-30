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
    - Lemma [lem:ff-eso] ([lem_ff_eso]): for [C] a category and [F] fully
      faithful, [∑_A F(A) ≅ B] is equivalent to a singleton once
      inhabited ([IsoC_postcomp_isEquiv], [fmap_iso_isEquiv]).
    - Theorem [thm:1types-are-groupoids], first part
      ([thm_1types_are_groupoids], with [Funext]; the inverse is
      [PathFun]).
    - Definition [def:flagged-cat] ([FlCat]); the path pregroupoid of
      exercise [xca:Rezk-completion-1trunc] ([TruncPathGrpd]).

    Left out (statements only, no proofs yet)
    - Lemmas [lem:cat-equiv-is-prop], [lem:equiv-precat-is-ff-split-eso],
      [lem:precomp-equiv-cat], theorem [thm:ff-eso-equiv],
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

(** Lemma [lem:cat-equiv-is-prop] (statement only). *)
Definition lem_cat_equiv_is_prop_stmt `{Funext} : Type
  := forall (C : Cat) (D : WildPreCat) (F : Functor (fst C) D), isProp (isCatEquiv F).

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

(** Lemma [lem:equiv-precat-is-ff-split-eso] (statement only). *)
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
