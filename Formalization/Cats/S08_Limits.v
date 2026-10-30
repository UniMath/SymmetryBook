(** * Section 6.8 Limits and colimits

    Part of Chapter 6 ([cats.tex]); see [Cats.v] for an overview of the
    chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:prod-in-a-cat] ([isProductCone], [ProductCone],
      [hasBinProducts]); the product of types is a product cone
      ([prod_isProductCone]).
    - Exercise [xca:product-cone-prop] ([xca_product_cone_prop], with
      [Funext]): two product cones are isomorphic, and transport along
      [idtoiso⁻¹] is precomposition with the inverse
      ([trp_hom_idtoiso]).
    - Remark [def:product-cones-as-terminal]: the precategory of cones
      ([ConeCat]), in which the product cones are the terminal cones
      ([productCone_terminal]).
    - Definition [def:coprod-in-a-cat] ([isCoproductCocone]), which is
      the product cone in the opposite category by definition
      ([isCoproductCocone_Op]).
    - Definition [def:pullback] ([pullback], [prB], [prC]), exercise
      [xca:univpropofpullback] ([pullback_univ_map],
      [pullback_univ_isEquiv]), pullback diagrams ([isPullbackSquare])
      and the example of the preimage ([pullback_point_eqv]).  These
      were formalized in Section 8.4 before [cats.tex] was added, and
      moved here.  NOTE for the book text: in [xca:univpropofpullback]
      the formula [(f(a), g(a), p(a))] should read [(β(a), γ(a), p(a))].
    - [G × H] with its projections is a product cone of groups
      ([prodG_isProductCone]): [f ↦ (p₁ ∘ f, p₂ ∘ f)] is an equivalence
      with inverse [pairG] ([prodG_Phi_isEquiv]).  [A ⨿ B] is a
      coproduct cocone of types ([sum_isCoproductCocone]), by the
      universal property of the sum. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Types.Sum Types.Unit Truncations.Core Spaces.Nat.Core.
From SymmetryBook Require Export Cats.S07_Equivalences.

Local Open Scope uf_scope.

(** ** 6.8 Limits and colimits *)

(** Definition [def:prod-in-a-cat]: a product cone [(P, p₁, p₂)] with
    its universal property. *)
Definition isProductCone {C : WildPreCat} {A B P : Ob C} (p1 : homC P A) (p2 : homC P B) : Type
  := forall (X : Ob C) (x1 : homC X A) (x2 : homC X B),
       isContr {f : homC X P & (x1 = p1 ∘c f) × (x2 = p2 ∘c f)}.

Definition ProductCone {C : WildPreCat} (A B : Ob C) : Type
  := {P : Ob C & {p : homC P A × homC P B & isProductCone (fst p) (snd p)}}.

Definition hasBinProducts (C : WildPreCat) : Type := forall A B : Ob C, ProductCone A B.

(** Exercise [xca:product-cone-prop] (with [Funext], so that being a
    product cone is a proposition). *)
Definition xca_product_cone_prop_stmt `{Funext} : Type
  := forall (C : WildPreCat), isUnivalent C -> forall A B : Ob C, isProp (ProductCone A B).

Section ProductConeProp.

  Context `{Funext} {C : WildPreCat} (u : isUnivalent C) (A B : Ob C).

  Definition isProductCone_isProp {P : Ob C} (p1 : homC P A) (p2 : homC P B)
    : isProp (isProductCone p1 p2)
    := Pi_isProp (fun X => Pi_isProp (fun x1 => Pi_isProp (fun x2 => isContr_isProp _))).

  (** A map into a product cone that is the identity on the projections
      is the identity. *)
  Definition cone_endo_id {P : Ob C} {p1 : homC P A} {p2 : homC P B}
    (t : isProductCone p1 p2) (h : homC P P) (e1 : p1 = p1 ∘c h) (e2 : p2 = p2 ∘c h)
    : h = idC P
    := ap fst (isContr_isProp' (t P p1 p2) (h; (e1; e2)) (idC P; ((rhoC p1)^; (rhoC p2)^))).

  (** Transport in [X ↦ Hom(X, D)] is precomposition with the inverse. *)
  Definition trp_hom_idtoiso {P Q D : Ob C} (e : P = Q) (h : homC P D)
    : trp (fun X => homC X D) e h = h ∘c fst (fst (snd (idtoiso e))).
  Proof. destruct e. exact (rhoC h)^. Defined.

  Definition trp_cone {P Q : Ob C} (e : P = Q)
    (w : {p : homC P A × homC P B & isProductCone (fst p) (snd p)})
    : fst (trp (fun X => {p : homC X A × homC X B & isProductCone (fst p) (snd p)}) e w)
      = (trp (fun X => homC X A) e (fst (fst w)); trp (fun X => homC X B) e (snd (fst w))).
  Proof. destruct e. exact refl. Defined.

  Definition ProductCone_isProp : isProp (ProductCone A B).
  Proof.
    intros [P [[p1 p2] tp]] [Q [[q1 q2] tq]].
    pose (f := fst (fst (tq P p1 p2))). pose (ef := snd (fst (tq P p1 p2))).
    pose (g := fst (fst (tp Q q1 q2))). pose (eg := snd (fst (tp Q q1 q2))).
    cbn in f, g, ef, eg.
    assert (gf : g ∘c f = idC P).
    { apply (cone_endo_id tp).
      - exact (fst ef @ ap (fun k => k ∘c f) (fst eg) @ (alphaC _ _ _)^).
      - exact (snd ef @ ap (fun k => k ∘c f) (snd eg) @ (alphaC _ _ _)^). }
    assert (fg : f ∘c g = idC Q).
    { apply (cone_endo_id tq).
      - exact (fst eg @ ap (fun k => k ∘c g) (fst ef) @ (alphaC _ _ _)^).
      - exact (snd eg @ ap (fun k => k ∘c g) (snd ef) @ (alphaC _ _ _)^). }
    pose (i := (f; ((g; fg); (g; gf))) : IsoC P Q).
    pose (e := eqinv (u P Q) i).
    pose (r := eqinv_r (u P Q) i : idtoiso e = i).
    refine (pathpair e _).
    apply (path_sigma_prop (fun p => isProductCone_isProp (fst p) (snd p))).
    refine (trp_cone e _ @ _).
    refine (ap011 (fun a b => (a; b) : homC Q A × homC Q B) _ _).
    - refine (trp_hom_idtoiso e p1 @ _).
      exact (ap (fun j : IsoC P Q => p1 ∘c fst (fst (snd j))) r @ (fst eg)^).
    - refine (trp_hom_idtoiso e p2 @ _).
      exact (ap (fun j : IsoC P Q => p2 ∘c fst (fst (snd j))) r @ (snd eg)^).
  Defined.

End ProductConeProp.

Definition xca_product_cone_prop `{Funext} : xca_product_cone_prop_stmt
  := fun C u A B => ProductCone_isProp u A B.

(** The product of types is a product cone in the wild category of
    types. *)
Definition prod_isProductCone (A B : Type)
  : isProductCone (C := TypeCat) (A := A) (B := B) (P := A × B) (fun w => fst w) (fun w => snd w).
Proof.
  intros X x1 x2.
  refine ((((fun x => (x1 x; x2 x)) : X -> A × B); (refl; refl)); _).
  intros [f [p q]]. revert x1 p. refine (paths_ind_r _ _ _). revert x2 q.
  refine (paths_ind_r _ _ _). exact refl.
Defined.

(** The product of groups with its projections is a product cone. *)
Definition prodG_isProductCone_stmt `{Funext} : Type
  := forall G H : Group,
       {p1 : Hom (prodG G H) G & {p2 : Hom (prodG G H) H & isProductCone (C := GroupCat) p1 p2}}.

(** The proof: [f ↦ (p₁ ∘ f, p₂ ∘ f)] is an equivalence, with inverse
    the pairing [pairG] of homomorphisms. *)
Definition ap_fst_pathpair_bin {X Y : Type} {x x' : X} {y y' : Y} (p : x = x') (q : y = y')
  : ap (fun w : X × Y => fst w) (pathpair_bin (p; q)) = p.
Proof. destruct p, q. exact refl. Defined.

Definition ap_snd_pathpair_bin {X Y : Type} {x x' : X} {y y' : Y} (p : x = x') (q : y = y')
  : ap (fun w : X × Y => snd w) (pathpair_bin (p; q)) = q.
Proof. destruct p, q. exact refl. Defined.

Definition pathpair_bin_eta {X Y : Type} {w w' : X × Y} (p : w = w')
  : pathpair_bin (ap (fun w0 : X × Y => fst w0) p; ap (fun w0 : X × Y => snd w0) p) = p.
Proof. destruct p. exact refl. Defined.

Section ProdCone.

  Context `{fe : Funext} (G H : Group).

  Local Notation p1 := (prG1 G H).
  Local Notation p2 := (prG2 G H).

  Definition pairG {K : Group} (g : Hom K G) (h : Hom K H) : Hom K (prodG G H)
    := mkhom (((fun k => (fst (Bf g) k; fst (Bf h) k) : utype (BG G) × utype (BG H));
               pathpair_bin (snd (Bf g); snd (Bf h))) : BG K →* BG (prodG G H)).

  Definition prodG_Phi {K : Group} (f : Hom K (prodG G H)) : Hom K G × Hom K H
    := (compG p1 f; compG p2 f).

  Definition prG1_pairG {K : Group} (g : Hom K G) (h : Hom K H) : compG p1 (pairG g h) = g.
  Proof.
    destruct g as [[g0 pg]].
    exact (ap (fun r => mkhom ((g0; r) : BG K →* BG G))
              (trans_1p _ @ ap_fst_pathpair_bin pg (snd (Bf h)))).
  Defined.

  Definition prG2_pairG {K : Group} (g : Hom K G) (h : Hom K H) : compG p2 (pairG g h) = h.
  Proof.
    destruct h as [[h0 ph]].
    exact (ap (fun r => mkhom ((h0; r) : BG K →* BG H))
              (trans_1p _ @ ap_snd_pathpair_bin (snd (Bf g)) ph)).
  Defined.

  Definition pairG_Phi {K : Group} (f : Hom K (prodG G H))
    : pairG (compG p1 f) (compG p2 f) = f.
  Proof.
    destruct f as [[f0 pf]].
    refine (ap (fun r => mkhom ((f0; r) : BG K →* BG (prodG G H))) _).
    refine (_ @ pathpair_bin_eta pf).
    exact (ap pathpair_bin (pathpair_bin (trans_1p _; trans_1p _))).
  Defined.

  Definition prodG_Phi_isEquiv (K : Group) : isEquiv (@prodG_Phi K).
  Proof.
    refine (iso_to_isEquiv (@prodG_Phi K) (fun w => pairG (fst w) (snd w)) pairG_Phi _).
    intros [g h]. exact (pathpair_bin (prG1_pairG g h; prG2_pairG g h)).
  Defined.

End ProdCone.

Definition prodG_isProductCone `{fe : Funext} : prodG_isProductCone_stmt.
Proof.
  intros G G'. refine (prG1 G G'; (prG2 G G'; _)).
  intros K x1 x2.
  refine (isContr_Eqv _ (prodG_Phi_isEquiv G G' K (x1; x2))).
  exact (Eqv_of_Equiv (equiv_functor_sigma_id
           (fun f => Equiv_of_Eqv (Eqv_inv (path_prod_eqv _ _ _ _))))).
Defined.

(** Remark [def:product-cones-as-terminal]: in the precategory of cones
    over [A, B], product cones are the terminal cones. *)
Section Cones.

  Context `{Funext} (C : WildPreCat) (pc : isPreCat C) (A B : Ob C).

  Definition ConeOb : Type := {X : Ob C & homC X A × homC X B}.

  Definition ConeHom (X P : ConeOb) : Type
    := {f : homC (fst X) (fst P) & (fst (snd X) = fst (snd P) ∘c f) × (snd (snd X) = snd (snd P) ∘c f)}.

  Definition path_ConeHom {X P : ConeOb} (u v : ConeHom X P) (e : fst u = fst v) : u = v
    := path_sigma_prop (fun _ => prod_isProp (pc _ _ _ _) (pc _ _ _ _)) (u := u) (v := v) e.

  Definition cone_id (X : ConeOb) : ConeHom X X
    := (idC (fst X); ((rhoC _)^; (rhoC _)^)).

  Definition cone_comp {X Y Z : ConeOb} (g : ConeHom Y Z) (f : ConeHom X Y) : ConeHom X Z
    := (fst g ∘c fst f;
        (fst (snd f) @ ap (fun k => k ∘c fst f) (fst (snd g)) @ (alphaC _ _ _)^;
         snd (snd f) @ ap (fun k => k ∘c fst f) (snd (snd g)) @ (alphaC _ _ _)^)).

  Definition ConeCat : WildPreCat
    := Build_WildPreCat ConeOb ConeHom cone_id (fun X Y Z => @cone_comp X Y Z)
         (fun X Y f => path_ConeHom (cone_comp (cone_id Y) f) f (lamC _))
         (fun X Y f => path_ConeHom (cone_comp f (cone_id X)) f (rhoC _))
         (fun X Y Z W f g h => path_ConeHom (cone_comp h (cone_comp g f)) (cone_comp (cone_comp h g) f)
                                 (alphaC _ _ _)).

  Definition productCone_terminal (P : ConeOb)
    : isProductCone (fst (snd P)) (snd (snd P)) <-> isTerminal (C := ConeCat) P
    := (fun (t : isProductCone (fst (snd P)) (snd (snd P))) (X : ConeOb) =>
          t (fst X) (fst (snd X)) (snd (snd X)),
        fun (t : isTerminal (C := ConeCat) P) X x1 x2 => t ((X; (x1; x2)) : ConeOb)).

End Cones.

(** Definition [def:coprod-in-a-cat]: coproduct cocones; they are the
    product cones in the opposite category. *)
Definition isCoproductCocone {C : WildPreCat} {A B Q : Ob C} (i1 : homC A Q) (i2 : homC B Q) : Type
  := forall (X : Ob C) (x1 : homC A X) (x2 : homC B X),
       isContr {f : homC Q X & (x1 = f ∘c i1) × (x2 = f ∘c i2)}.

Definition isCoproductCocone_Op (C : WildPreCat) {A B Q : Ob C} (i1 : homC A Q) (i2 : homC B Q)
  : isCoproductCocone i1 i2 = @isProductCone (Op C) A B Q i1 i2
  := refl.

(** The sum of types is a coproduct cocone. *)
Definition sum_isCoproductCocone_stmt `{Funext} : Type
  := forall A B : Type,
       isCoproductCocone (C := TypeCat) (A := A) (B := B) (Q := A ⨿ B) inl inr.

(** The proof: by the universal property of the sum, [f ↦ (f ∘ inl, f ∘ inr)]
    is an equivalence, so the type of [f] with [x₁ = f ∘ inl] and
    [x₂ = f ∘ inr] is equivalent to the contractible type of [f] with
    [sum_rec x₁ x₂ = f]. *)
Definition sum_isCoproductCocone `{Funext} : sum_isCoproductCocone_stmt.
Proof.
  intros A B X x1 x2.
  apply (@isContr_of_Contr _).
  refine (contr_equiv' {f : A ⨿ B -> X & sum_ind (fun _ => X) x1 x2 = f} _).
  refine (equiv_functor_sigma_id (fun f => _)).
  refine ((equiv_sigma_prod0 _ _)^-1
          oE (equiv_path_prod (x1, x2) (fun a => f (inl a), fun b => f (inr b)))^-1 oE _).
  exact (equiv_ap' (equiv_sum_ind (fun _ => X))^-1 _ f).
Defined.

(** Definition [def:pullback]: [∏(f,g) :≡ ∑_{(b,c):B×C} (f(b) = g(c))]. *)
Definition pullback {B C D : Type} (f : B -> D) (g : C -> D) : Type
  := {bc : B × C & f (fst bc) = g (snd bc)}.

Definition prB {B C D : Type} {f : B -> D} {g : C -> D} (w : pullback f g) : B
  := fst (fst w).

Definition prC {B C D : Type} {f : B -> D} {g : C -> D} (w : pullback f g) : C
  := snd (fst w).

(** Exercise [xca:univpropofpullback]. *)
Definition pullback_univ_map {A B C D : Type} (f : B -> D) (g : C -> D)
  (w : pullback (fun β : A -> B => f ∘ β) (fun γ : A -> C => g ∘ γ))
  : A -> pullback f g
  := fun a => ((fst (fst w) a; snd (fst w) a); ptw (snd w) a).

Definition pullback_univ_isEquiv `{Funext} {A B C D : Type} (f : B -> D) (g : C -> D)
  : isEquiv (@pullback_univ_map A B C D f g).
Proof.
  refine (iso_to_isEquiv _
            (fun h => (((fun a => prB (h a)); (fun a => prC (h a)));
                       ptw_inv (fun a => snd (h a)))) _ _).
  - intros [[β γ] p]. cbn.
    exact (ap (fun q => (((β; γ) : (A -> B) × (A -> C)); q)) (eqinv_l (funext _ _) p)).
  - intro h. apply ptw_inv. intro a. unfold pullback_univ_map. cbn.
    exact (ap (fun q => (((prB (h a); prC (h a)) : B × C); q))
              (ptw (eqinv_r (funext _ _) (fun a => snd (h a))) a)).
Defined.

(** Example: the preimage as a pullback, [B ×_D 1 ≃ f⁻¹(d)]. *)
Definition pullback_point_eqv {B D : Type} (f : B -> D) (d : D)
  : pullback f (fun _ : True => d) ≃ fiber f d.
Proof.
  refine (mkEqv (fun w => (prB w; (snd w)⁻¹))
                (fun v => (((fst v; triv) : B × True); (snd v)⁻¹)) _ _).
  - intros [[b []] p]. exact (ap (fun q => (((b; triv) : B × True); q)) (symm_symm p)).
  - intros [b p]. exact (ap (fun q => (b; q)) (symm_symm p)).
Defined.


(** In view of [xca:univpropofpullback], a pullback diagram is a
    commuting square [f ∘ g' = g ∘ f'] whose induced map
    [A → B ×_D C] is an equivalence. *)
Definition isPullbackSquare {A B C D : Type} (f : B -> D) (g : C -> D)
  (w : pullback (fun β : A -> B => f ∘ β) (fun γ : A -> C => g ∘ γ)) : Type
  := isEquiv (pullback_univ_map f g w).
