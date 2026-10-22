(** * Section 6.8 Limits and colimits

    Part of Chapter 6 ([cats.tex]); see [Cats.v] for an overview of the
    chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:prod-in-a-cat] ([isProductCone], [ProductCone],
      [hasBinProducts]); the product of types is a product cone
      ([prod_isProductCone]).
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

    Left out (statements only, no proofs yet)
    - Exercise [xca:product-cone-prop] ([xca_product_cone_prop_stmt]).
    - That [G × H] with its projections is a product cone of groups
      ([prodG_isProductCone_stmt]), and that [A ⨿ B] is a coproduct
      cocone of types ([sum_isCoproductCocone_stmt]). *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Types.Unit Truncations.Core Spaces.Nat.Core.
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

(** Exercise [xca:product-cone-prop] (statement only). *)
Definition xca_product_cone_prop_stmt : Type
  := forall (C : WildPreCat), isUnivalent C -> forall A B : Ob C, isProp (ProductCone A B).

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

(** The product of groups with its projections is a product cone
    (statement only). *)
Definition prodG_isProductCone_stmt `{Funext} : Type
  := forall G H : Group,
       {p1 : Hom (prodG G H) G & {p2 : Hom (prodG G H) H & isProductCone (C := GroupCat) p1 p2}}.

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

(** The sum of types is a coproduct cocone (statement only). *)
Definition sum_isCoproductCocone_stmt `{Funext} : Type
  := forall A B : Type,
       isCoproductCocone (C := TypeCat) (A := A) (B := B) (Q := A ⨿ B) inl inr.

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
