(** * Section 2.2 Types, elements, families, and functions

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Constant functions [cst := const], composition [comp := Compose]
      (notation [g ∘ f]) and [id := idmap], all defined from the library
      since they satisfy the book's defining equations by definition.
    - Associativity of composition and both unit laws hold by definition.
    - The notation [refl] for the constructor [idpath] of identity types,
      and the declaration of the scope [uf_scope] used throughout.
    - Bridge: [g ∘ f] is the library's [g o f]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.

Declare Scope uf_scope.
Delimit Scope uf_scope with uf.
Local Open Scope uf_scope.

(** [refl a] is the constructor [idpath a] of the identity type. *)
Notation refl := idpath.

(** ** 2.2 Types, elements, families, and functions *)

(** A family of types [T(x)] parametrized by [x : X] is a function
    [X -> Type]; a family of elements [e(x) : T(x)] is a dependent
    function, an element of the product type [forall x : X, T x],
    the book's [∏_{x:X} T(x)].  If [T] is constant this is the function
    type [X -> T]. *)

(** Definition [def:cst-map]: the constant function at [t]. *)
Definition cst {X T : Type} : T -> X -> T := @const X T.

(** Composition of functions: [g ∘ f :≡ (a ↦ g(f(a)))]. *)
Definition comp {X Y Z : Type} : (Y -> Z) -> (X -> Y) -> X -> Z
  := @Compose X Y Z.

Notation "g ∘ f" := (comp g f) : uf_scope.

(** The identity function [id_X :≡ (a ↦ a)]. *)
Definition id (X : Type) : X -> X := idmap.

Section TypesElementsFamiliesFunctions.

  Context {X Y Z W : Type} (f : X -> Y) (g : Y -> Z) (h : Z -> W).

  Definition comp_def : g ∘ f = (fun a => g (f a)) := refl.

  (** Associativity holds by definition: [(h ∘ g) ∘ f ≡ h ∘ (g ∘ f)]. *)
  Definition comp_assoc_jdeq : (h ∘ g) ∘ f = h ∘ (g ∘ f) := refl.

  (** Unit laws hold by definition, using the eta rule
      [f ≡ (a ↦ f(a))] (anchor [page:idofetaf]). *)
  Definition comp_id_r_jdeq : f ∘ id X = f := refl.
  Definition comp_id_l_jdeq : id Y ∘ f = f := refl.

End TypesElementsFamiliesFunctions.

(** *** Bridges to Coq-HoTT *)

Definition comp_is_compose {X Y Z : Type} (g : Y -> Z) (f : X -> Y)
  : g ∘ f = (g o f)%function := refl.
