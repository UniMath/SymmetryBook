(** * Section 2.11 Binary products

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Own binary product [X × Y :≡ Σ_{x:X} Y], shown equivalent to the
      library's [prod]; the notation is left-associative, so triples are
      parenthesized.
    - [lem:isEq-pair-bin=]: [q : y = y'] isn't definitionally a path
      over [p], so the map converts [q] with [po_const].
    - Exercises [xca:binary-prod-equiv] and [xca:binary-prod-comm].
    - Bridge: identifications of pairs in [X × Y] correspond to the
      library's [path_prod]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S10_IdentifyingPairs.

Local Open Scope uf_scope.

(** ** 2.11 Binary products

    The binary product [X × Y] is the sum over the constant family [Y]. *)

Notation "X × Y" := ({_ : X & Y})
  : uf_scope.

(** It is equivalent to Coq-HoTT's record type [prod]. *)
Definition binprod_prod (X Y : Type) : (X × Y) ≃ (X * Y)
  := mkEqv (fun w : X × Y => (fst w, snd w)) (fun w : X * Y => (Overture.fst w; Overture.snd w) : X × Y)
           (fun _ => refl) (fun _ => refl).

(** Paths over a path in a constant family are paths, as an equivalence. *)
Definition po_const {X Z : Type} {a a' : X} (p : a = a') {z z' : Z}
  : (z = z') -> PathOver (fun _ => Z) p z z'
  := match p with refl => id _ end.

Definition po_const_isEquiv {X Z : Type} {a a' : X} (p : a = a') (z z' : Z)
  : isEquiv (@po_const X Z a a' p z z')
  := match p with refl => id_isEquiv _ end.

(** Lemma [lem:isEq-pair-bin=]. *)
Definition pathpair_bin {X Y : Type} {x x' : X} {y y' : Y}
  : (x = x') × (y = y') -> ((x; y) = (x'; y') :> X × Y)
  := fun pq => pathpair (fst pq) (po_const (fst pq) (snd pq)).

Definition pathpair_bin_isEquiv {X Y : Type} {x x' : X} {y y' : Y}
  : isEquiv (@pathpair_bin X Y x x' y y')
  := comp_isEquiv (tot_isEquiv _ (fun p => po_const_isEquiv p y y')) pathpair_isEquiv.

Definition path_prod_eqv {X Y : Type} (x x' : X) (y y' : Y)
  : ((x = x') × (y = y')) ≃ ((x; y) = (x'; y') :> X × Y)
  := (_; pathpair_bin_isEquiv).

(** The product of two maps. *)
Definition prod_map {X X' Y Y' : Type} (f : X -> Y) (f' : X' -> Y')
  : X × X' -> Y × Y'
  := fun w => (f (fst w); f' (snd w)).

(** Exercise [xca:binary-prod-equiv]. *)
Definition bool_family (X Y : Type) : Bool -> Type
  := fun b => if b then Y else X.

Definition binary_prod_equiv `{Funext} (X Y : Type)
  : isEquiv (fun f : forall b, bool_family X Y b => (f no; f yes) : X × Y).
Proof.
  refine (iso_to_isEquiv _
            (fun (w : X × Y) b => match b return bool_family X Y b with
                                  | yes => snd w | no => fst w end)
            _ (fun _ => refl)).
  intro f. apply ptw_inv. intros []; exact refl.
Defined.

(** Exercise [xca:binary-prod-comm]. *)
Definition binary_prod_comm (X Y : Type) : (X × Y) ≃ (Y × X)
  := mkEqv (fun w : X × Y => (snd w; fst w) : Y × X)
           (fun w : Y × X => (snd w; fst w) : X × Y)
           (fun _ => refl) (fun _ => refl).

(** *** Bridges to Coq-HoTT *)

Definition binprod_paths_eqv {X Y : Type} (x x' : X) (y y' : Y)
  : ((x; y) = (x'; y') :> X × Y) ≃ ((x, y) = (x', y') :> X * Y)
  := Eqv_comp (Eqv_comp (Eqv_inv (path_prod_eqv x x' y y'))
                        (binprod_prod (x = x') (y = y')))
       (Eqv_of_Equiv (equiv_path_prod (x, y) (x', y'))).
