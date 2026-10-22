(** * Section 2.3 Universes

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - The universe hierarchy and cumulativity.
    - The correspondence between families of types and functions into a
      universe. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S02_Types.

Local Open Scope uf_scope.

(** ** 2.3 Universes

    Coq-HoTT has a hierarchy of universes [Type@{i}], which is
    cumulative: if [i < j] and [X : Type@{i}] then [X : Type@{j}].
    The smallest universe [U_0] is [Type0] in Coq-HoTT, which contains
    the basic types [ℕ], [False], [True], ... *)

Section Universes.

  Universes i j.
  Constraint i < j.

  (** Every universe is an element of a larger one. *)
  Definition universe_in_larger : Type@{j} := Type@{i}.

  (** Cumulativity (item [it:cumulative]). *)
  Definition cumulative (X : Type@{i}) : Type@{j} := X.

  (** Correspondence between families of types and functions into a
      universe: a family [T(x)] with [T(x) : U] gives [x ↦ T(x) : X -> U],
      and conversely [f' : X -> U] gives the family [f'(x)].  In Rocq
      these two views coincide: a family of types simply *is* a function
      into a universe. *)
  Definition family_to_function {X : Type@{i}} (T : X -> Type@{i})
    : X -> Type@{i} := fun x => T x.

  Definition family_to_function_eta {X : Type@{i}} (T : X -> Type@{i})
    : family_to_function T = T := refl.

  (** Function types between types in [U] are again in [U]. *)
  Definition fun_type_in_U (X Y : Type@{i}) : Type@{i} := X -> Y.

End Universes.
