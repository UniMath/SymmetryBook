(** * Section 2.8 Sum types

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Sum types are Coq-HoTT's [sig], written [{x : X & Y x}], with pairs
      [(x; y)] and [Tot Y]; [fst := pr1], [snd := pr2].  The record [sig]
      has primitive projections, hence definitional η, which makes many
      later round trips hold by definition.
    - Iterated and non-dependent sums.
    - Bridges: [fst] is [pr1], [snd] is [pr2]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S07_IdentifyingInFamilies.

Local Open Scope uf_scope.

(** ** 2.8 Sum types

    The sum type [∑_{x:X} Y(x)] is [{x : X & Y x}], also denoted [Tot(Y)].
    If [X] and [Y(x)] are in [U], then so is the sum. *)

Notation Tot Y := (sig Y).

Definition sum_in_U@{u} (X : Type@{u}) (Y : X -> Type@{u}) : Type@{u}
  := {x : X & Y x}.

(** First and second projection: [fst(a,b) :≡ a] and [snd(a,b) :≡ b],
    the library's [fst] and [snd]. *)
Definition fst {X : Type} {Y : X -> Type} (z : {x : X & Y x}) : X := pr1 z.
(** Second projection [it:second-projection]. *)
Definition snd {X : Type} {Y : X -> Type} (z : {x : X & Y x}) : Y (fst z)
  := pr2 z.

Definition fst_jdeq {X : Type} {Y : X -> Type} (a : X) (b : Y a)
  : fst (a; b) = a := refl.
Definition snd_jdeq {X : Type} {Y : X -> Type} (a : X) (b : Y a)
  : snd (a; b) = b := refl.

Check (@snd : forall {X : Type} {Y : X -> Type} (z : {x : X & Y x}), Y (fst z)).

(** Remark [rem:non-dependent-sums]: the binary product [X × Y] is the sum
    over a constant family (see 2.11).  Remark [rem:iterated-sums]:
    [(x, y, z) :≡ (x, (y, z))]. *)
Definition triple {X : Type} {Y : X -> Type} {Z : forall x, Y x -> Type}
  (x : X) (y : Y x) (z : Z x y) : {x : X & {y : Y x & Z x y}}
  := (x; y; z).

(** *** Bridges to Coq-HoTT *)

Definition fst_is_pr1 {X : Type} {Y : X -> Type} (z : {x : X & Y x})
  : fst z = pr1 z := refl.

Definition snd_is_pr2 {X : Type} {Y : X -> Type} (z : {x : X & Y x})
  : snd z = pr2 z := refl.
