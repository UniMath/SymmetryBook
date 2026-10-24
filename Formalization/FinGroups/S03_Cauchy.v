(** * Section 10.3 Cauchy's theorem

    Part of Chapter 10 ([fingp.tex]); see [FinGroups.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - The fixed points [X^G] of a [G]-set ([GFix]).

    Left out (statements only; time limit per result)
    - Lemma [lem:fixedptsize], theorem [thm:cauchys], lemma
      [lem:nontrivcenter] (with the center as [∏_z (z = z)]) and
      corollary [cor:orderpsquaredgroups], whose proof in the book is
      unfinished.
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core
  Spaces.Finite.Fin Spaces.Finite.Finite Spaces.Nat.Core Spaces.Nat.Division.
From SymmetryBook Require Export FinGroups.S02_Lagrange.

Local Open Scope uf_scope.

(** ** 10.3 Cauchy's theorem *)

(** The fixed points [X^G :≡ ∏_{z : BG} X(z)] of a [G]-set. *)
Definition GFix {G : Group} (X : GSet G) : Type := forall z : utype (BG G), el X z.

(** Lemma [lem:fixedptsize] (statement only). *)
Definition lem_fixedptsize_stmt `{ua : Univalence} : Type
  := forall (p n : ℕ) (G : Group) (FG : Finite (USym G)) (X : GSet G)
            (FX : Finite (el X (sh G))),
       IsPrime p -> fcard (USym G) = nat_pow p (S n) -> NatDivides p (fcard (el X (sh G))) ->
       {F : Finite (GFix X) & NatDivides p (fcard (GFix X))}.

(** Theorem [thm:cauchys] (statement only): a subgroup isomorphic to
    [C_p] ([CG (p-1)]). *)
Definition thm_cauchys_stmt `{ua : Univalence} : Type
  := forall (p : ℕ) (G : Group) (FG : Finite (USym G)),
       IsPrime p -> NatDivides p (fcard (USym G)) ->
       Ex (fun S : SubGrp G => Iso (subgrp_group S) (CG (pred p))).

(** The [C_p]-set [X] of the proof, with [X(Z/p)] the [p]-tuples with
    product [e_G], and the alternative proofs in the footnote, are not
    formalized. *)

(** Lemma [lem:nontrivcenter] (statement only): the center [Z(G)], whose
    underlying set is [∏_{z : BG} (z = z)] (the fixed points of [Ad_G]),
    is not trivial. *)
Definition lem_nontrivcenter_stmt `{ua : Univalence} : Type
  := forall (p n : ℕ) (G : Group) (FG : Finite (USym G)),
       IsPrime p -> fcard (USym G) = nat_pow p (S n) ->
       ¬ isContr (forall z : utype (BG G), z = z).

(** Corollary [cor:orderpsquaredgroups] (statement only; the book's proof
    is unfinished). *)
Definition cor_orderpsquaredgroups_stmt `{ua : Univalence} : Type
  := forall (p : ℕ) (G : Group) (FG : Finite (USym G)),
       IsPrime p -> fcard (USym G) = (p * p)%nat ->
       ¬ ptrunc (Iso G (CG (pred (p * p)))) ->
       ptrunc (Iso G (prodG (CG (pred p)) (CG (pred p)))).
