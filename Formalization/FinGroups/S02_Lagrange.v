(** * Section 10.2 Lagrange's theorem, counting version

    Part of Chapter 10 ([fingp.tex]); see [FinGroups.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    Finiteness is the library's [Finite] with cardinality [fcard], as in
    Section 5.7; [FinGroup_Finite] converts [isFinGroup] (Section 4.2,
    definition [def:finitegrd]).
    - Lemma [lem:Lagrangeascounting], first part ([Lagrangeascounting]),
      from [lagrange_card] of Section 5.3, assuming [G/H] finite.
    - The corollary on products ([card_prodG], with [prodG_Finite]).

    Left out (statements only)
    - That [G/H] is finite and the second part of
      [lem:Lagrangeascounting] ([Lagrangeascounting_stmt]); corollaries
      [cor:cyclicgroupsaresimple] and [cor:whatSylow2needs].
    - Informal: the chapter introduction, its examples, remark
      [rem:noofsubgps], the example of orders and the remark on [C_2^n].
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core
  Spaces.Finite.Fin Spaces.Finite.Finite Spaces.Nat.Core Spaces.Nat.Division.
From SymmetryBook Require Export Subgroups.Subgroups.

Local Open Scope uf_scope.

(** The introduction of the chapter (the example with [13] and [8], the
    examples on [Σ_3], [Σ_4], [Σ_n]) and remark [rem:noofsubgps] are
    informal. *)

(** ** 10.2 Lagrange's theorem, counting version *)

(** Definition [def:finitegrd]: [isFinGroup] and [CardG] (Section 4.2).
    Below finiteness is the library's [Finite], with cardinality
    [fcard], as in Section 5.7. *)
Definition FinGroup_Finite `{ua : Univalence} (G : Group) (h : isFinGroup G) : Finite (USym G)
  := isFinSet_Finite h.

(** The example after [def:finitegrd] (orders of the trivial, cyclic and
    permutation groups) is informal. *)

(** Lemma [lem:Lagrangeascounting], first part: [|G| = |G/H| · |H|], with
    [G/H] the set [X(sh_G)] of the subgroup [(X, pt_X, !)] (Section 5.3,
    [lagrange_card]).  We assume [G/H] finite; that it follows from the
    finiteness of [G] is stated in [Lagrangeascounting_stmt], together
    with the second part. *)
Definition Lagrangeascounting `{fe : Funext} {G : Group} (S : SubGrp G)
  (FG : Finite (USym G)) (FX : Finite (el (sg_X S) (sh G)))
  : fcard (USym G) = (fcard (el (sg_X S) (sh G)) * @fcard _ (subgrp_Finite S FG FX))%nat
  := lagrange_card S FG FX.

Definition Lagrangeascounting_stmt `{ua : Univalence} : Type
  := forall (G : Group) (S : SubGrp G) (FG : Finite (USym G)),
       {FX : Finite (el (sg_X S) (sh G)) &
         @fcard _ (subgrp_Finite S FG FX) = fcard (USym G) -> isContr (el (sg_X S) (sh G))}.

(** Corollary [cor:cyclicgroupsaresimple] (statement only); [CG k] is
    [C_{k+1}]. *)
Definition cor_cyclicgroupsaresimple_stmt `{ua : Univalence} : Type
  := forall (k : ℕ), IsPrime (S k) -> forall S : SubGrp (CG k),
       isContr (USym (subgrp_group S)) + isContr (el (sg_X S) (sh (CG k))).

(** Corollary [cor:whatSylow2needs] (statement only): [H] is a subgroup of
    the kernel [N]; surjectivity of [f] is surjectivity on symmetries. *)
Definition cor_whatSylow2needs_stmt `{ua : Univalence} : Type
  := forall (G G' H : Group) (f : Hom G G') (s : isSurj (USymf f)) (i : Hom H G) (m : ismono i)
            (FH : Finite (USym H)) (FG' : Finite (USym G')),
       nat_gcd (fcard (USym H)) (fcard (USym G')) = 1%nat ->
       {j : Hom H (Ker f) & compG (kermap f) j = i}.

(** The corollary on products: [|G × G'| = |G| · |G'|]. *)
Section CardProd.

  Context `{fe : Funext} (G G' : Group) {FG : Finite (USym G)} {FG' : Finite (USym G')}.

  Definition USym_prodG_prod : USym (prodG G G') <~> USym G * USym G'
    := Equiv_of_Eqv (Eqv_comp (USym_prodG G G') (binprod_prod _ _)).

  Definition prodG_Finite : Finite (USym (prodG G G'))
    := finite_equiv' _ USym_prodG_prod^-1 _.

  Definition card_prodG
    : @fcard _ prodG_Finite = (fcard (USym G) * fcard (USym G'))%nat
    := fcard_equiv' USym_prodG_prod @ fcard_prod _ _.

End CardProd.

(** The remark after it ([C_2^n] has order [2^n]) is informal. *)
