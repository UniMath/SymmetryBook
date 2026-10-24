(** * Section 10.4 Sylow's Theorems

    Part of Chapter 10 ([fingp.tex]); see [FinGroups.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:sylowsubgroup] ([isSylow], [Syl]); [Syl_G^p] is a
      subtype of [Sub(G)], not a [G]-subset (size issue, Section 9.4);
      the conjugates of a subgroup ([Conj]).

    Left out (statements only)
    - Theorems [thm:sylow1], [thm:sylow2] (= [lem:sylowsareconjugates])
      and [thm:sylow3], and lemma [lem:numberofconjofSylow].  The proofs
      in the book rely on [lem:fixedptsize], Cauchy's theorem, the Weyl
      group lemma [lem:WGHisHfixofG/H] and Section 9.6, which are stated
      only; the proof of [thm:sylow2] in the book is incomplete.
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core
  Spaces.Finite.Fin Spaces.Finite.Finite Spaces.Nat.Core Spaces.Nat.Division.
From SymmetryBook Require Export FinGroups.S03_Cauchy.

Local Open Scope uf_scope.

(** ** 10.4 Sylow's Theorems *)

(** Theorem [thm:sylow1] (statement only). *)
Definition thm_sylow1_stmt `{ua : Univalence} : Type
  := forall (p n : ℕ) (G : Group) (FG : Finite (USym G)),
       IsPrime p -> NatDivides (nat_pow p n) (fcard (USym G)) ->
       Ex (fun K : SubGrp G => {FK : Finite (USym (subgrp_group K)) &
                                 fcard (USym (subgrp_group K)) = nat_pow p n}).

Section SylowDef.

  Context `{ua : Univalence} (p : ℕ) (G : Group) {FG : Finite (USym G)}.

  (** Definition [def:sylowsubgroup].  [Syl_G^p] is taken as a subtype of
      [Sub(G) ≡ SubFam G sh_G], not as a [G]-subset (size issue, Section
      9.4); [G] acts by transport in [SubFam G]. *)
  Definition isSylow (K : SubGrp G) : Type
    := {FK : Finite (USym (subgrp_group K)) & {n : ℕ &
         (fcard (USym (subgrp_group K)) = nat_pow p n)
         × ¬ NatDivides (nat_pow p (S n)) (fcard (USym G))}}.

  Definition Syl : Type := {K : SubGrp G & isSylow K}.

  (** The conjugates of a subgroup: its orbit in [Sub(G)]. *)
  Definition Conj (K : SubGrp G) : Type
    := {K' : SubGrp G & Ex (fun g : USym G => K' = trp (SubFam G) g K)}.

  (** Lemma [lem:numberofconjofSylow] (statement only). *)
  Definition lem_numberofconjofSylow_stmt : Type
    := IsPrime p -> forall K : SubGrp G, isSylow K ->
         {F : Finite (Conj K) & ¬ NatDivides p (fcard (Conj K))}.

  (** Theorem [thm:sylow2] = lemma [lem:sylowsareconjugates] (statement
      only): the Sylow subgroups are conjugate, and a [p]-subgroup is
      conjugate to a subgroup of a Sylow subgroup. *)
  Definition thm_sylow2_stmt : Type
    := IsPrime p ->
       (forall K K' : SubGrp G, isSylow K -> isSylow K' ->
          Ex (fun g : USym G => K' = trp (SubFam G) g K))
       × (forall (H P : SubGrp G) (s : ℕ) (FH : Finite (USym (subgrp_group H))),
            fcard (USym (subgrp_group H)) = nat_pow p s -> isSylow P ->
            Ex (fun g : USym G =>
                  {j : Hom (subgrp_group (trp (SubFam G) g H : SubGrp G)) (subgrp_group P) &
                    compG (subgrp_incl P) j = subgrp_incl (trp (SubFam G) g H : SubGrp G)})).

  (** Theorem [thm:sylow3] (statement only). *)
  Definition thm_sylow3_stmt : Type
    := IsPrime p -> forall (P : SubGrp G) (sP : isSylow P),
         {F : Finite Syl &
           NatDivides (@fcard _ F)
             (nat_div (@fcard _ FG) (@fcard _ (fst sP)))
           × (nat_mod (@fcard _ F) p = 1%nat)}.

End SylowDef.

(** The final question in the book (standard examples) is informal. *)
