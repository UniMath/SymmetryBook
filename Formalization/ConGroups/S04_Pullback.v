(** * Section 8.4 The pullback

    Part of Chapter 8 ([congp.tex]); see [ConGroups.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - The pullback ([def:pullback]) and its universal property
      ([xca:univpropofpullback]) are formalized in Section 6.8
      ([Cats/S08_Limits.v]), where [cats.tex] defines them.
    - Definition [def:intersectionand unionofsets] ([sub_inter],
      [sub_union]); the book's union [A(s) + B(s)] is not a family of
      propositions, so we truncate it.  NOTE for the book text.
      Exercise [xca:intersectionpullbackofsets](1)
      ([pullback_inter_eqv]).
    - Definition [def:intersectionofgroups]: [pullbackG f f'] (the
      component at [(sh_H, sh_{H'}, p_{f'} p_f⁻¹)]), with its projections,
      and [intersectionG] of two monomorphisms.

    Left out (statements only, no proofs yet; time limit per result)
    - Example [ex:pullbackandgcd] ([ex_pullbackandgcd_stmt]), the example
      [L ℤ = a ℤ ∩ b ℤ] ([lcm_intersection_stmt], with [dgHom]), exercise
      [xca:intersectionpullbackofsets](2) ([xca_card_union_inter_stmt]),
      and the exercise on [Hom(K, H ×_G H')] and [U(H ×_G H')]
      ([pullbackG_univ_stmt]; the last part, about abstract groups, is
      not stated separately).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Spaces.Nat.Core Spaces.Nat.Division
  Spaces.Circle.
From SymmetryBook Require Export ConGroups.S03_Wreath.

Local Open Scope uf_scope.

(** ** 8.4 The pullback *)

(** Example [ex:pullbackandgcd] (statement only): the pullback of the
    [a]-fold and the [b]-fold coverings of the circle is
    [S1 × BC_{gcd(a,b)}]. *)
Definition ex_pullbackandgcd_stmt `{Univalence} : Type
  := forall i j : ℕ,
       pullback (dg (S i)) (dg (S j))
       ≃ (S1 × utype (BG (CG (pred (nat_gcd (S i) (S j)))))).

(** Definition [def:intersectionand unionofsets]: intersection and union
    of subsets (the union is the propositional truncation of the sum, so
    that it is again a subset). *)
Definition sub_inter {S : Type} (P Q : Sub S) : Sub S
  := fun s => ((fst (P s) × fst (Q s)); prod_isProp (snd (P s)) (snd (Q s))).

Definition sub_union {S : Type} (P Q : Sub S) : Sub S
  := fun s => ptrunc_PropU (fst (P s) ⨿ fst (Q s)).

(** Exercise [xca:intersectionpullbackofsets](1). *)
Definition pullback_inter_eqv {S : Type} (P Q : Sub S)
  : pullback (fun x : carrier P => fst x) (fun y : carrier Q => fst y)
    ≃ carrier (sub_inter P Q).
Proof.
  refine (mkEqv
    (fun w : pullback (fun x : carrier P => fst x) (fun y : carrier Q => fst y) =>
       exist (fun s => fst (sub_inter P Q s)) (fst (prB w))
         ((snd (prB w); trp (fun s => fst (Q s)) (snd w)⁻¹ (snd (prC w)))
          : fst (P (fst (prB w))) × fst (Q (fst (prB w)))))
    (fun v : carrier (sub_inter P Q) =>
       (((((fst v; fst (snd v)) : carrier P); ((fst v; snd (snd v)) : carrier Q))
         : carrier P × carrier Q); refl))
    _ _).
  - intros [[[s x] [s' y]] p]. cbn in p. destruct p. exact refl.
  - intros [s [x y]]. exact refl.
Defined.

(** Exercise [xca:intersectionpullbackofsets](2), part
    [xca:cardinalityintersectionunion] (statement only):
    for subsets of a finite set (with finite carriers),
    [|A| + |B| = |A ∪ B| + |A ∩ B|]. *)
Definition xca_card_union_inter_stmt `{Univalence} : Type
  := forall (S : Type) (P Q : Sub S)
            (hP : isFinSet (carrier P)) (hQ : isFinSet (carrier Q))
            (hU : isFinSet (carrier (sub_union P Q))) (hI : isFinSet (carrier (sub_inter P Q))),
       add (cardF hP) (cardF hQ) = add (cardF hU) (cardF hI).

(** Definition [def:intersectionofgroups]: the pullback of groups, the
    component of [BH ×_{BG} BH'] at [(sh_H, sh_{H'}, p_{f'} p_f⁻¹)]. *)
Section PullbackGroups.

  Context `{fe : Funext} {H H' G : Group} (f : Hom H G) (f' : Hom H' G).

  Definition pullbackB : Type := pullback (fst (Bf f)) (fst (Bf f')).

  Definition pullbackB_isGrpd : isGrpd pullbackB
    := Sigma_isGrpd (Sigma_isGrpd (BG_isGrpd H) (fun _ => BG_isGrpd H'))
         (fun _ => set_isGrpd (BG_isGrpd G _ _)).

  Definition pullbackB_pt : pullbackB
    := (((sh H; sh H') : utype (BG H) × utype (BG H')); snd (Bf f') ⋅ (snd (Bf f))⁻¹).

  Definition pullbackG : Group := AutG pullbackB_isGrpd pullbackB_pt.

  (** The projections are homomorphisms. *)
  Definition pullbackG_pr1 : Hom pullbackG H
    := mkhom (((fun w : component pullbackB pullbackB_pt => prB (fst w)); refl)
                : BG pullbackG →* BG H).

  Definition pullbackG_pr2 : Hom pullbackG H'
    := mkhom (((fun w : component pullbackB pullbackB_pt => prC (fst w)); refl)
                : BG pullbackG →* BG H').

End PullbackGroups.

(** The intersection of two monomorphisms is their pullback. *)
Definition intersectionG `{Funext} {G : Group} (m m' : Mono G) : Group
  := pullbackG (fst (snd m)) (fst (snd m')).

(** The example [Lℤ = aℤ ∩ bℤ] (statement only): with [a ↦ (dg_a, refl)]
    the subgroup [aℤ], the pullback of [aℤ] and [bℤ] is [ℤ], included
    by [dg_L] for [L] the least common multiple. *)
Definition dgHom `{Univalence} (n : ℕ) : Hom ZZ ZZ := mkhom ((dg n; refl) : BG ZZ →* BG ZZ).

Definition lcm_intersection_stmt `{Univalence} : Type
  := forall i j : ℕ,
       {k : Hom ZZ (pullbackG (dgHom (S i)) (dgHom (S j))) &
         isIso k
         × (compG (dgHom (S i)) (compG (pullbackG_pr1 (dgHom (S i)) (dgHom (S j))) k)
            = dgHom (nat_lcm (S i) (S j)))}.

(** The exercise on [Hom(K, H ×_G H')] and [U(H ×_G H')] (statement
    only). *)
Definition pullbackG_univ_stmt `{Funext} : Type
  := forall (H H' G K : Group) (f : Hom H G) (f' : Hom H' G),
       (pullback (fun k : Hom K H => compG f k) (fun k : Hom K H' => compG f' k)
        ≃ Hom K (pullbackG f f'))
       × (pullback (USymf f) (USymf f') ≃ USym (pullbackG f f')).
