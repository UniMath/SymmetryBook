(** * Section 9.8 The Weyl group

    Part of Chapter 9 ([subgroups.tex]); see [Subgroups.v] for an
    overview of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - For a subgroup [S ≡ (X, pt_X, !)]: definitions [def:Weyl] ([Weyl])
      and [def:normalizer] ([SubTot], [Normalizer]); the homomorphisms
      [i_G^H] ([iN], with [iN_ismono]), [p_G^H] ([pN]) and [j_H] ([jH],
      via [trans_at], [phiH]).

    - Lemma [lem:WGHisHfixofG/H] ([lem_WGHisHfixofGH], with [eWeyl]),
      under the hypothesis that every [G]-map [X → X] is invertible;
      [eWeyl] is always injective ([eWeyl_inj]).  NOTE for the book text:
      without the hypothesis the lemma fails (the fixed points of [G/H]
      are [{g | g⁻¹Hg ⊆ H}/H], while the symmetries of [W_G H] come from
      [N_G H = {g | g⁻¹Hg = H}]); e.g. [BS(1,2)] with [H = ⟨a⟩].  It holds
      for finite [H].

    Left out (statements only)
    - The rest of the lemma after the unpacking ([normalizer_lemma_stmt]):
      [p_G^H] is an epimorphism, [ker p_G^H = (H, j_H)], [i_H = i_G^H j_H].
    - The equivalence [e] of the unpacking of [N_G H] is not formalized
      separately.
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core.
From SymmetryBook Require Export Subgroups.S07_Automorphisms.

Local Open Scope uf_scope.

(** ** 9.8 The Weyl group *)

(** The subgroup [H] is given by [S ≡ (X, pt_X, !) : Sub(G)]; [H] itself is
    [subgrp_group S] with the monomorphism [subgrp_incl S] (Section 5.3),
    as recalled at the start of the section (informal). *)
Section Weyl.

  Context `{ua : Univalence} {G : Group} (S : SubGrp G).

  Local Notation X := (sg_X S).

  (** Definition [def:Weyl]: [W_G H :≡ Aut_{G-set}(X)]. *)
  Definition Weyl : Group := AutG GSet_isGrpd X.

  (** Definition [def:normalizer]: [N_G H :≡ Aut_{∑_y Sub(G)(y)}(sh_G, X, pt_X)]. *)
  Definition SubTot : Type := {y : utype (BG G) & SubFam G y}.

  Definition SubTot_isGrpd : isGrpd SubTot
    := Sigma_ntype 1 (BG_isGrpd G) (fun y => set_ntype 1 (SubGrp_isSet (regroup G y))).

  Definition Normalizer : Group := AutG SubTot_isGrpd ((sh G; S) : SubTot).

  (** The monomorphism [i_{N_G H}], the first projection. *)
  Definition iN : Hom Normalizer G
    := @mkhom Normalizer G ((fun u : component SubTot (sh G; S) => fst (fst u)); refl).

  Definition iN_ismono : ismono iN.
  Proof.
    refine (cancel_isInj (USym_isSet G) _). intros h h' e.
    refine (ap_fst_cancel (fun _ => prop_is_set ptrunc_isProp) h h' _).
    refine (ap_fst_cancel (fun y => SubGrp_isSet (regroup G y)) _ _ _).
    refine ((ap_compose fst fst h)^ @ _ @ ap_compose fst fst h').
    exact ((trans_1p _)^ @ e @ trans_1p _).
  Defined.

  (** The projection [p_G^H : Hom(N_G H, W_G H)], [(y, Y, pt, !) ↦ (Y, !)]. *)
  Definition BpN (u : component SubTot (sh G; S)) : utype (BG Weyl)
    := (sg_X (snd (fst u));
        ptrunc_rec ptrunc_isProp (fun r => trunc (ap (fun w : SubTot => sg_X (snd w) : GSet G) r))
          (snd u)).

  Definition pN : Hom Normalizer Weyl
    := @mkhom Normalizer Weyl (BpN; path_sigma_prop (fun _ => ptrunc_isProp)
                                      (u := sh Weyl) (v := BpN (sh Normalizer)) refl).

  (** The homomorphism [j_H : Hom(H, N_G H)], [(y, v) ↦ (y, X, v, !)];
      [X] is transitive also with respect to the shape [y]. *)
  Definition trans_at (y : utype (BG G)) : istrans (G := regroup G y) X.
  Proof.
    refine (ptrunc_rec ptrunc_isProp _ (snd (BG_isConn G) (sh G) y)).
    intro p. destruct p. exact (sg_trans S).
  Defined.

  Definition phiH (w : TotG X) : SubTot := (fst w; (X; (snd w; trans_at (fst w)))).

  Definition phiH_pt : ((sh G; S) : SubTot) = phiH (sh G; sg_pt S)
    := ap (fun t => (sh G; (X; (sg_pt S; t))) : SubTot) (istrans_isProp X _ _).

  Definition BjH (w : TotG X) : utype (BG Normalizer)
    := (phiH w;
        ptrunc_rec ptrunc_isProp (fun q => trunc (phiH_pt @ ap phiH q))
          (snd (conn_of_trans X (sg_trans S)) (sh G; sg_pt S) w)).

  Definition jH : Hom (subgrp_group S) Normalizer
    := @mkhom (subgrp_group S) Normalizer
         (BjH; path_sigma_prop (fun _ => ptrunc_isProp)
                 (u := sh Normalizer) (v := BjH (sh (subgrp_group S))) phiH_pt).

  (** The lemma after the unpacking of [N_G H]: [i_G^H] is a monomorphism
      ([iN_ismono]); the rest is stated only: [p_G^H] is an epimorphism,
      [ker p_G^H = (H, j_H)] as subgroups of [N_G H], and
      [i_H = i_G^H j_H]. *)
  Definition normalizer_lemma_stmt : Type
    := isepi pN
       × {m : ismono jH & ker pN = ((subgrp_group S; (jH; m)) : Mono Normalizer)}
       × (subgrp_incl S = compG iN jH).

  (** Lemma [lem:WGHisHfixofG/H]: the symmetries of [W_G H], i.e.
      [X = X], are the [H]-fixed points of [X = G/H], via
      [e(f)(y, v) :≡ f_y(v)].  NOTE: the book identifies
      [∏_y (X(y) = X(y))] with [∏_y (X(y) → X(y))], which needs that every
      [G]-map [X → X] is invertible.  That fails in general: the [G]-map
      [gH ↦ gnH] of [G/H] only needs [n⁻¹Hn ⊆ H], and it is invertible
      only if [n⁻¹Hn = H]; in [BS(1,2) = ⟨a, t | t a t⁻¹ = a²⟩] with
      [H = ⟨a⟩] and [n = t⁻¹] the inclusion is strict.  (It holds when [H]
      is finite.)  We assume that every [G]-map [X → X] is invertible;
      [e] is always injective ([eWeyl_inj]). *)
  Definition eWeyl (f : X = X) (w : TotG X) : el X (fst w)
    := trp (fun Z : GSet G => el Z (fst w)) f (snd w).

  Definition lem_WGHisHfixofGH_stmt : Type
    := (forall φ : forall y, el X y -> el X y, forall y, isEquiv (φ y)) -> isEquiv eWeyl.

  (** [e] is injective: an identification of [G]-sets is determined by
      its action ([GSet_path_ext] of Section 9.5). *)
  Definition eWeyl_inj (f f' : X = X) (e : forall w, eWeyl f w = eWeyl f' w) : f = f'
    := GSet_path_ext f f' (fun y v => e (y; v)).

  Definition lem_WGHisHfixofGH : lem_WGHisHfixofGH_stmt.
  Proof.
    intro hyp.
    pose (g := fun φ : forall w : TotG X, el X (fst w) =>
                 path_GSet (X := X) (Y := X)
                   (fun y => ((fun v => φ (y; v)); hyp (fun y v => φ (y; v)) y))).
    assert (eg : forall φ, eWeyl (g φ) = φ).
    { intro φ. apply ptw_inv. intros [y v]. exact (trp_path_GSet (G := G) _ y v). }
    refine (iso_to_isEquiv _ g _ eg).
    intro f. apply eWeyl_inj. intro w. exact (ptw (eg (eWeyl f)) w).
  Defined.

End Weyl.
