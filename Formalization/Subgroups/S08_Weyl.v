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
    - Parts of the lemma after the unpacking: [p_G^H] is an epimorphism
      ([pN_isepi]: every [e : X = X] merely comes from a loop at
      [(sh_G, X, pt)], [W_loops]), [i_H = i_G^H j_H] ([iH_jH]), and hence
      [j_H] is a monomorphism ([jH_ismono]).

    Left out (statements only)
    - The remaining part of the lemma after the unpacking,
      [ker p_G^H = (H, j_H)] (the statement [normalizer_lemma_stmt] is
      the whole lemma).
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
      ([iN_ismono]); [p_G^H] is an epimorphism ([pN_isepi] below),
      [ker p_G^H = (H, j_H)] as subgroups of [N_G H] (not proved), and
      [i_H = i_G^H j_H] ([iH_jH] below). *)
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

  (** Parts of [normalizer_lemma_stmt].  [p_G^H] is an epimorphism: every
      [e : X = X] is merely the image of a loop at [(sh_G, S)], the
      composite of [(sh_G, X, pt) = (sh_G, X, g·pt)] over a [g] with
      [g·pt = e⁻¹(pt)] ([sub_move]) and [(X, g·pt) = (X, pt)] given by [e]
      ([W_loops]). *)
  Definition sgX_SubGrp_path {Y Y' : GSet G} {x : el Y (sh G)} {y : el Y' (sh G)}
    {t : istrans Y} {t' : istrans Y'} (α : Y = Y')
    (h : trp (fun Y0 : GSet G => el Y0 (sh G)) α x = y)
    : ap (fun s : SubGrp G => sg_X s) (SubGrp_path (t := t) (t' := t') α h) = α.
  Proof.
    destruct α. destruct h.
    exact ((ap_compose (fun t0 => (Y; (x; t0)) : SubGrp G) (fun s : SubGrp G => sg_X s)
              (istrans_isProp Y t t'))^ @ ap_const (istrans_isProp Y t t') Y).
  Defined.

  Definition sub_move {y y' : utype (BG G)} (g : y = y') (x : el X y)
    (t : istrans (G := regroup G y) X) (t' : istrans (G := regroup G y') X)
    : {L : ((y; (X; (x; t))) : SubTot) = (y'; (X; (act X g x; t'))) &
        ap (fun v : SubTot => sg_X (snd v) : GSet G) L = refl}.
  Proof.
    destruct g. exists (ap (fun s => (y; (X; (x; s))) : SubTot) (istrans_isProp (G := regroup G y) X t t')).
    exact ((ap_compose (fun s => (y; (X; (x; s))) : SubTot) (fun v : SubTot => sg_X (snd v) : GSet G)
              (istrans_isProp (G := regroup G y) X t t'))^ @ ap_const (istrans_isProp (G := regroup G y) X t t') X).
  Defined.

  Definition W_loops (e : X = X)
    : ptrunc {L : ((sh G; S) : SubTot) = (sh G; S) &
               ap (fun v : SubTot => sg_X (snd v) : GSet G) L = e}.
  Proof.
    pose (x := trp (fun Z : GSet G => el Z (sh G)) e^ (sg_pt S)).
    refine (ptrunc_rec ptrunc_isProp _
              (snd (conn_of_trans X (sg_trans S)) (sh G; sg_pt S) (sh G; x))).
    intro r. pose (hg := act_ap_fst X r : act X (ap fst r) (sg_pt S) = x).
    pose (L1 := sub_move (ap fst r) (sg_pt S) (sg_trans S) (sg_trans S)).
    pose (h := ap (trp (fun Z : GSet G => el Z (sh G)) e) hg
               @ transport_pV (fun Z : GSet G => el Z (sh G)) e (sg_pt S)).
    pose (P2 := SubGrp_path (t := sg_trans S) (t' := sg_trans S) e h).
    apply trunc. exists (fst L1 @ ap (fun s => (sh G; s) : SubTot) P2).
    refine (ap_pp (fun v : SubTot => sg_X (snd v) : GSet G) (fst L1)
              (ap (fun s => (sh G; s) : SubTot) P2)
            @ ap011 concat (snd L1) _ @ concat_1p _).
    exact ((ap_compose (fun s => (sh G; s) : SubTot) (fun v : SubTot => sg_X (snd v) : GSet G) P2)^
           @ sgX_SubGrp_path e h).
  Defined.

  Definition pN_isepi : isepi pN.
  Proof.
    apply surj_isepi. apply (ap_isSurj_loops (Bf pN)). intro r.
    pose (apfe := isInj_ap_isEquiv (fst_isInj (Q := fun Z : GSet G => ptrunc (X = Z))
                                               (fun _ => ptrunc_isProp))
                    (BpN (sh Normalizer)) (BpN (sh Normalizer))).
    refine (ptrunc_rec ptrunc_isProp _ (W_loops (ap fst r))). intros [L hL].
    apply trunc.
    exists (path_sigma_prop (fun _ => ptrunc_isProp) (u := sh Normalizer) (v := sh Normalizer) L).
    apply (isInj_cancel (isEquiv_isInj apfe)).
    refine (hL^ @ _).
    refine (ap (ap (fun v : SubTot => sg_X (snd v) : GSet G))
              (ap_fst_path_sigma_prop (fun _ => ptrunc_isProp)
                 (u := sh Normalizer) (v := sh Normalizer) L)^ @ _).
    refine ((ap_compose fst (fun v : SubTot => sg_X (snd v) : GSet G) _)^ @ _).
    exact (ap_compose (fst (Bf pN)) (@fst (GSet G) (fun Z => ptrunc (X = Z)))
             (path_sigma_prop (fun _ => ptrunc_isProp) (u := sh Normalizer) (v := sh Normalizer) L)).
  Defined.

  (** [i_H = i_G^H j_H]. *)
  Definition iH_jH : subgrp_incl S = compG iN jH.
  Proof.
    apply (ap mkhom).
    refine (eqinv (snd (ptw_star (Bf (subgrp_incl S)) (pcomp (Bf iN) (Bf jH))))
              ((fun w => refl); _)).
    cbn. refine (_ @ (trans_1p _)^).
    pose (BjHpt := path_sigma_prop (fun _ : SubTot => ptrunc_isProp)
                    (u := sh Normalizer) (v := BjH (sh (subgrp_group S))) phiH_pt).
    refine (_ @ (ap_compose (@fst SubTot (fun v => ptrunc (((sh G; S) : SubTot) = v)))
                   (@fst (utype (BG G)) (SubFam G)) BjHpt)^).
    refine (_ @ (ap (ap (@fst (utype (BG G)) (SubFam G)))
                   (ap_fst_path_sigma_prop (fun _ => ptrunc_isProp)
                      (u := sh Normalizer) (v := BjH (sh (subgrp_group S))) phiH_pt))^).
    exact ((ap_const (istrans_isProp X (sg_trans S) (trans_at (sh G))) (sh G))^
           @ ap_compose (fun t => (sh G; (X; (sg_pt S; t))) : SubTot) fst _).
  Defined.

  (** [j_H] is a monomorphism, since [i_G^H j_H = i_H] is one. *)
  Definition jH_ismono : ismono jH.
  Proof.
    refine (cancel_isInj (USym_isSet Normalizer) _). intros h h' e.
    apply (isInj_cancel (subgrp_incl_ismono S)).
    exact (ptw (ap USymf iH_jH) h @ loops_fun_pcomp (Bf iN) (Bf jH) h
           @ ap (USymf iN) e
           @ (loops_fun_pcomp (Bf iN) (Bf jH) h')^ @ (ptw (ap USymf iH_jH) h')^).
  Defined.

End Weyl.
