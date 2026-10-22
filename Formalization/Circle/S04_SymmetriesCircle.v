(** * Section 3.4 The symmetries in the circle

    Part of Chapter 3 ([circle.tex]); see [Circle.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Transport in [R] along [loop] is the successor [zs], along [loop⁻¹]
      the predecessor (univalence made transparent,
      [rem:univalence-transparent]).
    - Powers [loop^n] for [n : ℤ] are the library's [loopexp] on [Int],
      via [toInt]: [loop^n :≡ loopexp loop (toInt n)].
    - [def:fPtoR] ([fPR]), [lem:windingnumber] ([winding]),
      [def:gRtoP] ([gRP], by circle induction), and [lem:univisexp]
      ([univisexp : (base = z) ≃ R(z)]); hence [uc_base = R].
    - [cor:S1groupoid]: [S1] is a groupoid and [n ↦ loop^n] is an
      equivalence.
    - [cor:univ-covers-S1]: [uc_base] and [exp] are universal coverings.
    - [def:windingnumber]: [wdg : (base = base) ≃ ℤ].
    - [lem:S1-delooping], following the book: [ap ě = e] on powers of
      [loop], then [conn_isEquiv_iff_point] (2.17).
    - Exercise [xca:general-winding]: [wdg_x : (x = x) ≃ ℤ] by circle
      induction (the loop case uses that every loop commutes with [loop]),
      and equivalences [f_x : S1 ≃ S1] with [f_x(base) ≡ x] ([rot]).
    - Exercise [xca:S1=S1-components], first part: [-id_S1] and [id_S1]
      are not in the same component ([id_negid_not_conn]).

    Left out (statements only, no proofs yet)
    - The second part of [xca:S1=S1-components]
      ([xca_S1S1_components_stmt]), which needs that the degree of an
      automorphism is [±1], and exercise [xca:(S1->S1)_(f)-eqv-S1]
      ([xca_S1S1_component_eqv_stmt]). *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Colimits.Coeq Colimits.Pushout
  Spaces.Nat.Core Spaces.Int Spaces.Circle.
From SymmetryBook Require Export Circle.S03_Coverings.

Local Open Scope uf_scope.

(** ** 3.4 The symmetries in the circle *)

Section SymmetriesCircle.

  Context `{Univalence}.

  (** Remark [rem:univalence-transparent], applied: transport in [R]
      along [loop] is the successor, along [loop⁻¹] the predecessor (with
      univalence transparent, [R(loop) = zs]). *)
  Definition trp_R_loop (y : ℤ) : trp R loop y = zs y.
  Proof.
    refine (transport_compose idmap R loop y @ _).
    refine (ap (fun r => transport idmap r y) (S1_rec_loop Type ℤ (etop zsEqv)) @ _).
    exact (ptw (ap fst (ptoe_etop zsEqv)) y).
  Defined.

  Definition trp_R_loopV (y : ℤ) : trp R loop⁻¹ y = zp y
    := (zp_zs _)^ @ ap zp ((trp_R_loop _)^ @ transport_pV R loop y).

  (** Powers [loop^n] for [n : ℤ], via the library's [loopexp] on [Int]:
      [loop^n :≡ loopexp loop (toInt n)], so that [loop^{n+1} = loop · loop^n]. *)
  Definition loopZ (n : ℤ) : base = base := loopexp loop (toInt n).

  Definition loopZ_0 : loopZ (iplus 0) = refl := refl.

  Definition loopZ_zs (n : ℤ) : loopZ (zs n) = loop ⋅ loopZ n
    := ap (loopexp loop) (toInt_zs n) @ loopexp_succ_r loop _
       @ (trans_is_concat _ _)^.

  Definition fromInt_succ (x : Int) : fromInt (int_succ x) = zs (fromInt x)
    := toInt_inj (toInt_fromInt _ @ ap int_succ (toInt_fromInt x)^ @ (toInt_zs _)^).

  Definition fromInt_pred (x : Int) : fromInt (int_pred x) = zp (fromInt x)
    := toInt_inj (toInt_fromInt _ @ ap int_pred (toInt_fromInt x)^ @ (toInt_zp _)^).

  (** Definition [def:fPtoR]: [f(z)(p) :≡ R(p)(0)]. *)
  Definition fPR (z : S1) (p : base = z) : R z := trp R p (iplus 0).

  (** Lemma [lem:windingnumber]. *)
  Definition winding_Int (x : Int) : fPR base (loopexp loop x) = fromInt x.
  Proof.
    unfold fPR. induction x as [|n IH|n IH] using Int_ind.
    - exact refl.
    - refine (ap (fun r : base = base => trp R r (iplus 0)) (loopexp_succ_r loop _) @ _).
      refine (transport_pp R _ _ _ @ _).
      exact (trp_R_loop _ @ ap zs IH @ (fromInt_succ _)^).
    - refine (ap (fun r : base = base => trp R r (iplus 0)) (loopexp_pred_r loop _) @ _).
      refine (transport_pp R _ _ _ @ _).
      exact (trp_R_loopV _ @ ap zp IH @ (fromInt_pred _)^).
  Defined.

  Definition winding (n : ℤ) : fPR base (loopZ n) = n
    := winding_Int (toInt n) @ fromInt_toInt n.

  (** Definition [def:gRtoP], by circle induction, with [g(base)(n) :≡
      loop^n] and [g(loop)] obtained from [loop · loop^{n-1} = loop^n]. *)
  Definition gRP_loop
    : PathOver (fun z => R z -> base = z) loop loopZ loopZ.
  Proof.
    apply ptw_inv. intro y.
    refine (trp_fun (Y := R) (Z := fun z => base = z) loop loopZ y @ _).
    refine (trp_paths_l base loop _ @ _).
    exact (ap (fun r => loop ⋅ loopZ r) (trp_R_loopV y) @ (loopZ_zs _)^
           @ ap loopZ (zs_zp y)).
  Defined.

  Definition gRP : forall z : S1, R z -> base = z
    := S1_ind (fun z => R z -> base = z) loopZ gRP_loop.

  (** Theorem [lem:univisexp]. *)
  Definition gRP_fPR (z : S1) (p : base = z) : gRP z (fPR z p) = p.
  Proof. destruct p. exact refl. Defined.

  Definition fPR_gRP (z : S1) (n : R z) : fPR z (gRP z n) = n.
  Proof.
    revert z n.
    refine (S1_ind_prop (fun z => forall n : R z, fPR z (gRP z n) = n)
              (fun z => Pi_isProp (fun n => R_isSet z _ _)) _).
    exact winding.
  Defined.

  Definition univisexp (z : S1) : (base = z) ≃ R z
    := mkEqv (fPR z) (gRP z) (gRP_fPR z) (fPR_gRP z).

  (** Hence the universal covering [uc_base] and [R] are identified. *)
  Definition uc_R : uc base = R := ptw_inv (fun z => etop (univisexp z)).

  (** Corollary [cor:S1groupoid]. *)
  Definition S1_base_paths_isSet (z : S1) : isSet (base = z)
    := is_ntype_Eqv 0 (Eqv_inv (univisexp z)) (R_isSet z).

  Definition S1_isGrpd : isGrpd S1.
  Proof.
    intro y. refine (ptrunc_rec (Pi_isProp (fun z => isSet_isProp _)) _ (S1_base_paths y)).
    intro p. destruct p. exact S1_base_paths_isSet.
  Defined.

  Definition loopZ_isEquiv : isEquiv loopZ
    := iso_to_isEquiv loopZ (fPR base) winding (gRP_fPR base).

  (** Corollary [cor:univ-covers-S1]. *)
  Definition ucStar : Ustar := (Tot (uc base); (base; refl)).

  Definition ucp : ucStar →* S1star := (@fst S1 (uc base); refl).

  Definition uc_isUnivCovering : isUnivCovering ucp
    := contr_univCovering ucp (singleton_contr base).

  Definition TotR_isContr : isContr (Tot R)
    := isContr_Eqv (tot (fun z => fPR z); tot_isEquiv _ (fun z => snd (univisexp z)))
         (singleton_contr base).

  Definition exp_isUnivCovering : isUnivCovering exp
    := contr_univCovering exp TotR_isContr.

  (** Definition [def:windingnumber]. *)
  Definition wdg : (base = base) ≃ ℤ := univisexp base.

  Definition wdg_loopZ (n : ℤ) : fst wdg (loopZ n) = n := winding n.

  Definition loopZ_wdg (p : base = base) : loopZ (fst wdg p) = p := gRP_fPR base p.

  (** Lemma [lem:S1-delooping]. *)
  Section Delooping.

    Context {A : Type} (cA : isConn A) (a : A) (e : (base = base) -> (a = a))
      (te : isEquiv e) (e1 : e refl = refl)
      (em : forall p q : base = base, e (p ⋅ q) = e p ⋅ e q).

    Definition ecS1 : S1 -> A := S1_rec A a (e loop).

    Definition e_concat (p q : base = base) : e (p @ q) = e p @ e q
      := ap e (trans_is_concat p q)^ @ em q p @ trans_is_concat _ _.

    Definition e_inv (p : base = base) : e p^ = (e p)^.
    Proof.
      apply moveL_V1. exact ((e_concat p p^)^ @ ap e (concat_pV p) @ e1).
    Defined.

    Definition e_loopexp (x : Int) : e (loopexp loop x) = loopexp (e loop) x.
    Proof.
      induction x as [|n IH|n IH] using Int_ind.
      - exact e1.
      - exact (ap e (loopexp_succ_r loop _) @ e_concat _ _
               @ ap (fun r => r @ e loop) IH @ (loopexp_succ_r _ _)^).
      - exact (ap e (loopexp_pred_r loop _) @ e_concat _ _
               @ ap011 concat IH (e_inv loop) @ (loopexp_pred_r _ _)^).
    Defined.

    Definition ap_ecS1 (p : base = base) : ap ecS1 p = e p.
    Proof.
      refine (ap (ap ecS1) (loopZ_wdg p)^ @ _ @ ap e (loopZ_wdg p)).
      exact (ap_loopexp ecS1 loop _ @ ap (fun r => loopexp r _) (S1_rec_loop _ _ _)
             @ (e_loopexp _)^).
    Defined.

    Definition ecS1_isEquiv : isEquiv ecS1
      := snd (conn_isEquiv_iff_point ecS1 S1_isConn cA base)
           (trp isEquiv (ptw_inv ap_ecS1)^ te).

  End Delooping.

  (** Exercise [xca:general-winding]. *)
  Definition loop_comm (q : base = base) : loop @ q = q @ loop.
  Proof.
    refine (ap (concat loop) (loopZ_wdg q)^ @ _ @ ap (fun r => r @ loop) (loopZ_wdg q)).
    exact ((loopexp_succ_l loop _)^ @ loopexp_succ_r loop _).
  Defined.

  Definition trp_Eqv_dom {X : Type} (Y : X -> Type) (Z : Type) {x x' : X}
    (p : x = x') (f : Y x ≃ Z) (y : Y x')
    : fst (trp (fun x => Y x ≃ Z) p f) y = fst f (trp Y p⁻¹ y).
  Proof. destruct p. exact refl. Defined.

  Definition wdgx_loop : PathOver (fun x => (x = x) ≃ ℤ) loop wdg wdg.
  Proof.
    apply path_Eqv, ptw_inv. intro q.
    refine (trp_Eqv_dom (fun x => x = x) ℤ loop wdg q @ _). apply ap.
    refine (transport_paths_lr loop^ q @ _).
    refine (ap (fun r => r @ q @ loop^) (inv_V loop) @ _).
    exact (ap (fun r => r @ loop^) (loop_comm q) @ concat_pp_V q loop).
  Defined.

  Definition wdgx : forall x : S1, (x = x) ≃ ℤ
    := S1_ind (fun x => (x = x) ≃ ℤ) wdg wdgx_loop.

  Definition wdgx_base : wdgx base = wdg := refl.

  (** The rotations [f_x : S1 ≃ S1] with [f_x(base) ≡ x], from
      [lem:S1-delooping] applied to [wdg_x⁻¹ ∘ wdg]. *)
  Definition ex (x : S1) : (base = base) -> (x = x)
    := fun p => eqinv (snd (wdgx x)) (fst wdg p).

  Definition ex_isEquiv (x : S1) : isEquiv (ex x)
    := comp_isEquiv (snd wdg) (eqinv_isEquiv (snd (wdgx x))).

  Definition ex_hom (x : S1)
    : (ex x refl = refl) × (forall p q, ex x (p ⋅ q) = ex x p ⋅ ex x q).
  Proof.
    revert x.
    refine (S1_ind_prop _ (fun x => prod_isProp (S1_isGrpd x x _ _)
              (Pi_isProp (fun p => Pi_isProp (fun q => S1_isGrpd x x _ _)))) _).
    pose (h := eqinv_l (snd wdg) : forall p, ex base p = p).
    exact (h refl; fun p q => h (p ⋅ q) @ ap011 (fun r s => r ⋅ s) (h p)^ (h q)^).
  Defined.

  Definition rot (x : S1) : S1 -> S1 := ecS1 x (ex x).

  Definition rot_base (x : S1) : rot x base = x := refl.

  Definition rot_isEquiv (x : S1) : isEquiv (rot x)
    := ecS1_isEquiv S1_isConn x (ex x) (ex_isEquiv x) (fst (ex_hom x)) (snd (ex_hom x)).

  (** Exercise [xca:S1=S1-components], first part: [-id_S1] and [id_S1] are
      not in the same component of [S1 → S1]. *)
  Definition negid : S1 -> S1 := S1_rec S1 base loop⁻¹.

  Definition wdg_loop : fst wdg loop = iplus 1
    := ap (fst wdg) (concat_1p loop)^ @ wdg_loopZ (iplus 1).

  Definition wdg_loopV : fst wdg loop⁻¹ = iminus (negN 1)
    := ap (fst wdg) (concat_1p loop^)^ @ wdg_loopZ (iminus (negN 1)).

  Definition iplus1_ne_iminus1 : iplus 1 ≠ iminus (negN 1)
    := fun e => match ap toInt e in (_ = y)
                      return (match y with posS _ => True | _ => False end) with
                | refl => tt
                end.

  Definition id_negid_not_conn : ¬ ptrunc (idmap = negid).
  Proof.
    refine (ptrunc_rec False_isProp _). intro h.
    pose (q := ptw h base : base = base).
    pose (nat := concat_Ap (ptw h) loop : ap idmap loop @ q = q @ ap negid loop).
    pose (r := (ap (fun r => r @ q) (ap_idmap loop))^ @ nat
               @ ap (concat q) (S1_rec_loop S1 base loop⁻¹) : loop @ q = q @ loop^).
    pose (l := cancelL q _ _ ((loop_comm q)^ @ r) : loop = loop^).
    exact (iplus1_ne_iminus1 (wdg_loop^ @ ap (fst wdg) l @ wdg_loopV)).
  Defined.

  (** Exercise [xca:S1=S1-components], second part (statement only):
      every automorphism of [S1] is merely [id] or [-id]. *)
  Definition xca_S1S1_components_stmt : Type
    := forall t : S1 ≃ S1, ptrunc (idmap = fst t) ⨿ ptrunc (negid = fst t).

  (** Exercise [xca:(S1->S1)_(f)-eqv-S1] (statement only). *)
  Definition xca_S1S1_component_eqv_stmt : Type
    := forall f : S1 -> S1, S1 ≃ component (S1 -> S1) f.

End SymmetriesCircle.
