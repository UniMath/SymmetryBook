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
      are not in the same component ([id_negid_not_conn]); second part:
      every automorphism [t] is merely [id] or [-id]
      ([xca_S1S1_components]).  Conjugating [ap_t] with a path
      [base = t(base)] gives an automorphism of [base = base] preserving
      composition ([autphi]); its degree [d] ([autdeg]) satisfies [dn = 1]
      for some [n], so [d = ±1] ([int_mul_eq_one]).
    - Exercise [xca:(S1->S1)_(f)-eqv-S1] ([xca_S1S1_component_eqv]), with
      [lem:S1-delooping] as in the hint: the loops at [(f, |refl|)] are
      the pointwise rotations [x ↦ ex(f(x))(p)] ([eS1]), since evaluation
      at [base] is an equivalence from [∏_x (f(x) = f(x))] to
      [f(base) = f(base)] ([ev_base_S1_isEquiv]). *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Types.Sum Truncations.Core Colimits.Coeq Colimits.Pushout
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

  (** Exercise [xca:S1=S1-components], second part: every automorphism
      [t] of [S1] is merely [id] or [-id].  Since [S1] is connected we may
      assume [p : base = t(base)]; conjugating [ap_t] with [p] gives an
      automorphism [φ] of [base = base] that preserves composition, hence
      [φ(loop^n) = φ(loop)^n].  Writing [φ(loop) = loop^d], surjectivity of
      [φ] gives [n] with [loop^{dn} = loop], so [dn = 1] and [d = ±1]; then
      [p] extends to a homotopy [id ~ t] or [-id ~ t].  The two cases
      exclude each other by the first part, so the sum is a proposition. *)
  Definition loopexp_unique {A : Type} {x : A} (r : x = x) (f g : Int -> x = x)
    (f0 : f zero = g zero) (fs : forall n, f (int_succ n) = f n @ r)
    (gs : forall n, g (int_succ n) = g n @ r)
    : forall n, f n = g n.
  Proof.
    induction n as [|n IH|n IH] using Int_ind.
    - exact f0.
    - exact (fs _ @ ap (fun s => s @ r) IH @ (gs _)^).
    - pose (m := int_pred (int_neg (int_of_nat n))).
      refine (cancelR _ _ r _).
      refine ((fs m)^ @ _ @ gs m).
      refine (ap f (int_pred_succ _) @ IH @ ap g (int_pred_succ _)^).
  Defined.

  Definition loopexp_mul {A : Type} {x : A} (p : x = x) (a b : Int)
    : loopexp (loopexp p a) b = loopexp p (int_mul a b).
  Proof.
    revert b. refine (loopexp_unique (loopexp p a) _ _ _ _ _).
    - exact (ap (loopexp p) (int_mul_0_r a))^.
    - intro n. exact (loopexp_succ_r _ _).
    - intro n. refine (ap (loopexp p) (int_mul_succ_r a n @ int_add_comm _ _) @ _).
      exact (loopexp_add p _ _).
  Defined.

  Definition int_mul_posS (a b : nat)
    : int_mul (posS a) (posS b) = posS (b + a * S b)%nat
    := int_nat_mul (S a) (S b).

  Definition posS_inj {a b : nat} (e : posS a = posS b) : a = b
    := ap (fun x => match x with posS n => n | _ => a end) e.

  Definition posS_ne_negS (a b : nat) : posS a <> negS b
    := fun e => transport (fun x => match x with posS _ => Unit | _ => Empty end) e tt.

  Definition posS_ne_zero (a : nat) : posS a <> zero
    := fun e => transport (fun x => match x with posS _ => Unit | _ => Empty end) e tt.

  Definition mul_succ_zero (a b : nat) (e : (b + a * S b)%nat = 0%nat) : a = 0%nat.
  Proof.
    destruct a as [|a]. - exact idpath.
    - destruct b; destruct (transport (fun n : nat => match n with O => Empty | S _ => Unit end) e tt).
  Defined.

  Definition int_mul_eq_one (x y : Int) (e : int_mul x y = posS 0)
    : (x = posS 0) + (x = negS 0).
  Proof.
    destruct x as [a| |a], y as [b| |b].
    - right. change (int_mul (int_neg (posS a)) (int_neg (posS b)) = posS 0) in e.
      rewrite int_mul_neg_l, int_mul_neg_r, int_neg_neg, int_mul_posS in e.
      exact (ap negS (mul_succ_zero a b (posS_inj e))).
    - destruct (posS_ne_zero 0 (e^ @ int_mul_0_r _)).
    - change (int_mul (int_neg (posS a)) (posS b) = posS 0) in e.
      rewrite int_mul_neg_l, int_mul_posS in e. destruct (posS_ne_negS _ _ e^).
    - destruct (posS_ne_zero 0 e^).
    - destruct (posS_ne_zero 0 e^).
    - destruct (posS_ne_zero 0 e^).
    - change (int_mul (posS a) (int_neg (posS b)) = posS 0) in e.
      rewrite int_mul_neg_r, int_mul_posS in e. destruct (posS_ne_negS _ _ e^).
    - destruct (posS_ne_zero 0 (e^ @ int_mul_0_r _)).
    - left. rewrite int_mul_posS in e.
      exact (ap posS (mul_succ_zero a b (posS_inj e))).
  Defined.

  Definition conj_loop_back {y z : S1} (p : y = z) (s : z = z) (l : y = y)
    (E : p @ s @ p^ = l) : l^ @ p @ s = p.
  Proof.
    destruct E. destruct p. rewrite concat_p1, concat_1p, concat_p1. apply concat_Vp.
  Defined.

  Definition loopexp_loop_inj (a b : Int) (e : loopexp loop a = loopexp loop b) : a = b
    := (toInt_fromInt a)^ @ ap toInt ((wdg_loopZ (fromInt a))^
         @ ap (fun r => fst wdg (loopexp loop r)) (toInt_fromInt a) @ ap (fst wdg) e
         @ ap (fun r => fst wdg (loopexp loop r)) (toInt_fromInt b)^ @ wdg_loopZ (fromInt b))
       @ toInt_fromInt b.

  Section Deg.
    Variables (t : S1 ≃ S1) (p : base = fst t base).

    Definition autphi (q : base = base) : base = base := p @ ap (fst t) q @ p^.

    Definition autphi_pp (q r : base = base) : autphi (q @ r) = autphi q @ autphi r.
    Proof.
      unfold autphi. rewrite ap_pp. rewrite !concat_pp_p. apply ap. apply ap.
      rewrite concat_V_pp. reflexivity.
    Defined.

    Definition autphi_1 : autphi 1 = 1 := ap (fun r => r @ p^) (concat_p1 p) @ concat_pV p.

    Definition autphi_loopexp (q : base = base) (n : Int)
      : autphi (loopexp q n) = loopexp (autphi q) n.
    Proof.
      revert n. refine (loopexp_unique (autphi q) _ _ autphi_1 _ _).
      - intro n. exact (ap autphi (loopexp_succ_r q n) @ autphi_pp _ _).
      - intro n. exact (loopexp_succ_r _ _).
    Defined.

    Definition autphi_isEquiv : IsEquiv autphi.
    Proof.
      pose (ht := IsEquiv_of_isEquiv (snd t)).
      assert (hc : IsEquiv (fun s : fst t base = fst t base => p @ s @ p^)).
      { exact (isequiv_compose (fun s : fst t base = fst t base => p @ s)
                 (fun u : base = fst t base => u @ p^)). }
      exact (isequiv_compose (ap (fst t) (x := base) (y := base)) (fun s => p @ s @ p^)).
    Defined.

    Definition autdeg : Int := toInt (fst wdg (autphi loop)).

    Definition autphi_loop : autphi loop = loopexp loop autdeg := (loopZ_wdg (autphi loop))^.

    Definition autdeg_unit : (autdeg = posS 0) + (autdeg = negS 0).
    Proof.
      pose (r := @equiv_inv _ _ autphi autphi_isEquiv loop).
      pose (n := toInt (fst wdg r)).
      apply (int_mul_eq_one autdeg n).
      apply loopexp_loop_inj.
      refine ((loopexp_mul _ _ _)^ @ _).
      refine (ap (fun s => loopexp s n) autphi_loop^ @ _).
      refine ((autphi_loopexp _ _)^ @ _).
      refine (ap autphi (loopZ_wdg r) @ eisretr autphi loop @ _).
      exact ((concat_1p _)^ @ (loopexp_succ_r loop zero)^).
    Defined.
  End Deg.

  Definition xca_S1S1_components (t : S1 ≃ S1)
    : ptrunc (idmap = fst t) ⨿ ptrunc (negid = fst t).
  Proof.
    assert (hP : isProp (ptrunc (idmap = fst t) ⨿ ptrunc (negid = fst t))).
    { refine (@IsHProp_isProp _ _). srapply ishprop_sum; try exact (isProp_IsHProp ptrunc_isProp).
      intros a b. apply id_negid_not_conn.
      refine (ptrunc_rec ptrunc_isProp _ a). intro a'.
      refine (ptrunc_rec ptrunc_isProp _ b). intro b'.
      exact (trunc (a' @ b'^)). }
    refine (ptrunc_rec hP _ (snd S1_isConn base (fst t base))). intro p.
    destruct (autdeg_unit t p) as [d|d].
    - left. apply trunc. apply ptw_inv.
      refine (S1_ind (fun x => x = fst t x) p _).
      refine (transport_paths_FlFr loop p @ _).
      refine (ap (fun r => r^ @ p @ _) (ap_idmap loop) @ _).
      apply conj_loop_back.
      exact (autphi_loop t p @ ap (loopexp loop) d @ loopexp_succ_r loop zero @ concat_1p _).
    - right. apply trunc. apply ptw_inv.
      refine (S1_ind (fun x => negid x = fst t x) p _).
      refine (transport_paths_FlFr loop p @ _).
      refine (ap (fun r => r^ @ p @ _) (S1_rec_loop S1 base loop^) @ _).
      apply conj_loop_back.
      exact (autphi_loop t p @ ap (loopexp loop) d @ loopexp_pred_r loop zero @ concat_1p _).
  Defined.

  (** Exercise [xca:(S1->S1)_(f)-eqv-S1], with [lem:S1-delooping] as in the
      hint, at the point [(f, |refl|)] of the component.  The map
      [e : (base = base) → ((f, |refl|) = (f, |refl|))] sends [p] to the
      pointwise rotation [x ↦ ex(f(x))(p)] (from [xca:general-winding]); it
      is an equivalence since evaluating at [base] is an equivalence from
      [∏_x (f(x) = f(x))] to [f(base) = f(base)] (all loops in [S1]
      commute), and it preserves composition since [ex] does. *)
  Section ComponentEqv.

    Variable f : S1 -> S1.

    Local Instance ptrunc_IsHProp (T : Type) : IsHProp (ptrunc T)
      := isProp_IsHProp ptrunc_isProp.

    Definition S1_loops_comm_base (u v : base = base) : u @ v = v @ u.
    Proof.
      refine (ap011 concat (loopZ_wdg u)^ (loopZ_wdg v)^ @ _
              @ ap011 concat (loopZ_wdg v) (loopZ_wdg u)).
      unfold loopZ. refine ((loopexp_add _ _ _)^ @ ap (loopexp loop) (int_add_comm _ _) @ loopexp_add _ _ _).
    Defined.

    Definition S1_loops_comm (y : S1) (u v : y = y) : u @ v = v @ u.
    Proof.
      revert y u v.
      refine (S1_ind_prop _ _ S1_loops_comm_base).
      intro y. apply Pi_isProp. intro u. apply Pi_isProp. intro v. exact (S1_isGrpd y y _ _).
    Defined.


    Definition ev_base_S1 (s : forall x, f x = f x) : f base = f base := s base.

    Definition ext_base_S1 (q : f base = f base) : forall x, f x = f x
      := S1_ind (fun x => f x = f x) q
           (transport_paths_FlFr loop q
            @ ap (fun r => r @ ap f loop) (S1_loops_comm _ _ _)
            @ concat_pp_p _ _ _ @ ap (concat q) (concat_Vp _) @ concat_p1 q).

    Definition ev_base_S1_isEquiv : IsEquiv ev_base_S1.
    Proof.
      refine (isequiv_adjointify ev_base_S1 ext_base_S1 (fun q => idpath) _).
      intro s. apply path_forall.
      refine (S1_ind_prop (fun x => ext_base_S1 (ev_base_S1 s) x = s x) _ idpath).
      intro x. exact (S1_isGrpd _ _ _ _).
    Defined.

    Definition hS1 (p : base = base) : forall x, f x = f x := fun x => ex (f x) p.

    Definition hS1_isEquiv : IsEquiv hS1.
    Proof.
      pose (ev := ev_base_S1_isEquiv).
      pose (exb := IsEquiv_of_isEquiv (ex_isEquiv (f base))).
      exact (@cancelL_isequiv _ _ _ ev_base_S1 hS1 ev exb).
    Defined.

    Definition aS1 : component (S1 -> S1) f := (f; trunc refl).

    Definition apfst_isEquiv : IsEquiv (@ap _ _ (@pr1 (S1 -> S1) (fun g => ptrunc (f = g))) aS1 aS1)
      := isequiv_ap_pr1_hprop aS1 aS1.

    Definition eS1 (p : base = base) : aS1 = aS1
      := @equiv_inv _ _ _ apfst_isEquiv (path_forall _ _ (hS1 p)).

    Definition eS1_isEquiv : IsEquiv eS1.
    Proof.
      pose (h := hS1_isEquiv).
      pose (i := @isequiv_inverse _ _ _ apfst_isEquiv).
      pose (j := @isequiv_compose _ _ _ hS1 h (path_forall f f) _).
      exact (@isequiv_compose _ _ _ (fun p => path_forall _ _ (hS1 p)) j _ i).
    Defined.

    Definition eS1_concat (p q : base = base) : eS1 (p @ q) = eS1 p @ eS1 q.
    Proof.
      apply (equiv_inj (ap pr1)). refine (eisretr (ap pr1) _ @ _ @ (ap_pp _ _ _)^).
      refine (_ @ ap011 concat (eisretr (ap pr1) _)^ (eisretr (ap pr1) _)^).
      refine (ap (path_forall _ _) _ @ path_forall_pp _ _ _ _ _).
      apply path_forall. intro x. unfold hS1.
      exact (ap (ex (f x)) (trans_is_concat p q)^ @ snd (ex_hom (f x)) q p @ trans_is_concat _ _).
    Defined.

    Definition eS1_1 : eS1 refl = refl.
    Proof.
      apply (equiv_inj (ap pr1)). refine (eisretr (ap pr1) _ @ _).
      refine (ap (path_forall _ _) _ @ path_forall_1 f).
      apply path_forall. intro x. exact (fst (ex_hom (f x))).
    Defined.

    Definition xca_S1S1_component_eqv : S1 ≃ component (S1 -> S1) f.
    Proof.
      refine (ecS1 aS1 eS1; ecS1_isEquiv (component_isConn f) aS1 eS1
                (isEquiv_of_IsEquiv eS1 (H := eS1_isEquiv)) eS1_1 _).
      intros p q. exact (ap eS1 (trans_is_concat q p) @ eS1_concat q p @ (trans_is_concat _ _)^).
    Defined.

  End ComponentEqv.

End SymmetriesCircle.
