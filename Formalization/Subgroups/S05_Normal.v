(** * Section 9.5 Normal subgroups

    Part of Chapter 9 ([subgroups.tex]); see [Subgroups.v] for an
    overview of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:normalsubgroup] ([Nor], [inor]) and the remark that
      [i] is an injection ([inor_cancel], [inor_isInj], [Nor_isSet]).
    - Definition [def:setofkernels] ([kerepi], [Kern], [Kern_incl]).
    - Definition [def:ker2] ([norX], [nor]).  Transitivity of
      [P_{f(y)} f] needs [USymf f] surjective, the part of [lem:epi-surj]
      left out in 9.2; [nor] takes surjectivity as a hypothesis.
    - Definition [def:normalquotient] ([GSet_isGrpd], [QG], [qN]); the
      pointing path of [Bq_N] is [refl] up to the membership proof.
    - Definition [def:associatednormal] ([ass], via [subgrp_to_mono] of
      Section 5.3).
    - Lemma [lem:evaliseqwhennormal] ([lem_evaliseqwhennormal]): by
      connectedness of [BG] we may assume [y ≡ z]; an identification of
      [G]-sets is determined by its action ([GSet_path_ext]), for the
      transitive [X_y] by the image of [pt_y] ([nor_ev_inj]), and
      [ap_{X_-}(g)] sends [g · pt_y] to [pt_y] ([nor_ap_act], by path
      induction), which gives both surjectivities.
    - Lemma [lem:diagfornormal] ([lem_diagfornormal], with surjectivity
      of [USymf f] as hypothesis, as for [nor]): [(B ker_f)⁻¹(z) ≃
      (f(sh_G) = f(z))] ([diag_eqv]), pointed.
    - Lemma [lem:normalsarekernels] ([lem_normalsarekernels], with the
      same hypothesis): from [lem:diagfornormal] and [mono_subgrp_mono]
      of Section 9.2.
    - Lemma [lem:qeq] in the form [lem_qeq_stmt] (see the size issue
      below), with surjectivity hypotheses ([lem_qeq]): [(Bq(y) = Bq(z))
      ≃ X_y(z)] by evaluation ([qeq_eqv]), and [Q] with [BQ(w) :≡ (z ↦ (w
      = f(z)))] ([Q0], [Qhom]), so that [BQ ∘ Bf ≡ Bq] on underlying
      types ([Q_comp]); [ap_{Q0}] is inverted by evaluation at [refl]
      ([apQ0_isEquiv], [Q_isIso]).
    - That [q_N] is an epimorphism ([qN_isepi]): [U q_N] is surjective by
      the second part of [lem:evaliseqwhennormal].

    Left out (statements only)
    - Corollary [cor:normalisnormal], lemma
      [lem:characterizations of normal] (parts (1) - (3)) ([..._stmt]).
    - The map [q : Nor(G) → Epi(G)] (see the size issue below).
    - Size issue: [G/N] lives in a larger universe than [G], so
      [nor(q(N)) = N] in [Nor(G)] and [(G', f) = q(nor(f))] in [Epi(G)]
      cannot be stated; [lem_qeq_stmt] states the content of the proof
      instead (pointed equivalences of [G]-sets, and an isomorphism [Q]
      with [Q f = q_{nor f}]), and this is what is proved.
    - Informal: the remark after [def:ker2], the remark after
      [def:normalquotient] ([Y/N] and torsors), the marginal remark after
      [def:associatednormal].
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core.
From SymmetryBook Require Export Subgroups.S04_SubgroupAction.

Local Open Scope uf_scope.

(** ** 9.5 Normal subgroups *)

Section Normal.

  Context `{ua : Univalence} (G : Group).

  (** Definition [def:normalsubgroup]: the fixed points of [Sub(G)], with
      [i(N) :≡ N(sh_G)].  [Sub(mkgroup(BG_÷, sh_G))] is [Sub(G)] by
      definition. *)
  Definition Nor : Type := forall y : utype (BG G), SubFam G y.

  Definition inor (N : Nor) : SubGrp G := N (sh G).

  (** The remark after [def:normalsubgroup]: [i] is an injection, by
      connectedness of [BG]. *)
  Definition inor_cancel (N N' : Nor) (e : inor N = inor N') : N = N'.
  Proof.
    apply ptw_inv. intro y.
    refine (ptrunc_rec (SubGrp_isSet (regroup G y) _ _) _ (snd (BG_isConn G) (sh G) y)).
    intro p. destruct p. exact e.
  Defined.

  Definition Nor_isSet : isSet Nor
    := Pi_isSet (fun y => SubGrp_isSet (regroup G y)).

  Definition inor_isInj : isInj inor
    := cancel_isInj (SubGrp_isSet G) (fun N N' => inor_cancel N N').

  (** The fixed points [∏_y Mono(G)(y)] of the marginal note (informal; the
      equivalence with [Nor(G)] needs [lem:SubG=MonoG]). *)

  (** Definition [def:setofkernels]: the set of kernels is the image of
      [ker] restricted to the epimorphisms. *)
  Definition kerepi (e : Epi G) : Mono G := ker (fst (snd e)).

  Definition Kern : Type := im kerepi.

  Definition Kern_incl : Kern -> Mono G := fst.

End Normal.

(** Definition [def:ker2]: [nor(G', f, !)(y) :≡ (P_{f(y)} f, refl, !)], with
    [P_{f(y)} f(z) :≡ (f(y) = f(z))].  Transitivity uses that [USymf f]
    is surjective, which for an epimorphism is the part of
    [lem:epi-surj] left out in Section 9.2 ([epi_surjection_stmt]); we
    take surjectivity as a hypothesis. *)
Section Nor.

  Context `{ua : Univalence} {G H : Group} (f : Hom G H) (s : isSurj (USymf f)).

  Local Notation k0 := (fst (Bf f)).

  Definition ap_isSurj_all (y : utype (BG G)) : isSurj (@ap _ _ k0 y y).
  Proof.
    refine (ptrunc_rec (Pi_isProp (fun _ => ptrunc_isProp)) _ (snd (BG_isConn G) (sh G) y)).
    intro p. destruct p. exact (loops_isSurj_ap (Bf f) s).
  Defined.

  Definition norX (y : utype (BG G)) : GSet G := fun z => ((k0 y = k0 z); BG_isGrpd H _ _).

  Definition act_norX {y z z' : utype (BG G)} (g : z = z') (q : k0 y = k0 z)
    : act (norX y) g q = q @ ap k0 g.
  Proof. destruct g. exact (concat_p1 q)^. Defined.

  Definition norX_trans (y : utype (BG G)) : istrans (G := regroup G y) (norX y).
  Proof.
    apply trunc. exists (refl : el (norX y) y). intro q.
    refine (ptrunc_rec ptrunc_isProp _ (ap_isSurj_all y q^)). intros [g e].
    apply trunc. exists g. refine (_ @ (act_norX g q)^).
    exact ((concat_pV q)^ @ ap (fun r => q @ r) e).
  Defined.

  Definition nor : Nor G := fun y => (norX y; (refl; norX_trans y)).

End Nor.

(** The remark after [def:ker2]: [P_{f(y)} f] is not a [G]-torsor unless [f]
    is an isomorphism (informal). *)

(** Lemma [lem:diagfornormal] (statement; proved below): around the top,
    [E(i(ker f))] is [y ↦ (sh_{G'} = f(y))] pointed at [Bf_pt]; around the
    bottom it is [nor(f)(sh_G)]; precomposition with [Bf_pt] identifies
    them. *)
Definition lem_diagfornormal_stmt `{ua : Univalence} : Type
  := forall (G H : Group) (f : Hom G H) (s : isSurj (USymf f)),
       Emono (kermap f) (kermap_ismono f) = inor G (nor f s).

(** Proof of [lem:diagfornormal]: the fibers [(B ker_f)⁻¹(z)] are
    equivalent to [f(sh_G) = f(z)] by [((x, q), !, p) ↦ Bf_pt⁻¹ q f(p⁻¹)]
    ([diag_eqv]); the inverse needs the proof of membership in the
    component of [(sh_G, Bf_pt)], which uses that [ap_{Bf}] is surjective
    ([diag_mem]). *)
Section DiagNormal.

  Context `{ua : Univalence} {G H : Group} (f : Hom G H) (s : isSurj (USymf f)).

  Local Notation k0 := (fst (Bf f)).
  Local Notation kp := (snd (Bf f)).
  Local Notation KF := (fibGSet (kermap f) (kermap_ismono f)).

  Definition fib_shift {w : utype (BG H)} {x x' : utype (BG G)} (g : x = x') (q : w = k0 x)
    : ((x; q) : fiber k0 w) = (x'; q @ ap k0 g).
  Proof. destruct g. exact (ap (fun t => (x; t) : fiber k0 w) (concat_p1 q)^). Defined.

  Definition diag_mem (z : utype (BG G)) (r : k0 (sh G) = k0 z)
    : ptrunc (shKer f = ((z; kp @ r) : fiber k0 (sh H))).
  Proof.
    refine (ptrunc_rec ptrunc_isProp _ (snd (BG_isConn G) (sh G) z)). intro z0. destruct z0.
    refine (ptrunc_rec ptrunc_isProp _ (ap_isSurj_all f s (sh G) r)). intros [g e].
    exact (trunc (fib_shift g kp @ ap (fun t => (sh G; kp @ t) : fiber k0 (sh H)) e^)).
  Defined.

  Definition diag_fw (z : utype (BG G)) (w : el KF z) : el (sg_X (nor f s (sh G))) z
    := kp^ @ snd (fst (fst w)) @ ap k0 (snd w)^.

  Definition diag_bw (z : utype (BG G)) (r : el (sg_X (nor f s (sh G))) z) : el KF z
    := ((((z; kp @ r) : fiber k0 (sh H)); diag_mem z r); refl).

  Definition diag_pt_path (z : utype (BG G)) {q1 q2 : sh H = k0 z} (e : q1 = q2)
    (c1 : ptrunc (shKer f = (z; q1))) (c2 : ptrunc (shKer f = (z; q2)))
    : ((((z; q1) : fiber k0 (sh H)); c1); refl) = (((((z; q2) : fiber k0 (sh H)); c2); refl) : el KF z).
  Proof. destruct e. exact (ap (fun c => ((((z; q1) : fiber k0 (sh H)); c); refl) : el KF z) (ptrunc_isProp c1 c2)). Defined.

  Definition diag_eqv (z : utype (BG G)) : el KF z ≃ el (sg_X (nor f s (sh G))) z.
  Proof.
    refine (mkEqv (diag_fw z) (diag_bw z) _ _).
    - intros [[[x q] c] p]. cbn in p. destruct p.
      exact (diag_pt_path z (ap (fun t => kp @ t) (concat_p1 _) @ concat_p_Vp kp q) _ _).
    - intro r. exact (concat_p1 _ @ concat_V_pp kp r).
  Defined.

  Definition lem_diagfornormal_pf : Emono (kermap f) (kermap_ismono f) = inor G (nor f s).
  Proof.
    refine (SubGrp_path (path_GSet diag_eqv) _).
    refine (trp_path_GSet diag_eqv (sh G) _ @ _).
    exact (concat_p1 (kp^ @ kp) @ concat_Vp kp).
  Defined.

End DiagNormal.

Definition lem_diagfornormal `{ua : Univalence} : lem_diagfornormal_stmt
  := fun G H f s => lem_diagfornormal_pf f s.

(** Lemma [lem:evaliseqwhennormal] (statement; proved below), with
    [N(y) ≡ (X_y, pt_y, !)]. *)
Definition lem_evaliseqwhennormal_stmt `{ua : Univalence} : Type
  := forall (G : Group) (N : Nor G) (y z : utype (BG G)),
       isEquiv (fun e : sg_X (N y) = sg_X (N z) => trp (fun X : GSet G => el X y) e (sg_pt (N y)))
       × isSurj (fun p : y = z => ap (fun w => sg_X (N w) : GSet G) p).

(** Lemma [lem:evaliseqwhennormal].  An identification of [G]-sets is
    determined by its action ([GSet_path_ext]); for the transitive [X_y]
    it is determined by the image of [pt_y] ([nor_ev_inj]), and
    [ap_{X_-}(p)] sends [p · pt_y] to [pt_z] ([nor_ap_act]), by induction
    on [p].  Both parts are propositions, so we may assume [y ≡ z]. *)
Definition GSet_path_ext `{ua : Univalence} {G : Group} {X Y : GSet G} (f f' : X = Y)
  (e : forall y v, trp (fun Z : GSet G => el Z y) f v = trp (fun Z : GSet G => el Z y) f' v)
  : f = f'.
Proof.
  apply (isInj_cancel (isEquiv_isInj (funext X Y))). apply ptw_inv. intro y.
  apply (isInj_cancel (isEquiv_isInj
           (isInj_ap_isEquiv (fst_isInj (fun Y => isSet_isProp Y)) (X y) (Y y)))).
  apply (isInj_cancel (isEquiv_isInj (IntroUF.S13_Univalence.ua _ _))).
  apply (path_sigma_prop (fun _ => isEquiv_isProp _)). apply ptw_inv. intro v.
  refine (_ @ e y v @ _).
  - destruct f. exact refl.
  - destruct f'. exact refl.
Defined.

Section EvalNormal.

  Context `{ua : Univalence} {G : Group} (N : Nor G).

  Local Notation XN w := (sg_X (N w) : GSet G).
  Local Notation ptN w := (sg_pt (N w) : el (XN w) w).

  Definition nor_reach (y : utype (BG G)) (a b : el (XN y) y)
    : ptrunc {q : y = y & act (XN y) q a = b}
    := ptrunc_rec ptrunc_isProp (fun r => trunc (ap fst r; act_ap_fst (XN y) r))
         (snd (conn_of_trans (G := regroup G y) (XN y) (sg_trans (N y))) (y; a) (y; b)).

  Definition nor_ap_act {y z : utype (BG G)} (p : y = z)
    : trp (fun Z : GSet G => el Z z) (ap (fun w => XN w) p) (act (XN y) p (ptN y)) = ptN z.
  Proof. destruct p. exact refl. Defined.

  Definition nor_ev_inj {y : utype (BG G)} (e e' : XN y = XN y)
    (h : trp (fun Z : GSet G => el Z y) e (ptN y) = trp (fun Z : GSet G => el Z y) e' (ptN y))
    : e = e'.
  Proof.
    apply GSet_path_ext. intros w v.
    assert (all : forall u : TotG (XN y),
               trp (fun Z : GSet G => el Z (fst u)) e (snd u)
               = trp (fun Z : GSet G => el Z (fst u)) e' (snd u)).
    { intro u.
      refine (ptrunc_rec (snd (XN y (fst u)) _ _) _
                (snd (conn_of_trans (G := regroup G y) (XN y) (sg_trans (N y))) (y; ptN y) u)).
      intro r. destruct r. exact h. }
    exact (all (w; v)).
  Defined.

  Definition nor_ap_V_pt {y : utype (BG G)} (g : y = y)
    : trp (fun Z : GSet G => el Z y) (ap (fun w => XN w) g)^ (ptN y) = act (XN y) g (ptN y)
    := (ap (trp (fun Z : GSet G => el Z y) (ap (fun w => XN w) g)^) (nor_ap_act g))^
       @ transport_Vp (fun Z : GSet G => el Z y) (ap (fun w => XN w) g) _.

End EvalNormal.

Definition lem_evaliseqwhennormal `{ua : Univalence} : lem_evaliseqwhennormal_stmt.
Proof.
  intros G N y z.
  refine (ptrunc_rec (prod_isProp (isEquiv_isProp _) (Pi_isProp (fun _ => ptrunc_isProp))) _
            (snd (BG_isConn G) y z)).
  intro p. destruct p. split.
  - apply inj_surj_isEquiv.
    + refine (cancel_isInj (snd (sg_X (N y) y)) _). intros e e' h. exact (nor_ev_inj N e e' h).
    + intro x. refine (ptrunc_rec ptrunc_isProp _ (nor_reach N y (sg_pt (N y)) x)).
      intros [g hg]. apply trunc. exists (ap (fun w => sg_X (N w) : GSet G) g)^.
      exact (hg^ @ (nor_ap_V_pt N g)^).
  - intro e.
    refine (ptrunc_rec ptrunc_isProp _
              (nor_reach N y (sg_pt (N y)) (trp (fun Z : GSet G => el Z y) e (sg_pt (N y))))).
    intros [g hg]. apply trunc. exists g^.
    apply (nor_ev_inj N). refine (hg^ @ (nor_ap_V_pt N g)^ @ _).
    exact (ap (fun r => trp (fun Z : GSet G => el Z y) r (sg_pt (N y))) (ap_V _ g)^).
Defined.

(** Definition [def:normalquotient]: [G/N :≡ Aut_{G-Set}(X_{sh_G})] and the
    quotient homomorphism [q_N], [Bq_N(z) :≡ X_z]; the pointing path is
    [refl] up to the proof of membership in the component.  That [q_N] is
    an epimorphism ([qN_isepi]) is proved via [lem:evaliseqwhennormal]. *)
Section Quotient.

  Context `{ua : Univalence} {G : Group} (N : Nor G).

  Definition GSet_isGrpd : isGrpd (GSet G) := Pi_ntype 1 (fun _ => SetU_isGrpd).

  Local Notation X := (fun y : utype (BG G) => sg_X (N y) : GSet G).

  Definition QG : Group := AutG GSet_isGrpd (X (sh G)).

  Definition Bq (z : utype (BG G)) : utype (BG QG)
    := (X z; ptrunc_rec ptrunc_isProp (fun p => trunc (ap X p)) (snd (BG_isConn G) (sh G) z)).

  Definition Bq_pt : sh QG = Bq (sh G)
    := path_sigma_prop (fun _ => ptrunc_isProp) (u := sh QG) (v := Bq (sh G)) refl.

  Definition qN : Hom G QG := @mkhom G QG (Bq; Bq_pt).

  Definition qN_isepi_stmt : Type := isepi qN.

  (** [q_N] is an epimorphism: [U q_N] is surjective since every
      identification [X_{sh_G} = X_{sh_G}] is merely [ap_X(g)]
      ([lem_evaliseqwhennormal]), and identifications in the component are
      determined by their first components. *)
  Definition qN_isepi : qN_isepi_stmt.
  Proof.
    apply surj_isepi. apply (ap_isSurj_loops (Bf qN)). intro r.
    pose (apfe := isInj_ap_isEquiv
                    (fst_isInj (Q := fun Z : GSet G => ptrunc (X (sh G) = Z)) (fun _ => ptrunc_isProp))
                    (Bq (sh G)) (Bq (sh G))).
    refine (ptrunc_rec ptrunc_isProp _ (snd (lem_evaliseqwhennormal G N (sh G) (sh G)) (ap fst r))).
    intros [p e]. apply trunc. exists p.
    apply (isInj_cancel (isEquiv_isInj apfe)).
    exact (e @ ap_compose Bq fst p).
  Defined.

End Quotient.

(** The remark after [def:normalquotient] on the quotient [Y/N] of a
    [G]-type and torsors (informal). *)

(** Lemma [lem:qeq] (statement; proved below).  Size issue: [G/N] lives in a
    larger universe than [G], so [nor(q(N))] and [N] are not elements of
    the same [Nor(G)], nor [(G', f)] and [q(nor(f))] of the same
    [Epi(G)].  We state the content of the book's proof instead:
    [nor(q(N))(y)] and [N(y)] are equivalent pointed [G]-sets (via the
    evaluation map of [lem:evaliseqwhennormal]), and [Q : G' → G/nor(f)]
    is an isomorphism with [Q f = q_{nor f}]. *)
Definition lem_qeq_stmt `{ua : Univalence} : Type
  := forall G : Group,
       (forall (N : Nor G) (s : isSurj (USymf (qN N))) (y : utype (BG G)),
          {e : forall z, el (sg_X (nor (qN N) s y)) z ≃ el (sg_X (N y)) z &
            fst (e y) (sg_pt (nor (qN N) s y)) = sg_pt (N y)})
       × (forall (H : Group) (f : Hom G H) (s : isSurj (USymf f)),
            {Q : Hom H (QG (nor f s)) & isIso Q × (compG Q f = qN (nor f s))}).

(** Proof of [lem:qeq].  First part: [(Bq(y) = Bq(z)) ≃ (X_y = X_z) ≃
    (X_z = X_y) ≃ X_y(z)], the last map by evaluation at [pt_z]
    ([lem:evaliseqwhennormal]).  Second part: [BQ(w) :≡ (z ↦ (w = f(z)))]
    ([Q0]), so that [BQ(f(y)) ≡ X_y]; [ap_{Q0}] at [f(sh_G)] is inverted
    by evaluation at [refl] ([ev_apQ0]). *)
Definition qeq_eqv `{ua : Univalence} {G : Group} (N : Nor G) (s : isSurj (USymf (qN N)))
  (y z : utype (BG G)) : el (sg_X (nor (qN N) s y)) z ≃ el (sg_X (N y)) z.
Proof.
  refine (Eqv_comp (ap fst; isInj_ap_isEquiv
                     (fst_isInj (Q := fun Z : GSet G => ptrunc (sg_X (N (sh G)) = Z))
                                (fun _ => ptrunc_isProp)) (Bq N y) (Bq N z)) _).
  refine (Eqv_comp (Eqv_of_Equiv (equiv_path_inverse _ _)) _).
  exact (_; fst (lem_evaliseqwhennormal G N z y)).
Defined.

Section QEq.

  Context `{ua : Univalence} {G H : Group} (f : Hom G H) (s : isSurj (USymf f)).

  Local Notation k0 := (fst (Bf f)).
  Local Notation kp := (snd (Bf f)).
  Local Notation Nf := (nor f s).
  Local Notation w0 := (k0 (sh G)).

  Definition Q0 (w : utype (BG H)) : GSet G := fun z => ((w = k0 z); BG_isGrpd H w (k0 z)).

  Definition BQ (w : utype (BG H)) : utype (BG (QG Nf))
    := (Q0 w; ptrunc_rec ptrunc_isProp (fun q => trunc (ap Q0 q)) (snd (BG_isConn H) w0 w)).

  Definition BQ_pt : sh (QG Nf) = BQ (sh H)
    := path_sigma_prop (fun _ => ptrunc_isProp) (u := sh (QG Nf)) (v := BQ (sh H)) (ap Q0 kp^).

  Definition Qhom : Hom H (QG Nf) := @mkhom H (QG Nf) (BQ; BQ_pt).

  Definition Q_comp : compG Qhom f = qN Nf.
  Proof.
    apply (ap mkhom).
    pose (h := fun x : utype (BG G) =>
                 path_sigma_prop (fun _ => ptrunc_isProp) (u := BQ (k0 x)) (v := Bq Nf x) refl).
    refine (eqinv (snd (ptw_star (pcomp (BQ; BQ_pt) (Bf f)) (Bq Nf; Bq_pt Nf))) (h; _)).
    apply (ap_fst_cancel (fun _ => prop_is_set ptrunc_isProp)).
    refine (ap (ap fst) (trans_is_concat _ _ @ ap (fun r => r @ h (sh G)) (trans_is_concat _ _))
            @ _).
    refine (ap_pp fst _ _ @ _ @ (ap_fst_path_sigma_prop (fun _ => ptrunc_isProp) _)^).
    refine (ap (fun r => r @ ap fst (h (sh G))) (ap_pp fst _ _) @ _).
    change ((ap fst BQ_pt @ ap fst (ap BQ kp)) @ ap fst (h (sh G)) = refl).
    pose (e1 := ap_fst_path_sigma_prop (fun _ => ptrunc_isProp)
                  (u := sh (QG Nf)) (v := BQ (sh H)) (ap Q0 kp^) : ap fst BQ_pt = ap Q0 kp^).
    pose (e3 := ap_fst_path_sigma_prop (fun _ => ptrunc_isProp)
                  (u := BQ (k0 (sh G))) (v := Bq Nf (sh G)) refl : ap fst (h (sh G)) = refl).
    refine (ap011 concat (ap011 concat e1 (ap_compose BQ fst kp)^) e3 @ concat_p1 _ @ _).
    exact (ap (fun r => r @ ap Q0 kp) (ap_V Q0 kp) @ concat_Vp _).
  Defined.

  Definition ev_apQ0 {w w' : utype (BG H)} (q : w = w') (r : w = w0)
    : trp (fun Z : GSet G => el Z (sh G)) (ap Q0 q) r = q^ @ r.
  Proof. destruct q. exact (concat_1p r)^. Defined.

  Definition apQ0_isEquiv : isEquiv (@ap _ _ Q0 w0 w0).
  Proof.
    pose (ev := fun e : Q0 w0 = Q0 w0 => trp (fun Z : GSet G => el Z (sh G)) e (refl : w0 = w0)).
    refine (snd (mkEqv (@ap _ _ Q0 w0 w0) (fun e => (ev e)^) _ _)).
    - intro p. exact (ap inverse (ev_apQ0 p refl) @ ap inverse (concat_p1 _) @ inv_V p).
    - intro e. apply (nor_ev_inj Nf (y := sh G)).
      exact (ev_apQ0 _ refl @ concat_p1 _ @ inv_V _).
  Defined.

  Definition apBQ_isEquiv : isEquiv (@ap _ _ BQ w0 w0).
  Proof.
    refine (two_of_three_f (@ap _ _ BQ w0 w0) (@ap _ _ Q0 w0 w0) (@ap _ _ fst (BQ w0) (BQ w0))
              (ptw_inv (fun p => (ap_compose BQ fst p)^)) apQ0_isEquiv _).
    exact (isInj_ap_isEquiv (fst_isInj (Q := fun Z : GSet G => ptrunc (sg_X (Nf (sh G)) = Z))
                                       (fun _ => ptrunc_isProp)) (BQ w0) (BQ w0)).
  Defined.

  Definition Q_isIso : isIso Qhom
    := snd (conn_isEquiv_iff_point BQ (BG_isConn H) (BG_isConn (QG Nf)) w0) apBQ_isEquiv.

End QEq.

Definition lem_qeq `{ua : Univalence} : lem_qeq_stmt.
Proof.
  intro G. split.
  - intros N s y. exact ((fun z => qeq_eqv N s y z); refl).
  - intros H f s. exact (Qhom f s; (Q_isIso f s; Q_comp f s)).
Defined.

(** Corollary [cor:normalisnormal] (statement only). *)
Definition cor_normalisnormal_stmt `{ua : Univalence} : Type
  := forall G : Group, isEquiv (IntroUF.S17_SurjInj.im_p (kerepi G)).

(** Lemma [lem:characterizations of normal] (statement only): the sets
    (1) - (3) are equivalent; (4) and (5) are fixed points of the
    families [MonoFam] and of abstract subgroups, not stated (size
    issue, Section 9.4). *)
Definition lem_characterizations_of_normal_stmt `{ua : Univalence} : Type
  := forall G : Group, (Epi G ≃ Kern G) × (Epi G ≃ Nor G).

(** *** The associated kernel *)

(** Definition [def:associatednormal]: [ass(N) :≡ E⁻¹(i(N))], with group
    [Ass(N) :≡ Aut_{∑_x X_{sh_G}(x)}(sh_G, pt_{sh_G})] and the first
    projection; here [subgrp_to_mono] (Section 5.3, the map [F] of
    [lem:SubG=MonoG]).  That it is a kernel is
    [lem:normalsarekernels] below. *)
Definition ass `{ua : Univalence} {G : Group} (N : Nor G) : Mono G := subgrp_to_mono (inor G N).

(** The marginal remark after [def:associatednormal] (informal). *)

(** Lemma [lem:normalsarekernels]. *)
Definition lem_normalsarekernels_stmt `{ua : Univalence} : Type
  := forall (G H : Group) (f : Hom G H) (s : isSurj (USymf f)), ass (nor f s) = ker f.

(** By [lem:diagfornormal], [i(nor(f)) = E(ker f)], and [E(ker f)] is the
    subgroup [mono_to_subgrp] of Section 9.2 (up to the transitivity
    proof), which [F] sends back to [ker f] ([mono_subgrp_mono]). *)
Definition lem_normalsarekernels `{ua : Univalence} : lem_normalsarekernels_stmt.
Proof.
  intros G H f s. unfold ass.
  refine (ap subgrp_to_mono (lem_diagfornormal G H f s)^ @ _).
  refine (_ @ (mono_subgrp_mono (kermap f) (kermap_ismono f))^).
  apply (ap subgrp_to_mono). exact (SubGrp_path refl refl).
Defined.
