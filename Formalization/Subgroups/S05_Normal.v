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
    - That [q_N] is an epimorphism ([qN_isepi]): [U q_N] is surjective by
      the second part of [lem:evaliseqwhennormal].

    Left out (statements only)
    - Lemmas [lem:diagfornormal], [lem:qeq],
      [lem:normalsarekernels], corollary [cor:normalisnormal], lemma
      [lem:characterizations of normal] (parts (1) - (3)) ([..._stmt]).
    - The map [q : Nor(G) → Epi(G)] (see the size issue below).
    - Size issue: [G/N] lives in a larger universe than [G], so
      [nor(q(N)) = N] in [Nor(G)] and [(G', f) = q(nor(f))] in [Epi(G)]
      cannot be stated; [lem_qeq_stmt] states the content of the proof
      instead (pointed equivalences of [G]-sets, and an isomorphism [Q]
      with [Q f = q_{nor f}]).
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

(** Lemma [lem:diagfornormal] (statement only): around the top,
    [E(i(ker f))] is [y ↦ (sh_{G'} = f(y))] pointed at [Bf_pt]; around the
    bottom it is [nor(f)(sh_G)]; precomposition with [Bf_pt] identifies
    them. *)
Definition lem_diagfornormal_stmt `{ua : Univalence} : Type
  := forall (G H : Group) (f : Hom G H) (s : isSurj (USymf f)),
       Emono (kermap f) (kermap_ismono f) = inor G (nor f s).

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

(** Lemma [lem:qeq] (statement only).  Size issue: [G/N] lives in a
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
    [lem:SubG=MonoG]).  That it is a kernel is part of
    [lem:normalsarekernels]. *)
Definition ass `{ua : Univalence} {G : Group} (N : Nor G) : Mono G := subgrp_to_mono (inor G N).

(** The marginal remark after [def:associatednormal] (informal). *)

(** Lemma [lem:normalsarekernels] (statement only). *)
Definition lem_normalsarekernels_stmt `{ua : Univalence} : Type
  := forall (G H : Group) (f : Hom G H) (s : isSurj (USymf f)), ass (nor f s) = ker f.
