(** * Section 5.4 Invariant maps and orbits

    Part of Chapter 5 ([actions.tex]); see [Actions.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:actiontype]: the action type [XhG X] ([X_hG]), the
      invariant maps [XuhG X] ([X^hG]) and the set of orbits [Orbits X]
      ([X/G]), a set.  Remark [rem:path-in-action-type]
      ([XhG_paths_eqv]).
    - Definition [def:orbit-map] ([orbit0_sub], [orbit0]) and lemma
      [lem:[]0-maps-to-X/G] ([orbit0_trans]).
    - Lemma [lem:X/G=setTruncX_hG]: [[_]₀] is surjective
      ([orbit0_isSurj]) and effective ([orbit0_eff]), so it induces an
      equivalence [‖X_hG‖₀ ≃ X/G] through which it factors
      ([orbit_tr_eqv], [orbit_tr_settrunc]).  We give this equivalence
      instead of the identification in [∑_{S:Set} (X_hG → S)].
    - Corollary [cor:orbit-equiv]: [orb x :≡ [(sh_G, x)]₀], surjective
      ([orb_isSurj]), with [[x] = [y] ↔ ∃_g (g · x = y)] ([orb_eq_iff]).
    - Remark [rem:SubGX=Sub(X/G)] ([SubG_Sub_orbits]) and exercise
      [xca:transX-just1orbit] ([orbits_contr_trans], [trans_orbits_contr]),
      via [isContr ‖T‖₀ ↔ isConn T].
    - Definition [def:orbit-stabilizer]: the stabilizer group [Gx X x]
      ([G_x], the automorphism group of [(sh_G, x)] in [X_hG]), [ix X x]
      ([i_x]) and the orbit [Gdot X x] ([G · x]); exercise
      [xca:[x]=[y]-implies-||Gx=Gy||] ([Gx_merely_eq]); lemma
      [lem:splitting into orbits] ([splitting_orbits]).
    - Definition [def:fixed-free] ([isFixed], [isFree], [isFreeG]);
      [x] is free iff its loops in [X_hG] are trivial ([free_iff_loops]).
    - Lemma [lem:free-pt-char], in the form: [x] is free iff
      [g ↦ g · x] is injective ([free_pt_char]).
    - Lemma [lem:X_hG-set-iff-Xfree] ([XhG_set_free], [free_XhG_set],
      [XhG_set_orbit0_isEquiv], [orbit0_isEquiv_XhG_set]).
    - Lemma [lem:fixed-char] ([fixed_char]), using that a map of connected
      types is an equivalence iff it is so on loops at a point.
    - Lemma [lem:fixpts-are-fixed]: evaluation at [sh_G] is injective
      ([ev_sh_inj]) and is an equivalence from [X^hG] onto the set of
      elements [x] with [x = g · x] for all [g] ([invariant_eqv]); these
      are the fixed elements by [fixed_char].  Exercise [xca:HomGsets-ev]
      ([HomGs_ev_eqv]).
    - Definition [def:Gx-action-on-G] ([tildeG]), exercise
      [xca:Gx-action-on-G] ([act_tildeG]), construction
      [con:orbit-stabilizer] ([orbit_stabilizer]) and corollary
      [cor:action-subgrp-free] ([tildeG_free]).

    Left out (statements only, no proofs yet; time limit per section)
    - The factorization through the quotient in [cor:orbit-equiv]
      ([cor_orbit_equiv_quot_stmt]), remarks [rem:orbit-fibs]
      ([rem_orbit_fibs_stmt]) and [rem:subgrp-is-stabsubgr]
      ([rem_subgrp_is_stabsubgr_stmt]), example [exa:fixed-free-neither]
      ([exa_fixed_free_stmt]) and exercises [xca:fixed-free-neither]
      ([xca_fixed_free_neither_stmt], first two parts), [xca:Gset-A->B]
      ([xca_Gset_AB_stmt]), [xca:fixed-free-neither-action-types]
      ([xca_fixed_free_action_types_stmt], first two parts), corollary
      [lem:cosets-Gx.g] ([lem_cosets_Gx_g_stmt], as injectivity of
      [h ↦ h · g]) and construction [con:preLagrange]
      ([con_preLagrange_stmt]).
    - The third parts of [xca:fixed-free-neither] and
      [xca:fixed-free-neither-action-types] concern the example of
      Section 5.7, which is itself left out there.

    Left out (not formalized)
    - Exercise [xca:lagrange2] asks for a different proof of
      [lagrange_card] (Section 5.3), whose statement is formalized.
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Truncations.SeparatedTrunc Cubical.DPath
  Spaces.Finite.Fin.
From SymmetryBook Require Export Actions.S03_Subgroups.

Local Open Scope uf_scope.

(** ** 5.4 Invariant maps and orbits *)

Section Orbits.

  Context `{Univalence} {G : Group} (X : GSet G).

  (** Definition [def:actiontype]: the action type [X_hG], the invariant
      maps [X^hG], and the set of orbits [X/G]. *)
  Definition XhG : Type := TotG X.

  Definition XuhG : Type := forall z, el X z.

  Definition Orbits : Type := {P : SubG X & istrans (GSet_sub X P)}.

  Definition Orbits_isSet : isSet Orbits
    := Sigma_ntype 0 (SubG_isSet X) (fun P => prop_ntype 0 _ (istrans_isProp _)).

  (** Remark [rem:path-in-action-type]. *)
  Definition XhG_paths_eqv {z w : utype (BG G)} (x : el X z) (y : el X w)
    : (((z; x) : XhG) = (w; y)) ≃ {g : z = w & act X g x = y}
    := Eqv_inv (path_sigma_eqv (Y := el X)).

  (** Definition [def:orbit-map]: [[u]₀ :≡ (z, x ↦ ‖u = (z,x)‖)]. *)
  Definition orbit0_sub (u : XhG) : SubG X
    := fun z x => ptrunc_PropU (u = (z; x)).

  (** The action in an underlying [G]-set [X_P] is the action of [X] on
      first components. *)
  Definition act_sub_fst (P : SubG X) {z w : utype (BG G)} (g : z = w)
    (y : el (GSet_sub X P) z) : fst (act (GSet_sub X P) g y) = act X g (fst y).
  Proof. destruct g. exact refl. Defined.

  Definition sub_path (P : SubG X) {z : utype (BG G)} {y y' : el (GSet_sub X P) z}
    (e : fst y = fst y') : y = y'
    := path_sigma_prop (fun a => snd (P z a)) e.

  Definition act_inv_l {z w : utype (BG G)} (g : z = w) (a : el X z)
    : act X g⁻¹ (act X g a) = a.
  Proof. destruct g. exact refl. Defined.

  Definition act_inv_r {z w : utype (BG G)} (g : z = w) (a : el X w)
    : act X g (act X g⁻¹ a) = a.
  Proof. destruct g. exact refl. Defined.

  (** Lemma [lem:[]0-maps-to-X/G]. *)
  Definition orbit0_trans (u : XhG) : istrans (GSet_sub X (orbit0_sub u)).
  Proof.
    destruct u as [z0 x0].
    refine (ptrunc_rec ptrunc_isProp _ (snd (BG_isConn G) z0 (sh G))). intro p.
    apply trunc. refine ((act X p x0; trunc (tot_path_act X p x0)); _).
    intros [y hy].
    refine (ptrunc_rec ptrunc_isProp _ hy). intro r.
    pose (r' := r ⋅ (tot_path_act X p x0)⁻¹ : ((sh G; act X p x0) : XhG) = (sh G; y)).
    apply trunc. refine ((ap fst r')⁻¹; _).
    apply sub_path. refine (_ @ (act_sub_fst _ _ _)^); cbn.
    exact ((act_inv_l _ _)^ @ ap (act X (ap fst r')⁻¹) (act_ap_fst X r')).
  Defined.

  Definition orbit0 (u : XhG) : Orbits := (orbit0_sub u; orbit0_trans u).

  (** The orbit through [x : X(sh_G)]. *)
  Definition orb (x : el X (sh G)) : Orbits := orbit0 (sh G; x).

  (** Effectiveness: [[u]₀ = [v]₀] implies [‖u = v‖]. *)
  Definition orbit0_eff (u v : XhG) (e : orbit0 u = orbit0 v) : ptrunc (u = v).
  Proof.
    pose (e' := ptw (ptw (ap fst e) (fst v)) (snd v)).
    exact (trp (fun T : PropU => fst T) e'⁻¹ (trunc refl)).
  Defined.

  Definition orbit0_path {u v : XhG} (r : u = v) : orbit0 u = orbit0 v := ap orbit0 r.

  (** Lemma [lem:X/G=setTruncX_hG]: [[_]] (and hence [[_]₀]) is surjective. *)
  Definition orb_isSurj : isSurj orb.
  Proof.
    intros [O t].
    refine (ptrunc_rec ptrunc_isProp _ t). intros [[x ox] hx].
    apply trunc. refine (x; _).
    refine (path_sigma_prop (fun P => istrans_isProp (GSet_sub X P)) _); cbn.
    apply ptw_inv. intro z. apply ptw_inv. intro a.
    refine (path_PropU _ _).
    - intro oa. refine (ptrunc_rec ptrunc_isProp _ (snd (BG_isConn G) z (sh G))). intro p.
      pose (ob := trp (fun T : PropU => fst T) (SubG_equivariant X O p a)⁻¹ oa).
      refine (ptrunc_rec ptrunc_isProp _ (hx (act X p a; ob))). intros [g eg].
      pose (eg' := ap fst eg @ act_sub_fst O g _ : x = act X g (act X p a)).
      apply trunc.
      exact ((tot_path_act X g (act X p a) ⋅ tot_path_act X p a)⁻¹
             ⋅ ap (fun c => (sh G; c) : XhG) eg').
    - intro r. refine (ptrunc_rec (snd (O z a)) _ r). clear r. intro r.
      refine (trp (fun T : PropU => fst T) _ ox).
      exact ((SubG_equivariant X O (ap fst r) x)^ @ ap (O z) (act_ap_fst X r)).
  Defined.

  Definition orbit0_isSurj : isSurj orbit0
    := fun O => Trunc_functor (-1)
                  (fun w : {x : el X (sh G) & O = orb x} => (((sh G; fst w) : XhG); snd w))
                  (orb_isSurj O).

  (** [X/G] is the set truncation of [X_hG]. *)
  Definition orbit_tr : strunc XhG -> Orbits := strunc_rec Orbits_isSet orbit0.

  Definition orbit_tr_isEquiv : isEquiv orbit_tr.
  Proof.
    refine (inj_surj_isEquiv (cancel_isInj Orbits_isSet _) _).
    - refine (strunc_ind_prop _ (fun a => Pi_isProp (fun b => Pi_isProp
                (fun _ => strunc_isSet a b))) _). intro u.
      refine (strunc_ind_prop _ (fun b => Pi_isProp (fun _ => strunc_isSet _ b)) _). intros v e.
      exact (ptrunc_rec (strunc_isSet _ _) (fun r => ap settrunc r) (orbit0_eff u v e)).
    - intro O. exact (Trunc_functor (-1)
                        (fun w : {u : XhG & O = orbit0 u} => (settrunc (fst w); snd w))
                        (orbit0_isSurj O)).
  Defined.

  Definition orbit_tr_eqv : strunc XhG ≃ Orbits := (orbit_tr; orbit_tr_isEquiv).

  Definition orbit_tr_settrunc (u : XhG) : orbit_tr (settrunc u) = orbit0 u := refl.

  (** Corollary [cor:orbit-equiv]. *)
  Definition orb_eq_iff (x y : el X (sh G))
    : (orb x = orb y) <-> Ex (fun g : USym G => act X g x = y).
  Proof.
    split.
    - intro e. exact (Trunc_functor (-1) (fst (XhG_paths_eqv x y)) (orbit0_eff _ _ e)).
    - intro h. refine (ptrunc_rec (Orbits_isSet _ _) _ h). intros [g eg].
      exact (orbit0_path (eqinv (snd (XhG_paths_eqv x y)) (g; eg))).
  Defined.

  (** Remark [rem:SubGX=Sub(X/G)]. *)
  Definition SubG_Sub_orbits : SubG X ≃ (Orbits -> PropU).
  Proof.
    refine (Eqv_comp (Eqv_inv (sigma_curry _ _ _)) _).
    refine (Eqv_comp (Eqv_inv (strunc_univ_prop XhG PropU_isSet)) _).
    refine (mkEqv (fun h => h ∘ eqinv orbit_tr_isEquiv) (fun k => k ∘ orbit_tr) _ _);
      intro h; apply ptw_inv; intro a.
    - exact (ap h (eqinv_l orbit_tr_isEquiv a)).
    - exact (ap h (eqinv_r orbit_tr_isEquiv a)).
  Defined.

  (** Exercise [xca:transX-just1orbit]. *)
  Definition strunc_contr_conn (T : Type) (c : isContr (strunc T)) : isConn T.
  Proof.
    refine (strunc_ind_prop (fun _ => ptrunc T) (fun _ => ptrunc_isProp)
              (fun t => trunc t) (fst c); _).
    intros a b.
    exact ((equiv_path_Tr a b)^-1 (isContr_isProp' c (settrunc a) (settrunc b))).
  Defined.

  Definition conn_strunc_contr (T : Type) (c : isConn T) : isContr (strunc T).
  Proof.
    refine (ptrunc_rec (isContr_isProp _) _ (fst c)). intro t.
    refine (settrunc t; _).
    refine (strunc_ind_prop _ (fun b => strunc_isSet _ b) _). intro b.
    exact (ptrunc_rec (strunc_isSet _ _) (fun r => ap settrunc r) (snd c t b)).
  Defined.

  Definition orbits_contr_trans (c : isContr Orbits) : istrans X
    := trans_of_conn X (strunc_contr_conn XhG (isContr_Eqv (Eqv_inv orbit_tr_eqv) c)).

  Definition trans_orbits_contr (t : istrans X) : isContr Orbits
    := isContr_Eqv orbit_tr_eqv (conn_strunc_contr XhG (conn_of_trans X t)).

End Orbits.

(** Corollary [cor:orbit-equiv], last part (statement only): [[_]]
    factors through the quotient of [X(sh_G)] by [∃_g (g · x = y)] by an
    equivalence. *)
Definition orbit_rel {G : Group} (X : GSet G) (x y : el X (sh G)) : PropU
  := (Ex (fun g : USym G => act X g x = y); ptrunc_isProp).

Definition cor_orbit_equiv_quot_stmt `{Univalence} : Type
  := forall (G : Group) (X : GSet G),
       {e : quot (orbit_rel X) ≃ Orbits X &
         forall x, fst e (S22_SetOperations.cls (orbit_rel X) x) = orb X x}.

(** Remark [rem:equivalents-of-[x]=[y]]: for [x, y : X(sh_G)] the
    propositions [[x] = [y]], [[x]₀ = [y]₀], [‖(sh_G,x) = (sh_G,y)‖] and
    [∃_g (g · x = y)] are equivalent (see [orbit0_eff] and [cor:orbit-equiv]
    above; used without mention). *)

(** Footnote [ft:orbit-surj]: the surjections [X(sh_G) → X_hG → X/G]
    justify the notation [X/G] (informal). *)

(** ** Stabilizers, fixed and free elements *)
Section Stabilizers.

  Context `{Univalence} {G : Group} (X : GSet G).

  Local Notation XhG := (XhG X).

  Definition XhG_isGrpd : isGrpd XhG := TotG_isGrpd X.

  (** Definition [def:orbit-stabilizer]: the stabilizer group [G_x], its
      monomorphism [i_x] into [G], and the orbit [G · x]. *)
  Definition Gx (x : el X (sh G)) : Group := AutG XhG_isGrpd ((sh G; x) : XhG).

  Definition BGx_fst (x : el X (sh G)) : utype (BG (Gx x)) -> utype (BG G)
    := fun w => fst (fst w).

  Definition ix (x : el X (sh G)) : Hom (Gx x) G := @mkhom (Gx x) G (BGx_fst x; refl).

  Definition Gdot (x : el X (sh G)) : Type := {y : el X (sh G) & orb X x = orb X y}.

  (** Exercise [xca:[x]=[y]-implies-||Gx=Gy||]. *)
  Definition Gx_merely_eq (x y : el X (sh G)) (e : orb X x = orb X y)
    : ptrunc (Gx x = Gx y)
    := Trunc_functor (-1) (fun r => ap (AutG XhG_isGrpd) r) (orbit0_eff X _ _ e).

  (** Lemma [lem:splitting into orbits]. *)
  Definition splitting_orbits : {O : Orbits X & fiber (orb X) O} ≃ el X (sh G)
    := sum_of_fibers (orb X).

  (** Remark [rem:orbit-fibs] (statement only): the action type of
      [X_{[x]}], pointed at [(sh_G, x)], is [BG_x], and its underlying set
      is [G · x]. *)
  Definition Xorb (x : el X (sh G)) : GSet G := GSet_sub X (orbit0_sub X (sh G; x)).

  Definition rem_orbit_fibs_stmt : Type
    := forall x : el X (sh G),
         {xp : fst (orbit0_sub X (sh G; x) (sh G) x) &
           ((TotG (Xorb x); ((sh G; (x; xp)) : TotG (Xorb x))) ≃* BG (Gx x))}
         × (el (Xorb x) (sh G) ≃ Gdot x).

  (** Remark [rem:subgrp-is-stabsubgr] (statement only). *)
  Definition rem_subgrp_is_stabsubgr_stmt : Type
    := (forall (x : el X (sh G)) (xp : fst (orbit0_sub X (sh G; x) (sh G) x))
               (t : istrans (Xorb x)) (m : ismono (ix x)),
          subgrp_to_mono ((Xorb x; ((x; xp); t)) : SubGrp G) = (Gx x; (ix x; m)))
       × (forall (t : istrans X) (x : el X (sh G)) (m : ismono (ix x)),
            subgrp_to_mono ((X; (x; t)) : SubGrp G) = (Gx x; (ix x; m))).

  (** Definition [def:fixed-free]. *)
  Definition isFixed (x : el X (sh G)) : Type := isIso (ix x).

  Definition isFree (x : el X (sh G)) : Type := isContr (utype (BG (Gx x))).

  Definition isFreeG : Type := forall x, isFree x.

  (** Loops in the component of [(sh_G, x)] are loops in [X_hG]. *)
  Definition comp_loops_eqv (x : el X (sh G)) (w : utype (BG (Gx x)))
    : (w = w) ≃ (fst w = fst w)
    := subtype_paths_eqv (fun _ => ptrunc_isProp) w w.

  Definition loops_prop_isSet {T : Type} (h : forall t : T, isProp (t = t)) : isSet T.
  Proof. intros a b p q. destruct q. exact (h a p refl). Defined.

  (** Elements of the component of [(sh_G, x)] have propositional loops
      iff [(sh_G, x)] has. *)
  Definition comp_loops_prop (x : el X (sh G)) (h : isProp (((sh G; x) : XhG) = (sh G; x)))
    : forall w : utype (BG (Gx x)), isProp (w = w).
  Proof.
    intros [u t]. refine (isProp_Eqv (Eqv_inv (comp_loops_eqv x (u; t))) _).
    refine (ptrunc_rec (isProp_isProp _) _ t). intro r. destruct r. exact h.
  Defined.

  Definition paths_prop_from_loops {T : Type} {a : T} (h : isProp (a = a)) (b : T)
    : isProp (a = b).
  Proof. intros p q. destruct q. exact (h p refl). Defined.

  Definition ap_fst_actpath {z w : utype (BG G)} (p : z = w) (a : el X z)
    (b : el X w) (e : act X p a = b)
    : ap fst (ap (fun c => (w; c) : XhG) e ⋅ tot_path_act X p a) = p.
  Proof. destruct e, p. exact refl. Defined.

  (** [x] is free iff its loops in [X_hG] are trivial. *)
  Definition free_iff_loops (x : el X (sh G))
    : isFree x <-> isProp (((sh G; x) : XhG) = (sh G; x)).
  Proof.
    split.
    - intro c. refine (isProp_Eqv (comp_loops_eqv x (pt (BG (Gx x)))) _).
      exact (prop_is_set (isContr_isProp' c) _ _).
    - intro h. exact (conn_loops_prop_isContr (BG_isConn (Gx x)) (comp_loops_prop x h)).
  Defined.

  (** Lemma [lem:free-pt-char]: [x] is free iff [g ↦ g · x] is
      injective. *)
  Definition free_pt_char (x : el X (sh G))
    : isFree x <-> (forall g g' : USym G, act X g x = act X g' x -> g = g').
  Proof.
    refine (iff_compose (free_iff_loops x) _). split.
    - intros h g g' e.
      pose (P := ap (fun c => (sh G; c) : XhG) e ⋅ tot_path_act X g x).
      refine ((ap_fst_actpath g x _ e)^ @ ap (ap fst) (paths_prop_from_loops h _ P _)
              @ ap_fst_actpath g' x _ refl).
    - intros h l l'.
      assert (k : forall l : ((sh G; x) : XhG) = (sh G; x), l = refl).
      { intro m. apply (ap_fst_cancel (el_isSet X)). apply h.
        exact (act_ap_fst X m). }
      exact (k l @ (k l')^).
  Defined.

  (** Lemma [lem:X_hG-set-iff-Xfree]. *)
  Definition XhG_set_free (s : isSet XhG) : isFreeG
    := fun x => Overture.snd (free_iff_loops x) (s _ _).

  Definition free_XhG_set (f : isFreeG) : isSet XhG.
  Proof.
    apply loops_prop_isSet. intros [z a].
    refine (ptrunc_rec (isProp_isProp _) _ (snd (BG_isConn G) z (sh G))). intro p.
    pose (hp := Overture.fst (free_iff_loops (act X p a)) (f (act X p a))).
    exact (isProp_Eqv (Eqv_inv (Eqv_of_Equiv
             (equiv_concat_lr (tot_path_act X p a)⁻¹ (tot_path_act X p a)))) hp).
  Defined.

  Definition XhG_set_orbit0_isEquiv (s : isSet XhG) : isEquiv (orbit0 X).
  Proof.
    refine (comp_isEquiv (f := settrunc) _ (orbit_tr_isEquiv X)).
    exact (isEquiv_of_IsEquiv _ (H := isequiv_tr 0 XhG (IsTrunc0 := isSet_IsHSet s))).
  Defined.

  Definition orbit0_isEquiv_XhG_set (t : isEquiv (orbit0 X)) : isSet XhG
    := is_ntype_Eqv 0 (Eqv_inv (orbit0 X; t)) (Orbits_isSet X).

  (** Lemma [lem:fixed-char]: [x] is fixed iff [x = g · x] for all [g]. *)
  Definition fixed_char (x : el X (sh G))
    : isFixed x <-> (forall g : USym G, x = act X g x).
  Proof.
    pose (cGx := BG_isConn (Gx x)).
    pose (w0 := pt (BG (Gx x))).
    split.
    - intros t g.
      pose (ta := fst (conn_isEquiv_iff_point _ cGx (BG_isConn G) w0) t).
      pose (l := eqinv ta g).
      refine ((act_ap_fst X (ap fst l))⁻¹ @ _).
      refine (ap (fun r => act X r x) _).
      exact ((ap_compose fst fst l)^ @ eqinv_r ta g).
    - intro h. apply (snd (conn_isEquiv_iff_point _ cGx (BG_isConn G) w0)).
      refine (iso_to_isEquiv _ (fun g => eqinv (snd (comp_loops_eqv x w0))
                 (ap (fun c => (sh G; c) : XhG) (h g)⁻¹ ⋅ tot_path_act X g x)) _ _).
      + intro l. apply (isInj_cancel (isEquiv_isInj (snd (comp_loops_eqv x w0)))).
        refine (eqinv_r _ _ @ _).
        apply (ap_fst_cancel (el_isSet X)).
        refine (ap_fst_actpath _ _ _ _ @ _).
        exact (ap_compose fst fst l).
      + intro g.
        change (ap (fun w : utype (BG (Gx x)) => fst (fst w))
                  (eqinv (snd (comp_loops_eqv x w0))
                     (ap (fun c => (sh G; c) : XhG) (h g)⁻¹ ⋅ tot_path_act X g x)) = g).
        refine (ap_compose (@fst XhG (fun w : XhG => ptrunc (((sh G; x) : XhG) = w)))
                  (@fst (utype (BG G)) (el X)) _ @ _).
        refine (ap (ap fst) (eqinv_r (snd (comp_loops_eqv x w0)) _) @ _).
        exact (ap_fst_actpath _ _ _ _).
  Defined.

  (** Lemma [lem:fixpts-are-fixed], with [X^hG] equivalent to the set of
      elements [x] with [x = g · x] for all [g]. *)
  Definition ev_sh (f : XuhG X) : el X (sh G) := f (sh G).

  (** Part [it:ev-is-inj]. *)
  Definition ev_sh_inj (f f' : XuhG X) (e : f (sh G) = f' (sh G)) : f = f'.
  Proof.
    apply ptw_inv. intro z.
    refine (ptrunc_rec (el_isSet X z _ _) _ (snd (BG_isConn G) (sh G) z)). intro p.
    destruct p. exact e.
  Defined.

  (** Part [it:ev-is-eq-on-inv]: the image of [ev] consists of the fixed
      elements. *)
  Definition invariant_fixed (f : XuhG X) (g : USym G) : f (sh G) = act X g (f (sh G))
    := (apD f g)^.

  Definition fixed_invariant (x : el X (sh G)) (h : forall g : USym G, x = act X g x)
    : XuhG X.
  Proof.
    intro z.
    refine (wconst_elim (el_isSet X z) (f := fun p : sh G = z => act X p x) _
              (snd (BG_isConn G) (sh G) z)).
    intros p p'. destruct p'.
    exact (h p)⁻¹.
  Defined.

  Definition fixed_invariant_sh (x : el X (sh G)) (h : forall g : USym G, x = act X g x)
    : fixed_invariant x h (sh G) = x.
  Proof.
    unfold fixed_invariant.
    generalize (snd (BG_isConn G) (sh G) (sh G)).
    refine (ptrunc_ind _ (fun _ => el_isSet X _ _ _) _). intro p. exact (h p)⁻¹.
  Defined.

  Definition fixed_set : Type := {x : el X (sh G) & forall g : USym G, x = act X g x}.

  Definition invariant_eqv : XuhG X ≃ fixed_set.
  Proof.
    refine (mkEqv (fun f => (f (sh G); invariant_fixed f))
                  (fun w => fixed_invariant (fst w) (snd w)) _ _).
    - intro f. apply ev_sh_inj. exact (fixed_invariant_sh _ _).
    - intros [x h].
      refine (path_sigma_prop (fun y => Pi_isProp (fun g => el_isSet X _ _ _)) _).
      exact (fixed_invariant_sh x h).
  Defined.




End Stabilizers.

(** Remarks [rem:orbit-fibs] and [rem:subgrp-is-stabsubgr], example
    [exa:fixed-free-neither] and exercise [xca:fixed-free-neither]
    (statements only). *)
Section StabilizerStatements.

  Context `{Univalence}.

  (** Example [exa:fixed-free-neither]: elements of a trivial [G]-set are
      fixed, and those of [princ G] are free.  (Placed after the section on
      stabilizers, which fixes one [G]-set [X], since it concerns the
      particular [G]-sets [triv_G S] and [princ G].) *)
  Definition exa_fixed_free_stmt : Type
    := (forall (G : Group) (S : SetU) (s : fst S), isFixed (trivG G S) s)
       × (forall (G : Group) (g : USym G), isFree (princ G) g).

  (** Exercise [xca:fixed-free-neither], first two parts (placed here for
      the same reason):
      [BG_s ≃ BG] for [triv_G S], and [BG_g] contractible for [princ G];
      the third part concerns the action of [C_4] on [Fin 4 → Fin 2] of
      Section 5.7. *)
  Definition xca_fixed_free_neither_stmt : Type
    := (forall (G : Group) (S : SetU) (s : fst S),
          utype (BG (Gx (trivG G S) s)) ≃ utype (BG G))
       × (forall (G : Group) (g : USym G), isContr (utype (BG (Gx (princ G) g)))).

End StabilizerStatements.

(** Exercise [xca:Gset-A->B] (statements only): for [G :≡ Σ_2 × Σ_2]
    and [X(A, B) :≡ A → B] there are [2] orbits and no invariant maps; for
    the constant [G]-set [𝟚 × 𝟚] there are [4] of each; for the
    [Σ_2]-sets [X(-, 𝟚)] there are [3] orbits and [2] invariant maps, and
    for [X(𝟚, -)] [2] orbits and none. *)
Section GsetAB.

  Context `{Univalence}.

  Definition XAB : GSet (prodG (SG 2) (SG 2))
    := fun z => ((el2 (fst z) -> el2 (snd z)); Pi_isSet (fun _ => el2_isSet (snd z))).

  Definition X22 : GSet (prodG (SG 2) (SG 2))
    := fun _ => ((Fin 2 × Fin 2); Sigma_isSet (Fin_isSet 2) (fun _ => Fin_isSet 2)).

  Definition XA2 : GSet (SG 2)
    := fun A => ((el2 A -> Fin 2); Pi_isSet (fun _ => Fin_isSet 2)).

  Definition X2B : GSet (SG 2)
    := fun B => ((Fin 2 -> el2 B); Pi_isSet (fun _ => el2_isSet B)).

  Definition xca_Gset_AB_stmt : Type
    := ((Orbits XAB ≃ Fin 2) × (XuhG XAB ≃ Fin 0))
       × ((Orbits X22 ≃ Fin 4) × (XuhG X22 ≃ Fin 4))
       × ((Orbits XA2 ≃ Fin 3) × (XuhG XA2 ≃ Fin 2))
       × ((Orbits X2B ≃ Fin 2) × (XuhG X2B ≃ Fin 0)).

End GsetAB.

(** Exercise [xca:HomGsets-ev]: maps of [G]-sets are the fixed elements
    of the [G]-set [z ↦ (X(z) → Y(z))]. *)
Definition funGSet `{Funext} {G : Group} (X Y : GSet G) : GSet G
  := fun z => ((el X z -> el Y z); Pi_isSet (fun _ => el_isSet Y z)).

Definition HomGs_ev_eqv `{Univalence} {G : Group} (X Y : GSet G)
  : HomGs X Y ≃ fixed_set (funGSet X Y)
  := invariant_eqv (funGSet X Y).

(** ** 5.4.1 The Orbit–Stabilizer theorem *)
Section OrbitStabilizer.

  Context `{Univalence} {G : Group} (X : GSet G) (x : el X (sh G)).

  (** Definition [def:Gx-action-on-G]: [G̃_x :≡ P_{sh_G} ∘ Bi_x]. *)
  Definition tildeG : GSet (Gx X x) := fun w => princ G (BGx_fst X x w).

  (** Exercise [xca:Gx-action-on-G]: the action is path composition. *)
  Definition act_tildeG {w w' : utype (BG (Gx X x))} (s : w = w') (g : el tildeG w)
    : act tildeG s g = ap (BGx_fst X x) s ⋅ g.
  Proof. destruct s. exact refl. Defined.

  (** Construction [con:orbit-stabilizer]: [(G̃_x)_{hG_x} ≃ G · x].
      Footnote [ft:action-type-tildeGx-set]: [(G̃_x)_{hG_x}] is a set
      already by [xca:Gx-action-on-G] (informal). *)
  Definition os_fwd (v : TotG tildeG) : Gdot X x.
  Proof.
    destruct v as [[[z y] t] p]. cbn in p.
    refine (act X p⁻¹ y; _).
    exact (ptrunc_rec (Orbits_isSet X _ _)
             (fun r => orbit0_path X (tot_path_act X p⁻¹ y ⋅ r)) t).
  Defined.

  Definition os_bwd (u : Gdot X x) : TotG tildeG
    := (((((sh G; fst u) : XhG X); orbit0_eff X (sh G; x) (sh G; fst u) (snd u))
         : utype (BG (Gx X x))); refl).

  Definition orbit_stabilizer : TotG tildeG ≃ Gdot X x.
  Proof.
    refine (mkEqv os_fwd os_bwd _ _).
    - intros [[[z y] t] p]. cbn in p. destruct p.
      exact (ap (fun t' => (((((sh G; y) : XhG X); t') : utype (BG (Gx X x))); refl)
                           : TotG tildeG)
                (ptrunc_isProp _ _)).
    - intros [y e].
      exact (@path_sigma_prop _ (fun y' => orb X x = orb X y') (fun _ => Orbits_isSet X _ _)
               (os_fwd (os_bwd (y; e))) (y; e) refl).
  Defined.

  (** Corollary [cor:action-subgrp-free]. *)
  Definition Gdot_isSet : isSet (Gdot X x)
    := Sigma_ntype 0 (el_isSet X _) (fun y => prop_ntype 0 _ (Orbits_isSet X _ _)).

  Definition tildeG_free : isFreeG tildeG
    := XhG_set_free tildeG (is_ntype_Eqv 0 (Eqv_inv orbit_stabilizer) Gdot_isSet).

End OrbitStabilizer.

(** Exercise [xca:fixed-free-neither-action-types], first two parts,
    corollary [lem:cosets-Gx.g], construction [con:preLagrange]
    (statements only).  Exercise [xca:lagrange2] asks for another proof
    of [lagrange_card] (Section 5.3).
    (The exercise is placed after the section on the Orbit–Stabilizer construction, which fixes [X] and [x], since it concerns the particular [G]-sets [triv_G S] and [princ G].) *)
Definition xca_fixed_free_action_types_stmt `{Univalence} : Type
  := (forall (G : Group) (S : SetU) (s : fst S), isContr (TotG (tildeG (trivG G S) s)))
     × (forall (G : Group) (g : USym G), TotG (tildeG (princ G) g) ≃ USym G).

Definition lem_cosets_Gx_g_stmt `{Univalence} : Type
  := forall (G : Group) (X : GSet G) (x : el X (sh G))
            (g : el (tildeG X x) (sh (Gx X x))),
       isInj (fun h : USym (Gx X x) => act (tildeG X x) h g).

Definition con_preLagrange_stmt `{Univalence} : Type
  := forall (G : Group) (S : SubGrp G),
       el (sg_X S) (sh G) ≃ Orbits (tildeG (sg_X S) (sg_pt S)).
