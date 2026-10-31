(** * Section 8.6 Sums of groups

    Part of Chapter 8 ([congp.tex]); see [ConGroups.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.  (Section 8.5,
    pushouts of types, is still to be written in the book.)

    ** Summary of this formalization

    - Definition [def:wedge]: [wedgeT A1 A2] as the library's pushout of
      the two points, with [wi1], [wi2], [wglue] and [i_2^g] ([wi2g]).
    - Lemma [lem:univvee]: [(A1 ∨ A2 →* B) ≃ (A1 →* B) × (A2 →* B)]
      ([univvee]).
    - The wedge of connected types is connected ([wedge_isConn]).
    - Definition [def:sumofgroup]: [sumG G1 G2], with structure maps
      [sumG_in1], [sumG_in2].  Deviation: the book takes
      [Aut_{A1 ∨ A2}(a_12)], which needs that the wedge of groupoids is a
      groupoid (lemma [lem:wedgeofgpoidisgpoid], only for decidable
      groups); we use the [1]-truncation of the wedge, a connected
      groupoid, which agrees with the wedge once that is a groupoid.
    - Lemma [lem:sumofgroupsISsum] ([sumG_univ]) and corollary
      [cor:ZplusZuniv] ([ZZ_sum_univ]).

    - Exercise [xca:whatAREabeliangroups] ([xca_whatAREabeliangroups],
      with [fold_map] and [wedge_incl]; the statement assumes [Funext]).
      Via [univvee], [e] extends the fold map iff [e ∘ i₁ = id = e ∘ i₂]
      ([ext_fold_fw], [ext_fold_bw]); then [(g, 1)] and [(1, h)] commute
      in [BG × BG] ([ext_fold_isAb]).  Conversely, the multiplication of an
      abelian group is a homomorphism [G × G → G] ([mulG_absHom]), which
      deloops by [abstr_hom_eqv] ([isAb_ext_fold]).

    Left out (statements only, no proofs yet; time limit per result)
    - Lemma [lem:wedgeofgpoidisgpoid] ([lem_wedgeofgpoidisgpoid_stmt]; the
      book's proof uses words for decidable groups).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Colimits.Pushout Spaces.Circle.
From SymmetryBook Require Export ConGroups.S04_Pullback.

Local Open Scope uf_scope.

(** ** 8.6 Sums of groups *)

(** Definition [def:wedge]: the wedge as the library's pushout of the two
    points, with [i_1 :≡ pushl], [i_2 :≡ pushr], [g :≡ pglue(triv)],
    pointed at [a_12 :≡ i_1(a_1)]. *)
Section Wedge.

  Context (A1 A2 : Ustar).

  Definition wedgeT : Type
    := Pushout (fun _ : True => pt A1) (fun _ : True => pt A2).

  Definition wi1 (a : utype A1) : wedgeT := pushl a.
  Definition wi2 (a : utype A2) : wedgeT := pushr a.
  Definition wglue : wi1 (pt A1) = wi2 (pt A2) := pglue triv.

  Definition wedge : Ustar := (wedgeT; wi1 (pt A1)).

  (** [i_2^g(p) :≡ g⁻¹ i_2(p) g]. *)
  Definition wi2g (p : pt A2 = pt A2) : pt wedge = pt wedge
    := wglue⁻¹ ⋅ (ap wi2 p ⋅ wglue).

  (** Lemma [lem:univvee]. *)
  Context (B : Ustar).

  Definition univvee_fw (k : wedge →* B) : (A1 →* B) × (A2 →* B)
    := ((fst k ∘ wi1; snd k); (fst k ∘ wi2; ap (fst k) wglue ⋅ snd k)).

  Definition univvee_bw (fs : (A1 →* B) × (A2 →* B)) : wedge →* B
    := (Pushout_rec (utype B) (fst (fst fs)) (fst (snd fs))
          (fun _ => snd (snd fs) ⋅ (snd (fst fs))⁻¹);
        snd (fst fs)).

  Definition univvee_fw_bw (fs : (A1 →* B) × (A2 →* B))
    : univvee_fw (univvee_bw fs) = fs.
  Proof.
    destruct fs as [[f1 p1] [f2 p2]]. unfold univvee_fw, univvee_bw. cbn.
    apply (ap (fun q => (((f1; p1) : A1 →* B); ((f2; q) : A2 →* B)))).
    refine (ap (fun r => r ⋅ p1) (Pushout_rec_beta_pglue _ f1 f2 _ triv) @ _).
    refine ((trans_assoc _ _ _)^ @ _).
    refine (ap (fun r => p2 ⋅ r) (trans_pV p1) @ _).
    exact (trans_1p p2).
  Defined.

  Definition univvee_bw_fw `{Funext} (k : wedge →* B) : univvee_bw (univvee_fw k) = k.
  Proof.
    destruct k as [k kp].
    refine (eqinv (snd (ptw_star (univvee_bw (univvee_fw (k; kp))) (k; kp))) _).
    unfold univvee_bw, univvee_fw. cbn.
    assert (E : (fun _ : True => (ap k wglue ⋅ kp) ⋅ kp⁻¹) = (fun a => ap k (pglue a))).
    { apply ptw_inv. intros []. refine ((trans_assoc _ _ _)^ @ _).
      refine (ap (fun r => ap k wglue ⋅ r) (trans_Vp kp) @ _). exact (trans_1p _). }
    pose (h := fun x => ap (fun gl => Pushout_rec (utype B) (k ∘ wi1) (k ∘ wi2) gl x) E
                        @ pushout_rec_unrec _ _ _ k x).
    refine (h; _). unfold h. cbn.
    refine (ap (fun r => r ⋅ kp) (_ : (_ @ _) = refl)).
    refine (ap (fun r => r @ _) _ @ concat_1p _).
    change (ap (fun _ => k (wi1 (pt A1))) E = refl). apply ap_const.
  Defined.

  Definition univvee `{Funext} : (wedge →* B) ≃ (A1 →* B) × (A2 →* B)
    := mkEqv univvee_fw univvee_bw univvee_bw_fw univvee_fw_bw.

End Wedge.

(** The wedge of connected types is connected. *)
Definition wedge_isConn (A1 A2 : Ustar) (c1 : isConn (utype A1)) (c2 : isConn (utype A2))
  : isConn (wedgeT A1 A2).
Proof.
  refine (isConn_from_pt (wi1 A1 A2 (pt A1)) _).
  exact (Pushout_ind (fun x => ptrunc (wi1 A1 A2 (pt A1) = x))
           (fun b => ptrunc_rec ptrunc_isProp (fun p => trunc (ap (wi1 A1 A2) p))
                       (snd c1 (pt A1) b))
           (fun c => ptrunc_rec ptrunc_isProp
                       (fun p => trunc (ap (wi2 A1 A2) p ⋅ wglue A1 A2))
                       (snd c2 (pt A2) c))
           (fun a => ptrunc_isProp _ _)).
Defined.

(** Definition [def:sumofgroup].  The book takes [Aut_{A_1 ∨ A_2}(a_12)],
    which needs that the wedge of groupoids is a groupoid (proved in the
    book only for decidable groups, lemma [lem:wedgeofgpoidisgpoid]); we
    take the [1]-truncation of the wedge instead, which is a connected
    groupoid by construction, and agrees with the wedge once that is
    known to be a groupoid. *)
Definition sumG (G1 G2 : Group) : Group
  := mkgroup (Trunc 1 (wedgeT (BG G1) (BG G2));
              (tr (wi1 (BG G1) (BG G2) (sh G1));
               (surj_isConn (f := tr)
                  (fun y => Trunc_ind (fun y => Ex (fun a => y = tr a))
                              (fun a => trunc (a; refl)) y)
                  (wedge_isConn _ _ (BG_isConn G1) (BG_isConn G2));
                IsTrunc_isGrpd (istrunc_truncation 1 _)))).

(** The structure maps. *)
Definition sumG_in1 (G1 G2 : Group) : Hom G1 (sumG G1 G2)
  := mkhom ((((fun a => tr (wi1 (BG G1) (BG G2) a)) : utype (BG G1) -> utype (BG (sumG G1 G2)));
             refl) : BG G1 →* BG (sumG G1 G2)).

Definition sumG_in2 (G1 G2 : Group) : Hom G2 (sumG G1 G2)
  := mkhom ((((fun a => tr (wi2 (BG G1) (BG G2) a)) : utype (BG G2) -> utype (BG (sumG G1 G2)));
             ap tr (wglue (BG G1) (BG G2))) : BG G2 →* BG (sumG G1 G2)).

(** Lemma [lem:sumofgroupsISsum]. *)
Definition sumG_univ `{Funext} (G1 G2 G : Group)
  : Hom (sumG G1 G2) G ≃ Hom G1 G × Hom G2 G.
Proof.
  pose (W := wedgeT (BG G1) (BG G2)).
  refine (Eqv_comp (Copy_eqv _) _).
  refine (Eqv_comp (Eqv_of_Equiv (equiv_functor_sigma_pb
             (Q := fun k : W -> utype (BG G) => sh G = k (wi1 (BG G1) (BG G2) (sh G1)))
             (Equiv_of_Eqv (@trunc_univ_prop _ 1 W (utype (BG G))
                              (isGrpd_IsTrunc (BG_isGrpd G)))))) _).
  refine (Eqv_comp (univvee (BG G1) (BG G2) (BG G)) _).
  refine (mkEqv (fun k => (mkhom (fst k); mkhom (snd k)))
                (fun h => (Bf (fst h); Bf (snd h))) _ _).
  - intro k. exact refl.
  - intros [[a] [b]]. exact refl.
Defined.

(** Corollary [cor:ZplusZuniv]. *)
Definition ZZ_sum_univ `{Univalence} (G : Group)
  : Hom (sumG ZZ ZZ) G ≃ USym G × USym G.
Proof.
  refine (Eqv_comp (sumG_univ ZZ ZZ G) _).
  refine (mkEqv (fun h => (fst (Hom_ZZ_eqv G) (fst h); fst (Hom_ZZ_eqv G) (snd h)))
                (fun u => (eqinv (snd (Hom_ZZ_eqv G)) (fst u);
                           eqinv (snd (Hom_ZZ_eqv G)) (snd u))) _ _).
  - intros [a b]. exact (ap011 (fun x y => (x; y) : Hom ZZ G × Hom ZZ G)
                           (eqinv_l (snd (Hom_ZZ_eqv G)) a) (eqinv_l (snd (Hom_ZZ_eqv G)) b)).
  - intros [a b]. exact (ap011 (fun x y => (x; y) : USym G × USym G)
                           (eqinv_r (snd (Hom_ZZ_eqv G)) a) (eqinv_r (snd (Hom_ZZ_eqv G)) b)).
Defined.

(** Exercise [xca:whatAREabeliangroups] (proved below): [G] is abelian
    iff the fold map [BG ∨ BG →* BG] extends over the inclusion
    [BG ∨ BG →* BG × BG]. *)
Definition BGxBG (G : Group) : Ustar := (utype (BG G) × utype (BG G); (sh G; sh G)).

Definition fold_map (G : Group) : wedge (BG G) (BG G) →* BG G
  := univvee_bw (BG G) (BG G) (BG G) (pid (BG G); pid (BG G)).

Definition wedge_incl (G : Group) : wedge (BG G) (BG G) →* BGxBG G
  := univvee_bw (BG G) (BG G) (BGxBG G)
       ((((fun z => (z; sh G)) : utype (BG G) -> utype (BGxBG G)); refl);
        (((fun z => (sh G; z)) : utype (BG G) -> utype (BGxBG G)); refl)).

Definition xca_whatAREabeliangroups_stmt `{Funext} : Type
  := forall G : Group,
       isAb G <-> {e : BGxBG G →* BG G & pcomp e (wedge_incl G) = fold_map G}.

(** Proof of the exercise.  By [univvee], [e] extends the fold map iff
    [e ∘ i₁ = id] and [e ∘ i₂ = id] ([ext_fold_iff]).  Then the loops
    [(g, 1)] and [(1, h)], which commute in [BG × BG] ([pair_loops_comm]),
    are sent to [g] and [h].  Conversely, for abelian [G] the
    multiplication [(a, b) ↦ a b] is a homomorphism [G × G → G]
    ([mulG_absHom]), which deloops by [abstr_hom_eqv] (Section 7.5). *)
Definition univvee_fw_pcomp {A1 A2 B C : Ustar} (e : B →* C) (k : wedge A1 A2 →* B)
  : univvee_fw A1 A2 C (pcomp e k)
    = (pcomp e (fst (univvee_fw A1 A2 B k)); pcomp e (snd (univvee_fw A1 A2 B k))).
Proof.
  destruct k as [k kp], e as [e ep].
  refine (ap (fun q => (((e ∘ k ∘ wi1 A1 A2; ap e kp ⋅ ep) : A1 →* C);
                        ((e ∘ k ∘ wi2 A1 A2; q) : A2 →* C))) _).
  refine (ap (fun r => trans (trans ep (ap e kp)) r) (ap_compose k e (wglue A1 A2)) @ _).
  refine (trans_assoc ep (ap e kp) (ap e (ap k (wglue A1 A2))) @ _).
  exact (ap (fun r => r ⋅ ep) (ap_trans e kp (ap k (wglue A1 A2)))^).
Defined.

Definition pair_loops_comm {A : Type} {x x' y y' : A} (p : x = x') (q : y = y')
  : ap (fun w => (x'; w) : A × A) q ⋅ ap (fun z => (z; y) : A × A) p
    = ap (fun z => (z; y') : A × A) p ⋅ ap (fun w => (x; w) : A × A) q.
Proof. destruct p, q. exact refl. Defined.

Definition comm4 {A : Type} {x : A} (a b c d : x = x) (cb : c ⋅ b = b ⋅ c)
  : (a ⋅ c) ⋅ (b ⋅ d) = (a ⋅ b) ⋅ (c ⋅ d).
Proof.
  refine (trans_assoc d b (a ⋅ c) @ _).
  refine (ap (fun r => r ⋅ d) ((trans_assoc b c a)^ @ ap (fun r => a ⋅ r) cb @ trans_assoc c b a) @ _).
  exact (trans_assoc d c (a ⋅ b))^.
Defined.

Section WhatAreAbelian.

  Context `{Funext} (G : Group).

  Local Notation i1 := ((((fun z => (z; sh G)) : utype (BG G) -> utype (BGxBG G)); refl)
                        : BG G →* BGxBG G).
  Local Notation i2 := ((((fun z => (sh G; z)) : utype (BG G) -> utype (BGxBG G)); refl)
                        : BG G →* BGxBG G).

  Definition ext_fold_fw (e : BGxBG G →* BG G) (E : pcomp e (wedge_incl G) = fold_map G)
    : (pcomp e i1; pcomp e i2) = ((pid (BG G); pid (BG G)) : (BG G →* BG G) × (BG G →* BG G))
    := ap (fun w => (pcomp e (fst w); pcomp e (snd w)) : (BG G →* BG G) × (BG G →* BG G))
          (univvee_fw_bw _ _ _ (i1; i2))^
       @ (univvee_fw_pcomp e (wedge_incl G))^ @ ap (univvee_fw _ _ _) E
       @ univvee_fw_bw _ _ _ (pid (BG G); pid (BG G)).

  Definition ext_fold_bw (e : BGxBG G →* BG G)
    (Q : (pcomp e i1; pcomp e i2) = ((pid (BG G); pid (BG G)) : (BG G →* BG G) × (BG G →* BG G)))
    : pcomp e (wedge_incl G) = fold_map G.
  Proof.
    apply (isInj_cancel (isEquiv_isInj (snd (univvee (BG G) (BG G) (BG G))))).
    refine (univvee_fw_pcomp e (wedge_incl G) @ _ @ (univvee_fw_bw _ _ _ (pid (BG G); pid (BG G)))^).
    exact (ap (fun w => (pcomp e (fst w); pcomp e (snd w)) : (BG G →* BG G) × (BG G →* BG G))
              (univvee_fw_bw _ _ _ (i1; i2)) @ Q).
  Defined.

  Definition loops_pid (g : USym G) : loops_fun (pid (BG G)) g = g
    := trans_1p _ @ ap_idmap g.

  Definition ext_fold_isAb (e : BGxBG G →* BG G) (E : pcomp e (wedge_incl G) = fold_map G)
    : isAb G.
  Proof.
    pose (Q := eqinv (snd (path_prod_eqv _ _ _ _)) (ext_fold_fw e E)).
    pose (L1 := fun g => (loops_pid g)^ @ ap (fun k => loops_fun k g) (fst Q)^
                         @ loops_fun_pcomp e i1 g
                         @ ap (loops_fun e) (loops_fun_refl (fun z : utype (BG G) => (z; sh G) : utype (BGxBG G)) g)).
    pose (L2 := fun h => (loops_pid h)^ @ ap (fun k => loops_fun k h) (snd Q)^
                         @ loops_fun_pcomp e i2 h
                         @ ap (loops_fun e) (loops_fun_refl (fun z : utype (BG G) => (sh G; z) : utype (BGxBG G)) h)).
    intros g h.
    refine (ap011 (fun a b => a ⋅ b) (L1 g) (L2 h) @ _ @ (ap011 (fun a b => a ⋅ b) (L2 h) (L1 g))^).
    refine ((loops_fun_comp _ (fst e) _ (snd e) _ _)^ @ _ @ loops_fun_comp _ (fst e) _ (snd e) _ _).
    exact (ap (loops_fun e) (pair_loops_comm g h)^).
  Defined.

  (** For abelian [G], the multiplication is a homomorphism. *)
  Definition snd2 (w : utype (BG G) × utype (BG G)) : utype (BG G) := snd w.

  Definition mulG (l : USym (prodG G G)) : USym G := ap fst l ⋅ ap snd2 l.

  Definition mulG_absHom (ab : isAb G) : absHom (abstr (prodG G G)) (abstr G).
  Proof.
    refine (mulG; _). intros s t. unfold mulG. cbn.
    refine (ap011 (fun a b => a ⋅ b) (ap_trans fst t s) (ap_trans snd2 t s) @ _).
    exact (comm4 _ _ _ _ (ab _ _)).
  Defined.

  Definition mulHom (ab : isAb G) : Hom (prodG G G) G
    := eqinv (abstr_hom_isEquiv (prodG G G) G) (mulG_absHom ab).

  Definition mulHom_i (ab : isAb G) (i : BG G →* BGxBG G)
    (hi : forall g, mulG (loops_fun i g) = g)
    : pcomp (Bf (mulHom ab)) i = pid (BG G).
  Proof.
    change (Bf (compG (mulHom ab) (@mkhom G (prodG G G) i)) = Bf (idG G)).
    apply ap.
    apply (isInj_cancel (isEquiv_isInj (abstr_hom_isEquiv G G))).
    refine (abstr_comp (@mkhom G (prodG G G) i) (mulHom ab) @ _ @ (abstr_id G)^).
    refine (ap (fun φ => absHom_comp φ (abstr_hom (@mkhom G (prodG G G) i)))
              (eqinv_r (abstr_hom_isEquiv (prodG G G) G) (mulG_absHom ab)) @ _).
    apply path_absHom. intro s. exact (hi s).
  Defined.

  Definition isAb_ext_fold (ab : isAb G)
    : {e : BGxBG G →* BG G & pcomp e (wedge_incl G) = fold_map G}.
  Proof.
    exists (Bf (mulHom ab)).
    apply ext_fold_bw. apply (fst (path_prod_eqv _ _ _ _)). split.
    - apply mulHom_i. intro g.
      refine (ap mulG (loops_fun_refl (fun z : utype (BG G) => (z; sh G) : utype (BGxBG G)) g) @ _).
      refine (ap011 (fun a b => a ⋅ b)
                ((ap_compose (fun z : utype (BG G) => (z; sh G) : utype (BGxBG G)) fst g)^ @ ap_idmap g)
                ((ap_compose (fun z : utype (BG G) => (z; sh G) : utype (BGxBG G)) snd2 g)^ @ ap_const g (sh G))
              @ _).
      exact (trans_1p g).
    - apply mulHom_i. intro h.
      refine (ap mulG (loops_fun_refl (fun z : utype (BG G) => (sh G; z) : utype (BGxBG G)) h) @ _).
      exact (ap011 (fun a b => a ⋅ b)
               ((ap_compose (fun z : utype (BG G) => (sh G; z) : utype (BGxBG G)) fst h)^ @ ap_const h (sh G))
               ((ap_compose (fun z : utype (BG G) => (sh G; z) : utype (BGxBG G)) snd2 h)^ @ ap_idmap h)).
  Defined.

End WhatAreAbelian.

Definition xca_whatAREabeliangroups `{Funext} : xca_whatAREabeliangroups_stmt
  := fun G => (isAb_ext_fold G, fun w => ext_fold_isAb G (fst w) (snd w)).

(** Lemma [lem:wedgeofgpoidisgpoid] (statement only): the wedge of the
    classifying types of decidable groups is a groupoid. *)
Definition lem_wedgeofgpoidisgpoid_stmt : Type
  := forall G1 G2 : Group, isDecSet (USym G1) -> isDecSet (USym G2) ->
       isGrpd (wedgeT (BG G1) (BG G2)).
