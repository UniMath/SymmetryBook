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

    Left out (statements only, no proofs yet; time limit per result)
    - Exercise [xca:whatAREabeliangroups]
      ([xca_whatAREabeliangroups_stmt], with [fold_map] and
      [wedge_incl]) and lemma [lem:wedgeofgpoidisgpoid]
      ([lem_wedgeofgpoidisgpoid_stmt]; the book's proof uses words for
      decidable groups).
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

(** Exercise [xca:whatAREabeliangroups] (statement only): [G] is abelian
    iff the fold map [BG ∨ BG →* BG] extends over the inclusion
    [BG ∨ BG →* BG × BG]. *)
Definition BGxBG (G : Group) : Ustar := (utype (BG G) × utype (BG G); (sh G; sh G)).

Definition fold_map (G : Group) : wedge (BG G) (BG G) →* BG G
  := univvee_bw (BG G) (BG G) (BG G) (pid (BG G); pid (BG G)).

Definition wedge_incl (G : Group) : wedge (BG G) (BG G) →* BGxBG G
  := univvee_bw (BG G) (BG G) (BGxBG G)
       ((((fun z => (z; sh G)) : utype (BG G) -> utype (BGxBG G)); refl);
        (((fun z => (sh G; z)) : utype (BG G) -> utype (BGxBG G)); refl)).

Definition xca_whatAREabeliangroups_stmt : Type
  := forall G : Group,
       isAb G <-> {e : BGxBG G →* BG G & pcomp e (wedge_incl G) = fold_map G}.

(** Lemma [lem:wedgeofgpoidisgpoid] (statement only): the wedge of the
    classifying types of decidable groups is a groupoid. *)
Definition lem_wedgeofgpoidisgpoid_stmt : Type
  := forall G1 G2 : Group, isDecSet (USym G1) -> isDecSet (USym G2) ->
       isGrpd (wedgeT (BG G1) (BG G2)).
