(** * Section 4.2 The type of groups

    Part of Chapter 4 ([group.tex]); see [Group.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:pt-conn-groupoid]: [UUscone] ([U_*^{=1}]), with the
      underlying pointed type [UUscone_ptd].
    - Exercise [xca:defgroup] ([isConn_from_pt], [pt_from_isConn],
      [isGrpd_loops], [loops_isGrpd], [UUscone_eqv]).  The book's
      "[A] is a groupoid iff [a = a] is a set" needs [A] connected for the
      converse; we assume it there.
    - Definition [def:typegroup]: [Group :≡ Copy(UUscone)] with
      constructor [mkgroup]; [def:classifying-type]: [B], [BG], [sh];
      [def:looptype]: [loops] ([Ω]); [def:group-symmetries]: [USym] ([U]),
      a set; [def:finite-group]: [isFinGroup], [CardG].
    - Remark [rem:aut]: [Group ≃ UUscone], identifications of groups are
      identifications of classifying types ([path_Group_eqv],
      [UUscone_paths_eqv]), and pointed equivalences of classifying types
      give identifications of groups ([path_Group], univalence).
    - Definition [def:automorphism-group]: [AutG gA a] for a groupoid [A]
      (with proof [gA]); the name [Aut] is taken by [X ≃ X] (Section 3.7).
      Remark [rem:symmetriesofnonconnectedgroupoids] ([group_is_AutG]).
    - Examples: [ZZ] ([ex:circlegroup]), the trivial group [TG], the
      permutation groups [SG_S], [SG n] ([ex:groups]), the cyclic groups
      [CG k] (for [m = k+1], with [Cyc_isGrpd]) and [ZmodmZ k]
      ([ex:cyclicgroups]), products [prodG] and [Klein]
      ([ex:productofgroups]) with [USym_prodG], finite products [PiG] with
      [USym_PiG] ([ex:bigproductofgroups], [xca:bigproductfunext](1), via
      the library's [finite_choice]).
    - Exercise [xca:groups] ([xca_groups]): two identifications
      [ℤ = Aut_Cyc(ℤ, zs)], from the equivalence [c : S1 ≃ InfCyc] of 3.5
      (with [InfCyc] the component of [(ℤ, zs)] in [Cyc]) and from [c]
      composed with [-id].  They differ because the pointed equivalence
      can be recovered from an identification of groups
      ([path_Group_pEqv_path_Group]) and [id ≠ -id] (3.4).
    - Exercise [xca:group-example-details]: [AutProp_trivial],
      [AutG_set_trivial], [contr_group_trivial], [SG0_trivial],
      [SG1_trivial], [SG_False_trivial], and [AutFinSet_SG], from the
      general [AutG_subtype] (components of a subtype are components of
      the ambient type); [Aut_Set(ℕ) = Aut_Set(ℤ)] ([SG_N_Z]), from the
      bijection [0, 1, 2, 3, … ↦ 0, -1, 1, -2, …] ([nat_Int]).
    - Exercise [xca:CG2isSG2] ([xca_CG2isSG2]): the fiber of [R_2] at
      [Fin 2] is connected, since every symmetry of [Fin 2] is [R_2] of
      [refl] or of [loop] ([RmFin1_loops]).
    - Exercise [xca:RmloopCGm] ([xca_RmloopCGm]): a symmetry [σ] of
      [Fin m] comes from a symmetry of [sh_{C'_m}] iff it is merely a
      power of [R_m(loop) = zs]; a symmetry of [sh_{C'_m}] is given by a
      loop [l] in [S1] ([Cm'_sym]), using that equal elements of a set
      truncation are merely equal.
    - Exercise [xca:klein-not-cyclic] ([xca_klein_not_cyclic]): every
      symmetry [g] of [Σ_2 × Σ_2] has [g g = refl] ([Klein_sq]), but the
      generator of [C_4] does not ([CG_gen_sq_ne]).
    - Exercise [xca:bigproductfunext](2) ([xca_bigproductfunext_2]).
    - Definition [def:abgp]: [isAb], a proposition, and [AbGroup];
      [ZZ_isAb]; exercise [exer:first examples]: [SG2_isAb], [prodG_isAb]
      and [SG3_not_isAb] (two transpositions of [Fin 3] do not commute).
      Commutation is reflected along injective maps ([comm_reflect]) and
      carried forward along them ([comm_forward]).
    - The exercise that [mkgroup(A,a)] and [mkgroup(A,b)] are merely
      identical ([mkgroup_merely_eq]).

    - The chain of identifications in [ex:cyclicgroups], end to end
      ([ex_cyclicgroups_chain]: [C_m = Z/mZ]).  The components of
      [Fincyc] in [Cyc] and of [R_m] in [S1 → Set] correspond under the
      inclusion [Cyc ⊆ ∑_{X:Set}(X ≃ X)] ([comp_sub_eqv]) and the
      equivalence [gSet] of 3.3 ([comp_eqv], [gSet_RmSet]).

    Left out (statements only, no proofs yet; time limit per result)
    - Example [ex:Cm] ([ex_Cm_stmt], with [RmFin], [BCm'], [shCm']).
    - [xca:typegroupisgroupoid] is postponed to Section 4.4
      ([Group_isGrpd]), where it follows from [lem:hom-is-set].
    - Size issues: [Aut_Group(G)] is a group in a larger universe than
      [G] ([AutGrp], Section 9.7).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Types.Sum Truncations.Core Truncations.SeparatedTrunc
  Spaces.Circle Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite Spaces.Int Projective.
From SymmetryBook Require Export Circle.Circle.

Local Open Scope uf_scope.

(** ** 4.2 The type of groups *)

(** Example [ex:base=base]: the symmetries [base = base] in the circle
    form the integers ([cor:S1groupoid] in 3.4); the group [ZZ] below. *)

(** Remark [rem:heap-preview]: identity types [a = a'] with [a ≠ a'] are
    heaps, see 7.7 (informal). *)

(** Definition [def:pt-conn-groupoid]: pointed connected groupoids
    [U_*^{=1} :≡ ∑_{A:U} (A × isConn(A) × isGrpd(A))]. *)
Definition UUscone : Type := {A : Type & A × (isConn A × isGrpd A)}.

(** The underlying pointed type of a pointed connected groupoid. *)
Definition UUscone_ptd (X : UUscone) : Ustar := (fst X; fst (snd X)).

Definition UUscone_isConn (X : UUscone) : isConn (fst X) := fst (snd (snd X)).

Definition UUscone_isGrpd (X : UUscone) : isGrpd (fst X) := snd (snd (snd X)).

(** Exercise [xca:defgroup]. *)
Section DefGroup.

  Context {A : Type} (a : A).

  Definition isConn_from_pt (h : forall x : A, ptrunc (a = x)) : isConn A.
  Proof.
    refine (trunc a; _).
    intros x y.
    refine (ptrunc_rec ptrunc_isProp _ (h x)); intro p.
    refine (ptrunc_rec ptrunc_isProp _ (h y)); intro q.
    exact (trunc (q ⋅ p⁻¹)).
  Defined.

  Definition pt_from_isConn (c : isConn A) : forall x : A, ptrunc (a = x)
    := snd c a.

  Definition isGrpd_loops (g : isGrpd A) : isSet (a = a) := g a a.

  (** The converse needs connectedness (as everywhere in this section). *)
  Definition loops_isGrpd `{Funext} (c : isConn A) (s : isSet (a = a)) : isGrpd A.
  Proof.
    intros x y.
    refine (ptrunc_rec (isSet_isProp _) _ (snd c a x)); intro p.
    destruct p.
    refine (ptrunc_rec (isSet_isProp _) _ (snd c a y)); intro q.
    destruct q. exact s.
  Defined.

End DefGroup.

Definition isConn_isProp `{Funext} (A : Type) : isProp (isConn A)
  := prod_isProp ptrunc_isProp
       (Pi_isProp (fun x => Pi_isProp (fun y => ptrunc_isProp))).

(** The equivalence of exercise [xca:defgroup]. *)
Definition UUscone_eqv `{Funext}
  : UUscone ≃ {A : Type & {a : A & (forall x : A, ptrunc (a = x)) × isSet (a = a)}}.
Proof.
  refine (Eqv_of_Equiv (equiv_functor_sigma_id (fun A => _))).
  refine (Equiv_of_Eqv (Eqv_of_Equiv (equiv_functor_sigma_id (fun a => _)))).
  refine (Equiv_of_Eqv (Eqv_of_props
            (prod_isProp (isConn_isProp A) (isGrpd_isProp A))
            (prod_isProp (Pi_isProp (fun x => ptrunc_isProp)) (isSet_isProp _))
            (fun w => (pt_from_isConn a (fst w); isGrpd_loops a (snd w)))
            (fun w => (isConn_from_pt a (fst w);
                       loops_isGrpd a (isConn_from_pt a (fst w)) (snd w))))).
Defined.

(** Definition [def:typegroup]: the type of groups, a wrapped copy of
    [U_*^{=1}] with constructor [mkgroup] (the book's underlined [Ω]). *)
Definition Group : Type := Copy UUscone.

Definition mkgroup (X : UUscone) : Group := inc X.

(** Definition [def:classifying-type]: the destructor [B], the
    classifying type [BG] and the designated shape [sh_G]. *)
Definition B (G : Group) : UUscone := out G.

Definition BG (G : Group) : Ustar := UUscone_ptd (B G).

Definition sh (G : Group) : utype (BG G) := pt (BG G).

Definition BG_isConn (G : Group) : isConn (utype (BG G)) := UUscone_isConn (B G).

Definition BG_isGrpd (G : Group) : isGrpd (utype (BG G)) := UUscone_isGrpd (B G).

Definition B_mkgroup (X : UUscone) : B (mkgroup X) = X := refl.

(** Definition [def:looptype]: [ΩX :≡ (a = a)], pointed at [refl a]. *)
Definition loops (X : Ustar) : Ustar := ((pt X = pt X); refl).

(** Definition [def:group-symmetries]: the symmetries [UG :≡ Ω BG] in
    [G]; it is a set. *)
Definition USym (G : Group) : Type := utype (loops (BG G)).

Definition USym_isSet (G : Group) : isSet (USym G) := BG_isGrpd G (sh G) (sh G).

(** Definition [def:finite-group]. *)
Definition isFinGroup (G : Group) : Type := isFinSet (USym G).

Definition CardG (G : Group) (h : isFinGroup G) : ℕ
  := Card (((USym G; USym_isSet G) : SetU); h).

(** Remark [rem:aut]: [Group ≃ U_*^{=1}], and identifications of groups
    correspond to identifications of classifying types. *)
Definition Group_eqv : Group ≃ UUscone := Copy_eqv UUscone.

Definition path_Group_eqv (X Y : UUscone) : (mkgroup X = mkgroup Y) ≃ (X = Y)
  := path_inc_eqv X Y.

(** [U_*^{=1}] as a subtype of the pointed types. *)
Definition UUscone_sub : UUscone ≃ {X : Ustar & isConn (utype X) × isGrpd (utype X)}
  := mkEqv (fun X : UUscone => ((fst X; fst (snd X)); snd (snd X))
              : {X : Ustar & isConn (utype X) × isGrpd (utype X)})
           (fun w => (fst (fst w); (snd (fst w); snd w)) : UUscone)
           (fun _ => refl) (fun _ => refl).

Definition isConnGrpd_isProp `{Funext} (X : Ustar)
  : isProp (isConn (utype X) × isGrpd (utype X))
  := prod_isProp (isConn_isProp _) (isGrpd_isProp _).

(** Identifications in [U_*^{=1}] are identifications of the underlying
    pointed types. *)
Definition UUscone_paths_eqv `{Funext} (X Y : UUscone)
  : (X = Y) ≃ (UUscone_ptd X = UUscone_ptd Y)
  := Eqv_comp (Eqv_of_Equiv (equiv_ap' (Equiv_of_Eqv UUscone_sub) X Y))
       (subtype_paths_eqv isConnGrpd_isProp (fst UUscone_sub X) (fst UUscone_sub Y)).

(** By univalence, a pointed equivalence of classifying types gives an
    identification of groups. *)
Definition path_Group `{Univalence} {G G' : Group} (e : BG G ≃* BG G') : G = G'.
Proof.
  refine ((inc_out G') ⋅ _ ⋅ (inc_out G)⁻¹).
  refine (ap inc _).
  refine (eqinv (snd (UUscone_paths_eqv (B G) (B G'))) _).
  exact (eqinv (path_to_pEqv_isEquiv (BG G) (BG G')) e).
Defined.

(** Remark [rem:BG-convention]: to define [f : ∏_{G:Group} T(G)] it
    suffices to define [f(mkgroup X)], [Group] being a wrapped copy of
    [U_*^{=1}] with constructor [mkgroup] (informal convention). *)

(** Definition [def:automorphism-group]: [Aut_A(a) :≡ mkgroup(A_(a), (a,!))]
    for a groupoid [A].  We call it [AutG] since [Aut X :≡ (X ≃ X)] is
    already used in Section 3.7. *)
Definition component_isGrpd `{Funext} {A : Type} (gA : isGrpd A) (a : A)
  : isGrpd (component A a)
  := Sigma_ntype 1 gA (fun x => prop_ntype 1 _ ptrunc_isProp).

Definition AutG `{Funext} {A : Type} (gA : isGrpd A) (a : A) : Group
  := mkgroup (component A a; ((a; trunc refl);
                (component_isConn a; component_isGrpd gA a))).

(** Remark [rem:symmetriesofnonconnectedgroupoids]: for connected [A],
    [fst : (A_(a), (a,!)) → (A, a)] is a pointed equivalence, so
    [mkgroup(A,a) = Aut_A(a)]. *)
Definition component_fst_isEquiv `{Funext} {A : Type} (cA : isConn A) (a : A)
  : isEquiv (@fst A (fun x => ptrunc (a = x))).
Proof.
  refine (iso_to_isEquiv _ (fun x => (x; snd cA a x)) _ _).
  - intros [x p].
    exact (@path_sigma_prop _ (fun x => ptrunc (a = x)) (fun _ => ptrunc_isProp)
             (x; snd cA a x) (x; p) refl).
  - intro x. exact refl.
Defined.

Definition group_is_AutG `{Univalence} (G : Group)
  : G = AutG (BG_isGrpd G) (sh G).
Proof.
  refine (path_Group (G := AutG (BG_isGrpd G) (sh G)) _)⁻¹.
  exact ((@fst _ (fun x => ptrunc (sh G = x)); refl);
         component_fst_isEquiv (BG_isConn G) (sh G)).
Defined.

(** Symmetries in [Aut_A(a)] are symmetries of [a] in [A]
    ([rem:whypointedconngpoid]); [ap fst] preserves composition. *)
Definition USym_AutG_eqv `{Funext} {A : Type} (gA : isGrpd A) (a : A)
  : USym (AutG gA a) ≃ (a = a)
  := subtype_paths_eqv (fun _ => ptrunc_isProp) (a; trunc refl) (a; trunc refl).

(** ** Groups with contractible classifying type *)

Definition map_contr_isEquiv {X Y : Type} (cX : isContr X) (cY : isContr Y)
  (f : X -> Y) : isEquiv f
  := fun y => Sigma_isContr cX
       (fun x => isProp_inhabited_isContr (prop_is_set (isContr_isProp' cY) y (f x))
                   (isContr_isProp' cY y (f x))).

(** Any two groups with contractible classifying types can be
    identified. *)
Definition path_Group_contr `{Univalence} {G G' : Group}
  (c : isContr (utype (BG G))) (c' : isContr (utype (BG G'))) : G = G'
  := path_Group (((fun _ => sh G'); refl); map_contr_isEquiv c c' _).

(** [Aut_A(a)] has a contractible classifying type when [a = a] is a
    proposition. *)
Definition AutG_contr `{Funext} {A : Type} (gA : isGrpd A) (a : A)
  (h : isProp (a = a)) : isContr (utype (BG (AutG gA a))).
Proof.
  refine (conn_loops_prop_isContr (component_isConn a) _).
  intros [x p].
  refine (isProp_Eqv (Eqv_inv (subtype_paths_eqv (fun _ => ptrunc_isProp) (x; p) (x; p))) _).
  refine (ptrunc_rec (isProp_isProp _) _ p). intro q. destruct q. exact h.
Defined.

(** ** First examples *)

Section FirstExamples.

  Context `{Univalence}.

  (** Example [ex:circlegroup]: the group of integers [ℤ :≡ mkgroup(S1, base)]
      (we write [ZZ]). *)
  Definition ZZ : Group := mkgroup (S1; (base; (S1_isConn; S1_isGrpd))).

  Definition ZZ_AutG : ZZ = AutG S1_isGrpd base := group_is_AutG ZZ.

  (** Example [ex:groups](1), item [ex:trivgroup]: the trivial group [𝟙 :≡ Aut_Prop(True)]. *)
  Definition PropU_isGrpd : isGrpd PropU := set_ntype 1 PropU_isSet.

  Definition TrueProp : PropU := (True; True_isProp).

  Definition TG : Group := AutG PropU_isGrpd TrueProp.

  Definition TG_contr : isContr (utype (BG TG))
    := AutG_contr _ _ (PropU_isSet _ _).

  (** Exercise [xca:group-example-details], first part: [Aut_Prop(P)] is
      trivial for any proposition [P], and so is [Aut_S(x)] for any set [S]. *)
  Definition AutG_set_trivial {S : Type} (sS : isSet S) (x : S)
    : AutG (set_ntype 1 sS) x = TG
    := path_Group_contr (AutG_contr _ _ (sS x x)) TG_contr.

  Definition AutProp_trivial (P : PropU) : AutG PropU_isGrpd P = TG
    := path_Group_contr (AutG_contr _ _ (PropU_isSet _ _)) TG_contr.

  (** The trivial group is [mkgroup(C, c)] for any contractible [C]. *)
  Definition contr_UUscone {C : Type} (c : isContr C) : UUscone
    := (C; (fst c; (isConn_from_pt (fst c) (fun x => trunc (snd c x));
                    prop_ntype 1 _ (isContr_isProp' c)))).

  Definition contr_group_trivial {C : Type} (c : isContr C)
    : mkgroup (contr_UUscone c) = TG
    := path_Group_contr (G := mkgroup (contr_UUscone c)) c TG_contr.

  (** Example [ex:groups](2, 3), items [ex:permgroup] and
      [ex:genpermgroup]: the permutation groups [Σ_S :≡ Aut_Set(S)]
      and [Σ_n :≡ Aut_Set(Fin n)]. *)
  Definition SG_S (S : SetU) : Group := AutG SetU_isGrpd S.

  Definition FinSetU (n : ℕ) : SetU := (Fin n; Fin_isSet n).

  Definition SG (n : ℕ) : Group := SG_S (FinSetU n).

  (** Symmetries in [Σ_S] are identifications [S = S] of types. *)
  Definition USym_SG_S_eqv (S : SetU) : USym (SG_S S) ≃ (fst S = fst S)
    := Eqv_comp (USym_AutG_eqv SetU_isGrpd S)
         (subtype_paths_eqv (fun X => isSet_isProp X) S S).

  (** Exercise [xca:group-example-details]: [Σ_0], [Σ_1] and [Σ_False]
      are trivial. *)
  Definition SG_S_prop_trivial (S : SetU) (h : isProp (fst S)) : SG_S S = TG.
  Proof.
    refine (path_Group_contr (AutG_contr _ _ _) TG_contr).
    refine (isProp_Eqv (Eqv_inv (subtype_paths_eqv (fun X => isSet_isProp X) S S)) _).
    exact (isProp_Eqv (Eqv_inv ((@idtoeqv _ _; ua _ _) : (fst S = fst S) ≃ _))
             (Eqv_props_isProp h)).
  Defined.

  Definition SG0_trivial : SG 0 = TG
    := SG_S_prop_trivial (FinSetU 0) (fun x : Fin 0 => match x with end).

  Definition SG1_trivial : SG 1 = TG := SG_S_prop_trivial (FinSetU 1) Fin1_isProp.

  Definition False_isProp' : isProp False := fun x : False => match x with end.

  Definition SG_False_trivial : SG_S (False; prop_is_set False_isProp') = TG
    := SG_S_prop_trivial (False; prop_is_set False_isProp') False_isProp'.
  (** Components of a subtype are components of the ambient type. *)
  Definition AutG_subtype {A : Type} {Q : A -> Type} (hQ : forall x, isProp (Q x))
    (gS : isGrpd {x : A & Q x}) (gA : isGrpd A) (w : {x : A & Q x})
    : AutG gS w = AutG gA (fst w).
  Proof.
    apply path_Group.
    pose (f := fun v : component _ w =>
                 (fst (fst v); ptrunc_rec ptrunc_isProp (fun p => trunc (ap fst p)) (snd v))
                 : component A (fst w)).
    pose (g := fun u : component A (fst w) =>
                 ((fst u; ptrunc_rec (hQ _) (fun r : fst w = fst u => trp Q r (snd w)) (snd u));
                  ptrunc_rec ptrunc_isProp
                    (fun r : fst w = fst u => trunc (path_sigma_prop hQ (u := w)
                                                       (v := (fst u; _)) r)) (snd u))
                 : component _ w).
    refine ((f; refl); iso_to_isEquiv f g _ _).
    - intro v. apply (path_sigma_prop (fun _ => ptrunc_isProp)).
      exact (@path_sigma_prop _ _ hQ (fst (g (f v))) (fst v) refl).
    - intro u. apply (path_sigma_prop (fun _ => ptrunc_isProp)). exact refl.
  Defined.

  (** Exercise [xca:group-example-details]: [Aut_FinSet(Fin n) = Σ_n]. *)
  Definition FinSet_isGrpd : isGrpd FinSet
    := Sigma_ntype 1 SetU_isGrpd (fun S => prop_ntype 1 _ ptrunc_isProp).

  Definition FinSetF (n : ℕ) : FinSet := (FinSetU n; trunc (n; refl)).

  Definition AutFinSet_SG (n : ℕ) : AutG FinSet_isGrpd (FinSetF n) = SG n
    := AutG_subtype (fun S => ptrunc_isProp) FinSet_isGrpd SetU_isGrpd (FinSetF n).

  (** Example [ex:cyclicgroups]: the cyclic group [C_m :≡ Aut_Cyc(Fin m, zs)]
      for [m = k+1], and [ℤ/mℤ :≡ Aut_{S1 → Set}(R_m)]. *)
  Definition Cyc_isGrpd : isGrpd Cyc.
  Proof.
    refine (Sigma_ntype 1 SetU_isGrpd (fun X => Sigma_ntype 1 _ (fun t => prop_ntype 1 _ _))).
    - exact (set_ntype 1 (Eqv_sets_isSet (snd X))).
    - exact (prod_isProp ptrunc_isProp
               (Pi_isProp (fun x => Pi_isProp (fun x' => snd (conn_by t x x'))))).
  Defined.

  Definition CG (k : ℕ) : Group := AutG Cyc_isGrpd (Fincyc k).

  Definition RmSet (k : ℕ) : S1 -> SetU := fun z => (Rm k z; Rm_isSet k z).

  Definition ZmodmZ (k : ℕ) : Group
    := AutG (fun_ntype 1 SetU_isGrpd) (RmSet k).

  (** [InfCyc] is the component of [(ℤ, zs)] in [Cyc]. *)
  Definition CycP_Zs : CycP Zs := (ℤ_isSet; (snd zsEqv; Z_isCycle)).

  Definition IC_to_cyc (w : InfCyc) : component Cyc Zcyc.
  Proof.
    pose (Cp := ptrunc_rec (CycP_isProp _) (fun p => trp CycP p CycP_Zs) (snd w)).
    refine (cyc_of (fst w; Cp); _).
    exact (ptrunc_rec ptrunc_isProp
             (fun p : Zs = fst w => trunc (cyc_path Zcyc (cyc_of (fst w; Cp)) p)) (snd w)).
  Defined.

  Definition cyc_to_IC (d : component Cyc Zcyc) : InfCyc
    := (cyc_endo (fst d); ptrunc_rec ptrunc_isProp (fun p => trunc (ap cyc_endo p)) (snd d)).

  Definition IC_to_cyc_isEquiv : isEquiv IC_to_cyc.
  Proof.
    refine (iso_to_isEquiv _ cyc_to_IC _ _).
    - intro w. exact (path_sigma_prop (fun _ => ptrunc_isProp) (u := cyc_to_IC (IC_to_cyc w))
                        (v := w) refl).
    - intro d. exact (path_sigma_prop (fun _ => ptrunc_isProp) (u := IC_to_cyc (cyc_to_IC d))
                        (v := d) (cyc_path (fst (IC_to_cyc (cyc_to_IC d))) (fst d) refl)).
  Defined.

  (** The pointed equivalence [S1 ≃ Cyc_(ℤ,zs)], [z ↦ c(z)]. *)
  Definition f1 : S1 -> component Cyc Zcyc := IC_to_cyc ∘ c.

  Definition f1_isEquiv : isEquiv f1 := comp_isEquiv c_isEquiv IC_to_cyc_isEquiv.

  Definition f1_pt : (Zcyc; trunc refl) = f1 base
    := path_sigma_prop (fun _ => ptrunc_isProp) (u := ((Zcyc; trunc refl) : component Cyc Zcyc)) (v := f1 base)
         (cyc_path Zcyc (fst (f1 base)) refl).

  Definition e1 : BG ZZ ≃* BG (AutG Cyc_isGrpd Zcyc) := ((f1; f1_pt); f1_isEquiv).

  Definition e2 : BG ZZ ≃* BG (AutG Cyc_isGrpd Zcyc)
    := ((f1 ∘ negid; f1_pt); comp_isEquiv (snd negidEqv) f1_isEquiv).

  (** The pointed equivalence underlying an identification of groups. *)
  Definition path_Group_pEqv {G G' : Group} (p : G = G') : BG G ≃* BG G'
    := path_to_pEqv (fst (UUscone_paths_eqv (B G) (B G')) (ap B p)).

  Definition path_Group_pEqv_path_Group (X Y : UUscone)
    (e : BG (mkgroup X) ≃* BG (mkgroup Y))
    : path_Group_pEqv (path_Group e) = e.
  Proof.
    unfold path_Group_pEqv, path_Group.
    refine (ap (fun r : mkgroup X = mkgroup Y =>
                  path_to_pEqv (fst (UUscone_paths_eqv X Y) (ap out r))) (trans_1p _) @ _).
    refine (ap (fun r : X = Y => path_to_pEqv (fst (UUscone_paths_eqv X Y) r))
              ((ap_compose inc out _)^ @ ap_idmap _) @ _).
    refine (ap path_to_pEqv (eqinv_r (snd (UUscone_paths_eqv X Y)) _) @ _).
    exact (eqinv_r (path_to_pEqv_isEquiv _ _) e).
  Defined.

  (** Exercise [xca:groups]: two different identifications
      [ℤ = Aut_Cyc(ℤ, zs)], from [c] and from [c ∘ (-id)].  They are
      different since the pointed equivalence can be recovered from the
      identification ([path_Group_pEqv_path_Group]) and [id ≠ -id]
      ([id_negid_not_conn]).
    (Placed after [ex:cyclicgroups], since it uses [Cyc_isGrpd].) *)
  Definition xca_groups
    : {p : ZZ = AutG Cyc_isGrpd Zcyc & {q : ZZ = AutG Cyc_isGrpd Zcyc & p ≠ q}}.
  Proof.
    refine (path_Group e1; (path_Group e2; _)).
    intro h.
    pose (h1 := (path_Group_pEqv_path_Group _ _ e1)^ @ ap path_Group_pEqv h
                @ path_Group_pEqv_path_Group _ _ e2).
    pose (h2 := ap (fun e : BG ZZ ≃* BG (AutG Cyc_isGrpd Zcyc) => fst (fst e)) h1).
    apply id_negid_not_conn. apply trunc. apply ptw_inv. intro x.
    exact (Eqv_inj (f1; f1_isEquiv) (ptw h2 x)).
  Defined.

  (** The identification [Aut_Set(ℕ) = Aut_Set(ℤ)] of exercise
      [xca:group-example-details], from an explicit bijection [ℕ ≃ Int]:
      [0, 1, 2, 3, 4, …] ↦ [0, -1, 1, -2, 2, …]. *)
  Fixpoint dbl (k : nat) : nat := match k with O => O | S k => S (S (dbl k)) end.

  Definition int_to_nat (z : Int) : nat
    := match z with negS k => S (dbl k) | zero => O | posS k => S (S (dbl k)) end.

  Definition int_shift (z : Int) : Int
    := match z with negS k => negS (S k) | zero => posS O | posS k => posS (S k) end.

  Fixpoint nat_to_int (n : nat) : Int
    := match n with
       | O => zero
       | S O => negS O
       | S (S n) => int_shift (nat_to_int n)
       end.

  Definition int_to_nat_shift (z : Int) : int_to_nat (int_shift z) = S (S (int_to_nat z)).
  Proof. destruct z; exact refl. Defined.

  Fixpoint nat_int_nat (n : nat) : int_to_nat (nat_to_int n) = n
    := match n with
       | O => refl
       | S O => refl
       | S (S n) => int_to_nat_shift (nat_to_int n) @ ap (fun m => S (S m)) (nat_int_nat n)
       end.

  Definition int_nat_int (z : Int) : nat_to_int (int_to_nat z) = z.
  Proof.
    destruct z as [k| |k].
    - induction k as [|k IH]; [exact refl|]. exact (ap int_shift IH).
    - exact refl.
    - induction k as [|k IH]; [exact refl|]. exact (ap int_shift IH).
  Defined.

  Definition nat_Int : nat ≃ Int := mkEqv nat_to_int int_to_nat nat_int_nat int_nat_int.

  Definition SG_N_Z : SG_S (ℕ; ℕ_isSet) = SG_S (ℤ; ℤ_isSet).
  Proof.
    apply ap.
    refine (path_sigma_prop (fun X => isSet_isProp X) _).
    exact (etop (Eqv_comp nat_Int (Eqv_inv ℤ_Int))).
  Defined.

  (** The chain of identifications in example [ex:cyclicgroups], end to
      end: [C_m = Aut_{S1 → Set}(R_m)]. *)
  Definition ex_cyclicgroups_chain_stmt : Type := forall k : ℕ, CG k = ZmodmZ k.

  (** Components along an equivalence [e] with [e(a) = b]. *)
  Definition comp_eqv {A B : Type} (e : A ≃ B) {a : A} {b : B} (q : fst e a = b)
    : component A a ≃ component B b.
  Proof.
    refine (mkEqv (fun w => (fst e (fst w); ptrunc_rec ptrunc_isProp
                               (fun p => trunc (q^ @ ap (fst e) p)) (snd w)))
              (fun w => (eqinv (snd e) (fst w); ptrunc_rec ptrunc_isProp
                           (fun p => trunc ((eqinv_l (snd e) a)^ @ ap (eqinv (snd e)) (q @ p)))
                           (snd w))) _ _).
    - intro w. apply (path_sigma_prop (fun _ => ptrunc_isProp)). exact (eqinv_l (snd e) (fst w)).
    - intro w. apply (path_sigma_prop (fun _ => ptrunc_isProp)). exact (eqinv_r (snd e) (fst w)).
  Defined.

  (** The component of a subtype is the component of the ambient type. *)
  Definition comp_sub_eqv {A : Type} {P : A -> Type} (hP : forall x, isProp (P x)) (a : A) (pa : P a)
    : component {x : A & P x} (a; pa) ≃ component A a.
  Proof.
    refine (mkEqv (fun w => (fst (fst w); ptrunc_rec ptrunc_isProp
                               (fun p => trunc (ap fst p)) (snd w)))
              (fun w => ((fst w; ptrunc_rec (hP _) (fun p => trp P p pa) (snd w));
                         ptrunc_rec ptrunc_isProp
                           (fun p => trunc (path_sigma_prop hP (u := (a; pa))
                                              (v := (fst w; ptrunc_rec (hP _) (fun p => trp P p pa) (snd w))) p))
                           (snd w))) _ _).
    - intro w. apply (path_sigma_prop (fun _ => ptrunc_isProp)).
      apply (path_sigma_prop hP). exact refl.
    - intro w. apply (path_sigma_prop (fun _ => ptrunc_isProp)). exact refl.
  Defined.

  (** Cycles as a subtype of [∑_{X:Set} (X ≃ X)]. *)
  Local Notation TSet := {X : SetU & fst X ≃ fst X}.

  Definition CycQ (w : TSet) : Type
    := ptrunc (fst (fst w)) × (forall x x' : fst (fst w), fst (conn_by (snd w) x x')).

  Definition CycQ_isProp (w : TSet) : isProp (CycQ w)
    := prod_isProp ptrunc_isProp
         (Pi_isProp (fun x => Pi_isProp (fun x' => snd (conn_by (snd w) x x')))).

  Definition cyc_T_eqv : Cyc ≃ {w : TSet & CycQ w}
    := mkEqv (fun c : Cyc => ((fst c; fst (snd c)); snd (snd c)) : {w : TSet & CycQ w})
         (fun v : {w : TSet & CycQ w} => (fst (fst v); (snd (fst v); snd v)) : Cyc)
         (fun _ => refl) (fun _ => refl).

  (** [g(R_m) = (Fin m, s)], with [g] as in [gSet]. *)
  Definition gSet_RmSet (k : ℕ)
    : fst gSet (RmSet k) = ((Fin (S k); Fin_isSet (S k)); finsuccEqv k).
  Proof.
    refine (ap (fun s => ((Fin (S k); s); idtoeqv (ap fst (ap (RmSet k) loop))) : TSet)
              (isSet_isProp _ (Rm_isSet k base) (Fin_isSet (S k))) @ _).
    refine (ap (fun E => ((Fin (S k); Fin_isSet (S k)); E) : TSet) _).
    refine (ap idtoeqv ((ap_compose (RmSet k) fst loop)^ @ S1_rec_loop _ _ _) @ _).
    exact (ptoe_etop (finsuccEqv k)).
  Defined.

  Definition cyc_chain_eqv (k : ℕ) : utype (BG (CG k)) ≃ utype (BG (ZmodmZ k))
    := Eqv_comp (comp_eqv cyc_T_eqv (a := Fincyc k) refl)
         (Eqv_comp (comp_sub_eqv CycQ_isProp ((Fin (S k); Fin_isSet (S k)); finsuccEqv k) (snd (snd (Fincyc k))))
            (comp_eqv (Eqv_inv gSet)
               (ap (eqinv (snd gSet)) (gSet_RmSet k)^ @ eqinv_l (snd gSet) (RmSet k)))).

  (** The chain of identifications in example [ex:cyclicgroups]: [C_m]
      and [Z/mZ] are the automorphism groups of corresponding points
      under [Cyc ⊆ ∑_{X:Set} (X ≃ X) ≃ (S1 → Set)]. *)
  Definition ex_cyclicgroups_chain : ex_cyclicgroups_chain_stmt.
  Proof.
    intro k. refine (path_Group ((fst (cyc_chain_eqv k); _); snd (cyc_chain_eqv k))).
    exact (path_sigma_prop (fun _ => ptrunc_isProp)
             (u := sh (ZmodmZ k)) (v := fst (cyc_chain_eqv k) (sh (CG k)))
             (ap (eqinv (snd gSet)) (gSet_RmSet k)^ @ eqinv_l (snd gSet) (RmSet k))^).
  Defined.

  (** Example [ex:Cm]: [BC'_m :≡ ∑_{X:FinSet_m} ‖R_m⁻¹(X)‖₀], the
      [0]-image of [R_m : S1 → FinSet_m], pointed at
      [(Fin m, |(base, refl)|₀)]; that it is a pointed connected groupoid
      pointed-equivalent to [BC_m] is stated only. *)
  Definition RmFin (k : ℕ) (z : S1) : FinSet_n (S k)
    := (RmSet k z; ptrunc_rec ptrunc_isProp (fun p : base = z => trunc (ap (Rm k) p))
                     (S1_base_paths z)).

  Definition BCm' (k : ℕ) : Type := {X : FinSet_n (S k) & strunc (fiber (RmFin k) X)}.

  Definition shCm' (k : ℕ) : BCm' k := (RmFin k base; settrunc (base; refl)).

  Definition ex_Cm_stmt : Type
    := forall k : ℕ, isConn (BCm' k) × isGrpd (BCm' k)
                     × ((BCm' k; shCm' k) ≃* BG (CG k)).

  (** The loops of a [2]-element type other than [refl] are all equal. *)
  Definition two_loops (A : Type0) (e : (Bool : Type0) = A) (q q' : A = A)
    (n : q <> refl) (n' : q' <> refl) : q = q'.
  Proof.
    destruct e.
    destruct (Bool_paths_cases q) as [eq|eq]; [destruct (n eq)|].
    destruct (Bool_paths_cases q') as [eq'|eq']; [destruct (n' eq')|].
    exact (eq @ eq'^).
  Defined.

  Definition loops_dec (A : Type0) (e : (Bool : Type0) = A) (q : A = A)
    : (q = refl) + (q <> refl).
  Proof.
    destruct e.
    destruct (Bool_paths_cases q) as [eq|eq]; [left; exact eq|].
    right. intro r. exact (refl_ne_swap (r^ @ eq)).
  Defined.

  Definition finsucc1_ne_refl : etop (finsuccEqv 1) <> refl.
  Proof.
    intro h.
    pose (h1 := ap fst ((ptoe_etop _)^ @ ap idtoeqv h)).
    pose (e := Eqv_of_Equiv (equiv_fin_finnat 2)).
    pose (x := eqinv (snd e) (fn0 1)).
    assert (E : fst (fsEqv 1) (fn0 1) = fn0 1).
    { refine (_ @ ap (fst e) (ptw h1 x) @ eqinv_r (snd e) _).
      change (fst (fsEqv 1) (fn0 1)
              = fst e (eqinv (snd e) (fst (fsEqv 1) (fst e x)))).
      refine (_ @ (eqinv_r (snd e) _)^).
      exact (ap (fst (fsEqv 1)) (eqinv_r (snd e) _)^). }
    pose (E2 := ap fst E). cbn in E2.
    exact (Spaces.Nat.Core.neq_nat_zero_succ _ E2^).
  Defined.

  Definition carrier2 (X : FinSet_n 2) : Type0 := fst (fst X).

  Definition carrier2_ap_isEquiv (X Y : FinSet_n 2)
    : isEquiv (@ap _ _ carrier2 X Y).
  Proof.
    refine (isEquiv_homotopic (fun p : X = Y => ap fst (ap fst p)) (ap carrier2) _ _).
    - intro p. exact (ap_compose fst fst p)^.
    - exact (comp_isEquiv (isInj_ap_isEquiv (fst_isInj (fun _ => ptrunc_isProp)) X Y)
               (isInj_ap_isEquiv (fst_isInj (fun X => isSet_isProp X)) _ _)).
  Defined.

  (** Every symmetry of [R_2(base)] in [FinSet_2] is [R_2] applied to
      [refl] or to [loop]. *)
  Definition RmFin1_loops (p : RmFin 1 base = RmFin 1 base)
    : {l : base = base & ap (RmFin 1) l = p}.
  Proof.
    pose (ce := carrier2_ap_isEquiv (RmFin 1 base) (RmFin 1 base)).
    assert (A2 : (Bool : Type0) = carrier2 (RmFin 1 base)) by exact Fin2_Bool_path⁻¹.
    destruct (loops_dec _ A2 (ap carrier2 p)) as [e|n].
    - refine (refl; _). apply (Eqv_inj (_; ce)).
      change (refl = ap carrier2 p). exact e^.
    - refine (loop; _). apply (Eqv_inj (_; ce)).
      change (ap carrier2 (ap (RmFin 1) loop) = ap carrier2 p).
      refine (two_loops _ A2 _ _ _ n).
      intro r. apply finsucc1_ne_refl.
      refine (_ @ r).
      refine ((S1_rec_loop _ _ _)^ @ _).
      exact (ap_compose (RmFin 1) carrier2 loop).
  Defined.

  (** Exercise [xca:CG2isSG2]. *)
  Definition xca_CG2isSG2 : isContr (strunc (fiber (RmFin 1) (RmFin 1 base))).
  Proof.
    apply isConn_strunc_isContr.
    refine (isConn_from_pt ((base; refl) : fiber (RmFin 1) (RmFin 1 base)) _).
    intros [z p]. revert z p.
    refine (S1_ind_prop _ (fun _ => Pi_isProp (fun _ => ptrunc_isProp)) _).
    intro p. apply trunc.
    destruct (RmFin1_loops p) as [l e].
    refine (pathpair l _).
    exact (trp_fiber_path _ _ _ @ trans_1p _ @ e).
  Defined.

End FirstExamples.

Section RmloopCGm.

  Context `{Univalence} (k : ℕ).

  Definition projCm' (w : BCm' k) : Type0 := fst (fst (fst w)).

  Definition trp_strunc {A : Type} (F : A -> Type) {X X' : A} (r : X = X') (w : F X)
    : trp (fun X => strunc (F X)) r (settrunc w) = settrunc (trp F r w)
    := match r with refl => refl end.

  Definition trp_fiber_target {A B : Type} (f : A -> B) {X X' : B} (r : X = X')
    (w : fiber f X) : trp (fun X => fiber f X) r w = (fst w; snd w ⋅ r⁻¹).
  Proof.
    destruct r, w as [a p].
    exact (ap (fun q => (a; q) : fiber f X) (trans_1p p)^).
  Defined.

  Definition fiber_path_inv {A B : Type} (f : A -> B) {y : B} (w w' : fiber f y)
    (e : w = w') : {l : fst w = fst w' & snd w' = ap f l ⋅ snd w}
    := match e with refl => (refl; refl) end.

  Definition ap_Rm_loopexp (n : Int)
    : ap (Rm k) (loopexp loop n) = loopexp (etop (finsuccEqv k)) n
    := ap_loopexp (Rm k) loop n @ ap (fun q => loopexp q n) (S1_rec_loop _ _ _).

  (** The symmetry of [sh_{C'_m}] given by [l : base = base]. *)
  Definition Cm'_sym (l : base = base) : shCm' k = shCm' k.
  Proof.
    refine (pathpair (ap (RmFin k) l)
              (trp_strunc (fiber (RmFin k)) _ _
               @ ap settrunc (trp_fiber_target (RmFin k) (ap (RmFin k) l)
                                ((base; refl) : fiber (RmFin k) (RmFin k base))
                              @ pathpair (y' := refl) l _))).
    exact (trp_fiber_path _ _ _ @ trans_Vp _).
  Defined.

  Definition ap_proj_Cm'_sym (l : base = base)
    : ap projCm' (Cm'_sym l) = ap (Rm k) l.
  Proof.
    unfold Cm'_sym.
    refine (ap_compose (fun w : BCm' k => fst w) (fun X : FinSet_n (S k) => fst (fst X)) _ @ _).
    refine (ap (ap (fun X : FinSet_n (S k) => fst (fst X))) (ap_fst_pathpair _ _) @ _).
    exact (ap_compose (RmFin k) (fun X : FinSet_n (S k) => fst (fst X)) l)^.
  Defined.

  (** Exercise [xca:RmloopCGm]. *)
  Definition xca_RmloopCGm (σ : projCm' (shCm' k) = projCm' (shCm' k))
    : ptrunc (fiber (fun p : shCm' k = shCm' k => ap projCm' p) σ)
      <-> ptrunc {n : Int & σ = loopexp (etop (finsuccEqv k)) n}.
  Proof.
    split.
    - refine (ptrunc_rec ptrunc_isProp _). intros [P e].
      pose (r := ap fst P).
      pose (E := (trp_strunc (fiber (RmFin k)) r ((base; refl) : fiber (RmFin k) (RmFin k base)))^
                 @ (transport_compose (fun X => strunc (fiber (RmFin k) X)) fst P _)^
                 @ apD snd P).
      pose (E2 := ap settrunc (trp_fiber_target _ r _)^ @ E).
      refine (ptrunc_rec ptrunc_isProp _ (equiv_inverse (equiv_path_Tr (n := -1) _ _) E2)).
      intro F. destruct (fiber_path_inv _ _ _ F) as [l hl]. cbn in l, hl.
      refine (trunc (toInt (fst wdg l); _)).
      refine (e @ _).
      assert (Er : r = ap (RmFin k) l).
      { exact (ap (fun q => q ⋅ r) hl @ (trans_assoc _ _ _)^
               @ ap (fun q => _ ⋅ q) (trans_pV r) @ trans_1p _). }
      refine (ap_compose (fun w : BCm' k => fst w) (fun X : FinSet_n (S k) => fst (fst X)) P @ _).
      change (ap (fun X : FinSet_n (S k) => fst (fst X)) r
              = loopexp (etop (finsuccEqv k)) (toInt (fst wdg l))).
      refine (ap _ Er @ (ap_compose (RmFin k) (fun X : FinSet_n (S k) => fst (fst X)) l)^ @ _).
      refine (ap (ap (Rm k)) (loopZ_wdg l)^ @ _).
      exact (ap_Rm_loopexp _).
    - refine (ptrunc_rec ptrunc_isProp _). intros [n e].
      refine (trunc (Cm'_sym (loopexp loop n); _)).
      exact (e @ (ap_Rm_loopexp n)^ @ (ap_proj_Cm'_sym _)^).
  Defined.

End RmloopCGm.


(** Example [ex:productofgroups]: [G × H :≡ mkgroup(BG × BH)]. *)
Definition prodG `{Funext} (G G' : Group) : Group
  := mkgroup (utype (BG G) × utype (BG G');
              ((sh G; sh G');
               (Sigma_isConn (BG_isConn G) (fun _ => BG_isConn G');
                prod_ntype 1 (BG_isGrpd G) (BG_isGrpd G')))).

Definition USym_prodG `{Funext} (G G' : Group)
  : USym (prodG G G') ≃ USym G × USym G'
  := Eqv_inv (path_prod_eqv (sh G) (sh G) (sh G') (sh G')).

(** The Klein four-group [Σ_2 × Σ_2]. *)
Definition Klein `{Univalence} : Group := prodG (SG 2) (SG 2).

(** Loops whose squares are trivial, transported along injective maps. *)
Definition sq_reflect {X Y : Type} (F : X -> Y) (j : isInj F) (x : X)
  (c : forall h : F x = F x, h ⋅ h = refl)
  : forall g : x = x, g ⋅ g = refl.
Proof.
  intro g.
  pose (e := isInj_ap_isEquiv j x x).
  refine ((eqinv_l e (g ⋅ g))^ @ ap (eqinv e) _ @ eqinv_l e refl).
  exact (ap_trans F g g @ c _).
Defined.

(** Exercise [xca:klein-not-cyclic]: [C_4 ≠ Σ_2 × Σ_2], since every
    symmetry [g] of the Klein four-group has [g g = refl] ([Klein_sq]),
    while the generator [zs] of [C_4] does not. *)
Section KleinNotCyclic.

  Context `{Univalence}.

  Definition swap_swap : swap ⋅ swap = refl.
  Proof.
    unfold swap. refine ((etop_comp swapEqv swapEqv)^ @ _ @ etop_id Bool).
    apply ap. apply path_Eqv. apply ptw_inv. intros []; exact refl.
  Defined.

  Definition Bool_loops_sq (A : Type) (e : (Bool : Type) = A)
    : forall g : A = A, g ⋅ g = refl.
  Proof.
    destruct e. intro g.
    destruct (Bool_paths_cases g) as [eg|eg]; destruct eg^.
    - exact refl.
    - exact swap_swap.
  Defined.

  Definition SG2_sq (g : USym (SG 2)) : g ⋅ g = refl.
  Proof.
    revert g.
    refine (sq_reflect fst (fst_isInj (fun _ => ptrunc_isProp)) _ _).
    refine (sq_reflect fst (fst_isInj (fun X => isSet_isProp X)) _ _).
    exact (Bool_loops_sq _ Fin2_Bool_path⁻¹).
  Defined.

  Definition Klein_sq (g : USym Klein) : g ⋅ g = refl.
  Proof.
    revert g.
    refine (sq_reflect (fst (binprod_prod _ _))
              (isEquiv_isInj (snd (binprod_prod _ _))) _ _).
    intro g.
    refine (trans_is_concat _ _ @ _).
    apply (equiv_inj (equiv_path_prod _ _)^-1); cbn.
    refine (path_prod' _ _).
    - refine (ap_pp _ g g @ _).
      exact ((trans_is_concat _ _)^ @ SG2_sq _).
    - refine (ap_pp _ g g @ _).
      exact ((trans_is_concat _ _)^ @ SG2_sq _).
  Defined.

  (** The generator of [C_4]: [(Fin 4, zs) = (Fin 4, zs)] given by [zs]. *)
  Definition CG_gen (k : ℕ) : USym (CG k).
  Proof.
    refine (path_sigma_prop (fun _ => ptrunc_isProp) _).
    exact (cyc_path (Fincyc k) (Fincyc k) (endo_path (finsuccEqv k) refl)).
  Defined.

  Definition ap_carrier_CG_gen (k : ℕ)
    : ap (fun w : component Cyc (Fincyc k) => fst (fst (fst w))) (CG_gen k)
      = etop (finsuccEqv k).
  Proof.
    unfold CG_gen, path_sigma_prop.
    refine (ap_compose (fun w : component Cyc (Fincyc k) => fst w)
              (fun c : Cyc => fst (fst c)) _ @ _).
    refine (ap (ap (fun c : Cyc => fst (fst c))) (ap_fst_pathpair _ _) @ _).
    refine (ap_carrier_cyc_path _ _ _ @ _).
    exact (ap_fst_endo_path _ _).
  Defined.

  (** [zs² ≠ id] on [Fin 4]. *)
  Definition finsucc_sq_ne
    : fst (finsuccEqv 3) ∘ fst (finsuccEqv 3) <> id (Fin 4).
  Proof.
    intro h.
    pose (e := Eqv_of_Equiv (equiv_fin_finnat 4)).
    pose (x := eqinv (snd e) (fn0 3)).
    assert (E : fst (fsEqv 3) (fst (fsEqv 3) (fn0 3)) = fn0 3).
    { refine (_ @ ap (fst e) (ptw h x) @ eqinv_r (snd e) _).
      change (fst (fsEqv 3) (fst (fsEqv 3) (fn0 3))
              = fst e (eqinv (snd e) (fst (fsEqv 3) (fst e (eqinv (snd e)
                  (fst (fsEqv 3) (fst e x))))))).
      refine (_ @ (eqinv_r (snd e) _)^).
      refine (ap (fst (fsEqv 3)) _).
      refine (_ @ (eqinv_r (snd e) _)^).
      exact (ap (fst (fsEqv 3)) (eqinv_r (snd e) _)^). }
    pose (E2 := ap fst E). cbn in E2.
    exact (Spaces.Nat.Core.neq_nat_zero_succ _ E2^).
  Defined.

  Definition CG_gen_sq_ne : CG_gen 3 ⋅ CG_gen 3 <> refl.
  Proof.
    intro h. apply finsucc_sq_ne.
    pose (h2 := (ap_trans _ (CG_gen 3) (CG_gen 3))^
                @ ap (ap (fun w : component Cyc (Fincyc 3) => fst (fst (fst w)))) h).
    rewrite ap_carrier_CG_gen in h2.
    pose (h3 := (etop_comp (finsuccEqv 3) (finsuccEqv 3) @ h2 @ (etop_id _)^)).
    exact (ap fst ((ptoe_etop _)^ @ ap idtoeqv (h3) @ ptoe_etop _)).
  Defined.

  (** Exercise [xca:klein-not-cyclic]. *)
  Definition xca_klein_not_cyclic : CG 3 <> Klein.
  Proof.
    intro p. apply CG_gen_sq_ne.
    exact (trp (fun G => forall g : USym G, g ⋅ g = refl) p⁻¹ Klein_sq _).
  Defined.

End KleinNotCyclic.


(** Example [ex:bigproductofgroups] and exercise [xca:bigproductfunext](1)
    ([it:bigproductfunext-i]):
    a finite product of connected groupoids is connected (by the
    library's finite choice), so we have the product of a finite family
    of groups, and [ptw] identifies its symmetries. *)
Section BigProduct.

  Context `{Univalence} {S : Type} (hS : isFinSet S) (G : S -> Group).

  Definition PiG_pt : forall s, utype (BG (G s)) := fun s => sh (G s).

  Definition PiG_isConn : isConn (forall s, utype (BG (G s))).
  Proof.
    refine (isConn_from_pt PiG_pt _). intro f.
    pose (FS := isFinSet_Finite hS).
    refine (ptrunc_rec ptrunc_isProp (fun h => trunc (ptw_inv h)) _).
    exact (@finite_choice S FS (fun s => sh (G s) = f s) (fun _ => tt)
             (fun s => snd (BG_isConn (G s)) (sh (G s)) (f s))).
  Defined.

  Definition PiG : Group
    := mkgroup ((forall s, utype (BG (G s)));
                (PiG_pt; (PiG_isConn; Pi_ntype 1 (fun s => BG_isGrpd (G s))))).

  Definition USym_PiG : USym PiG ≃ (forall s, USym (G s))
    := Eqv_of_Equiv (equiv_apD10 _ PiG_pt PiG_pt).

End BigProduct.

(** Exercise [xca:bigproductfunext](2): for [S = 𝟚] the product is the
    binary product. *)
Definition Bool_isFinSet `{Univalence} : isFinSet Bool := trunc (2%nat; etop (Eqv_inv Fin2_Bool)).

Definition xca_bigproductfunext_2 `{Univalence} (G : Bool -> Group)
  : PiG Bool_isFinSet G = prodG (G yes) (G no).
Proof.
  apply path_Group.
  refine (((fun f : forall b, utype (BG (G b)) =>
             ((f yes; f no) : utype (BG (G yes)) × utype (BG (G no)))); refl); _).
  refine (iso_to_isEquiv _ (fun (w : utype (BG (G yes)) × utype (BG (G no))) (b : Bool) => if b as b return utype (BG (G b)) then fst w else snd w) _ _).
  - intro f. apply ptw_inv. intros []; exact refl.
  - intros [x y]. exact refl.
Defined.

(** Definition [def:abgp]: abelian groups. *)
Definition isAb (G : Group) : Type := forall g h : USym G, g ⋅ h = h ⋅ g.

Definition isAb_isProp `{Funext} (G : Group) : isProp (isAb G)
  := Pi_isProp (fun g => Pi_isProp (fun h => USym_isSet G _ _)).

Definition AbGroup : Type := {G : Group & isAb G}.

(** Commutation of loops reflects along maps that are injective (in the
    book's sense: with propositional fibers). *)
Definition comm_reflect {X Y : Type} (F : X -> Y) (j : isInj F) (x : X)
  (c : forall g h : F x = F x, g ⋅ h = h ⋅ g)
  : forall g h : x = x, g ⋅ h = h ⋅ g.
Proof.
  intros g h.
  pose (e := isInj_ap_isEquiv j x x).
  refine ((eqinv_l e (g ⋅ h))^ @ ap (eqinv e) _ @ eqinv_l e (h ⋅ g)).
  exact (ap_trans F h g @ c _ _ @ (ap_trans F g h)^).
Defined.

Section AbelianExamples.

  Context `{Univalence}.

  (** [ℤ] is abelian. *)
  Definition loopexp_comm {X : Type} {x : X} (p : x = x) (m n : Int)
    : loopexp p m ⋅ loopexp p n = loopexp p n ⋅ loopexp p m.
  Proof.
    refine (trans_is_concat _ _ @ _ @ (trans_is_concat _ _)^).
    exact ((loopexp_add p n m)^ @ ap (loopexp p) (int_add_comm n m) @ loopexp_add p m n).
  Defined.

  Definition ZZ_isAb : isAb ZZ.
  Proof.
    intros g h.
    rewrite <- (loopZ_wdg g), <- (loopZ_wdg h).
    apply loopexp_comm.
  Defined.

  (** Exercise [exer:first examples]: [Σ_2] is abelian. *)
  Definition Bool_loops_comm (A : Type) (e : (Bool : Type) = A)
    : forall g h : A = A, g ⋅ h = h ⋅ g.
  Proof.
    destruct e. intros g h.
    destruct (Bool_paths_cases g) as [eg|eg]; destruct (Bool_paths_cases h) as [eh|eh];
      destruct eg^, eh^; try exact refl.
    - exact (trans_1p _)^.
    - exact (trans_1p _).
  Defined.

  Definition SG2_isAb : isAb (SG 2).
  Proof.
    refine (comm_reflect fst (fst_isInj (fun _ => ptrunc_isProp)) _ _).
    refine (comm_reflect fst (fst_isInj (fun X => isSet_isProp X)) _ _).
    exact (Bool_loops_comm _ Fin2_Bool_path⁻¹).
  Defined.

  (** Exercise [exer:first examples]: products of abelian groups are
      abelian. *)
  Definition prodG_isAb (G G' : Group) (a : isAb G) (a' : isAb G')
    : isAb (prodG G G').
  Proof.
    refine (comm_reflect (fst (binprod_prod _ _))
              (isEquiv_isInj (snd (binprod_prod _ _))) _ _).
    intros g h.
    refine (trans_is_concat _ _ @ _ @ (trans_is_concat _ _)^).
    apply (equiv_inj (equiv_path_prod _ _)^-1); cbn.
    refine (path_prod' _ _).
    - refine (ap_pp _ h g @ _ @ (ap_pp _ g h)^).
      exact ((trans_is_concat _ _)^ @ a _ _ @ trans_is_concat _ _).
    - refine (ap_pp _ h g @ _ @ (ap_pp _ g h)^).
      exact ((trans_is_concat _ _)^ @ a' _ _ @ trans_is_concat _ _).
  Defined.

End AbelianExamples.

(** Commutation transported forward along maps with [ap] an equivalence. *)
Definition comm_forward {X Y : Type} (F : X -> Y) (j : isInj F) (x : X)
  (c : forall g h : x = x, g ⋅ h = h ⋅ g)
  : forall g h : F x = F x, g ⋅ h = h ⋅ g.
Proof.
  intros g h.
  pose (e := isInj_ap_isEquiv j x x).
  refine (ap011 (fun u v => u ⋅ v) (eqinv_r e g)^ (eqinv_r e h)^ @ _).
  refine ((ap_trans F _ _)^ @ ap (ap F) (c _ _) @ ap_trans F _ _ @ _).
  exact (ap011 (fun u v => u ⋅ v) (eqinv_r e h) (eqinv_r e g)).
Defined.

(** Exercise [exer:first examples]: [Σ_3] is not abelian; two
    transpositions of [Fin 3] do not commute. *)
Section SG3NotAb.

  Context `{Univalence}.

  Definition f3a (x : Fin 3) : Fin 3
    := match x with
       | inl (inl (inl e)) => match e with end
       | inl (inl (inr _)) => inl (inr tt)
       | inl (inr _) => inl (inl (inr tt))
       | inr _ => inr tt
       end.

  Definition f3b (x : Fin 3) : Fin 3
    := match x with
       | inl (inl (inl e)) => match e with end
       | inl (inl (inr _)) => inl (inl (inr tt))
       | inl (inr _) => inr tt
       | inr _ => inl (inr tt)
       end.

  Definition f3a_inv (x : Fin 3) : f3a (f3a x) = x.
  Proof. destruct x as [[[[]|[]]|[]]|[]]; exact refl. Defined.

  Definition f3b_inv (x : Fin 3) : f3b (f3b x) = x.
  Proof. destruct x as [[[[]|[]]|[]]|[]]; exact refl. Defined.

  Definition f3aEqv : Fin 3 ≃ Fin 3 := mkEqv f3a f3a f3a_inv f3a_inv.
  Definition f3bEqv : Fin 3 ≃ Fin 3 := mkEqv f3b f3b f3b_inv f3b_inv.

  Definition SG3_not_isAb : ¬ isAb (SG 3).
  Proof.
    intro c.
    pose (c1 := comm_forward fst (fst_isInj (fun _ => ptrunc_isProp)) _ c).
    pose (c2 := comm_forward fst (fst_isInj (fun X => isSet_isProp X)) _ c1).
    pose (h := c2 (etop f3aEqv) (etop f3bEqv)).
    pose (h2 := etop_comp f3bEqv f3aEqv @ h @ (etop_comp f3aEqv f3bEqv)^).
    pose (h3 := ap fst ((ptoe_etop _)^ @ ap idtoeqv h2 @ ptoe_etop _)).
    pose (h4 := ap10 h3 (inl (inl (inr tt)))). cbn in h4.
    exact (inl_ne_inr _ _ h4).
  Defined.

End SG3NotAb.


(** Remark [rem:whatAREabeliangroups]: the classifying types of abelian
    groups are identity types of [2]-types; see Chapter [abelian.tex]
    (informal here). *)

(** Exercise: [mkgroup(A,a)] and [mkgroup(A,b)] are merely identical. *)
Definition mkgroup_merely_eq {A : Type} (a : A) (cA : isConn A) (gA : isGrpd A) (b : A)
  : ptrunc (mkgroup (A; (a; (cA; gA))) = mkgroup (A; (b; (cA; gA)))).
Proof.
  refine (ptrunc_rec ptrunc_isProp _ (snd cA a b)). intro p.
  destruct p. exact (trunc refl).
Defined.
