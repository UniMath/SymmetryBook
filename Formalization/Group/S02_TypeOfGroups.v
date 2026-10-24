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
    - Exercise [xca:group-example-details], all but the last part:
      [AutProp_trivial], [AutG_set_trivial], [contr_group_trivial],
      [SG0_trivial], [SG1_trivial], [SG_False_trivial], and
      [AutFinSet_SG], from the general [AutG_subtype] (components of a
      subtype are components of the ambient type).
    - Definition [def:abgp]: [isAb], a proposition, and [AbGroup];
      [ZZ_isAb]; exercise [exer:first examples]: [SG2_isAb] and
      [prodG_isAb].  Commutation is reflected along injective maps
      ([comm_reflect]).
    - The exercise that [mkgroup(A,a)] and [mkgroup(A,b)] are merely
      identical ([mkgroup_merely_eq]).

    Left out (statements only, no proofs yet; time limit per result)
    - [xca:groups] ([xca_groups_stmt]), the identification
      [Aut_Set(ℕ) = Aut_Set(ℤ)] ([SG_N_Z_stmt]), example [ex:Cm]
      ([ex_Cm_stmt], with [RmFin], [BCm'], [shCm']) with [xca:CG2isSG2]
      and [xca:RmloopCGm] ([xca_CG2isSG2_stmt], [xca_RmloopCGm_stmt]),
      [xca:klein-not-cyclic] ([xca_klein_not_cyclic_stmt]), that [Σ_3] is
      not abelian ([SG3_not_isAb_stmt]), [xca:bigproductfunext](2)
      ([xca_bigproductfunext_2_stmt]), and the chain of identifications
      in [ex:cyclicgroups], end to end ([ex_cyclicgroups_chain_stmt]).
    - [xca:typegroupisgroupoid] is postponed to Section 4.4
      ([Group_isGrpd]), where it follows from [lem:hom-is-set].
    - Size issues: [Aut_Group(G)] is a group in a larger universe than
      [G] ([AutGrp], Section 9.7).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Spaces.Circle Spaces.Finite.Fin Spaces.Finite.Finite Spaces.Int Projective.
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

  (** Left-out results of this part (statements only). *)

  (** Exercise [xca:groups]: two different identifications
      [ℤ = Aut_Cyc(ℤ, zs)].
    (Placed after [ex:cyclicgroups], since it uses [Cyc_isGrpd].) *)
  Definition xca_groups_stmt : Type
    := {p : ZZ = AutG Cyc_isGrpd Zcyc & {q : ZZ = AutG Cyc_isGrpd Zcyc & p ≠ q}}.

  (** The identification [Aut_Set(ℕ) = Aut_Set(ℤ)]. *)
  Definition SG_N_Z_stmt : Type := SG_S (ℕ; ℕ_isSet) = SG_S (ℤ; ℤ_isSet).

  (** The chain of identifications in example [ex:cyclicgroups], end to
      end: [C_m = Aut_{S1 → Set}(R_m)]. *)
  Definition ex_cyclicgroups_chain_stmt : Type := forall k : ℕ, CG k = ZmodmZ k.

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

  (** Exercise [xca:CG2isSG2]. *)
  Definition xca_CG2isSG2_stmt : Type := isContr (strunc (fiber (RmFin 1) (RmFin 1 base))).

  (** Exercise [xca:RmloopCGm]: the symmetries of [sh_{C'_m}] give
      exactly the permutations of [Fin m] generated by [R_m(loop)]. *)
  Definition xca_RmloopCGm_stmt : Type
    := forall (k : ℕ) (σ : fst (fst (fst (shCm' k))) = fst (fst (fst (shCm' k)))),
         ptrunc (fiber (fun p : shCm' k = shCm' k => ap (fun w : BCm' k => fst (fst (fst w))) p) σ)
         <-> ptrunc {n : Int & σ = loopexp (etop (finsuccEqv k)) n}.

End FirstExamples.

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

(** Exercise [xca:klein-not-cyclic] (statement only). *)
Definition xca_klein_not_cyclic_stmt `{Univalence} : Type := CG 3 ≠ Klein.

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

(** Exercise [xca:bigproductfunext](2) (statement only): for [S = 𝟚]
    the product is the binary product. *)
Definition Bool_isFinSet `{Univalence} : isFinSet Bool := trunc (2%nat; etop (Eqv_inv Fin2_Bool)).

Definition xca_bigproductfunext_2_stmt `{Univalence} : Type
  := forall G : Bool -> Group, PiG Bool_isFinSet G = prodG (G yes) (G no).

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

(** [Σ_3] is not abelian (statement only). *)
Definition SG3_not_isAb_stmt `{Univalence} : Type := ¬ isAb (SG 3).

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
