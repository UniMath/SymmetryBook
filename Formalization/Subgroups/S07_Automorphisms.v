(** * Section 9.7 Automorphisms of groups

    Part of Chapter 9 ([subgroups.tex]); see [Subgroups.v] for an
    overview of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - [Aut(G)] ([AutGrp]): [Group] is universe polymorphic, so
      [Aut_Group(G)] is a group (in a larger universe than [G]); its
      classifying type is [BAutG] of Section 4.4 by definition.  By
      replacement it has a copy in the universe of [G] ([AutGrp_small],
      [AutGrp_small_pEqv]).
    - [inn : Hom(G, Aut(G))] ([mkhom (Binn G)], pointed by [(inc_out G)⁻¹]);
      [out(G)] ([outG], the cokernel of [inn]); [Inn(G)] ([InnG], the
      image of [inn]); [Out(G)] ([OutG]).
    - The remark on [USym inn] ([USym_inn], via [USymf_path_Group_Iso]
      and [trp_Binn_loop] of Section 7.3), with [h ↦ g h g⁻¹].  NOTE for
      the book text: the remark says [h ↦ g⁻¹ h g]; see [USym_inn_stmt].
    - Lemma [lemma:coker-out-action] ([coker_out_action]): the fibers of
      [Binn] by the book's chain of equivalences ([fiber_Binn_eqv]), and
      the set truncation of an equivalence ([strunc_eqv], now in Section 9.3).
    - The kernel of [inn] is [Aut_{BG_÷ = BG_÷}(refl)] ([ker_inn_center],
      via [fiber_Binn_eqv], which sends [shKer] to [refl]); this is the
      center of [sec:abelian-groups] (Chapter 12, not formalized yet).
    - That [Inn(G)] is normal ([Inn_normal], after the section): the
      family [y ↦ (z ↦ ‖BG(z)_÷ = BG(y)_÷‖₀)] pointed at [|refl|]
      ([XU], [NInn]) is transitive, since every [e : BK_÷ = BK_÷] merely
      comes from an identification [K = K] ([KL_group]); at the shape it
      is [out(G)] pointed at [|shKer|] ([coker_out_action],
      [fiber_Binn_shKer]).

    - Exercise [xca:AutC3] of Section 5.2 ([xca_AutC3], stated in
      [Actions/S02_GSets.v]), at the end of this file.

    Left out (statements only)
    - Construction [cons:simpler-version-Out]
      ([cons_simpler_version_Out_stmt], as an isomorphism, with
      [Trunc1U_isGrpd]).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Types.Sum Truncations.Core Spaces.Finite.Fin.
From SymmetryBook Require Export Subgroups.S06_IntersectNormal.

Local Open Scope uf_scope.

(** ** 9.7 Automorphisms of groups *)

(** [USymf] of the isomorphism given by an identification of groups is
    transport. *)
Definition USymf_path_Group_Iso `{Univalence} {G K : Group} (P : G = K) (h : USym G)
  : USymf (fst (fst (path_Group_Iso_eqv G K) P)) h = trp USym P h.
Proof. destruct P. destruct G as [X]. exact (trans_1p _ @ ap_idmap h). Defined.

(** [strunc_eqv]: the set truncation of an equivalence, Section 9.3. *)

(** The fibers of [Binn]: [Binn⁻¹(G') ≃ (BG'_÷ = BG_÷)], as in the proof
    of lemma [lemma:coker-out-action]. *)
Definition fiber_Binn_eqv `{Univalence} (G : Group) (G' : component Group G)
  : fiber (fst (Binn G)) G' ≃ (utype (BG (fst G')) = utype (BG G)).
Proof.
  destruct G as [X], G' as [[Z] r].
  refine (Eqv_comp (tot (fun y (p : ((inc Z; r) : component Group (inc X)) = fst (Binn (inc X)) y)
                           => ap fst p);
                    tot_isEquiv _ (fun y => snd (subtype_paths_eqv (fun _ => ptrunc_isProp) _ _))) _).
  refine (Eqv_comp (tot (fun y => fst (path_inc_eqv Z (fst X; (y; snd (snd X)))));
                    tot_isEquiv _ (fun y => snd (path_inc_eqv Z (fst X; (y; snd (snd X)))))) _).
  refine (Eqv_comp (tot (fun y => fst (UUscone_paths_eqv Z (fst X; (y; snd (snd X)))));
                    tot_isEquiv _ (fun y => snd (UUscone_paths_eqv Z (fst X; (y; snd (snd X)))))) _).
  refine (Eqv_comp (tot (fun y => fst (Eqv_inv (path_sigma_eqv (Y := idmap)
                                                  (x := fst Z) (x' := fst X)
                                                  (y := fst (snd Z)) (y' := y))));
                    tot_isEquiv _ (fun y => snd (Eqv_inv path_sigma_eqv))) _).
  refine (Eqv_comp (sigma_comm _ _ _) _).
  exact (sigma_contr_fibers (fun q => singleton_contr (trp idmap q (fst (snd Z))))).
Defined.

Definition USym_inn_gen `{Univalence} (G : Group) (g h : USym G)
  : USymf (fst (fst (path_Group_Iso_eqv G G) (ap fst (loops_fun (Binn G) g)))) h = (g ⋅ h) ⋅ g⁻¹.
Proof.
  revert g h. destruct G as [X]. intros g h.
  refine (USymf_path_Group_Iso _ h @ _).
  refine ((ptw (trp_ap USym fst (loops_fun (Binn (inc X)) g)) h)^ @ _).
  exact (trp_Binn_loop X g h).
Defined.

Section Automorphisms.

  Context `{ua : Univalence} (G : Group).

  (** [Aut(G) :≡ Aut_Group(G)]; its classifying type is [BAutG G] of
      Section 4.4 by definition.  [Group] is universe polymorphic, so
      [Aut(G)] is a group (in a larger universe than [G]). *)
  Definition AutGrp : Group := AutG Group_isGrpd G.

  Definition BAutGrp_is_BAutG : BG AutGrp = BAutG G := refl.

  (** By replacement [Aut(G)] has a copy in the universe of [G]: the type
      of groups is locally small (identifications are isomorphisms,
      [path_Group_Iso_eqv]), so the component [BAut(G)] is essentially
      small ([AutG_small]). *)
  Definition Group_locSmall : locSmall Group := fun H K => (Iso H K; path_Group_Iso_eqv H K).

  Definition AutGrp_small (rep : Replacement) : Group
    := AutG_small rep Group_isGrpd Group_locSmall G.

  Definition AutGrp_small_pEqv (rep : Replacement) : BG AutGrp ≃* BG (AutGrp_small rep)
    := AutG_small_pEqv rep Group_isGrpd Group_locSmall G.

  (** The homomorphism [inn : G → Aut(G)] with [Binn(y) :≡ mkgroup(BG_÷, y)]
      ([Binn], [def:inner-autos], Section 4.4; pointed by [(inc_out G)⁻¹]
      instead of [refl_G], since [Copy] has no definitional eta). *)
  Definition inn : Hom G AutGrp := @mkhom G AutGrp (Binn G).

  (** The remark on [USym inn]: [USym inn(g)] is the inner automorphism
      [h ↦ g h g⁻¹], up to the identification [path_Group_Iso_eqv] of
      Section 4.4.  NOTE for the book text: the remark says
      [h ↦ g⁻¹ h g], with [B(USym inn(g))] the identity pointed by [g];
      by example [exa:conj-concrete] (and [abstr(Binn)(g) = conj^g] in
      example [ex:conjhom]) it is pointed by [g⁻¹], giving
      [h ↦ g h g⁻¹] ([abstr_Binn] in Section 7.3 agrees). *)
  Definition USym_inn_stmt : Type
    := forall g h : USym G,
         USymf (fst (fst (path_Group_Iso_eqv G G) (ap fst (USymf inn g)))) h = (g ⋅ h) ⋅ g⁻¹.

  Definition USym_inn : USym_inn_stmt
    := fun g h => USym_inn_gen G g h.

  (** The kernel of [inn] is [Aut_{BG_÷ = BG_÷}(refl)], the center [Z(G)]
      of [sec:abelian-groups] (Chapter 12, not formalized yet); proved
      after the section ([ker_inn_center]). *)
  Definition ker_inn_center_stmt : Type
    := forall gp : isGrpd (utype (BG G) = utype (BG G)), Iso (Ker inn) (AutG gp refl).

  (** The definition of [out(G)]: the cokernel of [inn], an [Aut(G)]-set. *)
  Definition outG : GSet AutGrp := coker inn.

  (** Lemma [lemma:coker-out-action]: [out(G)(G') = ‖BG'_÷ = BG_÷‖₀]. *)
  Definition coker_out_action_stmt : Type
    := forall G' : utype (BG AutGrp),
         el outG G' ≃ strunc (utype (BG (fst G')) = utype (BG G)).

  Definition coker_out_action : coker_out_action_stmt
    := fun G' => strunc_eqv (fiber_Binn_eqv G G').

  (** The definition of [Inn(G) :≡ Im(inn)]. *)
  Definition InnG : Group := Img inn.

  (** The lemma that [Inn(G)] is normal in [Aut(G)] (statement; proved
      after the section, [Inn_normal]). *)
  Definition Inn_normal_stmt : Type
    := {N : Nor AutGrp & inor AutGrp N = imsub inn}.

  (** The definition of [Out(G) :≡ Aut_{Aut(G)-Set}(out(G))]. *)
  Definition OutG : Group := AutG GSet_isGrpd outG.

  (** Construction [cons:simpler-version-Out] (statement only):
      [Aut_{‖U‖₁}(|BG_÷|₁) = Out(G)], stated as an isomorphism since the
      two groups live in different universes. *)
  Definition Trunc1U_isGrpd : isGrpd (Trunc 1 Type) := IsTrunc_ntype 1 _.

  Definition cons_simpler_version_Out_stmt : Type
    := Iso (AutG Trunc1U_isGrpd (tr (utype (BG G)))) OutG.

End Automorphisms.

(** The kernel of [inn] is [Aut_{BG_÷ = BG_÷}(refl)]: by [fiber_Binn_eqv]
    the fiber of [Binn] over [sh_{Aut(G)}] is [BG_÷ = BG_÷], with [shKer]
    sent to [refl]. *)
Definition ap_fst_pair_refl {A : Type} {P : A -> Type} (x : A) (s s' : P x) (e : s = s')
  : ap fst (match e in (_ = b) return ((x; s) = (x; b) :> {a : A & P a}) with refl => refl end) = refl.
Proof. destruct e. exact refl. Defined.

Definition fiber_Binn_shKer `{ua : Univalence} (X : UUscone)
  : fst (fiber_Binn_eqv (inc X) (sh (AutGrp (inc X)))) (shKer (inn (inc X))) = refl.
Proof.
  cbn.
  refine (ap (fun r : inc X = inc X =>
                fst (pathsplit (ap fst (ap (fun X0 : UUscone => ((fst X0; fst (snd X0)); snd (snd X0)))
                                         (ap out r)))))
            (ap_fst_pair_refl (inc X) _ _ _) @ _).
  exact refl.
Defined.

Definition ker_inn_center `{ua : Univalence} (G : Group) : ker_inn_center_stmt G.
Proof.
  destruct G as [X]. intro gp.
  pose (e := comp_eqv (fiber_Binn_eqv (inc X) (sh (AutGrp (inc X)))) (fiber_Binn_shKer X)).
  refine (fst (path_Group_Iso_eqv _ _)
            (@path_Group _ (Ker (inn (inc X))) (AutG gp refl) ((fst e; _); snd e))).
  apply (path_sigma_prop (fun _ => ptrunc_isProp)). exact (fiber_Binn_shKer X)^.
Defined.

(** [Inn(G)] is normal in [Aut(G)]: the family [y ↦ ‖BG(y)_÷ = BG(z)_÷‖₀]
    of [Aut(G)]-sets, pointed at [|refl|] ([XU], [NInn]), is transitive
    since every identification [e : BK_÷ = BK_÷] of a group [K] merely
    comes from an identification [K = K] ([KL_group]: move the base point
    along a path [e(sh_K) = sh_K]); at [sh_{Aut(G)}] it is [out(G)]
    ([coker_out_action]) pointed at [|shKer|] ([fiber_Binn_shKer]). *)
Definition UUscone_loop `{Funext} {A A' : Type} (e : A = A') (a : A) (a' : A')
  (q : trp idmap e a = a') (h : isConn A × isGrpd A) (h' : isConn A' × isGrpd A')
  : ((A; (a; h)) : UUscone) = (A'; (a'; h')).
Proof.
  destruct e. destruct q.
  exact (ap (fun h0 => (A; (a; h0)) : UUscone) (isConnGrpd_isProp (A; a) h h')).
Defined.

Definition ap_fst_UUscone_loop `{Funext} {A A' : Type} (e : A = A') (a : A) (a' : A')
  (q : trp idmap e a = a') (h : isConn A × isGrpd A) (h' : isConn A' × isGrpd A')
  : ap (fun X : UUscone => fst X) (UUscone_loop e a a' q h h') = e.
Proof.
  destruct e. destruct q.
  change (ap (fun X : UUscone => fst X)
            (ap (fun h0 => (A; (a; h0)) : UUscone) (isConnGrpd_isProp (A; a) h h')) = refl).
  exact ((ap_compose (fun h0 => (A; (a; h0)) : UUscone) (fun X : UUscone => fst X)
            (isConnGrpd_isProp (A; a) h h'))^
         @ ap_const (isConnGrpd_isProp (A; a) h h') A).
Defined.

Definition KL_group `{Funext} (K : Group) (e : utype (BG K) = utype (BG K))
  : ptrunc {P : K = K & ap (fun K0 : Group => utype (BG K0)) P = e}.
Proof.
  destruct K as [[A [a h]]]. cbn in e.
  refine (ptrunc_rec ptrunc_isProp _ (snd (fst h) (trp idmap e a) a)). intro q.
  apply trunc. exists (ap inc (UUscone_loop e a a q h h)).
  exact ((ap_compose inc (fun K0 : Group => utype (BG K0)) _)^ @ ap_fst_UUscone_loop e a a q h h).
Defined.

Section InnNormal.

  Context `{ua : Univalence} (G : Group).

  Local Notation UA z := (utype (BG (fst z))).

  Definition KL_comp (y : utype (BG (AutGrp G))) (e : UA y = UA y)
    : ptrunc {g : y = y & ap (fun z : utype (BG (AutGrp G)) => UA z) g = e}.
  Proof.
    refine (ptrunc_rec ptrunc_isProp _ (KL_group (fst y) e)). intros [P hP].
    apply trunc. exists (path_sigma_prop (fun _ => ptrunc_isProp) (u := y) (v := y) P).
    refine (ap_compose fst (fun K0 : Group => utype (BG K0)) _ @ _).
    exact (ap (ap (fun K0 : Group => utype (BG K0))) (ap_fst_path_sigma_prop _ P) @ hP).
  Defined.

  Definition XU (y : utype (BG (AutGrp G))) : GSet (AutGrp G)
    := fun z => (strunc (UA z = UA y); strunc_isSet).

  Definition act_XU (y : utype (BG (AutGrp G))) {z z' : utype (BG (AutGrp G))} (g : z = z')
    (e : UA z = UA y)
    : act (XU y) g (settrunc e)
      = settrunc ((ap (fun w : utype (BG (AutGrp G)) => UA w) g)^ @ e).
  Proof. destruct g. exact (ap settrunc (concat_1p e)^). Defined.

  Definition XU_trans (y : utype (BG (AutGrp G))) : istrans (G := regroup (AutGrp G) y) (XU y).
  Proof.
    apply trunc. exists (settrunc refl : el (XU y) y).
    refine (strunc_ind_prop _ (fun _ => ptrunc_isProp) _). intro e.
    refine (ptrunc_rec ptrunc_isProp _ (KL_comp y e)). intros [g hg].
    apply trunc. exists g. refine (_ @ (act_XU y g e)^).
    exact (ap settrunc ((concat_Vp e)^ @ ap (fun r => r^ @ e) hg^)).
  Defined.

  Definition NInn : Nor (AutGrp G) := fun y => (XU y; (settrunc refl; XU_trans y)).

End InnNormal.

Definition Inn_normal `{ua : Univalence} (G : Group) : Inn_normal_stmt G.
Proof.
  destruct G as [X]. exists (NInn (inc X)). unfold inor.
  pose (ce := coker_out_action (inc X) (sh (AutGrp (inc X)))).
  refine (SubGrp_path (path_GSet (X := XU (inc X) (sh (AutGrp (inc X)))) (Y := outG (inc X))
                         (fun z => Eqv_inv (coker_out_action (inc X) z))) _).
  refine (trp_path_GSet _ (sh _) _ @ _).
  exact ((ap (eqinv (snd ce)) (ap settrunc (fiber_Binn_shKer X)))^
         @ eqinv_l (snd ce) (settrunc (shKer (inn (inc X))))
         : _ = settrunc (shKer (inn (inc X)))).
Defined.

(** ** Exercise [xca:AutC3] (Section 5.2)

    Placed here since the second part uses that homomorphisms are
    determined by their action on symmetries ([USymf_cancel], Section
    9.2).  First part: [Ψ : (X, f) ↦ (X, f_0)] is a pointed equivalence
    from the component of [(𝟙 ⨿ 𝟚, f)] to [BC_3] ([ac_part1]), with
    inverse [(X, t) ↦ (X, (t, t²))].  Second part: the loops of
    [BS2onC3(𝟚)] are [refl], [g] and [g g], with [g] given by [f_0]
    ([acloop_cases]), so identifications [S2onC3(𝟚) = S2onC3(𝟚)] are
    determined by what they do with [g] ([acKpath_eq]); transport along
    the swap of [𝟚] sends [g] to [g g] ([acLg_sw]).  Hence [ap] of the map
    [BΣ_2 → BAut(C_3)] at [𝟚] is a bijection, and the map is an
    equivalence by [conn_isEquiv_iff_point]. *)
Section AutC3.

  Context `{Univalence}.

  Local Notation S0 := (sh (SG 2)).
  Local Notation C3s := (True ⨿ Fin 2).
  Local Notation BE := (component (EndoFam (Fin 2)) (C3pt (sh (SG 2)))).

  Definition ac_f : C3s -> C3s := f3 S0 fin2_0.
  Definition ac_g : C3s -> C3s := f3 S0 fin2_1.

  (** The explicit 3-cycle [0 ↦ s ↦ s' ↦ 0] on [𝟙 ⨿ 𝟚]. *)
  Definition c3rot (x : C3s) : C3s
    := match x with inl _ => inr fin2_0 | inr (inl _) => inr fin2_1 | inr (inr _) => inl triv end.

  Definition other_0 : other (BSG2_FinSet S0) fin2_0 = fin2_1
    := (other_unique (BSG2_FinSet S0) (fun e => f2_ne e^))^.

  Definition other_1 : other (BSG2_FinSet S0) fin2_1 = fin2_0
    := (other_unique (BSG2_FinSet S0) f2_ne)^.

  Definition ac_f_eq (x : C3s) : ac_f x = c3rot x.
  Proof.
    destruct x as [[]|[[[]|[]]|[]]].
    - exact refl.
    - exact (ap inr other_0).
    - exact refl.
  Defined.

  Definition ac_g_eq (x : C3s) : ac_g x = c3rot (c3rot x).
  Proof.
    destruct x as [[]|[[[]|[]]|[]]].
    - exact refl.
    - exact refl.
    - exact (ap inr other_1).
  Defined.

  Definition cyc3_3 (x : C3s) : c3rot (c3rot (c3rot x)) = x.
  Proof. destruct x as [[]|[[[]|[]]|[]]]; exact refl. Defined.

  Definition ac_gf (x : C3s) : ac_g (ac_f x) = x
    := ac_g_eq _ @ ap (fun y => c3rot (c3rot y)) (ac_f_eq x) @ cyc3_3 x.

  Definition ac_fg (x : C3s) : ac_f (ac_g x) = x
    := ac_f_eq _ @ ap c3rot (ac_g_eq x) @ cyc3_3 x.

  Definition ac_fEqv : C3s ≃ C3s := mkEqv ac_f ac_g ac_gf ac_fg.

  Definition cyc3_conn (x x' : C3s) : {k : ℕ & iter c3rot k x = x'}.
  Proof.
    destruct x as [[]|[[[]|[]]|[]]], x' as [[]|[[[]|[]]|[]]];
      first [ exact (0%nat; refl) | exact (1%nat; refl) | exact (2%nat; refl) ].
  Defined.

  Definition ac_f_isCycle : isCycle ac_fEqv
    := (trunc (inl triv); fun x x' =>
          trunc (iplus (fst (cyc3_conn x x'));
                 (iter_ext _ _ ac_f_eq _ x @ snd (cyc3_conn x x'))^)).

  (** [Ψ : BS2onC3(𝟚) → BC_3, (X, f) ↦ (X, f_0)], with inverse
      [(X, t) ↦ (X, (t, t²))]. *)
  Definition acQ (v : EndoFam (Fin 2)) : Type
    := {tE : isEquiv (snd v fin2_0) & isCycle ((snd v fin2_0; tE) : fst (fst v) ≃ fst (fst v))}.

  Definition acQ_isProp (v : EndoFam (Fin 2)) : isProp (acQ v)
    := Sigma_isProp (isEquiv_isProp _)
         (fun tE => prod_isProp ptrunc_isProp
                      (Pi_isProp (fun _ => Pi_isProp (fun _ => ptrunc_isProp)))).

  Definition acQ_w (w : BE) : acQ (fst w)
    := ptrunc_rec (acQ_isProp _) (fun q => trp acQ q ((snd ac_fEqv; ac_f_isCycle) : acQ (C3pt S0)))
         (snd w).

  Definition acPsi0 (w : BE) : Cyc
    := (fst (fst w); ((snd (fst w) fin2_0; fst (acQ_w w)); snd (acQ_w w))).

  Definition acb : BE := (C3pt S0; trunc refl).

  Definition phi3' (x : Fin 3) : C3s
    := match x with
       | inl (inl (inl e)) => match e with end
       | inl (inl (inr _)) => inl triv
       | inl (inr _) => inr fin2_0
       | inr _ => inr fin2_1
       end.

  Definition psi3' (x : C3s) : Fin 3
    := match x with inl _ => p30 | inr (inl _) => p31 | inr (inr _) => p32 end.

  Definition phi3'Eqv : Fin 3 ≃ C3s.
  Proof.
    refine (mkEqv phi3' psi3' _ _).
    - intros [[[[]|[]]|[]]|[]]; exact refl.
    - intros [[]|[[[]|[]]|[]]]; exact refl.
  Defined.

  Definition phi3'_comm (x : Fin 3) : phi3' (zs3 x) = ac_f (phi3' x).
  Proof.
    refine (_ @ (ac_f_eq _)^). destruct x as [[[[]|[]]|[]]|[]]; exact refl.
  Defined.

  Definition acPsi_pt : Fincyc 2 = acPsi0 acb
    := cyc_path (Fincyc 2) (acPsi0 acb) (endo_path phi3'Eqv (path_forall _ _ phi3'_comm)).

  Definition acPsiC (w : BE) : component Cyc (Fincyc 2)
    := (acPsi0 w; ptrunc_rec ptrunc_isProp
                    (fun q => trunc (acPsi_pt @ ap acPsi0
                                       (path_sigma_prop (fun _ => ptrunc_isProp) (u := acb) (v := w) q)))
                    (snd w)).

  Definition ac_fam (c : Cyc) (s : Fin 2) : cX c -> cX c
    := match s with inl _ => fst (ct c) | inr _ => fun x => fst (ct c) (fst (ct c) x) end.

  Definition acPhi0 (c : Cyc) : EndoFam (Fin 2) := (fst c; ac_fam c).

  Definition ac_ff (x : C3s) : ac_f (ac_f x) = ac_g x
    := ac_f_eq _ @ ap c3rot (ac_f_eq x) @ (ac_g_eq x)^.

  Definition acPhi_b : acPhi0 (acPsi0 acb) = C3pt S0.
  Proof.
    refine (ap (fun h => (fst (C3pt S0); h) : EndoFam (Fin 2)) _).
    apply path_forall. intro s. apply path_forall. intro x.
    destruct s as [[[]|[]]|[]].
    - exact refl.
    - exact (ac_ff x).
  Defined.

  Definition acPhi_pt : C3pt S0 = acPhi0 (Fincyc 2) := acPhi_b^ @ (ap acPhi0 acPsi_pt)^.

  Definition acPhiC (c : component Cyc (Fincyc 2)) : BE
    := (acPhi0 (fst c); ptrunc_rec ptrunc_isProp (fun p => trunc (acPhi_pt @ ap acPhi0 p)) (snd c)).

  Definition acPsiPhi (c : component Cyc (Fincyc 2)) : acPsiC (acPhiC c) = c
    := path_sigma_prop (fun _ => ptrunc_isProp) (u := acPsiC (acPhiC c)) (v := c)
         (cyc_path (fst (acPsiC (acPhiC c))) (fst c) refl).

  Definition acSq (v : EndoFam (Fin 2)) : Type
    := forall x, snd v fin2_1 x = snd v fin2_0 (snd v fin2_0 x).

  Definition acSq_w (w : BE) : acSq (fst w)
    := ptrunc_rec (Pi_isProp (fun x => snd (fst (fst w)) _ _))
         (fun q => trp acSq q ((fun x => (ac_ff x)^) : acSq (C3pt S0))) (snd w).

  Definition acPhiPsi (w : BE) : acPhiC (acPsiC w) = w.
  Proof.
    refine (path_sigma_prop (fun _ => ptrunc_isProp) (u := acPhiC (acPsiC w)) (v := w) _).
    refine (ap (fun h => (fst (fst w); h) : EndoFam (Fin 2)) _).
    apply path_forall. intro s. apply path_forall. intro x.
    destruct s as [[[]|[]]|[]].
    - exact refl.
    - exact (acSq_w w x)^.
  Defined.

  Definition acPsiC_isEquiv : isEquiv acPsiC := iso_to_isEquiv acPsiC acPhiC acPhiPsi acPsiPhi.

  (** The first part: [S2onC3(𝟚) = C_3]. *)
  Definition ac_part1 : S2onC3 S0 = CG 2
    := @path_Group _ (S2onC3 S0) (CG 2) ((acPsiC; path_sigma_prop (fun _ => ptrunc_isProp) (u := sh (CG 2)) (v := acPsiC acb)
                              acPsi_pt); acPsiC_isEquiv).

  (** The second part.  Loops of [BS2onC3(𝟚)] are determined by their
      permutations of [𝟙 ⨿ 𝟚], which commute with [f]. *)
  Local Notation cE := (fun w : BE => fst (fst (fst w))).
  Local Notation K := (S2onC3 (sh (SG 2))).

  Definition acperm_comm {u v : BE} (p : u = v) (s : Fin 2) (x : fst (fst (fst u)))
    : ptoe (ap cE p) (snd (fst u) s x) = snd (fst v) s (ptoe (ap cE p) x).
  Proof. destruct p. exact refl. Defined.

  Definition acperm_idtoeqv {u v : BE} (p : u = v) (x : fst (fst (fst u)))
    : fst (idtoeqv (ap fst (ap fst (ap fst p)))) x = ptoe (ap cE p) x.
  Proof. destruct p. exact refl. Defined.

  Definition acloop_inj (h h' : USym K) (e : forall x, ptoe (ap cE h) x = ptoe (ap cE h') x)
    : h = h'.
  Proof.
    apply (ap_fst_cancel (fun _ => prop_is_set ptrunc_isProp)).
    apply (ap_fst_cancel (fun X : SetU => Pi_isSet (fun _ => Pi_isSet (fun _ => snd X)))).
    apply (ap_fst_cancel (fun X : Type => prop_is_set (isSet_isProp X))).
    refine ((etop_ptoe _)^ @ ap etop (path_Eqv _ _ (ptw_inv (fun x => _))) @ etop_ptoe _).
    exact (acperm_idtoeqv h x @ e x @ (acperm_idtoeqv h' x)^).
  Defined.

  (** The generator, with permutation [f_0]. *)
  Definition trp_fam {X Y : SetU} (p : X = Y) (h : Fin 2 -> fst X -> fst X)
    : trp (fun X : SetU => Fin 2 -> fst X -> fst X) p h
      = fun s x => ptoe (ap fst p) (h s (ptoe (ap fst p)⁻¹ x)).
  Proof. destruct p. exact refl. Defined.

  Definition ac_comm (s : Fin 2) (y : C3s) : ac_f (f3 S0 s y) = f3 S0 s (ac_f y).
  Proof.
    destruct s as [[[]|[]]|[]].
    - exact refl.
    - exact (ac_fg y @ (ac_gf y)^).
  Defined.

  Definition ac_P_eq (y : C3s)
    : ptoe (ap fst (path_SetU0 (S := fst (C3pt S0)) (T := fst (C3pt S0)) ac_fEqv)) y = ac_f y
    := ap (fun q => ptoe q y)
          (@ap_fst_sigma_prop Type isSet (fun A => isSet_isProp A) (fst (C3pt S0)) (fst (C3pt S0))
             (etop ac_fEqv))
       @ ap (fun e : C3s ≃ C3s => fst e y) (ptoe_etop ac_fEqv).

  Definition acgen_T
    : trp (fun X : SetU => Fin 2 -> fst X -> fst X)
        (path_SetU0 (S := fst (C3pt S0)) (T := fst (C3pt S0)) ac_fEqv) (f3 S0) = f3 S0.
  Proof.
    refine (trp_fam _ _ @ _).
    apply path_forall. intro s. apply path_forall. intro x.
    pose (P := ap fst (path_SetU0 (S := fst (C3pt S0)) (T := fst (C3pt S0)) ac_fEqv)).
    exact (ac_P_eq _ @ ac_comm s _ @ ap (f3 S0 s) ((ac_P_eq _)^ @ ptoe_V_r P x)).
  Defined.

  Definition acgen0 : C3pt S0 = C3pt S0
    := pathpair (Y := fun X : SetU => Fin 2 -> fst X -> fst X)
         (path_SetU0 (S := fst (C3pt S0)) (T := fst (C3pt S0)) ac_fEqv) acgen_T.

  Definition acgen : USym K
    := path_sigma_prop (fun _ => ptrunc_isProp) (u := acb) (v := acb) acgen0.

  Definition cE_split {u v : BE} (p : u = v) (x : fst (fst (fst u)))
    : ptoe (ap cE p) x = ptoe (ap (fun X : SetU => fst X) (ap (fun w : EndoFam (Fin 2) => fst w) (ap fst p))) x.
  Proof. destruct p. exact refl. Defined.

  Definition acgen_perm (x : C3s) : ptoe (ap cE acgen) x = ac_f x.
  Proof.
    refine (cE_split acgen x @ _ @ ac_P_eq x).
    refine (ap (fun q : C3pt S0 = C3pt S0 => ptoe (ap (fun X : SetU => fst X) (ap (fun w : EndoFam (Fin 2) => fst w) q)) x)
               (@ap_fst_sigma_prop _ (fun c => ptrunc (C3pt S0 = c)) (fun _ => ptrunc_isProp) acb acb acgen0) @ _).
    exact (ap (fun q : fst (C3pt S0) = fst (C3pt S0) => ptoe (ap (fun X : SetU => fst X) q) x)
              (ap_fst_pathpair (Y := fun X : SetU => Fin 2 -> fst X -> fst X) _ acgen_T)).
  Defined.

  (** Every loop is [refl], [g] or [g g]. *)
  Definition c3_cases (z : C3s) : (z = inl triv) + (z = inr fin2_0) + (z = inr fin2_1).
  Proof.
    destruct z as [[]|[[[]|[]]|[]]]; [left; left | left; right | right]; exact refl.
  Defined.

  Definition acperm_cases (pm : C3s -> C3s) (hc : forall y, pm (ac_f y) = ac_f (pm y))
    : (forall x, pm x = x) + (forall x, pm x = c3rot x) + (forall x, pm x = c3rot (c3rot x)).
  Proof.
    pose (hc' := fun y => ap pm (ac_f_eq y)^ @ hc y @ ac_f_eq _).
    assert (G : forall v, pm (inl triv) = v ->
                  (pm (inl triv) = v) × (pm (inr fin2_0) = c3rot v) × (pm (inr fin2_1) = c3rot (c3rot v))).
    { intros v e0.
      pose (e1 := hc' (inl triv) @ ap c3rot e0).
      exact ((e0; e1); hc' (inr fin2_0) @ ap c3rot e1). }
    destruct (c3_cases (pm (inl triv))) as [[e|e]|e];
      destruct (G _ e) as [[e0 e1] e2];
      [left; left | left; right | right];
      intros [[]|[[[]|[]]|[]]]; assumption.
  Defined.

  Definition acloop_cases (h : USym K) : (h = refl) + (h = acgen) + (h = acgen ⋅ acgen).
  Proof.
    destruct (acperm_cases (ptoe (ap cE h)) (fun y => acperm_comm h fin2_0 y)) as [[E|E]|E];
      [left; left | left; right | right]; apply acloop_inj; intro x.
    - exact (E x).
    - exact (E x @ (acgen_perm x @ ac_f_eq x)^).
    - refine (E x @ _ @ (ptoe_ap_trans cE acgen acgen x)^).
      exact (ap c3rot (acgen_perm x @ ac_f_eq x)^ @ (acgen_perm _ @ ac_f_eq _)^).
  Defined.

  Definition acgen_ne : acgen ≠ refl
    := fun e => inl_ne_inr _ _ ((ap (fun q : USym K => ptoe (ap cE q) (inl triv)) e)^
                                 @ acgen_perm (inl triv)).

  (** Identifications [K = K] are determined by what they do with [g]. *)
  Definition trp_USym_refl {G G' : Group} (P : G = G') : trp USym P refl = refl.
  Proof. destruct P. exact refl. Defined.

  Definition trp_USym_cc {G G' : Group} (P : G = G') (g h : USym G)
    : trp USym P (g ⋅ h) = trp USym P g ⋅ trp USym P h.
  Proof. destruct P. exact refl. Defined.

  Definition acKpath_eq (P P' : K = K) (e : trp USym P acgen = trp USym P' acgen) : P = P'.
  Proof.
    apply (isInj_cancel (isEquiv_isInj (snd (path_Group_Iso_eqv K K)))).
    refine (path_sigma_prop (fun f => isEquiv_isProp _) _).
    apply USymf_cancel. apply path_forall. intro h.
    refine (USymf_path_Group_Iso P h @ _ @ (USymf_path_Group_Iso P' h)^).
    destruct (acloop_cases h) as [[E|E]|E]; destruct E^.
    - exact (trp_USym_refl P @ (trp_USym_refl P')^).
    - exact e.
    - exact (trp_USym_cc P _ _ @ ap011 (fun a b => b ⋅ a) e e @ (trp_USym_cc P' _ _)^).
  Defined.

  (** Transport of [g] along a loop [l] of [BΣ_2]: its permutation is
      conjugated by [id ⨿ trp(l)]. *)
  Definition trp_USym_S2onC3 {S S' : BSG2} (l : S = S') (h : USym (S2onC3 S))
    : trp USym (ap S2onC3 l) h = trp (fun S => USym (S2onC3 S)) l h.
  Proof. destruct l. exact refl. Defined.

  Definition trp_perm {S S' : BSG2} (l : S = S') (h : USym (S2onC3 S)) (x : True ⨿ el2 S)
    : ptoe (ap (fun w : utype (BG (S2onC3 S')) => fst (fst (fst w)))
                (trp (fun S => USym (S2onC3 S)) l h))
           (trp (fun S => True ⨿ el2 S) l x)
      = trp (fun S => True ⨿ el2 S) l
          (ptoe (ap (fun w : utype (BG (S2onC3 S)) => fst (fst (fst w))) h) x).
  Proof. destruct l. exact refl. Defined.

  Definition trp_sum_inl {S S' : BSG2} (l : S = S') (t : True)
    : trp (fun S => True ⨿ el2 S) l (inl t) = inl t.
  Proof. destruct l. exact refl. Defined.

  Definition trp_sum_inr {S S' : BSG2} (l : S = S') (s : el2 S)
    : trp (fun S => True ⨿ el2 S) l (inr s) = inr (trp el2 l s).
  Proof. destruct l. exact refl. Defined.

  Definition acLg (l : S0 = S0) : USym K := trp (fun S => USym (S2onC3 S)) l acgen.

  Definition acLg_0 (l : S0 = S0)
    : ptoe (ap cE (acLg l)) (inl triv) = inr (trp el2 l fin2_0)
    := ap (ptoe (ap cE (acLg l))) (trp_sum_inl l triv)^ @ trp_perm l acgen (inl triv)
       @ ap (trp (fun S => True ⨿ el2 S) l) (acgen_perm (inl triv)) @ trp_sum_inr l fin2_0.

  Definition SGS_perm_trp {A B : BSG2} (p : A = B) (x : el2 A)
    : fst (SGS_perm (S := FinSetU 2) p) x = trp el2 p x.
  Proof. destruct p. exact refl. Defined.

  (** Loops of [BΣ_2] are determined by where they send [0]. *)
  Definition sg2_loop_inj (l l' : S0 = S0) (e : trp el2 l fin2_0 = trp el2 l' fin2_0) : l = l'.
  Proof.
    destruct (trp2_cases l) as [b [E _]], (trp2_cases l') as [b' [E' _]].
    assert (bb : b = b').
    { pose (e0 := (E fin2_0)^ @ e @ E' fin2_0).
      destruct b, b'; first [exact refl | destruct (f2_ne e0) | destruct (f2_ne e0^)]. }
    apply SGS_perm_inj. intro x.
    exact (SGS_perm_trp l x @ E x @ ap (fun c => perm2 c x) bb @ (E' x)^ @ (SGS_perm_trp l' x)^).
  Defined.

  (** [g] transported along the swap is [g g]. *)
  Definition sw3 (x : C3s) : C3s := match x with inl t => inl t | inr s => inr (f2sw s) end.

  Definition sw3_trp (x : C3s) : trp (fun S => True ⨿ el2 S) gsw2 x = sw3 x.
  Proof.
    destruct x as [t|s].
    - exact (trp_sum_inl gsw2 t).
    - exact (trp_sum_inr gsw2 s @ ap inr (trp_lp2 Bool.true s)).
  Defined.

  Definition acLg_sw : acLg gsw2 = acgen ⋅ acgen.
  Proof.
    apply acloop_inj. intro y.
    refine (ap (ptoe (ap cE (acLg gsw2))) (sw3_trp (sw3 y) @ _)^ @ trp_perm gsw2 acgen (sw3 y)
            @ sw3_trp _ @ ap sw3 (acgen_perm _ @ ac_f_eq _) @ _ @ (ptoe_ap_trans cE acgen acgen y)^).
    - destruct y as [[]|[[[]|[]]|[]]]; exact refl.
    - refine (_ @ ap c3rot (acgen_perm y @ ac_f_eq y)^ @ (acgen_perm _ @ ac_f_eq _)^).
      destruct y as [[]|[[[]|[]]|[]]]; exact refl.
  Defined.

  Definition inr_cancel3 {s s' : Fin 2} (e : (inr s : C3s) = inr s') : s = s'
    := ap (fun z : C3s => match z with inl _ => s | inr t => t end) e.

  Definition acLg_inj (l l' : S0 = S0) (E : acLg l = acLg l') : l = l'.
  Proof.
    apply sg2_loop_inj. apply inr_cancel3.
    refine ((acLg_0 l)^ @ _ @ acLg_0 l').
    destruct E. exact refl.
  Defined.


  Definition acS_inj (l l' : S0 = S0) (e : ap S2onC3 l = ap S2onC3 l') : l = l'
    := acLg_inj l l' ((trp_USym_S2onC3 l acgen)^ @ ap (fun q : K = K => trp USym q acgen) e
                      @ trp_USym_S2onC3 l' acgen).

  (** Every identification [K = K] comes from a loop of [BΣ_2]. *)
  Definition acS_surj (P : K = K) : ptrunc {l : S0 = S0 & ap S2onC3 l = P}.
  Proof.
    apply trunc.
    pose (ψ := trp USym P).
    destruct (acloop_cases (ψ acgen)) as [[E|E]|E].
    - destruct (acgen_ne ((trp_V_p USym P acgen)^ @ ap (trp USym P⁻¹) (E @ (trp_USym_refl _)^)
                          @ trp_V_p USym P refl)).
    - exists refl. exact (acKpath_eq refl P E^).
    - exists gsw2.
      exact (acKpath_eq (ap S2onC3 gsw2) P (trp_USym_S2onC3 gsw2 acgen @ acLg_sw @ E^)).
  Defined.

End AutC3.

(** The map [BΣ_2 → BAut(C_3)], for any proof [m] that it lands in the
    component: injective and surjective on loops at [𝟚]. *)
Definition acF `{Univalence} (m : forall S, ptrunc (CG 2 = S2onC3 S)) (S : BSG2)
  : component Group (CG 2) := (S2onC3 S; m S).

Definition acF_fst `{Univalence} (m : forall S, ptrunc (CG 2 = S2onC3 S))
  {S S' : BSG2} (l : S = S') : ap fst (ap (acF m) l) = ap S2onC3 l.
Proof. destruct l. exact refl. Defined.

Definition acF_ap_isInj `{Univalence} (m : forall S, ptrunc (CG 2 = S2onC3 S))
  : isInj (@ap _ _ (acF m) (sh (SG 2)) (sh (SG 2))).
Proof.
  refine (cancel_isInj (component_isGrpd Group_isGrpd (CG 2) _ _) (fun l l' e => _)).
  apply acS_inj.
  exact ((acF_fst m l)^ @ ap (ap fst) e @ acF_fst m l').
Defined.

Definition acF_ap_isSurj `{Univalence} (m : forall S, ptrunc (CG 2 = S2onC3 S))
  : isSurj (@ap _ _ (acF m) (sh (SG 2)) (sh (SG 2))).
Proof.
  intro q. refine (ptrunc_rec ptrunc_isProp _ (acS_surj (ap fst q))). intros [l e].
  apply trunc. exists l.
  apply (ap_fst_cancel (fun _ => prop_is_set ptrunc_isProp)).
  exact (e^ @ (acF_fst m l)^).
Defined.

Definition xca_AutC3 `{Univalence} : xca_AutC3_stmt
  := (ac_part1; fun m => snd (conn_isEquiv_iff_point (acF m) (BG_isConn (SG 2))
                                (component_isConn (CG 2)) (sh (SG 2)))
                            (inj_surj_isEquiv (acF_ap_isInj m) (acF_ap_isSurj m))).
