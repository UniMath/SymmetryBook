(** * Section 9.7 Automorphisms of groups

    Part of Chapter 9 ([subgroups.tex]); see [Subgroups.v] for an
    overview of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - [Aut(G)] ([AutGrp]): [Group] is universe polymorphic, so
      [Aut_Group(G)] is a group (in a larger universe than [G]); its
      classifying type is [BAutG] of Section 4.4 by definition.  NOTE:
      the summaries of Sections 4.2 and 4.4 say that [Group] is not
      universe polymorphic; that is outdated.
    - [inn : Hom(G, Aut(G))] ([mkhom (Binn G)], pointed by [(inc_out G)⁻¹]);
      [out(G)] ([outG], the cokernel of [inn]); [Inn(G)] ([InnG], the
      image of [inn]); [Out(G)] ([OutG]).
    - The remark on [USym inn] ([USym_inn], via [USymf_path_Group_Iso]
      and [trp_Binn_loop] of Section 7.3), with [h ↦ g h g⁻¹].  NOTE for
      the book text: the remark says [h ↦ g⁻¹ h g]; see [USym_inn_stmt].
    - Lemma [lemma:coker-out-action] ([coker_out_action]): the fibers of
      [Binn] by the book's chain of equivalences ([fiber_Binn_eqv]), and
      the set truncation of an equivalence ([strunc_eqv]).
    - The kernel of [inn] is [Aut_{BG_÷ = BG_÷}(refl)] ([ker_inn_center],
      via [fiber_Binn_eqv], which sends [shKer] to [refl]); this is the
      center of [sec:abelian-groups] (Chapter 12, not formalized yet).
    - That [Inn(G)] is normal ([Inn_normal], after the section): the
      family [y ↦ (z ↦ ‖BG(z)_÷ = BG(y)_÷‖₀)] pointed at [|refl|]
      ([XU], [NInn]) is transitive, since every [e : BK_÷ = BK_÷] merely
      comes from an identification [K = K] ([KL_group]); at the shape it
      is [out(G)] pointed at [|shKer|] ([coker_out_action],
      [fiber_Binn_shKer]).

    Left out (statements only)
    - Construction [cons:simpler-version-Out]
      ([cons_simpler_version_Out_stmt], as an isomorphism, with
      [Trunc1U_isGrpd]).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core.
From SymmetryBook Require Export Subgroups.S06_IntersectNormal.

Local Open Scope uf_scope.

(** ** 9.7 Automorphisms of groups *)

(** [USymf] of the isomorphism given by an identification of groups is
    transport. *)
Definition USymf_path_Group_Iso `{Univalence} {G K : Group} (P : G = K) (h : USym G)
  : USymf (fst (fst (path_Group_Iso_eqv G K) P)) h = trp USym P h.
Proof. destruct P. destruct G as [X]. exact (trans_1p _ @ ap_idmap h). Defined.

(** The set truncation of an equivalence. *)
Definition strunc_eqv {A B : Type} (e : A ≃ B) : strunc A ≃ strunc B.
Proof.
  refine (mkEqv (strunc_rec strunc_isSet (fun a => settrunc (fst e a)))
                (strunc_rec strunc_isSet (fun b => settrunc (eqinv (snd e) b))) _ _).
  - exact (strunc_ind_prop _ (fun _ => strunc_isSet _ _)
             (fun a => ap settrunc (eqinv_l (snd e) a))).
  - exact (strunc_ind_prop _ (fun _ => strunc_isSet _ _)
             (fun b => ap settrunc (eqinv_r (snd e) b))).
Defined.

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
