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

    Left out (statements only)
    - That [Inn(G)] is
      normal ([Inn_normal_stmt]); construction [cons:simpler-version-Out]
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

  (** The lemma that [Inn(G)] is normal in [Aut(G)] (statement only). *)
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
