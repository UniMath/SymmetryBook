(** * Section 5.3 Subgroups

    Part of Chapter 5 ([actions.tex]); see [Actions.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:set-of-subgroups]: [SubGrp G :≡ ∑_X X(sh_G) ×
      isTrans(X)]; exercise [xca:group-Xx!] ([TotG_isGrpd] and
      [conn_of_trans] of Section 5.2); definition
      [def:underlying-group-of-subgroup] ([subgrp_group]).
    - Lemma [lem:SubGisset] ([SubGrp_isSet]), via
      [pointed_GSet_paths_isProp]: identifications of pointed transitive
      [G]-sets form the fibers of the injective evaluation map
      ([ev_path_isInj]).
    - Definition [def:decidable-subgroup] ([isDecSubGrp]).
    - Definition [def:typeofmono]: [ismono], [Mono G], [Mono_trivial],
      [Mono_proper]; example [ex:prodinclismono] ([inG1_ismono],
      [inG2_ismono]) and example [ex:SGninSGn+1] ([ex_SGninSGn1]: a
      loop of [BΣ_S] is determined by its permutation ([SGS_perm_inj]),
      and [_ ⨿ T] acts on permutations as [σ ⨿ id] ([sum_hom_perm])).
    - The map [F : Sub(G) → Mono(G)] of lemma [lem:SubG=MonoG]
      ([subgrp_to_mono]); [Ufst] is injective since identifications in
      a total space over a family of sets are determined by their first
      component ([ap_fst_cancel]).
    - Lemma [lem:E-preserves-symms] ([E_preserves_symms]), stated for
      [F(X, pt)] (the book reduces to this case).
    - Definition [def:triv-proper-Mono] ([SubGrp_trivial],
      [SubGrp_proper]).
    - Constructions [con:lagrange] ([lagrange]) and [cor:lagrange-dep-sum]
      ([lagrange_dep]).
    - Exercises [xca:n-is-ptd-n+1] ([xca_n_is_ptd]: [S ↦ (S ⨿ 𝟙, inr tt)],
      inverse [(X, x) ↦ X - {x}], with [Cpl_card] by counting) and
      [xca:A-is-A-1+1] ([xca_A_is_A_1_1]); the book's hint for the first
      ([xca:finsets-decidable]) is used through [finset_isDecSet].
    - Exercise [xca:lagrange] ([subgrp_Finite], [lagrange_card]), with
      the library's [Finite] and [fcard]; the choice function needed by
      the Lagrange construction exists merely, by transitivity and finite
      choice.
    - Exercise [xca:lagrange-Z-action-Rm] ([xca_lagrange_Z_Rm]), by
      [con:lagrange] with the choice map [i ↦ loop⁻ⁱ]
      ([lagrange_choice_Rm]), since [loop⁻¹] acts as the predecessor;
      this also shows that [R_m] is transitive ([RmZset_trans]), which
      the statement assumes.
    - Exercise [xca:lagrange-if-subgr-not-normal]
      ([xca_lagrange_wedge]): the same argument ([pred_choice]) with the
      loop [pushl(loop)], which acts as the successor; the wedge is still
      assumed a connected groupoid.

    - Example [ex:prodinclisGset] ([ex_prodinclisGset], with the
      transitivity as a hypothesis): [a ↦ ((a, sh_{G'}), refl)] is a
      pointed equivalence compatible with the inclusions.  Identifications
      in [Mono(G)] come from such pointed equivalences ([Mono_path]).
    - That [F] is an equivalence (lemma [lem:SubG=MonoG], exercise
      [xca:SubG=MonoG]) and corollary [lem:setofsubgroups]: statements
      [lem_SubG_MonoG_stmt] and [lem_setofsubgroups_stmt] here, proofs
      [lem_SubG_MonoG] and [lem_setofsubgroups] in Section 9.2
      ([Subgroups/S02_Epis.v]), since the inverse uses that the fibers of
      [Bi] are sets for a mono [i] ([ismono_isCovering]).

    Left out (statements only, no proofs yet; time limit per result)
    - Examples [ex:Rm0-subgroup], [exa:fix1subSGn], [exa:C3subC6],
      [exa:EforSG3], and exercises
      [xca:SG2subSG3] and [xca:C3subSG3] (the [..._stmt] definitions);
      where an example needs that a [G]-set is transitive, this is a
      hypothesis.
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Cubical.DPath HFiber
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite Spaces.Nat.Core Projective
  Colimits.Pushout Spaces.Circle.
From SymmetryBook Require Export Actions.S02_GSets.

Local Open Scope uf_scope.

(** ** 5.3 Subgroups *)

(** Definition [def:set-of-subgroups]. *)
Definition SubGrp (G : Group) : Type
  := {X : GSet G & el X (sh G) × istrans X}.

Definition sg_X {G : Group} (S : SubGrp G) : GSet G := fst S.
Definition sg_pt {G : Group} (S : SubGrp G) : el (sg_X S) (sh G) := fst (snd S).
Definition sg_trans {G : Group} (S : SubGrp G) : istrans (sg_X S) := snd (snd S).

(** Exercise [xca:group-Xx!]. *)
Definition TotG_isGrpd `{Funext} {G : Group} (X : GSet G) : isGrpd (TotG X)
  := Sigma_ntype 1 (BG_isGrpd G) (fun z => set_ntype 1 (el_isSet X z)).

(** Definition [def:underlying-group-of-subgroup]. *)
Definition subgrp_group `{Funext} {G : Group} (S : SubGrp G) : Group
  := mkgroup (TotG (sg_X S); ((sh G; sg_pt S);
                (conn_of_trans _ (sg_trans S); TotG_isGrpd (sg_X S)))).

(** Example [ex:Rm0-subgroup]: the symmetries of [ℤ] picked out by
    [(R_m, 0)] are the [loop^{mk}]. *)
Definition ex_Rm0_subgroup_stmt `{Univalence} : Type
  := forall (k : ℕ) (p : base = base),
       (trp (Rm k) p fin_zero = fin_zero)
       <-> ptrunc {j : ℤ & p = loopZ (zmul (iplus (S k)) j)}.

(** Lemma [lem:SubGisset]. *)
Definition istrans_isProp {G : Group} (X : GSet G) : isProp (istrans X) := ptrunc_isProp.

Definition trp_el_hom_of_path {G : Group} {X Y : GSet G} (e : X = Y) (z : utype (BG G))
  (x : el X z) : trp (fun X : GSet G => el X z) e x = hom_of_path e z x.
Proof. destruct e. exact refl. Defined.

Definition pointed_GSet_paths_isProp `{Univalence} {G : Group} (X X' : GSet G)
  (t : istrans X) (x : el X (sh G)) (x' : el X' (sh G))
  : isProp (((X; x) : {X : GSet G & el X (sh G)}) = (X'; x')).
Proof.
  refine (isProp_Eqv (path_sigma_eqv (Y := fun X : GSet G => el X (sh G))) _).
  refine (isProp_Eqv _ (ev_path_isInj (Y := X') t x x')).
  refine (tot (fun e (h : x' = hom_of_path e (sh G) x) =>
                 (h⁻¹ ⋅ trp_el_hom_of_path e (sh G) x) : PathOver _ e x x');
          tot_isEquiv _ (fun e => _)).
  destruct e. change (isEquiv (fun h : x' = x => h⁻¹ ⋅ refl)).
  refine (iso_to_isEquiv _ (fun k => k⁻¹) _ _); intro h; destruct h; exact refl.
Defined.

Definition SubGrp_isSet `{Univalence} (G : Group) : isSet (SubGrp G).
Proof.
  pose (r := mkEqv (fun S : SubGrp G => (((sg_X S; sg_pt S) : {X : GSet G & el X (sh G)});
                                          sg_trans S))
                   (fun w : {Y : {X : GSet G & el X (sh G)} & istrans (fst Y)} =>
                      (fst (fst w); (snd (fst w); snd w)) : SubGrp G)
                   (fun _ => refl) (fun _ => refl)
             : SubGrp G ≃ {Y : {X : GSet G & el X (sh G)} & istrans (fst Y)}).
  intros u v.
  refine (isProp_Eqv (Eqv_inv (Eqv_comp (Eqv_of_Equiv (equiv_ap' (Equiv_of_Eqv r) u v))
                                 (subtype_paths_eqv (fun Y => istrans_isProp (fst Y)) _ _))) _).
  exact (pointed_GSet_paths_isProp _ _ (sg_trans u) _ _).
Defined.

(** Example [exa:fix1subSGn]: the subgroup [(X, k)] of [Σ_{n+1}] fixing
    [k] has underlying group isomorphic to [Σ_n]. *)
Definition exa_fix1subSGn_stmt `{Univalence} : Type
  := forall (n : ℕ) (k : Fin (S n)) (t : istrans (std_SGset (S n))),
       Iso (subgrp_group ((std_SGset (S n); (k; t)) : SubGrp (SG (S n)))) (SG n).

(** Exercises [xca:n-is-ptd-n+1] and [xca:A-is-A-1+1]. *)
Definition xca_n_is_ptd_stmt `{Univalence} : Type
  := forall n : ℕ, FinSet_n n ≃ {X : FinSet_n (S n) & fst (fst X)}.

Definition xca_A_is_A_1_1_stmt `{Univalence} : Type
  := forall A : Type, isDecSet A -> A ≃ {B : Type & A ≃ (B ⨿ True)}.

Section RemovePoint.
  Context `{Univalence} {A : Type} (dA : isDecSet A).

  (** The complement [A - {a}] and the equivalence [A ≃ (A - {a}) + 𝟙]. *)
  Definition unit_tt (t : True) : t = tt := match t with tt => refl end.

  Definition Cpl (a : A) : Type := {x : A & x ≠ a}.

  Definition Cpl_path {a : A} (u v : Cpl a) (r : fst u = fst v) : u = v
    := path_sigma_prop (fun x => Pi_isProp (fun _ (e e' : Empty) => match e with end)) r.

  Definition cplE (a : A) : A ≃ (Cpl a ⨿ True).
  Proof.
    refine (mkEqv (fun x => match snd (dA x a) with inl _ => inr tt | inr ne => inl (x; ne) end)
                  (fun s => match s with inl w => fst w | inr _ => a end) _ _).
    - intro x. destruct (snd (dA x a)) as [e|ne]; [exact e^ | exact refl].
    - intros [[x ne]|[]].
      + cbn. destruct (snd (dA x a)) as [e|ne']; [destruct (ne e)|].
        apply ap. apply Cpl_path. exact refl.
      + destruct (snd (dA a a)) as [_|ne]; [exact refl | destruct (ne refl)].
  Defined.

  Definition cplE_inv_tt (a : A) : eqinv (snd (cplE a)) (inr tt) = a := refl.

  Definition sum_map {C B : Type} (g : C -> B) (s : C ⨿ True) : B ⨿ True
    := match s with inl c => inl (g c) | inr t => inr t end.

  Definition trp_sumEqv {C B : Type} (p : C = B) (f : A ≃ (C ⨿ True)) (x : A)
    : fst (trp (fun B => A ≃ (B ⨿ True)) p f) x = sum_map (ptoe p) (fst f x).
  Proof. destruct p. change (fst f x = sum_map idmap (fst f x)). destruct (fst f x); exact refl. Defined.

  Section Back.
    Context (B : Type) (e : A ≃ (B ⨿ True)).

    Local Notation a := (eqinv (snd e) (inr tt)).

    Definition psiB (b : B) : Cpl a.
    Proof.
      refine (eqinv (snd e) (inl b); _). intro r.
      exact (inl_ne_inr _ _ ((eqinv_r (snd e) (inl b))^ @ ap (fst e) r @ eqinv_r (snd e) (inr tt))).
    Defined.

    Definition psiB_isEquiv : isEquiv psiB.
    Proof.
      refine (iso_to_isEquiv psiB
                (fun w => match fst e (fst w) as s return (fst e (fst w) = s -> B) with
                          | inl b => fun _ => b
                          | inr t => fun r => match snd w ((eqinv_l (snd e) (fst w))^
                                                  @ ap (eqinv (snd e)) (r @ ap inr (unit_tt t))) with end
                          end refl) _ _).
      - intro b. cbn.
        generalize (refl (fst e (eqinv (snd e) (inl b)))).
        generalize (fst e (eqinv (snd e) (inl b))) at 2 3. intros s r.
        destruct s as [b'|t].
        + exact (ap (fun s => match s with inl c => c | inr _ => b end) (r^ @ eqinv_r (snd e) (inl b))).
        + destruct (inl_ne_inr _ _ ((eqinv_r (snd e) (inl b))^ @ r)).
      - intros [x ne]. cbn.
        generalize (refl (fst e x)). generalize (fst e x) at 2 3. intros s r.
        destruct s as [b'|t].
        + apply Cpl_path. cbn. exact (ap (eqinv (snd e)) r^ @ eqinv_l (snd e) x).
        + destruct (ne ((eqinv_l (snd e) x)^ @ ap (eqinv (snd e)) (r @ ap inr (unit_tt t)))).
    Defined.

    Definition phiB : Cpl a ≃ B := Eqv_inv (psiB; psiB_isEquiv).


    Definition cpl_back_path : ((Cpl a; cplE a) : {B : Type & A ≃ (B ⨿ True)}) = (B; e).
    Proof.
      refine (pathpair (etop phiB) _).
      apply path_Eqv. apply path_forall. intro x.
      refine (trp_sumEqv (etop phiB) (cplE a) x @ _).
      refine (ap (fun g => sum_map g (fst (cplE a) x)) (ap fst (ptoe_etop phiB)) @ _).
      unfold cplE. cbn.
      destruct (snd (dA x a)) as [r|ne].
      - refine (_ @ ap (fst e) r^). exact (eqinv_r (snd e) (inr tt))^.
      - cbn. generalize (refl (fst e x)). generalize (fst e x) at 2 3. intros s r.
        destruct s as [b|t].
        + exact r^.
        + destruct (ne ((eqinv_l (snd e) x)^ @ ap (eqinv (snd e)) (r @ ap inr (unit_tt t)))).
    Defined.
  End Back.

  (** Exercise [xca:A-is-A-1+1]: [a ↦ (A - {a}, ·)], with inverse
      [(B, e) ↦ e⁻¹(inr tt)]. *)
  Definition xca_A_is_A_1_1_eqv : A ≃ {B : Type & A ≃ (B ⨿ True)}
    := mkEqv (fun a => (Cpl a; cplE a)) (fun w => eqinv (snd (snd w)) (inr tt))
             (fun a => refl) (fun w => cpl_back_path (fst w) (snd w)).
End RemovePoint.

Section PointedFinSets.
  Context `{Univalence}.

  Definition path_FS {k : ℕ} {S T : FinSet_n k} (E : fst (fst S) ≃ fst (fst T)) : S = T
    := path_sigma_prop (fun _ => ptrunc_isProp)
         (path_sigma_prop (fun X => isSet_isProp X) (u := fst S) (v := fst T) (etop E)).

  Definition trp_FS {k : ℕ} {S T : FinSet_n k} (E : fst (fst S) ≃ fst (fst T)) (y : fst (fst S))
    : trp (fun X : FinSet_n k => fst (fst X)) (path_FS E) y = fst E y.
  Proof.
    refine ((ptoe_ap (fun X : FinSet_n k => fst (fst X)) (path_FS E) y)^ @ _).
    refine (ap (fun q => ptoe q y) (ap_compose fst fst _ @ _) @ ap (fun e => fst e y) (ptoe_etop E)).
    unfold path_FS. rewrite ap_fst_sigma_prop. exact (ap_fst_sigma_prop _ _).
  Defined.

  Definition FS_isFinSet {k : ℕ} (X : FinSet_n k) : isFinSet (fst (fst X))
    := ptrunc_rec ptrunc_isProp (fun q => trunc (k; q^)) (snd X).

  (** Removing a point from a [k+1]-element set leaves a [k]-element set. *)
  Definition Cpl_Finite {X : Type} (FX : Finite X) (dX : isDecSet X) (x : X) : Finite (Cpl x).
  Proof.
    refine (@finite_sigma _ (fun y => y ≠ x) FX (fun y => @finite_decidable_hprop _ _ _)).
    - exact (isProp_IsHProp (Pi_isProp (fun _ (e e' : Empty) => match e with end))).
    - destruct (snd (dX y x)) as [e|ne]; [exact (inr (fun k => k e)) | exact (inl ne)].
  Defined.

  Definition Cpl_card {k : ℕ} (X : FinSet_n (S k)) (x : fst (fst X))
    : ptrunc (Fin k = Cpl x).
  Proof.
    pose (FX := isFinSet_Finite (FS_isFinSet X)).
    pose (dX := finset_isDecSet (FS_isFinSet X)).
    pose (FC := Cpl_Finite FX dX x).
    assert (c : fcard (Cpl x) = k).
    { refine (ptrunc_rec (ℕ_isSet _ _) _ (snd X)). intro q.
      assert (e : (fcard (Cpl x) + fcard True)%nat = S k).
      { refine ((fcard_sum (Cpl x) True)^ @ _).
        refine ((fcard_equiv' (Equiv_of_Eqv (cplE dX x)))^ @ _).
        exact (fcard_equiv' (Equiv_of_Eqv (idtoeqv q)))^. }
      apply path_nat_succ. refine (_ @ e).
      exact (ap S (nat_add_zero_r _)^ @ (nat_add_succ_r _ 0)^). }
    refine (ptrunc_rec ptrunc_isProp _ (merely_equiv_fin (Cpl x))). intro f.
    exact (trunc ((ap Fin c)^ @ etop (Eqv_inv (Eqv_of_Equiv f)))).
  Defined.

  Context (n : ℕ).

  Definition FS_plus1 (S0 : FinSet_n n) : FinSet_n (S n)
    := ((fst (fst S0) ⨿ True; sum_isSet (snd (fst S0)) (prop_is_set True_isProp));
        ptrunc_rec ptrunc_isProp (fun q => trunc (ap (fun T => T ⨿ True) q)) (snd S0)).

  Definition FS_minus1 (X : FinSet_n (S n)) (x : fst (fst X)) : FinSet_n n
    := ((Cpl x; Sigma_isSet (snd (fst X)) (fun _ => Pi_isSet (fun _ (e e' : Empty) => match e with end)));
        Cpl_card X x).

  Definition minus_plus (S0 : FinSet_n n) : FS_minus1 (FS_plus1 S0) (inr tt) = S0.
  Proof.
    apply path_FS.
    refine (mkEqv (fun w : Cpl (inr tt : fst (fst S0) ⨿ True) =>
                     match fst w as y return (y ≠ inr tt -> fst (fst S0)) with
                     | inl s => fun _ => s
                     | inr t => fun ne => match ne (ap inr (unit_tt t)) with end
                     end (snd w))
                  (fun s => (inl s; fun q => inl_ne_inr _ _ q)) _ _).
    - intros [[s|t] ne].
      + apply Cpl_path. exact refl.
      + destruct (ne (ap inr (unit_tt t))).
    - intro s. exact refl.
  Defined.

  Definition plus_minus (X : FinSet_n (S n)) (x : fst (fst X))
    : ((FS_plus1 (FS_minus1 X x); inr tt) : {X : FinSet_n (S n) & fst (fst X)}) = (X; x).
  Proof.
    pose (dX := finset_isDecSet (FS_isFinSet X)).
    refine (pathpair (path_FS (S := FS_plus1 (FS_minus1 X x)) (T := X) (Eqv_inv (cplE dX x))) _).
    exact (trp_FS (S := FS_plus1 (FS_minus1 X x)) (T := X) (Eqv_inv (cplE dX x)) (inr tt)).
  Defined.

  (** Exercise [xca:n-is-ptd-n+1]: [S ↦ (S ⨿ 𝟙, inr tt)], with inverse
      [(X, x) ↦ X - {x}]. *)
  Definition xca_n_is_ptd_eqv : FinSet_n n ≃ {X : FinSet_n (S n) & fst (fst X)}
    := mkEqv (fun S0 => (FS_plus1 S0; inr tt)) (fun w => FS_minus1 (fst w) (snd w))
             minus_plus (fun w => plus_minus (fst w) (snd w)).
End PointedFinSets.

Definition xca_n_is_ptd `{Univalence} : xca_n_is_ptd_stmt
  := xca_n_is_ptd_eqv.

Definition xca_A_is_A_1_1 `{Univalence} : xca_A_is_A_1_1_stmt
  := fun A dA => xca_A_is_A_1_1_eqv dA.

(** Example [exa:C3subC6]: [C_6] has a subgroup isomorphic to [C_3]. *)
Definition exa_C3subC6_stmt `{Univalence} : Type
  := {S : SubGrp (CG 5) & Iso (subgrp_group S) (CG 2)}.

(** Definition [def:decidable-subgroup]. *)
Definition isDecSubGrp {G : Group} (S : SubGrp G) : Type := isDecSet (el (sg_X S) (sh G)).

(** Definition [def:typeofmono]. *)
Definition ismono {H G : Group} (i : Hom H G) : Type := isInj (USymf i).

Definition Mono (G : Group) : Type := {H : Group & {i : Hom H G & ismono i}}.

Definition Mono_trivial {G : Group} (m : Mono G) : Type := isContr (utype (BG (fst m))).

Definition Mono_proper {G : Group} (m : Mono G) : Type := ¬ isIso (fst (snd m)).

(** Example [ex:SGninSGn+1]: [B ↦ B ⨿ T] gives a monomorphism
    [Σ_S → Σ_{S ⨿ T}]. *)
Definition ex_SGninSGn1_stmt `{Univalence} : Type
  := forall S T : SetU, ismono (sum_hom S T).

(** The underlying permutation of a loop in [BΣ_S] determines the loop. *)
Definition SGS_perm `{Univalence} {S : SetU} {A B : utype (BG (SG_S S))} (p : A = B)
  : fst (fst A) ≃ fst (fst B)
  := idtoeqv (ap fst (ap fst p)).

Definition SGS_perm_inj `{Univalence} {S : SetU} {A B : utype (BG (SG_S S))} (p q : A = B)
  (h : forall x, fst (SGS_perm p) x = fst (SGS_perm q) x) : p = q.
Proof.
  pose (j1 := isInj_cancel (isEquiv_isInj (snd (subtype_paths_eqv (fun _ => ptrunc_isProp) A B)))).
  pose (j2 := isInj_cancel (isEquiv_isInj
                (snd (subtype_paths_eqv (fun X => isSet_isProp X) (fst A) (fst B))))).
  apply j1. apply j2.
  exact ((etop_ptoe _)^ @ ap etop (path_Eqv _ _ (ptw_inv h)) @ etop_ptoe _).
Defined.

Definition sum_hom_perm `{Univalence} (S T : SetU) {A B : utype (BG (SG_S S))} (p : A = B)
  (x : fst (fst A))
  : fst (SGS_perm (ap (comp_map S (sumSetU T)) p)) (inl x) = inl (fst (SGS_perm p) x).
Proof. destruct p. exact refl. Defined.

Definition ex_SGninSGn1 `{Univalence} : ex_SGninSGn1_stmt.
Proof.
  intros S T. refine (cancel_isInj (USym_isSet _) _). intros p q e.
  assert (r : forall l : USym (SG_S S),
             USymf (sum_hom S T) l = ap (comp_map S (sumSetU T)) l).
  { intro l. exact (trans_1p _). }
  apply SGS_perm_inj. intro x.
  exact (ap (fun s => match s with inl y => y | inr _ => x end)
            ((sum_hom_perm S T p x)^
             @ ap (fun l : USym (SG_S (sumSetU T S)) => fst (SGS_perm l) (inl x))
                  ((r p)^ @ e @ r q)
             @ sum_hom_perm S T q x)).
Defined.

(** Exercise [xca:SG2subSG3]: for a pointing path [π], the image of
    [Ui_3] consists of the permutations fixing the point [π⁻¹(inr triv)];
    here [Σ_3] is represented by the set [Fin 2 ⨿ 𝟙]. *)
Definition T1 `{Univalence} : SetU := (True; prop_is_set True_isProp).

Definition X3 `{Univalence} : SetU := sumSetU T1 (FinSetU 2).

Definition i3 `{Univalence} (pp : sh (SG_S X3) = comp_map (FinSetU 2) (sumSetU T1) (sh (SG 2)))
  : Hom (SG 2) (SG_S X3)
  := mkhom ((comp_map (FinSetU 2) (sumSetU T1); pp) : BG (SG 2) →* BG (SG_S X3)).

Definition xca_SG2subSG3_stmt `{Univalence} : Type
  := forall (pp : sh (SG_S X3) = comp_map (FinSetU 2) (sumSetU T1) (sh (SG 2)))
            (σ : USym (SG_S X3)),
       let xpp := ptoe (ap (fun w : utype (BG (SG_S X3)) => fst (fst w)) pp)⁻¹ (inr triv) in
       ptrunc (fiber (USymf (i3 pp)) σ)
       <-> (ptoe (ap (fun w : utype (BG (SG_S X3)) => fst (fst w)) σ) xpp = xpp).

(** Exercise [xca:C3subSG3]. *)
Definition xca_C3subSG3_stmt `{Univalence} : Type
  := {j : Hom (CG 2) (SG 3) & {j' : Hom (CG 2) (SG 3) &
       {m : ismono j & {m' : ismono j' &
         (USymf j ≠ USymf j')
         × (((CG 2; (j; m)) : Mono (SG 3)) = (CG 2; (j'; m')))}}}}.

(** Example [ex:prodinclismono]: the inclusions into [G × H] are
    monomorphisms. *)
Definition inj_of_retraction {A B : Type} (sB : isSet B) (f : A -> B) (r : B -> A)
  (h : forall a, r (f a) = a) : isInj f
  := cancel_isInj sB (fun a a' e => (h a)^ @ ap r e @ h a').

Definition ap_fst_ap_pair {A B : Type} (b : B) {x y : A} (p : x = y)
  : ap fst (ap (fun z => (z; b) : A × B) p) = p.
Proof. destruct p. exact refl. Defined.

Definition ap_snd_ap_pair {A B : Type} (a : A) {x y : B} (p : x = y)
  : ap (fun w : A × B => snd w) (ap (fun z => (a; z) : A × B) p) = p.
Proof. destruct p. exact refl. Defined.

Definition inG1_ismono `{Funext} (G K : Group) : ismono (inG1 G K)
  := inj_of_retraction (USym_isSet _) _ (fun q : USym (prodG G K) => ap fst q)
       (fun g => ap (ap fst) (trans_1p _) @ ap_fst_ap_pair _ g).

Definition inG2_ismono `{Funext} (G K : Group) : ismono (inG2 G K)
  := inj_of_retraction (USym_isSet _) _ (fun q : USym (prodG G K) => ap (fun w : utype (BG (prodG G K)) => snd w) q)
       (fun g => ap (ap (fun w : utype (BG (prodG G K)) => snd w)) (trans_1p _) @ ap_snd_ap_pair _ g).

(** Over a family of sets, identifications in the total type are
    determined by their first component. *)
Definition ap_fst_cancel {A : Type} {Y : A -> Type} (sY : forall a, isSet (Y a))
  {u v : {a : A & Y a}} (h h' : u = v) (e : ap fst h = ap fst h') : h = h'.
Proof.
  refine ((pathpair_pathsplit h)^ @ _ @ pathpair_pathsplit h').
  pose (hP := fun p : fst u = fst v => sY _ (trp Y p (snd u)) (snd v)
              : isProp (PathOver Y p (snd u) (snd v))).
  refine (ap (fun w : {p : fst u = fst v & PathOver Y p (snd u) (snd v)} =>
                pathpair (fst w) (snd w))
             (path_sigma_prop hP (u := pathsplit h) (v := pathsplit h') _)).
  exact (fst_pathsplit h @ e @ (fst_pathsplit h')^).
Defined.

(** The map [F : Sub(G) → Mono(G)] of lemma [lem:SubG=MonoG]. *)
Section SubToMono.

  Context `{Funext} {G : Group} (S : SubGrp G).

  Definition subgrp_incl : Hom (subgrp_group S) G
    := @mkhom (subgrp_group S) G ((fun w => fst w); refl).

  Definition subgrp_incl_ismono : ismono subgrp_incl.
  Proof.
    refine (cancel_isInj (USym_isSet G) _). intros h h' e.
    refine (ap_fst_cancel (el_isSet (sg_X S)) h h' _).
    exact ((trans_1p _)^ @ e @ trans_1p _).
  Defined.

  Definition subgrp_to_mono : Mono G := (subgrp_group S; (subgrp_incl; subgrp_incl_ismono)).

  Definition ap_fst_tot_path_act {z w : utype (BG G)} (p : z = w) (a : el (sg_X S) z)
    : ap fst (tot_path_act (sg_X S) p a) = p.
  Proof. destruct p. exact refl. Defined.

  Definition ap_fst_act_path {z w : utype (BG G)} (p : z = w) (a : el (sg_X S) z)
    (b : el (sg_X S) w) (e : act (sg_X S) p a = b)
    : ap fst (ap (fun c => (w; c) : TotG (sg_X S)) e ⋅ tot_path_act (sg_X S) p a) = p.
  Proof. destruct e. exact (ap_fst_tot_path_act p a). Defined.

  (** Lemma [lem:E-preserves-symms], for [F(X, pt)].
    (Placed in the section of the map [F] of [lem:SubG=MonoG], whose data it uses.) *)
  Definition E_preserves_symms (g : USym G)
    : (act (sg_X S) g (sg_pt S) = sg_pt S)
      <-> Ex (fun h : USym (subgrp_group S) => g = USymf subgrp_incl h).
  Proof.
    split.
    - intro e. apply trunc.
      refine (ap (fun c => (sh G; c) : TotG (sg_X S)) e ⋅ tot_path_act _ g (sg_pt S); _).
      refine (_ @ (trans_1p _)^).
      change (g = ap fst (ap (fun c => (sh G; c) : TotG (sg_X S)) e
                          ⋅ tot_path_act (sg_X S) g (sg_pt S))).
      exact (ap_fst_act_path g _ _ e)^.
    - intro h. refine (ptrunc_rec (el_isSet _ _ _ _) _ h). intros [k e].
      refine (ap (fun r => act (sg_X S) r (sg_pt S)) (e @ trans_1p _) @ _).
      exact (act_ap_fst (sg_X S) k).
  Defined.

End SubToMono.

(** Identifications in [Mono(G)] from pointed equivalences of
    classifying types that commute with the inclusions. *)
Definition ismono_isProp `{Funext} {H G : Group} (i : Hom H G) : isProp (ismono i)
  := Pi_isProp (fun _ => isProp_isProp _).

Definition Mono_path_aux `{ua : Univalence} {G H H' : Group} (p : H = H')
  (i : Hom H G) (i' : Hom H' G) (mi : ismono i) (mi' : ismono i')
  (h : pcomp (Bf i') (fst (path_Group_pEqv p)) = Bf i)
  : ((H; (i; mi)) : Mono G) = (H'; (i'; mi')).
Proof.
  destruct p.
  refine (ap (fun w => (H; w) : Mono G) (path_sigma_prop ismono_isProp (u := (i; mi)) (v := (i'; mi')) _)).
  exact ((inc_out i)^ @ ap inc h^ @ inc_out i').
Defined.

Definition Mono_path `{ua : Univalence} {G : Group} (m m' : Mono G)
  (e : BG (fst m) ≃* BG (fst m'))
  (h : pcomp (Bf (fst (snd m'))) (fst e) = Bf (fst (snd m))) : m = m'.
Proof.
  destruct m as [[X] [i mi]], m' as [[Y] [i' mi']].
  refine (Mono_path_aux (path_Group e) i i' mi mi' _).
  exact (ap (fun e0 : BG (mkgroup X) ≃* BG (mkgroup Y) => pcomp (Bf i') (fst e0))
            (path_Group_pEqv_path_Group X Y e) @ h).
Defined.

(** Example [exa:EforSG3]: [F] sends the standard [Σ_3]-set, pointed at
    the added element, to [(Σ_2, i_3)] (with [π :≡ refl]). *)
Definition exa_EforSG3_stmt `{Univalence} : Type
  := forall (t : istrans (fun A : utype (BG (SG_S X3)) => fst A)) (m : ismono (i3 refl)),
       subgrp_to_mono (((fun A : utype (BG (SG_S X3)) => fst A); (inr triv; t))
                       : SubGrp (SG_S X3))
       = ((SG 2; (i3 refl; m)) : Mono (SG_S X3)).

(** Lemma [lem:SubG=MonoG] with exercise [xca:SubG=MonoG], and corollary
    [lem:setofsubgroups] (proved in Section 9.2: [lem_SubG_MonoG],
    [lem_setofsubgroups]). *)
Definition lem_SubG_MonoG_stmt `{Funext} : Type
  := forall G : Group, isEquiv (fun S : SubGrp G => subgrp_to_mono S).

Definition lem_setofsubgroups_stmt `{Univalence} : Type := forall G : Group, isSet (Mono G).

(** Definition [def:triv-proper-Mono]. *)
Definition SubGrp_trivial {G : Group} (S : SubGrp G) : Type := isContr (TotG (sg_X S)).

Definition SubGrp_proper {G : Group} (S : SubGrp G) : Type
  := ¬ isContr (el (sg_X S) (sh G)).

(** Remark [rem:notationsubgroup]: classical notation for subgroups
    (informal). *)

(** Example [ex:prodinclisGset]: the [G × G']-set corresponding to
    [i₁ : G → G × G'] is [princ_{G'} ∘ proj₂] (the transitivity is a
    hypothesis). *)
Definition ex_prodinclisGset_stmt `{Univalence} : Type
  := forall (G G' : Group)
            (t : istrans (fun z : utype (BG (prodG G G')) => princ G' (snd z))),
       subgrp_to_mono (((fun z : utype (BG (prodG G G')) => princ G' (snd z));
                        ((refl : el (princ G') (sh G')); t)) : SubGrp (prodG G G'))
       = ((G; (inG1 G G'; inG1_ismono G G')) : Mono (prodG G G')).

(** The proof: [a ↦ ((a, sh_{G'}), refl)] is a pointed equivalence from
    [BG] to the classifying type of the subgroup, and composed with the
    inclusion it is [Bi₁] ([Mono_path]). *)
Definition ex_prodinclisGset `{ua : Univalence} : ex_prodinclisGset_stmt.
Proof.
  intros G G' t.
  pose (X := fun z : utype (BG (prodG G G')) => princ G' (snd z)).
  pose (S := (X; ((refl : el (princ G') (sh G')); t)) : SubGrp (prodG G G')).
  pose (f := fun a : utype (BG G) => (((a; sh G') : utype (BG (prodG G G'))); refl) : TotG X).
  assert (sf : forall w : TotG X, f (fst (fst w)) = w).
  { intros [[a b] p]. change (sh G' = b) in p. destruct p. exact refl. }
  refine (Mono_path (G := prodG G G') ((G; (inG1 G G'; inG1_ismono G G')) : Mono (prodG G G'))
            (subgrp_to_mono S)
            (((f; refl); iso_to_isEquiv f (fun w : TotG X => fst (fst w)) (fun _ => refl) sf)
             : BG G ≃* BG (subgrp_group S)) refl)^.
Defined.


(** ** 5.3.3 The Lagrange construction *)
Section Lagrange.

  Context `{Funext} {G : Group} (S : SubGrp G).

  Local Notation X := (sg_X S).
  Local Notation pt0 := (sg_pt S).

  Definition cls (g : USym G) : el X (sh G) := act X g pt0.

  Definition fiber_cls_eqv (x : el X (sh G))
    : fiber cls x ≃ (((sh G; pt0) : TotG X) = (sh G; x)).
  Proof.
    refine (Eqv_comp _ (path_sigma_eqv (Y := el X))).
    refine (tot (fun g (e : x = cls g) => e⁻¹ : PathOver (el X) g pt0 x);
            tot_isEquiv _ (fun g => _)).
    refine (iso_to_isEquiv _ (fun e => e⁻¹) _ _); intro e; exact (symm_symm e).
  Defined.

  Definition back_path (x : el X (sh G)) (f : {g : USym G & act X g x = pt0})
    : ((sh G; x) : TotG X) = (sh G; pt0)
    := ap (fun c => (sh G; c) : TotG X) (snd f) ⋅ tot_path_act X (fst f) x.

  (** Construction [con:lagrange]; footnote [ft:lagrange-dep-sum] leads to
      [lagrange_dep] below. *)
  Definition lagrange (f : forall x : el X (sh G), {g : USym G & act X g x = pt0})
    : USym G ≃ (el X (sh G) × USym (subgrp_group S)).
  Proof.
    refine (Eqv_comp (Eqv_inv (sum_of_fibers cls)) _).
    refine (tot (fun x (u : fiber cls x) => back_path x (f x) ⋅ fst (fiber_cls_eqv x) u);
            tot_isEquiv _ (fun x => _)).
    exact (comp_isEquiv (snd (fiber_cls_eqv x)) (comp_l_isEquiv (back_path x (f x)))).
  Defined.

  (** Construction [cor:lagrange-dep-sum]. *)
  Definition lagrange_dep (f : forall x : el X (sh G), {g : USym G & act X g x = pt0})
    : USym G ≃ {x : el X (sh G) & ((sh G; x) : TotG X) = (sh G; x)}.
  Proof.
    refine (Eqv_comp (Eqv_inv (sum_of_fibers cls)) _).
    refine (tot (fun x (u : fiber cls x) => fst (fiber_cls_eqv x) u ⋅ back_path x (f x));
            tot_isEquiv _ (fun x => _)).
    refine (comp_isEquiv (snd (fiber_cls_eqv x)) _).
    refine (iso_to_isEquiv _ (fun q => q ⋅ (back_path x (f x))⁻¹) _ _); intro q.
    - refine ((trans_assoc _ _ _)^ @ _).
      exact (ap (fun r => q ⋅ r) (trans_Vp _) @ trans_1p q).
    - refine ((trans_assoc _ _ _)^ @ _).
      exact (ap (fun r => q ⋅ r) (trans_pV _) @ trans_1p q).
  Defined.

End Lagrange.

(** Exercise [xca:lagrange]: for a finite group [G] and a finite [G]-set,
    the underlying group [H] of [(X, pt)] is finite and
    [Card(G) = Card(X) · Card(H)].  We count with the library's [fcard]. *)
Section LagrangeCount.

  Context `{Funext} {G : Group} (S : SubGrp G).

  Local Notation X := (sg_X S).
  Local Notation pt0 := (sg_pt S).

  Definition lagrange_choice (x : el X (sh G))
    : ptrunc {g : USym G & act X g x = pt0}
    := Trunc_functor (-1) (fun r => (ap fst r; act_ap_fst X r))
         (snd (conn_of_trans X (sg_trans S)) (sh G; x) (sh G; pt0)).

  Context (FG : Finite (USym G)) (FX : Finite (el X (sh G))).

  Definition merely_lagrange : ptrunc (USym G ≃ (el X (sh G) × USym (subgrp_group S)))
    := Trunc_functor (-1) (lagrange S)
         (@finite_choice _ FX (fun x => {g : USym G & act X g x = pt0}) (fun _ => tt)
            lagrange_choice).

  Definition subgrp_Finite : Finite (USym (subgrp_group S)).
  Proof.
    refine (ptrunc_rec IsHProp_isProp _ merely_lagrange). intro e.
    pose (FP := finite_equiv' _ (Equiv_of_Eqv e) FG).
    exact (finite_equiv' _ (hfiber_fibration pt0 (fun _ => USym (subgrp_group S)))^-1
             (finite_hfiber (fun w : el X (sh G) × USym (subgrp_group S) => fst w) pt0)).
  Defined.

  Definition lagrange_card
    : fcard (USym G) = (fcard (el X (sh G)) * @fcard _ subgrp_Finite)%nat.
  Proof.
    refine (ptrunc_rec (ℕ_isSet _ _) _ merely_lagrange). intro e.
    pose (FH := subgrp_Finite).
    refine (fcard_equiv' (Equiv_of_Eqv (Eqv_comp e (binprod_prod _ _))) @ _).
    exact (fcard_prod _ _).
  Defined.

End LagrangeCount.

(** Exercises after [xca:lagrange]. *)
Section LagrangeExercises.

  Context `{Univalence}.

  (** Exercise [xca:lagrange-Z-action-Rm]: [UZ ≃ Fin m × UH_m] for the
      subgroup [(R_m, 0)] of [ℤ] (given its transitivity). *)
  Definition RmZset (k : ℕ) : GSet ZZ := RmSet k.

  Definition xca_lagrange_Z_Rm_stmt : Type
    := forall (k : ℕ) (t : istrans (RmZset k)),
         USym ZZ ≃ (Fin (S k) × USym (subgrp_group ((RmZset k; (fin_zero; t)) : SubGrp ZZ))).

  (** Iterating a loop [l] that acts on coordinates [c : FinNat(k+1) → T(a)]
      as the predecessor [fp] brings every element to [c(0)]. *)
  Section PredIter.

    Context (k : ℕ) {A : Type} (T : A -> Type) {a : A} (l : a = a)
      (c : FinNat (S k) -> T a) (d : T a -> FinNat (S k)) (cd : forall y, c (d y) = y)
      (hl : forall u, trp T l (c u) = c (fp k u)).

    Fixpoint pred_pow (i : ℕ) : a = a
      := match i with O => refl | S i' => pred_pow i' ⋅ l end.

    Definition trp_trans_T {b b' b'' : A} (q : b' = b'') (p : b = b') (y : T b)
      : trp T (q ⋅ p) y = trp T q (trp T p y).
    Proof. destruct q. exact refl. Defined.

    Definition pred_pow_zero (i : ℕ) (li : (i < S k)%nat)
      : trp T (pred_pow i) (c (i; li)) = c (zero_finnat k).
    Proof.
      revert li. induction i as [|i IH]; intro li.
      - exact (ap c (path_sigma_prop (fun x => fn_isProp_lt k x) (u := (0%nat; li))
                       (v := zero_finnat k) refl)).
      - exact (trp_trans_T _ _ _ @ ap (trp T (pred_pow i)) (hl (S i; li)) @ IH _).
    Defined.

    Definition pred_choice (y : T a) : {g : a = a & trp T g y = c (zero_finnat k)}
      := (pred_pow (fst (d y));
          ap (trp T (pred_pow (fst (d y)))) (cd y)^ @ pred_pow_zero _ (snd (d y))).

  End PredIter.

  (** The choice map for [con:lagrange]: [loop⁻ⁱ] brings [i] to [0], since
      [loop⁻¹] acts as the predecessor [fp]. *)
  Section LagrangeRm.

    Context (k : ℕ).

    Local Notation ψ := (Eqv_of_Equiv (equiv_fin_finnat (S k))).

    Definition fromNat (u : FinNat (S k)) : Fin (S k) := eqinv (snd ψ) u.

    Definition fromNat_zero : fromNat (zero_finnat k) = fin_zero
      := ap (eqinv (snd ψ)) (path_fin_to_finnat_fin_zero k)^ @ eqinv_l (snd ψ) fin_zero.

    Definition act_loop_Rm (y : Fin (S k)) : act (RmZset k) loop y = fst (finsuccEqv k) y.
    Proof.
      refine (ptw (trp_ap idmap (Rm k) loop) y @ _).
      refine (ap (fun q => trp idmap q y) (S1_rec_loop _ _ _) @ _).
      exact (ap (fun e => fst e y) (ptoe_etop (finsuccEqv k))).
    Defined.

    Definition trp_Vp_T {B : Type} (T : B -> Type) {b b' : B} (p : b = b') (z : T b)
      : trp T p⁻¹ (trp T p z) = z.
    Proof. destruct p. exact refl. Defined.

    (** If [p] acts as [finsucc], then [p⁻¹] acts as [fp]. *)
    Definition trp_V_finsucc {B : Type} (T : B -> Type) {b : B} (p : b = b)
      (Tb : T b = Fin (S k))
      (h : forall y, trp T p (trp idmap Tb^ y) = trp idmap Tb^ (fst (finsuccEqv k) y))
      (u : FinNat (S k))
      : trp T p⁻¹ (trp idmap Tb^ (fromNat u)) = trp idmap Tb^ (fromNat (fp k u)).
    Proof.
      pose (r := ap (fun v => eqinv (snd ψ) (fs k v)) (eqinv_r (snd ψ) (fp k u))
                 @ ap (eqinv (snd ψ)) (fs_fp k u)
                 : fst (finsuccEqv k) (fromNat (fp k u)) = fromNat u).
      refine (ap (trp T p⁻¹) ((ap (trp idmap Tb^) r)^ @ (h _)^) @ _).
      exact (trp_Vp_T T p _).
    Defined.

    Definition lagrange_choice_Rm (x : Fin (S k))
      : {g : USym ZZ & act (RmZset k) g x = fin_zero}.
    Proof.
      pose (w := pred_choice k (fun z => Rm k z) loop⁻¹ fromNat (fst ψ) (eqinv_l (snd ψ))
                   (trp_V_finsucc (fun z => Rm k z) loop refl act_loop_Rm) x).
      exact (fst w; snd w @ fromNat_zero).
    Defined.

  End LagrangeRm.

  Definition xca_lagrange_Z_Rm : xca_lagrange_Z_Rm_stmt
    := fun k t => lagrange ((RmZset k; (fin_zero; t)) : SubGrp ZZ) (lagrange_choice_Rm k).

  (** The hypothesis of the statement holds: [R_m] is transitive. *)
  Definition RmZset_trans (k : ℕ) : istrans (RmZset k)
    := trunc (fin_zero; fun y => trunc (fst (lagrange_choice_Rm k y); (snd (lagrange_choice_Rm k y))^)).

  (** Exercise [xca:lagrange-if-subgr-not-normal]: for the wedge group
      (assumed a connected groupoid) acting on [Fin 3] by the cyclic
      successor and the transposition [(0 1)], a choice map for the
      Lagrange construction at the point [0]. *)
  Definition fin3 (i : ℕ) (l : (i < 3)%nat) : Fin 3 := (equiv_fin_finnat 3)^-1 (i; l).

  Definition t01 : Fin 3 ≃ Fin 3
    := transpEqv (Fin_isDecSet 3) (fin3 0 _) (fin3 1 _).

  Definition X3wedge : WedgeS1S1 -> SetU
    := @Pushout_rec True S1 S1 (fun _ => base) (fun _ => base) SetU (S1_rec SetU (FinSetU 3) (path_SetU (S := FinSetU 3) (T := FinSetU 3) (finsuccEqv 2)))
         (S1_rec SetU (FinSetU 3) (path_SetU (S := FinSetU 3) (T := FinSetU 3) t01)) (fun _ => refl).

  Definition xca_lagrange_wedge_stmt : Type
    := forall (c : isConn WedgeS1S1) (g : isGrpd WedgeS1S1),
         let G := mkgroup (WedgeS1S1; (pushl base; (c; g))) in
         forall x : Fin 3, {h : USym G & act (X3wedge : GSet G) h x = fin3 0 _}.

  (** As for [R_m]: [pushl(loop)] acts as the successor, so its inverse
      powers bring every element to [0]. *)
  Definition act_wedge_loop (y : Fin 3)
    : trp (fun w => fst (X3wedge w)) (ap pushl loop) y = fst (finsuccEqv 2) y.
  Proof.
    refine ((ptw (trp_ap (fun w => fst (X3wedge w)) pushl loop) y)^ @ _).
    refine (ptw (trp_ap idmap (fun z => fst (X3wedge (pushl z))) loop) y @ _).
    refine (ap (fun q => trp idmap q y) (ap_compose (fun z => X3wedge (pushl z)) fst loop) @ _).
    refine (ap (fun q : FinSetU 3 = FinSetU 3 => trp idmap (ap fst q) y) (S1_rec_loop _ _ _) @ _).
    refine (ap (fun q : Fin 3 = Fin 3 => trp idmap q y)
              (ap_fst_sigma_prop (fun X => isSet_isProp X) (u := FinSetU 3) (v := FinSetU 3)
                 (etop (finsuccEqv 2))) @ _).
    exact (ap (fun e => fst e y) (ptoe_etop (finsuccEqv 2))).
  Defined.

  Definition fromNat_fin3 (l : (0 < 3)%nat) : fromNat 2 (zero_finnat 2) = fin3 0 l.
  Proof.
    refine (ap (fromNat 2) (path_sigma_prop (fun x => fn_isProp_lt 2 x) (u := zero_finnat 2)
                              (v := (0%nat; l)) refl) @ _).
    refine (ap (eqinv (snd (Eqv_of_Equiv (equiv_fin_finnat 3)))) (eisretr _ (0%nat; l))^ @ _).
    exact (eqinv_l (snd (Eqv_of_Equiv (equiv_fin_finnat 3))) _).
  Defined.

  Definition xca_lagrange_wedge : xca_lagrange_wedge_stmt.
  Proof.
    intros c g G x.
    pose (w := pred_choice 2 (fun w => fst (X3wedge w)) (ap pushl loop)⁻¹ (fromNat 2)
                 (fst (Eqv_of_Equiv (equiv_fin_finnat 3)))
                 (eqinv_l (snd (Eqv_of_Equiv (equiv_fin_finnat 3))))
                 (trp_V_finsucc 2 (fun w => fst (X3wedge w)) (ap pushl loop) refl act_wedge_loop) x).
    exact (fst w; snd w @ fromNat_fin3 _).
  Defined.

End LagrangeExercises.
