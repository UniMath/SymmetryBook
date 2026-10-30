(** * Section 4.4 Homomorphisms

    Part of Chapter 4 ([group.tex]); see [Group.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:grouphomomorphism]: [Hom G H :≡ Copy(BG →* BH)] with
      constructor [mkhom] and destructor [Bf] (the book's [B]).
    - Definition [def:loops-map]: [loops_fun k] ([Ωk(p) :≡ k_pt⁻¹ · k(p) ·
      k_pt]) and the pointed [loops_map k]; remark [rem:loops-map]
      ([loops_fun_refl]); definition [def:USym-hom] ([USymf]).
    - Lemma [lem:grouphomomaxioms] ([USymf_unit], [USymf_inv],
      [USymf_comp]), by induction on the pointing path.
    - Definitions [def:groupisomorphism] ([isIso], [Iso]),
      [def:identity-group-homomorphism] ([idG], [idG_isIso]) and
      [def:group-homomorphism-composition] ([compG]).
    - Remark [remark:groupsasunivalenttype]: [(G = H) ≃ Iso(G,H)]
      ([path_Group_Iso_eqv]).
    - Lemma [lem:hom-is-set], in the general form of footnote
      [ft:ptd-decr-h-lev] for [k = 1, n = 0]: [X →* Y] is a set when [X]
      is connected and [Y] a groupoid ([pmap_isSet], [Hom_isSet],
      [Iso_isSet]).  The proof uses the characterization [ptw_star] of
      identifications of pointed maps from Section 2.21.
    - Exercise [xca:typegroupisgroupoid] from Section 4.2: [Group_isGrpd].
    - Example [ex:groups-morphisms]: (1) [sum_hom] and [prod_hom] for
      [_ ⨿ T] and [_ × T] on [Σ_S]; (2) the unique homomorphisms to and
      from the trivial group ([Hom_to_TG_isContr], [Hom_from_TG_isContr],
      from [pmap_to_contr_isContr], [pmap_from_contr_isContr]); (3)
      projections and inclusions [prG1], [prG2], [inG1], [inG2].
    - Construction [def:loops-compose] ([loops_fun_pcomp], [loops_pcomp])
      and corollary [cor:USym-compose] ([USym_compose]).
    - Example [ex:Zinitial]: [evG], which is [evp] of Section 3.1, is an
      equivalence; [Hom_ZZ_eqv : Hom(ℤ, G) ≃ UG]; [veG] with
      [veG(g)(base) ≡ sh_G] and pointing path [refl].
    - Lemma [lem:Znatural] ([Znatural]).
    - Exercise [xca:BGtotype] ([BGtotype_12], [BGtotype_23] (by [refl]),
      [BGtotype_34], via [to_comp]).
    - Example [exa:conj-concrete]: [regroup G y :≡ mkgroup(BG_÷, y)], the
      isomorphism [conj_hom G p], and its action on symmetries is
      conjugation [g ↦ p g p⁻¹] ([conj_hom_USym]).
    - Definition [def:inner-autos]: [Binn : BG →* BAut(G)] ([BAutG] is the
      component of [G] in [Group], pointed at [G]); the group [Aut(G)],
      in a larger universe, is [AutGrp] of Section 9.7.  The pointing path is [(inc_out G)⁻¹] rather than [refl]:
      [Copy] has no definitional eta rule, so [mkgroup(BG_÷, sh_G)] is
      not judgmentally [G].

    - Example [ex:groups-morphisms](1) for [Σ_m → Σ_{m+n}] and
      [Σ_m → Σ_{mn}] ([SG_sum_hom], [SG_prod_hom], given the
      identifications of finite sets), and (4) ([mod_hom], with
      [forget_cyc_hom] and [Rm_hom]).  The equivalences
      [Fin(m) ⨿ Fin(n) ≃ Fin(m+n)] and [Fin(m) × Fin(n) ≃ Fin(mn)]
      used there ([fin_sum_eqv], [fin_prod_eqv], by induction).
    - The remark that [id_{Σ_3} ≠ τ̃] in [Hom(Σ_3, Σ_3)] ([id_ne_tau],
      with [tau3]): otherwise [τ] would commute with the transposition
      [σ] of the first two elements ([sigma3]); symmetries act on
      [Fin 3] by [Fpath].
    - The factorization of [R_m] through [mod_m] ([mod_factor]): both
      maps [S1 → BΣ_m] agree on [base] by definition and on [loop]
      after projecting to [U] ([mod_factor_loop], [S1_htpy]).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Types.Sum Truncations.Core Spaces.Circle Spaces.Finite.Fin.
From SymmetryBook Require Export Group.S03_AbstractGroups.

Local Open Scope uf_scope.

(** ** 4.4 Homomorphisms *)

(** Remark [rem:homom-eqs]: [ap k] of a pointed map [k : BG →* BH]
    preserves unit, inverses and composition; made precise in
    [lem:grouphomomaxioms] below. *)

(** Definition [def:grouphomomorphism]: [Hom(G,H) :≡ Copy(BG →* BH)],
    with constructor [mkhom] and destructor [Bf]. *)
Definition Hom (G H : Group) : Type := Copy (BG G →* BG H).

Definition mkhom {G H : Group} (k : BG G →* BG H) : Hom G H := inc k.

Definition Bf {G H : Group} (f : Hom G H) : BG G →* BG H := out f.

(** Definition [def:loops-map]: [Ωk(p) :≡ k_pt⁻¹ · k(p) · k_pt], pointed by
    the inverse law. *)
Definition loops_fun {X Y : Ustar} (k : X →* Y) (p : pt X = pt X) : pt Y = pt Y
  := (snd k)⁻¹ ⋅ (ap (fst k) p ⋅ snd k).

Definition loops_map {X Y : Ustar} (k : X →* Y) : loops X →* loops Y
  := (loops_fun k; (trans_pV (snd k))⁻¹).

(** Remark [rem:loops-map]. *)
Definition loops_fun_refl {X Y : Ustar} (k0 : utype X -> utype Y)
  (p : pt X = pt X) : loops_fun ((k0; refl) : X →* (utype Y; k0 (pt X))) p = ap k0 p
  := trans_1p _.

(** Definition [def:USym-hom]. *)
Definition USymf {G H : Group} (f : Hom G H) : USym G -> USym H := loops_fun (Bf f).

(** Lemma [lem:grouphomomaxioms], by induction on the pointing path. *)
Section HomAxioms.

  Context {A B : Type} (x : A) (k0 : A -> B).

  Definition loops_fun_unit (y : B) (kp : y = k0 x)
    : loops_fun ((k0; kp) : (A; x) →* (B; y)) refl = refl
    := trans_pV kp.

  Definition loops_fun_inv (y : B) (kp : y = k0 x) (g : x = x)
    : loops_fun ((k0; kp) : (A; x) →* (B; y)) g⁻¹
      = (loops_fun ((k0; kp) : (A; x) →* (B; y)) g)⁻¹.
  Proof.
    revert y kp. refine (paths_ind_r _ _ _).
    exact (trans_1p _ @ ap_symm k0 g @ ap symm (trans_1p _)^).
  Defined.

  Definition loops_fun_comp (y : B) (kp : y = k0 x) (g g' : x = x)
    : loops_fun ((k0; kp) : (A; x) →* (B; y)) (g' ⋅ g)
      = loops_fun ((k0; kp) : (A; x) →* (B; y)) g'
        ⋅ loops_fun ((k0; kp) : (A; x) →* (B; y)) g.
  Proof.
    revert y kp. refine (paths_ind_r _ _ _).
    exact (trans_1p _ @ ap_trans k0 g g'
           @ ap011 (fun a b => a ⋅ b) (trans_1p _)^ (trans_1p _)^).
  Defined.

End HomAxioms.

(** Equation [gp-homo-unit]. *)
Definition USymf_unit {G H : Group} (f : Hom G H) : USymf f refl = refl
  := loops_fun_unit (sh G) (fst (Bf f)) (sh H) (snd (Bf f)).

(** Equation [gp-homo-inv]. *)
Definition USymf_inv {G H : Group} (f : Hom G H) (g : USym G)
  : USymf f g⁻¹ = (USymf f g)⁻¹
  := loops_fun_inv (sh G) (fst (Bf f)) (sh H) (snd (Bf f)) g.

(** Equation [gp-homo-comp]. *)
Definition USymf_comp {G H : Group} (f : Hom G H) (g g' : USym G)
  : USymf f (g' ⋅ g) = USymf f g' ⋅ USymf f g
  := loops_fun_comp (sh G) (fst (Bf f)) (sh H) (snd (Bf f)) g g'.

(** Definition [def:groupisomorphism]. *)
Definition isIso {G H : Group} (f : Hom G H) : Type := isEquiv (fst (Bf f)).

Definition Iso (G H : Group) : Type := {f : Hom G H & isIso f}.

(** Definition [def:identity-group-homomorphism]. *)
Definition idG (G : Group) : Hom G G := mkhom (pid (BG G)).

Definition idG_isIso (G : Group) : isIso (idG G) := id_isEquiv _.

(** Remark [remark:groupsasunivalenttype]: [(G = H) ≃ Iso(G,H)]. *)
Definition Iso_pEqv (G H : Group) : Iso G H ≃ (BG G ≃* BG H).
Proof.
  refine (mkEqv (fun i : Iso G H => ((Bf (fst i); snd i) : BG G ≃* BG H))
                (fun e => ((mkhom (fst e); snd e) : Iso G H)) _ (fun e => refl)).
  intros [[k] t]. exact refl.
Defined.

Definition path_Group_Iso_eqv `{Univalence} (G K : Group) : (G = K) ≃ Iso G K.
Proof.
  refine (Eqv_comp _ (Eqv_inv (Iso_pEqv G K))).
  refine (Eqv_comp _ (path_to_pEqv; path_to_pEqv_isEquiv (BG G) (BG K))).
  refine (Eqv_comp _ (UUscone_paths_eqv (B G) (B K))).
  exact (Eqv_comp (Eqv_of_Equiv (equiv_concat_lr (inc_out G) (inc_out K)^))
           (path_inc_eqv (B G) (B K))).
Defined.

(** Definition [def:group-homomorphism-composition]. *)
Definition compG {G G' G'' : Group} (f' : Hom G' G'') (f : Hom G G') : Hom G G''
  := mkhom (pcomp (Bf f') (Bf f)).

(** Remark [rem:Bf-convention]: to define [φ : ∏_{f:Hom(G,H)} T(f)] it
    suffices to consider [f ≡ mkhom(Bf)] (informal convention). *)

(** Lemma [lem:hom-is-set], in the general form of footnote
    [ft:ptd-decr-h-lev]: [X →* Y] is a set when [X] is connected and [Y]
    is a groupoid. *)
Definition pmap_isSet `{Funext} {X Y : Ustar} (cX : isConn (utype X))
  (gY : isGrpd (utype Y)) : isSet (X →* Y).
Proof.
  intros f g.
  refine (isProp_Eqv (Eqv_inv (ptw_star f g)) _).
  intros [h e] [j e'].
  refine (path_sigma_prop (fun _ => gY _ _ _ _) _); cbn.
  apply ptw_inv. intro t.
  refine (ptrunc_rec (gY _ _ _ _) _ (snd cX (pt X) t)). intro q. destruct q.
  refine (cancelL (snd f) _ _ _).
  exact ((trans_is_concat _ _)^ @ e @ e'^ @ trans_is_concat _ _).
Defined.

Definition Hom_isSet `{Funext} (G H : Group) : isSet (Hom G H)
  := is_ntype_Eqv 0 (Eqv_inv (Copy_eqv _)) (pmap_isSet (BG_isConn G) (BG_isGrpd H)).

Definition Iso_isSet `{Funext} (G H : Group) : isSet (Iso G H)
  := Sigma_ntype 0 (Hom_isSet G H) (fun f => prop_ntype 0 _ (isEquiv_isProp _)).

(** Exercise [xca:typegroupisgroupoid] (postponed from Section 4.2):
    identity types of groups are sets, so [Group] is a groupoid. *)
Definition Group_isGrpd `{Univalence} : isGrpd Group
  := fun G K => is_ntype_Eqv 0 (Eqv_inv (path_Group_Iso_eqv G K)) (Iso_isSet G K).

(** ** Example [ex:groups-morphisms] *)

(** (2) There is a unique homomorphism to and from the trivial group;
    more generally [X →* Y] is contractible when [Y] or [X] is. *)
Definition pmap_to_contr_isContr `{Funext} {X Y : Ustar} (cY : isContr (utype Y))
  : isContr (X →* Y).
Proof.
  refine (isProp_inhabited_isContr _ ((fun _ => pt Y); refl)).
  intros f g.
  refine (eqinv (snd (ptw_star f g)) ((fun x => isContr_isProp' cY _ _); _)).
  exact (prop_is_set (isContr_isProp' cY) _ _ _ _).
Defined.

Definition pmap_from_contr_isContr `{Funext} {X Y : Ustar} (cX : isContr (utype X))
  : isContr (X →* Y).
Proof.
  refine (iso_to_isEquiv (fun f : utype X -> utype Y => f (pt X))
            (fun y => @cst (utype X) (utype Y) y) _ _ (pt Y)).
  - intro f. apply ptw_inv. intro x. exact (ap f (isContr_isProp' cX (pt X) x)).
  - intro y. exact refl.
Defined.

Definition Hom_to_TG_isContr `{Univalence} (G : Group) : isContr (Hom G TG)
  := isContr_Eqv (Eqv_inv (Copy_eqv _)) (pmap_to_contr_isContr TG_contr).

Definition Hom_from_TG_isContr `{Univalence} (G : Group) : isContr (Hom TG G)
  := isContr_Eqv (Eqv_inv (Copy_eqv _)) (pmap_from_contr_isContr TG_contr).

(** (3) Projections and inclusions for [G × H]. *)
Section ProdHoms.

  Context `{Funext} (G K : Group).

  Definition prG1 : Hom (prodG G K) G
    := @mkhom (prodG G K) G ((fun z => fst z); refl).

  Definition prG2 : Hom (prodG G K) K
    := @mkhom (prodG G K) K ((fun z => snd z); refl).

  Definition inG1 : Hom G (prodG G K)
    := @mkhom G (prodG G K) ((fun z => (z; sh K) : utype (BG (prodG G K))); refl).

  Definition inG2 : Hom K (prodG G K)
    := @mkhom K (prodG G K) ((fun z => (sh G; z) : utype (BG (prodG G K))); refl).

End ProdHoms.

(** (1) [_ ⨿ T : Σ_S → Σ_{S ⨿ T}] and [_ × T : Σ_S → Σ_{S × T}], pointed by
    [refl]. *)
Section PermHoms.

  Context `{Univalence} (S T : SetU).

  Definition sumSetU (X : SetU) : SetU := (fst X ⨿ fst T; sum_isSet (snd X) (snd T)).

  Definition prodSetU (X : SetU) : SetU
    := (fst X × fst T; Sigma_ntype 0 (snd X) (fun _ => snd T)).

  Definition comp_map (F : SetU -> SetU) (X : component SetU S) : component SetU (F S)
    := (F (fst X); ptrunc_rec ptrunc_isProp (fun p => trunc (ap F p)) (snd X)).

  Definition sum_hom : Hom (SG_S S) (SG_S (sumSetU S))
    := @mkhom (SG_S S) (SG_S (sumSetU S)) (comp_map sumSetU; refl).

  Definition prod_hom : Hom (SG_S S) (SG_S (prodSetU S))
    := @mkhom (SG_S S) (SG_S (prodSetU S)) (comp_map prodSetU; refl).

End PermHoms.

(** Identifications of sets from equivalences. *)
Definition path_SetU0 `{Univalence} {S T : SetU} (e : fst S ≃ fst T) : S = T
  := path_sigma_prop (fun A => isSet_isProp A) (u := S) (v := T) (etop e).

(** The homomorphisms [Σ_m → Σ_{m+n}] and [Σ_m → Σ_{mn}] of example
    [ex:groups-morphisms](1), from identifications
    [Fin(m+n) = Fin(m) ⨿ Fin(n)] and [Fin(mn) = Fin(m) × Fin(n)]; these
    equivalences are [fin_sum_eqv] and [fin_prod_eqv] below. *)
Definition SG_sum_hom `{Univalence} (m n : ℕ)
  (e : fst (sumSetU (FinSetU n) (FinSetU m)) ≃ fst (FinSetU (add m n)))
  : Hom (SG m) (SG (add m n))
  := trp (fun S => Hom (SG m) (SG_S S)) (path_SetU0 (S := sumSetU (FinSetU n) (FinSetU m)) (T := FinSetU (add m n)) e)
       (sum_hom (FinSetU m) (FinSetU n)).

Definition SG_prod_hom `{Univalence} (m n : ℕ)
  (e : fst (prodSetU (FinSetU n) (FinSetU m)) ≃ fst (FinSetU (mul m n)))
  : Hom (SG m) (SG (mul m n))
  := trp (fun S => Hom (SG m) (SG_S S)) (path_SetU0 (S := prodSetU (FinSetU n) (FinSetU m)) (T := FinSetU (mul m n)) e)
       (prod_hom (FinSetU m) (FinSetU n)).

Definition fin_sum_eqv_stmt : Type := forall m n : ℕ, Fin m ⨿ Fin n ≃ Fin (add m n).

Definition fin_prod_eqv_stmt : Type := forall m n : ℕ, Fin m × Fin n ≃ Fin (mul m n).

(** Both by induction, using [Fin (S k) ≡ Fin k ⨿ 𝟙], [add m (S n) ≡
    S (add m n)] and [mul (S m) n ≡ add (mul m n) n]. *)
Definition sum_eqv {A A' B B' : Type} (e1 : A ≃ A') (e2 : B ≃ B') : A ⨿ B ≃ A' ⨿ B'
  := mkEqv (fun s => match s with inl a => inl (fst e1 a) | inr b => inr (fst e2 b) end)
           (fun s => match s with inl a => inl (eqinv (snd e1) a) | inr b => inr (eqinv (snd e2) b) end)
           (fun s => match s with inl a => ap inl (eqinv_l (snd e1) a)
                               | inr b => ap inr (eqinv_l (snd e2) b) end)
           (fun s => match s with inl a => ap inl (eqinv_r (snd e1) a)
                               | inr b => ap inr (eqinv_r (snd e2) b) end).

Fixpoint fin_sum_eqv (m n : ℕ) : Fin m ⨿ Fin n ≃ Fin (add m n)
  := match n with
     | O => mkEqv (fun s : Fin m ⨿ Empty => match s with inl a => a | inr e => match e with end end)
                  (fun a : Fin m => inl a)
                  (fun s : Fin m ⨿ Empty => match s with inl a => refl | inr e => match e with end end)
                  (fun a => refl)
     | S n' => Eqv_comp
                 (mkEqv (fun s : Fin m ⨿ (Fin n' ⨿ True) =>
                           match s with inl a => inl (inl a) | inr (inl b) => inl (inr b)
                                      | inr (inr t) => inr t end)
                        (fun s => match s with inl (inl a) => inl a | inl (inr b) => inr (inl b)
                                             | inr t => inr (inr t) end)
                        (fun s => match s with inl a => refl | inr (inl b) => refl
                                             | inr (inr t) => refl end)
                        (fun s => match s with inl (inl a) => refl | inl (inr b) => refl
                                             | inr t => refl end))
                 (sum_eqv (fin_sum_eqv m n') (idEqv True))
     end.

Fixpoint fin_prod_eqv (m n : ℕ) : Fin m × Fin n ≃ Fin (mul m n)
  := match m with
     | O => mkEqv (fun w : Empty × Fin n => match fst w with end) (fun e : Empty => match e with end)
                  (fun w : Empty × Fin n => match fst w with end) (fun e : Empty => match e with end)
     | S m' => Eqv_comp
                 (mkEqv (fun w : (Fin m' ⨿ True) × Fin n =>
                           match fst w with inl a => inl (a; snd w) | inr _ => inr (snd w) end)
                        (fun s => match s with inl w => (inl (fst w); snd w) | inr b => (inr tt; b) end)
                        (fun w => match w with
                                  | (inl a; b) => refl
                                  | (inr t; b) => match t with tt => refl end
                                  end)
                        (fun s => match s with inl w => refl | inr b => refl end))
                 (Eqv_comp (sum_eqv (fin_prod_eqv m' n) (idEqv (Fin n)))
                           (fin_sum_eqv (mul m' n) n))
     end.

Definition fin_sum_eqv_proof : fin_sum_eqv_stmt := fin_sum_eqv.

Definition fin_prod_eqv_proof : fin_prod_eqv_stmt := fin_prod_eqv.

(** Example [ex:groups-morphisms](4), item [it:mod_m]: [mod_m : ℤ → C_m], with
    [Bmod_m(base) :≡ (Fin m, zs)] and [Bmod_m(loop) := (zs, !)], pointed
    by [refl]; and the homomorphism [C_m → Σ_m] forgetting the cycle
    structure.  [R_m : ℤ → Σ_m] factors as their composite
    ([mod_factor] below). *)
Definition mod_hom `{Univalence} (k : ℕ) : Hom ZZ (CG k)
  := mkhom ((S1_rec (utype (BG (CG k))) (sh (CG k))
               (path_sigma_prop (fun _ => ptrunc_isProp) (u := sh (CG k)) (v := sh (CG k))
                  (cyc_path (Fincyc k) (Fincyc k) (endo_path (finsuccEqv k) refl)));
             refl) : BG ZZ →* BG (CG k)).

Definition forget_cyc_hom `{Univalence} (k : ℕ) : Hom (CG k) (SG (S k))
  := mkhom (((fun w : component Cyc (Fincyc k) =>
                (fst (fst w); ptrunc_rec ptrunc_isProp (fun p => trunc (ap fst p)) (snd w))
                : component SetU (FinSetU (S k)));
             refl) : BG (CG k) →* BG (SG (S k))).

Definition Rm_hom `{Univalence} (k : ℕ) : Hom ZZ (SG (S k))
  := mkhom (((fun z => (RmSet k z; ptrunc_rec ptrunc_isProp
                                     (fun p : base = z => trunc (ap (RmSet k) p)) (S1_base_paths z))
                       : component SetU (FinSetU (S k)));
             refl) : BG ZZ →* BG (SG (S k))).

Definition mod_factor_stmt `{Univalence} : Type
  := forall k : ℕ, compG (forget_cyc_hom k) (mod_hom k) = Rm_hom k.

(** The proof: both maps [S1 → BΣ_m] agree on [base] by definition, and
    on [loop] after projecting to [U], where both give [etop(zs)]
    ([S1_htpy]); identifications in a component of [SetU] are determined
    by their underlying identifications of types. *)
Section ModFactor.

  Context `{ua : Univalence} (k : ℕ).

  Definition SetU_comp_loop_inj {S : SetU} {c c' : component SetU S} (α β : c = c')
    (e : ap fst (ap fst α) = ap fst (ap fst β)) : α = β.
  Proof.
    apply (isInj_cancel (isEquiv_isInj
             (isInj_ap_isEquiv (fst_isInj (fun _ => ptrunc_isProp)) c c'))).
    apply (isInj_cancel (isEquiv_isInj
             (isInj_ap_isEquiv (fst_isInj (fun X => isSet_isProp X)) (fst c) (fst c')))).
    exact e.
  Defined.

  Definition ap_fst_fst_S1 {S : SetU} (h : S1 -> component SetU S)
    : ap fst (ap fst (ap h loop)) = ap (fun z => fst (fst (h z))) loop
    := (ap (ap fst) (ap_compose h fst loop)^ @ (ap_compose (fun z => fst (h z)) fst loop)^).

  Local Notation f0 := (fst (Bf (compG (forget_cyc_hom k) (mod_hom k)))).
  Local Notation g0 := (fst (Bf (Rm_hom k))).

  Definition mod_factor_loop : ap f0 loop = ap g0 loop.
  Proof.
    apply SetU_comp_loop_inj.
    refine (ap_fst_fst_S1 f0 @ _ @ (ap_fst_fst_S1 g0)^).
    refine (ap_compose _ (fun c : component Cyc (Fincyc k) => fst (fst (fst c))) loop @ _).
    refine (ap (ap (fun c : component Cyc (Fincyc k) => fst (fst (fst c)))) (S1_rec_loop _ _ _) @ _).
    refine (ap_compose fst (fun c : Cyc => fst (fst c)) _ @ _).
    refine (ap (ap (fun c : Cyc => fst (fst c))) (ap_fst_pathpair _ _) @ _).
    refine (ap_carrier_cyc_path _ _ _ @ _).
    refine (ap_fst_endo_path _ _ @ _).
    exact (S1_rec_loop _ _ _)^.
  Defined.

  Definition mod_factor_htpy : forall z, f0 z = g0 z
    := S1_htpy (f := f0) (g := g0) refl (mod_factor_loop @ (trans_1p _)^).

  Definition trp_pointing {A B : Type} {a : A} {b : B} {h h' : A -> B} (P : h = h')
    (r : b = h a) : trp (fun k0 : A -> B => b = k0 a) P r = ptw P a ⋅ r.
  Proof. destruct P. exact refl. Defined.

End ModFactor.

Definition mod_factor `{ua : Univalence} : mod_factor_stmt.
Proof.
  intro k.
  refine (ap mkhom (pathpair (ptw_inv (mod_factor_htpy k)) _)).
  refine (trp_pointing (A := utype (BG ZZ)) (B := utype (BG (SG (S k)))) (a := base)
            (ptw_inv (mod_factor_htpy k)) _ @ _).
  exact (ap (fun r => r ⋅ refl) (ap (fun H => H base) (eqinv_r (funext _ _) (mod_factor_htpy k)))).
Defined.

(** The remark that [id_{Σ_3} ≠ τ̃ :≡ (id, τ)] in [Hom(Σ_3, Σ_3)], for
    a transposition [τ]. *)
Definition tau3 `{Univalence} : sh (SG 3) = sh (SG 3)
  := path_sigma_prop (fun _ => ptrunc_isProp) (u := sh (SG 3)) (v := sh (SG 3))
       (path_SetU0 (S := FinSetU 3) (T := FinSetU 3) (Eqv_of_Equiv (fin_transpose_last_two 1))).

Definition id_ne_tau_stmt `{Univalence} : Type
  := idG (SG 3) ≠ mkhom ((idmap; tau3) : BG (SG 3) →* BG (SG 3)).

(** The proof: equality would make [τ] commute with every symmetry, but
    it does not commute with the transposition [σ] of the first two
    elements.  Symmetries of [Σ_3] act on [Fin 3] by [Fpath]. *)
Section IdNeTau.

  Context `{ua : Univalence}.

  Definition Fpath {c c' : component SetU (FinSetU 3)} (q : c = c') : fst (fst c) -> fst (fst c')
    := ptoe (ap fst (ap fst q)).

  Definition Fpath_trans {c c' c'' : component SetU (FinSetU 3)} (p : c = c') (q : c' = c'')
    (x : fst (fst c)) : Fpath (q ⋅ p) x = Fpath q (Fpath p x).
  Proof. destruct q, p. exact refl. Defined.

  Definition Fpath_V {c c' : component SetU (FinSetU 3)} (p : c = c') (x : fst (fst c))
    : Fpath p⁻¹ (Fpath p x) = x.
  Proof. destruct p. exact refl. Defined.

  Definition sym3 (e : Fin 3 ≃ Fin 3) : sh (SG 3) = sh (SG 3)
    := path_sigma_prop (fun _ => ptrunc_isProp) (u := sh (SG 3)) (v := sh (SG 3))
         (path_SetU0 (S := FinSetU 3) (T := FinSetU 3) e).

  Definition Fpath_sym3 (e : Fin 3 ≃ Fin 3) (x : Fin 3) : Fpath (sym3 e) x = fst e x.
  Proof.
    unfold Fpath, sym3.
    refine (ap (fun q : FinSetU 3 = FinSetU 3 => ptoe (ap fst q) x)
              (ap_fst_pathpair _ _) @ _).
    refine (ap (fun q : Fin 3 = Fin 3 => ptoe q x) (ap_fst_pathpair _ _) @ _).
    exact (ap (fun f => fst f x) (ptoe_etop e)).
  Defined.

  Definition sigma3 : Fin 3 ≃ Fin 3
    := Eqv_of_Equiv (equiv_functor_sum' (fin_transpose_last_two 0) (equiv_idmap Unit)).

  Definition id_ne_tau : id_ne_tau_stmt.
  Proof.
    intro e.
    pose (s := sym3 sigma3).
    pose (r := ap (fun h : Hom (SG 3) (SG 3) =>
                     Fpath (c := sh (SG 3)) (c' := sh (SG 3)) (USymf h s) (inl (inl (inr tt)))) e).
    cbn beta in r. unfold USymf, loops_fun in r. cbn in r.
    assert (L : Fpath (refl⁻¹ ⋅ (ap idmap s ⋅ refl)) (inl (inl (inr tt))) = inl (inr tt)).
    { refine (ap (fun q : sh (SG 3) = sh (SG 3) => Fpath q (inl (inl (inr tt))))
                (trans_1p _ @ ap_idmap s) @ _).
      exact (Fpath_sym3 sigma3 _). }
    assert (R : Fpath (tau3⁻¹ ⋅ (ap idmap s ⋅ tau3)) (inl (inl (inr tt))) = inr tt).
    { refine (Fpath_trans _ _ _ @ _).
      refine (ap (Fpath tau3⁻¹) (Fpath_trans _ _ _ @ _) @ _).
      { refine (ap (Fpath (ap idmap s))
                  (Fpath_sym3 (Eqv_of_Equiv (fin_transpose_last_two 1)) (inl (inl (inr tt)))) @ _).
        refine (ap (fun q : sh (SG 3) = sh (SG 3) => Fpath q (inl (inl (inr tt)))) (ap_idmap s) @ _).
        exact (Fpath_sym3 sigma3 (inl (inl (inr tt)))
               @ (Fpath_sym3 (Eqv_of_Equiv (fin_transpose_last_two 1)) (inr tt))^). }
      exact (Fpath_V _ _). }
    pose (w := L^ @ r @ R).
    exact (trp (fun x : Fin 3 => match x with inl _ => Unit | inr _ => Empty end) w tt).
  Defined.

End IdNeTau.

(** Construction [def:loops-compose], pointwise, by induction on the
    pointing paths. *)
Definition loops_fun_pcomp {X Y Z : Ustar} (g : Y →* Z) (f : X →* Y)
  (p : pt X = pt X) : loops_fun (pcomp g f) p = loops_fun g (loops_fun f p).
Proof.
  destruct X as [A x], Y as [B y], Z as [C z], f as [f0 fp], g as [g0 gp].
  cbn in *. revert z gp. refine (paths_ind_r _ _ _).
  revert y fp g0. refine (paths_ind_r _ _ _). intro g0.
  unfold loops_fun, pcomp; cbn.
  refine (trans_1p _ @ _ @ (trans_1p _ @ ap (ap g0) (trans_1p _))^).
  exact (ap_compose f0 g0 p).
Defined.

Definition loops_pcomp `{Funext} {X Y Z : Ustar} (g : Y →* Z) (f : X →* Y)
  : loops_fun (pcomp g f) = loops_fun g ∘ loops_fun f
  := ptw_inv (loops_fun_pcomp g f).

(** Corollary [cor:USym-compose]. *)
Definition USym_compose `{Funext} {G H K : Group} (φ : Hom G H) (ψ : Hom H K)
  : USymf (compG ψ φ) = USymf ψ ∘ USymf φ
  := loops_pcomp (Bf ψ) (Bf φ).

(** Example [ex:Zinitial]: [ev : (S1, base) →* BG ≃ UG], [ev(f) :≡ Ωf(loop)];
    this is [evp] of Section 3.1, and [Hom(ℤ, G) ≃ UG]. *)
Section ZInitial.

  Context `{Univalence}.

  Definition evG (G : Group) (k : BG ZZ →* BG G) : USym G := loops_fun k loop.

  Definition evG_is_evp (G : Group) (k : BG ZZ →* BG G) : evG G k = evp (sh G) k
    := refl.

  Definition evG_isEquiv (G : Group) : isEquiv (evG G) := evp_isEquiv (sh G).

  Definition Hom_ZZ_eqv (G : Group) : Hom ZZ G ≃ USym G
    := Eqv_comp (Copy_eqv _) (evG G; evG_isEquiv G).

  (** [ve(g)(base) ≡ sh_G], pointed by [refl]. *)
  Definition veG (G : Group) (g : USym G) : Hom ZZ G
    := @mkhom ZZ G (evp_inv (sh G) g).

  Definition veG_base (G : Group) (g : USym G) : fst (Bf (veG G g)) base = sh G := refl.

  Definition veG_pt (G : Group) (g : USym G) : snd (Bf (veG G g)) = refl := refl.

  (** Lemma [lem:Znatural]. *)
  Definition Znatural (G K : Group) (f : Hom G K) (k : Hom ZZ G)
    : fst (Hom_ZZ_eqv K) (compG f k) = USymf f (fst (Hom_ZZ_eqv G) k).
  Proof.
    destruct k as [k]. exact (loops_fun_pcomp (Bf f) k loop).
  Defined.

End ZInitial.

(** Exercise [xca:BGtotype]. *)
Section BGtoType.

  Context `{Funext} (G : Group) {A : Type} (gA : isGrpd A).

  Local Notation X := (utype (BG G)).

  (** (1) ≃ (2), by exercise [xca:freemaps]. *)
  Definition BGtotype_12 : (X -> A) ≃ {a : A & {f : X -> A & a = f (sh G)}}
    := Eqv_inv (freemaps (BG G) A).

  (** (2) is (3) by definition of pointed maps. *)
  Definition BGtotype_23
    : {a : A & {f : X -> A & a = f (sh G)}} = {a : A & BG G →* (A; a)}
    := refl.

  Definition ap_fst_path_sigma_prop {P : A -> Type} (hP : forall a, isProp (P a))
    {u v : {a : A & P a}} (e : fst u = fst v)
    : ap fst (path_sigma_prop hP e) = e
    := ap_fst_pathpair e _.

  (** (3) ≃ (4): pointed maps into [(A, a)] land in the component of [a]. *)
  Definition to_comp (a : A) (k : BG G →* (A; a)) : BG G →* BG (AutG gA a)
    := ((fun x => (fst k x; ptrunc_rec ptrunc_isProp
                              (fun q : sh G = x => trunc (ap (fst k) q ⋅ snd k))
                              (snd (BG_isConn G) (sh G) x)) : component A a);
        @path_sigma_prop A (fun x => ptrunc (a = x)) (fun _ => ptrunc_isProp)
          (a; trunc refl) (fst k (sh G); _) (snd k)).

  Definition from_comp (a : A) (m : BG G →* BG (AutG gA a)) : BG G →* (A; a)
    := ((fun x => fst (fst m x)); ap fst (snd m)).

  Definition to_comp_isEquiv (a : A) : isEquiv (to_comp a).
  Proof.
    refine (iso_to_isEquiv _ (from_comp a) _ _).
    - intros [k0 kp]. unfold from_comp, to_comp; cbn.
      exact (ap (fun r => ((k0; r) : BG G →* (A; a))) (@ap_fst_path_sigma_prop (fun x => ptrunc (a = x)) _
                                                   (a; trunc refl) (k0 (sh G); _) kp)).
    - intros [m0 mp].
      refine (eqinv (snd (ptw_star _ _)) _).
      unshelve refine (_; _).
      + intro x. apply (path_sigma_prop (fun _ => ptrunc_isProp)). exact refl.
      + pose (e := isInj_ap_isEquiv (fst_isInj (fun x : A => @ptrunc_isProp (a = x)))
                     (a; trunc refl) (m0 (sh G))).
        refine ((eqinv_l e _)^ @ ap (eqinv e) _ @ eqinv_l e _).
        refine (ap_trans _ _ _ @ _).
        refine (ap011 (fun r s => r ⋅ s) (ap_fst_path_sigma_prop _ _)
                  (ap_fst_path_sigma_prop _ _)).
  Defined.

  Definition BGtotype_34
    : {a : A & BG G →* (A; a)} ≃ {a : A & Hom G (AutG gA a)}
    := Eqv_of_Equiv (equiv_functor_sigma_id
         (fun a => Equiv_of_Eqv (Eqv_comp (to_comp a; to_comp_isEquiv a)
                                          (Eqv_inv (Copy_eqv _))))).

End BGtoType.

(** Remark [rem:first-abs-hom]: contrary to homomorphisms of abstract
    groups, ours preserve the group structure automatically
    ([lem:grouphomomaxioms]); see 7.3 (informal). *)

(** Example [exa:conj-concrete]: moving the shape along [p : sh_G = y].
    [(id, p⁻¹) : BG ≃* (BG_÷, y)] gives an isomorphism, and its [Ω] is
    conjugation [g ↦ p g p⁻¹]. *)
Definition regroup (G : Group) (y : utype (BG G)) : Group
  := mkgroup (fst (B G); (y; snd (snd (B G)))).

Definition conj_hom (G : Group) {y : utype (BG G)} (p : sh G = y) : Hom G (regroup G y)
  := @mkhom G (regroup G y) (idmap; p⁻¹).

Definition conj_hom_isIso (G : Group) {y : utype (BG G)} (p : sh G = y)
  : isIso (conj_hom G p)
  := id_isEquiv _.

Definition conj_hom_USym (G : Group) {y : utype (BG G)} (p : sh G = y) (g : USym G)
  : USymf (conj_hom G p) g = p ⋅ (g ⋅ p⁻¹).
Proof. destruct p. exact (ap (fun q => q ⋅ refl) (ap_idmap g)). Defined.

(** Definition [def:inner-autos]: [Binn : BG →* BAut(G)], [y ↦ mkgroup(BG_÷, y)].
    [BAut(G)] is the component of [G] in [Group]; it is wrapped as a group
    in Section 9.7 ([AutGrp]).  The pointing path
    is [inc_out G] rather than [refl], since [Copy] has no definitional
    eta rule. *)
Definition BAutG (G : Group) : Ustar := (component Group G; (G; trunc refl)).

Definition Binn (G : Group) : BG G →* BAutG G.
Proof.
  refine ((fun y => (regroup G y;
                     ptrunc_rec ptrunc_isProp
                       (fun p : sh G = y => trunc (ap (regroup G) p ⋅ (inc_out G)⁻¹))
                       (snd (BG_isConn G) (sh G) y)) : component Group G); _).
  refine (@path_sigma_prop Group (fun K => ptrunc (G = K)) (fun _ => ptrunc_isProp)
            (G; trunc refl) (regroup G (sh G); _) _).
  exact (inc_out G)⁻¹.
Defined.

