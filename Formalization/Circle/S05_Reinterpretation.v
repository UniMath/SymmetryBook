(** * Section 3.5 A reinterpretation of the circle

    Part of Chapter 3 ([circle.tex]); see [Circle.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - [Endo :≡ ∑_{X:U}(X → X)]; an equivalence [e : X ≃ Y] with
      [e t = u e] gives [(X,t) = (Y,u)] ([endo_path]).
    - [def:S1toC]: [InfCyc], the component of [Endo] at [(ℤ, zs)], and
      [c : S1 → InfCyc] with [c(loop)] given by the predecessor.
    - [lem:IdCisZet], in the form: the type of pointed infinite cycles is
      contractible ([IC_pointed_isContr]), hence [ev_0 : ((ℤ,zs) = w) → w]
      is an equivalence for every [w : InfCyc] ([ev0_isEquiv], by
      [lem:fiberwise-equiv-from-tot]).  The equivalence [n ↦ t^n(x)] is
      checked for [(ℤ, zs)], where it is [n ↦ x + n].
    - [lem:conn-eq-f-ap-f-x] is [conn_isEquiv_iff_point] from 2.17.
    - [thm:S1bysymmetries]: [c] is an equivalence, by the book's second
      proof ([ev_0 (ap_c (loop^n)) = -n]).
    - Exercise [xca:TTYoneda], first part ([yoneda_eqv]), and second
      part: [x ↦ (y ↦ x = y)] is injective ([xca_TTYoneda_inj]), since
      its fibers are contractible when inhabited: by function
      extensionality, univalence and Yoneda, the fiber over
      [y ↦ (x₀ = y)] is [∑_x (x = x₀)] ([yon_fiber_contr]).

    Left out (not formalized)
    - The first proof of [thm:S1bysymmetries] (via diagram
      [eq:setbundle-Sc-univ-comp]); the theorem itself is proved by the
      second proof. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Colimits.Coeq Colimits.Pushout
  Spaces.Nat.Core Spaces.Int Spaces.Circle Universes.HProp.
From SymmetryBook Require Export Circle.S04_SymmetriesCircle.

Local Open Scope uf_scope.

(** ** 3.5 A reinterpretation of the circle *)

Section Reinterpretation.

  Context `{Univalence}.

  (** Types with an endofunction, [∑_{X:U}(X → X)]. *)
  Definition Endo : Type := {X : Type & X -> X}.

  (** Identifications in [Endo]: an equivalence [e : X ≃ Y] with
      [e ∘ t = u ∘ e] gives [(X,t) = (Y,u)], whose underlying
      identification of types is [etop e]. *)
  Definition endo_path {X Y : Type} {t : X -> X} {u : Y -> Y} (e : X ≃ Y)
    (h : fst e ∘ t = u ∘ fst e) : ((X; t) : Endo) = (Y; u).
  Proof.
    refine (pathpair (Y := fun X : Type => X -> X) (etop e) _).
    refine (trp_endo_ua e t @ ptw_inv (fun y => _)).
    exact (ptw h (eqinv (snd e) y) @ ap u (eqinv_r (snd e) y)).
  Defined.

  Definition ap_fst_endo_path {X Y : Type} {t : X -> X} {u : Y -> Y}
    (e : X ≃ Y) (h : fst e ∘ t = u ∘ fst e)
    : ap (fun w : Endo => fst w) (endo_path e h) = etop e
    := ap_fst_pathpair _ _.

  (** Iteration [t^n] for [n : ℤ] of an equivalence [t] of a set. *)
  Definition iterZ_zs {X : Type} (sX : isSet X) (t : X ≃ X) (n : ℤ) (x : X)
    : iterZ t (zs n) x = fst t (iterZ t n x).
  Proof.
    revert n. refine (ℤ_ind_prop _ (fun n => sX _ _) _ _).
    - intro n. exact refl.
    - intros [[|k]].
      + exact refl.
      + exact (eqinv_r (snd t) _)^.
  Defined.

  (** The base point [(ℤ, zs)] and the type of infinite cycles
      ([def:S1toC]): the component of [Endo] containing [(ℤ, zs)].
    (Part of [def:S1toC]; placed before [lem:IdCisZet], which uses it.) *)
  Definition Zs : Endo := (ℤ; zs).

  Definition InfCyc : Type := component Endo Zs.

  Definition c0 : InfCyc := (Zs; trunc refl).

  Definition carrier_IC (w : InfCyc) : Type := fst (fst w).

  (** Properties of infinite cycles, transported from [(ℤ, zs)]. *)
  Definition IC_prop (P : Endo -> Type) (hP : forall w, isProp (P w)) (p0 : P Zs)
    (w : InfCyc) : P (fst w)
    := ptrunc_rec (hP (fst w)) (fun p => trp P p p0) (snd w).

  Definition IC_isSet (w : InfCyc) : isSet (carrier_IC w)
    := IC_prop (fun v => isSet (fst v)) (fun v => isSet_isProp _) ℤ_isSet w.

  Definition IC_isEquiv (w : InfCyc) : isEquiv (snd (fst w))
    := IC_prop (fun v => isEquiv (snd v)) (fun v => isEquiv_isProp _) (snd zsEqv) w.

  Definition IC_eqv (w : InfCyc) : carrier_IC w ≃ carrier_IC w
    := (snd (fst w); IC_isEquiv w).

  (** For an infinite cycle [(X,t)] and [x : X], [n ↦ t^n(x)] is an
      equivalence [ℤ ≃ X]; it suffices to check this for [(ℤ, zs)], where
      it is [n ↦ x + n]. *)
  Definition orbit (w : InfCyc) (x : carrier_IC w) : ℤ -> carrier_IC w
    := fun n => iterZ (IC_eqv w) n x.

  Definition orbit_isEquiv (w : InfCyc) (x : carrier_IC w) : isEquiv (orbit w x).
  Proof.
    revert x. unfold orbit, IC_eqv. generalize (IC_isEquiv w).
    refine (IC_prop (fun v => forall (tE : isEquiv (snd v)) (x : fst v),
                       isEquiv (fun n => iterZ (snd v; tE) n x))
              (fun v => Pi_isProp (fun _ => Pi_isProp (fun _ => isEquiv_isProp _))) _ w).
    intros tE x.
    assert (e : ((zs; tE) : ℤ ≃ ℤ) = zsEqv) by exact (path_Eqv (zs; tE) zsEqv refl).
    refine (trp (fun E : ℤ ≃ ℤ => isEquiv (fun n => iterZ E n x)) e^ _).
    exact (snd (zaddEqv x)).
  Defined.

  Definition orbit_zs (w : InfCyc) (x : carrier_IC w) (n : ℤ)
    : orbit w x (zs n) = snd (fst w) (orbit w x n)
    := iterZ_zs (IC_isSet w) (IC_eqv w) n x.

  (** Remark [rem:bang]: [!] names elements of a proposition clear from
      the context (a notational convention). *)

  (** Lemma [lem:IdCisZet], in the form: the type of pointed infinite
      cycles is contractible.  Hence, for [(X,t)] in [InfCyc],
      [ev_0 : ((ℤ,zs) = (X,t)) → X] is an equivalence (below). *)
  Definition IC_pointed_isContr : isContr {w : InfCyc & carrier_IC w}.
  Proof.
    refine ((c0; iplus 0); _).
    intros [[[X t] m] x].
    pose (w := ((X; t); m) : InfCyc).
    pose (e := (orbit w x; orbit_isEquiv w x) : ℤ ≃ X).
    pose (h := ptw_inv (orbit_zs w x) : fst e ∘ zs = t ∘ fst e).
    pose (P := path_sigma_prop (u := c0) (v := w) (fun _ => ptrunc_isProp) (endo_path e h)).
    refine (pathpair P _).
    change (trp carrier_IC P (iplus 0) = x).
    refine (transport_compose (fun v : Endo => fst v) fst P (iplus 0) @ _).
    refine (ap (fun r : Zs = (X; t) => trp (fun v : Endo => fst v) r (iplus 0))
              (ap_fst_pathpair _ _) @ _).
    refine (transport_compose idmap (fun v : Endo => fst v) (endo_path e h) (iplus 0) @ _).
    refine (ap (fun r : ℤ = X => transport idmap r (iplus 0)) (ap_fst_endo_path e h) @ _).
    exact (ptw (ap fst (ptoe_etop e)) (iplus 0)).
  Defined.

  Definition ev0 (w : InfCyc) (p : c0 = w) : carrier_IC w
    := trp carrier_IC p (iplus 0).

  Definition ev0_isEquiv (w : InfCyc) : isEquiv (ev0 w)
    := isEquiv_from_tot ev0
         (contr_map_isEquiv (singleton_contr c0) IC_pointed_isContr _) w.

  (** Definition [def:S1toC]: [c(base) :≡ (ℤ, zs)], and [c(loop)] is given by
      the predecessor [zs⁻¹] with the (trivial) proof of [zs⁻¹ zs = zs zs⁻¹]. *)
  Definition zpEqv : ℤ ≃ ℤ := mkEqv zp zs zs_zp zp_zs.

  Definition cloop : c0 = c0
    := path_sigma_prop (u := c0) (v := c0) (fun _ => ptrunc_isProp)
         (endo_path (t := zs) (u := zs) zpEqv
            (ptw_inv (fun n => zp_zs n @ (zs_zp n)^))).

  Definition c : S1 -> InfCyc := S1_rec InfCyc c0 cloop.

  (** Exercise [xca:TTYoneda], first part. *)
  Definition yoneda_eqv {X : Type} (F : X -> Type) (x : X)
    : F x ≃ (forall y : X, x = y -> F y).
  Proof.
    refine (mkEqv (fun u y p => trp F p u) (fun k => k x refl) (fun u => refl) _).
    intro k. apply ptw_inv. intro y. apply ptw_inv. intro p. destruct p. exact refl.
  Defined.

  (** Exercise [xca:TTYoneda], second part: the map [x ↦ (y ↦ (x = y))] is
      an injection.  We show that its fibers are contractible when inhabited
      (the alternative mentioned in the book): over [y ↦ (x₀ = y)] the fiber
      is [∑_x ((y ↦ (x₀ = y)) = (y ↦ (x = y)))], and by function
      extensionality, univalence and the first part (with [F :≡ (y ↦ (x = y))])
      the type of identifications is [x = x₀], with [∑_x (x = x₀)]
      contractible.  The natural maps [(x₀ = y) → (x = y)] obtained from
      [u : x = x₀] are [p ↦ u · p], which are all equivalences. *)
  Definition yon_base_equiv {X : Type} (x0 x : X)
    : (x = x0) <~> (forall y : X, x0 = y -> x = y).
  Proof.
    refine (equiv_adjointify (fun u y p => u @ p) (fun k => k x0 idpath) _ _).
    - intro k. funext y p. destruct p. exact (concat_p1 _).
    - intro u. exact (concat_p1 u).
  Defined.

  Definition yon_path_equiv {X : Type} (x0 x : X)
    : (forall y : X, (x0 = y) <~> (x = y)) <~> (x = x0).
  Proof.
    refine (_ oE (equiv_sig_coind (fun y => x0 = y -> x = y) (fun y f => IsEquiv f))^-1
              oE equiv_functor_forall_id (fun y => (issig_equiv (x0 = y) (x = y))^-1)).
    transitivity {u : x = x0 & forall y, IsEquiv (fun p : x0 = y => u @ p)}.
    - symmetry.
      pose (e := yon_base_equiv x0 x).
      exact (equiv_functor_sigma' (Q := fun k : forall y, x0 = y -> x = y => forall y, IsEquiv (k y))
               e (fun u => equiv_idmap)).
    - apply equiv_sigma_contr. intro u.
      apply (contr_inhabited_hprop _). intro y. exact _.
  Defined.

  Definition yon_fiber_contr {X : Type} (x0 : X)
    : Contr {x : X & (fun y => x0 = y) = (fun y => x = y)}.
  Proof.
    refine (contr_equiv' {x : X & x = x0} _).
    apply equiv_functor_sigma_id. intro x.
    exact (equiv_inverse (yon_path_equiv x0 x
           oE equiv_functor_forall_id (fun y => equiv_equiv_path _ _) oE equiv_apD10 _ _ _)).
  Defined.

  (** The injection of the second part. *)
  Definition xca_TTYoneda_inj (X : Type) : isInj (fun x : X => fun y : X => x = y).
  Proof.
    intros F z z'.
    pose (C := transport (fun G => Contr {x : X & G = (fun y => x = y)})
                 (snd z)^ (yon_fiber_contr (fst z))).
    exact (@path_contr _ C z z').
  Defined.

  (** Lemma [lem:conn-eq-f-ap-f-x] is [conn_isEquiv_iff_point] from 2.17. *)
  Definition conn_eq_f_ap_f_x `{Funext} {X Y : Type} (cX : isConn X)
    (cY : isConn Y) (x : X) (f : X -> Y)
    : (isEquiv f -> isEquiv (@ap X Y f x x)) × (isEquiv (@ap X Y f x x) -> isEquiv f)
    := conn_isEquiv_iff_point f cX cY x.

  (** Theorem [thm:S1bysymmetries], by the second proof in the book:
      [ev_0 ∘ ap_c ∘ loop^-] is [n ↦ -n]. *)
  Definition ap_carrier_cloop : ap carrier_IC cloop = etop zpEqv.
  Proof.
    refine (ap_compose fst (fun v : Endo => fst v) cloop @ _).
    refine (ap (ap (fun v : Endo => fst v)) (ap_fst_pathpair _ _) @ _).
    exact (ap_fst_endo_path _ _).
  Defined.

  Definition ptoe_zpEqv (y : ℤ) : transport idmap (etop zpEqv) y = zp y
    := ptw (ap fst (ptoe_etop zpEqv)) y.

  Definition ptoe_zpEqvV (y : ℤ) : transport idmap (etop zpEqv)^ y = zs y
    := (zs_zp _)^ @ ap zs ((ptoe_zpEqv _)^ @ transport_pV idmap (etop zpEqv) y).

  Definition ev0_cloop_Int (x : Int)
    : ev0 c0 (loopexp cloop x) = fromInt (int_neg x).
  Proof.
    unfold ev0.
    refine (transport_compose idmap carrier_IC _ _ @ _).
    refine (ap (fun r : ℤ = ℤ => transport idmap r (iplus 0))
              (ap_loopexp carrier_IC cloop x @ ap (fun r => loopexp r x) ap_carrier_cloop) @ _).
    induction x as [|n IH|n IH] using Int_ind.
    - exact refl.
    - refine (ap (fun r : ℤ = ℤ => transport idmap r (iplus 0)) (loopexp_succ_r _ _) @ _).
      refine (transport_pp idmap _ _ _ @ _).
      refine (ptoe_zpEqv _ @ ap zp IH @ _).
      exact ((fromInt_pred _)^ @ ap fromInt (int_neg_succ _)^).
    - refine (ap (fun r : ℤ = ℤ => transport idmap r (iplus 0)) (loopexp_pred_r _ _) @ _).
      refine (transport_pp idmap _ _ _ @ _).
      refine (ptoe_zpEqvV _ @ ap zs IH @ _).
      exact ((fromInt_succ _)^ @ ap fromInt (int_neg_pred _)^).
  Defined.

  Definition ev0_ap_c_loopZ (n : ℤ) : ev0 c0 (ap c (loopZ n)) = zneg n.
  Proof.
    refine (ap (ev0 c0) (ap_loopexp c loop _ @ ap (fun r => loopexp r _)
                           (S1_rec_loop InfCyc c0 cloop)) @ _).
    refine (ev0_cloop_Int _ @ _).
    apply toInt_inj.
    exact (toInt_fromInt _ @ (toInt_zneg n)^).
  Defined.

  Definition ap_c_isEquiv : isEquiv (@ap S1 InfCyc c base base).
  Proof.
    pose (k := fun n => ap c (loopZ n)).
    assert (sk : isEquiv k).
    { apply (two_of_three_f k zneg (ev0 c0) (ptw_inv ev0_ap_c_loopZ)).
      - exact (snd znegEqv).
      - exact (ev0_isEquiv c0). }
    exact (two_of_three_h loopZ k (ap c) (ptw_inv (fun n => refl)) loopZ_isEquiv sk).
  Defined.

  Definition c_isEquiv : isEquiv c
    := snd (conn_eq_f_ap_f_x S1_isConn (component_isConn Zs) base c) ap_c_isEquiv.

  (** The identity type [(X,t) = (Y,u)] in [Endo] is equivalent to
      [∑_{e : X ≃ Y} (e t = u e)]. *)
  Definition endo_trp_eqv {X Y : Type} (p : X = Y) (t : X -> X) (u : Y -> Y)
    : (trp (fun X : Type => X -> X) p t = u) ≃ (ptoe p ∘ t = u ∘ ptoe p).
  Proof. destruct p. exact (idEqv _). Defined.

  Definition endo_paths_eqv {X Y : Type} (t : X -> X) (u : Y -> Y)
    : (((X; t) : Endo) = (Y; u)) ≃ {e : X ≃ Y & fst e ∘ t = u ∘ fst e}.
  Proof.
    refine (Eqv_comp (Eqv_inv (path_sigma_eqv (Y := fun X : Type => X -> X))) _).
    refine (Eqv_comp (tot (fun p => fst (endo_trp_eqv p t u));
                      tot_isEquiv _ (fun p => snd (endo_trp_eqv p t u))) _).
    exact (Eqv_of_Equiv (equiv_functor_sigma_pb
             (Q := fun e : X ≃ Y => fst e ∘ t = u ∘ fst e)
             (Equiv_of_Eqv (idtoeqv; ua X Y)))).
  Defined.

End Reinterpretation.
