(** * Section 3.6 Connected coverings over the circle

    Part of Chapter 3 ([circle.tex]); see [Circle.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Iteration [t^n] for [n : ℤ] of a permutation of a set ([tpow]),
      with [t^{n+m} = t^m t^n] and [t^{-n} t^n = id].
    - [def:connected-by-t]: [conn_by], an equivalence relation.
    - [con:cycset-connS1cover]: [‖∑_{z:S1} E(z)‖₀ ≃ X/∼] ([quot_eqv]) for
      [E :≡ ve_U(X, etop t)].
    - [def:Cyc], and [thm:cycset-connS1cover]: [∑_z E(z)] is connected iff
      [(X,t)] is a cycle ([conn_isCycle], [isCycle_conn]).
    - [def:dgm-map] ([dg]).
    - The standard finite [m]-element cycle with the exercise: the
      successor on [∑_i (i < m)] with an explicit inverse, transported to
      [Fin m] ([finsuccEqv]); [def:RmtoS1] ([Rm], [powm]), a covering.
    - Exercise [xca:preim-eq] ([preim_eq]).
    - [def:subgroup-zet-of-cycle] ([Ht]) and [lem:cycle-order-point-ap]:
      [H_t = {n | t^n(x) = x}] for a cycle ([Ht_point]); the equivalence
      [((base,x) = (base,x)) ≃ ∑_n (t^n(x) = x)] whose first component is
      the winding number of the projected loop ([loopsAE_isEquiv]); and
      [H_t] is the image of that map ([image_loops_Ht]).

    - [lem:IdCycle], all three implications, with identifications in
      [Endo] characterized as [∑_{e:X≃Y} (e t = u e)] ([endo_paths_eqv],
      3.5): 1 ⇒ 2 ([IdCycle_12]), 2 ⇒ 3 ([IdCycle_23], via the book's
      [P_x], whose center gives the unique [e] with [e(x₀) = y₀]) and
      3 ⇒ 1 ([IdCycle_31]); [cor:ConnCycles] ([ConnCycles]).
    - Exercise [xca:map-of-cycles], all three parts.
    - [cor:set-trunc-cyc] ([set_trunc_cyc]): [H] is some [H_t] iff it
      contains [0] and is closed under addition and negation; the
      converse direction is [def:standard-cycle] ([standard_cycle],
      [(ℤ/∼_H, zs)] with [H_t = H]).
    - [def:Order] ([Order], [ord], [HO], [divides]); [(ℤ, zs)] and the
      standard [m]-cycles are cycles, giving the principal orders.
    - After [def:Order], principal orders as subsets of [ℤ]: [H] of
      [(ℤ, zs)] is [{0}] ([Hc_Z]) and [H] of the standard [m]-cycle is [mℤ]
      ([Hc_FinNat], [Hc_Fin]), from the criterion [Ht_mult]: if
      [t^m(x₀) = x₀] and no [0 < r < m] has [t^r(x₀) = x₀], then
      [H_t = mℤ], by Euclidean division ([xca:euclid-div-Z]).  (Moved here
      from 3.8, where they were derived via [m]-th roots.)
    - The Limited Principle of Omniscience ([LPO]), [LEM → LPO]
      ([LEM_LPO]) and exercise [xca:not-not-lpoP].
    - [lem:componentsofcoversofS1] ([lem_componentsofcoversofS1]): under
      LPO, [ConnDecCovS1 ≃ component(R) ⨿ ∑_m component(R_m)].  As in the
      book: a connected covering [C] gives a cycle [(X, t)]
      ([conn_cycE], via [thm:cycset-connS1cover] and [gU]); with [x₀ : X]
      (we prove a proposition) LPO is applied to [P(n) :≡ (t^{n+1}(x₀) =
      x₀)], decidable since [X] is.  If [P] is constantly [0], then
      [H_t = {0}], otherwise [H_t = mℤ] for the least [m]; by
      [lem:IdCycle] the cycle is then merely identified with [(ℤ, zs)] or
      [(Fin m, zs)], and identifications of the underlying [Endo]s give
      identifications of coverings ([endo_cov_path], through [gSet]).  For
      the equivalence we also show what the book leaves implicit: the
      components are disjoint ([Bc_isProp]: [m ∈ H] distinguishes [R]
      from [R_m] ([RSet_ne_Rm]), and [Fin m = Fin m'] gives [m = m']), and
      [R] and [R_m] are connected and decidable ([ConnDec_RSet],
      [ConnDec_Rm]).
    - Remark [rem:flipthecircle]: [(S1, r) = (S1, id)] as coverings, via
      the general [(A, f e) = (A', f)] for an equivalence [e].
    - Functoriality: the function underlying a composite identification
      in [Endo] is the composite ([endo_fun_concat]).

    Left out (statements only, no proofs yet)
    - [con:psi-alpha-m] and [cor:dgm-conncov] ([con_psi_alpha_m_stmt],
      [cor_dgm_conncov_stmt]; the book leaves the inverse of [ψ_m] as an
      exercise).
    - [cor:id-m-cycle] ([cor_id_m_cycle_stmt]): the evaluation map is an
      instance of [ConnCycles], and the compatibility with [zs] follows
      from [endo_fun_concat]; the instantiation at [Fin m] ran into
      universe constraints and was not finished.
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Types.Arrow Truncations.Core Colimits.Coeq
  Colimits.Pushout Spaces.Nat.Core Spaces.Int Spaces.Circle
  Spaces.Finite.Fin Spaces.Finite.FinNat.
From SymmetryBook Require Export Circle.S05_Reinterpretation.

Local Open Scope uf_scope.

(** ** 3.6 Connected coverings over the circle *)

(** Diagram [eq:subgroup-covering-1]: for a pointed connected covering
    [f : A → S1], [ap_f] followed by the winding number embeds
    [a₀ = a₀] into [ℤ]; see [loopsAE_isEquiv] and [image_loops_Ht]
    below. *)

(** Iteration [t^n] of a permutation [t] of a set, for [n : ℤ]. *)
Section Iteration.

  Context `{Funext} {X : Type} (sX : isSet X) (t : X ≃ X).

  Definition tpow (n : ℤ) (x : X) : X := iterZ t n x.

  Definition tpow_zs (n : ℤ) (x : X) : tpow (zs n) x = fst t (tpow n x)
    := iterZ_zs sX t n x.

  Definition tpow_zp (n : ℤ) (x : X) : tpow (zp n) x = eqinv (snd t) (tpow n x)
    := (eqinv_l (snd t) _)^
       @ ap (eqinv (snd t)) ((tpow_zs (zp n) x)^ @ ap (fun k => tpow k x) (zs_zp n)).

  Definition tpow_add (n m : ℤ) (x : X) : tpow (zadd n m) x = tpow m (tpow n x).
  Proof.
    revert m. refine (ℤ_ind_prop _ (fun m => sX _ _) _ _).
    - intro k. induction k as [|k IH].
      + exact refl.
      + exact (tpow_zs (zadd n (iplus k)) x @ ap (fst t) IH).
    - intros [k]. induction k as [|k IH].
      + exact refl.
      + exact (ap (fun w => tpow w x) (eqinv_mkEqv zs zp zp_zs zs_zp _)
               @ tpow_zp _ x @ ap (eqinv (snd t)) IH).
  Defined.

  Definition zadd_zneg (n : ℤ) : zadd n (zneg n) = iplus 0
    := toInt_inj (y := iplus 0) (toInt_zadd _ _ @ ap (int_add (toInt n)) (toInt_zneg n)
                  @ int_add_neg_r _).

  Definition tpow_neg (n : ℤ) (x : X) : tpow (zneg n) (tpow n x) = x
    := (tpow_add n (zneg n) x)^ @ ap (fun k => tpow k x) (zadd_zneg n).

  (** Definition [def:connected-by-t]: [x ∼ x'] iff [x' = t^n(x)] for some
      [n : ℤ]; an equivalence relation. *)
  Definition conn_by (x x' : X) : PropU
    := (ptrunc {n : ℤ & x' = tpow n x}; ptrunc_isProp).

  Definition conn_by_refl (x : X) : fst (conn_by x x) := trunc (iplus 0; refl).

  Definition conn_by_sym (x x' : X) : fst (conn_by x x') -> fst (conn_by x' x)
    := ptrunc_rec ptrunc_isProp
         (fun w => trunc (zneg (fst w); (tpow_neg (fst w) x)^ @ ap (tpow (zneg (fst w))) (snd w)^)).

  Definition conn_by_trans (x x' x'' : X)
    : fst (conn_by x x') -> fst (conn_by x' x'') -> fst (conn_by x x'')
    := fun u v => ptrunc_rec ptrunc_isProp (fun w => ptrunc_rec ptrunc_isProp
         (fun w' => trunc (zadd (fst w) (fst w');
                           snd w' @ ap (tpow (fst w')) (snd w) @ (tpow_add _ _ x)^)) v) u.

End Iteration.

(** Construction [con:cycset-connS1cover]. *)
Section CycsetConnS1cover.

  Context `{Univalence} {X : Type} (sX : isSet X) (t : X ≃ X).

  Definition E : S1 -> Type := ve Type (X; etop t).

  Definition trp_E_loop (y : X) : trp E loop y = fst t y.
  Proof.
    refine (transport_compose idmap E loop y @ _).
    refine (ap (fun r => transport idmap r y) (S1_rec_loop Type X (etop t)) @ _).
    exact (ptw (ap fst (ptoe_etop t)) y).
  Defined.

  Definition trp_E_loopV (y : X) : trp E loop⁻¹ y = eqinv (snd t) y
    := (eqinv_l (snd t) _)^ @ ap (eqinv (snd t)) ((trp_E_loop _)^ @ transport_pV E loop y).

  Definition AE : Type := {z : S1 & E z}.

  Definition step (y : X) : ((base; y) : AE) = (base; fst t y)
    := pathpair (Y := E) loop (trp_E_loop y).

  Definition conn_orbit (n : ℤ)
    : forall x : X, ptrunc (((base; x) : AE) = (base; tpow t n x)).
  Proof.
    revert n. refine (ℤ_ind_prop _ (fun n => Pi_isProp (fun _ => ptrunc_isProp)) _ _).
    - intros k x. induction k as [|k IH].
      + exact (trunc refl).
      + exact (ptrunc_rec ptrunc_isProp (fun p => trunc (step _ ⋅ p)) IH).
    - intros [k] x. induction k as [|k IH].
      + exact (trunc refl).
      + refine (ptrunc_rec ptrunc_isProp (fun p => trunc (_ ⋅ p)) IH).
        exact (step (eqinv (snd t) _) @ ap (fun v => (base; v) : AE) (eqinv_r (snd t) _))^.
  Defined.

  Let R := conn_by t.

  Definition Q : Type := quot R.

  Definition g0_loop : PathOver (fun z => E z -> Q) loop (cls R) (cls R).
  Proof.
    apply ptw_inv. intro y.
    refine (transport_arrow_toconst loop (cls R) y @ _).
    refine (ap (cls R) (trp_E_loopV y) @ _).
    apply (snd (cls_eq_iff R (conn_by_refl t) (conn_by_sym sX t) (conn_by_trans sX t) _ _)).
    exact (trunc (iplus 1; (eqinv_r (snd t) y)^)).
  Defined.

  Definition g0 : forall z : S1, E z -> Q := S1_ind (fun z => E z -> Q) (cls R) g0_loop.

  Definition gq : strunc AE -> Q
    := strunc_rec (quot_isSet R) (fun w => g0 (fst w) (snd w)).

  Definition hq_resp (x x' : X) (r : fst (R x x'))
    : settrunc ((base; x) : AE) = settrunc (base; x').
  Proof.
    refine (ptrunc_rec (strunc_isSet _ _) _ r). intros [n e].
    refine (ptrunc_rec (strunc_isSet _ _) _ (conn_orbit n x)). intro p.
    exact (ap settrunc ((ap (fun v => (base; v) : AE) e)⁻¹ ⋅ p)).
  Defined.

  Definition hq : Q -> strunc AE
    := fbar R (conn_by_refl t) strunc_isSet (fun x : X => settrunc ((base; x) : AE)) hq_resp.

  Definition quot_eqv : strunc AE ≃ Q.
  Proof.
    refine (mkEqv gq hq _ _).
    - refine (strunc_ind_prop _ (fun s => strunc_isSet _ _) _). intros [z e]. revert z e.
      refine (S1_ind_prop (fun z => forall e : E z, hq (gq (settrunc (z; e))) = settrunc (z; e))
                (fun z => Pi_isProp (fun e => strunc_isSet _ _)) _).
      intro e. exact refl.
    - refine (im_ind R _ (fun q => quot_isSet R _ _) _). intro x. exact refl.
  Defined.

  (** Corollary [thm:cycset-connS1cover]: the covering [(∑_{z:S1} E(z), fst)]
      is connected iff [(X,t)] is a cycle, i.e. [X] is nonempty and any
      two elements are connected by [t].
    (Placed before [def:Cyc], in the section of the construction [con:cycset-connS1cover] that it uses.) *)
  Definition isCycle : Type := ptrunc X × (forall x x' : X, fst (R x x')).

  Definition conn_isCycle (c : isConn AE) : isCycle.
  Proof.
    pose (cQ := isContr_Eqv quot_eqv (isConn_strunc_isContr c)).
    refine (_; fun x x' => fst (cls_eq_iff R (conn_by_refl t) (conn_by_sym sX t)
                                  (conn_by_trans sX t) x x') (isContr_isProp' cQ _ _)).
    exact (ptrunc_rec ptrunc_isProp (fun w => trunc (fst w)) (snd (fst cQ))).
  Defined.

  Definition isCycle_conn (cy : isCycle) : isConn AE.
  Proof.
    apply strunc_isContr_isConn.
    refine (isContr_Eqv (Eqv_inv quot_eqv) _).
    refine (ptrunc_rec (isContr_isProp _) _ (fst cy)). intro x0.
    refine (cls R x0; im_ind R _ (fun q => quot_isSet R _ _) _). intro x.
    exact (snd (cls_eq_iff R (conn_by_refl t) (conn_by_sym sX t) (conn_by_trans sX t) _ _)
             (snd cy x0 x)).
  Defined.

End CycsetConnS1cover.

(** Definition [def:Cyc]. *)
Definition Cyc `{Funext} : Type
  := {X : SetU & {t : fst X ≃ fst X &
       ptrunc (fst X) × (forall x x' : fst X, fst (conn_by t x x'))}}.

(** Definition [def:dgm-map]: the degree [m] function, [dg_m(loop) := loop^m]. *)
Definition dg `{Univalence} (m : ℕ) : S1 -> S1 := S1_rec S1 base (loopZ (iplus m)).

(** The standard finite [m]-element cycle, for [m = k+1]: the successor
    [zs(i) :≡ i+1] for [i < m-1] and [zs(m-1) :≡ 0], defined on
    [∑_{i:ℕ} (i < m)] (the library's [FinNat]) and transported to [Fin m]
    along [Fin m ≃ ∑_i (i < m)].  The exercise asks for an explicit
    inverse. *)
Section FinCycle.

  Context (k : ℕ).

  Definition fn_isProp_lt (x : ℕ) : isProp (x < S k)%nat := IsHProp_isProp.

  Definition fs (u : FinNat (S k)) : FinNat (S k)
    := match dec (fst u < k)%nat with
       | inl l => (S (fst u); leq_succ l)
       | inr _ => (0%nat; leq_succ (leq_zero_l k))
       end.

  Definition fp (u : FinNat (S k)) : FinNat (S k)
    := match u with
       | (O; _) => (k; leq_refl (S k))
       | (S x; l) => (x; leq_succ_l l)
       end.

  Definition fs_fp (u : FinNat (S k)) : fs (fp u) = u.
  Proof.
    destruct u as [[|x] l]; unfold fs, fp; cbn.
    - destruct (dec (k < k)%nat) as [l'|nl].
      + destruct (lt_irrefl k l').
      + apply (path_sigma_prop fn_isProp_lt); exact refl.
    - destruct (dec (x < k)%nat) as [l'|nl].
      + apply (path_sigma_prop fn_isProp_lt); exact refl.
      + destruct (nl (leq_pred' l)).
  Defined.

  Definition fp_fs (u : FinNat (S k)) : fp (fs u) = u.
  Proof.
    destruct u as [x l]; unfold fs; cbn.
    destruct (dec (x < k)%nat) as [l'|nl]; cbn.
    - apply (path_sigma_prop fn_isProp_lt); exact refl.
    - apply (path_sigma_prop fn_isProp_lt). cbn.
      exact (leq_antisym (Overture.fst geq_iff_not_lt nl) (leq_pred' l)).
  Defined.

  Definition fsEqv : FinNat (S k) ≃ FinNat (S k) := mkEqv fs fp fp_fs fs_fp.

  Definition finsuccEqv : Fin (S k) ≃ Fin (S k)
    := Eqv_comp (Eqv_of_Equiv (equiv_fin_finnat (S k)))
         (Eqv_comp fsEqv (Eqv_inv (Eqv_of_Equiv (equiv_fin_finnat (S k))))).

  Definition Fin_isSet (n : ℕ) : isSet (Fin n) := fun x y => fst (Fin_isDecSet n x y).

  (** Definition [def:RmtoS1]: [R_m(base) :≡ Fin m], [R_m(loop) := etop(zs)],
      and the [m]-th power bundle [pow_m :≡ fst : Tot(R_m) → S1]. *)
  Context `{Univalence}.

  Definition Rm : S1 -> Type := S1_rec Type (Fin (S k)) (etop finsuccEqv).

  Definition Rm_isSet (z : S1) : isSet (Rm z)
    := ptrunc_rec (isSet_isProp _)
         (fun p : base = z => trp (fun x => isSet (Rm x)) p (Fin_isSet (S k)))
         (S1_base_paths z).

  Definition TotRmStar : Ustar := (Tot Rm; (base; fin_zero)).

  Definition powm : TotRmStar →* S1star := (@fst S1 Rm; refl).

  Definition powm_covering : isPtdCovering powm
    := fun z => is_ntype_Eqv 0 (fst_fiber_eqv Rm z) (Rm_isSet z).

End FinCycle.

(** Remark [rem:finitecoveringsofS1]: a picture of the [m]-th power
    bundle [R_m] (informal). *)

(** Construction [con:psi-alpha-m] and corollary [cor:dgm-conncov]
    (statements only), for [m = k+1]. *)
Definition con_psi_alpha_m_stmt `{Univalence} : Type
  := forall k : ℕ, {ψ : Tot (Rm k) ≃ S1 & fst (powm k) = dg (S k) ∘ fst ψ}.

Definition cor_dgm_conncov_stmt `{Univalence} : Type
  := forall k : ℕ, isConnCovering (dg (S k))
                   × (forall z : S1, ptrunc (fiber (dg (S k)) z = Fin (S k))).

(** Exercise [xca:preim-eq]. *)
Definition comp_l_isEquiv {X : Type} {a b c : X} (r : b = c)
  : isEquiv (fun p : a = b => r ⋅ p).
Proof. destruct r. exact (id_isEquiv _). Defined.

Definition preim_eq {A B C : Type} (f : A -> C) (g : B -> C) (e : A ≃ B)
  (h : forall x, f x = g (fst e x)) (c : C)
  : isEquiv (fun w : fiber f c => ((fst e (fst w); h (fst w) ⋅ snd w) : fiber g c)).
Proof.
  refine (comp_isEquiv (f := tot (fun a (p : c = f a) => h a ⋅ p))
            (g := fun w : {a : A & c = g (fst e a)} => ((fst e (fst w); snd w) : fiber g c))
            (tot_isEquiv _ (fun a => comp_l_isEquiv (h a))) _).
  exact (isEquiv_of_IsEquiv _
           (H := equiv_isequiv (equiv_functor_sigma_pb (Q := fun b => c = g b)
                                  (Equiv_of_Eqv e)))).
Defined.

(** Definition [def:subgroup-zet-of-cycle]: [H_t :≡ {n : ℤ | t^n = id}],
    and the first part of [lem:cycle-order-point-ap]. *)
Section Orders.

  Context `{Univalence} {X : Type} (sX : isSet X) (t : X ≃ X).

  Definition Ht (n : ℤ) : PropU
    := ((tpow t n = idmap); Pi_isSet (fun _ => sX) _ _).

  Definition Ht_point (cy : isCycle t) (x : X) (n : ℤ)
    : (fst (Ht n) -> tpow t n x = x) × (tpow t n x = x -> fst (Ht n)).
  Proof.
    refine (fun e => ptw e x; _).
    intro e. apply ptw_inv. intro x'.
    refine (ptrunc_rec (sX _ _) _ (snd cy x x')). intros [j ej].
    refine (ap (tpow t n) ej @ (tpow_add sX t j n x)^ @ ap (fun w => tpow t w x) (zadd_comm j n)
            @ tpow_add sX t n j x @ ap (tpow t j) e @ ej^).
  Defined.

  (** Loops at [(base, x)] in [∑_{z:S1} E(z)] correspond to
      [∑_{n:ℤ} (t^n(x) = x)], via the winding number of the projection. *)
  Definition trp_E_loopexp (y : Int) (x : X)
    : trp (E t) (loopexp loop y) x = tpow t (fromInt y) x.
  Proof.
    induction y as [|n IH|n IH] using Int_ind.
    - exact refl.
    - refine (ap (fun r : base = base => trp (E t) r x) (loopexp_succ_r loop _) @ _).
      refine (transport_pp (E t) _ _ _ @ trp_E_loop t _ @ ap (fst t) IH @ _).
      exact ((tpow_zs sX t _ x)^ @ ap (fun w => tpow t w x) (fromInt_succ _)^).
    - refine (ap (fun r : base = base => trp (E t) r x) (loopexp_pred_r loop _) @ _).
      refine (transport_pp (E t) _ _ _ @ trp_E_loopV t _ @ ap (eqinv (snd t)) IH @ _).
      exact ((tpow_zp sX t _ x)^ @ ap (fun w => tpow t w x) (fromInt_pred _)^).
  Defined.

  Definition trp_E_loopZ (n : ℤ) (x : X) : trp (E t) (loopZ n) x = tpow t n x
    := trp_E_loopexp (toInt n) x @ ap (fun w => tpow t w x) (fromInt_toInt n).

  Definition trp_ap_fst {Z : Type} {P : Z -> Type} {u v : {z : Z & P z}} (p : u = v)
    : trp P (ap fst p) (snd u) = snd v
    := match p with refl => refl end.

  Definition loopsAE (x : X)
    : (((base; x) : AE t) = (base; x)) -> {n : ℤ & tpow t n x = x}
    := fun p => (fst wdg (ap fst p);
                 (trp_E_loopZ _ x)^ @ ap (fun q : base = base => trp (E t) q x) (loopZ_wdg (ap fst p))
                 @ trp_ap_fst p).

  Definition loopsAE_inv (x : X) (w : {n : ℤ & tpow t n x = x})
    : ((base; x) : AE t) = (base; x)
    := pathpair (Y := E t) (loopZ (fst w)) (trp_E_loopZ (fst w) x @ snd w).


  Definition split' {u v : AE t} (p : u = v)
    : {q : fst u = fst v & trp (E t) q (snd u) = snd v}
    := (ap fst p; trp_ap_fst p).

  Definition split'_isEquiv (u v : AE t) : isEquiv (@split' u v).
  Proof.
    assert (h : forall p : u = v, pathsplit p = split' p) by (intro p; destruct p; exact refl).
    refine (trp isEquiv (ptw_inv h) _).
    exact (iso_to_isEquiv pathsplit (fun pq => pathpair (fst pq) (snd pq))
             pathpair_pathsplit (fun pq => pathsplit_pathpair (fst pq) (snd pq))).
  Defined.

  Definition loopsAE_reindex (x : X)
    : {q : base = base & trp (E t) q x = x} -> {n : ℤ & tpow t n x = x}
    := fun w => (fst wdg (fst w);
                 (trp_E_loopZ _ x)^ @ ap (fun q : base = base => trp (E t) q x)
                                         (loopZ_wdg (fst w)) @ snd w).

  Definition loopsAE_reindex_isEquiv (x : X) : isEquiv (loopsAE_reindex x).
  Proof.
    refine (iso_to_isEquiv _ (fun w => (loopZ (fst w); trp_E_loopZ (fst w) x @ snd w)) _ _).
    - intro w. apply (path_sigma_prop (fun q => sX _ _)). exact (loopZ_wdg _).
    - intro w. apply (path_sigma_prop (fun n => sX _ _)). exact (wdg_loopZ _).
  Defined.

  (** The equivalence of [lem:cycle-order-point-ap]: [((base,x) = (base,x)) ≃
      ∑_{n:ℤ} (t^n(x) = x)], whose first component is the winding number of
      the projected loop. *)
  Definition loopsAE_isEquiv (x : X) : isEquiv (loopsAE x)
    := comp_isEquiv (split'_isEquiv ((base; x) : AE t) (base; x)) (loopsAE_reindex_isEquiv x).

  (** The image of the composite [eq:order-composite],
      [(a = a) → (base = base) ≃ ℤ] (with [a :≡ (base, x)]), is [H_t], for
      a cycle [(X,t)]. *)
  Definition image_loops_Ht (cy : isCycle t) (x : X) (n : ℤ)
    : (ptrunc {p : ((base; x) : AE t) = (base; x) & fst wdg (ap fst p) = n}
       -> fst (Ht n))
      × (fst (Ht n) -> ptrunc {p : ((base; x) : AE t) = (base; x) & fst wdg (ap fst p) = n}).
  Proof.
    refine (ptrunc_rec (snd (Ht n)) _; _).
    - intros [p e]. apply (snd (Ht_point cy x n)).
      exact (ap (fun w => tpow t w x) e^ @ snd (loopsAE x p)).
    - intro h. refine (trunc (loopsAE_inv x (n; fst (Ht_point cy x n) h); _)).
      exact (ap (fst wdg) (ap_fst_pathpair _ _) @ wdg_loopZ n).
  Defined.

End Orders.

(** Maps commuting with the permutations commute with their powers. *)
Section CycleMaps.

  Context `{Univalence} {X Y : Type} (sY : isSet Y) (t : X ≃ X) (u : Y ≃ Y)
    (f : X -> Y) (hf : forall x, f (fst t x) = fst u (f x)).

  Definition cmap_inv (y : X) : f (eqinv (snd t) y) = eqinv (snd u) (f y)
    := (eqinv_l (snd u) _)^ @ ap (eqinv (snd u)) ((hf _)^ @ ap f (eqinv_r (snd t) y)).

  Definition tpow_comm_map (n : ℤ) (x : X) : f (tpow t n x) = tpow u n (f x).
  Proof.
    revert n. refine (ℤ_ind_prop _ (fun n => sY _ _) _ _).
    - intro k. induction k as [|k IH]; [exact refl | exact (hf _ @ ap (fst u) IH)].
    - intros [k]. induction k as [|k IH];
        [exact refl | exact (cmap_inv _ @ ap (eqinv (snd u)) IH)].
  Defined.

End CycleMaps.

Definition zadd_sub_add (m n : ℤ) : zadd (zadd m (zneg n)) n = m
  := toInt_inj (y := m)
       (toInt_zadd _ _ @ ap (fun a => int_add a (toInt n))
          (toInt_zadd _ _ @ ap (int_add (toInt m)) (toInt_zneg n))
        @ (int_add_assoc _ _ _)^ @ ap (int_add (toInt m)) (int_add_neg_l _)
        @ int_add_0_r _).

(** The construction in the proof of [lem:IdCycle]: if [H_t ⊆ H_u], then
    for [x₀ : X], [y₀ : Y] there is a unique [e : X → Y] with [e t = u e]
    and [e(x₀) = y₀], namely the center of
    [P_x :≡ ∑_{y:Y} ∏_{n:ℤ} ((x = t^n(x₀)) → (y = u^n(y₀)))]. *)
Section CycleMapConstruction.

  Context `{Univalence} {X Y : Type} (sX : isSet X) (sY : isSet Y)
    (t : X ≃ X) (u : Y ≃ Y) (cX : isCycle t)
    (hH : forall n, fst (Ht sX t n) -> fst (Ht sY u n)) (x0 : X) (y0 : Y).

  Definition agree (m n : ℤ) (e : tpow t m x0 = tpow t n x0)
    : tpow u m y0 = tpow u n y0.
  Proof.
    pose (d := zadd m (zneg n)).
    pose (ed := tpow_add sX t m (zneg n) x0 @ ap (tpow t (zneg n)) e @ tpow_neg sX t n x0
                : tpow t d x0 = x0).
    pose (hd := hH d (snd (Ht_point sX t cX x0 d) ed)).
    exact (ap (fun w => tpow u w y0) (zadd_sub_add m n)^ @ tpow_add sY u d n y0
           @ ap (tpow u n) (ptw hd y0)).
  Defined.

  Definition Pt (x : X) : Type
    := {y : Y & forall n : ℤ, x = tpow t n x0 -> y = tpow u n y0}.

  Definition Pt_isContr (x : X) : isContr (Pt x).
  Proof.
    refine (ptrunc_rec (isContr_isProp _) _ (snd cX x0 x)). intros [m em].
    refine ((tpow u m y0; fun n en => agree m n (em^ @ en)); _).
    intros [y φ].
    apply (path_sigma_prop (fun y => Pi_isProp (fun n => Pi_isProp (fun _ => sY _ _)))).
    exact (φ m em)^.
  Defined.

  Definition eF (x : X) : Y := fst (fst (Pt_isContr x)).

  Definition eF_spec (x : X) (n : ℤ) (en : x = tpow t n x0) : eF x = tpow u n y0
    := snd (fst (Pt_isContr x)) n en.

  Definition Pt_unique (x : X) (y y' : Pt x) : fst y = fst y'
    := ap fst (isContr_isProp' (Pt_isContr x) y y').

  Definition eF_x0 : eF x0 = y0 := eF_spec x0 (iplus 0) refl.

  Definition eF_comm (x : X) : eF (fst t x) = fst u (eF x).
  Proof.
    refine (Pt_unique (fst t x) (fst (Pt_isContr _)) (fst u (eF x); _)).
    intros n en.
    pose (ex := (eqinv_l (snd t) x)^ @ ap (eqinv (snd t)) en @ (tpow_zp sX t n x0)^
                : x = tpow t (zp n) x0).
    exact (ap (fst u) (eF_spec x (zp n) ex) @ (tpow_zs sY u (zp n) y0)^
           @ ap (fun w => tpow u w y0) (zs_zp n)).
  Defined.

  Definition eF_unique (f : X -> Y) (hf : forall x, f (fst t x) = fst u (f x))
    (f0 : f x0 = y0) (x : X) : f x = eF x
    := Pt_unique x (f x; fun n en => ap f en @ tpow_comm_map sY t u f hf n x0
                                      @ ap (tpow u n) f0)
         (fst (Pt_isContr x)).

End CycleMapConstruction.


(** Lemma [lem:IdCycle].  Identifications [(X,t) = (Y,u)] are taken in
    [Endo :≡ ∑_{X:U}(X → X)], and correspond to [∑_{e:X≃Y} (e t = u e)]
    ([endo_paths_eqv], 3.5); part 3 is stated for the latter type, which
    the book identifies with the former "transparently". *)
Section IdCycle.

  Context `{Univalence} {X Y : Type} (sX : isSet X) (sY : isSet Y)
    (t : X ≃ X) (u : Y ≃ Y) (cX : isCycle t) (cY : isCycle u).

  Definition Ht_transfer {A B : Type} (sA : isSet A) (sB : isSet B)
    (a : A ≃ A) (b : B ≃ B) (e : A ≃ B) (h : forall x, fst e (fst a x) = fst b (fst e x))
    (n : ℤ) : fst (Ht sA a n) -> fst (Ht sB b n)
    := fun ha => ptw_inv (fun y => (ap (tpow b n) (eqinv_r (snd e) y))^
                     @ (tpow_comm_map sB a b (fst e) h n _)^ @ ap (fst e) (ptw ha _)
                     @ eqinv_r (snd e) y).

  Definition inv_comm {A B : Type} (a : A ≃ A) (b : B ≃ B) (e : A ≃ B)
    (h : forall x, fst e (fst a x) = fst b (fst e x)) (y : B)
    : eqinv (snd e) (fst b y) = fst a (eqinv (snd e) y)
    := ap (eqinv (snd e)) (ap (fst b) (eqinv_r (snd e) y)^ @ (h _)^) @ eqinv_l (snd e) _.

  Definition Hiff : Type
    := forall n, (fst (Ht sX t n) -> fst (Ht sY u n)) × (fst (Ht sY u n) -> fst (Ht sX t n)).

  Definition EndoEqv : Type := {e : X ≃ Y & fst e ∘ fst t = fst u ∘ fst e}.

  (** 1 ⇒ 2, i.e. [nr:TruncXtYu] ⇒ [nr:HtSubZYu] ([Hiff]). *)
  Definition IdCycle_12 (p : ptrunc (((X; fst t) : Endo) = (Y; fst u))) : Hiff.
  Proof.
    refine (ptrunc_rec (Pi_isProp (fun n => prod_isProp (fun_isProp (snd (Ht sY u n)))
                                              (fun_isProp (snd (Ht sX t n))))) _ p).
    intro q. pose (w := fst (endo_paths_eqv (fst t) (fst u)) q).
    intro n. exact (Ht_transfer sX sY t u (fst w) (ptw (snd w)) n;
                    Ht_transfer sY sX u t (Eqv_inv (fst w))
                      (inv_comm t u (fst w) (ptw (snd w))) n).
  Defined.

  (** 2 ⇒ 3, i.e. [nr:HtSubZYu] ⇒ [nr:eXtYuPtd]. *)
  Definition IdCycle_23 (hH : Hiff) (x0 : X) (y0 : Y)
    : isContr {w : EndoEqv & fst (fst w) x0 = y0}.
  Proof.
    pose (h1 := fun n => fst (hH n)). pose (h2 := fun n => snd (hH n)).
    pose (f := eF sX sY t u cX h1 x0 y0). pose (g := eF sY sX u t cY h2 y0 x0).
    assert (gf : forall x, g (f x) = x).
    { intro x.
      exact (eF_unique sX sX t t cX (fun n h => h) x0 x0 (fun x => g (f x))
               (fun x => ap g (eF_comm _ _ _ _ _ _ _ _ x) @ eF_comm _ _ _ _ _ _ _ _ _)
               (ap g (eF_x0 _ _ _ _ _ _ _ _) @ eF_x0 _ _ _ _ _ _ _ _) x
             @ (eF_unique sX sX t t cX (fun n h => h) x0 x0 idmap (fun x => refl) refl x)^). }
    assert (fg : forall y, f (g y) = y).
    { intro y.
      exact (eF_unique sY sY u u cY (fun n h => h) y0 y0 (fun y => f (g y))
               (fun y => ap f (eF_comm _ _ _ _ _ _ _ _ y) @ eF_comm _ _ _ _ _ _ _ _ _)
               (ap f (eF_x0 _ _ _ _ _ _ _ _) @ eF_x0 _ _ _ _ _ _ _ _) y
             @ (eF_unique sY sY u u cY (fun n h => h) y0 y0 idmap (fun y => refl) refl y)^). }
    refine ((((mkEqv f g gf fg; ptw_inv (eF_comm sX sY t u cX h1 x0 y0)) : EndoEqv);
             eF_x0 sX sY t u cX h1 x0 y0); _).
    intros [[e h] p0].
    apply (path_sigma_prop (fun _ => sY _ _)).
    apply (path_sigma_prop (fun e : X ≃ Y => Pi_isSet (fun _ => sY) _ _)).
    apply path_Eqv, ptw_inv. intro x.
    exact (eF_unique sX sY t u cX h1 x0 y0 (fst e) (ptw h) p0 x)^.
  Defined.

  (** 3 ⇒ 1, i.e. [nr:eXtYuPtd] ⇒ [nr:TruncXtYu]. *)
  Definition IdCycle_31 (h3 : forall x0 y0, isContr {w : EndoEqv & fst (fst w) x0 = y0})
    : ptrunc (((X; fst t) : Endo) = (Y; fst u))
    := ptrunc_rec ptrunc_isProp
         (fun x0 => ptrunc_rec ptrunc_isProp
            (fun y0 => trunc (eqinv (snd (endo_paths_eqv (fst t) (fst u)))
                                (fst (fst (h3 x0 y0)))))
            (fst cY))
         (fst cX).

  (** Corollary [cor:ConnCycles]: evaluation at [x₀] is an equivalence
      [((X,t) = (Y,u)) ≃ Y]. *)
  Definition ev_x0 (x0 : X) (p : ((X; fst t) : Endo) = (Y; fst u)) : Y
    := fst (fst (fst (endo_paths_eqv (fst t) (fst u)) p)) x0.

  Definition ConnCycles (hH : Hiff) (x0 : X) : isEquiv (ev_x0 x0).
  Proof.
    refine (comp_isEquiv (f := fst (endo_paths_eqv (fst t) (fst u)))
              (g := fun w : EndoEqv => fst (fst w) x0)
              (snd (endo_paths_eqv (fst t) (fst u))) _).
    intro y0.
    exact (isContr_Eqv (tot (fun w (p : fst (fst w) x0 = y0) => p⁻¹);
                        tot_isEquiv _ (fun w => snd symm_eqv))
             (IdCycle_23 hH x0 y0)).
  Defined.

End IdCycle.

(** Corollary [cor:id-m-cycle] (statement only): for the cycles
    [(Fin m, zs)], evaluation at [0] is an equivalence
    [((Fin m, zs) = (Fin m, zs)) ≃ Fin m], sending [refl] to [0], under
    which composition with [(zs, !)] corresponds to [zs]; this is the
    diagram of Figure [fig:id-m-cycle] for [e ≡ zs]. *)
Definition cor_id_m_cycle_stmt `{Univalence} : Type
  := forall k : ℕ,
       let zsk := fst (finsuccEqv k) in
       {e : (((Fin (S k); zsk) : Endo) = (Fin (S k); zsk)) ≃ Fin (S k) &
         (fst e refl = fin_zero)
         × (forall p, fst e (endo_path (finsuccEqv k) refl ⋅ p) = zsk (fst e p))}.

(** Remark [rem:thenonuniquenessofgeneratorsofmodulararithmetic1]: for
    [m > 2], [zs] is not the only [e] with [(Fin m, e)] a cycle, [e]
    commuting with [zs] (the precondition [P(e)] of Figure
    [fig:id-m-cycle]), and the diagram of [cor:id-m-cycle] commuting;
    [e ≡ zs⁻¹] also works.  The solutions are the [zs^k] with
    [1 ≤ k ≤ m] and [k] relatively prime to [m] (informal). *)

(** Corollary [cor:set-trunc-cyc], first half: each [H_t] contains [0] and
    is closed under addition and negation. *)
Definition Ht_subgroup `{Univalence} {X : Type} (sX : isSet X) (t : X ≃ X)
  : fst (Ht sX t (iplus 0))
    × (forall n m, fst (Ht sX t n) -> fst (Ht sX t m) -> fst (Ht sX t (zadd n m)))
    × (forall n, fst (Ht sX t n) -> fst (Ht sX t (zneg n))).
Proof.
  refine ((refl; fun n m hn hm => ptw_inv (fun x => _)); fun n hn => ptw_inv (fun x => _)).
  - exact (tpow_add sX t n m x @ ap (tpow t m) (ptw hn x) @ ptw hm x).
  - exact (ap (tpow t (zneg n)) (ptw hn x)^ @ tpow_neg sX t n x).
Defined.

(** Exercise [xca:map-of-cycles]. *)
Section MapOfCycles.

  Context `{Univalence} {X Y : Type} (sX : isSet X) (sY : isSet Y)
    (t : X ≃ X) (u : Y ≃ Y) (cX : isCycle t) (cY : isCycle u)
    (f : X -> Y) (hf : forall x, f (fst t x) = fst u (f x)).

  Definition mapcyc_i (n : ℤ) : fst (Ht sX t n) -> fst (Ht sY u n)
    := fun ht => ptrunc_rec (snd (Ht sY u n))
         (fun x0 => snd (Ht_point sY u cY (f x0) n)
                      ((tpow_comm_map sY t u f hf n x0)^ @ ap f (ptw ht x0)))
         (fst cX).

  Definition mapcyc_ii : isSurj f
    := fun y => ptrunc_rec ptrunc_isProp
         (fun x0 => ptrunc_rec ptrunc_isProp
            (fun w => trunc (tpow t (fst w) x0; snd w @ (tpow_comm_map sY t u f hf (fst w) x0)^))
            (snd cY (f x0) y))
         (fst cX).

  Definition mapcyc_iii (hH : forall n, fst (Ht sY u n) -> fst (Ht sX t n)) : isInj f.
  Proof.
    apply (cancel_isInj sY). intros x x' e.
    refine (ptrunc_rec (sX _ _) _ (snd cX x x')). intros [n en].
    pose (eu := (tpow_comm_map sY t u f hf n x)^ @ ap f en^ @ e^ : tpow u n (f x) = f x).
    pose (ht := hH n (snd (Ht_point sY u cY (f x) n) eu)).
    exact ((ptw ht x)^ @ en^).
  Defined.

End MapOfCycles.

(** Definition [def:Order]: [Order :≡ ‖Cyc‖₀], with [ord :≡ |_|₀]; the
    subset [H] of an order, and divisibility [d | k] iff [H_k ⊆ H_d]. *)
Definition Hc `{Univalence} (c : Cyc) : ℤ -> PropU := Ht (snd (fst c)) (fst (snd c)).

Definition Order `{Univalence} : Type := strunc Cyc.

Definition ord `{Univalence} : Cyc -> Order := settrunc.

Definition HO `{Univalence} : Order -> ℤ -> PropU
  := strunc_rec (Pi_isSet (fun _ => PropU_isSet)) Hc.

Definition divides `{Univalence} (d k : Order) : Type
  := forall n, fst (HO k n) -> fst (HO d n).

(** The infinite cycle [(ℤ, zs)] and the standard [m]-cycles, giving the
    principal orders [ℕ → Order] ([0] to the infinite order). *)
Definition zadd_sub (x x' : ℤ) : x' = zadd x (zadd x' (zneg x)).
Proof.
  apply toInt_inj. symmetry.
  rewrite toInt_zadd, toInt_zadd, toInt_zneg.
  rewrite (int_add_comm (toInt x') _), int_add_assoc, int_add_neg_r.
  exact refl.
Defined.

Definition Z_isCycle `{Univalence} : isCycle zsEqv
  := (trunc (iplus 0); fun x x' => trunc (zadd x' (zneg x); zadd_sub x x')).

Definition Zcyc `{Univalence} : Cyc := ((ℤ; ℤ_isSet); (zsEqv; Z_isCycle)).

Section FinIsCycle.

  Context `{Univalence} (k : ℕ).

  Definition FinNat_isSet : isSet (FinNat (S k))
    := Sigma_isSet (IsHSet_isSet ishset_nat) (fun x => prop_is_set (fn_isProp_lt k x)).

  Definition fn0 : FinNat (S k) := (0%nat; leq_succ (leq_zero_l k)).

  Definition fs_iter (i : ℕ) (l : (i < S k)%nat) : tpow (fsEqv k) (iplus i) fn0 = (i; l).
  Proof.
    induction i as [|i IH].
    - apply (path_sigma_prop (fn_isProp_lt k)). exact refl.
    - refine (ap (fs k) (IH (leq_succ_l l)) @ _). unfold fs. cbn.
      destruct (dec (i < k)%nat) as [l'|nl].
      + apply (path_sigma_prop (fn_isProp_lt k)). exact refl.
      + destruct (nl (leq_pred' l)).
  Defined.

  Definition FinNat_isCycle : isCycle (fsEqv k).
  Proof.
    refine (trunc fn0; fun x x' => trunc (zadd (zneg (iplus (fst x))) (iplus (fst x')); _)).
    refine ((fs_iter (fst x') (snd x'))^ @ _).
    refine (ap (tpow (fsEqv k) (iplus (fst x'))) (tpow_neg FinNat_isSet (fsEqv k) _ fn0)^ @ _).
    refine (ap (fun v => tpow (fsEqv k) (iplus (fst x')) (tpow (fsEqv k) (zneg (iplus (fst x))) v))
              (fs_iter (fst x) (snd x)) @ _).
    exact (tpow_add FinNat_isSet (fsEqv k) _ _ x)^.
  Defined.

  Definition Fin_isCycle : isCycle (finsuccEqv k).
  Proof.
    pose (e := Eqv_of_Equiv (equiv_fin_finnat (S k))).
    assert (he : forall x, fst e (fst (finsuccEqv k) x) = fst (fsEqv k) (fst e x))
      by (intro x; exact (eqinv_r (snd e) _)).
    refine (trunc fin_zero; fun x x' => _).
    refine (ptrunc_rec ptrunc_isProp _ (snd FinNat_isCycle (fst e x) (fst e x'))).
    intros [n en]. refine (trunc (n; Eqv_inj e (en @ _))).
    exact (tpow_comm_map FinNat_isSet (finsuccEqv k) (fsEqv k) (fst e) he n x)^.
  Defined.

  Definition Fincyc : Cyc := ((Fin (S k); Fin_isSet (S k)); (finsuccEqv k; Fin_isCycle)).

End FinIsCycle.

Definition principal_order `{Univalence} (n : ℕ) : Order
  := match n with O => ord Zcyc | S k => ord (Fincyc k) end.

(** After [def:Order]: a principal order [d] is simply [dℤ], as a subset
    of [ℤ]; we compute [H] for [(ℤ, zs)] and for the standard [m]-cycles. *)
Definition zadd_0_l (n : ℤ) : zadd (iplus 0) n = n
  := toInt_inj (y := n) (toInt_zadd (iplus 0) n).

(** [H] of the infinite cycle [(ℤ, zs)] is [{0}]. *)
Definition Hc_Z `{Univalence} (n : ℤ)
  : (fst (Hc Zcyc n) -> n = iplus 0) × (n = iplus 0 -> fst (Hc Zcyc n))
  := (fun h => (zadd_0_l n)^ @ ptw h (iplus 0);
      fun e : n = iplus 0 => trp (fun w => fst (Hc Zcyc w)) e^
                                (refl : fst (Hc Zcyc (iplus 0)))).

(** If [t^m(x₀) = x₀] for [m = k+1], and [t^r(x₀) = x₀] with [r < m]
    only for [r = 0], then [H_t = mℤ]; by Euclidean division. *)
Section HtMult.

  Context `{Univalence} {X : Type} (sX : isSet X) (t : X ≃ X) (cy : isCycle t)
    (x0 : X) (k : ℕ) (hm : tpow t (iplus (S k)) x0 = x0)
    (hr : forall r : ℕ, (r < S k)%nat -> tpow t (iplus r) x0 = x0 -> r = 0%nat).

  Definition Ht_mul (q : ℤ) : fst (Ht sX t (zmul (iplus (S k)) q)).
  Proof.
    pose (hM := snd (Ht_point sX t cy x0 (iplus (S k))) hm).
    revert q. refine (ℤ_ind_prop _ (fun q => snd (Ht sX t _)) _ _).
    - intro j. induction j as [|j IH].
      + exact (fst (fst (Ht_subgroup sX t))).
      + exact (snd (fst (Ht_subgroup sX t)) _ _ hM IH).
    - intros [j].
      assert (hj : fst (Ht sX t (zmul (iplus (S k)) (iplus j)))).
      { induction j as [|j IH].
        + exact (fst (fst (Ht_subgroup sX t))).
        + exact (snd (fst (Ht_subgroup sX t)) _ _ hM IH). }
      refine (trp (fun w => fst (Ht sX t w)) _ (snd (Ht_subgroup sX t) _ hj)).
      apply toInt_inj.
      refine (toInt_zneg _ @ ap int_neg (toInt_zmul _ _) @ (int_mul_neg_r (toInt (iplus (S k))) (toInt (iplus j)))^
              @ (toInt_zmul (iplus (S k)) (iminus (negN j)))^).
  Defined.

  Definition Ht_mult (n : ℤ)
    : (fst (Ht sX t n) -> Ex (fun q => n = zmul (iplus (S k)) q))
      × (Ex (fun q => n = zmul (iplus (S k)) q) -> fst (Ht sX t n)).
  Proof.
    refine (fun h => _; ptrunc_rec (snd (Ht sX t n))
                          (fun w => trp (fun v => fst (Ht sX t v)) (snd w)^ (Ht_mul (fst w)))).
    destruct (euclid_div_Sk n k) as [q [r [lr en]]].
    assert (er : tpow t (iplus r) x0 = x0).
    { refine (ap (tpow t (iplus r)) (ptw (Ht_mul q) x0)^ @ _).
      refine ((tpow_add sX t _ _ x0)^ @ _).
      refine (ap (fun w => tpow t w x0) (ap (fun w => zadd w (iplus r)) (zmul_comm _ _) @ en^) @ _).
      exact (fst (Ht_point sX t cy x0 n) h). }
    pose (r0 := hr r lr er).
    exact (trunc (q; en @ ap (fun s => zadd (zmul q (iplus (S k))) (iplus s)) r0
                     @ zmul_comm _ _)).
  Defined.

End HtMult.

(** [H] of the standard [m]-cycle, [m = k+1], is [mℤ]. *)
Section HcFin.

  Context `{Univalence} (k : ℕ).

  Definition fs_last : fs k (k; leq_refl (S k)) = fn0 k.
  Proof.
    unfold fs; cbn. destruct (dec (k < k)%nat) as [l|nl].
    - destruct (lt_irrefl k l).
    - apply (path_sigma_prop (fn_isProp_lt k)). exact refl.
  Defined.

  Definition Hc_FinNat (n : ℤ)
    : (fst (Ht (FinNat_isSet k) (fsEqv k) n) -> Ex (fun q => n = zmul (iplus (S k)) q))
      × (Ex (fun q => n = zmul (iplus (S k)) q) -> fst (Ht (FinNat_isSet k) (fsEqv k) n)).
  Proof.
    refine (Ht_mult (FinNat_isSet k) (fsEqv k) (FinNat_isCycle k) (fn0 k) k _ _ n).
    - change (fs k (tpow (fsEqv k) (iplus k) (fn0 k)) = fn0 k).
      exact (ap (fs k) (fs_iter k k (leq_refl (S k))) @ fs_last).
    - intros r lr e. exact (ap fst ((fs_iter k r lr)^ @ e)).
  Defined.

  Definition Hc_Fin (n : ℤ)
    : (fst (Hc (Fincyc k) n) -> Ex (fun q => n = zmul (iplus (S k)) q))
      × (Ex (fun q => n = zmul (iplus (S k)) q) -> fst (Hc (Fincyc k) n)).
  Proof.
    pose (e := Eqv_of_Equiv (equiv_fin_finnat (S k))).
    assert (he : forall x, fst e (fst (finsuccEqv k) x) = fst (fsEqv k) (fst e x))
      by (intro x; exact (eqinv_r (snd e) _)).
    pose (to := Ht_transfer (Fin_isSet (S k)) (FinNat_isSet k) (finsuccEqv k) (fsEqv k) e he n).
    pose (back := Ht_transfer (FinNat_isSet k) (Fin_isSet (S k)) (fsEqv k) (finsuccEqv k)
                    (Eqv_inv e) (inv_comm (finsuccEqv k) (fsEqv k) e he) n).
    exact (fun h => fst (Hc_FinNat n) (to h); fun h => back (snd (Hc_FinNat n) h)).
  Defined.

End HcFin.

(** Corollary [cor:set-trunc-cyc], second half, and [def:standard-cycle]:
    for [H ⊆ ℤ] containing [0] and closed under addition and negation, the
    cycle [(ℤ/∼_H, zs)], with [z ∼_H z'] iff [z - z' ∈ H], has [H_t = H].
    (Placed after [def:standard-cycle], which it uses.) *)
Section StandardCycle.

  Context `{Univalence} (Hs : ℤ -> PropU) (h0 : fst (Hs (iplus 0)))
    (hadd : forall n m, fst (Hs n) -> fst (Hs m) -> fst (Hs (zadd n m)))
    (hneg : forall n, fst (Hs n) -> fst (Hs (zneg n))).

  Definition zsub (z z' : ℤ) : ℤ := zadd z (zneg z').

  Definition zsub_neg (z z' : ℤ) : zneg (zsub z z') = zsub z' z.
  Proof.
    apply toInt_inj. unfold zsub.
    repeat first [rewrite toInt_zadd | rewrite toInt_zneg | rewrite toInt_zs | rewrite toInt_zp].
    rewrite int_neg_add, int_neg_neg, int_add_comm. exact refl.
  Defined.

  Definition zsub_trans (z z' z'' : ℤ) : zadd (zsub z z') (zsub z' z'') = zsub z z''.
  Proof.
    apply toInt_inj. unfold zsub.
    repeat first [rewrite toInt_zadd | rewrite toInt_zneg | rewrite toInt_zs | rewrite toInt_zp].
    rewrite int_add_assoc, <- (int_add_assoc (toInt z)), int_add_neg_l, int_add_0_r.
    exact refl.
  Defined.

  Definition zsub_zs (z z' : ℤ) : zsub (zs z) (zs z') = zsub z z'.
  Proof.
    apply toInt_inj. unfold zsub.
    repeat first [rewrite toInt_zadd | rewrite toInt_zneg | rewrite toInt_zs | rewrite toInt_zp].
    rewrite int_neg_succ, int_add_succ_l, int_add_pred_r, int_pred_succ. exact refl.
  Defined.

  Definition zsub_zp (z z' : ℤ) : zsub (zp z) (zp z') = zsub z z'.
  Proof.
    apply toInt_inj. unfold zsub.
    repeat first [rewrite toInt_zadd | rewrite toInt_zneg | rewrite toInt_zs | rewrite toInt_zp].
    rewrite int_neg_pred, int_add_pred_l, int_add_succ_r, int_succ_pred. exact refl.
  Defined.

  Definition zsub_0 (n : ℤ) : zsub (zadd (iplus 0) n) (iplus 0) = n.
  Proof.
    apply toInt_inj. unfold zsub.
    repeat first [rewrite toInt_zadd | rewrite toInt_zneg | rewrite toInt_zs | rewrite toInt_zp]. cbn. rewrite int_add_0_r. exact refl.
  Defined.

  Definition RH (z z' : ℤ) : PropU := Hs (zsub z z').

  Definition RH_refl (z : ℤ) : fst (RH z z) := trp (fun w => fst (Hs w)) (zadd_zneg z)^ h0.

  Definition RH_sym (z z' : ℤ) (r : fst (RH z z')) : fst (RH z' z)
    := trp (fun w => fst (Hs w)) (zsub_neg z z') (hneg _ r).

  Definition RH_trans (z z' z'' : ℤ) (r : fst (RH z z')) (r' : fst (RH z' z''))
    : fst (RH z z'')
    := trp (fun w => fst (Hs w)) (zsub_trans z z' z'') (hadd _ _ r r').

  Definition ZH : Type := quot RH.

  Definition clsH (z : ℤ) : ZH := cls RH z.

  Definition clsH_eq (z z' : ℤ) (r : fst (RH z z')) : clsH z = clsH z'
    := snd (cls_eq_iff RH RH_refl RH_sym RH_trans z z') r.

  Definition tH : ZH -> ZH
    := fbar RH RH_refl (quot_isSet RH) (fun z => clsH (zs z))
         (fun z z' r => clsH_eq _ _ (trp (fun w => fst (Hs w)) (zsub_zs z z')^ r)).

  Definition tHi : ZH -> ZH
    := fbar RH RH_refl (quot_isSet RH) (fun z => clsH (zp z))
         (fun z z' r => clsH_eq _ _ (trp (fun w => fst (Hs w)) (zsub_zp z z')^ r)).

  Definition tHEqv : ZH ≃ ZH.
  Proof.
    refine (mkEqv tH tHi _ _).
    - refine (im_ind RH _ (fun q => quot_isSet RH _ _) _). intro z.
      exact (ap clsH (zp_zs z)).
    - refine (im_ind RH _ (fun q => quot_isSet RH _ _) _). intro z.
      exact (ap clsH (zs_zp z)).
  Defined.

  Definition tpow_clsH (n z : ℤ) : tpow tHEqv n (clsH z) = clsH (zadd z n).
  Proof.
    revert n. refine (ℤ_ind_prop _ (fun n => quot_isSet RH _ _) _ _).
    - intro k. induction k as [|k IH]; [exact refl | exact (ap tH IH)].
    - intros [k]. induction k as [|k IH].
      + exact refl.
      + exact (eqinv_mkEqv tH tHi _ _ _ @ ap tHi IH
               @ ap clsH (eqinv_mkEqv zs zp zp_zs zs_zp _)^).
  Defined.

  Definition ZH_isCycle : isCycle tHEqv.
  Proof.
    refine (trunc (clsH (iplus 0)); _).
    refine (im_ind RH _ (fun q => Pi_isProp (fun q' => ptrunc_isProp)) _). intro z.
    refine (im_ind RH _ (fun q' => ptrunc_isProp) _). intro z'.
    exact (trunc (zadd z' (zneg z); ap clsH (zadd_sub z z') @ (tpow_clsH _ z)^)).
  Defined.

  Definition standard_cycle : Cyc := ((ZH; quot_isSet RH); (tHEqv; ZH_isCycle)).

  Definition standard_cycle_H (n : ℤ)
    : (fst (Hc standard_cycle n) -> fst (Hs n)) × (fst (Hs n) -> fst (Hc standard_cycle n)).
  Proof.
    pose (hp := Ht_point (quot_isSet RH) tHEqv ZH_isCycle (clsH (iplus 0)) n).
    refine (fun h => _; fun h => snd hp _).
    - pose (e := (tpow_clsH n (iplus 0))^ @ fst hp h).
      exact (trp (fun w => fst (Hs w)) (zsub_0 n)
               (fst (cls_eq_iff RH RH_refl RH_sym RH_trans _ _) e)).
    - exact (tpow_clsH n (iplus 0) @ clsH_eq _ _ (trp (fun w => fst (Hs w)) (zsub_0 n)^ h)).
  Defined.

End StandardCycle.

(** Corollary [cor:set-trunc-cyc]: [H ⊆ ℤ] is of the form [H_t] for a cycle
    iff it contains [0] and is closed under addition and negation. *)
Definition isSubgroupZ (Hs : ℤ -> PropU) : Type
  := fst (Hs (iplus 0))
     × (forall n m, fst (Hs n) -> fst (Hs m) -> fst (Hs (zadd n m)))
     × (forall n, fst (Hs n) -> fst (Hs (zneg n))).

Definition set_trunc_cyc `{Univalence} (Hs : ℤ -> PropU)
  : (ptrunc {c : Cyc & forall n, (fst (Hc c n) -> fst (Hs n)) × (fst (Hs n) -> fst (Hc c n))}
     -> isSubgroupZ Hs)
    × (isSubgroupZ Hs
       -> ptrunc {c : Cyc & forall n, (fst (Hc c n) -> fst (Hs n)) × (fst (Hs n) -> fst (Hc c n))}).
Proof.
  refine (_; fun s => trunc (standard_cycle Hs (fst (fst s)) (snd (fst s)) (snd s);
                             standard_cycle_H _ _ _ _)).
  refine (ptrunc_rec _ _).
  - exact (prod_isProp (prod_isProp (snd (Hs _))
             (Pi_isProp (fun n => Pi_isProp (fun m => fun_isProp (fun_isProp (snd (Hs _)))))))
             (Pi_isProp (fun n => fun_isProp (snd (Hs _))))).
  - intros [c hc].
    pose (sg := Ht_subgroup (snd (fst c)) (fst (snd c))).
    refine ((fst (hc _) (fst (fst sg));
             fun n m hn hm => fst (hc _) (snd (fst sg) n m (snd (hc n) hn) (snd (hc m) hm)));
            fun n hn => fst (hc _) (snd sg n (snd (hc n) hn))).
Defined.

(** The Limited Principle of Omniscience ([LPO]): for [P : ℕ → 𝟚], either
    there is a smallest [n₀] with [P(n₀) = yes], or [P] is constantly [no]. *)
Definition LPO : Type
  := forall P : ℕ -> Bool,
       {n0 : ℕ & Pmin (fun n => ((P n = yes); isSet_bool _ _)) n0} ⨿ (forall n, P n = no).

Definition Bool_dec_yes (b : Bool) : isDecidable (b = yes)
  := match b as b' return isDecidable (b' = yes) with
     | yes => inl refl
     | no => inr (fun e => yes_ne_no e^)
     end.

Definition not_yes_no (b : Bool) : ¬ (b = yes) -> b = no
  := match b as b' return ¬ (b' = yes) -> b' = no with
     | yes => fun n => match n refl with end
     | no => fun _ => refl
     end.

(** The Law of Excluded Middle implies LPO. *)
Definition LEM_LPO `{Funext} (lem : LEM) : LPO.
Proof.
  intro P. pose (Q := fun n => ((P n = yes); isSet_bool (P n) yes) : PropU).
  destruct (lem (ptrunc {n : ℕ & P n = yes}) ptrunc_isProp) as [w|nw].
  - exact (inl (min Q (fun n => Bool_dec_yes (P n)) w)).
  - exact (inr (fun n => not_yes_no (P n) (fun e => nw (trunc (n; e))))).
Defined.

(** Exercise [xca:not-not-lpoP]. *)
Definition not_not_LPO (P : ℕ -> Bool)
  : ¬ ¬ ({n0 : ℕ & Pmin (fun n => ((P n = yes); isSet_bool _ _)) n0} ⨿ (forall n, P n = no)).
Proof.
  intro nq. apply nq. right. intro n.
  apply not_yes_no. intro e.
  apply nq. left.
  exact (mu (fun n => ((P n = yes); isSet_bool _ _)) (fun n => Bool_dec_yes (P n)) (S n);
         mu_Pmin (fun n => ((P n = yes); isSet_bool _ _)) (fun n => Bool_dec_yes (P n)) n e).
Defined.

(** Functoriality of the identification of [lem:IdCycle]: the underlying
    function of a composite of identifications in [Endo] is the composite. *)
Definition endo_fun `{Univalence} {X Y : Type} {t : X -> X} {u : Y -> Y}
  (p : ((X; t) : Endo) = (Y; u)) : X -> Y
  := fst (fst (fst (endo_paths_eqv t u) p)).

Definition endo_fun_trp `{Univalence} {X Y : Type} {t : X -> X} {u : Y -> Y}
  (p : ((X; t) : Endo) = (Y; u)) (x : X)
  : endo_fun p x = transport idmap (ap (fun w : Endo => fst w) p) x.
Proof.
  assert (G : forall (w : Endo) (q : ((X; t) : Endo) = w),
             @endo_fun _ X (fst w) t (snd w) q x
             = transport idmap (ap (fun w : Endo => fst w) q) x)
    by (intros w q; destruct q; exact refl).
  exact (G (Y; u) p).
Defined.

Definition endo_fun_concat `{Univalence} {X Y Z : Type} {t : X -> X} {u : Y -> Y}
  {v : Z -> Z} (p : ((X; t) : Endo) = (Y; u)) (q : ((Y; u) : Endo) = (Z; v)) (x : X)
  : endo_fun (p @ q) x = endo_fun q (endo_fun p x).
Proof.
  refine (endo_fun_trp _ x @ _).
  refine (ap (fun r => transport idmap r x) (ap_pp (fun w : Endo => fst w) p q)
          @ transport_pp idmap _ _ x @ _).
  exact (ap (transport idmap (ap (fun w : Endo => fst w) q)) (endo_fun_trp p x)^
         @ (endo_fun_trp q _)^).
Defined.


Definition ConnDecCovS1 : Type
  := {E : S1 -> SetU & isConn {z : S1 & fst (E z)} × (forall z, isDecSet (fst (E z)))}.

(** Lemma [lem:componentsofcoversofS1]: under LPO, the connected
    decidable coverings of the circle are the component of the universal
    covering and those of the [m]-fold coverings. *)
Section ComponentsOfCoversOfS1.

  Context `{Univalence}.

  (** The cycle [(E(base), trp^E_loop)] of a covering [E : S1 → Set]
      ([gSet] of [thm:coveringsofS1perms]), and its underlying [Endo]. *)
  Definition cycE (E : S1 -> SetU) : {X : SetU & fst X ≃ fst X} := fst gSet E.

  Definition endoE (E : S1 -> SetU) : Endo := (fst (fst (cycE E)); fst (snd (cycE E))).

  (** An identification of the underlying [Endo]s gives one of coverings. *)
  Definition endo_lift {X : Type} {t : X -> X} (w : Endo) (q : ((X; t) : Endo) = w)
    (sX : isSet X) (te : isEquiv t) (sY : isSet (fst w)) (ue : isEquiv (snd w))
    : (((X; sX); (t; te)) : {X : SetU & fst X ≃ fst X}) = ((fst w; sY); (snd w; ue)).
  Proof.
    destruct q.
    exact (ap (fun v : isSet X × isEquiv t => ((X; fst v); (t; snd v)) : {X : SetU & fst X ≃ fst X})
              (prod_isProp (isSet_isProp _) (isEquiv_isProp _) (sX; te) (sY; ue))).
  Defined.

  Definition endo_cov_path {E E' : S1 -> SetU} (p : endoE E = endoE E') : E = E'
    := Eqv_inj gSet (x := E) (x' := E') (endo_lift (endoE E') p (snd (fst (cycE E))) (snd (snd (cycE E)))
                       (snd (fst (cycE E'))) (snd (snd (cycE E')))).

  (** For the coverings [E_t(base) :≡ X], [E_t(loop) :≡ etop(t)] of
      [con:cycset-connS1cover], the cycle is [(X, t)]. *)
  Definition EV {X : Type} (t : X ≃ X) (s : forall z, isSet (E t z)) : S1 -> SetU
    := fun z => (E t z; s z).

  Definition endoE_EV {X : Type} (t : X ≃ X) (s : forall z, isSet (E t z))
    : endoE (EV t s) = (X; fst t).
  Proof.
    apply (ap (fun f => (X; f) : Endo)).
    exact (ap (fun r => fst (idtoeqv r)) ((ap_compose (EV t s) fst loop)^
                                          @ S1_rec_loop Type X (etop t))
           @ ap fst (ptoe_etop t)).
  Defined.

  (** A connected covering gives a cycle ([thm:cycset-connS1cover]). *)
  Definition conn_cycE (C : S1 -> SetU) (c : isConn {z : S1 & fst (C z)})
    : isCycle (snd (cycE C)).
  Proof.
    pose (t := snd (cycE C)).
    assert (F : (fun z => fst (C z)) = E t).
    { apply (Eqv_inj gU).
      refine (ap (fun e => (fst (C base); e) : {X : Type & X ≃ X}) _).
      exact (ap idtoeqv (ap_compose C fst loop) @ (ptoe_etop t)^
             @ ap idtoeqv (S1_rec_loop Type _ (etop t))^). }
    exact (conn_isCycle (snd (fst (cycE C))) t
             (trp (fun S : S1 -> Type => isConn {z : S1 & S z}) F c)).
  Defined.

  Definition RmSet (k : ℕ) : S1 -> SetU := fun z => (Rm k z; Rm_isSet k z).

  Definition ConnDec (E : S1 -> SetU) : Type
    := isConn {z : S1 & fst (E z)} × (forall z, isDecSet (fst (E z))).

  Definition ConnDec_isProp (E : S1 -> SetU) : isProp (ConnDec E)
    := prod_isProp (prod_isProp ptrunc_isProp
                      (Pi_isProp (fun _ => Pi_isProp (fun _ => ptrunc_isProp))))
         (Pi_isProp (fun z => isDecSet_isProp _)).

  Definition ConnDec_RSet : ConnDec RSet
    := (isCycle_conn ℤ_isSet zsEqv Z_isCycle;
        S1_ind_prop (fun z => isDecSet (R z)) (fun z => isDecSet_isProp _) ℤ_isDecSet).

  Definition ConnDec_Rm (k : ℕ) : ConnDec (RmSet k)
    := (isCycle_conn (Fin_isSet (S k)) (finsuccEqv k) (Fin_isCycle k);
        S1_ind_prop (fun z => isDecSet (Rm k z)) (fun z => isDecSet_isProp _)
          (Fin_isDecSet (S k))).

  (** Cycles with the same [H] give merely identified coverings
      ([lem:IdCycle]). *)
  Definition cov_merely (C : S1 -> SetU) (cC : isCycle (snd (cycE C)))
    {Y : Type} (sY : isSet Y) (u : Y ≃ Y) (cY : isCycle u)
    (hH : Hiff (snd (fst (cycE C))) sY (snd (cycE C)) u)
    (D : S1 -> SetU) (eD : endoE D = (Y; fst u))
    : ptrunc (D = C)
    := ptrunc_rec ptrunc_isProp (fun p => trunc (endo_cov_path (eD @ p^)))
         (IdCycle_31 _ u cC cY (IdCycle_23 _ sY _ u cC cY hH)).

  Definition endoE_RSet : endoE RSet = (ℤ; fst zsEqv) := endoE_EV zsEqv R_isSet.

  Definition endoE_Rm (k : ℕ) : endoE (RmSet k) = (Fin (S k); fst (finsuccEqv k))
    := endoE_EV (finsuccEqv k) (Rm_isSet k).

  (** The universal covering is not an [m]-fold covering: [m ∈ H] for the
      latter, but not for the former. *)
  Definition RSet_ne_Rm (k : ℕ) (p : RSet = RmSet k) : False.
  Proof.
    pose (hH := IdCycle_12 ℤ_isSet (Fin_isSet (S k)) zsEqv (finsuccEqv k)
                  (trunc (endoE_RSet^ @ ap endoE p @ endoE_Rm k))).
    pose (h := snd (hH (iplus (S k))) (snd (Hc_Fin k (iplus (S k))) (trunc (iplus 1; refl)))).
    exact (zero_ne_succ k (iplus_inj (fst (Hc_Z (iplus (S k))) h))^).
  Defined.

  Definition Bc (C : S1 -> SetU) : Type
    := ptrunc (RSet = C) ⨿ {k : ℕ & ptrunc (RmSet k = C)}.

  Definition Bc_isProp (C : S1 -> SetU) : isProp (Bc C).
  Proof.
    intros [a|[k a]] [b|[k' b]].
    - exact (ap inl (ptrunc_isProp _ _)).
    - refine (match _ : False with end).
      refine (ptrunc_rec False_isProp _ a). intro p.
      refine (ptrunc_rec False_isProp _ b). intro q.
      exact (RSet_ne_Rm k' (p @ q^)).
    - refine (match _ : False with end).
      refine (ptrunc_rec False_isProp _ a). intro p.
      refine (ptrunc_rec False_isProp _ b). intro q.
      exact (RSet_ne_Rm k (q @ p^)).
    - assert (e : k = k').
      { refine (ptrunc_rec (ℕ_isSet _ _) _ a). intro p.
        refine (ptrunc_rec (ℕ_isSet _ _) _ b). intro q.
        exact (ap nat_pred (Fin_paths_eq (ap (fun D : S1 -> SetU => fst (D base)) (p @ q^)))). }
      destruct e. exact (ap (fun w => inr (k; w)) (ptrunc_isProp _ _)).
  Defined.

  Definition ConnDec_Bc (C : S1 -> SetU) (b : Bc C) : ConnDec C
    := match b with
       | inl a => ptrunc_rec (ConnDec_isProp C) (fun p => trp ConnDec p ConnDec_RSet) a
       | inr (k; a) => ptrunc_rec (ConnDec_isProp C) (fun p => trp ConnDec p (ConnDec_Rm k)) a
       end.

  (** Booleans from decisions. *)
  Definition bdec {A : Type} (d : isDecidable A) : Bool
    := match d with inl _ => yes | inr _ => no end.

  Definition bdec_yes {A : Type} (d : isDecidable A) : bdec d = yes -> A
    := match d with
       | inl a => fun _ => a
       | inr _ => fun e => match yes_ne_no e^ with end
       end.

  Definition yes_bdec {A : Type} (d : isDecidable A) (a : A) : bdec d = yes
    := match d with inl _ => refl | inr n => match n a with end end.

  (** The main step: by LPO, a connected decidable covering is merely the
      universal covering, or merely an [m]-fold covering. *)
  Definition Bc_ConnDec (lpo : LPO) (C : S1 -> SetU) (cd : ConnDec C) : Bc C.
  Proof.
    pose (sX := snd (fst (cycE C))). pose (t := snd (cycE C)).
    pose (cy := conn_cycE C (fst cd)).
    pose (dX := snd cd base : isDecSet (fst (fst (cycE C)))).
    refine (ptrunc_rec (Bc_isProp C) _ (fst cy)). intro x0.
    pose (Pb := fun n : ℕ => bdec (snd (dX (tpow t (iplus (S n)) x0) x0))).
    destruct (lpo Pb) as [[n0 [p0 pmin]] | none].
    - (* the least [m = n₀+1] with [t^m(x₀) = x₀]: [H_t = mℤ] *)
      right. exists n0.
      assert (hr : forall r : ℕ, (r < S n0)%nat -> tpow t (iplus r) x0 = x0 -> r = 0%nat).
      { intros [|r] lr e; [exact refl|].
        destruct (lt_irrefl r (leq_trans (leq_pred' lr)
                                (le_leq (pmin r (yes_bdec _ e))))). }
      pose (hM := Ht_mult sX t cy x0 n0 (bdec_yes _ p0) hr).
      refine (cov_merely C cy (Fin_isSet (S n0)) (finsuccEqv n0) (Fin_isCycle n0) _
                (RmSet n0) (endoE_Rm n0)).
      intro n. exact (fun h => snd (Hc_Fin n0 n) (fst (hM n) h);
                      fun h => snd (hM n) (fst (Hc_Fin n0 n) h)).
    - (* no such [m]: [H_t = {0}] *)
      left.
      assert (H0 : forall n, fst (Ht sX t n) -> n = iplus 0).
      { assert (pos : forall a, fst (Ht sX t (iplus (S a))) -> False).
        { intros a h. apply yes_ne_no.
          exact ((yes_bdec _ (fst (Ht_point sX t cy x0 _) h))^ @ none a). }
        refine (ℤ_ind_prop _ (fun n => fun_isProp (ℤ_isSet _ _)) _ _).
        - intros [|a] h; [exact refl | destruct (pos a h)].
        - intros [[|a]] h; [exact zeq | destruct (pos a (snd (Ht_subgroup sX t) _ h))]. }
      refine (cov_merely C cy ℤ_isSet zsEqv Z_isCycle _ RSet endoE_RSet).
      intro n. refine (fun h => snd (Hc_Z n) (H0 n h); fun h => _).
      exact (trp (fun w => fst (Ht sX t w)) (fst (Hc_Z n) h)^ (fst (fst (Ht_subgroup sX t)))).
  Defined.

  Definition CompT : Type
    := component (S1 -> SetU) RSet ⨿ {k : ℕ & component (S1 -> SetU) (RmSet k)}.

  Definition splitB (C : S1 -> SetU) (b : Bc C) : CompT
    := match b with inl a => inl (C; a) | inr (k; a) => inr (k; (C; a)) end.

  Definition lem_componentsofcoversofS1 (lpo : LPO) : ConnDecCovS1 ≃ CompT.
  Proof.
    refine (mkEqv (fun w => splitB (fst w) (Bc_ConnDec lpo (fst w) (snd w)))
              (fun v => match v with
                        | inl (C; a) => (C; ConnDec_Bc C (inl a))
                        | inr (k; (C; a)) => (C; ConnDec_Bc C (inr (k; a)))
                        end) _ _).
    - intros [C cd]. change (fst (C; cd)) with C. change (snd (C; cd)) with cd.
      destruct (Bc_ConnDec lpo C cd) as [a|[k a]];
        (apply (path_sigma_prop ConnDec_isProp); exact refl).
    - intros [[C a]|[k [C a]]].
      + exact (ap (splitB C) (Bc_isProp C _ (inl a))).
      + exact (ap (splitB C) (Bc_isProp C _ (inr (k; a)))).
  Defined.

End ComponentsOfCoversOfS1.

(** Remark [rem:flipthecircle]: the orientation reversing map [r :≡ -id_S1]
    and [id_S1] give the same covering, since [r] is an equivalence. *)
Definition cov_eq `{Univalence} {A A' C : Type} (e : A ≃ A') (f : A' -> C)
  : ((A; f ∘ fst e) : {B : Type & B -> C}) = (A'; f).
Proof.
  refine (pathpair (Y := fun B : Type => B -> C) (etop e) (ptw_inv (fun y => _))).
  refine (transport_arrow_toconst (etop e) (f ∘ fst e) y @ ap f _).
  exact ((ptw (ap fst (ptoe_etop e)) _)^ @ transport_pV idmap (etop e) y).
Defined.

Definition negid_negid `{Univalence} (x : S1) : negid (negid x) = x.
Proof.
  refine (S1_htpy (f := fun x => negid (negid x)) (g := idmap) refl _ x).
  refine (ap_compose negid negid loop @ ap (ap negid) (S1_rec_loop S1 base loop⁻¹)
          @ ap_V negid loop @ ap inverse (S1_rec_loop S1 base loop⁻¹) @ inv_V loop @ _).
  exact ((trans_1p _ @ ap_idmap loop)^).
Defined.

Definition negidEqv `{Univalence} : S1 ≃ S1 := mkEqv negid negid negid_negid negid_negid.

Definition flip_cover `{Univalence}
  : ((S1; negid) : {B : Type & B -> S1}) = (S1; idmap)
  := cov_eq negidEqv idmap.
