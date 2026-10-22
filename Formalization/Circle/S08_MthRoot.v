(** * Section 3.8 The m-th root: coverings over the components of Cyc

    Part of Chapter 3 ([circle.tex]); see [Circle.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - [def:Cyc-components]: [Cyc0] and [Cycm k] (for [m = k+1]), the
      components of [Cyc] at [(ℤ, zs)] and [(Fin m, zs)].
    - Construction [con:root]: the [m]-th root [ᵐ√t] on [𝟙m × X], with
      [𝟙m] represented as [∑_{i:ℕ} (i < m)] ([FinNat]).
    - Lemma [lem:root-pres-equiv], with an explicit inverse
      ([root_isEquiv]).
    - [(ᵐ√t)^m (i, x) = (i, t(x))] ([root_m]), which the book also writes
      as [(ᵐ√t)^m = (id, t)].
    - Exercise [xca:root-NOT-pres-inv] ([root_not_pres_inv]): a
      counterexample for [m = 2], [X = ℤ], [t = zs].
    - Definition [def:root]: the formal [m]-th root [ρ_m] on [∑_X (X → X)]
      ([rho]).

    - Powers of the root: [(ᵐ√t)^{mq}(i,x) = (i, t^q(x))] for [q : ℤ]
      ([root_pow]).
    - Lemma [lem:m-root-id] and its converse: [(ᵐ√t)^n = id] iff [n = mq]
      with [t^q = id] ([m_root_id], [m_root_id_conv], [Ht_root]); as in
      the book, by Euclidean division [n = qm + r] ([euclid_div_Sk] from
      3.2, exercise [xca:euclid-div-Z]) and looking at the first component.
    - Lemma [lem:root-pres-cycle]: the [m]-th root of a cycle is a cycle
      ([root_isCycle], [rho_cyc]).
    - Identifications of cycles from identifications in [Endo]
      ([cyc_path]); cycles with the same [H] are merely identified, and
      pointed ones uniquely ([cyc_merely_eq], [cyc_pointed_path]).
    - Lemma [lem:sum-cycle-point-contr], for the component of any cycle
      ([sum_cycle_point_contr]).
    - Lemma [lem:deg-m-on-Cyc]: [ρ_m : Cyc_0 →* Cyc_0] and
      [ρ_m : Cyc_n →* Cyc_{mn}] ([rho_Cyc0], [rho_Cyc0_pt], [rho_Cycm],
      [rho_Cycm_pt]).  Instead of the book's explicit equivalence
      [φ(k, r) :≡ k + mr], the identifications come from [lem:IdCycle]:
      [H_{(ℤ,zs)} = {0}], [H_{(Fin n, zs)} = nℤ] ([Hc_Z], [Hc_Fin], from
      3.6), and [H_{ᵐ√t} = mH_t].
    - [X/m] ([Xm]) and lemma [lem:X-mod-m-chosen] ([X_mod_m_chosen]), as in
      the book by Euclidean division: [euclid_div_Sk] for surjectivity, and
      its uniqueness [euclid_unique_Sk] for [small_diff].

    - The identification of [ρ_m] with the degree [m] map,
      [ρ_m c = c dg_m] as maps [S1 → InfCyc] ([root_degree_square]), and
      exercise [xca:pointed-maps-circle] ([root_degree_ptd]).  As in the
      book, it comes down to comparing two loops at [(ℤ, zs)]; we compare
      them through the equivalence [ev_0] of [lem:IdCisZet], using the
      equivariant map [φ] with [φ(0,0) = 0] given by [lem:IdCycle].

    - Construction [thm:fiber-cdg] ([fiber_cdg]): for any cycle [(X,t)],
      [∑_{c:Cyc} ((X,t) = ρ_m(c)) ≃ P × X/m], where [P] says that [m]
      divides the order of [t].  The map sends [(c, e)] to the proof of [P]
      and the class [[e⁻¹(0,y)]] for any [y] in [c] (independent of [y]).
      Instead of the book's inverse (whose second round trip the book
      leaves to the reader), we show that the fibers are contractible:
      over [(P, [x])] the fiber is equivalent to the type of quadruples
      [(c, e, y, e⁻¹(0,y) = x)], which in turn is equivalent to the type of
      pointed cycles in one component, contractible by
      [lem:sum-cycle-point-contr].  That component is the one of the
      orbit of a point [x₀] under [t^m], with [t^m] restricted to it (the
      book's [(V, t^m)]); the standard cycle [ℤ/∼_H] of [cor:set-trunc-cyc]
      would not do here, since as a quotient by a [Prop]-valued relation
      it lives in a higher universe than [(X,t)].
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Spaces.Nat.Core Spaces.Int
  Spaces.Circle Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Nat.Division.
From SymmetryBook Require Export Circle.S07_Permutations.

Local Open Scope uf_scope.

(** ** 3.8 The [m]-th root: coverings over the components of [Cyc] *)

(** Definition [def:Cyc-components]: [Cyc_0] (infinite cycles) and the
    components [Cyc_m] of the standard [m]-cycles ([m = k+1]). *)
Definition Cyc0 `{Univalence} : Type := component Cyc Zcyc.

Definition Cycm `{Univalence} (k : ℕ) : Type := component Cyc (Fincyc k).

(** Construction [con:root]: the [m]-th root of [t : X → X] on
    [𝟙m × X], with [𝟙m] represented as [∑_{i:ℕ} (i < m)] ([FinNat]):
    [(i, x) ↦ (i+1, x)] for [i < m-1] and [(m-1, x) ↦ (0, t(x))]. *)
Section Root.

  Context (k : ℕ) {X : Type}.

  Definition FN : Type := FinNat (S k).

  Definition root (t : X -> X) (w : FN × X) : FN × X
    := match dec (fst (fst w) < k)%nat with
       | inl l => ((S (fst (fst w)); leq_succ l); snd w)
       | inr _ => (fn0 k; t (snd w))
       end.

  Definition root_inv (t' : X -> X) (w : FN × X) : FN × X
    := match fst w with
       | (O; _) => ((k; leq_refl (S k)); t' (snd w))
       | (S i; l) => ((i; leq_succ_l l); snd w)
       end.

  Definition FN_path {i j : ℕ} {l : (i < S k)%nat} {l' : (j < S k)%nat} (e : i = j)
    : ((i; l) : FN) = (j; l')
    := path_sigma_prop (fn_isProp_lt k) (u := (i; l)) (v := (j; l')) e.

  Definition pair_path {u v : FN} {x y : X} (e : u = v) (e' : x = y)
    : ((u; x) : FN × X) = (v; y)
    := ap011 (fun a b => (a; b) : FN × X) e e'.

  (** Lemma [lem:root-pres-equiv], with an explicit inverse. *)
  Definition root_isEquiv (t : X ≃ X) : isEquiv (root (fst t)).
  Proof.
    refine (iso_to_isEquiv _ (root_inv (eqinv (snd t))) _ _).
    - intros [[i l] x]. unfold root. cbn.
      destruct (dec (i < k)%nat) as [l'|nl]; cbn.
      + exact (pair_path (FN_path refl) refl).
      + exact (pair_path (FN_path (leq_antisym (Overture.fst geq_iff_not_lt nl) (leq_pred' l)))
                         (eqinv_l (snd t) x)).
    - intros [[i l] x]. destruct i as [|i]; unfold root_inv, root; cbn.
      + destruct (dec (k < k)%nat) as [l'|_]; [destruct (lt_irrefl k l')|].
        exact (pair_path (FN_path refl) (eqinv_r (snd t) x)).
      + destruct (dec (i < k)%nat) as [l'|nl]; [| destruct (nl (leq_pred' l))].
        exact (pair_path (FN_path refl) refl).
  Defined.

  Definition rootEqv (t : X ≃ X) : (FN × X) ≃ (FN × X)
    := (root (fst t); root_isEquiv t).


  (** Iterating the [m]-th root [m] times gives [(i, x) ↦ (i, t(x))], hence
      the name. *)
  Definition root_up (t : X -> X) (j : ℕ)
    : forall (i : ℕ) (li : (i < S k)%nat) (l : (i + j < S k)%nat) (x : X),
      nat_iter j (root t) (((i; li) : FN); x) = (((i + j)%nat; l) : FN; x).
  Proof.
    induction j as [|j IH]; intros i li l x.
    - exact (pair_path (FN_path (nat_add_zero_r i)^) refl).
    - assert (e : (i + S j = S (i + j))%nat) by exact (nat_add_succ_r i j).
      assert (l' : (i + j < S k)%nat)
        by exact (leq_succ_l (trp (fun n => (S n <= S k)%nat) e l)).
      refine (ap (root t) (IH i li l' x) @ _). unfold root. cbn.
      destruct (dec (i + j < k)%nat) as [l''|nl].
      + exact (pair_path (FN_path e^) refl).
      + destruct (nl (trp (fun n => (n <= k)%nat) e (leq_pred' l))).
  Defined.

  Definition root_last (t : X -> X) (x : X)
    : root t (((k; leq_refl (S k)) : FN); x) = (fn0 k; t x).
  Proof.
    unfold root. cbn.
    destruct (dec (k < k)%nat) as [l'|nl]; [destruct (lt_irrefl k l') | exact refl].
  Defined.

  Definition root_m (t : X -> X) (i : ℕ) (li : (i < S k)%nat) (x : X)
    : nat_iter (S k) (root t) (((i; li) : FN); x) = ((i; li) : FN; t x).
  Proof.
    pose (le_ik := leq_pred' li).
    assert (e : (i + S (k - i) = S k)%nat)
      by exact (nat_add_succ_r i (k - i) @ ap S (nat_add_sub_r_cancel le_ik)).
    refine (ap (fun n => nat_iter n (root t) (((i; li) : FN); x)) e^ @ _).
    refine (nat_iter_add i (S (k - i)) (root t) _ @ _).
    assert (lk : (i + (k - i) < S k)%nat)
      by exact (trp (fun n => (n < S k)%nat) (nat_add_sub_r_cancel le_ik)^ (leq_refl (S k))).
    refine (ap (fun w => nat_iter i (root t) (root t w)) (root_up t (k - i) i li lk x) @ _).
    refine (ap (fun w => nat_iter i (root t) (root t (w; x)))
              (FN_path (l' := leq_refl (S k)) (nat_add_sub_r_cancel le_ik)) @ _).
    refine (ap (fun w => nat_iter i (root t) w) (root_last t x) @ _).
    exact (root_up t i 0%nat (leq_succ (leq_zero_l k)) li (t x)).
  Defined.

End Root.

(** Definition [def:root]: the formal [m]-th root function on [Endo].
    (Placed after [lem:root-pres-equiv]: the section on [ᵐ√t] fixes [X], while [ρ_m] needs [ᵐ√t] for all [X].) *)
Definition rho (k : ℕ) (w : Endo) : Endo := (FN k × fst w; root k (snd w)).

(** Exercise [xca:root-NOT-pres-inv]: [ᵐ√(t⁻¹)] and [ᵐ√t] need not
    commute.  For [m = 2], [X = ℤ] and [t = zs], at [(1, 0)] the two
    composites give [(1, 1)] and [(1, -1)]. *)
Definition root_not_pres_inv
  : ¬ (root 1 zp (root 1 zs (((1%nat; leq_refl 2) : FN 1); iplus 0))
       = root 1 zs (root 1 zp (((1%nat; leq_refl 2) : FN 1); iplus 0))).
Proof.
  intro h. pose (h' := ap (fun w : FN 1 × ℤ => toInt (snd w)) h). cbn in h'.
  exact (trp (fun i : Int => match i with posS _ => True | _ => False end) h' triv).
Defined.

(** Powers of the [m]-th root, for a permutation [t] of a set [X]. *)
Section RootPowers.

  Context `{Univalence} (k : ℕ) {X : Type} (sX : isSet X) (t : X ≃ X).

  Definition sFX : isSet (FN k × X) := Sigma_isSet (FinNat_isSet k) (fun _ => sX).

  Definition Rt : (FN k × X) ≃ (FN k × X) := rootEqv k t.

  Definition pow_comm (a b : ℤ) (y : X) : tpow t a (tpow t b y) = tpow t b (tpow t a y)
    := (tpow_add sX t b a y)^ @ ap (fun w => tpow t w y) (zadd_comm b a) @ tpow_add sX t a b y.

  Definition tpow_neg' (n : ℤ) (y : X) : tpow t n (tpow t (zneg n) y) = y
    := pow_comm n (zneg n) y @ tpow_neg sX t n y.

  (** [(ᵐ√t)^{mj}(i, x) = (i, t^j(x))] for [j : ℕ]. *)
  Definition root_pow_nat (i : ℕ) (li : (i < S k)%nat) (j : ℕ)
    : forall x : X, nat_iter (S k * j)%nat (root k (fst t)) (((i; li) : FN k); x)
                    = ((i; li) : FN k; tpow t (iplus j) x).
  Proof.
    induction j as [|j IH]; intro x.
    - exact (ap (fun n => nat_iter n (root k (fst t)) (((i; li) : FN k); x))
               (nat_mul_zero_r (S k))).
    - refine (ap (fun n => nat_iter n (root k (fst t)) (((i; li) : FN k); x))
                (nat_mul_succ_r (S k) j) @ _).
      refine (nat_iter_add (S k * j)%nat (S k) (root k (fst t)) _ @ _).
      refine (ap (fun w => nat_iter (S k * j)%nat (root k (fst t)) w) (root_m k (fst t) i li x) @ _).
      exact (IH (fst t x) @ ap (fun y => ((i; li) : FN k; y)) (pow_comm (iplus j) (iplus 1) x)).
  Defined.

  Definition zmul_neg (a b : ℤ) : zmul a (zneg b) = zneg (zmul a b)
    := toInt_inj (y := zneg (zmul a b))
         (toInt_zmul _ _ @ ap (int_mul (toInt a)) (toInt_zneg b)
          @ int_mul_neg_r _ _ @ ap int_neg (toInt_zmul a b)^ @ (toInt_zneg _)^).

  (** [(ᵐ√t)^{mq}(i, x) = (i, t^q(x))] for [q : ℤ]. *)
  Definition root_pow (q : ℤ) (w : FN k × X)
    : tpow Rt (zmul (iplus (S k)) q) w = (fst w; tpow t q (snd w)).
  Proof.
    destruct w as [[i li] x]. revert q x.
    refine (ℤ_ind_prop _ (fun q => Pi_isProp (fun x => sFX _ _)) _ _).
    - intros j x. refine (ap (fun n => tpow Rt n _) (iplus_mul (S k) j)^ @ _).
      exact (root_pow_nat i li j x).
    - intros [j] x.
      pose (z := (((i; li) : FN k); tpow t (zneg (iplus j)) x) : FN k × X).
      assert (e : tpow Rt (zmul (iplus (S k)) (iplus j)) z = (((i; li) : FN k); x)).
      { refine (ap (fun n => tpow Rt n z) (iplus_mul (S k) j)^ @ _).
        exact (root_pow_nat i li j _ @ ap (fun y => ((i; li) : FN k; y)) (tpow_neg' _ x)). }
      refine (ap (fun n => tpow Rt n _) (zmul_neg (iplus (S k)) (iplus j)) @ _).
      exact (ap (tpow Rt (zneg (zmul (iplus (S k)) (iplus j)))) e^ @ tpow_neg sFX Rt _ z).
  Defined.

  (** Lemma [lem:m-root-id]: if [(ᵐ√t)^n = id] (and [X] is nonempty), then
      [n = mq] with [t^q = id]; and conversely.
    (Placed before [lem:deg-m-on-Cyc], which uses it.) *)
  Definition m_root_id (n : ℤ) (x0 : X) (h : tpow Rt n = idmap)
    : Ex (fun q : ℤ => (n = zmul (iplus (S k)) q) × (tpow t q = idmap)).
  Proof.
    destruct (euclid_div_Sk n k) as [q [r [lr en]]].
    (* [(ᵐ√t)^{qm+r}(0, x) = (r, t^q(x))] *)
    assert (E : forall x, tpow Rt n (fn0 k; x) = (((r; lr) : FN k); tpow t q x)).
    { intro x. refine (ap (fun w => tpow Rt w (fn0 k; x)) en @ tpow_add sFX Rt _ _ _ @ _).
      refine (ap (tpow Rt (iplus r))
                (ap (fun w => tpow Rt w (fn0 k; x)) (zmul_comm q (iplus (S k)))
                 @ root_pow q (fn0 k; x)) @ _).
      exact (root_up k (fst t) r 0%nat (leq_succ (leq_zero_l k)) lr (tpow t q x)). }
    assert (r0 : r = 0%nat).
    { exact (ap (fun w : FN k × X => fst (fst w)) ((E x0)^ @ ptw h _)). }
    refine (trunc (q; (en @ ap (fun s => zadd (zmul q (iplus (S k))) (iplus s)) r0
                       @ zmul_comm _ _; _))).
    apply ptw_inv. intro x.
    exact (ap (fun w : FN k × X => snd w) ((E x)^ @ ptw h _)).
  Defined.

  Definition m_root_id_conv (q : ℤ) (hq : tpow t q = idmap)
    : tpow Rt (zmul (iplus (S k)) q) = idmap
    := ptw_inv (fun w => root_pow q w @ ap (fun y => (fst w; y)) (ptw hq (snd w))).

  (** Lemma [lem:root-pres-cycle]: the [m]-th root of a cycle is a cycle. *)
  Definition up_conn (a a' : ℕ) (la : (a < S k)%nat) (la' : (a' < S k)%nat) (y : X)
    (le : (a <= a')%nat)
    : fst (conn_by Rt ((((a; la) : FN k); y)) ((((a'; la') : FN k); y))).
  Proof.
    pose (e := nat_add_sub_r_cancel le : (a + (a' - a) = a')%nat).
    pose (l := trp (fun n => (n < S k)%nat) e^ la').
    refine (trunc (iplus (a' - a); _)).
    refine (_ @ (root_up k (fst t) (a' - a) a la l y)^).
    exact (pair_path k (FN_path k e^) refl).
  Defined.

  Definition root_isCycle (cy : isCycle t) : isCycle Rt.
  Proof.
    refine (ptrunc_rec ptrunc_isProp (fun x0 => trunc ((fn0 k; x0) : FN k × X)) (fst cy); _).
    intros [[a la] x] [[a' la'] x'].
    refine (conn_by_trans sFX Rt _ ((((a; la) : FN k); x')) _ _ _).
    - refine (ptrunc_rec ptrunc_isProp _ (snd cy x x')). intros [n e].
      refine (trunc (zmul (iplus (S k)) n; _)).
      exact (ap (fun y => (((a; la) : FN k); y)) e @ (root_pow n ((((a; la) : FN k); x)))^).
    - destruct (leq_dichotomy a a') as [le|gt].
      + exact (up_conn a a' la la' x' le).
      + exact (conn_by_sym sFX Rt _ _ (up_conn a' a la' la x' (leq_succ_l gt))).
  Defined.

  (** The subset [H] of the [m]-th root: [n ∈ H_{ᵐ√t}] iff [n = mq] with
      [q ∈ H_t] ([lem:m-root-id] and its converse). *)
  Definition Ht_root (cy : isCycle t) (n : ℤ)
    : (fst (Ht sFX Rt n) -> Ex (fun q => (n = zmul (iplus (S k)) q) × fst (Ht sX t q)))
      × (Ex (fun q => (n = zmul (iplus (S k)) q) × fst (Ht sX t q)) -> fst (Ht sFX Rt n)).
  Proof.
    refine (fun h => ptrunc_rec ptrunc_isProp (fun x0 => m_root_id n x0 h) (fst cy); _).
    refine (ptrunc_rec (snd (Ht sFX Rt n)) _). intros [q [e hq]].
    exact (trp (fun w => fst (Ht sFX Rt w)) e^ (m_root_id_conv q hq)).
  Defined.

End RootPowers.

(** Identifications of cycles come from identifications in [Endo]. *)
Section CycPaths.

  Context `{Univalence}.

  Definition cyc_endo (c : Cyc) : Endo := (fst (fst c); fst (fst (snd c))).

  Definition CycP (w : Endo) : Type
    := isSet (fst w) × {tE : isEquiv (snd w) & isCycle ((snd w; tE) : fst w ≃ fst w)}.

  Definition CycP_isProp (w : Endo) : isProp (CycP w)
    := prod_isProp (isSet_isProp _)
         (Sigma_isProp (isEquiv_isProp _)
            (fun tE => prod_isProp ptrunc_isProp
                         (Pi_isProp (fun _ => Pi_isProp (fun _ => ptrunc_isProp))))).

  Definition cyc_of (v : {w : Endo & CycP w}) : Cyc
    := ((fst (fst v); fst (snd v)); ((snd (fst v); fst (snd (snd v))); snd (snd (snd v)))).

  Definition cyc_path (c d : Cyc) (e : cyc_endo c = cyc_endo d) : c = d
    := ap cyc_of (path_sigma_prop CycP_isProp
         (u := (cyc_endo c; (snd (fst c); (snd (fst (snd c)); snd (snd c)))))
         (v := (cyc_endo d; (snd (fst d); (snd (fst (snd d)); snd (snd d))))) e).

  Definition ap_carrier_cyc_of {u v : {w : Endo & CycP w}} (P : u = v)
    : ap (fun c : Cyc => fst (fst c)) (ap cyc_of P) = ap (fun w : Endo => fst w) (ap fst P)
    := match P with refl => refl end.

  Definition ap_carrier_cyc_path (c d : Cyc) (e : cyc_endo c = cyc_endo d)
    : ap (fun c : Cyc => fst (fst c)) (cyc_path c d e) = ap (fun w : Endo => fst w) e
    := ap_carrier_cyc_of (path_sigma_prop CycP_isProp
         (u := (cyc_endo c; (snd (fst c); (snd (fst (snd c)); snd (snd c)))))
         (v := (cyc_endo d; (snd (fst d); (snd (fst (snd d)); snd (snd d))))) e)
       @ ap (ap (fun w : Endo => fst w)) (ap_fst_pathpair _ _).

  (** Cycles with the same subset [H] are merely identified
      ([lem:IdCycle]), and pointed cycles even uniquely. *)
  Definition Hiffc (c d : Cyc) : Type
    := Hiff (snd (fst c)) (snd (fst d)) (fst (snd c)) (fst (snd d)).

  Definition cyc_merely_eq (c d : Cyc) (hH : Hiffc c d) : ptrunc (c = d)
    := ptrunc_rec ptrunc_isProp (fun e => trunc (cyc_path c d e))
         (IdCycle_31 (fst (snd c)) (fst (snd d)) (snd (snd c)) (snd (snd d))
            (IdCycle_23 (snd (fst c)) (snd (fst d)) (fst (snd c)) (fst (snd d))
                        (snd (snd c)) (snd (snd d)) hH)).

  Definition cyc_pointed_path (c d : Cyc) (hH : Hiffc c d)
    (x0 : fst (fst c)) (y0 : fst (fst d)) : c = d
    := cyc_path c d (eqinv (snd (endo_paths_eqv _ _))
         (fst (fst (IdCycle_23 (snd (fst c)) (snd (fst d)) (fst (snd c)) (fst (snd d))
                                (snd (snd c)) (snd (snd d)) hH x0 y0)))).

End CycPaths.

(** Lemma [lem:deg-m-on-Cyc]: [ρ_m] maps [Cyc_0] to [Cyc_0] and [Cyc_n] to
    [Cyc_{mn}], as pointed maps.  Instead of the explicit equivalence
    [φ(k, r) :≡ k + mr], we compare the subsets [H] ([lem:IdCycle]):
    [H_{ᵐ√t} = m H_t] by [lem:m-root-id]. *)
Section DegMOnCyc.

  Context `{Univalence} (k : ℕ).

  Definition rho_cyc (c : Cyc) : Cyc
    := ((FN k × fst (fst c); sFX k (snd (fst c)));
        (Rt k (fst (snd c)); root_isCycle k (snd (fst c)) (fst (snd c)) (snd (snd c)))).

  Definition Hc_rho (c : Cyc) (n : ℤ)
    : (fst (Hc (rho_cyc c) n) -> Ex (fun q => (n = zmul (iplus (S k)) q) × fst (Hc c q)))
      × (Ex (fun q => (n = zmul (iplus (S k)) q) × fst (Hc c q)) -> fst (Hc (rho_cyc c) n))
    := Ht_root k (snd (fst c)) (fst (snd c)) (snd (snd c)) n.

  Definition Hiff_rho_Z : Hiffc (rho_cyc Zcyc) Zcyc.
  Proof.
    intro n. refine (fun h => _; fun h => _).
    - refine (snd (Hc_Z n) _).
      refine (ptrunc_rec (ℤ_isSet _ _) _ (fst (Hc_rho Zcyc n) h)). intros [q [e hq]].
      exact (e @ ap (zmul (iplus (S k))) (fst (Hc_Z q) hq)).
    - apply (snd (Hc_rho Zcyc n)). apply trunc.
      exact (iplus 0; (fst (Hc_Z n) h; snd (Hc_Z _) refl)).
  Defined.

  Definition rho_Z_path : rho_cyc Zcyc = Zcyc
    := cyc_pointed_path (rho_cyc Zcyc) Zcyc Hiff_rho_Z (fn0 k; iplus 0) (iplus 0).

  Definition rho_Cyc0 (w : Cyc0) : Cyc0
    := (rho_cyc (fst w);
        ptrunc_rec ptrunc_isProp (fun p => trunc (ap rho_cyc p ⋅ rho_Z_path⁻¹)) (snd w)).

  Definition rho_Cyc0_pt : rho_Cyc0 (Zcyc; trunc refl) = (Zcyc; trunc refl)
    := path_sigma_prop (fun _ => ptrunc_isProp) (u := rho_Cyc0 (Zcyc; trunc refl))
         (v := (Zcyc; trunc refl)) rho_Z_path.

End DegMOnCyc.


Section DegMOnCycN.

  Context `{Univalence} (k j : ℕ).

  Definition zmul_assoc_nat (a b : ℕ) (p : ℤ)
    : zmul (iplus a) (zmul (iplus b) p) = zmul (iplus (a * b)%nat) p.
  Proof.
    apply toInt_inj.
    refine (toInt_zmul (iplus a) (zmul (iplus b) p)
            @ ap (int_mul (int_of_nat a)) (toInt_zmul (iplus b) p) @ _).
    refine (int_mul_assoc _ _ _ @ _ @ (toInt_zmul (iplus (a * b)%nat) p)^).
    exact (ap (fun z => int_mul z (toInt p)) (int_nat_mul a b)).
  Defined.

  (** For [m = k+1] and [n = j+1], [mn = (j + k(j+1)) + 1] by definition. *)
  Definition jmn : ℕ := (j + k * S j)%nat.

  Definition Hiff_rho_Fin : Hiffc (rho_cyc k (Fincyc j)) (Fincyc jmn).
  Proof.
    intro n. refine (fun h => _; fun h => _).
    - change (fst (Hc (Fincyc jmn) n)).
      refine (snd (Hc_Fin jmn n) _).
      refine (ptrunc_rec ptrunc_isProp _ (fst (Hc_rho k (Fincyc j) n) h)). intros [q [e hq]].
      refine (ptrunc_rec ptrunc_isProp _ (fst (Hc_Fin j q) hq)). intros [p ep].
      exact (trunc (p; e @ ap (zmul (iplus (S k))) ep @ zmul_assoc_nat (S k) (S j) p)).
    - change (fst (Hc (rho_cyc k (Fincyc j)) n)).
      refine (snd (Hc_rho k (Fincyc j) n) _).
      refine (ptrunc_rec ptrunc_isProp _ (fst (Hc_Fin jmn n) h)). intros [p ep].
      refine (trunc (zmul (iplus (S j)) p; (ep @ (zmul_assoc_nat (S k) (S j) p)^; _))).
      exact (snd (Hc_Fin j _) (trunc (p; refl))).
  Defined.

  Definition rho_Fin_path : rho_cyc k (Fincyc j) = Fincyc jmn
    := cyc_pointed_path _ _ Hiff_rho_Fin (fn0 k; fin_zero) fin_zero.

  Definition rho_Cycm (w : Cycm j) : Cycm jmn
    := (rho_cyc k (fst w);
        ptrunc_rec ptrunc_isProp (fun p => trunc (ap (rho_cyc k) p ⋅ rho_Fin_path⁻¹)) (snd w)).

  Definition rho_Cycm_pt : rho_Cycm (Fincyc j; trunc refl) = (Fincyc jmn; trunc refl)
    := path_sigma_prop (fun _ => ptrunc_isProp) (u := rho_Cycm (Fincyc j; trunc refl))
         (v := (Fincyc jmn; trunc refl)) rho_Fin_path.

End DegMOnCycN.

(** The identification of [ρ_m] with the degree [m] map ([ρ_m c = c dg_m],
    as maps [S1 → Cyc_0]), and exercise [xca:pointed-maps-circle].  We work
    with [InfCyc] (the component of [Endo]), on which [c] is defined. *)
Section RootDegree.

  Context `{Univalence} (k : ℕ).

  Definition EZ : rho k Zs = Zs := ap cyc_endo (rho_Z_path k).

  Definition rhoIC (w : InfCyc) : InfCyc
    := (rho k (fst w);
        ptrunc_rec ptrunc_isProp (fun p => trunc (ap (rho k) p ⋅ EZ⁻¹)) (snd w)).

  Definition endo_fun_ap_rho {w w' : Endo} (E : w = w') (v : FN k × fst w)
    : endo_fun (ap (rho k) E) v = (fst v; endo_fun E (snd v)).
  Proof.
    destruct E. refine (endo_fun_trp _ v @ _).
    exact (ap (fun y => (fst v; y) : FN k × fst w) (endo_fun_trp (refl w) (snd v)))^.
  Defined.

  Definition endo_fun_endo_path {X Y : Type} {t : X -> X} {u : Y -> Y} (e : X ≃ Y)
    (h : fst e ∘ t = u ∘ fst e) (x : X) : endo_fun (endo_path e h) x = fst e x
    := endo_fun_trp _ x @ ap (fun r => transport idmap r x) (ap_fst_endo_path e h)
       @ ptw (ap fst (ptoe_etop e)) x.

  Definition endo_fun_inv {X Y : Type} {t : X -> X} {u : Y -> Y}
    (p : ((X; t) : Endo) = (Y; u)) (y : Y) : endo_fun p (endo_fun p^ y) = y
    := (endo_fun_concat p^ p y)^ @ ap (fun r => endo_fun r y) (concat_Vp p)
       @ endo_fun_trp refl y.

  (** The function underlying [EZ]: the unique equivariant [φ] with
      [φ(0, 0) = 0] (in the book, [φ(k, r) = k + mr]). *)
  Local Notation phi := (endo_fun EZ).

  Definition endo_fun_comm {X Y : Type} {t : X -> X} {u : Y -> Y}
    (p : ((X; t) : Endo) = (Y; u)) (x : X) : endo_fun p (t x) = u (endo_fun p x).
  Proof.
    assert (G : forall (w : Endo) (q : ((X; t) : Endo) = w),
               @endo_fun _ X (fst w) t (snd w) q (t x)
               = snd w (@endo_fun _ X (fst w) t (snd w) q x))
      by (intros w q; destruct q; exact refl).
    exact (G (Y; u) p).
  Defined.

  Definition phi_comm (w : FN k × ℤ) : phi (root k zs w) = zs (phi w)
    := endo_fun_comm EZ w.

  Definition ap_cyc_endo_cyc_of {u v : {w : Endo & CycP w}} (P : u = v)
    : ap cyc_endo (ap cyc_of P) = ap fst P
    := match P with refl => refl end.

  Definition ap_cyc_endo_cyc_path (c d : Cyc) (E : cyc_endo c = cyc_endo d)
    : ap cyc_endo (cyc_path c d E) = E
    := ap_cyc_endo_cyc_of (path_sigma_prop CycP_isProp
         (u := (cyc_endo c; (snd (fst c); (snd (fst (snd c)); snd (snd c)))))
         (v := (cyc_endo d; (snd (fst d); (snd (fst (snd d)); snd (snd d))))) E)
       @ ap_fst_pathpair _ _.

  Definition phi_00 : phi (fn0 k; iplus 0) = iplus 0.
  Proof.
    unfold EZ, rho_Z_path, cyc_pointed_path.
    rewrite ap_cyc_endo_cyc_path.
    refine (ap (fun w : {e : (FN k × ℤ) ≃ ℤ & fst e ∘ root k zs = zs ∘ fst e}
                  => fst (fst w) (fn0 k; iplus 0))
              (eqinv_r (snd (endo_paths_eqv (root k zs) zs)) _) @ _).
    exact (snd (fst (IdCycle_23 (snd (fst (rho_cyc k Zcyc))) (snd (fst Zcyc))
                      (fst (snd (rho_cyc k Zcyc))) (fst (snd Zcyc))
                      (snd (snd (rho_cyc k Zcyc))) (snd (snd Zcyc))
                      (Hiff_rho_Z k) (fn0 k; iplus 0) (iplus 0)))).
  Defined.

  Definition PZ : rhoIC c0 = c0
    := path_sigma_prop (fun _ => ptrunc_isProp) (u := rhoIC c0) (v := c0) EZ.

  Definition ev0_endo {w1 w2 : InfCyc} (r : w1 = w2) (x : carrier_IC w1)
    : trp carrier_IC r x = endo_fun (ap fst r) x.
  Proof.
    refine (transport_compose idmap carrier_IC r x @ _).
    refine (ap (fun q => transport idmap q x) (ap_compose fst (fun w : Endo => fst w) r) @ _).
    exact (endo_fun_trp _ x)^.
  Defined.

  Definition phi_comm' (w : FN k × ℤ) : phi (fst (Rt k zsEqv) w) = fst zsEqv (phi w)
    := phi_comm w.

  Definition loops_compare
    : ev0 c0 (PZ^ @ ap rhoIC cloop @ PZ) = ev0 c0 (ap c (loopZ (iplus (S k)))).
  Proof.
    refine (_ @ (ev0_ap_c_loopZ (iplus (S k)))^).
    unfold ev0. refine (ev0_endo _ _ @ _).
    refine (ap (fun r => endo_fun r (iplus 0))
              (ap_pp fst (PZ^ @ ap rhoIC cloop) PZ
               @ ap (fun r => r @ ap fst PZ) (ap_pp fst PZ^ (ap rhoIC cloop))) @ _).
    refine (endo_fun_concat _ _ _ @ _).
    refine (ap (endo_fun (ap fst PZ)) (endo_fun_concat _ _ _) @ _).
    pose (aPZ := ap_fst_pathpair (Y := fun x : Endo => ptrunc (Zs = x)) _ _ : ap fst PZ = EZ).
    refine (ap (fun r => endo_fun r _) aPZ @ _).
    assert (w0 : endo_fun (ap fst PZ^) (iplus 0) = (fn0 k; iplus 0)).
    { refine (ap (fun r => endo_fun r (iplus 0)) (ap_V fst PZ @ ap inverse aPZ) @ _).
      refine (ap (endo_fun EZ^) phi_00^ @ _).
      refine (ap (fun r => endo_fun EZ^ (endo_fun r (fn0 k; iplus 0))) (inv_V EZ)^ @ _).
      exact (endo_fun_inv EZ^ _). }
    refine (ap (fun v => endo_fun EZ (endo_fun (ap fst (ap rhoIC cloop)) v)) w0 @ _).
    assert (y : endo_fun (ap fst (ap rhoIC cloop)) (fn0 k; iplus 0) = (fn0 k; zp (iplus 0))).
    { refine (ap (fun r => endo_fun r (fn0 k; iplus 0))
                ((ap_compose rhoIC fst cloop)^ @ ap_compose fst (rho k) cloop) @ _).
      refine (endo_fun_ap_rho _ _ @ _).
      refine (ap (fun z => ((fn0 k; z) : FN k × ℤ)) _).
      refine (ap (fun r => endo_fun r (iplus 0)) (ap_fst_pathpair _ _) @ _).
      exact (endo_fun_endo_path zpEqv _ (iplus 0)). }
    refine (ap (endo_fun EZ) y @ _).
    assert (rp : tpow (Rt k zsEqv) (zmul (iplus (S k)) (iminus (negN 1))) (fn0 k; iplus 0)
                 = (fn0 k; zp (iplus 0))).
    { refine (root_pow k ℤ_isSet zsEqv _ _ @ _).
      exact (ap (fun z => ((fn0 k; z) : FN k × ℤ)) (eqinv_mkEqv zs zp zp_zs zs_zp _)). }
    refine (ap phi rp^ @ _).
    refine (tpow_comm_map ℤ_isSet (Rt k zsEqv) zsEqv phi phi_comm' _ _ @ _).
    refine (ap (tpow zsEqv _) phi_00 @ _).
    refine (zadd_0_l _ @ _).
    exact (zmul_neg (iplus (S k)) (iplus 1)).
  Defined.

  Definition loops_eq : PZ^ @ ap rhoIC cloop @ PZ = ap c (loopZ (iplus (S k)))
    := Eqv_inj ((ev0 c0; ev0_isEquiv c0) : (c0 = c0) ≃ carrier_IC c0) loops_compare.

  Definition conj_back {A : Type} {a b : A} (p : a = b) (X : a = a) (Z : b = b)
    (e : p^ @ X @ p = Z) : X = p @ Z @ p^.
  Proof.
    destruct e. destruct p. rewrite !concat_p1, !concat_1p. exact refl.
  Defined.

  Definition square_loop
    : ap (fun z => rhoIC (c z)) loop
      = PZ⁻¹ ⋅ (ap (fun z => c (dg (S k) z)) loop ⋅ PZ).
  Proof.
    refine (ap_compose c rhoIC loop @ ap (ap rhoIC) (S1_rec_loop InfCyc c0 cloop) @ _).
    refine (conj_back PZ _ _ loops_eq @ _).
    refine (ap (fun Y => PZ @ Y @ PZ^)
              (ap_compose (dg (S k)) c loop
               @ ap (ap c) (S1_rec_loop S1 base (loopZ (iplus (S k)))))^ @ _).
    exact (trans_is_concat _ _ @ ap (fun r => r @ PZ^) (trans_is_concat PZ _))^.
  Defined.

  (** [ρ_m c = c dg_m] as maps [S1 → InfCyc]. *)
  Definition root_degree_square : (fun z => rhoIC (c z)) = (fun z => c (dg (S k) z))
    := S1_fun_path (f := fun z => rhoIC (c z)) (g := fun z => c (dg (S k) z)) PZ square_loop.

  (** Exercise [xca:pointed-maps-circle]: the same as pointed maps. *)
  Definition rho_c_ptd : S1star →* ((InfCyc; c0) : Ustar)
    := ((fun z => rhoIC (c z)); PZ⁻¹).

  Definition c_dg_ptd : S1star →* ((InfCyc; c0) : Ustar)
    := ((fun z => c (dg (S k) z)); refl).

  Definition root_degree_ptd : rho_c_ptd = c_dg_ptd
    := eqinv (snd (ptw_star rho_c_ptd c_dg_ptd))
         (S1_htpy (f := fun z => rhoIC (c z)) (g := fun z => c (dg (S k) z)) PZ square_loop;
          trans_Vp PZ).

End RootDegree.

Section SumCyclePoint.

  Context `{Univalence}.

  (** Lemma [lem:sum-cycle-point-contr]: for any cycle [c], the type of
      pointed cycles in the component of [c] is contractible. *)
  Definition sum_cycle_point_contr (c : Cyc)
    : isContr {w : component Cyc c & fst (fst (fst w))}.
  Proof.
    refine (ptrunc_rec (isContr_isProp _) _ (fst (snd (snd c)))). intro x0.
    refine (((c; trunc refl); x0); _).
    intros [[d m] y].
    pose (hH := IdCycle_12 (snd (fst c)) (snd (fst d)) (fst (snd c)) (fst (snd d))
                  (ptrunc_rec ptrunc_isProp (fun p => trunc (ap cyc_endo p)) m) : Hiffc c d).
    pose (z := fst (IdCycle_23 (snd (fst c)) (snd (fst d)) (fst (snd c)) (fst (snd d))
                      (snd (snd c)) (snd (snd d)) hH x0 y)).
    pose (E := eqinv (snd (endo_paths_eqv _ _)) (fst z)).
    pose (P := path_sigma_prop (fun _ => ptrunc_isProp)
                 (u := (c; trunc refl) : component Cyc c) (v := (d; m)) (cyc_path c d E)).
    refine (pathpair P _).
    refine (transport_compose idmap (fun w : component Cyc c => fst (fst (fst w))) P x0 @ _).
    refine (ap (fun r => transport idmap r x0)
              (ap_compose fst (fun c : Cyc => fst (fst c)) P
               @ ap (ap (fun c : Cyc => fst (fst c))) (ap_fst_pathpair _ _)
               @ ap_carrier_cyc_path c d E) @ _).
    refine ((endo_fun_trp E x0)^ @ _).
    exact (ap (fun w : {e : _ & _} => fst (fst w) x0) (eqinv_r (snd (endo_paths_eqv _ _)) (fst z))
           @ snd z).
  Defined.

End SumCyclePoint.

(** Integer arithmetic used below, via [toInt]. *)
Definition zmul_add (a b c : ℤ) : zmul a (zadd b c) = zadd (zmul a b) (zmul a c).
Proof.
  apply toInt_inj.
  refine (toInt_zmul _ _ @ ap (int_mul (toInt a)) (toInt_zadd b c) @ int_dist_l _ _ _ @ _).
  exact (ap011 int_add (toInt_zmul a b)^ (toInt_zmul a c)^ @ (toInt_zadd _ _)^).
Defined.

(** If [i, j < m] and [i - j = mu], then [i = j]. *)
Definition small_diff (k i j : ℕ) (li : (i < S k)%nat) (lj : (j < S k)%nat) (u : ℤ)
  (e : zadd (iplus i) (zneg (iplus j)) = zmul (iplus (S k)) u) : i = j.
Proof.
  refine (snd (euclid_unique_Sk (iplus 0) u i j li lj _)).
  apply toInt_inj.
  refine (toInt_zadd _ _ @ ap (fun t => int_add t _) (toInt_zmul _ _) @ _
          @ (toInt_zadd _ _)^).
  refine (_ @ ap (fun t => int_add t _)
                (ap toInt e @ toInt_zmul _ _ @ int_mul_comm _ _ @ (toInt_zmul u _)^)).
  rewrite toInt_zadd, toInt_zneg, <- int_add_assoc, int_add_neg_l, int_add_0_r.
  exact refl.
Defined.

(** The set [X/m :≡ X/∼_m], with [x ∼_m x'] iff [x' = t^{mr}(x)] for some
    [r : ℤ], and lemma [lem:X-mod-m-chosen]. *)
Section XmodM.

  Context `{Univalence} (k : ℕ) {X : Type} (sX : isSet X) (t : X ≃ X) (cy : isCycle t).

  Definition simm (x x' : X) : PropU
    := (ptrunc {r : ℤ & x' = tpow t (zmul (iplus (S k)) r) x}; ptrunc_isProp).

  Definition simm_refl (x : X) : fst (simm x x) := trunc (iplus 0; refl).

  Definition simm_sym (x x' : X) (h : fst (simm x x')) : fst (simm x' x).
  Proof.
    refine (ptrunc_rec ptrunc_isProp _ h). intros [r e].
    refine (trunc (zneg r; _)).
    refine ((tpow_neg sX t _ x)^ @ _).
    exact (ap (tpow t (zneg (zmul (iplus (S k)) r))) e^
           @ ap (fun w => tpow t w x') (zmul_neg _ _)^).
  Defined.

  Definition simm_trans (x x' x'' : X) (h : fst (simm x x')) (h' : fst (simm x' x''))
    : fst (simm x x'').
  Proof.
    refine (ptrunc_rec ptrunc_isProp _ h). intros [r e].
    refine (ptrunc_rec ptrunc_isProp _ h'). intros [r' e'].
    refine (trunc (zadd r r'; _)).
    refine (e' @ ap (tpow t _) e @ (tpow_add sX t _ _ x)^ @ _).
    exact (ap (fun w => tpow t w x) (zmul_add _ _ _)^).
  Defined.

  Definition Xm : Type := quot simm.

  Definition clsm (x : X) : Xm := cls simm x.

  Definition clsm_iff (x x' : X)
    : (clsm x = clsm x' -> fst (simm x x')) × (fst (simm x x') -> clsm x = clsm x')
    := cls_eq_iff simm simm_refl simm_sym simm_trans x x'.

  (** [P]: [m] divides the order of [t], i.e. [H_t ⊆ mℤ]. *)
  Definition Pdiv : Type
    := forall n, fst (Ht sX t n) -> Ex (fun q => n = zmul (iplus (S k)) q).

  Definition fXm (x0 : X) (i : FN k) : Xm := clsm (tpow t (iplus (fst i)) x0).

  Definition fXm_surj (x0 : X) : isSurj (fXm x0).
  Proof.
    refine (im_ind simm _ (fun _ => ptrunc_isProp) _). intro x.
    refine (ptrunc_rec ptrunc_isProp _ (snd cy x0 x)). intros [n en].
    destruct (euclid_div_Sk n k) as [q [r [lr e]]].
    refine (trunc (((r; lr) : FN k); _)).
    apply (snd (clsm_iff _ _)).
    refine (simm_sym _ _ (trunc (q; en @ _))).
    refine (ap (fun w => tpow t w x0) (e @ zadd_comm _ _) @ _).
    exact (tpow_add sX t _ _ x0 @ ap (fun w => tpow t w _) (zmul_comm q (iplus (S k)))).
  Defined.

  Definition fXm_inj (hP : Pdiv) (x0 : X) : isInj (fXm x0).
  Proof.
    apply (cancel_isInj (quot_isSet simm)). intros [i li] [j lj] e.
    apply (path_sigma_prop (fn_isProp_lt k)). cbn.
    refine (ptrunc_rec (ℕ_isSet _ _) _ (fst (clsm_iff _ _) e)). intros [r er].
    pose (d := zadd (zadd (iplus i) (zmul (iplus (S k)) r)) (zneg (iplus j))).
    assert (ed : tpow t d x0 = x0).
    { refine (tpow_add sX t _ _ x0 @ _).
      refine (ap (tpow t (zneg (iplus j))) (tpow_add sX t _ _ x0 @ er^) @ _).
      exact (tpow_neg sX t _ x0). }
    refine (ptrunc_rec (ℕ_isSet _ _) _ (hP d (snd (Ht_point sX t cy x0 d) ed))). intros [s es].
    refine (small_diff k i j li lj (zadd s (zneg r)) _).
    refine (_ @ ap (zadd _) (zmul_neg _ _)^ @ (zmul_add _ _ _)^).
    refine (_ @ ap (fun w => zadd w (zneg (zmul (iplus (S k)) r))) es).
    apply toInt_inj. unfold d.
    repeat first [rewrite toInt_zadd | rewrite toInt_zneg].
    rewrite <- (int_add_assoc (toInt (iplus i)) (toInt (zmul (iplus (S k)) r))).
    rewrite (int_add_comm (toInt (zmul (iplus (S k)) r)) (int_neg (toInt (iplus j)))).
    rewrite int_add_assoc, <- (int_add_assoc _ (toInt (zmul (iplus (S k)) r))).
    rewrite int_add_neg_r, int_add_0_r. exact refl.
  Defined.

  Definition X_mod_m_chosen (hP : Pdiv) (x0 : X) : isEquiv (fXm x0)
    := inj_surj_isEquiv (fXm_inj hP x0) (fXm_surj x0).

End XmodM.

(** Construction [thm:fiber-cdg]: for any cycle [(X,t)], the fiber
    [∑_{c:Cyc} ((X,t) = ρ_m(c))] of [ρ_m] is equivalent to [P × X/m], where
    [P] says that [m] divides the order of [t].  The map sends [(c, e)] to
    the proof of [P] (by [lem:m-root-id]) and the class [[e⁻¹(0,y)]] for
    any [y] in [c].  Instead of the book's inverse, we show that the fibers
    of this map are contractible: the fiber over [(P, [x])] is equivalent
    to the type of pointed cycles in the component of the cycles with
    [H = {q | t^{mq} = id}], which is contractible by
    [lem:sum-cycle-point-contr].  A cycle in that component is the orbit of
    a point [x₀] under [t^m], with [t^m] restricted to it (the book's
    [(V, t^m)], below); the standard cycle [ℤ/∼_H] of [cor:set-trunc-cyc]
    would not do, since it lives in a higher universe than [(X,t)]. *)
Section FiberCdg.

  Context `{Univalence} (k : ℕ) (d : Cyc).

  Local Notation X := (fst (fst d)).
  Local Notation sX := (snd (fst d)).
  Local Notation t := (fst (snd d)).
  Local Notation cy := (snd (snd d)).
  Local Notation Y c := (fst (fst c)).

  Definition Fib : Type := {c : Cyc & d = rho_cyc k c}.

  Definition Einv {c : Cyc} (e : d = rho_cyc k c) : FN k × Y c -> X
    := endo_fun (ap cyc_endo e)^.

  Definition endo_fun_retr {A B : Type} {a : A -> A} {b : B -> B}
    (p : ((A; a) : Endo) = (B; b)) (v : A) : endo_fun p^ (endo_fun p v) = v
    := ap (fun r => endo_fun p^ (endo_fun r v)) (inv_V p)^ @ endo_fun_inv p^ v.

  Definition Einv_inj {c : Cyc} (e : d = rho_cyc k c) {v v' : FN k × Y c}
    (h : Einv e v = Einv e v') : v = v'
    := (endo_fun_retr (ap cyc_endo e)^ v)^
       @ ap (endo_fun ((ap cyc_endo e)^)^) h @ endo_fun_retr (ap cyc_endo e)^ v'.

  Definition Einv_pow {c : Cyc} (e : d = rho_cyc k c) (n : ℤ) (v : FN k × Y c)
    : Einv e (tpow (Rt k (fst (snd c))) n v) = tpow t n (Einv e v)
    := tpow_comm_map sX (Rt k (fst (snd c))) t (Einv e)
         (endo_fun_comm (ap cyc_endo e)^) n v.

  Definition hiff_e {c : Cyc} (e : d = rho_cyc k c) : Hiffc d (rho_cyc k c)
    := IdCycle_12 _ _ _ _ (trunc (ap cyc_endo e)).

  Definition Pdiv_F (w : Fib) : Pdiv k sX t
    := fun n h => ptrunc_rec ptrunc_isProp (fun z => trunc (fst z; fst (snd z)))
                    (fst (Hc_rho k (fst w) n) (fst (hiff_e (snd w) n) h)).

  Definition gpt {c : Cyc} (e : d = rho_cyc k c) (y : Y c) : Xm k t
    := clsm k t (Einv e (fn0 k; y)).

  Definition gpt_wconst {c : Cyc} (e : d = rho_cyc k c) : wconst (gpt e).
  Proof.
    intros y y'. apply (snd (clsm_iff k sX t _ _)).
    refine (ptrunc_rec ptrunc_isProp _ (snd (snd (snd c)) y y')). intros [r er].
    refine (trunc (r; _)).
    refine (ap (fun z => Einv e (fn0 k; z)) er @ _).
    refine (ap (Einv e) (root_pow k (snd (fst c)) (fst (snd c)) r (fn0 k; y))^ @ _).
    exact (Einv_pow e _ _).
  Defined.

  Definition g_F (w : Fib) : Xm k t
    := wconst_elim (quot_isSet (simm k t)) (gpt_wconst (snd w)) (fst (snd (snd (fst w)))).

  Definition g_F_pt (w : Fib) (y : Y (fst w)) : g_F w = gpt (snd w) y
    := ap (wconst_elim (quot_isSet (simm k t)) (gpt_wconst (snd w))) (ptrunc_isProp _ _)
       @ wconst_elim_trunc _ _ y.

  Definition G_F (w : Fib) : Pdiv k sX t × Xm k t := (Pdiv_F w; g_F w).

  (** The subgroup [{q | t^{mq} = id}] of [ℤ], the [H] of the cycles [c]
      with [(X,t)] identified with [ρ_m(c)]. *)
  Local Notation Hs q := (Ht sX t (zmul (iplus (S k)) q)).

  Definition Hs_0 : fst (Hs (iplus 0)) := fst (fst (Ht_subgroup sX t)).

  Definition Hs_add (n q : ℤ) (hn : fst (Hs n)) (hq : fst (Hs q)) : fst (Hs (zadd n q))
    := trp (fun z => fst (Ht sX t z)) (zmul_add _ _ _)^
         (snd (fst (Ht_subgroup sX t)) _ _ hn hq).

  Definition Hs_neg (n : ℤ) (hn : fst (Hs n)) : fst (Hs (zneg n))
    := trp (fun z => fst (Ht sX t z)) (zmul_neg _ _)^ (snd (Ht_subgroup sX t) _ hn).

  (** A cycle [c₀] whose [H] is [{q | t^{mq} = id}] determines the
      component of the cycles [c] with [(X,t)] identified with [ρ_m(c)]. *)

  Definition Ht_root_cancel (c : Cyc) (q : ℤ)
    (h : fst (Hc (rho_cyc k c) (zmul (iplus (S k)) q))) : fst (Hc c q).
  Proof.
    apply ptw_inv. intro y.
    exact (ap (fun v : FN k × Y c => snd v)
              ((root_pow k (snd (fst c)) (fst (snd c)) q (fn0 k; y))^ @ ptw h _)).
  Defined.

  Definition hiff_comp (c0 : Cyc)
    (Hc0 : forall q, (fst (Hc c0 q) -> fst (Hs q)) × (fst (Hs q) -> fst (Hc c0 q)))
    (c : Cyc) (hH : Hiffc d (rho_cyc k c)) : ptrunc (c0 = c).
  Proof.
    apply cyc_merely_eq. intro q. refine (fun h => _; fun h => _).
    - exact (Ht_root_cancel c q (fst (hH (zmul (iplus (S k)) q)) (fst (Hc0 q) h))).
    - pose (h1 := m_root_id_conv k (snd (fst c)) (fst (snd c)) q h).
      pose (h2 := snd (hH (zmul (iplus (S k)) q)) h1).
      exact (snd (Hc0 q) h2).
  Defined.

  Definition comp_hiff (c0 : Cyc)
    (Hc0 : forall q, (fst (Hc c0 q) -> fst (Hs q)) × (fst (Hs q) -> fst (Hc c0 q)))
    (hP : Pdiv k sX t) (c : Cyc) (m0 : ptrunc (c0 = c))
    : Hiffc d (rho_cyc k c).
  Proof.
    pose (hc := IdCycle_12 _ _ _ _ (ptrunc_rec ptrunc_isProp
                  (fun p => trunc (ap cyc_endo p)) m0) : Hiffc c0 c).
    intro n. refine (fun h => _; fun h => _).
    - refine (ptrunc_rec (snd (Hc (rho_cyc k c) n)) _ (hP n h)). intros [q eq].
      apply (snd (Hc_rho k c n)). refine (trunc (q; (eq; _))).
      exact (fst (hc q) (snd (Hc0 q) (trp (fun z => fst (Ht sX t z)) eq h))).
    - refine (ptrunc_rec (snd (Ht sX t n)) _ (fst (Hc_rho k c n) h)). intros [q [eq hq]].
      exact (trp (fun z => fst (Ht sX t z)) eq^ (fst (Hc0 q) (snd (hc q) hq))).
  Defined.

End FiberCdg.

Definition cyc_path_ap `{Univalence} {c c' : Cyc} (p : c = c')
  : cyc_path c c' (ap cyc_endo p) = p.
Proof.
  destruct p. unfold cyc_path, path_sigma_prop. cbn.
  match goal with |- context [CycP_isProp ?w ?a ?b] => generalize (CycP_isProp w a b) end.
  intro q. assert (E : q = refl) by apply (prop_is_set (CycP_isProp _)).
  rewrite E. exact refl.
Defined.

Section FiberCdg2.

  Context `{Univalence} (k : ℕ) (d : Cyc).

  Local Notation X := (fst (fst d)).
  Local Notation sX := (snd (fst d)).
  Local Notation t := (fst (snd d)).
  Local Notation cy := (snd (snd d)).
  Local Notation Y c := (fst (fst c)).

  (** The orbit of [x₀] under [t^m], with [t^m] restricted to it: a cycle in
      the universe of [X] whose [H] is [{q | t^{mq} = id}]. *)
  Definition tm : X -> X := tpow t (iplus (S k)).
  Definition tm_inv : X -> X := tpow t (zneg (iplus (S k))).

  Definition tpow_neg_r (n : ℤ) (y : X) : tpow t n (tpow t (zneg n) y) = y
    := (tpow_add sX t (zneg n) n y)^
       @ ap (fun w => tpow t w y) (zadd_comm (zneg n) n @ zadd_zneg n).

  Definition tmEqv : X ≃ X
    := mkEqv tm tm_inv (fun x => tpow_neg sX t _ x) (fun x => tpow_neg_r _ x).

  Definition eqinv_zaddEqv (z w : ℤ) : eqinv (snd (zaddEqv z)) w = zadd w (zneg z).
  Proof.
    refine (eqinv_mkEqv (zadd z) (fun w => fromInt (int_add (int_neg (toInt z)) (toInt w)))
              _ _ w @ _).
    apply toInt_inj. rewrite toInt_fromInt, toInt_zadd, toInt_zneg.
    exact (int_add_comm _ _).
  Defined.

  Definition tpow_tm (r : ℤ) (x : X) : tpow tmEqv r x = tpow t (zmul (iplus (S k)) r) x.
  Proof.
    revert r. refine (ℤ_ind_prop _ (fun r => sX _ _) _ _).
    - intro j. induction j as [|j IH]; [exact refl|].
      refine (ap tm IH @ (tpow_add sX t _ _ x)^ @ _).
      exact (ap (fun w => tpow t w x) (zadd_comm _ _)).
    - intros [j]. induction j as [|j IH]; [exact refl|].
      refine (eqinv_mkEqv tm tm_inv _ _ _ @ ap tm_inv IH @ (tpow_add sX t _ _ x)^ @ _).
      exact (ap (fun w => tpow t w x) (eqinv_zaddEqv _ _)^).
  Defined.

  Section Orbit.

    Context (x0 : X).

    Definition XV : Type := {x : X & fst (simm k t x0 x)}.

    Definition sXV : isSet XV := Sigma_isSet sX (fun _ => prop_is_set ptrunc_isProp).

    Definition XV_path {v v' : XV} (e : fst v = fst v') : v = v'
      := path_sigma_prop (fun _ => ptrunc_isProp) e.

    Definition tV (v : XV) : XV
      := (tm (fst v); simm_trans k sX t x0 (fst v) _ (snd v) (trunc (iplus 1; refl))).

    Definition tVi (v : XV) : XV
      := (tm_inv (fst v);
          simm_trans k sX t x0 (fst v) _ (snd v)
            (trunc (zneg (iplus 1); ap (fun w => tpow t w (fst v)) (zmul_neg _ _)^))).

    Definition tVEqv : XV ≃ XV
      := mkEqv tV tVi (fun v => XV_path (v := tVi (tV v)) (v' := v) (tpow_neg sX t _ (fst v)))
               (fun v => XV_path (v := tV (tVi v)) (v' := v) (tpow_neg_r _ (fst v))).

    Definition fst_tpow_tV (r : ℤ) (v : XV)
      : fst (tpow tVEqv r v) = tpow t (zmul (iplus (S k)) r) (fst v)
      := tpow_comm_map sX tVEqv tmEqv fst (fun v => refl) r v @ tpow_tm r (fst v).

    Definition XV_isCycle : isCycle tVEqv.
    Proof.
      refine (trunc ((x0; simm_refl k t x0) : XV); fun v v' => _).
      refine (ptrunc_rec ptrunc_isProp _
                (simm_trans k sX t _ _ _ (simm_sym k sX t _ _ (snd v)) (snd v'))).
      intros [r er]. exact (trunc (r; XV_path (er @ (fst_tpow_tV r v)^))).
    Defined.

    Definition cV : Cyc := ((XV; sXV); (tVEqv; XV_isCycle)).

    Definition HcV (q : ℤ)
      : (fst (Hc cV q) -> fst (Ht sX t (zmul (iplus (S k)) q)))
        × (fst (Ht sX t (zmul (iplus (S k)) q)) -> fst (Hc cV q)).
    Proof.
      refine (fun h => _; fun h => _).
      - apply (snd (Ht_point sX t cy x0 _)).
        exact ((fst_tpow_tV q (x0; simm_refl k t x0))^
               @ ap fst (ptw h (x0; simm_refl k t x0))).
      - apply ptw_inv. intro v. apply XV_path.
        exact (fst_tpow_tV q v @ ptw h (fst v)).
    Defined.

  End Orbit.

  Definition Ipt (x : X) (c : Cyc) (y : Y c) : Type
    := {e : d = rho_cyc k c & Einv k d e (fn0 k; y) = x}.

  Local Notation IC23 c hH x y
    := (IdCycle_23 sX (sFX k (snd (fst c))) t (Rt k (fst (snd c))) cy
         (root_isCycle k (snd (fst c)) (fst (snd c)) (snd (snd c))) hH x (fn0 k; y)).

  Local Notation PhiE c := (endo_paths_eqv (fst t) (root k (fst (fst (snd c))))).

  Definition toI (x0 : X) (hP : Pdiv k sX t) (x : X) (c : Cyc) (y : Y c)
    (m0 : ptrunc (cV x0 = c)) : Ipt x c y.
  Proof.
    pose (z := fst (IC23 c (comp_hiff k d (cV x0) (HcV x0) hP c m0) x y)).
    pose (E' := eqinv (snd (PhiE c)) (fst z)).
    refine (cyc_path d (rho_cyc k c) E'; _).
    assert (h : endo_fun E' x = (fn0 k; y)).
    { exact (ap (fun w : {e : X ≃ (FN k × Y c) & _} => fst (fst w) x)
                (eqinv_r (snd (PhiE c)) (fst z)) @ snd z). }
    unfold Einv.
    refine (ap (fun r => endo_fun r^ (fn0 k; y)) (ap_cyc_endo_cyc_path d (rho_cyc k c) E') @ _).
    exact (ap (endo_fun E'^) h^ @ endo_fun_retr E' x).
  Defined.

  Definition Ipt_isProp (x : X) (c : Cyc) (y : Y c) : isProp (Ipt x c y).
  Proof.
    intros [e1 q1] [e2 q2].
    pose (C := IC23 c (hiff_e k d e1) x y).
    assert (pf : forall e (q : Einv k d e (fn0 k; y) = x),
               endo_fun (ap cyc_endo e) x = (fn0 k; y)).
    { intros e q. exact (ap (endo_fun (ap cyc_endo e)) q^ @ endo_fun_inv (ap cyc_endo e) _). }
    pose (z1 := (fst (PhiE c) (ap cyc_endo e1); pf e1 q1)
                : {w : {e : X ≃ (FN k × Y c) & _} & fst (fst w) x = (fn0 k; y)}).
    pose (z2 := (fst (PhiE c) (ap cyc_endo e2); pf e2 q2)
                : {w : {e : X ≃ (FN k × Y c) & _} & fst (fst w) x = (fn0 k; y)}).
    assert (ee : e1 = e2).
    { refine ((cyc_path_ap e1)^ @ ap (cyc_path d (rho_cyc k c)) _ @ cyc_path_ap e2).
      exact (Eqv_inj (PhiE c) (ap fst (isContr_isProp' C z1 z2))). }
    exact (path_sigma_prop (fun e => sX _ _) (u := (e1; q1)) (v := (e2; q2)) ee).
  Defined.

  Definition Ptd (x : X) : Type
    := {c : Cyc & {e : d = rho_cyc k c & {y : Y c & Einv k d e (fn0 k; y) = x}}}.

  Definition Ptd_isContr (hP : Pdiv k sX t) (x : X) : isContr (Ptd x).
  Proof.
    refine (ptrunc_rec (isContr_isProp _) _ (fst cy)). intro x0.
    refine (isContr_retract
              (fun w : {w : component Cyc (cV x0) & Y (fst w)} =>
                 (fst (fst w); (fst (toI x0 hP x _ (snd w) (snd (fst w)));
                                (snd w; snd (toI x0 hP x _ (snd w) (snd (fst w))))))
                 : Ptd x)
              (fun p => ((fst p; hiff_comp k d (cV x0) (HcV x0) (fst p)
                                   (hiff_e k d (fst (snd p))));
                         fst (snd (snd p))) : {w : component Cyc (cV x0) & Y (fst w)})
              _ (sum_cycle_point_contr (cV x0))).
    intros [c [e [y q]]].
    exact (ap (fun z : Ipt x c y => ((c; (fst z; (y; snd z))) : Ptd x))
              (Ipt_isProp x c y _ (e; q))).
  Defined.

  Definition Pdiv_isProp : isProp (Pdiv k sX t)
    := Pi_isProp (fun n => fun_isProp ptrunc_isProp).

  Definition PXm_isSet : isSet (Pdiv k sX t × Xm k t)
    := Sigma_isSet (prop_is_set Pdiv_isProp) (fun _ => quot_isSet (simm k t)).

  Definition Ky_isProp (x : X) (w : Fib k d)
    : isProp {y : Y (fst w) & Einv k d (snd w) (fn0 k; y) = x}.
  Proof.
    intros [y1 q1] [y2 q2].
    apply (path_sigma_prop (fun _ => sX _ _)).
    exact (ap (fun v : FN k × Y (fst w) => snd v) (Einv_inj k d (snd w) (q1 @ q2^))).
  Defined.

  Definition Ky_of (x : X) (w : Fib k d) (r : clsm k t x = g_F k d w)
    : {y : Y (fst w) & Einv k d (snd w) (fn0 k; y) = x}.
  Proof.
    refine (ptrunc_rec (Ky_isProp x w) _ (fst (snd (snd (fst w))))). intro y0.
    pose (r' := r @ g_F_pt k d w y0).
    refine (ptrunc_rec (Ky_isProp x w) _ (fst (clsm_iff k sX t _ _) r')). intros [n en].
    refine (tpow (fst (snd (fst w))) (zneg n) y0; _).
    refine (ap (Einv k d (snd w))
              (root_pow k (snd (fst (fst w))) (fst (snd (fst w))) (zneg n) (fn0 k; y0))^ @ _).
    refine (Einv_pow k d (snd w) _ _ @ _).
    refine (ap (fun z => tpow t z _) (zmul_neg _ _) @ _).
    exact (ap (tpow t _) en @ tpow_neg sX t _ x).
  Defined.

  Definition fiber_G_isContr (hP : Pdiv k sX t) (x : X)
    : isContr {w : Fib k d & (hP; clsm k t x) = G_F k d w}.
  Proof.
    refine (isContr_retract
              (fun p : Ptd x => (((fst p; fst (snd p)) : Fib k d);
                     ap011 (fun a b => (a; b) : Pdiv k sX t × Xm k t)
                       (Pdiv_isProp _ _)
                       (ap (clsm k t) (snd (snd (snd p)))^
                        @ (g_F_pt k d (fst p; fst (snd p)) (fst (snd (snd p))))^))
                     : {w : Fib k d & (hP; clsm k t x) = G_F k d w})
              (fun q : {w : Fib k d & (hP; clsm k t x) = G_F k d w} =>
                 (fst (fst q); (snd (fst q);
                   Ky_of x (fst q) (ap (fun v : Pdiv k sX t × Xm k t => snd v) (snd q))))
                 : Ptd x)
              _ (Ptd_isContr hP x)).
    intro q. refine (path_sigma_prop (fun w => PXm_isSet _ _) _). exact refl.
  Defined.

  Definition G_F_isEquiv : isEquiv (G_F k d).
  Proof.
    intros [hP V]. revert V hP.
    refine (im_ind (simm k t) (fun V => forall hP, isContr (fiber (G_F k d) (hP; V)))
              (fun V => Pi_isProp (fun hP => isContr_isProp _)) _).
    intros x hP.
    exact (fiber_G_isContr hP x).
  Defined.

  Definition fiber_cdg : Fib k d ≃ (Pdiv k sX t × Xm k t) := (G_F k d; G_F_isEquiv).

End FiberCdg2.
