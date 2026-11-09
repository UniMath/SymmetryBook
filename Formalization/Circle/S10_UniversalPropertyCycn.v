(** * Section 3.10 Universal property of Cyc_n

    Part of Chapter 3 ([circle.tex]); see [Circle.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - For [n = k+1]: the base point [pt_n :≡ (Fin n, zs)] of [Cyc_n] and
      its symmetry [σ_n :≡ (zs⁻¹, !)] ([pt_n], [sigma_n]); powers of a
      symmetry ([ppow]).
    - Theorem [prop:ump-cycn-into-groupoids] ([ump_cycn]): for a groupoid
      [A], [ev : f ↦ (f(pt_n), ap_f(σ_n), !)] is an equivalence
      [(Cyc_n → A) ≃ ∑_{a:A} ∑_{σ : a = a} (refl_a = σ^n)] (the statement
      [ump_cycn_stmt] asks for an equivalence whose first two components
      are [f(pt_n)] and [ap_f(σ_n)]).  On the way: [σ_n^n = refl]
      ([sigma_pow]), and every symmetry of [pt_n] is a power of [σ_n]
      ([pw_surj]).  Deviation: the uniqueness part avoids the book's
      [χ]; see the comment before [UMPProof].
    - The corollary after the theorem ([cycn_coverings]): connected
      coverings over [Cyc_n] are the cycles [(X,t)] with [t^n = id];
      via [ump_cycn] for [A :≡ Set], connectedness of the total space
      becomes [X] inhabited and any two elements related by a power of
      [t] ([conn_Cw], [Bp_Bq]).

    Nothing in this section is left out. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Spaces.Nat.Core Spaces.Finite.Fin
  Spaces.Finite.FinNat.
From SymmetryBook Require Export Circle.S09_HigherImages.

Local Open Scope uf_scope.

(** ** 3.10 Universal property of [Cyc_n] *)

Section UniversalPropertyCycn.

  Context `{Univalence} (k : ℕ).

  (** The base point [pt_n :≡ (Fin n, zs)] of [Cyc_n], for [n = k+1]. *)
  Definition pt_n : Cycm k := (Fincyc k; trunc refl).

  (** The symmetry [σ_n :≡ (zs⁻¹, !)] of [pt_n]: [zs⁻¹] commutes with
      [zs]. *)
  Definition zs_inv_comm
    : fst (Eqv_inv (finsuccEqv k)) ∘ fst (finsuccEqv k)
      = fst (finsuccEqv k) ∘ fst (Eqv_inv (finsuccEqv k))
    := ptw_inv (fun x => eqinv_l (snd (finsuccEqv k)) x @ (eqinv_r (snd (finsuccEqv k)) x)^).

  Definition sigma_n : pt_n = pt_n
    := path_sigma_prop (fun _ => ptrunc_isProp) (u := pt_n) (v := pt_n)
         (cyc_path (Fincyc k) (Fincyc k) (endo_path (Eqv_inv (finsuccEqv k)) zs_inv_comm)).

  (** Powers [σ^i] of a symmetry. *)
  Fixpoint ppow {A : Type} {a : A} (s : a = a) (i : ℕ) : a = a
    := match i with O => refl | S i' => s ⋅ ppow s i' end.

  (** Theorem [prop:ump-cycn-into-groupoids] (proved below as [ump_cycn]). *)
  Definition ump_cycn_stmt : Type
    := forall (A : Type) (gA : isGrpd A),
         {e : (Cycm k -> A) ≃ {a : A & {s : a = a & refl = ppow s (S k)}} &
           forall f : Cycm k -> A,
             ((f pt_n; ap f sigma_n) : {a : A & a = a})
             = (fst (fst e f); fst (snd (fst e f)))}.

  (** The corollary after the theorem (proved below as
      [cycn_coverings]): the connected
      coverings over [Cyc_n] are the cycles whose order divides [n], i.e.
      with [t^n = id]. *)
  Definition cycn_coverings_stmt : Type
    := {Fam : Cycm k -> SetU & isConn {c : Cycm k & fst (Fam c)}}
       ≃ {c : Cyc & tpow (fst (snd c)) (iplus (S k)) = idmap}.

End UniversalPropertyCycn.

(** The proof of [prop:ump-cycn-into-groupoids], following the book.
    Evaluation at [0] of the transport along [τ : pt_n = pt_n] is an
    equivalence onto [Fin n] ([Ecyc_isEquiv], from [cor:id-m-cycle]),
    which sends [σ_n] to [zs⁻¹] (= [fp] on [∑_i i < n], [EN_l], [EN_r]);
    hence [σ_n^n = refl] ([sigma_pow]).  The type [T(x)] ([Tx]) is
    contractible ([Tx_contr]): at [pt_n] every [π] is determined by
    [π(refl)] (induction on [∑_i i < n]), and [x ↦ fst(center T(x))] is
    the inverse [cyc_Psi] of [ev].  Deviation: instead of the book's
    argument with [χ] for the uniqueness, the second round trip
    [cyc_Psi (ev f) = f] holds since [(f(x), ap_f)] is in [T(x)]
    ([Psi_ev]).  Powers are in diagrammatic order ([spow],
    [ppow_pw]). *)
Section UMPProof.

  Context `{Univalence} (k : ℕ).

  Local Notation pt := (pt_n k).
  Local Notation σ := (sigma_n k).
  Local Notation zinv := (eqinv (snd (finsuccEqv k))).

  Definition Car (x : Cycm k) : Type := fst (fst (fst x)).

  Definition tinv (x : Cycm k) : Car x -> Car x := eqinv (snd (fst (snd (fst x)))).

  Definition trp_tinv {x y : Cycm k} (τ : x = y) (z : Car x)
    : transport Car τ (tinv x z) = tinv y (transport Car τ z)
    := match τ with refl => refl end.

  Definition trp_sigma (z : Fin (S k)) : transport Car σ z = zinv z.
  Proof.
    refine (transport_compose idmap Car σ z @ _).
    refine (ap (fun r => transport idmap r z)
              (ap_compose fst (fun c : Cyc => fst (fst c)) σ
               @ ap (ap (fun c : Cyc => fst (fst c))) (ap_fst_pathpair _ _)
               @ ap_carrier_cyc_path _ _ _) @ _).
    refine ((endo_fun_trp _ z)^ @ _).
    exact (endo_fun_endo_path _ _ z).
  Defined.

  Definition Ecyc {x : Cycm k} (τ : pt = x) : Car x := transport Car τ fin_zero.

  Definition Ecyc_l (τ : pt = pt) : Ecyc (σ @ τ) = zinv (Ecyc τ)
    := transport_pp Car σ τ fin_zero @ ap (transport Car τ) (trp_sigma fin_zero)
       @ trp_tinv τ fin_zero.

  Definition Ecyc_r (τ : pt = pt) : Ecyc (τ @ σ) = zinv (Ecyc τ)
    := transport_pp Car τ σ fin_zero @ trp_sigma _.

  (** [Ecyc] is the evaluation at [0] of [cor:id-m-cycle]. *)
  Definition to_v (c : Cyc) : {w : Endo & CycP w}
    := (cyc_endo c; (snd (fst c); (snd (fst (snd c)); snd (snd c)))).

  Definition to_v_IsEquiv : IsEquiv to_v
    := isequiv_adjointify to_v cyc_of (fun v => refl) (fun c => refl).

  Definition Ech : (pt = pt) ≃ Fin (S k)
    := Eqv_comp (subtype_paths_eqv (fun _ => ptrunc_isProp) pt pt)
         (Eqv_comp (ap to_v; isEquiv_of_IsEquiv (ap to_v) (H := isequiv_ap (H := to_v_IsEquiv) _ _))
            (Eqv_comp (subtype_paths_eqv CycP_isProp (to_v (Fincyc k)) (to_v (Fincyc k))
                       : (to_v (Fincyc k) = to_v (Fincyc k))
                         ≃ (((Fin (S k); fst (finsuccEqv k)) : Endo) = (Fin (S k); fst (finsuccEqv k))))
                      (idm_eqv k))).

  Definition Ech_trp {x y : Cycm k} (τ : x = y) (z : Car x)
    : transport idmap (ap (fun w : Endo => fst w) (ap fst (ap to_v (ap fst τ)))) z
      = transport Car τ z
    := match τ with refl => refl end.

  Definition Ecyc_isEquiv : isEquiv (@Ecyc pt).
  Proof.
    refine (isEquiv_homotopic (fst Ech) _ (fun τ => _) (snd Ech)).
    exact (endo_fun_trp _ fin_zero @ Ech_trp τ fin_zero).
  Defined.


  (** The same, landing in [∑_{i:ℕ} i < n], where [zs⁻¹] is [fp]. *)
  Definition EN (τ : pt = pt) : FinNat (S k) := fin_to_finnat (Ecyc τ).

  Definition ftf_zs (w : Fin (S k))
    : fin_to_finnat (fst (finsuccEqv k) w) = fs k (fin_to_finnat w)
    := eqinv_r (snd (Eqv_of_Equiv (equiv_fin_finnat (S k)))) (fs k (fin_to_finnat w)).

  Definition ftf_zinv (u : Fin (S k)) : fin_to_finnat (zinv u) = fp k (fin_to_finnat u)
    := (fp_fs k _)^ @ ap (fp k) (ftf_zs (zinv u))^
       @ ap (fun v => fp k (fin_to_finnat v)) (eqinv_r (snd (finsuccEqv k)) u).

  Definition EN_refl : EN refl = zero_finnat k := path_fin_to_finnat_fin_zero k.

  Definition EN_l (τ : pt = pt) : EN (σ @ τ) = fp k (EN τ)
    := ap fin_to_finnat (Ecyc_l τ) @ ftf_zinv _.

  Definition EN_r (τ : pt = pt) : EN (τ @ σ) = fp k (EN τ)
    := ap fin_to_finnat (Ecyc_r τ) @ ftf_zinv _.

  Definition EN_isEquiv : isEquiv EN
    := comp_isEquiv Ecyc_isEquiv (snd (Eqv_of_Equiv (equiv_fin_finnat (S k)))).

  Definition EN_inj {τ τ' : pt = pt} (e : EN τ = EN τ') : τ = τ'
    := (eqinv_l EN_isEquiv τ)^ @ ap (eqinv EN_isEquiv) e @ eqinv_l EN_isEquiv τ'.

  (** Powers in diagrammatic order, [spow s (i+1) :≡ spow s i @ s]. *)
  Fixpoint spow {A : Type} {a : A} (s : a = a) (i : ℕ) : a = a
    := match i with O => idpath | S i' => spow s i' @ s end.

  Definition ppow_pw {A : Type} {a : A} (s : a = a) (i : ℕ) : ppow s i = spow s i.
  Proof.
    induction i as [|i IH]. - exact refl.
    - exact (trans_concat _ _ @ ap (fun v => v @ s) IH).
  Defined.

  Definition ap_pw {A B : Type} (f : A -> B) {a : A} (s : a = a) (i : ℕ)
    : ap f (spow s i) = spow (ap f s) i.
  Proof.
    induction i as [|i IH]. - exact refl.
    - exact (ap_pp f _ _ @ ap (fun v => v @ ap f s) IH).
  Defined.

  Fixpoint fpi (j : ℕ) (u : FinNat (S k)) : FinNat (S k)
    := match j with O => u | S j' => fp k (fpi j' u) end.

  Definition EN_pw (i : ℕ) : EN (spow σ i) = fpi i (zero_finnat k).
  Proof.
    induction i as [|i IH]. - exact EN_refl.
    - exact (EN_r _ @ ap (fp k) IH).
  Defined.

  Definition fp_fst (u : FinNat (S k)) (m : ℕ) (e : fst u = S m) : fst (fp k u) = m.
  Proof.
    destruct u as [[|x] l]; cbn in *. - discriminate e. - exact (ap nat_pred e).
  Defined.

  Definition fpi_fst (j m : ℕ) (e : (j + m)%nat = k) : fst (fpi (S j) (zero_finnat k)) = m.
  Proof.
    revert m e. induction j as [|j IH]; intros m e.
    - exact e^.
    - apply (fp_fst _ m). apply IH. exact (nat_add_succ_r j m @ e).
  Defined.

  Definition sigma_pow : spow σ (S k) = refl.
  Proof.
    apply EN_inj. refine (EN_pw (S k) @ _ @ EN_refl^).
    apply (path_sigma_prop (fn_isProp_lt k)). exact (fpi_fst k 0 (nat_add_zero_r k)).
  Defined.

  Section TContr.

    Context {A : Type} (gA : isGrpd A) {a : A} (s : a = a) (r : spow s (S k) = refl).

    Fixpoint Rs (x : ℕ) : a = a := match x with O => idpath | S x' => s^ @ Rs x' end.

    Definition pw_Rs (x : ℕ) : spow s x @ Rs x = refl.
    Proof.
      induction x as [|x IH]. - exact refl.
      - exact (concat_pp_p _ _ _ @ ap (concat (spow s x)) (concat_p_Vp s (Rs x)) @ IH).
    Defined.

    Definition Rs_k : Rs k = s
      := (concat_V_pp (spow s k) (Rs k))^ @ ap (concat (spow s k)^) (pw_Rs k @ r^)
         @ concat_V_pp (spow s k) s.

    Definition Rs_fp (u : FinNat (S k)) : Rs (fst (fp k u)) = s @ Rs (fst u).
    Proof.
      destruct u as [[|x] l]; cbn.
      - exact (Rs_k @ (concat_p1 s)^).
      - exact (concat_p_Vp s (Rs x))^.
    Defined.

    (** The type [T(x)] of the book, with [π(τσ_n) = π(τ)σ]. *)
    Definition Tx (x : Cycm k) : Type
      := {b : A & {pi : (pt = x) -> a = b & forall τ, pi (σ @ τ) = s @ pi τ}}.

    Definition cyc_pi0 (τ : pt = pt) : a = a := Rs (fst (EN τ)).

    Definition cyc_c0 (τ : pt = pt) : cyc_pi0 (σ @ τ) = s @ cyc_pi0 τ
      := ap (fun u => Rs (fst u)) (EN_l τ) @ Rs_fp (EN τ).

    Definition Tx_path (b : A) (q : a = b) (pi : (pt = pt) -> a = b)
      (c : forall τ, pi (σ @ τ) = s @ pi τ) (h : forall τ, pi τ = cyc_pi0 τ @ q)
      : ((a; (cyc_pi0; cyc_c0)) : Tx pt) = (b; (pi; c)).
    Proof.
      destruct q. destruct (ptw_inv (fun τ => (h τ @ concat_p1 _)^) : cyc_pi0 = pi).
      exact (ap (fun c' => ((a; (cyc_pi0; c')) : Tx pt))
                (Pi_isProp (fun τ => gA _ _ _ _) cyc_c0 c)).
    Defined.

    Definition Tpt_contr : isContr (Tx pt).
    Proof.
      refine ((a; (cyc_pi0; cyc_c0)); _). intros [b [pi c]].
      refine (Tx_path b (pi refl) pi c _).
      pose (Einv := eqinv EN_isEquiv).
      assert (e0 : Einv (zero_finnat k) = refl)
        by exact (ap Einv EN_refl^ @ eqinv_l EN_isEquiv refl).
      assert (cl : forall x (l : (x < S k)%nat), pi (Einv (x; l)) = Rs x @ pi refl).
      { induction x as [|x IH]; intro l.
        - refine (ap (fun u => pi (Einv u)) (path_sigma_prop (fn_isProp_lt k) (u := (0%nat; l)) (v := zero_finnat k) refl) @ _).
          exact (ap pi e0 @ (concat_1p (pi refl))^).
        - pose (τ := Einv (S x; l)).
          assert (eτ : σ @ τ = Einv (x; leq_succ_l l)).
          { refine ((eqinv_l EN_isEquiv _)^ @ ap Einv (EN_l τ @ _)).
            exact (ap (fp k) (eqinv_r EN_isEquiv (S x; l))). }
          refine ((concat_V_pp s (pi τ))^ @ ap (concat s^) ((c τ)^ @ ap pi eτ @ IH _) @ _).
          exact (concat_p_pp _ _ _). }
      intro τ.
      refine (ap pi (eqinv_l EN_isEquiv τ)^ @ cl _ _).
    Defined.

    Definition Tx_contr (x : Cycm k) : isContr (Tx x)
      := ptrunc_rec (isContr_isProp _) (fun p : pt = x => trp (fun y => isContr (Tx y)) p Tpt_contr)
           (snd (component_isConn _) pt x).

  End TContr.

  Section Ev.

    Context {A : Type} (gA : isGrpd A).

    Local Notation Sig := {a : A & {t : a = a & refl = ppow t (S k)}}.

    Definition ev_rho (f : Cycm k -> A) : refl = ppow (ap f σ) (S k)
      := ap (ap f) sigma_pow^ @ ap_pw f σ (S k) @ (ppow_pw _ _)^.

    Definition evc (f : Cycm k -> A) : Sig := (f pt; (ap f σ; ev_rho f)).

    Definition r_of (w : Sig) : spow (fst (snd w)) (S k) = refl
      := (ppow_pw _ _)^ @ (snd (snd w))^.

    Definition cyc_Psi (w : Sig) (x : Cycm k) : A
      := fst (fst (Tx_contr gA (fst (snd w)) (r_of w) x)).

    Definition Psi_ph (w : Sig) (x : Cycm k) : (pt = x) -> fst w = cyc_Psi w x
      := fst (snd (fst (Tx_contr gA (fst (snd w)) (r_of w) x))).

    Definition Psi_c (w : Sig) (x : Cycm k) (τ : pt = x)
      : Psi_ph w x (σ @ τ) = fst (snd w) @ Psi_ph w x τ
      := snd (snd (fst (Tx_contr gA (fst (snd w)) (r_of w) x))) τ.

    Definition Psi_nat (w : Sig) {x x' : Cycm k} (α : x = x') (β : pt = x)
      : Psi_ph w x' (β @ α) = Psi_ph w x β @ ap (cyc_Psi w) α.
    Proof. destruct α. exact (ap (Psi_ph w x) (concat_p1 β) @ (concat_p1 _)^). Defined.

    Definition loop_path {a b : A} (P : a = b) (u : b = b) (t : a = a) (h : P @ u = t @ P)
      (ρ : refl = ppow u (S k)) (ρ' : refl = ppow t (S k))
      : ((b; (u; ρ)) : Sig) = (a; (t; ρ')).
    Proof.
      destruct P. destruct ((concat_1p u)^ @ h @ concat_p1 t).
      exact (ap (fun ρ0 => ((a; (u; ρ0)) : Sig)) (gA _ _ _ _ ρ ρ')).
    Defined.

    Definition ev_Psi (w : Sig) : evc (cyc_Psi w) = w.
    Proof.
      destruct w as [a [t ρ]].
      pose (w := (a; (t; ρ)) : Sig).
      refine (loop_path (Psi_ph w pt refl) (ap (cyc_Psi w) σ) t _ (ev_rho _) ρ).
      exact ((Psi_nat w σ refl)^ @ ap (Psi_ph w pt) (concat_1p σ @ (concat_p1 σ)^)
             @ Psi_c w pt refl).
    Defined.

    Definition Psi_ev (f : Cycm k -> A) : cyc_Psi (evc f) = f
      := ptw_inv (fun x => ap fst (snd (Tx_contr gA (ap f σ) (r_of (evc f)) x)
                                      (f x; (ap f; fun τ => ap_pp f σ τ)))).

  End Ev.

End UMPProof.

Definition ump_cycn `{Univalence} (k : ℕ) : ump_cycn_stmt k
  := fun A gA => ((evc k (A := A); iso_to_isEquiv _ (cyc_Psi k gA) (Psi_ev k gA) (ev_Psi k gA));
                  fun f => refl).

(** The corollary after [prop:ump-cycn-into-groupoids]. *)
Section CycnCoverings.

  Context `{Univalence} (k : ℕ).

  Local Notation pt := (pt_n k).
  Local Notation σ := (sigma_n k).

  Definition leq_split {x m : ℕ} (l : (x <= m)%nat) : {j : ℕ & (j + x)%nat = m}.
  Proof.
    induction l as [|m l IH]. - exact (0%nat; refl).
    - exact (S (fst IH); ap S (snd IH)).
  Defined.

  (** Every symmetry of [pt_n] is a power of [σ_n]. *)
  Definition pw_surj (τ : pt = pt) : {i : ℕ & τ = spow σ i}.
  Proof.
    pose (w := leq_split (leq_pred' (snd (EN k τ)))).
    refine (S (fst w); EN_inj k _).
    refine (_ @ (EN_pw k (S (fst w)))^).
    apply (path_sigma_prop (fn_isProp_lt k)). exact (fpi_fst k (fst w) _ (snd w))^.
  Defined.

  Definition trp_famap {Fam : Cycm k -> SetU} {c c' : Cycm k} (p : c = c') (x : fst (Fam c))
    : transport (fun c => fst (Fam c)) p x = transport idmap (ap fst (ap Fam p)) x
    := match p with refl => refl end.

  Definition trp_ap_fst' {Z : Type} {P : Z -> Type} {u v : {z : Z & P z}} (p : u = v)
    : transport P (ap fst p) (snd u) = snd v
    := match p with refl => refl end.

  Local Notation Sig := {X : SetU & {u : X = X & refl = ppow u (S k)}}.

  Definition Cw (w : Sig) : Type
    := ptrunc (fst (fst w))
       × (forall x x' : fst (fst w),
            ptrunc {i : ℕ & transport idmap (ap fst (spow (fst (snd w)) i)) x = x'}).

  Definition Cw_isProp (w : Sig) : isProp (Cw w)
    := prod_isProp ptrunc_isProp (Pi_isProp (fun _ => Pi_isProp (fun _ => ptrunc_isProp))).

  Definition isConn_isProp' (Z : Type) : isProp (isConn Z)
    := prod_isProp ptrunc_isProp (Pi_isProp (fun _ => Pi_isProp (fun _ => ptrunc_isProp))).

  Definition conn_Cw (Fam : Cycm k -> SetU)
    : isConn {c : Cycm k & fst (Fam c)} <-> Cw (evc k Fam).
  Proof.
    pose (P := fun c => fst (Fam c)).
    assert (tr_pw : forall i (x : P pt), transport P (spow σ i) x
                                       = transport idmap (ap fst (spow (ap Fam σ) i)) x).
    { intros i x. exact (trp_famap _ x @ ap (fun r => transport idmap (ap fst r) x) (ap_pw Fam σ i)). }
    split.
    - intros [ci cp]. refine (_; fun x x' => _).
      + refine (ptrunc_rec ptrunc_isProp _ ci). intros [c y].
        refine (ptrunc_rec ptrunc_isProp _ (snd (component_isConn _) pt c)). intro q.
        exact (trunc (transport P q^ y)).
      + refine (ptrunc_rec ptrunc_isProp _ (cp (pt; x) (pt; x'))). intro p.
        pose (w := pw_surj (ap fst p)).
        exact (trunc (fst w; (tr_pw _ x)^ @ ap (fun r => transport P r x) (snd w)^
                             @ trp_ap_fst' p)).
    - intros [ci cp]. refine (ptrunc_rec ptrunc_isProp (fun x => trunc ((pt; x) : {c : Cycm k & P c})) ci; _).
      intros [c y] [c' y'].
      refine (ptrunc_rec ptrunc_isProp _ (snd (component_isConn _) pt c)). intro q. destruct q.
      refine (ptrunc_rec ptrunc_isProp _ (snd (component_isConn _) pt c')). intro q. destruct q.
      refine (ptrunc_rec ptrunc_isProp _ (cp y y')). intros [i e].
      exact (trunc (pathpair (Y := P) (spow σ i) (tr_pw i y @ e))).
  Defined.

  Definition eX (X : SetU) : (X = X) ≃ (fst X ≃ fst X)
    := Eqv_comp (subtype_paths_eqv (fun Y => isSet_isProp Y) X X) (idtoeqv; ua _ _).

  Definition iter_pw (X : SetU) (u : X = X) (i : ℕ) (x : fst X)
    : transport idmap (ap fst (spow u i)) x = iter (fst (fst (eX X) u)) i x.
  Proof.
    induction i as [|i IH]. - exact refl.
    - refine (ap (fun r => transport idmap r x) (ap_pp fst (spow u i) u) @ _).
      exact (transport_pp idmap _ _ x @ ap (transport idmap (ap fst u)) IH).
  Defined.

  Definition iter_add {Y : Type} (f : Y -> Y) (a b : ℕ) (y : Y)
    : iter f a (iter f b y) = iter f (a + b)%nat y.
  Proof. induction a as [|a IH]. - exact refl. - exact (ap f IH). Defined.

  Definition cyc_Bp (X : SetU) (u : X = X) : Type
    := (refl = ppow u (S k))
       × (ptrunc (fst X)
          × (forall x x' : fst X, ptrunc {i : ℕ & transport idmap (ap fst (spow u i)) x = x'})).

  Definition cyc_Bq (X : SetU) (t : fst X ≃ fst X) : Type
    := (ptrunc (fst X) × (forall x x' : fst X, fst (conn_by t x x')))
       × (tpow t (iplus (S k)) = idmap).

  Definition Bp_isProp (X : SetU) (u : X = X) : isProp (cyc_Bp X u)
    := prod_isProp (SetU_isGrpd X X _ _)
         (prod_isProp ptrunc_isProp (Pi_isProp (fun _ => Pi_isProp (fun _ => ptrunc_isProp)))).

  Definition Bq_isProp (X : SetU) (t : fst X ≃ fst X) : isProp (cyc_Bq X t)
    := prod_isProp (prod_isProp ptrunc_isProp
                      (Pi_isProp (fun x => Pi_isProp (fun x' => snd (conn_by t x x')))))
         (Pi_isSet (fun _ => snd X) _ _).

  Definition tpow_nat {X : SetU} (t : fst X ≃ fst X) (h : iter (fst t) (S k) = idmap)
    : forall m : ℤ, ptrunc {i : ℕ & forall x, tpow t m x = iter (fst t) i x}.
  Proof.
    assert (fe : forall y, eqinv (snd t) y = iter (fst t) k y)
      by (intro y; exact (ap (eqinv (snd t)) (ptw h y)^ @ eqinv_l (snd t) _)).
    assert (neg : forall j, {i : ℕ & forall x, iter (eqinv (snd t)) j x = iter (fst t) i x}).
    { induction j as [|j IH]. - exact (0%nat; fun x => refl).
      - exact ((k + fst IH)%nat;
               fun x => ap (eqinv (snd t)) (snd IH x) @ fe _ @ iter_add (fst t) k (fst IH) x). }
    refine (ℤ_ind_prop _ (fun _ => ptrunc_isProp) (fun j => trunc (j; fun x => refl)) _).
    intros [j]. exact (trunc (neg j)).
  Defined.

  Definition Bp_Bq (X : SetU) (u : X = X) : cyc_Bp X u <-> cyc_Bq X (fst (eX X) u).
  Proof.
    pose (t := fst (eX X) u).
    split.
    - intros [ρ [ci cp]].
      refine ((ci; fun x x' => _); _).
      + refine (ptrunc_rec ptrunc_isProp _ (cp x x')). intros [i e].
        exact (trunc (iplus i; ((iter_pw X u i x)^ @ e)^)).
      + pose (pwr := (ppow_pw u (S k))^ @ ρ^).
        exact (ptw_inv (fun x => (iter_pw X u (S k) x)^
                                 @ ap (fun r => transport idmap (ap fst r) x) pwr)).
    - intros [[ci cp] h].
      assert (E : fst (eX X) (spow u (S k)) = fst (eX X) refl).
      { apply path_Eqv. exact (ptw_inv (fun x => iter_pw X u (S k) x @ ptw h x)). }
      pose (pwr := (eqinv_l (snd (eX X)) _)^ @ ap (eqinv (snd (eX X))) E
                   @ eqinv_l (snd (eX X)) refl).
      refine ((ppow_pw u (S k) @ pwr)^; (ci; fun x x' => _)).
      refine (ptrunc_rec ptrunc_isProp _ (cp x x')). intros [m e].
      refine (ptrunc_rec ptrunc_isProp _ (tpow_nat t h m)). intros [i g].
      exact (trunc (i; iter_pw X u i x @ (g x)^ @ e^)).
  Defined.

  Definition cycn_coverings : cycn_coverings_stmt k.
  Proof.
    pose (ev := ump_cycn k SetU SetU_isGrpd).
    refine (Eqv_comp (tot (fun Fam => Overture.fst (conn_Cw Fam));
                      tot_isEquiv _ (fun Fam => snd (Eqv_of_props (isConn_isProp' _) (Cw_isProp _)
                                                        (Overture.fst (conn_Cw Fam)) (Overture.snd (conn_Cw Fam)))))
                     _).
    refine (Eqv_comp (Eqv_of_Equiv (equiv_functor_sigma_pb (Q := Cw) (Equiv_of_Eqv (fst ev)))) _).
    refine (Eqv_comp (Y := {X : SetU & {u : X = X & cyc_Bp X u}})
              (mkEqv (fun v : {w : Sig & Cw w} =>
                        (fst (fst v); (fst (snd (fst v)); (snd (snd (fst v)); snd v)))
                        : {X : SetU & {u : X = X & cyc_Bp X u}})
                     (fun v : {X : SetU & {u : X = X & cyc_Bp X u}} =>
                        ((fst v; (fst (snd v); fst (snd (snd v)))); snd (snd (snd v))) : {w : Sig & Cw w})
                     (fun v => refl) (fun v => refl)) _).
    refine (Eqv_comp (Y := {X : SetU & {t : fst X ≃ fst X & cyc_Bq X t}})
              (tot (fun X => fst (Eqv_comp _ (Eqv_of_Equiv (equiv_functor_sigma_pb (Q := cyc_Bq X)
                                                               (Equiv_of_Eqv (eX X))))));
               tot_isEquiv _ (fun X => snd (Eqv_comp
                   (tot (fun u => Overture.fst (Bp_Bq X u));
                    tot_isEquiv _ (fun u => snd (Eqv_of_props (Bp_isProp X u) (Bq_isProp X _)
                                                   (Overture.fst (Bp_Bq X u)) (Overture.snd (Bp_Bq X u)))))
                   (Eqv_of_Equiv (equiv_functor_sigma_pb (Q := cyc_Bq X) (Equiv_of_Eqv (eX X))))))) _).
    exact (mkEqv (fun v : {X : SetU & {t : fst X ≃ fst X & cyc_Bq X t}} =>
                    ((fst v; (fst (snd v); fst (snd (snd v)))); snd (snd (snd v)))
                    : {c : Cyc & tpow (fst (snd c)) (iplus (S k)) = idmap})
                 (fun v : {c : Cyc & tpow (fst (snd c)) (iplus (S k)) = idmap} =>
                    (fst (fst v); (fst (snd (fst v)); (snd (snd (fst v)); snd v)))
                    : {X : SetU & {t : fst X ≃ fst X & cyc_Bq X t}})
                 (fun v => refl) (fun v => refl)).
  Defined.

End CycnCoverings.
