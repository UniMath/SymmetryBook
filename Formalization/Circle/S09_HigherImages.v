(** * Section 3.9 Higher images

    Part of Chapter 3 ([circle.tex]); see [Circle.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Exercise [xca:cancel-injection] ([cancel_injection]).
    - Exercise [xca:cancel-surjection] ([cancel_surjection]), and that it
      fails for arbitrary [Y] ([cancel_surjection_fails]): the constant
      map [p : 𝟙 → S1] at [base] is a surjection, and [id_S1 ≠ -id_S1]
      (3.4), but [id_S1 ∘ p] and [-id_S1 ∘ p] are both constant at [base],
      so [ap_{_∘p} : (id = -id) → (id∘p = -id∘p)] goes from an empty type
      to an inhabited one.
    - Definitions [def:n-image], [def:n-connected], [def:n-truncated] for
      [n ≥ -2], with the library's [Trunc n] ([im_n], [isnConn],
      [isnConnMap], [isnTruncMap]); [n]-truncated maps use the library's
      [IsTrunc n] on fibers.
    - The [n]-image factorization [f = i ∘ p] (by definition), [i] is
      [n]-truncated and [p] is [n]-connected; [lem:trunc-n-connected]
      ([tr_isnConnMap], via the library's [conn_map_to_O]).  The fibers of
      [p] are those of [|_|_n] since [p] is [tot(|_|_n)] after
      [A ≃ ∑_b f⁻¹(b)] ([fiber_im_p]).
    - Construction [con:fibcomp=fibfib] with exercise [xca:fibcomp=fibfib]
      ([fibcomp_fibfib]), via [fiber_comp_eqv] (3.3).
    - Exercise [xca:trunc-sum-type+fam], the library's [equiv_O_sigma_O].
    - [def:type-of-factorizations] ([Fact]) and theorem
      [thm:n-im-univ-prop] ([n_im_univ_prop]): the type of factorizations
      into an [n]-connected and an [n]-truncated map is contractible.  We
      derive it from the library's [contr_factor] for the factorization
      system of [Tr n], through an equivalence with the library's record
      [Factorization]; [n_image_fact] is the [n]-image factorization.
    - Exercise [xca:im_preserves_conn] ([im_preserves_conn]).
    - Theorem [thm:image-Z-to-Cm] ([thm_image_Z_to_Cm], with [q = qZ]),
      exercise [xca:image-Z-to-Cm] ([xca_image_Z_to_Cm]: the fiber of [q]
      at the standard [m]-cycle is [Cyc_0]) and exercise
      [xca:image-Cmd-to-Cm] ([xca_image_Cmd_to_Cm], for finite orders
      [d = j+1], with [q = qFin]).  All three are instances of one
      construction for a component [Cyc_B] of the domain of [ρ_m] and its
      image component [Cyc_{B'}] ([qmap], [qmap_fiber_pt],
      [qmap_isnConnMap]).
    Deviations:
    - [(X/m, t̄)] ([qcyc]) uses the library's quotient [QuotHIT] ([Qm]),
      which stays in the universe of [X], instead of the book's [X/m]
      ([Xm], 3.8), a quotient by a [Prop]-valued relation in a larger
      universe; the two are equivalent ([QmE]).  Hence [-/m ≡ r ∘ q] holds
      up to an equivalence of underlying sets ([modm]).
    - Components of [Cyc] are recognized by their subsets [H]
      ([lem:IdCycle], 3.8): [Hdesc c D] says that [D] describes [H] of [c]
      ([Hdesc_qcyc]: [H] of [X/m] is [{n | ∃r. n + mr ∈ H}]).
    - Instead of the book's [φ] and [ψ], the fiber of [q] at the standard
      [m]-cycle is computed via the contractible type of pointed
      [m]-cycles ([lem:sum-cycle-point-contr]): it is the sum over [Cyc_{B'}]
      of the [X/m], hence by [thm:fiber-cdg] the sum of the fibers of
      [ρ_m], i.e. [Cyc_B] ([tot_fib_rho]).  [r] is [0]-truncated since its
      fibers are those of [Cyc_m → Cyc] (propositions) over those of
      [Cyc → Set] (sets of cycle structures).
    - In [ψ((Y,u),e') :≡ (e'(0), u^m)], [e'(0)] stands for the subset
      [Y_{e'(0)}] of [Y] ([def:subtype]); we do not construct [ψ]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Truncations.Connectedness
  Modalities.ReflectiveSubuniverse Modalities.Modality Factorization
  Spaces.Nat.Core Spaces.Int Spaces.Circle Spaces.Finite.Fin Spaces.Finite.FinNat
  Colimits.Quotient HFiber.
From SymmetryBook Require Export Circle.S08_MthRoot.

Local Open Scope uf_scope.

(** ** 3.9 Higher images *)

(** Diagram [eqn:image-univ-prop]: uniqueness of the image factorization;
    the case [n = -1] of [thm:n-im-univ-prop] below. *)

(** Exercise [xca:cancel-injection]: postcomposition with an injection
    induces equivalences on identifications. *)
Definition cancel_injection `{Funext} {A B X : Type} (i : A -> B) (j : isInj i)
  (f g : X -> A) : isEquiv (@ap (X -> A) (X -> B) (fun h => i ∘ h) f g).
Proof.
  pose (api := fun x => isInj_ap_isEquiv j (f x) (g x)).
  pose (F := fun p : f = g => ptw_inv (fun x => ap i (ptw p x)) : i ∘ f = i ∘ g).
  assert (sF : isEquiv F).
  { refine (iso_to_isEquiv F (fun q => ptw_inv (fun x => eqinv (api x) (ptw q x))) _ _).
    - intro p. refine (_ @ eqinv_l (funext f g) p). apply ap. apply ptw_inv. intro x.
      refine (ap (eqinv (api x)) (ptw (eqinv_r (funext _ _) _) x) @ _).
      exact (eqinv_l (api x) _).
    - intro q. refine (_ @ eqinv_l (funext _ _) q). unfold F. apply ap. apply ptw_inv. intro x.
      refine (ap (ap i) (ptw (eqinv_r (funext _ _) _) x) @ _).
      exact (eqinv_r (api x) _). }
  refine (trp isEquiv (ptw_inv (fun p => _)) sF).
  destruct p. exact (eqinv_l (funext _ _) refl).
Defined.

(** Exercise [xca:cancel-surjection]: for a set [Y], precomposition with
    a surjection induces equivalences on identifications. *)
Definition cancel_surjection `{Funext} {A B Y : Type} (p : A -> B) (s : isSurj p)
  (sY : isSet Y) (f g : B -> Y) : isEquiv (@ap (B -> Y) (A -> Y) (fun h => h ∘ p) f g).
Proof.
  pose (sBY := Pi_isSet (fun _ : B => sY)). pose (sAY := Pi_isSet (fun _ : A => sY)).
  refine (snd (Eqv_of_props (sBY f g) (sAY _ _) (ap (fun h => h ∘ p)) _)).
  intro r. apply ptw_inv. intro b.
  exact (ptrunc_rec (sY _ _) (fun w => ap f (snd w) @ ptw r (fst w) @ (ap g (snd w))^) (s b)).
Defined.

(** Exercise [xca:cancel-surjection], second part: this is not true for
    all types [Y].  The counterexample, suggested by the author: the
    constant map [p : 𝟙 → S1] at [base] is a surjection, [id_S1 ≠ -id_S1]
    (3.4), but [id_S1 ∘ p] and [-id_S1 ∘ p] are both constant at [base]. *)
Definition const_base_isSurj `{Univalence} : isSurj (fun _ : True => base)
  := fun z => ptrunc_rec ptrunc_isProp (fun e : base = z => trunc (tt; e⁻¹))
                (S1_base_paths z).

Definition cancel_surjection_fails `{Univalence}
  : ¬ isEquiv (@ap (S1 -> S1) (True -> S1) (fun h => h ∘ (fun _ : True => base))
                 idmap negid).
Proof.
  intro s. apply id_negid_not_conn. exact (trunc (eqinv s refl)).
Defined.

(** Definitions [def:n-image], [def:n-connected], [def:n-truncated], for
    truncation levels [n ≥ -2], with the library's [Trunc n]. *)
Definition im_n (n : trunc_index) {A B : Type} (f : A -> B) : Type
  := {b : B & Trunc n (fiber f b)}.

Definition isnConn (n : trunc_index) (A : Type) : Type := isContr (Trunc n A).

Definition isnConnMap (n : trunc_index) {A B : Type} (f : A -> B) : Type
  := forall b, isnConn n (fiber f b).

Definition isnTruncMap (n : trunc_index) {A B : Type} (f : A -> B) : Type
  := forall b, IsTrunc n (fiber f b).

(** The factorization [eqn:n-image-factorization] of [f] through its
    [n]-image. *)
Section NImage.

  Context (n : trunc_index) {A B : Type} (f : A -> B).

  Definition im_p (a : A) : im_n n f := (f a; tr (a; refl)).

  Definition im_i : im_n n f -> B := fst.

  Definition im_factor : f = im_i ∘ im_p := refl.

  Definition im_i_isnTruncMap : isnTruncMap n im_i
    := fun b => @istrunc_equiv_istrunc _ _
                  (Equiv_of_Eqv (fst_fiber_eqv (fun b => Trunc n (fiber f b)) b)) n _.

  (** [im_p] is [tot(|_|)] after the equivalence [A ≃ ∑_b f⁻¹(b)], so its
      fibers are those of [|_|_n : f⁻¹(b) → ‖f⁻¹(b)‖_n]. *)
  Definition fiber_precomp_eqv {X Y Z : Type} (e : X ≃ Y) (h : Y -> Z) (z : Z)
    : fiber (h ∘ fst e) z ≃ fiber h z
    := Eqv_comp (fiber_comp_eqv (fst e) h z)
         (sigma_contr_fibers (C := fun w : fiber h z => fiber (fst e) (fst w))
            (fun w => snd e (fst w))).

  Definition fiber_im_p (b : B) (z : Trunc n (fiber f b))
    : fiber im_p (b; z) ≃ fiber (@tr n (fiber f b)) z
    := Eqv_comp (fiber_precomp_eqv (Eqv_inv (sum_of_fibers f)) (tot (fun b => @tr n _)) (b; z))
                (fiber_tot (fun b => @tr n (fiber f b)) b z).

End NImage.

(** Lemma [lem:trunc-n-connected], via the library's [conn_map_to_O]. *)
Definition fiber_hfiber_trunc (n : trunc_index) {X Y : Type} (f : X -> Y) (y : Y)
  : Trunc n (fiber f y) <~> Trunc n (hfiber f y)
  := Trunc_functor_equiv n (Equiv_of_Eqv (fiber_hfiber f y)).

Definition tr_isnConnMap (n : trunc_index) (A : Type) : isnConnMap n (@tr n A)
  := fun z => isContr_Eqv (Eqv_of_Equiv (fiber_hfiber_trunc n tr z)^-1)
                (@isContr_of_Contr _ (@conn_map_to_O (Tr n) A z)).

Definition im_p_isnConnMap (n : trunc_index) {A B : Type} (f : A -> B)
  : isnConnMap n (im_p n f)
  := fun w => isContr_Eqv (Eqv_of_Equiv (Trunc_functor_equiv n
                (Equiv_of_Eqv (Eqv_inv (fiber_im_p n f (fst w) (snd w))))))
                (tr_isnConnMap n _ (snd w)).

(** Construction [con:fibcomp=fibfib] and exercise [xca:fibcomp=fibfib]. *)
Definition fibcomp_fibfib {A X B : Type} (g : A -> X) (h : X -> B) (b : B)
  : fiber (h ∘ g) b
    ≃ {y : fiber h b & fiber (fun a => (h (g a); (g a; refl)) : {b : B & fiber h b}) (b; y)}.
Proof.
  pose (gt := fun a => (h (g a); (g a; refl)) : {b : B & fiber h b}).
  refine (Eqv_comp (fiber_comp_eqv gt fst b) _).
  exact (Eqv_of_Equiv (equiv_inverse (equiv_functor_sigma_pb
           (Q := fun w : fiber (@fst B (fiber h)) b => fiber gt (fst w))
           (Equiv_of_Eqv (fst_fiber_eqv (fiber h) b))))).
Defined.

(** Exercise [xca:trunc-sum-type+fam], the library's [equiv_O_sigma_O]. *)
Definition trunc_sum_fam (n : trunc_index) {X : Type} (Y : X -> Type)
  : Trunc n {x : X & Y x} ≃ Trunc n {x : X & Trunc n (Y x)}
  := Eqv_of_Equiv (equiv_O_sigma_O (Tr n) Y)^-1.

(** Definition [def:type-of-factorizations], and theorem
    [thm:n-im-univ-prop]: the type of factorizations of [f] into an
    [n]-connected map followed by an [n]-truncated one is contractible.  We
    derive it from the library's [contr_factor] for the factorization
    system of the modality [Tr n]. *)
Definition Fact {X Y : Type} (f : X -> Y) : Type
  := {Z : Type & {g : X -> Z & {h : Z -> Y & f = h ∘ g}}}.

Definition FactNConn (n : trunc_index) {X Y : Type} (f : X -> Y) : Type
  := {Z : Type & {g : X -> Z & {h : Z -> Y &
       (f = h ∘ g) × isnConnMap n g × isnTruncMap n h}}}.

Section NImUnivProp.

  Context `{Univalence} (n : trunc_index) {X Y : Type} (f : X -> Y).

  Definition conn_to {Z : Type} (g : X -> Z) (c : isnConnMap n g) : IsConnMap (Tr n) g
    := fun z => Contr_of_isContr (isContr_Eqv (Eqv_of_Equiv (fiber_hfiber_trunc n g z)) (c z)).

  Definition conn_from {Z : Type} (g : X -> Z) (c : IsConnMap (Tr n) g) : isnConnMap n g
    := fun z => isContr_Eqv (Eqv_of_Equiv (fiber_hfiber_trunc n g z)^-1)
                  (@isContr_of_Contr _ (c z)).

  Definition trunc_to {Z : Type} (h : Z -> Y) (t : isnTruncMap n h) : MapIn (Tr n) h
    := fun y => @inO_tr_istrunc n _
                  (@istrunc_equiv_istrunc _ _ (Equiv_of_Eqv (fiber_hfiber h y)) n (t y)).

  Definition trunc_from {Z : Type} (h : Z -> Y) (t : MapIn (Tr n) h) : isnTruncMap n h
    := fun y => @istrunc_equiv_istrunc _ _ (Equiv_of_Eqv (fiber_hfiber h y))^-1 n
                  (@istrunc_inO_tr n _ (t y)).

  Definition isnConnMap_isProp {Z : Type} (g : X -> Z) : isProp (isnConnMap n g)
    := Pi_isProp (fun z => isContr_isProp _).

  Definition isnTruncMap_isProp {Z : Type} (h : Z -> Y) : isProp (isnTruncMap n h)
    := Pi_isProp (fun y => IsHProp_isProp).

  Definition fact_inner_eqv (Z : Type) (g : X -> Z) (h : Z -> Y)
    : (((f = h ∘ g) × isnConnMap n g) × isnTruncMap n h)
      ≃ {p : h o g == f & {_ : IsConnMap (Tr n) g & MapIn (Tr n) h}}.
  Proof.
    refine (mkEqv (fun w => ((fun a => (ptw (fst (fst w)) a)^);
                             (conn_to g (snd (fst w)); trunc_to h (snd w))))
                  (fun w => (((ptw_inv (fun a => (fst w a)^));
                              conn_from g (fst (snd w))); trunc_from h (snd (snd w)))) _ _).
    - intros [[r c] t].
      apply (path_sigma_prop (fun _ => isnTruncMap_isProp h)).
      apply (path_sigma_prop (fun _ => isnConnMap_isProp g)). cbn.
      refine (_ @ eqinv_l (funext _ _) r). apply ap. apply ptw_inv. intro a.
      exact (inv_V _).
    - intros [p [c t]].
      apply path_sigma_hprop. cbn. apply path_forall. intro a.
      refine (ap inverse (ptw (eqinv_r (funext _ _) _) a) @ _).
      exact (inv_V _).
  Defined.

  Definition FactNConn_eqv
    : FactNConn n f ≃ Factorization (@IsConnMap (Tr n)) (@MapIn (Tr n)) f.
  Proof.
    refine (Eqv_comp _ (Eqv_of_Equiv issig_Factorization)).
    refine (tot (fun Z => tot (fun g => tot (fun h => fst (fact_inner_eqv Z g h))));
            tot_isEquiv _ (fun Z => tot_isEquiv _ (fun g =>
              tot_isEquiv _ (fun h => snd (fact_inner_eqv Z g h))))).
  Defined.

  Definition n_im_univ_prop : isContr (FactNConn n f)
    := isContr_Eqv (Eqv_inv FactNConn_eqv)
         (@isContr_of_Contr _ (contr_factor (O_factsys (Tr n)) f)).

  (** Its center is the [n]-image factorization. *)
  Definition n_image_fact : FactNConn n f
    := (im_n n f; (im_p n f; (im_i n f; ((refl; im_p_isnConnMap n f);
                                          im_i_isnTruncMap n f)))).

End NImUnivProp.

(** Exercise [xca:im_preserves_conn]: [n]-images ([n ≥ -1]) of a map out
    of a connected type are connected. *)
Definition im_preserves_conn `{Univalence} (k : trunc_index) {A B : Type} (f : A -> B)
  (cA : isConn A) : isConn (im_n k.+1 f).
Proof.
  refine (surj_isConn (f := im_p k.+1 f) _ cA). intros [b z]. revert z.
  refine (Trunc_ind (fun z => Ex (fun a => ((b; z) : im_n k.+1 f) = im_p k.+1 f a)) _).
  - intro z. exact (istrunc_leq (trunc_index_leq_minus_two_n k : (-1 <= k.+1)%trunc)).
  - intros [a e]. revert b e. refine (paths_ind_r _ _ _). exact (trunc (a; refl)).
Defined.

(** Preparations for [thm:image-Z-to-Cm]: for a cycle [(X,t)], the cycle
    [(X/m, t̄)], with [t̄[x] = [t(x)]]. *)
Section QuotCyc.

  Context `{Univalence} (k : ℕ) (c : Cyc).

  Local Notation X := (fst (fst c)).
  Local Notation sX := (snd (fst c)).
  Local Notation t := (fst (snd c)).
  Local Notation cy := (snd (snd c)).

  (** The small model of [X/m]: the library's quotient by [∼_m]. *)
  Definition Qm : Type := QuotHIT (simm k t).

  Definition Qm_isSet : isSet Qm := IsHSet_isSet (ishset_quotient _).

  Definition qcls (x : X) : Qm := class_of _ x.

  Definition tpow_t (n : ℤ) (x : X) : fst t (tpow t n x) = tpow t n (fst t x)
    := tpow_comm_map sX t t (fst t) (fun _ => refl) n x.

  Definition simm_t (x x' : X)
    : (fst (simm k t x x') -> fst (simm k t (fst t x) (fst t x')))
      × (fst (simm k t (fst t x) (fst t x')) -> fst (simm k t x x')).
  Proof.
    refine (fun h => _; fun h => _).
    - refine (ptrunc_rec ptrunc_isProp _ h). intros [r e].
      exact (trunc (r; ap (fst t) e @ tpow_t _ x)).
    - refine (ptrunc_rec ptrunc_isProp _ h). intros [r e].
      refine (trunc (r; _)).
      exact ((eqinv_l (snd t) x')^ @ ap (eqinv (snd t)) (e @ (tpow_t _ x)^)
             @ eqinv_l (snd t) _).
  Defined.

  Definition tbarE : Qm <~> Qm
    := equiv_quotient_functor' (fun x y => fst (simm k t x y)) (fun x y => fst (simm k t x y))
         (Equiv_of_Eqv t) (fun a b => Overture.pair (fst (simm_t a b)) (snd (simm_t a b))).

  Definition tbar : Qm ≃ Qm := Eqv_of_Equiv tbarE.

  Definition tbar_cls (x : X) : fst tbar (qcls x) = qcls (fst t x) := refl.

  Definition tpow_cls (n : ℤ) (x : X) : tpow tbar n (qcls x) = qcls (tpow t n x)
    := (tpow_comm_map Qm_isSet t tbar qcls (fun _ => refl) n x)^.

  Definition tbar_isCycle : isCycle tbar.
  Proof.
    refine (ptrunc_rec ptrunc_isProp (fun x => trunc (qcls x)) (fst cy); _).
    refine (Quotient_ind_hprop _ _ _). intro x.
    refine (Quotient_ind_hprop _ _ _). intro x'.
    refine (ptrunc_rec ptrunc_isProp _ (snd cy x x')). intros [n e].
    exact (trunc (n; ap qcls e @ (tpow_cls n x)^)).
  Defined.

  Definition qcyc : Cyc := ((Qm; Qm_isSet); (tbar; tbar_isCycle)).

End QuotCyc.

(** Integer arithmetic for multiples of [m = k+1]. *)
Definition int_mul_posS_zero (k : nat) (a : Int) (e : int_mul (posS k) a = zero) : a = zero.
Proof.
  destruct a as [c| |c].
  - change (int_mul (posS k) (int_neg (posS c)) = zero) in e.
    rewrite int_mul_neg_r, int_mul_posS in e.
    destruct (transport (fun x => match x with negS _ => Unit | _ => Empty end) e tt).
  - exact refl.
  - rewrite int_mul_posS in e. destruct (posS_ne_zero _ e).
Defined.

Definition int_mul_posS_cancel (k : nat) (a b : Int)
  (e : int_mul (posS k) a = int_mul (posS k) b) : a = b.
Proof.
  assert (e0 : int_mul (posS k) (int_add a (int_neg b)) = zero).
  { rewrite int_dist_l, int_mul_neg_r, e. apply int_add_neg_r. }
  pose (e1 := int_mul_posS_zero k _ e0).
  refine ((int_add_0_r a)^ @ ap (int_add a) (int_add_neg_l b)^ @ int_add_assoc _ _ _ @ _).
  exact (ap (fun x => int_add x b) e1).
Defined.

Definition zmul_cancel (k : ℕ) (a b : ℤ)
  (e : zmul (iplus (S k)) a = zmul (iplus (S k)) b) : a = b
  := toInt_inj (int_mul_posS_cancel k _ _ ((toInt_zmul _ _)^ @ ap toInt e @ toInt_zmul _ _)).

Section HDesc.

  Context `{Univalence}.

  (** A description [D] of the subset [H] of a cycle. *)
  Definition Hdesc (c : Cyc) (D : ℤ -> Type) : Type
    := forall n, (fst (Hc c n) -> D n) × (D n -> fst (Hc c n)).

  Definition Hdesc_isProp (c : Cyc) (D : ℤ -> Type) (hD : forall n, isProp (D n))
    : isProp (Hdesc c D)
    := Pi_isProp (fun n => prod_isProp (fun_isProp (hD n)) (fun_isProp (snd (Hc c n)))).

  Definition Hdesc_path {c d : Cyc} (p : c = d) {D : ℤ -> Type} (h : Hdesc c D)
    : Hdesc d D
    := match p with refl => h end.

  Definition Hdesc_merely {c d : Cyc} (p : ptrunc (c = d)) {D : ℤ -> Type}
    (hD : forall n, isProp (D n)) (h : Hdesc c D) : Hdesc d D
    := ptrunc_rec (Hdesc_isProp d D hD) (fun p => Hdesc_path p h) p.

  Definition Hdesc_merely_eq (c d : Cyc) (D : ℤ -> Type) (hc : Hdesc c D) (hd : Hdesc d D)
    : ptrunc (c = d)
    := cyc_merely_eq c d (fun n => (fun h => snd (hd n) (fst (hc n) h);
                                    fun h => snd (hc n) (fst (hd n) h))).

  Definition Hdesc_iff {c : Cyc} {D D' : ℤ -> Type} (h : Hdesc c D)
    (i : forall n, (D n -> D' n) × (D' n -> D n)) : Hdesc c D'
    := fun n => (fun x => fst (i n) (fst (h n) x); fun x => snd (h n) (snd (i n) x)).

End HDesc.

Section QuotDesc.

  Context `{Univalence} (k : ℕ) (c : Cyc).

  Local Notation X := (fst (fst c)).
  Local Notation sX := (snd (fst c)).
  Local Notation t := (fst (snd c)).
  Local Notation cy := (snd (snd c)).
  Local Notation m := (iplus (S k)).

  Definition QmE : Xm k t ≃ Qm k c
    := quot_QuotHIT (simm k t) (simm_refl k t) (simm_sym k sX t) (simm_trans k sX t).

  Definition simm_qpath (x x' : X) (e : qcls k c x = qcls k c x') : fst (simm k t x x')
    := fst (clsm_iff k sX t x x')
         ((eqinv_l (snd QmE) (clsm k t x))^ @ ap (eqinv (snd QmE)) e
          @ eqinv_l (snd QmE) (clsm k t x')).

  Definition qpath_simm (x x' : X) (r : fst (simm k t x x')) : qcls k c x = qcls k c x'
    := qglue r.

  (** [H] of [(X/m, t̄)]: [t̄^n = id] iff [t^{n+mr} = id] for some [r]. *)
  Definition Hdesc_qcyc (D : ℤ -> Type) (hD : forall n, isProp (D n)) (h : Hdesc c D)
    : Hdesc (qcyc k c) (fun n => Ex (fun r => D (zadd n (zmul m r)))).
  Proof.
    refine (ptrunc_rec (Hdesc_isProp _ _ (fun _ => ptrunc_isProp)) _ (fst cy)). intro x0.
    intro n. refine (fun hn => _; fun hn => _).
    - pose (e := ptw hn (qcls k c x0) : tpow (tbar k c) n (qcls k c x0) = qcls k c x0).
      refine (ptrunc_rec ptrunc_isProp _ (simm_qpath _ _ ((tpow_cls k c n x0)^ @ e))).
      intros [r er]. refine (trunc (r; fst (h _) _)).
      apply (snd (Ht_point sX t cy x0 _)).
      exact (tpow_add sX t n _ x0 @ er^).
    - refine (snd (Ht_point _ (tbar k c) (tbar_isCycle k c) (qcls k c x0) n) _).
      refine (ptrunc_rec (Qm_isSet k c _ _) _ hn). intros [r hr].
      refine (tpow_cls k c n x0 @ qpath_simm _ _ (trunc (r; _))).
      exact ((fst (Ht_point sX t cy x0 _) (snd (h _) hr))^ @ tpow_add sX t n _ x0).
  Defined.

End QuotDesc.


(** Generic equivalences on sums and fibers. *)
Definition prod_prop_l_eqv {P Y : Type} (hP : isProp P) (p : P) : (P × Y) ≃ Y
  := mkEqv (fun w : P × Y => snd w) (fun y => (p; y) : P × Y)
       (fun w : P × Y => ap (fun a => (a; snd w) : P × Y) (hP p (fst w))) (fun y => refl).

Definition sum_fiber_eqv {A B : Type} (f : A -> B) (P : B -> Type)
  : {a : A & P (f a)} ≃ {b : B & fiber f b × P b}.
Proof.
  refine (mkEqv (fun w : {a : A & P (f a)} =>
                   (f (fst w); (((fst w; refl) : fiber f (f (fst w))); snd w))
                   : {b : B & fiber f b × P b})
                (fun v : {b : B & fiber f b × P b} =>
                   (fst (fst (snd v)); trp P (snd (fst (snd v))) (snd (snd v)))
                   : {a : A & P (f a)}) _ _).
  - intros [a p]. exact refl.
  - intros [b [[a e] p]]. revert b e p.
    refine (paths_ind_r (f a) (fun b e => forall p : P b,
              ((f a; ((a; refl); trp P e p)) : {b : B & fiber f b × P b}) = (b; ((a; e); p))) _).
    intro p. exact refl.
Defined.

Definition contr_base_gen {Bt : Type} (Q F : Bt -> Type) (w w' : {b : Bt & Q b})
  (p : w = w') (x : F (fst w))
  : ((fst w'; (trp F (ap fst p) x; snd w')) : {b : Bt & F b × Q b}) = (fst w; (x; snd w))
  := match p with refl => refl end.

Definition contr_base_eqv {Bt : Type} (Q F : Bt -> Type) (C : isContr {b : Bt & Q b})
  (b0 : Bt) (q0 : Q b0) : {b : Bt & F b × Q b} ≃ F b0.
Proof.
  pose (pC := isContr_isProp' C).
  refine (mkEqv (fun v : {b : Bt & F b × Q b} =>
                   trp F (ap fst (pC (fst v; snd (snd v)) (b0; q0))) (fst (snd v)))
                (fun x => (b0; (x; q0)) : {b : Bt & F b × Q b}) _ _).
  - intros [b [x q]]. exact (contr_base_gen Q F (b; q) (b0; q0) _ x).
  - intro x.
    exact (ap (fun r => trp F (ap fst r) x) (prop_is_set pC _ _ (pC (b0; q0) (b0; q0)) refl)).
Defined.

(** Fibers of a map restricted to subtypes that it reflects. *)
Definition sub_fiber_eqv {A B : Type} (P : A -> Type) (Q : B -> Type)
  (hP : forall a, isProp (P a)) (hQ : forall b, isProp (Q b)) (f : A -> B)
  (pres : forall a, P a -> Q (f a)) (refl_ : forall a, Q (f a) -> P a)
  (y : {b : B & Q b})
  : fiber (fun x : {a : A & P a} => (f (fst x); pres _ (snd x)) : {b : B & Q b}) y
    ≃ fiber f (fst y).
Proof.
  pose (F' := fun x : {a : A & P a} => (f (fst x); pres _ (snd x)) : {b : B & Q b}).
  change (fiber F' y ≃ fiber f (fst y)).
  refine (mkEqv (fun z : fiber F' y => (fst (fst z); ap fst (snd z)) : fiber f (fst y))
            (fun z : fiber f (fst y) =>
               (((fst z; refl_ (fst z) (trp Q (snd z) (snd y))) : {a : A & P a});
                path_sigma_prop hQ (u := y) (v := F' (fst z; refl_ (fst z) (trp Q (snd z) (snd y))))
                  (snd z)) : fiber F' y) _ _).
  - intros [x e]. revert y e.
    refine (paths_ind_r _ _ _).
    destruct x as [a pa]. cbn.
    refine (ap (fun z : P a => (((a; z) : {a : A & P a});
                 path_sigma_prop hQ (u := (f a; pres a pa)) (v := (f a; pres a z)) refl))
               (hP a _ pa) @ _).
    refine (ap (fun r => (((a; pa) : {a : A & P a}); r)) _).
    exact (ap (fun r => pathpair (Y := Q) refl r) (prop_is_set (hQ (f a)) _ _ _ refl)).
  - intros [x e]. exact (ap (fun r => (x; r) : fiber f (fst y)) (ap_fst_pathpair _ _)).
Defined.

(** Descriptions of [H] for the standard cycles. *)
Definition D0 (n : ℤ) : Type := n = iplus 0.

Definition D0_isProp (n : ℤ) : isProp (D0 n) := ℤ_isSet _ _.

Definition Dfin (j : ℕ) (n : ℤ) : Type := Ex (fun q => n = zmul (iplus (S j)) q).

Definition Dfin_isProp (j : ℕ) (n : ℤ) : isProp (Dfin j n) := ptrunc_isProp.

Definition hZ `{Univalence} : Hdesc Zcyc D0 := Hc_Z.

Definition hFin `{Univalence} (j : ℕ) : Hdesc (Fincyc j) (Dfin j) := Hc_Fin j.

(** Arithmetic, through the library's [Int]. *)
Definition zadd_zmul_neg (k : ℕ) (n q : ℤ) (e : n = zmul (iplus (S k)) q)
  : zadd n (zmul (iplus (S k)) (zneg q)) = iplus 0.
Proof.
  apply toInt_inj. rewrite toInt_zadd, toInt_zmul, toInt_zneg, e, toInt_zmul.
  rewrite int_mul_neg_r. apply int_add_neg_r.
Defined.

Definition zadd_zmul_solve (k : ℕ) (n r s : ℤ)
  (e : zadd n (zmul (iplus (S k)) r) = zmul (iplus (S k)) s)
  : n = zmul (iplus (S k)) (zadd s (zneg r)).
Proof.
  apply toInt_inj. rewrite toInt_zmul, toInt_zadd, toInt_zneg, int_dist_l, int_mul_neg_r.
  rewrite <- toInt_zmul, <- e, toInt_zadd, toInt_zmul.
  rewrite <- int_add_assoc, int_add_neg_r. exact (int_add_0_r _)^.
Defined.

Definition qd0 (k : ℕ) (n : ℤ)
  : (Ex (fun r => D0 (zadd n (zmul (iplus (S k)) r))) -> Dfin k n)
    × (Dfin k n -> Ex (fun r => D0 (zadd n (zmul (iplus (S k)) r)))).
Proof.
  refine (ptrunc_rec ptrunc_isProp _; ptrunc_rec ptrunc_isProp _).
  - intros [r e]. exact (trunc (zadd (iplus 0) (zneg r); zadd_zmul_solve k n r (iplus 0) e)).
  - intros [q e]. exact (trunc (zneg q; zadd_zmul_neg k n q e)).
Defined.

Definition qdfin (k j : ℕ) (n : ℤ)
  : (Ex (fun r => Dfin (jmn k j) (zadd n (zmul (iplus (S k)) r))) -> Dfin k n)
    × (Dfin k n -> Ex (fun r => Dfin (jmn k j) (zadd n (zmul (iplus (S k)) r)))).
Proof.
  refine (ptrunc_rec ptrunc_isProp _; ptrunc_rec ptrunc_isProp _).
  - intros [r h]. refine (ptrunc_rec ptrunc_isProp _ h). intros [p e].
    refine (trunc (zadd (zmul (iplus (S j)) p) (zneg r); zadd_zmul_solve k n r _ _)).
    exact (e @ (zmul_assoc_nat (S k) (S j) p)^).
  - intros [q e]. refine (trunc (zneg q; trunc (iplus 0; zadd_zmul_neg k n q e))).
Defined.

Definition pd0 (k : ℕ) (n : ℤ) (h : D0 n) : Ex (fun q => n = zmul (iplus (S k)) q)
  := trunc (iplus 0; h).

Definition pdfin (k j : ℕ) (n : ℤ) (h : Dfin (jmn k j) n)
  : Ex (fun q => n = zmul (iplus (S k)) q)
  := ptrunc_rec ptrunc_isProp
       (fun w => trunc (zmul (iplus (S j)) (fst w); snd w @ (zmul_assoc_nat (S k) (S j) _)^)) h.

Definition back0 `{Univalence} (k : ℕ) (c : Cyc) (h : Hdesc (rho_cyc k c) D0) : Hdesc c D0.
Proof.
  intro n. refine (fun hn => _; fun e => _).
  - apply (zmul_cancel k). refine (fst (h _) _).
    exact (snd (Hc_rho k c _) (trunc (n; (refl; hn)))).
  - exact (trp (fun w => fst (Hc c w)) e^ (refl : fst (Hc c (iplus 0)))).
Defined.

Definition backfin `{Univalence} (k j : ℕ) (c : Cyc) (h : Hdesc (rho_cyc k c) (Dfin (jmn k j)))
  : Hdesc c (Dfin j).
Proof.
  intro n. refine (fun hn => _; fun hd => _).
  - refine (ptrunc_rec ptrunc_isProp _ (fst (h _) (snd (Hc_rho k c _) (trunc (n; (refl; hn)))))).
    intros [p e]. refine (trunc (p; zmul_cancel k _ _ _)).
    exact (e @ (zmul_assoc_nat (S k) (S j) p)^).
  - refine (ptrunc_rec (snd (Hc c n)) _ hd). intros [p e].
    assert (hm : fst (Hc (rho_cyc k c) (zmul (iplus (S k)) n))).
    { apply (snd (h _)). refine (trunc (p; _)).
      exact (ap (zmul (iplus (S k))) e @ zmul_assoc_nat (S k) (S j) p). }
    refine (ptrunc_rec (snd (Hc c n)) _ (fst (Hc_rho k c _) hm)). intros [q [eq hq]].
    exact (trp (fun w => fst (Hc c w)) (zmul_cancel k _ _ eq)^ hq).
Defined.

(** The general construction, for a component [Cyc_B] of the domain of
    [ρ_m] and the component [Cyc_{B'}] with [ρ_m(B) = B'], each given by a
    description [DB], [DB'] of [H]; [back] says that [ρ_m(c)] in [Cyc_{B'}]
    implies [c] in [Cyc_B], [qd] describes [H] of [X/m] for [X] in
    [Cyc_{B'}] (namely [mℤ]), and [pd] says that [m] divides the order. *)
Definition rho_back_comp `{Univalence} (k : ℕ) (B B' : Cyc) (DB DB' : ℤ -> Type)
  (hDB' : forall n, isProp (DB' n)) (hB : Hdesc B DB) (hB' : Hdesc B' DB')
  (back : forall c, Hdesc (rho_cyc k c) DB' -> Hdesc c DB)
  (c : Cyc) (p : ptrunc (B' = rho_cyc k c)) : ptrunc (B = c)
  := Hdesc_merely_eq B c DB hB (back c (Hdesc_merely p hDB' hB')).

Definition rho_comp `{Univalence} (k : ℕ) (B B' : Cyc) (rB : rho_cyc k B = B')
  (c : Cyc) (p : ptrunc (B = c)) : ptrunc (B' = rho_cyc k c)
  := ptrunc_rec ptrunc_isProp (fun p => trunc (rB^ @ ap (rho_cyc k) p)) p.

Definition tot_fib_rho `{Univalence} (k : ℕ) (B B' : Cyc)
  (to : forall c : Cyc, ptrunc (B' = rho_cyc k c) -> ptrunc (B = c))
  (fr : forall c : Cyc, ptrunc (B = c) -> ptrunc (B' = rho_cyc k c))
  : {d : component Cyc B' & Fib k (fst d)} ≃ component Cyc B.
Proof.
  refine (mkEqv (fun w => (fst (snd w); to _
                   (ptrunc_rec ptrunc_isProp (fun p => trunc (p @ snd (snd w))) (snd (fst w)))))
                (fun c => ((rho_cyc k (fst c); fr _ (snd c)); (fst c; refl))) _ _).
  - intros [[d pd0] [c e]].
    change (d = rho_cyc k c) in e. revert pd0. revert e. revert d. refine (paths_ind_r _ _ _).
    intro pd0.
    exact (ap (fun z : ptrunc (B' = rho_cyc k c) =>
                 (((rho_cyc k c; z) : component Cyc B'); ((c; refl) : Fib k (rho_cyc k c)))
                 : {d : component Cyc B' & Fib k (fst d)})
              (ptrunc_isProp _ _)).
  - intros [c pc].
    exact (ap (fun z : ptrunc (B = c) => (c; z) : component Cyc B) (ptrunc_isProp _ _)).
Defined.

Definition Pdiv_comp `{Univalence} (k : ℕ) (B' : Cyc) (DB' : ℤ -> Type)
  (hDB' : forall n, isProp (DB' n)) (hB' : Hdesc B' DB')
  (pd : forall n, DB' n -> Ex (fun q => n = zmul (iplus (S k)) q))
  (d : component Cyc B') : Pdiv k (snd (fst (fst d))) (fst (snd (fst d)))
  := fun n h => pd n (fst (Hdesc_merely (snd d) hDB' hB' n) h).

(** The fibers of [ρ_m] over [Cyc_{B'}] are the [X/m]. *)
Definition fib_Qm `{Univalence} (k : ℕ) (B' : Cyc) (DB' : ℤ -> Type)
  (hDB' : forall n, isProp (DB' n)) (hB' : Hdesc B' DB')
  (pd : forall n, DB' n -> Ex (fun q => n = zmul (iplus (S k)) q))
  (d : component Cyc B') : Fib k (fst d) ≃ Qm k (fst d)
  := Eqv_comp (Eqv_comp (fiber_cdg k (fst d))
                 (prod_prop_l_eqv (Pdiv_isProp k (fst d)) (Pdiv_comp k B' DB' hDB' hB' pd d)))
       (QmE k (fst d)).

(** The map [q : Cyc_{B'} → Cyc_m], [(X,t) ↦ (X/m, t̄)]. *)
Definition qmap `{Univalence} (k : ℕ) (B' : Cyc) (DB' : ℤ -> Type)
  (hDB' : forall n, isProp (DB' n)) (hB' : Hdesc B' DB')
  (qd : forall n, (Ex (fun r => DB' (zadd n (zmul (iplus (S k)) r))) -> Dfin k n)
                  × (Dfin k n -> Ex (fun r => DB' (zadd n (zmul (iplus (S k)) r)))))
  (d : component Cyc B') : Cycm k
  := (qcyc k (fst d);
      Hdesc_merely_eq (Fincyc k) (qcyc k (fst d)) (Dfin k) (hFin k)
        (Hdesc_iff (Hdesc_qcyc k (fst d) DB' hDB' (Hdesc_merely (snd d) hDB' hB')) qd)).

Definition Ptype `{Univalence} (k : ℕ) (z : Cycm k) : Type := fst (fst (fst z)).

Definition qmap_fiber_pt `{Univalence} (k : ℕ) (B B' : Cyc) (DB DB' : ℤ -> Type)
  (hDB' : forall n, isProp (DB' n)) (hB : Hdesc B DB) (hB' : Hdesc B' DB')
  (rB : rho_cyc k B = B') (back : forall c, Hdesc (rho_cyc k c) DB' -> Hdesc c DB)
  (qd : forall n, (Ex (fun r => DB' (zadd n (zmul (iplus (S k)) r))) -> Dfin k n)
                  × (Dfin k n -> Ex (fun r => DB' (zadd n (zmul (iplus (S k)) r)))))
  (pd : forall n, DB' n -> Ex (fun q => n = zmul (iplus (S k)) q))
  : fiber (qmap k B' DB' hDB' hB' qd) (Fincyc k; trunc refl) ≃ component Cyc B.
Proof.
  pose (q := qmap k B' DB' hDB' hB' qd).
  pose (F := fun d => fib_Qm k B' DB' hDB' hB' pd d).
  pose (E1 := (tot (fun d => eqinv (snd (F d)));
               tot_isEquiv _ (fun d => snd (Eqv_inv (F d))))
              : {d : component Cyc B' & Ptype k (q d)} ≃ {d : component Cyc B' & Fib k (fst d)}).
  pose (E2 := tot_fib_rho k B B' (rho_back_comp k B B' DB DB' hDB' hB hB' back)
                (rho_comp k B B' rB)).
  pose (E3 := sum_fiber_eqv q (Ptype k)).
  pose (E4 := contr_base_eqv (Ptype k) (fiber q) (sum_cycle_point_contr (Fincyc k))
                (Fincyc k; trunc refl) fin_zero).
  exact (Eqv_comp (Eqv_inv E4) (Eqv_comp (Eqv_inv E3) (Eqv_comp E1 E2))).
Defined.

Definition qmap_isnConnMap `{Univalence} (k : ℕ) (B B' : Cyc) (DB DB' : ℤ -> Type)
  (hDB' : forall n, isProp (DB' n)) (hB : Hdesc B DB) (hB' : Hdesc B' DB')
  (rB : rho_cyc k B = B') (back : forall c, Hdesc (rho_cyc k c) DB' -> Hdesc c DB)
  (qd : forall n, (Ex (fun r => DB' (zadd n (zmul (iplus (S k)) r))) -> Dfin k n)
                  × (Dfin k n -> Ex (fun r => DB' (zadd n (zmul (iplus (S k)) r)))))
  (pd : forall n, DB' n -> Ex (fun q => n = zmul (iplus (S k)) q))
  : isnConnMap 0 (qmap k B' DB' hDB' hB' qd).
Proof.
  intro z.
  refine (ptrunc_rec (isContr_isProp _) _
            (snd (component_isConn (Fincyc k)) (Fincyc k; trunc refl) z)).
  intro e. destruct e.
  exact (isConn_strunc_isContr
           (isConn_Eqv (Eqv_inv (qmap_fiber_pt k B B' DB DB' hDB' hB hB' rB back qd pd))
              (component_isConn B))).
Defined.

(** The underlying set map [r : Cyc_m → Set] is [0]-truncated: its fibers
    are those of [Cyc_m → Cyc] (propositions) over those of [Cyc → Set]
    (cycle structures on a set, a set). *)
Definition cycstr_isSet `{Funext} (X : SetU)
  : isSet {t : fst X ≃ fst X & ptrunc (fst X) × (forall x x' : fst X, fst (conn_by t x x'))}.
Proof.
  refine (Sigma_isSet (Sigma_isSet (Pi_isSet (fun _ => snd X))
                         (fun f => prop_is_set (isEquiv_isProp f))) _).
  intro t. apply prop_is_set.
  exact (prod_isProp ptrunc_isProp (Pi_isProp (fun _ => Pi_isProp (fun _ => ptrunc_isProp)))).
Defined.

Definition r_isnTruncMap `{Univalence} (k : ℕ)
  : isnTruncMap 0 (fun c : Cycm k => fst (fst c)).
Proof.
  intro S.
  refine (istrunc_equiv_istrunc _ (Equiv_of_Eqv (fiber_hfiber _ S))^-1).
  exact (@istruncmap_compose 0 (Cycm k) Cyc SetU pr1 pr1
           (fun X => istrunc_equiv_istrunc _ (hfiber_fibration X _)
                       (IsTrunc0 := isSet_IsHSet (cycstr_isSet X)))
           (fun c => istrunc_equiv_istrunc _ (hfiber_fibration c _)
                       (IsTrunc0 := isSet_IsHSet (prop_is_set ptrunc_isProp))) S).
Defined.

(** Theorem [thm:image-Z-to-Cm]: the [0]-image factorization of
    [-/m : Cyc_0 → Set] goes through [Cyc_m], with [q(X,t) = (X/m, t̄)]
    ([qZ]) and [r : Cyc_m → Set] the underlying set ([r_isnTruncMap]).
    Since the book's [X/m] ([Xm], 3.8) is a quotient by a [Prop]-valued
    relation, it lives in a larger universe than [X]; [q] uses the
    library's quotient [Qm] instead, so [r ∘ q] and [-/m] are compared by
    an equivalence of underlying sets ([modm]). *)
Definition modm `{Univalence} (k : ℕ) (c : Cyc0) : SetU
  := (Xm k (fst (snd (fst c))); quot_isSet _).

Definition qZ `{Univalence} (k : ℕ) : Cyc0 -> Cycm k := qmap k Zcyc D0 D0_isProp hZ (qd0 k).

Definition thm_image_Z_to_Cm `{Univalence} (k : ℕ)
  : {q : Cyc0 -> Cycm k &
      (forall c, fst (fst (fst (q c))) ≃ fst (modm k c))
      × isnConnMap 0 q × isnTruncMap 0 (fun c : Cycm k => fst (fst c))}.
Proof.
  refine (qZ k; ((fun c => Eqv_inv (QmE k (fst c)); _); r_isnTruncMap k)).
  exact (qmap_isnConnMap k Zcyc Zcyc D0 D0 D0_isProp hZ hZ (rho_Z_path k) (back0 k)
           (qd0 k) (pd0 k)).
Defined.

(** Exercise [xca:image-Z-to-Cm]: the details of the proof above; the
    fiber of [q] at the standard [m]-cycle is [Cyc_0].  Instead of
    the book's inverse [ψ], we use that the type of pointed [m]-cycles is
    contractible ([lem:sum-cycle-point-contr]), so the fiber at the
    standard cycle is the sum of the fibers [Y/m] over [Cyc_0], i.e. the
    sum of the fibers of [ρ_m] by [thm:fiber-cdg], i.e. [Cyc_0]. *)
Definition xca_image_Z_to_Cm `{Univalence} (k : ℕ)
  : fiber (qZ k) (Fincyc k; trunc refl) ≃ Cyc0
  := qmap_fiber_pt k Zcyc Zcyc D0 D0 D0_isProp hZ hZ (rho_Z_path k) (back0 k) (qd0 k) (pd0 k).

(** Exercise [xca:image-Cmd-to-Cm], for orders [d = j+1]: [-/m] on
    [Cyc_{md}] is the family of fibers of [ρ_m : Cyc_d → Cyc_{md}]; it
    lifts to a [0]-connected [q : Cyc_{md} → Cyc_m] whose fiber at the
    standard [m]-cycle is [Cyc_d]. *)
Definition qFin `{Univalence} (k j : ℕ) : Cycm (jmn k j) -> Cycm k
  := qmap k (Fincyc (jmn k j)) (Dfin (jmn k j)) (Dfin_isProp _) (hFin _) (qdfin k j).

Definition fiber_rho_Cycm `{Univalence} (k j : ℕ) (c : Cycm (jmn k j))
  : fiber (rho_Cycm k j) c ≃ Fib k (fst c)
  := sub_fiber_eqv (fun a => ptrunc (Fincyc j = a)) (fun b => ptrunc (Fincyc (jmn k j) = b))
       (fun _ => ptrunc_isProp) (fun _ => ptrunc_isProp) (rho_cyc k)
       (fun a p => snd (rho_Cycm k j (a; p)))
       (rho_back_comp k (Fincyc j) (Fincyc (jmn k j)) (Dfin j) (Dfin (jmn k j))
          (Dfin_isProp _) (hFin j) (hFin _) (backfin k j)) c.

Definition qFin_fiber `{Univalence} (k j : ℕ) (c : Cycm (jmn k j))
  : fiber (rho_Cycm k j) c ≃ fst (fst (fst (qFin k j c)))
  := Eqv_comp (fiber_rho_Cycm k j c) (fib_Qm k _ _ (Dfin_isProp _) (hFin _) (pdfin k j) c).

Definition qFin_isnConnMap `{Univalence} (k j : ℕ) : isnConnMap 0 (qFin k j)
  := qmap_isnConnMap k (Fincyc j) (Fincyc (jmn k j)) (Dfin j) (Dfin (jmn k j))
       (Dfin_isProp _) (hFin j) (hFin _) (rho_Fin_path k j) (backfin k j)
       (qdfin k j) (pdfin k j).

Definition qFin_fiber_pt `{Univalence} (k j : ℕ)
  : fiber (qFin k j) (Fincyc k; trunc refl) ≃ Cycm j
  := qmap_fiber_pt k (Fincyc j) (Fincyc (jmn k j)) (Dfin j) (Dfin (jmn k j))
       (Dfin_isProp _) (hFin j) (hFin _) (rho_Fin_path k j) (backfin k j)
       (qdfin k j) (pdfin k j).

Definition xca_image_Cmd_to_Cm `{Univalence} (k j : ℕ)
  : {q : Cycm (jmn k j) -> Cycm k &
      (forall c, fiber (rho_Cycm k j) c ≃ fst (fst (fst (q c))))
      × isnConnMap 0 q
      × (fiber q (Fincyc k; trunc refl) ≃ Cycm j)}
  := (qFin k j; ((qFin_fiber k j; qFin_isnConnMap k j); qFin_fiber_pt k j)).
