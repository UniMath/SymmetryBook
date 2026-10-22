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

    Left out (statements only, no proofs yet)
    - Theorem [thm:image-Z-to-Cm] ([thm_image_Z_to_Cm_stmt], with [modm])
      and exercise [xca:image-Cmd-to-Cm] ([xca_image_Cmd_to_Cm_stmt], for
      finite orders [d]); they need [X/m] and [thm:fiber-cdg] (3.8).  The
      exercise attached to the proof of [thm:image-Z-to-Cm] is not stated
      separately. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Truncations.Connectedness
  Modalities.ReflectiveSubuniverse Modalities.Modality Factorization
  Spaces.Nat.Core Spaces.Int Spaces.Circle.
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

(** Theorem [thm:image-Z-to-Cm] (statement only): the [0]-image
    factorization of [-/m : Cyc_0 → Set] goes through [Cyc_m], with
    [r : Cyc_m → Set] the underlying set.  Since [X/m] is a quotient by a
    [Prop]-valued relation, it lives in a larger universe than [X], so
    [r ∘ q] and [-/m] can only be compared by an equivalence of underlying
    sets, not by an identification in one universe of sets. *)
Definition modm `{Univalence} (k : ℕ) (c : Cyc0) : SetU
  := (Xm k (fst (snd (fst c))); quot_isSet _).

Definition thm_image_Z_to_Cm_stmt `{Univalence} : Type
  := forall k : ℕ,
       {q : Cyc0 -> Cycm k &
         (forall c, fst (fst (fst (q c))) ≃ fst (modm k c))
         × isnConnMap 0 q × isnTruncMap 0 (fun c : Cycm k => fst (fst c))}.

(** Exercise [xca:image-Cmd-to-Cm] (statement only), for orders
    [d = j+1]: [-/m] on [Cyc_{md}] is the family of fibers of
    [ρ_m : Cyc_d → Cyc_{md}]; it lifts to a [0]-connected
    [q : Cyc_{md} → Cyc_m] whose fiber at the standard [m]-cycle is
    [Cyc_d]. *)
Definition xca_image_Cmd_to_Cm_stmt `{Univalence} : Type
  := forall k j : ℕ,
       {q : Cycm (jmn k j) -> Cycm k &
         (forall c, fiber (rho_Cycm k j) c ≃ fst (fst (fst (q c))))
         × isnConnMap 0 q
         × (fiber q (Fincyc k; trunc refl) ≃ Cycm j)}.
