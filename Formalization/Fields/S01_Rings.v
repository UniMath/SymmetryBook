(** * Section 13.1 Rings, abstract and concrete

    Part of Chapter 13 ([fields.tex]); see [Fields.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    Only the questions [TBD1] and [TBD2] of Example [exa:allS1*-swap]
    and the claim [M ≃ ℤ] of that example, with [m_k ↦ k] and the
    reading of [m_k] being [kγ], are addressed so far; the other
    labels of this section are not formalized yet (no [_stmt]s either:
    the chapter is still in flux).

    The example studies [M :≡ S¹ →* (S¹ →* B²ℤ)] and maps
    [m_k : M] given by [m_k(base) :≡ pt] and [m_k(loop) := ptw_*⁻¹(k')]
    with [k'(base) :≡ refl_pt] and [k'(loop)] the [k]-loop around
    [id_S¹].  [TBD1] asks for the relation between [m_k] and
    multiplication by [k], [TBD2] whether [swap(m_k)] is [m_k] or
    [m_{-k}].

    Forget the pointing paths and write [F(z,w) :≡ m(z)(w)] for
    [m :≡ m_1].  A pair of paths [p] in [z] and [q] in [w] gives a
    square [F(p,q)], which can be read in two ways, as a path over [p]
    or as a path over [q]:
    - z-outer: [apd] of [z ↦ ap_{F(z,-)}(q)] applied to [p]
      ([reading_z]);
    - w-outer: [apd] of [w ↦ ap_{F(-,w)}(p)] applied to [q]
      ([reading_w]).
    Both are turned into squares ([Sq t bo l r :≡ (r ⋅ t = bo ⋅ l)]) by
    the same conversion [po_sq] of paths over a path in a family of
    identity types [x ↦ (u(x) = v(x))].

    The sign:
    - [reading_w_z]: for any [F : A → B → C] and any paths [p], [q],
      [reading_w F p q = (reading_z F p q)⁻¹]: transposing a square
      inverts it.
    - [reading_w_swap]: [reading_w (swap2 F) q p ≡ reading_z F p q], so
      [reading_w (swap2 F) q p = (reading_w F p q)⁻¹].

    Bilinearity:
    - [hpaste], [vpaste]: horizontal and vertical pasting of squares;
      [reading_w_hpaste], [reading_w_vpaste]: the reading of
      [F(p' ⋅ p, q)] is the pasting of those of [F(p,q)] and [F(p',q)],
      and likewise in [q] (up to [ap_trans] on the sides).
    - For loops [p], [q] whose sides are identified with [refl]
      ([eP], [eQ]), [loops_reading F p q eP eQ] is a 2-loop at
      [F(a,b)] ([sq_2loop]).  [loops_reading_hpaste] and
      [loops_reading_vpaste]: it is a homomorphism in each variable,
      with the side identifications of composites given by [ecomp];
      [loops_reading_swap]: swapping the arguments of [F] inverts it.
    - [loop3_loop2_reading]: for [F : S¹ → S¹ → C] the 2-loop of
      [F(loop³,loop²)] is [6γ], written [((γ⋅γ)⋅(γ⋅γ))⋅(γ⋅γ)], where [γ]
      is the 2-loop of [F(loop,loop)]; [loop3_loop2_reading_z]: the
      z-outer reading, that is, [apd] of [z ↦ ap_{F(z,-)}(loop²)]
      applied to [loop³], is [(6γ)⁻¹].

    Precomposition and powers ([TBD1]):
    - [reading_w_precomp1], [reading_w_precomp2],
      [loops_reading_precomp1], [loops_reading_precomp2]: the reading
      of [F ∘ (f × id)] at [(p,q)] is that of [F] at [(ap_f(p),q)], and
      likewise in the second variable (up to [ap_comp] on the sides).
    - [loops_reading_pow1], [loops_reading_pow2]: the 2-loop of
      [F(p^n,q)] and of [F(p,q^n)] is the [n]-th power of that of
      [F(p,q)] ([ppow], with [p^{n+1} :≡ p ⋅ p^n]).
    - [loops_reading_dg1], [loops_reading_dg2]: for [F : S¹ → S¹ → C]
      and the degree [k] map [dg k] of Section 3.6 ([k : ℕ]), the 2-loop
      of [F ∘ (dg_k × id)] and of [F ∘ (id × dg_k)] at [(loop,loop)] is
      the [k]-th power of that of [F].

    How this answers [TBD2].  By definition of [m], the w-outer reading
    is the natural one: [ap_{F(-,w)}(loop) = ptw(m(loop))(w) = k'(w)], so
    the w-outer reading of [F(loop,loop)] is [ap_{k'}(loop)], the
    generator [γ] of [Ω²(B²ℤ) ≃ ℤ] (corresponding to [k = 1]); this is
    also how [M ≃ Ω²(B²ℤ)] reads off [m].  For [swap(m)] the outer
    variable is [w], so its w-outer reading is the z-outer reading of
    [m], which is [γ⁻¹] by [loops_reading_swap].  Hence
    [swap(m_1) = m_{-1}], and likewise [swap(m_k) = m_{-k}]: the twist
    on [S¹ ∧ S¹ ≃ S²] has degree [-1].

    How this answers [TBD1].  By bilinearity the 2-loop of
    [F(loop^i,loop^j)] is [ij] times that of [F(loop,loop)]; for [m_k]
    the latter is [kγ] (the [k]-loop around [id_S¹]).  Precomposing
    [m_1] with the degree [k] map in either argument multiplies the
    2-loop at [(loop,loop)] by [k] ([loops_reading_dg1],
    [loops_reading_dg2]), so under [M ≃ Ω²(B²ℤ) ≃ ℤ]
    (read off at [(loop,loop)]) [m_k = m_1 ∘ (dg_k × id) = m_1 ∘ (id ×
    dg_k)], and [m_k] corresponds to [k].

    The equivalence [M ≃ ℤ] (claimed in [exa:allS1*-swap]), with
    [B²ℤ :≡ Σ_{X:U} ‖S¹ = X‖₀] pointed at [(S¹,|refl|)] ([B2Z]) and
    [S¹ →* B²ℤ] pointed at the constant map ([pmap_ptd]):
    - [M_eqv_loops]: [M ≃ Ω(S¹ →* B²ℤ)] by evaluation at [loop]
      ([evp], [cor:circle-loopspace]; this is [ev] of
      [rem:pointing-ev]).
    - [loops_cst_eqv]: [Ω(S¹ →* B²ℤ) ≃ (S¹ →* ΩB²ℤ)], which is [ptw_*]
      ([con:identity-ptd-maps]) at the constant map, implemented
      directly ([lc_eqv], for any pointed [B]) so that a loop [ℓ] goes
      to [(apD10(ap_fst(ℓ)), e)] by definition.
    - [omega2_eqv]: [(S¹ →* ΩB²ℤ) ≃ Ω²B²ℤ], [evp] again.
    - [omega2_B2Z_eqv]: [Ω²B²ℤ ≃ ℤ], along the second argument of the
      example: the second component of [pt = pt] is a path in the set
      [‖S¹ = S¹‖₀], so [Ω²B²ℤ ≃ (refl_{S¹} = refl_{S¹})] ([sigma_step]);
      by univalence and function extensionality this is [∏_x (x = x)]
      ([ua_step]), which is [base = base] by evaluation at [base]
      ([ev_step], from [xca:(S1->S1)_(f)-eqv-S1]), and that is [ℤ] by
      [wdg].
    - [M_eqv_Z]: the composite [M ≃ ℤ].

    The maps [m_k], for all [k : ℤ], as in the example:
    - [kloop k]: the [k]-loop around [id_S¹], pointwise
      [x ↦ ex(x)(loop^k)] ([kloop_pw]), made a 2-loop at [refl_{S¹}]
      by function extensionality and univalence ([kloop_id]) and then
      at [refl_{pt}] in [B²ℤ].
    - [dg_k' : S¹ →* ΩB²ℤ] with [dg_k'(base) :≡ refl], [dg_k'(loop) :=
      kloop k], pointed by [refl]; [m_k] with [m_k(base) :≡ pt],
      [m_k(loop) := ptw_*⁻¹(dg_k')] and [(m_k)_pt :≡ refl].
    - [M_eqv_Z_m]: [M_eqv_Z(m_k) = k].

    The w-outer reading of [m_k]:
    - [reading_lc] (any pointed [B]): for [m :≡ evp⁻¹(ℓ)] the w-outer
      reading of [F(z,w) :≡ m(z)(w)] at [(loop,loop)] is [evp] of
      [lc_eqv(ℓ)], with the sides identified with [refl] by [eP_of]
      (from the pointing path [e] of [lc_eqv(ℓ)]) and [eQ_of] ([ap] of
      a constant).  It rests on [reading_w_fun] (the reading in terms
      of [apD10] of [ap_G(p)]) and [const_reading] (for a constant
      function the reading of a homotopy [h] is [ap_h], conjugated).
    - [reading_m_k]: for [m_k] ([F_k], [eP_k], [eQ_k]) this is
      [kloop k]; [reading_m_k_Z]: it corresponds to [k] under
      [Ω²B²ℤ ≃ ℤ].
    - [Psi]: the composite [Ω²B²ℤ → (base = base)] as a single [ap]
      ([Psi_eq]), hence injective ([Psi_inj]) and preserving powers;
      [kloop_pow]: [kloop k = γ^k] with [γ :≡ kloop 1] ([gamma]).
    - [reading_m_1]: [γ] is the reading of [m_1];
      [reading_m_k_gamma]: the reading of [m_k] is [γ^k] ([loopexp]).
    - [reading_m_1_dg1], [reading_m_1_dg2] ([TBD1] for [k : ℕ]): the
      readings of [m_1 ∘ (dg_k × id)] and [m_1 ∘ (id × dg_k)] equal
      that of [m_k].


    Negative degrees and independence of the sides:
    - [loops_reading_indep]: the 2-loop of a square of loops does not
      depend on the identifications of its sides with [refl] (changing
      them conjugates it, and 2-loops commute: [eckmann_hilton]).
    - [loops_reading_inv1], [loops_reading_inv2]: [p⁻¹] gives the
      inverse 2-loop; [loops_reading_loopexp1], [loops_reading_loopexp2]:
      the integer power [p^z] ([loopexp], [z : Int]) gives [γ^z].
    - [dgZ k :≡ S1_rec base loop^k] for [k : ℤ] ([dg n ≡ dgZ(ι₊ n)],
      [dg_dgZ]); [loops_reading_dgZ1], [loops_reading_dgZ2]: precomposing
      with [dgZ k] in either argument gives [γ^k].
    - [reading_m_k_any]: the reading of [m_k] is [γ^k] for any side
      identifications; [reading_m_1_dgZ1], [reading_m_1_dgZ2] ([TBD1] for
      all [k : ℤ]): the readings of [m_1 ∘ (dg_k × id)] and
      [m_1 ∘ (id × dg_k)] equal that of [m_k].  The sign and the bilinearity are independent of all
    of this: they hold for any [F]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core Spaces.Int Spaces.Circle.
From SymmetryBook Require Export FinGroups.FinGroups.

Local Open Scope uf_scope.

(** ** 13.1 Rings, abstract and concrete *)

(** *** Example [exa:allS1*-swap], [TBD1] and [TBD2]: bilinearity and
    the sign of [swap] *)

(** A path over [p] in the family [x ↦ (u(x) = v(x))] is a square with
    sides [ap_u(p)] and [ap_v(p)]; defined by induction on [p]. *)
Definition po_sq {X Y : Type} {u v : X -> Y} {x x' : X} (p : x = x')
  {α : u x = v x} {β : u x' = v x'}
  : PathOver (fun x => u x = v x) p α β -> (ap v p ⋅ α = β ⋅ ap u p).
Proof.
  destruct p. intro r. exact ((trans_1p β)⁻¹ ⋅ r).
Defined.

Section SquareReadings.

  Context {A B C : Type} (F : A -> B -> C).

  (** The z-outer reading of the square [F(p,q)]. *)
  Definition reading_z {a a' : A} (p : a = a') {b b' : B} (q : b = b')
    : ap (fun z => F z b') p ⋅ ap (F a) q = ap (F a') q ⋅ ap (fun z => F z b) p
    := po_sq (u := fun z => F z b) (v := fun z => F z b') p
             (apd (fun z => ap (F z) q) p).

  (** The w-outer reading of the square [F(p,q)]. *)
  Definition reading_w {a a' : A} (p : a = a') {b b' : B} (q : b = b')
    : ap (F a') q ⋅ ap (fun z => F z b) p = ap (fun z => F z b') p ⋅ ap (F a) q
    := po_sq (u := F a) (v := F a') q
             (apd (fun w => ap (fun z => F z w) p) q).

  (** The sign: the two readings are inverse to each other. *)
  Definition reading_w_z {a a' : A} (p : a = a') {b b' : B} (q : b = b')
    : reading_w p q = (reading_z p q)⁻¹.
  Proof. destruct p, q. exact refl. Defined.

End SquareReadings.

(** Swapping the arguments of a function of two variables. *)
Definition swap2 {A B C : Type} (F : A -> B -> C) : B -> A -> C
  := fun w z => F z w.

(** The w-outer reading of [swap2 F] is the z-outer reading of [F]. *)
Definition reading_w_swap_jdeq {A B C : Type} (F : A -> B -> C)
  {a a' : A} (p : a = a') {b b' : B} (q : b = b')
  : reading_w (swap2 F) q p = reading_z F p q
  := refl.

Definition reading_w_swap {A B C : Type} (F : A -> B -> C)
  {a a' : A} (p : a = a') {b b' : B} (q : b = b')
  : reading_w (swap2 F) q p = (reading_w F p q)⁻¹
  := (symm_symm (reading_z F p q) ⋅ ap symm (reading_w_z F p q))⁻¹.

(** *** Squares and their pasting

    A square with top [t], bottom [bo], left [l] and right [r] is an
    identification [r ⋅ t = bo ⋅ l]; [reading_w F p q] is a square with
    [t :≡ ap_{F(-,b)}(p)], [bo :≡ ap_{F(-,b')}(p)], [l :≡ ap_{F(a,-)}(q)]
    and [r :≡ ap_{F(a',-)}(q)]. *)
Section Squares.

  Context {C : Type}.

  Definition Sq {c00 c10 c01 c11 : C} (t : c00 = c10) (bo : c01 = c11)
    (l : c00 = c01) (r : c10 = c11) : Type
    := r ⋅ t = bo ⋅ l.

  (** Horizontal pasting. *)
  Definition hpaste {c00 c10 c20 c01 c11 c21 : C}
    {t1 : c00 = c10} {b1 : c01 = c11} {l : c00 = c01} {m : c10 = c11}
    {t2 : c10 = c20} {b2 : c11 = c21} {r : c20 = c21}
    (s1 : Sq t1 b1 l m) (s2 : Sq t2 b2 m r) : Sq (t2 ⋅ t1) (b2 ⋅ b1) l r
    := trans_assoc l b1 b2 ⋅ ap (fun x => b2 ⋅ x) s1 ⋅ (trans_assoc t1 m b2)⁻¹
       ⋅ ap (fun x => x ⋅ t1) s2 ⋅ trans_assoc t1 t2 r.

  (** Vertical pasting. *)
  Definition vpaste {c00 c10 c01 c11 c02 c12 : C}
    {t : c00 = c10} {m : c01 = c11} {l1 : c00 = c01} {r1 : c10 = c11}
    {bo : c02 = c12} {l2 : c01 = c02} {r2 : c11 = c12}
    (s1 : Sq t m l1 r1) (s2 : Sq m bo l2 r2) : Sq t bo (l2 ⋅ l1) (r2 ⋅ r1)
    := (trans_assoc l1 l2 bo)⁻¹ ⋅ ap (fun x => x ⋅ l1) s2 ⋅ trans_assoc l1 m r2
       ⋅ ap (fun x => r2 ⋅ x) s1 ⋅ (trans_assoc t r1 r2)⁻¹.

  (** Changing the sides of a square along identifications. *)
  Definition Sq_sides {c00 c10 c01 c11 : C}
    {t t' : c00 = c10} {bo bo' : c01 = c11} {l l' : c00 = c01} {r r' : c10 = c11}
    (φt : t = t') (φb : bo = bo') (φl : l = l') (φr : r = r')
    : Sq t bo l r -> Sq t' bo' l' r'.
  Proof. destruct φt, φb, φl, φr. exact (id _). Defined.

  (** A square of loops at [c] whose sides are identified with [refl] is
      a 2-loop at [c]. *)
  Definition sq_2loop {c : C} {t bo l r : c = c}
    (et : refl = t) (eb : refl = bo) (el : refl = l) (er : refl = r)
    : Sq t bo l r -> (refl c = refl c).
  Proof. destruct et, eb, el, er. exact (id _). Defined.

  (** Transposing a square of loops inverts its 2-loop. *)
  Definition sq_2loop_inv {c : C} {t bo l r : c = c}
    (et : refl = t) (eb : refl = bo) (el : refl = l) (er : refl = r)
    (s : Sq t bo l r)
    : sq_2loop el er et eb s⁻¹ = (sq_2loop et eb el er s)⁻¹.
  Proof. destruct et, eb, el, er. exact refl. Defined.

  Definition sq_2loop_sides {c : C} {t t' bo bo' l l' r r' : c = c}
    (φt : t = t') (φb : bo = bo') (φl : l = l') (φr : r = r')
    (et : refl = t) (eb : refl = bo) (el : refl = l) (er : refl = r)
    (s : Sq t bo l r)
    : sq_2loop (φt ⋅ et) (φb ⋅ eb) (φl ⋅ el) (φr ⋅ er) (Sq_sides φt φb φl φr s)
      = sq_2loop et eb el er s.
  Proof. destruct φt, φb, φl, φr. exact refl. Defined.

  (** Composites of loops identified with [refl]. *)
  Definition eq_trans2 {c : C} {x y : c = c} (ex : refl = x) (ey : refl = y)
    : refl = y ⋅ x.
  Proof. destruct ex, ey. exact refl. Defined.

  Local Definition ap_r_refl {c : C} {x y : c = c} (s : x = y)
    : ap (fun z => z ⋅ refl) s = (trans_1p y)⁻¹ ⋅ s ⋅ trans_1p x.
  Proof. destruct s, x. exact refl. Defined.

  (** Pasting squares composes their 2-loops. *)
  Definition sq_2loop_hpaste {c : C} {t1 b1 l m t2 b2 r : c = c}
    (et1 : refl = t1) (eb1 : refl = b1) (el : refl = l) (em : refl = m)
    (et2 : refl = t2) (eb2 : refl = b2) (er : refl = r)
    (s1 : Sq t1 b1 l m) (s2 : Sq t2 b2 m r)
    : sq_2loop (eq_trans2 et1 et2) (eq_trans2 eb1 eb2) el er (hpaste s1 s2)
      = sq_2loop et1 eb1 el em s1 ⋅ sq_2loop et2 eb2 em er s2.
  Proof.
    destruct et1, eb1, el, em, et2, eb2, er. cbn.
    unfold hpaste; cbn.
    exact (ap (fun u => s1 ⋅ u) (trans_1p s2 ⋅ ap_r_refl s2)
           ⋅ ap (fun u => u ⋅ _) (ap_idmap s1)
           ⋅ ap (fun u => u ⋅ _) (trans_1p _) ⋅ trans_1p _).
  Defined.

  Definition sq_2loop_vpaste {c : C} {t m l1 r1 bo l2 r2 : c = c}
    (et : refl = t) (em : refl = m) (el1 : refl = l1) (er1 : refl = r1)
    (eb : refl = bo) (el2 : refl = l2) (er2 : refl = r2)
    (s1 : Sq t m l1 r1) (s2 : Sq m bo l2 r2)
    : sq_2loop et eb (eq_trans2 el1 el2) (eq_trans2 er1 er2) (vpaste s1 s2)
      = sq_2loop em eb el2 er2 s2 ⋅ sq_2loop et em el1 er1 s1.
  Proof.
    destruct et, em, el1, er1, eb, el2, er2. cbn.
    unfold vpaste; cbn.
    exact (ap (fun u => s2 ⋅ u) (ap_idmap s1)
           ⋅ ap (fun u => u ⋅ _) (trans_1p s2 ⋅ ap_r_refl s2)
           ⋅ ap (fun u => u ⋅ _) (trans_1p _) ⋅ trans_1p _).
  Defined.

End Squares.

(** The w-outer reading respects composition in each variable. *)
Section ReadingPaste.

  Context {A B C : Type} (F : A -> B -> C).

  Definition reading_w_hpaste {a a' a'' : A} (p : a = a') (p' : a' = a'')
    {b b' : B} (q : b = b')
    : reading_w F (p' ⋅ p) q
      = Sq_sides (ap_trans (fun z => F z b) p p')⁻¹
                 (ap_trans (fun z => F z b') p p')⁻¹ refl refl
                 (hpaste (reading_w F p q) (reading_w F p' q)).
  Proof. destruct q, p', p. exact refl. Defined.

  Definition reading_w_vpaste {a a' : A} (p : a = a')
    {b b' b'' : B} (q : b = b') (q' : b' = b'')
    : reading_w F p (q' ⋅ q)
      = Sq_sides refl refl (ap_trans (F a) q q')⁻¹ (ap_trans (F a') q q')⁻¹
                 (vpaste (reading_w F p q) (reading_w F p q')).
  Proof. destruct q', q, p. exact refl. Defined.

End ReadingPaste.

(** *** Loops: the readings as 2-loops

    For loops [p] at [a] and [q] at [b], with the sides [ap_{F(-,b)}(p)]
    and [ap_{F(a,-)}(q)] identified with [refl], the w-outer reading is
    a 2-loop at [F(a,b)].  It is bilinear, and swapping the arguments of
    [F] inverts it. *)

(** Identifications of sides with [refl] for composite loops. *)
Definition ecomp {X Y : Type} (f : X -> Y) {x : X} {p p' : x = x}
  (e : refl = ap f p) (e' : refl = ap f p') : refl = ap f (p' ⋅ p)
  := (ap_trans f p p')⁻¹ ⋅ eq_trans2 e e'.

Section LoopReadings.

  Context {A B C : Type} (F : A -> B -> C) {a : A} {b : B}.

  Definition loops_reading (p : a = a) (q : b = b)
    (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q)
    : refl (F a b) = refl (F a b)
    := sq_2loop eP eP eQ eQ (reading_w F p q).

  (** Bilinearity, first variable. *)
  Definition loops_reading_hpaste (p p' : a = a) (q : b = b)
    (eP : refl = ap (fun z => F z b) p) (eP' : refl = ap (fun z => F z b) p')
    (eQ : refl = ap (F a) q)
    : loops_reading (p' ⋅ p) q (ecomp _ eP eP') eQ
      = loops_reading p q eP eQ ⋅ loops_reading p' q eP' eQ.
  Proof.
    unfold loops_reading.
    refine (_ ⋅ ap (sq_2loop _ _ _ _) (reading_w_hpaste F p p' q)).
    refine (_ ⋅ sq_2loop_sides _ _ refl refl _ _ eQ eQ _).
    exact (sq_2loop_hpaste eP eP eQ eQ eP' eP' eQ _ _).
  Defined.

  (** Bilinearity, second variable. *)
  Definition loops_reading_vpaste (p : a = a) (q q' : b = b)
    (eP : refl = ap (fun z => F z b) p)
    (eQ : refl = ap (F a) q) (eQ' : refl = ap (F a) q')
    : loops_reading p (q' ⋅ q) eP (ecomp _ eQ eQ')
      = loops_reading p q' eP eQ' ⋅ loops_reading p q eP eQ.
  Proof.
    unfold loops_reading.
    refine (_ ⋅ ap (sq_2loop _ _ _ _) (reading_w_vpaste F p q q')).
    refine (_ ⋅ sq_2loop_sides refl refl _ _ _ _ _ _ _).
    exact (sq_2loop_vpaste eP eP eQ eQ eP eQ' eQ' _ _).
  Defined.

End LoopReadings.

(** Swapping the arguments inverts the 2-loop. *)
Definition loops_reading_swap {A B C : Type} (F : A -> B -> C) {a : A} {b : B}
  (p : a = a) (q : b = b)
  (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q)
  : loops_reading (swap2 F) q p eQ eP = (loops_reading F p q eP eQ)⁻¹.
Proof.
  unfold loops_reading.
  refine (_ ⋅ ap (sq_2loop eQ eQ eP eP) (reading_w_swap F p q)).
  exact (sq_2loop_inv eP eP eQ eQ (reading_w F p q)).
Defined.


(** *** The case of [TBD2]: [loop³] and [loop²]

    Let [F : S¹ → S¹ → C] with the sides [ap_{F(-,base)}(loop)] and
    [ap_{F(base,-)}(loop)] identified with [refl] (for [F(z,w) :≡ m(z)(w)]
    these are [ptw(m(loop))(base) = m_loop(base) ≡ refl] and
    [ap_{cst}(loop) = refl]), and let [γ] be the 2-loop of [F(loop,loop)].
    Then the w-outer reading of [F(loop³,loop²)] is [6γ], and the
    z-outer one, which is [apd] of [z ↦ ap_{F(z,-)}(loop²)] applied to
    [loop³], is its inverse. *)
Section Loop3Loop2.

  Context {C : Type} (F : S1 -> S1 -> C)
    (eP : refl = ap (fun z => F z base) loop) (eQ : refl = ap (F base) loop).

  Definition loop2 : base = base := loop ⋅ loop.
  Definition loop3 : base = base := loop ⋅ loop2.

  Definition eP3 : refl = ap (fun z => F z base) loop3
    := ecomp _ (ecomp _ eP eP) eP.
  Definition eQ2 : refl = ap (F base) loop2 := ecomp _ eQ eQ.

  Definition γ : refl (F base base) = refl (F base base)
    := loops_reading F loop loop eP eQ.

  Definition loop1_loop2_reading
    : loops_reading F loop loop2 eP eQ2 = γ ⋅ γ
    := loops_reading_vpaste F loop loop loop eP eQ eQ.

  Definition loop3_loop2_reading
    : loops_reading F loop3 loop2 eP3 eQ2 = ((γ ⋅ γ) ⋅ (γ ⋅ γ)) ⋅ (γ ⋅ γ).
  Proof.
    refine (_ ⋅ loops_reading_hpaste F loop2 loop loop2 (ecomp _ eP eP) eP eQ2).
    exact (ap (fun u => (u ⋅ u) ⋅ u) loop1_loop2_reading
           ⋅ ap (fun u => u ⋅ _) (loops_reading_hpaste F loop loop loop2 eP eP eQ2)).
  Defined.

  (** The z-outer reading: [(6γ)⁻¹]. *)
  Definition loop3_loop2_reading_z
    : loops_reading (swap2 F) loop2 loop3 eQ2 eP3
      = (((γ ⋅ γ) ⋅ (γ ⋅ γ)) ⋅ (γ ⋅ γ))⁻¹
    := ap symm loop3_loop2_reading ⋅ loops_reading_swap F loop3 loop2 eP3 eQ2.

End Loop3Loop2.

(** *** Precomposition and powers, for [TBD1] *)

Local Definition ap_comp {X Y Z : Type} (f : X -> Y) (h : Y -> Z)
  {x x' : X} (p : x = x') : ap (fun z => h (f z)) p = ap h (ap f p)
  := match p with refl => refl end.

Section Precomposition.

  Context {A A' B B' C : Type} (F : A -> B -> C).

  (** Precomposition in the first variable. *)
  Definition reading_w_precomp1 (f : A' -> A) {a a' : A'} (p : a = a')
    {b b' : B} (q : b = b')
    : Sq_sides (ap_comp f (fun x => F x b) p) (ap_comp f (fun x => F x b') p)
               refl refl (reading_w (fun z w => F (f z) w) p q)
      = reading_w F (ap f p) q.
  Proof. destruct p, q. exact refl. Defined.

  (** Precomposition in the second variable. *)
  Definition reading_w_precomp2 (g : B' -> B) {a a' : A} (p : a = a')
    {b b' : B'} (q : b = b')
    : Sq_sides refl refl (ap_comp g (F a) q) (ap_comp g (F a') q)
               (reading_w (fun z w => F z (g w)) p q)
      = reading_w F p (ap g q).
  Proof. destruct p, q. exact refl. Defined.

  Definition loops_reading_precomp1 (f : A' -> A) {a : A'} {b : B}
    (p : a = a) (q : b = b)
    (eP : refl = ap (fun z => F (f z) b) p) (eQ : refl = ap (F (f a)) q)
    : loops_reading (fun z w => F (f z) w) p q eP eQ
      = loops_reading F (ap f p) q (ap_comp f (fun x => F x b) p ⋅ eP) eQ
    := ap (sq_2loop _ _ eQ eQ) (reading_w_precomp1 f p q)
       ⋅ (sq_2loop_sides _ _ refl refl eP eP eQ eQ _)⁻¹.

  Definition loops_reading_precomp2 (g : B' -> B) {a : A} {b : B'}
    (p : a = a) (q : b = b)
    (eP : refl = ap (fun z => F z (g b)) p) (eQ : refl = ap (fun w => F a (g w)) q)
    : loops_reading (fun z w => F z (g w)) p q eP eQ
      = loops_reading F p (ap g q) eP (ap_comp g (F a) q ⋅ eQ)
    := ap (sq_2loop eP eP _ _) (reading_w_precomp2 g p q)
       ⋅ (sq_2loop_sides refl refl _ _ eP eP eQ eQ _)⁻¹.

End Precomposition.

(** Transporting the loops along identifications. *)
Definition loops_reading_tr1 {A B C : Type} (F : A -> B -> C) {a : A} {b : B}
  {p p' : a = a} (α : p = p') (q : b = b)
  (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q)
  : loops_reading F p q eP eQ = loops_reading F p' q (ap (ap _) α ⋅ eP) eQ.
Proof. destruct α. exact refl. Defined.

Definition loops_reading_tr2 {A B C : Type} (F : A -> B -> C) {a : A} {b : B}
  (p : a = a) {q q' : b = b} (β : q = q')
  (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q)
  : loops_reading F p q eP eQ = loops_reading F p q' eP (ap (ap _) β ⋅ eQ).
Proof. destruct β. exact refl. Defined.

(** Powers [p^n] of a loop, with [p^{n+1} :≡ p ⋅ p^n], and of 2-loops. *)
Fixpoint ppow {X : Type} {x : X} (p : x = x) (n : nat) : x = x
  := match n with O => refl | S n => p ⋅ ppow p n end.

Fixpoint eppow {X Y : Type} (f : X -> Y) {x : X} {p : x = x}
  (e : refl = ap f p) (n : nat) : refl = ap f (ppow p n)
  := match n with O => refl | S n => ecomp f (eppow f e n) e end.

Definition gpow_comm {X : Type} {x : X} {y : x = x} (γ : y = y) (n : nat)
  : ppow γ n ⋅ γ = γ ⋅ ppow γ n.
Proof.
  induction n as [|n IH]; cbn.
  - exact (trans_1p γ)⁻¹.
  - exact (ap (fun u => γ ⋅ u) IH ⋅ (trans_assoc _ _ _)⁻¹).
Defined.

Section Powers.

  Context {A B C : Type} (F : A -> B -> C) {a : A} {b : B}.

  Local Definition sq_2loop_l {c : C} {l : c = c} (e : refl = l)
    : sq_2loop refl refl e e (trans_1p l) = refl.
  Proof. destruct e. exact refl. Defined.

  Local Definition sq_2loop_t {c : C} {t : c = c} (e : refl = t)
    : sq_2loop e e refl refl ((trans_1p t)⁻¹ ⋅ refl) = refl.
  Proof. destruct e. exact refl. Defined.

  Local Definition reading_w_refl1 {b' : B} (q : b = b')
    : reading_w F (refl a) q = trans_1p (ap (F a) q).
  Proof. destruct q. exact refl. Defined.

  (** [F(p^n,q)] has [n] times the 2-loop of [F(p,q)]. *)
  Definition loops_reading_pow1 (p : a = a) (q : b = b)
    (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q) (n : nat)
    : loops_reading F (ppow p n) q (eppow _ eP n) eQ
      = ppow (loops_reading F p q eP eQ) n.
  Proof.
    induction n as [|n IH].
    - exact (sq_2loop_l eQ ⋅ ap (sq_2loop refl refl eQ eQ) (reading_w_refl1 q)).
    - exact (gpow_comm _ n ⋅ ap (fun u => u ⋅ _) IH
             ⋅ loops_reading_hpaste F (ppow p n) p q (eppow _ eP n) eP eQ).
  Defined.

  (** [F(p,q^n)] has [n] times the 2-loop of [F(p,q)]. *)
  Definition loops_reading_pow2 (p : a = a) (q : b = b)
    (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q) (n : nat)
    : loops_reading F p (ppow q n) eP (eppow _ eQ n)
      = ppow (loops_reading F p q eP eQ) n.
  Proof.
    induction n as [|n IH].
    - exact (sq_2loop_t eP).
    - exact (ap (fun u => _ ⋅ u) IH
             ⋅ loops_reading_vpaste F p (ppow q n) q eP (eppow _ eQ n) eQ).
  Defined.

End Powers.

(** [TBD1]: precomposing with the degree [k] map [dg_k] in either
    variable multiplies the 2-loop of [F(loop,loop)] by [k]. *)
Section DegreePrecomposition.

  Context `{Univalence} {C : Type} (F : S1 -> S1 -> C)
    (eP : refl = ap (fun z => F z base) loop) (eQ : refl = ap (F base) loop)
    (k : nat).

  Definition loopZ_ppow (n : nat) : loopZ (iplus n) = ppow loop n.
  Proof.
    induction n as [|n IH].
    - exact refl.
    - exact (ap (fun u => loop ⋅ u) IH ⋅ loopZ_zs (iplus n)).
  Defined.

  Definition dg_loop : ap (dg k) loop = ppow loop k
    := loopZ_ppow k ⋅ S1_rec_loop S1 base (loopZ (iplus k)).

  Local Definition cancel {Y : Type} {r t0 t1 t2 : Y}
    (α : t1 = t0) (φ : t2 = t1) (E : r = t0)
    : α ⋅ (φ ⋅ (φ⁻¹ ⋅ α⁻¹ ⋅ E)) = E.
  Proof. destruct φ, α. exact refl. Defined.

  (** The sides of [F ∘ (dg_k × id)] and [F ∘ (id × dg_k)]. *)
  Definition eP_dg1 : refl = ap (fun z => F (dg k z) base) loop
    := (ap_comp (dg k) (fun x => F x base) loop)⁻¹
       ⋅ (ap (ap (fun x => F x base)) dg_loop)⁻¹ ⋅ eppow _ eP k.

  Definition eQ_dg2 : refl = ap (fun w => F base (dg k w)) loop
    := (ap_comp (dg k) (F base) loop)⁻¹
       ⋅ (ap (ap (F base)) dg_loop)⁻¹ ⋅ eppow _ eQ k.

  Definition loops_reading_dg1
    : loops_reading (fun z w => F (dg k z) w) loop loop eP_dg1 eQ
      = ppow (loops_reading F loop loop eP eQ) k
    := loops_reading_pow1 F loop loop eP eQ k
       ⋅ ap (fun e => loops_reading F (ppow loop k) loop e eQ) (cancel _ _ _)
       ⋅ loops_reading_tr1 F dg_loop loop _ eQ
       ⋅ loops_reading_precomp1 F (dg k) loop loop eP_dg1 eQ.

  Definition loops_reading_dg2
    : loops_reading (fun z w => F z (dg k w)) loop loop eP eQ_dg2
      = ppow (loops_reading F loop loop eP eQ) k
    := loops_reading_pow2 F loop loop eP eQ k
       ⋅ ap (fun e => loops_reading F loop (ppow loop k) eP e) (cancel _ _ _)
       ⋅ loops_reading_tr2 F loop dg_loop eP _
       ⋅ loops_reading_precomp2 F (dg k) loop loop eP eQ_dg2.

End DegreePrecomposition.

(** *** Independence of the side identifications, and negative degrees

    The 2-loop of a square of loops does not depend on how its sides are
    identified with [refl]: changing them conjugates it, and 2-loops
    commute (Eckmann-Hilton). *)
Section Independence.

  Context {C : Type} {c : C}.

  Local Definition sq_2loop_conj {t l : c = c} (e : refl = t) (f : refl = l)
    (s : Sq t t l l)
    : sq_2loop e e f f s
      = (ap011 (fun x y : c = c => y ⋅ x) f e)⁻¹
        ⋅ (s ⋅ ap011 (fun x y : c = c => y ⋅ x) e f).
  Proof. destruct e, f. exact (trans_1p s)⁻¹. Defined.

  Local Definition ap011_split {x x' y y' : c = c} (α : x = x') (β : y = y')
    : ap011 (fun x y : c = c => y ⋅ x) α β
      = ap (fun x => y ⋅ x) α @ ap (fun y => y ⋅ x') β.
  Proof. destruct α, β. exact refl. Defined.

  Local Definition ap_trans_refl {y y' : c = c} (β : y = y')
    : ap (fun z : c = c => z ⋅ refl) β = trans_1p y @ β @ (trans_1p y')^.
  Proof. destruct β. exact (whiskerR (concat_p1 _) _ @ concat_pV _)^. Defined.

  Local Definition ap011_2loops (α β : refl c = refl c :> (c = c))
    : ap011 (fun x y : c = c => y ⋅ x) α β = α @ β.
  Proof.
    refine (ap011_split α β @ _).
    refine (ap (fun u => u @ _) (ap_idmap α) @ _).
    exact (ap (fun u => α @ u) (ap_trans_refl β @ concat_p1 _ @ concat_1p _)).
  Defined.

  Definition sq_2loop_2loops (e f : refl c = refl c :> (c = c))
    (s : Sq (refl c) (refl c) (refl c) (refl c))
    : sq_2loop e e f f s = s.
  Proof.
    refine (sq_2loop_conj e f s @ _).
    refine (trans_is_concat _ _ @ _).
    refine (ap (fun u => u @ _) (trans_is_concat _ _) @ _).
    refine (ap (fun u => (_ @ s) @ u^) (ap011_2loops f e @ eckmann_hilton f e) @ _).
    refine (ap (fun u => (u @ s) @ _) (ap011_2loops e f) @ _).
    refine (ap (fun u => u @ _) (eckmann_hilton _ s) @ _).
    exact (concat_pp_V _ _).
  Defined.

  Definition sq_2loop_indep {t l : c = c} (e e' : refl = t) (f f' : refl = l)
    (s : Sq t t l l)
    : sq_2loop e e f f s = sq_2loop e' e' f' f' s.
  Proof. destruct e, f. exact (sq_2loop_2loops e' f' s)^. Defined.

End Independence.

Definition loops_reading_indep {A B C : Type} (F : A -> B -> C) {a : A} {b : B}
  (p : a = a) (q : b = b)
  (eP eP' : refl = ap (fun z => F z b) p) (eQ eQ' : refl = ap (F a) q)
  : loops_reading F p q eP eQ = loops_reading F p q eP' eQ'
  := sq_2loop_indep _ _ _ _ _.

(** Inverse loops give inverse 2-loops. *)
Section Inverses.

  Context {A B C : Type} (F : A -> B -> C) {a : A} {b : B}.

  Definition einv {X Y : Type} (f : X -> Y) {x : X} {p : x = x}
    (e : refl = ap f p) : refl = ap f p⁻¹
    := (ap_V f p)^ ⋅ ap inverse e.

  Local Definition cancel_r {X : Type} {x : X} {u v : x = x} (h : refl = v @ u)
    : v = u^
    := (concat_p1 _)^ @ whiskerL _ (concat_pV u)^ @ concat_p_pp _ _ _
       @ whiskerR h^ _ @ concat_1p _.

  Local Definition cancel_l {X : Type} {x : X} {u v : x = x} (h : refl = u @ v)
    : v = u^
    := (concat_1p _)^ @ whiskerR (concat_Vp u)^ _ @ concat_pp_p _ _ _
       @ whiskerL _ h^ @ concat_p1 _.

  Definition loops_reading_inv1 (p : a = a) (q : b = b)
    (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q)
    (eP' : refl = ap (fun z => F z b) p⁻¹)
    : loops_reading F p⁻¹ q eP' eQ = (loops_reading F p q eP eQ)⁻¹.
  Proof.
    apply cancel_r.
    refine (_ @ trans_is_concat _ _).
    refine (_ @ loops_reading_hpaste F p p⁻¹ q eP eP' eQ).
    refine (_ @ (loops_reading_tr1 F (trans_pV p) q _ eQ)^).
    exact ((loops_reading_pow1 F p q eP eQ 0)^ @ loops_reading_indep F _ q _ _ eQ eQ).
  Defined.

  Definition loops_reading_inv2 (p : a = a) (q : b = b)
    (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q)
    (eQ' : refl = ap (F a) q⁻¹)
    : loops_reading F p q⁻¹ eP eQ' = (loops_reading F p q eP eQ)⁻¹.
  Proof.
    apply cancel_l.
    refine (_ @ trans_is_concat _ _).
    refine (_ @ loops_reading_vpaste F p q q⁻¹ eP eQ eQ').
    refine (_ @ (loops_reading_tr2 F p (trans_pV q) eP _)^).
    exact ((loops_reading_pow2 F p q eP eQ 0)^ @ loops_reading_indep F p _ eP eP _ _).
  Defined.

End Inverses.

(** Integer powers [p^z] ([loopexp]) multiply the 2-loop by [z]. *)
Section IntPowers.

  Context {A B C : Type} (F : A -> B -> C) {a : A} {b : B}.

  Definition eloopexp {X Y : Type} (f : X -> Y) {x : X} {p : x = x}
    (e : refl = ap f p) (z : Int) : refl = ap f (loopexp p z).
  Proof.
    induction z as [|n IH|n IH].
    - exact refl.
    - exact ((ap (ap f) (loopexp_succ_r p n @ (trans_is_concat _ _)^))⁻¹ ⋅ ecomp f IH e).
    - exact ((ap (ap f) (loopexp_pred_r p _ @ (trans_is_concat _ _)^))⁻¹
             ⋅ ecomp f IH (einv f e)).
  Defined.

  Definition loops_reading_loopexp1 (p : a = a) (q : b = b)
    (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q) (z : Int)
    (e : refl = ap (fun z => F z b) (loopexp p z))
    : loops_reading F (loopexp p z) q e eQ = loopexp (loops_reading F p q eP eQ) z.
  Proof.
    revert e. induction z as [|n IH|n IH]; intro e.
    - exact (loops_reading_indep F _ q e refl eQ eQ @ loops_reading_pow1 F p q eP eQ 0).
    - refine (loops_reading_tr1 F (loopexp_succ_r p n @ (trans_is_concat _ _)^) q e eQ @ _).
      refine (loops_reading_indep F _ q _ (ecomp _ (eloopexp _ eP n) eP) eQ eQ @ _).
      refine (loops_reading_hpaste F _ p q _ eP eQ @ trans_is_concat _ _ @ _).
      exact (ap (fun u => _ @ u) (IH _) @ (loopexp_succ_l _ n)^).
    - refine (loops_reading_tr1 F (loopexp_pred_r p _ @ (trans_is_concat _ _)^) q e eQ @ _).
      refine (loops_reading_indep F _ q _
                (ecomp _ (eloopexp _ eP _) (einv _ eP)) eQ eQ @ _).
      refine (loops_reading_hpaste F _ p⁻¹ q _ _ eQ @ trans_is_concat _ _ @ _).
      refine (ap (fun u => u @ _) (loops_reading_inv1 F p q eP eQ _) @ _).
      exact (ap (fun u => _ @ u) (IH _) @ (loopexp_pred_l _ _)^).
  Defined.

  Definition loops_reading_loopexp2 (p : a = a) (q : b = b)
    (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q) (z : Int)
    (e : refl = ap (F a) (loopexp q z))
    : loops_reading F p (loopexp q z) eP e = loopexp (loops_reading F p q eP eQ) z.
  Proof.
    revert e. induction z as [|n IH|n IH]; intro e.
    - exact (loops_reading_indep F p _ eP eP e refl @ loops_reading_pow2 F p q eP eQ 0).
    - refine (loops_reading_tr2 F p (loopexp_succ_r q n @ (trans_is_concat _ _)^) eP e @ _).
      refine (loops_reading_indep F p _ eP eP _ (ecomp _ (eloopexp _ eQ n) eQ) @ _).
      refine (loops_reading_vpaste F p _ q eP _ eQ @ trans_is_concat _ _ @ _).
      exact (ap (fun u => u @ _) (IH _) @ (loopexp_succ_r _ n)^).
    - refine (loops_reading_tr2 F p (loopexp_pred_r q _ @ (trans_is_concat _ _)^) eP e @ _).
      refine (loops_reading_indep F p _ eP eP _
                (ecomp _ (eloopexp _ eQ _) (einv _ eQ)) @ _).
      refine (loops_reading_vpaste F p _ q⁻¹ eP _ _ @ trans_is_concat _ _ @ _).
      refine (ap (fun u => _ @ u) (loops_reading_inv2 F p q eP eQ _) @ _).
      exact (ap (fun u => u @ _) (IH _) @ (loopexp_pred_r _ _)^).
  Defined.

End IntPowers.

(** The degree [k] map for all [k : ℤ] ([dg] of [def:dgm-map] is
    [dgZ ∘ ι₊] by definition), and precomposition with it. *)
Definition dgZ `{Univalence} (k : ℤ) : S1 -> S1 := S1_rec S1 base (loopZ k).

Definition dg_dgZ `{Univalence} (n : nat) : dg n = dgZ (iplus n) := refl.

Section IntDegrees.

  Context `{Univalence} {C : Type} (F : S1 -> S1 -> C)
    (eP : refl = ap (fun z => F z base) loop) (eQ : refl = ap (F base) loop)
    (k : ℤ).

  Definition dgZ_loop : ap (dgZ k) loop = loopexp loop (toInt k)
    := S1_rec_loop S1 base (loopZ k).

  Definition loops_reading_dgZ1 (eP' : refl = ap (fun z => F (dgZ k z) base) loop)
    : loops_reading (fun z w => F (dgZ k z) w) loop loop eP' eQ
      = loopexp (loops_reading F loop loop eP eQ) (toInt k)
    := loops_reading_precomp1 F (dgZ k) loop loop eP' eQ
       @ loops_reading_tr1 F dgZ_loop loop _ eQ
       @ loops_reading_loopexp1 F loop loop eP eQ (toInt k) _.

  Definition loops_reading_dgZ2 (eQ' : refl = ap (fun w => F base (dgZ k w)) loop)
    : loops_reading (fun z w => F z (dgZ k w)) loop loop eP eQ'
      = loopexp (loops_reading F loop loop eP eQ) (toInt k)
    := loops_reading_precomp2 F (dgZ k) loop loop eP eQ'
       @ loops_reading_tr2 F loop dgZ_loop eP _
       @ loops_reading_loopexp2 F loop loop eP eQ (toInt k) _.

End IntDegrees.

(** *** The w-outer reading of a map [m : S¹ →* (S¹ →* B)]

    For a loop [ℓ] at the constant pointed map, and [m :≡ evp⁻¹(ℓ)]
    (so [m(base) :≡ cst], [m(loop) = ℓ], [m_pt :≡ refl]), the w-outer
    reading of [F(z,w) :≡ m(z)(w)] at [(loop,loop)] is [evp] of the
    pointed map [S¹ →* ΩB] corresponding to [ℓ]. *)

(** [X →* Y] pointed at the constant map [(cst_{pt}, refl)]. *)
Definition pmap_ptd (X Y : Ustar) : Ustar
  := ((X →* Y); ((fun _ => pt Y); refl)).

(** The w-outer reading of [G(p,q)] in terms of a path [φ] of functions
    identified with [ap_G(p)]. *)
Definition beta_w {A B C : Type} (G : A -> B -> C) {a a' : A} (p : a = a')
  {φ : G a = G a'} (θ : ap G p = φ) (w : B)
  : apD10 φ w = ap (fun z => G z w) p.
Proof. destruct θ, p. exact refl. Defined.

Definition reading_w_fun {A B C : Type} (G : A -> B -> C) {a a' : A}
  (p : a = a') {φ : G a = G a'} (θ : ap G p = φ) {b b' : B} (q : b = b')
  : reading_w G p q
    = Sq_sides (beta_w G p θ b) (beta_w G p θ b') refl refl
        (po_sq (u := G a) (v := G a') q (apd (apD10 φ) q)).
Proof. destruct θ, p, q. exact refl. Defined.

Local Definition sq_2loop_t1 {C : Type} {c : C} {t : c = c} (et : refl = t)
  (s : Sq t refl refl refl) : sq_2loop et refl refl refl s = s ⋅ et.
Proof. destruct et. exact (trans_1p s)⁻¹. Defined.

(** For a constant function the reading of a homotopy [h] is [ap_h],
    conjugated by the identifications of its ends with [refl]. *)
Definition const_reading {B C : Type} (c0 : C) (h : B -> c0 = c0)
  {b b' : B} (q : b = b') (et : refl = h b) (eb : refl = h b')
  : sq_2loop et eb (ap_const q c0)⁻¹ (ap_const q c0)⁻¹
      (po_sq (u := fun _ => c0) (v := fun _ => c0) q (apd h q))
    = eb⁻¹ ⋅ (ap h q ⋅ et).
Proof.
  destruct q. cbn. revert et eb. generalize (h b). intros t et eb.
  destruct eb. exact (sq_2loop_t1 et refl).
Defined.

Section PtdReading.

  Context `{Funext} (B : Ustar).

  Local Notation c := (pt (pmap_ptd S1star B)).

  Local Definition trp_pt_eqv {f g : S1 -> utype B} (φ : f = g)
    (u : pt B = f base) (v : pt B = g base)
    : (transport (fun f => pt B = f base) φ u = v) <~> (v = apD10 φ base ⋅ u).
  Proof. destruct φ. exact (equiv_path_inverse _ _). Defined.

  (** [ptw_*] at the constant map, directly: a loop [ℓ] at [c] goes to
      [(apD10(ap_fst(ℓ)), e)] with [e : refl = apD10(ap_fst(ℓ))(base)]. *)
  Definition lc_eqv : (c = c) ≃ (S1star →* loops B).
  Proof.
    apply Eqv_of_Equiv.
    refine (equiv_compose' _ (equiv_path_sigma _ c c)^-1).
    refine (equiv_functor_sigma' (equiv_apD10 _ _ _) _).
    intro φ. cbn.
    exact (equiv_compose' (equiv_concat_r (trans_1p _) _) (trp_pt_eqv φ refl refl)).
  Defined.

  Definition F_of (ℓ : c = c) : S1 -> S1 -> utype B
    := fun z w => fst (S1_rec _ c ℓ z) w.

  Definition theta_of (ℓ : c = c)
    : ap (fun z => fst (S1_rec _ c ℓ z)) loop = ap fst ℓ
    := ap_compose (S1_rec _ c ℓ) fst loop @ ap (ap fst) (S1_rec_loop _ c ℓ).

  Definition eP_of (ℓ : c = c) : refl = ap (fun z => F_of ℓ z base) loop
    := beta_w (fun z => fst (S1_rec _ c ℓ z)) loop (theta_of ℓ) base
       ⋅ snd (fst lc_eqv ℓ).

  Definition eQ_of (ℓ : c = c) : refl = ap (F_of ℓ base) loop
    := (ap_const loop (pt B))⁻¹.

  (** The w-outer reading of [F_of ℓ] at [(loop,loop)] is [evp] of the
      pointed map corresponding to [ℓ]. *)
  Definition reading_lc (ℓ : c = c)
    : loops_reading (F_of ℓ) loop loop (eP_of ℓ) (eQ_of ℓ)
      = evp _ (fst lc_eqv ℓ).
  Proof.
    unfold loops_reading.
    refine (ap (sq_2loop _ _ _ _)
              (reading_w_fun (fun z => fst (S1_rec _ c ℓ z)) loop (theta_of ℓ) loop) @ _).
    refine (sq_2loop_sides _ _ refl refl _ _ _ _ _ @ _).
    exact (const_reading (pt B) (apD10 (ap fst ℓ)) loop _ _).
  Defined.

End PtdReading.

(** The equivalence [M ≃ ℤ] of Example [exa:allS1*-swap]. *)
Section MEqvZ.

  Context `{Univalence}.

  (** [B²ℤ :≡ Σ_{X:U} ‖S¹ = X‖₀], pointed at [(S¹,|refl|)]. *)
  Definition B2Z : Ustar := ({X : Type & Tr 0 (S1 = X)}; (S1; tr refl)).

  Definition M : Type := S1star →* pmap_ptd S1star B2Z.

  (** Evaluation at [loop] ([evp], [cor:circle-loopspace]). *)
  Definition M_eqv_loops
    : M ≃ (pt (pmap_ptd S1star B2Z) = pt (pmap_ptd S1star B2Z))
    := (evp _; evp_isEquiv _).

  (** [ptw_*] ([con:identity-ptd-maps]) at the constant map, as
      [lc_eqv]. *)
  Definition loops_cst_eqv
    : (pt (pmap_ptd S1star B2Z) = pt (pmap_ptd S1star B2Z))
      ≃ (S1star →* loops B2Z)
    := lc_eqv B2Z.

  Definition omega2_eqv
    : (S1star →* loops B2Z) ≃ (refl (pt B2Z) = refl (pt B2Z))
    := (evp _; evp_isEquiv _).

  (** [Ω²B²ℤ ≃ (refl_{S¹} = refl_{S¹})]: the second component of a
      loop at [pt] is a path in the set [‖S¹ = S¹‖₀]. *)
  Definition sigma_step : (refl (pt B2Z) = refl (pt B2Z)) ≃ (refl S1 = refl S1).
  Proof.
    apply Eqv_of_Equiv.
    refine (equiv_compose' (equiv_path_sigma_hprop
      (P := fun p : S1 = S1 => transport (fun X => Tr 0 (S1 = X)) p (tr refl) = tr refl)
      (refl; refl) (refl; refl))^-1 _).
    exact (equiv_ap (equiv_path_sigma _ (pt B2Z) (pt B2Z))^-1 refl refl).
  Defined.

  (** [(refl_{S¹} = refl_{S¹}) ≃ ∏_x (x = x)]: univalence and function
      extensionality. *)
  Definition ua_step : (refl S1 = refl S1) ≃ (forall x : S1, x = x).
  Proof.
    apply Eqv_of_Equiv.
    refine (equiv_compose' (equiv_path_forall (fun x : S1 => x) (fun x => x))^-1 _).
    refine (equiv_compose' (Build_Equiv _ _ (ap (x := equiv_path S1 S1 refl)
              (y := equiv_path S1 S1 refl) (@equiv_fun S1 S1)) _) _).
    exact (equiv_ap (equiv_equiv_path S1 S1) refl refl).
  Defined.

  (** [∏_x (x = x) ≃ (base = base)]: evaluation at [base]
      ([xca:(S1->S1)_(f)-eqv-S1]). *)
  Definition ev_step : (forall x : S1, x = x) ≃ (base = base)
    := Eqv_of_Equiv (Build_Equiv _ _ _ (ev_base_S1_isEquiv idmap)).

  Definition omega2_B2Z_eqv : (refl (pt B2Z) = refl (pt B2Z)) ≃ ℤ
    := Eqv_comp sigma_step (Eqv_comp ua_step (Eqv_comp ev_step wdg)).

  Definition M_eqv_Z : M ≃ ℤ
    := Eqv_comp M_eqv_loops
         (Eqv_comp loops_cst_eqv (Eqv_comp omega2_eqv omega2_B2Z_eqv)).

  (** The maps [m_k : M] of the example, for [k : ℤ].  First the
      [k]-loop around [id_S¹]: pointwise it is [x ↦ ex(x)(loop^k)]
      ([ext_base_S1], the rotation extending [loop^k]); by function
      extensionality and univalence it is a 2-loop at [refl_{S¹}], and
      hence at [refl_{pt}] in [B²ℤ] (the truncated component being a
      set). *)
  Definition kloop_pw (k : ℤ) : forall x : S1, x = x
    := ext_base_S1 idmap (loopZ k).

  Definition kloop_id (k : ℤ) : refl S1 = refl S1
    := eqinv (snd ua_step) (kloop_pw k).

  Definition kloop (k : ℤ) : refl (pt B2Z) = refl (pt B2Z)
    := eqinv (snd sigma_step) (kloop_id k).

  (** [dg_k' : S¹ →* ΩB²ℤ], with [dg_k'(base) :≡ refl_{pt}],
      [dg_k'(loop) := kloop k], pointed by reflexivity. *)
  Definition dg_k' (k : ℤ) : S1star →* loops B2Z := evp_inv _ (kloop k).

  (** [m_k(base) :≡ pt], [m_k(loop) := ptw_*⁻¹(dg_k')] (with the
      pointing condition of [dg_k'] turned around as in
      [loops_cst_eqv]), [(m_k)_pt :≡ refl]. *)
  Definition m_k (k : ℤ) : M := evp_inv _ (eqinv (snd loops_cst_eqv) (dg_k' k)).

  Definition evp_evp_inv {A : Type} (a : A) (l : a = a) : evp a (evp_inv a l) = l
    := trans_1p _ @ S1_rec_loop A a l.

  Definition omega2_kloop (k : ℤ) : fst omega2_B2Z_eqv (kloop k) = k.
  Proof.
    change (fst wdg (fst ev_step (fst ua_step (fst sigma_step
              (eqinv (snd sigma_step) (kloop_id k))))) = k).
    refine (ap (fun x => fst wdg (fst ev_step (fst ua_step x)))
              (eqinv_r (snd sigma_step) _) @ _).
    refine (ap (fun x => fst wdg (fst ev_step x)) (eqinv_r (snd ua_step) _) @ _).
    exact (wdg_loopZ k).
  Defined.

  (** [M_eqv_Z] sends [m_k] to [k]. *)
  Definition M_eqv_Z_m (k : ℤ) : fst M_eqv_Z (m_k k) = k.
  Proof.
    change (fst omega2_B2Z_eqv (fst omega2_eqv (fst loops_cst_eqv
              (evp _ (evp_inv _ (eqinv (snd loops_cst_eqv) (dg_k' k)))))) = k).
    refine (ap (fun l => fst omega2_B2Z_eqv (fst omega2_eqv (fst loops_cst_eqv l)))
              (evp_evp_inv _ _) @ _).
    refine (ap (fun d => fst omega2_B2Z_eqv (fst omega2_eqv d))
              (eqinv_r (snd loops_cst_eqv) _) @ _).
    refine (ap (fst omega2_B2Z_eqv) (evp_evp_inv _ _) @ _).
    exact (omega2_kloop k).
  Defined.

  (** The w-outer reading of [m_k] (pointing paths forgotten,
      [F(z,w) :≡ m_k(z)(w)]) at [(loop,loop)] is the [k]-loop around
      [id_S¹], with the sides identified with [refl] by [eP_of] (from
      the pointing of [dg_k']) and [eQ_of] ([ap] of a constant). *)
  Definition ell_k (k : ℤ) : pt (pmap_ptd S1star B2Z) = pt (pmap_ptd S1star B2Z)
    := eqinv (snd loops_cst_eqv) (dg_k' k).

  Definition reading_m_k (k : ℤ)
    : loops_reading (fun z w => fst (fst (m_k k) z) w) loop loop
        (eP_of B2Z (ell_k k)) (eQ_of B2Z (ell_k k))
      = kloop k
    := reading_lc B2Z (ell_k k)
       @ ap (evp _) (eqinv_r (snd loops_cst_eqv) (dg_k' k))
       @ evp_evp_inv _ _.

  (** Hence it corresponds to [k] under [Ω²B²ℤ ≃ ℤ]. *)
  Definition reading_m_k_Z (k : ℤ)
    : fst omega2_B2Z_eqv
        (loops_reading (fun z w => fst (fst (m_k k) z) w) loop loop
           (eP_of B2Z (ell_k k)) (eQ_of B2Z (ell_k k)))
      = k
    := ap (fst omega2_B2Z_eqv) (reading_m_k k) @ omega2_kloop k.

  (** The composite of [sigma_step], [ua_step] and [ev_step] as a
      single [ap]: it sends a 2-loop [x] to [ap] of
      [r ↦ ptoe(ap_fst(r))(base)] at [x]; so it preserves powers. *)
  Definition Psi (x : refl (pt B2Z) = refl (pt B2Z)) : base = base
    := ap (fun r : pt B2Z = pt B2Z => transport idmap (ap pr1 r) base) x.

  Local Definition inv_path_sigma_hprop_pr1 {A : Type} {P : A -> Type}
    `{forall x, IsHProp (P x)} (u v : sig P) (r : u = v)
    : (equiv_path_sigma_hprop u v)^-1 r = ap pr1 r
    := (pr1_path_path_sigma_hprop u v _)^
       @ ap (fun r => r..1) (eisretr (path_sigma_hprop u v) r).

  Local Definition apD10_ap_ev {X Y : Type} {f g : X -> Y} (q : f = g) (x : X)
    : apD10 q x = ap (fun h => h x) q.
  Proof. destruct q. exact refl. Defined.

  Local Definition ap5 {A1 A2 A3 A4 A5 A6 : Type} (h1 : A1 -> A2) (h2 : A2 -> A3)
    (h3 : A3 -> A4) (h4 : A4 -> A5) (h5 : A5 -> A6) {a a' : A1} (x : a = a')
    : ap (fun r => h5 (h4 (h3 (h2 (h1 r))))) x = ap h5 (ap h4 (ap h3 (ap h2 (ap h1 x)))).
  Proof. destruct x. exact refl. Defined.

  Definition Psi_eq (x : refl (pt B2Z) = refl (pt B2Z))
    : Psi x = fst ev_step (fst ua_step (fst sigma_step x)).
  Proof.
    change (Psi x = apD10 (ap (@equiv_fun S1 S1) (ap (equiv_path S1 S1)
              ((equiv_path_sigma_hprop
                (P := fun p : S1 = S1 => transport (fun X => Tr 0 (S1 = X)) p (tr refl) = tr refl)
                (refl; refl) (refl; refl))^-1
                 (ap (equiv_path_sigma _ (pt B2Z) (pt B2Z))^-1 x)))) base).
    refine (_ @ (apD10_ap_ev _ base)^).
    refine (_ @ (ap (fun y => ap (fun h : S1 -> S1 => h base)
                   (ap (@equiv_fun S1 S1) (ap (equiv_path S1 S1) y)))
                   (inv_path_sigma_hprop_pr1 _ _ _))^).
    exact (ap5 (equiv_path_sigma _ (pt B2Z) (pt B2Z))^-1 pr1 (equiv_path S1 S1)
             (@equiv_fun S1 S1) (fun h : S1 -> S1 => h base) x).
  Defined.

  Definition Psi_inj {x y : refl (pt B2Z) = refl (pt B2Z)} (e : Psi x = Psi y) : x = y.
  Proof.
    pose (E := Eqv_comp sigma_step (Eqv_comp ua_step ev_step)).
    refine ((eqinv_l (snd E) x)^ @ _ @ eqinv_l (snd E) y).
    exact (ap (eqinv (snd E)) ((Psi_eq x)^ @ e @ Psi_eq y)).
  Defined.

  Definition Psi_kloop (k : ℤ) : Psi (kloop k) = loopZ k.
  Proof.
    refine (Psi_eq _ @ _).
    change (fst ev_step (fst ua_step (fst sigma_step
              (eqinv (snd sigma_step) (kloop_id k)))) = loopZ k).
    refine (ap (fun x => fst ev_step (fst ua_step x)) (eqinv_r (snd sigma_step) _) @ _).
    exact (ap (fst ev_step) (eqinv_r (snd ua_step) _)).
  Defined.

  (** [γ :≡ kloop 1] (the generator), and [kloop k = γ^k]. *)
  Definition gamma : refl (pt B2Z) = refl (pt B2Z) := kloop (iplus 1).

  Definition kloop_pow (k : ℤ) : kloop k = loopexp gamma (toInt k).
  Proof.
    apply Psi_inj.
    refine (Psi_kloop k @ _ @ (ap_loopexp _ gamma (toInt k))^).
    exact (ap (fun p => loopexp p (toInt k))
             (Psi_kloop (iplus 1) @ loopexp_succ_r loop zero @ concat_1p loop))^.
  Defined.

  (** Integer powers in the library's sense agree with [ppow] on [ℕ]. *)
  Definition loopexp_ppow {X : Type} {x : X} (p : x = x) (n : nat)
    : loopexp p (toInt (iplus n)) = ppow p n.
  Proof.
    induction n as [|n IH].
    - exact refl.
    - exact (ap (loopexp p) (toInt_zs (iplus n)) @ loopexp_succ_r p _
             @ (trans_is_concat _ _)^ @ ap (fun u => p ⋅ u) IH).
  Defined.

  (** Write [F_k(z,w) :≡ m_k(z)(w)], with the sides of its square at
      [(loop,loop)] identified with [refl] by [eP_k], [eQ_k]. *)
  Definition F_k (k : ℤ) : S1 -> S1 -> utype B2Z := fun z w => fst (fst (m_k k) z) w.
  Definition eP_k (k : ℤ) := eP_of B2Z (ell_k k).
  Definition eQ_k (k : ℤ) := eQ_of B2Z (ell_k k).

  (** The w-outer reading of [m_k] is [kγ], with [γ] that of [m_1]. *)
  Definition reading_m_1 : loops_reading (F_k (iplus 1)) loop loop (eP_k _) (eQ_k _) = gamma
    := reading_m_k (iplus 1).

  Definition reading_m_k_gamma (k : ℤ)
    : loops_reading (F_k k) loop loop (eP_k k) (eQ_k k) = loopexp gamma (toInt k)
    := reading_m_k k @ kloop_pow k.

  (** [TBD1], for [k : ℕ]: precomposing [m_1] with the degree [k] map in
      either argument gives the same 2-loop as [m_k]. *)
  Definition reading_m_1_dg1 (n : nat)
    : loops_reading (fun z w => F_k (iplus 1) (dg n z) w) loop loop
        (eP_dg1 (F_k (iplus 1)) (eP_k _) n) (eQ_k _)
      = loops_reading (F_k (iplus n)) loop loop (eP_k _) (eQ_k _)
    := loops_reading_dg1 _ _ _ n @ ap (fun g => ppow g n) reading_m_1
       @ (reading_m_k_gamma (iplus n) @ loopexp_ppow gamma n)^.

  Definition reading_m_1_dg2 (n : nat)
    : loops_reading (fun z w => F_k (iplus 1) z (dg n w)) loop loop
        (eP_k _) (eQ_dg2 (F_k (iplus 1)) (eQ_k _) n)
      = loops_reading (F_k (iplus n)) loop loop (eP_k _) (eQ_k _)
    := loops_reading_dg2 _ _ _ n @ ap (fun g => ppow g n) reading_m_1
       @ (reading_m_k_gamma (iplus n) @ loopexp_ppow gamma n)^.

  (** By [loops_reading_indep] the choice of [eP_k], [eQ_k] does not
      matter. *)
  Definition reading_m_k_any (k : ℤ)
    (eP : refl = ap (fun z => F_k k z base) loop) (eQ : refl = ap (F_k k base) loop)
    : loops_reading (F_k k) loop loop eP eQ = loopexp gamma (toInt k)
    := loops_reading_indep _ _ _ _ _ _ _ @ reading_m_k_gamma k.

  (** [TBD1] for all [k : ℤ]: precomposing [m_1] with the degree [k]
      map ([dgZ]) in either argument gives the 2-loop of [m_k], for any
      identifications of the sides with [refl]. *)
  Definition reading_m_1_dgZ1 (k : ℤ)
    (eP' : refl = ap (fun z => F_k (iplus 1) (dgZ k z) base) loop)
    (eQ' : refl = ap (F_k (iplus 1) base) loop)
    (eP : refl = ap (fun z => F_k k z base) loop) (eQ : refl = ap (F_k k base) loop)
    : loops_reading (fun z w => F_k (iplus 1) (dgZ k z) w) loop loop eP' eQ'
      = loops_reading (F_k k) loop loop eP eQ
    := loops_reading_indep (fun z w => F_k (iplus 1) (dgZ k z) w) loop loop
         eP' eP' eQ' (eQ_k _)
       @ loops_reading_dgZ1 _ (eP_k _) (eQ_k _) k eP'
       @ ap (fun g => loopexp g (toInt k)) reading_m_1
       @ (reading_m_k_any k eP eQ)^.

  Definition reading_m_1_dgZ2 (k : ℤ)
    (eP' : refl = ap (fun z => F_k (iplus 1) z base) loop)
    (eQ' : refl = ap (fun w => F_k (iplus 1) base (dgZ k w)) loop)
    (eP : refl = ap (fun z => F_k k z base) loop) (eQ : refl = ap (F_k k base) loop)
    : loops_reading (fun z w => F_k (iplus 1) z (dgZ k w)) loop loop eP' eQ'
      = loops_reading (F_k k) loop loop eP eQ
    := loops_reading_indep (fun z w => F_k (iplus 1) z (dgZ k w)) loop loop
         eP' (eP_k _) eQ' eQ'
       @ loops_reading_dgZ2 _ (eP_k _) (eQ_k _) k eQ'
       @ ap (fun g => loopexp g (toInt k)) reading_m_1
       @ (reading_m_k_any k eP eQ)^.

End MEqvZ.
