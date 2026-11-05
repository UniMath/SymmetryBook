(** * Section 13.1 Rings, abstract and concrete

    Part of Chapter 13 ([fields.tex]); see [Fields.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    Only the questions [TBD1] and [TBD2] of Example [exa:allS1*-swap]
    and the claim [M ≃ ℤ] of that example are addressed so far; the
    other labels of this section are not formalized yet (no [_stmt]s
    either: the chapter is still in flux).

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
    - [loops_cst_eqv]: [Ω(S¹ →* B²ℤ) ≃ (S¹ →* ΩB²ℤ)] by [ptw_*]
      ([con:identity-ptd-maps]) and turning the pointing condition
      [h(base) ⋅ refl = refl] into [refl = h(base)].
    - [omega2_eqv]: [(S¹ →* ΩB²ℤ) ≃ Ω²B²ℤ], [evp] again.
    - [omega2_B2Z_eqv]: [Ω²B²ℤ ≃ ℤ], along the second argument of the
      example: the second component of [pt = pt] is a path in the set
      [‖S¹ = S¹‖₀], so [Ω²B²ℤ ≃ (refl_{S¹} = refl_{S¹})]; by univalence
      and function extensionality this is [∏_x (x = x)], which is
      [base = base] by evaluation at [base] ([ev_base_S1_isEquiv], from
      [xca:(S1->S1)_(f)-eqv-S1]), and that is [ℤ] by [wdg].
    - [M_eqv_Z]: the composite [M ≃ ℤ].

    Not formalized: [m_k], the value of [M_eqv_Z] at [m_k] and the
    identification of the w-outer reading of [m_k] with [kγ], and
    negative [k].  The sign and the bilinearity are independent of all
    of this: they hold for any [F]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core Spaces.Circle.
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

(** The equivalence [M ≃ ℤ] of Example [exa:allS1*-swap]. *)
Section MEqvZ.

  Context `{Univalence}.

  (** [B²ℤ :≡ Σ_{X:U} ‖S¹ = X‖₀], pointed at [(S¹,|refl|)]. *)
  Definition B2Z : Ustar := ({X : Type & Tr 0 (S1 = X)}; (S1; tr refl)).

  (** [X →* Y] pointed at the constant map [(cst_{pt}, refl)]. *)
  Definition pmap_ptd (X Y : Ustar) : Ustar
    := ((X →* Y); ((fun _ => pt Y); refl)).

  Definition M : Type := S1star →* pmap_ptd S1star B2Z.

  (** Evaluation at [loop] ([evp], [cor:circle-loopspace]). *)
  Definition M_eqv_loops
    : M ≃ (pt (pmap_ptd S1star B2Z) = pt (pmap_ptd S1star B2Z))
    := (evp _; evp_isEquiv _).

  (** [ptw_*] ([con:identity-ptd-maps]) at the constant map. *)
  Definition loops_cst_eqv
    : (pt (pmap_ptd S1star B2Z) = pt (pmap_ptd S1star B2Z))
      ≃ (S1star →* loops B2Z).
  Proof.
    refine (Eqv_comp (ptw_star _ _) _).
    apply Eqv_of_Equiv. refine (equiv_functor_sigma_id _). intro h. cbn.
    refine (equiv_compose' (equiv_path_inverse _ _) _).
    exact (equiv_concat_l (trans_1p (h base))^ _).
  Defined.

  Definition omega2_eqv
    : (S1star →* loops B2Z) ≃ (refl (pt B2Z) = refl (pt B2Z))
    := (evp _; evp_isEquiv _).

  (** [Ω²B²ℤ ≃ (refl_{S¹} = refl_{S¹}) ≃ ∏_x (x = x) ≃ (base = base)
      ≃ ℤ]. *)
  Definition omega2_B2Z_eqv : (refl (pt B2Z) = refl (pt B2Z)) ≃ ℤ.
  Proof.
    apply (Eqv_comp (Y := (refl S1 = refl S1))).
    - apply Eqv_of_Equiv.
      refine (equiv_compose' (equiv_path_sigma_hprop
        (P := fun p : S1 = S1 => transport (fun X => Tr 0 (S1 = X)) p (tr refl) = tr refl)
        (refl; refl) (refl; refl))^-1 _).
      exact (equiv_ap (equiv_path_sigma _ (pt B2Z) (pt B2Z))^-1 refl refl).
    - apply (Eqv_comp (Y := (forall x : S1, x = x))).
      + apply Eqv_of_Equiv.
        refine (equiv_compose' (equiv_path_forall (fun x : S1 => x) (fun x => x))^-1 _).
        refine (equiv_compose'
                  (equiv_path_equiv (equiv_path S1 S1 refl) (equiv_path S1 S1 refl))^-1 _).
        exact (equiv_ap (equiv_equiv_path S1 S1) refl refl).
      + apply (Eqv_comp (Y := (base = base))).
        * apply Eqv_of_Equiv. exact (Build_Equiv _ _ _ (ev_base_S1_isEquiv idmap)).
        * exact wdg.
  Defined.

  Definition M_eqv_Z : M ≃ ℤ
    := Eqv_comp M_eqv_loops
         (Eqv_comp loops_cst_eqv (Eqv_comp omega2_eqv omega2_B2Z_eqv)).

End MEqvZ.
