(** * Section 13.1 Rings, abstract and concrete

    Part of Chapter 13 ([fields.tex]); see [Fields.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    Only the questions [TBD1] and [TBD2] of Example [exa:allS1*-swap]
    are addressed so far; the other labels of this section are not
    formalized yet (no [_stmt]s either: the chapter is still in flux).

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
    2-loop at [(loop,loop)] by [k], so under [M ≃ Ω²(B²ℤ) ≃ ℤ]
    (read off at [(loop,loop)]) [m_k = m_1 ∘ (dg_k × id) = m_1 ∘ (id ×
    dg_k)], and [m_k] corresponds to [k].

    Not formalized: [B²ℤ], [m_k], the equivalence [M ≃ ℤ] and the
    identification of the w-outer reading of [m_k] with [kγ] (these
    need the set truncation of [S¹ = X], univalence and [ptw_*]).  The
    sign and the bilinearity are independent of all of this: they hold
    for any [F]. *)

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
