(** * Section 13.1 Rings, abstract and concrete

    Part of Chapter 13 ([fields.tex]); see [Fields.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    Only the sign question [TBD2] of Example [exa:allS1*-swap] is
    formalized so far; the other labels of this section are not
    formalized yet (no [_stmt]s either: the chapter is still in flux).

    The example studies [M :≡ S¹ →* (S¹ →* B²ℤ)] and maps
    [m_k : M] given by [m_k(base) :≡ pt] and [m_k(loop) := ptw_*⁻¹(k')]
    with [k'(base) :≡ refl_pt] and [k'(loop)] the [k]-loop around
    [id_S¹].  [TBD2] asks whether [swap(m_k)] is [m_k] or [m_{-k}].

    Forget the pointing paths and write [F(z,w) :≡ m(z)(w)] for
    [m :≡ m_1].  A pair of paths [p] in [z] and [q] in [w] gives a
    square [F(p,q)], which can be read in two ways, as a path over [p]
    or as a path over [q]:
    - z-outer: [apd] of [z ↦ ap_{F(z,-)}(q)] applied to [p]
      ([reading_z]);
    - w-outer: [apd] of [w ↦ ap_{F(-,w)}(p)] applied to [q]
      ([reading_w]).
    Both are turned into squares by the same conversion [po_sq] of paths
    over a path in a family of identity types [x ↦ (u(x) = v(x))].

    - [reading_w_z]: for any [F : A → B → C] and any paths [p], [q],
      [reading_w F p q = (reading_z F p q)⁻¹].  This is the sign:
      transposing a square inverts it.
    - [reading_w_swap]: [reading_w (swap2 F) q p ≡ reading_z F p q], so
      [reading_w (swap2 F) q p = (reading_w F p q)⁻¹].
    - [loops_reading_w_swap]: the same for loops [p], [q], when the four
      sides are identified with [refl], so that both readings are
      2-loops in [C]: the 2-loop of [swap2 F] is the inverse of that
      of [F].

    How this answers [TBD2].  By definition of [m], the w-outer reading
    is the natural one: [ap_{F(-,w)}(loop) = ptw(m(loop))(w) = k'(w)], so
    the w-outer reading of [F(loop,loop)] is [ap_{k'}(loop)], the
    generator [γ] of [Ω²(B²ℤ) ≃ ℤ] (corresponding to [k = 1]); this is
    also how [M ≃ Ω²(B²ℤ)] reads off [m].  For [swap(m)] the outer
    variable is [w], so its w-outer reading is the z-outer reading of
    [m], which is [γ⁻¹] by [loops_reading_w_swap].  Hence
    [swap(m_1) = m_{-1}], and likewise [swap(m_k) = m_{-k}]: the twist
    on [S¹ ∧ S¹ ≃ S²] has degree [-1].

    In particular, applying [z ↦ ap_{m(z)}(loop²)] to [loop³] gives the
    z-outer reading of [F(loop³,loop²)], which is [(6γ)⁻¹]: the w-outer
    reading is [ap_{k'³}(loop²) = 6γ] by bilinearity.

    Not formalized: [B²ℤ], [m_k] and the identification of the w-outer
    reading with [γ] (these need the set truncation of [S¹ = X],
    univalence and [ptw_*]), and the bilinearity giving the factor 6.
    The sign is independent of all of this: it holds for any [F]. *)

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

(** *** Example [exa:allS1*-swap], [TBD2]: the sign of [swap] *)

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

(** A square of loops at [c] whose sides are identified with [refl] is
    a 2-loop at [c]. *)
Definition sq_2loop {C : Type} {c : C} {x y x' y' : c = c}
  (ex : x = refl) (ey : y = refl) (ex' : x' = refl) (ey' : y' = refl)
  : (x ⋅ y = y' ⋅ x') -> (refl c = refl c).
Proof.
  destruct (ex⁻¹), (ey⁻¹), (ex'⁻¹), (ey'⁻¹). exact (id _).
Defined.

Definition sq_2loop_inv {C : Type} {c : C} {x y x' y' : c = c}
  (ex : x = refl) (ey : y = refl) (ex' : x' = refl) (ey' : y' = refl)
  (s : x ⋅ y = y' ⋅ x')
  : sq_2loop ey' ex' ey ex s⁻¹ = (sq_2loop ex ey ex' ey' s)⁻¹.
Proof.
  revert s. revert ey'. revert y'. revert ex'. revert x'.
  revert ey. revert y. revert ex. revert x.
  refine (paths_ind_r _ _ _). refine (paths_ind_r _ _ _).
  refine (paths_ind_r _ _ _). refine (paths_ind_r _ _ _).
  intro s. exact refl.
Defined.

(** For loops [p] at [a] and [q] at [b], with the sides [ap_{F(-,b)}(p)]
    and [ap_{F(a,-)}(q)] identified with [refl], both readings are
    2-loops at [F(a,b)], and swapping the arguments inverts the
    2-loop. *)
Section LoopReadings.

  Context {A B C : Type} (F : A -> B -> C) {a : A} {b : B}
    (p : a = a) (q : b = b)
    (eP : ap (fun z => F z b) p = refl) (eQ : ap (F a) q = refl).

  Definition loops_reading_w : refl (F a b) = refl (F a b)
    := sq_2loop eQ eP eQ eP (reading_w F p q).

  Definition loops_reading_w_swap
    : sq_2loop eP eQ eP eQ (reading_w (swap2 F) q p) = loops_reading_w⁻¹.
  Proof.
    unfold loops_reading_w.
    refine (_ ⋅ ap (sq_2loop eP eQ eP eQ) (reading_w_swap F p q)).
    exact (sq_2loop_inv eQ eP eQ eP (reading_w F p q)).
  Defined.

End LoopReadings.

(** The case of [TBD2]: [p :≡ loop³] and [q :≡ loop²] in [S¹]; applying
    [z ↦ ap_{F(z,-)}(loop²)] to [loop³] is the z-outer reading, the
    inverse of the w-outer one. *)
Definition loop3_loop2_reading {C : Type} (F : S1 -> S1 -> C)
  : reading_z F (loop ⋅ loop ⋅ loop) (loop ⋅ loop)
    = (reading_w F (loop ⋅ loop ⋅ loop) (loop ⋅ loop))⁻¹
  := (symm_symm _ ⋅ ap symm (reading_w_z F _ _))⁻¹.
