(** * Section 3.7 Interlude: combinatorics of permutations

    Part of Chapter 3 ([circle.tex]); see [Circle.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - For a decidable set [A]: fixed points, moved elements and the
      support of a permutation ([def:support-permutation]); the exercise
      that permutations with disjoint supports commute
      ([disjoint_commute]).
    - Transpositions [(a b)] ([transp]), which are involutions.
    - Cyclic permutations [(a₁ ⋯ a_k)] for a list of pairwise distinct
      elements ([cyc]), and exercise [xca:perm-prod-transpositions]:
      [(a₁ a₂ ⋯ a_k) = (a₁ a_k)⋯(a₁ a₂)] ([cyc_transps]), from the step
      [(a₁ a₂ a₃ ⋯ a_k) = (a₁ a₃ ⋯ a_k)(a₁ a₂)].
    - Exercise [xca:factorial]: a finite set of cardinality [n] has [n!]
      permutations ([card_Aut]), via the library's [fcard_aut].

    - Orbits in a finite set (used, but not spelled out, in the book): for
      a permutation [t] of a finite set and [x₀], the orbit
      [x_k :≡ t^k(x₀)] returns to [x₀] (by the pigeonhole principle
      [lem:PHP]), and [x₀, …, x_{d₀}] are pairwise distinct for the least
      return [d₀+1] ([period_data], [ox_idx_inj]); [orbit_cyc] is the
      cyclic permutation [(x₀ x₁ ⋯ x_{d₀})], which agrees with [t] on the
      orbit and fixes everything else ([orbit_cyc_in], [orbit_cyc_out]).
    - Remark [rem:cycle-vs-cycle], first part: for a cycle [(X,t)] with
      [X] an [n]-element set and [x₀ : X], [t] is the cyclic permutation
      [(x₀ t(x₀) ⋯ t^{n-1}(x₀))] of pairwise distinct elements
      ([cycle_as_cyc]).  The orbit exhausts [X] ([cycle_inorb]), so
      [X ≃ {k | k < d₀+1}] ([cycle_count_eqv]) and [d₀+1 = n].
      NOTE for the book text: that the [n] elements listed are pairwise
      distinct needs the pigeonhole principle; the remark could say so.
    - Remark [rem:cycle-vs-cycle], second part: for a permutation [t] of a
      set [X], [X ≃ ∑_{q : X/∼} orbit(q)] ([cycle_decomp]), with [t]
      corresponding to [∑_q t_q] ([orbit_t], [cycle_decomp_t]); each
      [(orbit(q), t_q)] is a cycle ([orbit_isCycle]), so its covering over
      [S1] is connected ([orbit_conn]).  The orbits are the components of
      the covering of [t] by [quot_eqv] (3.6).  We decompose on the side
      of permutations rather than coverings.
    - The corollary that every permutation of a finite set is a composite
      of transpositions ([perm_transpositions], with [transpsL]), as in
      the book: we peel off the cyclic permutation of one orbit at a time
      ([peelEqv], [peel_factor]) and write each as transpositions by
      [xca:perm-prod-transpositions].

    - Remark [rem:cycle-vs-cycle]: a cyclic permutation moves only the
      elements of its list ([cyc_fixes]).

    - The exercise on binomial coefficients (after
      [def:support-permutation]): a set of cardinality [n] has
      [n!/(k!(n-k)!)] subsets with [k] elements ([xca_binomial_subsets])
      and [n!/(k!(n-k)!)⋅(k-1)!] [k]-cycle permutations for [2 ≤ k ≤ n]
      ([xca_kcycles], with [isKCycle]); both multiplied out, avoiding
      division.  Subsets are counted through their characteristic maps
      to [Bool] and Pascal's rule (the library's [nat_choose]).  For
      [k]-cycles, the distinct lists of length [k] number [n!/(n-k)!]
      ([fcard_DL]), and each [k]-cycle [σ] comes from exactly [k] of them,
      one for each element of its support, since such a list is the orbit
      list of its first element ([list_seg], [fcard_F]).
      The book assumes [2 ≤ k ≤ n] for both parts (the only [1]-cycle
      is the identity); the subsets are counted for all [k ≤ n].
    - That [(ℤ, zs)] is not a cyclic permutation ([zs_not_cyc]): the
      integer [1 + Σ_a nat(a)] is not in the list ([iplus_notin]), so
      [cyc] fixes it.
    - The corollary with [a ≠ b] for each pair [(a, b)] in the list
      ([perm_transpositions_ne]), by dropping the pairs [(a, a)]
      ([filter_ne]).

    Left out (not formalized)
    - The claim in [rem:cycle-vs-cycle] that turning a transposition
      into a cycle requires decidability (a statement about what cannot
      be proved). *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Spaces.Nat.Core Spaces.Int
  Spaces.Circle Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core Spaces.List.Theory Types.Sum Types.Unit Types.Empty
  Spaces.Nat.Binomial Spaces.Nat.Factorial Spaces.Nat.Division HFiber.
From SymmetryBook Require Export Circle.S06_ConnCoverings.

Local Open Scope uf_scope.

(** ** 3.7 Interlude: combinatorics of permutations *)

Section Permutations.

  Context `{Funext} {A : Type} (dA : isDecSet A).

  Definition deceq (a b : A) : isDecidable (a = b) := snd (dA a b).

  Definition not_not_eq {a b : A} (nn : ¬ ¬ (a = b)) : a = b
    := match deceq a b with inl e => e | inr n => match nn n with end end.

  (** Definition [def:support-permutation]: fixed points, moved elements and
      the support of a permutation. *)
  Definition fixed (σ : A ≃ A) (a : A) : Type := fst σ a = a.

  Definition moved (σ : A ≃ A) (a : A) : Type := ¬ fixed σ a.

  Definition support (σ : A ≃ A) : Type := {a : A & moved σ a}.

  Definition moved_dec (σ : A ≃ A) (a : A) : isDecidable (moved σ a)
    := match deceq (fst σ a) a with
       | inl e => inr (fun n => n e)
       | inr n => inl n
       end.

  Definition moved_image (σ : A ≃ A) (a : A) (m : moved σ a) : moved σ (fst σ a)
    := fun e => m (Eqv_inj σ e).

  (** Exercise: permutations with disjoint supports commute. *)
  Definition disjoint (σ τ : A ≃ A) : Type := forall a, ¬ (moved σ a × moved τ a).

  Definition disjoint_commute (σ τ : A ≃ A) (d : disjoint σ τ)
    : fst σ ∘ fst τ = fst τ ∘ fst σ.
  Proof.
    apply ptw_inv. intro a. unfold comp.
    destruct (deceq (fst σ a) a) as [e|n].
    - destruct (deceq (fst τ a) a) as [e'|n'].
      + exact ((ap (fst σ) e' @ e) @ (ap (fst τ) e @ e')^).
      + assert (f : fst σ (fst τ a) = fst τ a)
          by exact (not_not_eq (fun ns => d (fst τ a) (ns; moved_image τ a n'))).
        exact (f @ (ap (fst τ) e)^).
    - assert (f : fst τ (fst σ a) = fst σ a)
        by exact (not_not_eq (fun nt => d (fst σ a) (moved_image σ a n; nt))).
      assert (g : fst τ a = a) by exact (not_not_eq (fun nt => d a (n; nt))).
      exact (ap (fst σ) g @ f^).
  Defined.

  (** Transpositions [(a b)]. *)
  Definition transp (a b : A) (x : A) : A
    := match deceq x a with
       | inl _ => b
       | inr _ => match deceq x b with inl _ => a | inr _ => x end
       end.

  Definition transp_invol (a b x : A) : transp a b (transp a b x) = x.
  Proof.
    unfold transp at 2.
    destruct (deceq x a) as [ea|na].
    - unfold transp. destruct (deceq b a) as [eba|nba].
      + exact (eba @ ea^).
      + destruct (deceq b b) as [_|nbb]; [exact ea^ | destruct (nbb refl)].
    - destruct (deceq x b) as [eb|nb].
      + unfold transp. destruct (deceq a a) as [_|naa]; [exact eb^ | destruct (naa refl)].
      + unfold transp. destruct (deceq x a) as [ea|_]; [destruct (na ea)|].
        destruct (deceq x b) as [eb|_]; [destruct (nb eb) | exact refl].
  Defined.

  Definition transpEqv (a b : A) : A ≃ A
    := mkEqv (transp a b) (transp a b) (transp_invol a b) (transp_invol a b).

  (** Cyclic permutations [(a₁ a₂ ⋯ a_k)], for a list of pairwise distinct
      elements: [a_i ↦ a_{i+1}], [a_k ↦ a₁], other elements fixed.  We give
      it by [next l h x], which maps an element of [l] to its successor in
      [l], the last element to [h], and fixes elements not in [l]. *)
  Fixpoint next (l : list A) (h x : A) : A
    := match l with
       | nil => x
       | cons b r => match deceq x b with
                     | inl _ => match r with nil => h | cons c _ => c end
                     | inr _ => next r h x
                     end
       end.

  Definition cyc (a1 : A) (r : list A) : A -> A := next (cons a1 r) a1.

  Fixpoint notin (x : A) (l : list A) : Type
    := match l with nil => Unit | cons b r => (x ≠ b) × notin x r end.

  Fixpoint distinct (l : list A) : Type
    := match l with nil => Unit | cons b r => notin b r × distinct r end.

  Definition next_notin (l : list A) (h x : A) (n : notin x l) : next l h x = x.
  Proof.
    induction l as [|b r IH].
    - exact refl.
    - cbn. destruct (deceq x b) as [e|_]; [destruct (fst n e) | exact (IH (snd n))].
  Defined.

  (** [next (b :: r)] differs from [next r] only at [b] and at the last
      element of [r]. *)
  Definition next_cons_ne (b c : A) (r : list A) (h x : A) (nb : x ≠ b)
    : next (cons b (cons c r)) h x = next (cons c r) h x.
  Proof. cbn. destruct (deceq x b) as [e|_]; [destruct (nb e) | exact refl]. Defined.

  (** Exercise [xca:perm-prod-transpositions]:
      [(a₁ a₂ ⋯ a_k) = (a₁ a_k)(a₁ a_{k-1})⋯(a₁ a₂)], from the step
      [(a₁ a₂ a₃ ⋯ a_k) = (a₁ a₃ ⋯ a_k)(a₁ a₂)]. *)
  Fixpoint transps (a1 : A) (r : list A) : A -> A
    := match r with
       | nil => idmap
       | cons b r' => fun x => transps a1 r' (transp a1 b x)
       end.


  Definition cyc_step (a1 a2 : A) (r : list A) (n12 : a1 ≠ a2) (n2 : notin a2 r) (x : A)
    : cyc a1 (cons a2 r) x = cyc a1 r (transp a1 a2 x).
  Proof.
    unfold cyc, transp.
    destruct (deceq x a1) as [e1|n1].
    - destruct e1. cbn. destruct (deceq x x) as [_|nxx]; [|destruct (nxx refl)].
      destruct (deceq a2 x) as [e|_]; [destruct (n12 e^)|].
      exact (next_notin r x a2 n2)^.
    - destruct (deceq x a2) as [e2|n2'].
      + destruct e2. cbn.
        destruct (deceq x a1) as [e|_]; [destruct (n1 e)|].
        destruct (deceq x x) as [_|nxx]; [|destruct (nxx refl)].
        destruct (deceq a1 a1) as [_|naa]; [exact refl | destruct (naa refl)].
      + cbn. destruct (deceq x a1) as [e|_]; [destruct (n1 e)|].
        destruct (deceq x a2) as [e|_]; [destruct (n2' e) | exact refl].
  Defined.

  Definition cyc_transps (a1 : A) (r : list A) (dr : distinct (cons a1 r)) (x : A)
    : cyc a1 r x = transps a1 r x.
  Proof.
    revert x. induction r as [|b r IH]; intro x.
    - unfold cyc. cbn. destruct (deceq x a1) as [e|_]; [exact e^ | exact refl].
    - refine (cyc_step a1 b r (fst (fst dr)) (fst (snd dr)) x @ _).
      exact (IH (snd (fst dr); snd (snd dr)) _).
  Defined.

  (** Remark [rem:cycle-vs-cycle]: a cyclic permutation moves only the
      elements of its list.
    (Placed after [xca:perm-prod-transpositions], since it uses the cyclic permutations [cyc] defined there.) *)
  Definition cyc_fixes (a1 : A) (r : list A) (x : A) (n : notin x (cons a1 r))
    : cyc a1 r x = x
    := next_notin (cons a1 r) a1 x n.

End Permutations.

(** Hence the infinite cycle [(ℤ, zs)] is not a cyclic permutation:
    some [x] is not in the list, so [cyc] fixes it, but [zs] does not. *)
Definition zs_not_cyc_stmt : Type
  := forall (dZ : isDecSet ℤ) (a1 : ℤ) (r : list ℤ), ¬ (forall x, zs x = cyc dZ a1 r x).

Fixpoint sum_nat_of_int (l : list ℤ) : ℕ
  := match l with nil => 0%nat | cons b r => nat_add (nat_of_int (toInt b)) (sum_nat_of_int r) end.

Definition nat_of_int_iplus (k : ℕ) : nat_of_int (toInt (iplus k)) = k
  := match k with O => refl | S _ => refl end.

Definition nat_ne_S_add (n j : ℕ) : n ≠ S (nat_add n j).
Proof.
  induction n as [|n IH].
  - intro e. exact (trp (fun k : ℕ => match k with O => True | S _ => Empty end) e triv).
  - intro e. exact (IH (ap nat_pred e)).
Defined.

(** [iplus (S (Σ + k))] is not in the list, where [Σ] sums the
    [nat_of_int] of its elements. *)
Definition iplus_notin (l : list ℤ) : forall k : ℕ,
  notin (iplus (S (nat_add (sum_nat_of_int l) k))) l.
Proof.
  induction l as [|b r IH]; intro k.
  - exact tt.
  - split.
    + intro e. apply (nat_ne_S_add (nat_of_int (toInt b)) (nat_add (sum_nat_of_int r) k)).
      refine ((ap (fun z => nat_of_int (toInt z)) e)^ @ nat_of_int_iplus _ @ _).
      exact (ap S (nat_add_assoc _ _ _)^).
    + refine (trp (fun m => notin (iplus (S m)) r) _ (IH (nat_add (nat_of_int (toInt b)) k))).
      exact (nat_add_assoc _ _ _ @ ap (fun m => nat_add m k) (nat_add_comm _ _)).
Defined.

Definition zs_not_cyc : zs_not_cyc_stmt.
Proof.
  intros dZ a1 r h.
  pose (M := nat_add (sum_nat_of_int (cons a1 r)) 0).
  pose (e := h (iplus (S M)) @ cyc_fixes dZ a1 r _ (iplus_notin (cons a1 r) 0)).
  exact (nat_ne_S_add (S M) 0 ((iplus_inj e)^ @ ap S (nat_add_zero_r _)^)).
Defined.

(** Exercise [xca:factorial]: a finite set of cardinality [n] has [n!]
    permutations, via the library's [fcard_aut] instead of the bijection
    [eq:type-factorial] of the hint. *)
Definition Aut (X : Type) : Type := X ≃ X.

Definition Aut_isFinSet `{Univalence} {X : Type} (h : isFinSet X) : isFinSet (Aut X)
  := isFinSet_Eqv (Eqv_inv (Equiv_Eqv_eqv X X))
       (Finite_isFinSet (@finite_aut _ X (isFinSet_Finite h))).

Definition card_Aut `{Univalence} {X : Type} (h : isFinSet X)
  : cardF (Aut_isFinSet h) = fact (cardF h).
Proof.
  refine (cardF_fcard _ @ _ @ ap fact (cardF_fcard h)^).
  refine (_ @ @fcard_aut _ X (isFinSet_Finite h)).
  exact (@fcard_equiv' _ _ (Equiv_of_Eqv (Eqv_inv (Equiv_Eqv_eqv X X))) _ _).
Defined.

(** ** Cycles versus cyclic permutations *)

(** A bounded search for the least witness of a decidable family. *)
Definition least_dec (Q : ℕ -> Type) (dq : forall k, isDecidable (Q k))
  : forall b : ℕ, {k : ℕ & (k < b)%nat × (Q k × forall k', (k' < k)%nat -> ¬ Q k')}
                  ⨿ (forall k, (k < b)%nat -> ¬ Q k).
Proof.
  intro b. induction b as [|b IH].
  - right. intros k l. destruct (not_lt_zero_r k l).
  - destruct IH as [[k [l q]]|nq].
    + left. exact (k; (lt_trans l (leq_refl (S b)); q)).
    + destruct (dq b) as [q|nq'].
      * left. exact (b; (leq_refl (S b); (q; nq))).
      * right. intros k l.
        destruct (lt_succ_cases l) as [l'|e].
        -- exact (nq k l').
        -- destruct e. exact nq'.
Defined.

Section Orbit.

  Context `{Funext} {X : Type} (dA : isDecSet X) (t : X ≃ X) (x0 : X).

  (** The orbit [x_k :≡ t^k(x₀)]. *)
  Definition ox (k : ℕ) : X := iter (fst t) k x0.

  Definition iter_inj (k : ℕ) {y y' : X} (e : iter (fst t) k y = iter (fst t) k y') : y = y'.
  Proof.
    induction k as [|k IH].
    - exact e.
    - exact (IH (Eqv_inj t e)).
  Defined.

  Definition ox_add (a b : ℕ) : ox (a + b) = iter (fst t) a (ox b)
    := nat_iter_add a b (fst t) x0.

  (** If [x_k = x_m] with [m ≤ k], then [x_{k-m} = x₀]. *)
  Definition ox_shift {m k : ℕ} (l : (m <= k)%nat) (e : ox k = ox m) : ox (k - m)%nat = x0.
  Proof.
    apply (iter_inj m).
    exact ((ox_add m (k - m)%nat)^ @ ap ox (nat_add_sub_r_cancel l) @ e).
  Defined.

  (** The finite set is given by an injection into [{k | k < n}]. *)
  Context (n : ℕ) (code : X -> ℕ) (code_lt : forall x, (code x < n)%nat)
    (code_inj : forall x x', code x = code x' -> x = x').

  (** By the pigeonhole principle, the orbit returns to [x₀]. *)
  Definition orbit_return : {j : ℕ & (0 < j)%nat × (ox j = x0)}.
  Proof.
    destruct (PHP_lib n (fun k => code (ox k)) (fun k _ => code_lt (ox k)))
      as [m [k [lmk [_ e]]]].
    exact ((k - m)%nat; (equiv_lt_lt_sub k m lmk; ox_shift (leq_lt lmk) (code_inj _ _ e))).
  Defined.

  (** The least return: [x_{d} = x₀] for [d :≡ d₀+1], and [x_{k+1} ≠ x₀]
      for [k < d₀]. *)
  Definition period_data
    : {d0 : ℕ & (ox (S d0) = x0) × (forall k, (k < d0)%nat -> ox (S k) ≠ x0)}.
  Proof.
    destruct orbit_return as [j [lj ej]].
    destruct (least_dec (fun k => ox (S k) = x0) (fun k => snd (dA (ox (S k)) x0)) j)
      as [[k [_ [q mn]]]|none].
    - exact (k; (q; mn)).
    - destruct j as [|j].
      + destruct (lt_irrefl 0 lj).
      + destruct (none j (leq_refl (S j)) ej).
  Defined.

  Definition d0 : ℕ := fst period_data.

  Definition ox_period : ox (S d0) = x0 := fst (snd period_data).

  Definition ox_minimal : forall k, (k < d0)%nat -> ox (S k) ≠ x0
    := snd (snd period_data).

  (** [x₀, …, x_{d₀}] are pairwise distinct. *)
  Definition ox_lt_ne {i i' : ℕ} (l : (i < i')%nat) (l' : (i' < S d0)%nat)
    (e : ox i = ox i') : False.
  Proof.
    pose (q := ox_shift (leq_lt l) e^).
    pose (p := equiv_lt_lt_sub i' i l).
    pose (b := leq_sub_l i' i).
    clearbody q p b. revert q p b. generalize (i' - i)%nat. intros [|j] q p b.
    - exact (lt_irrefl 0 p).
    - exact (ox_minimal j (leq_pred' (lt_leq_lt_trans b l')) q).
  Defined.

  Definition ox_idx_inj {i i' : ℕ} (l : (i < S d0)%nat) (l' : (i' < S d0)%nat)
    (e : ox i = ox i') : i = i'.
  Proof.
    destruct (nat_trichotomy i i') as [[lt|eq]|gt].
    - destruct (ox_lt_ne lt l' e).
    - exact eq.
    - destruct (ox_lt_ne gt l e^).
  Defined.

  (** Membership in the orbit [{x₀, …, x_{d₀}}]. *)
  Definition inorb (y : X) : Type := {i : ℕ & (i < S d0)%nat × (y = ox i)}.

  Definition inorb_isProp (y : X) : isProp (inorb y).
  Proof.
    intros [i [l e]] [i' [l' e']].
    apply (path_sigma_prop (fun _ => prod_isProp (IsHProp_isProp (P := (_ < _)%nat))
                                       (fst (dA _ _)))).
    exact (ox_idx_inj l l' (e^ @ e')).
  Defined.

  Definition inorb_dec (y : X) : isDecidable (inorb y)
    := match bounded_dec (fun i => y = ox i) (fun i => snd (dA y (ox i))) (S d0) with
       | inl w => inl w
       | inr nw => inr (fun w => nw (fst w) (fst (snd w)) (snd (snd w)))
       end.

  Definition inorb_ox (k : ℕ) (l : (k < S d0)%nat) : inorb (ox k) := (k; (l; refl)).

  Definition inorb_t (y : X) (w : inorb y) : inorb (fst t y).
  Proof.
    destruct w as [i [l e]].
    destruct (equiv_leq_lt_or_eq l) as [l'|q].
    - exact (S i; (l'; ap (fst t) e)).
    - exact (0%nat; (leq_succ (leq_zero_l d0); ap (fst t) e @ ap ox q @ ox_period)).
  Defined.

  Definition inorb_tinv (y : X) (w : inorb y) : inorb (eqinv (snd t) y).
  Proof.
    destruct w as [[|i] [l e]].
    - refine (d0; (leq_refl (S d0); _)).
      exact (ap (eqinv (snd t)) (e @ ox_period^) @ eqinv_l (snd t) (ox d0)).
    - refine (i; (leq_succ_r (leq_pred' l); _)).
      exact (ap (eqinv (snd t)) e @ eqinv_l (snd t) (ox i)).
  Defined.

  Definition inorb_tpow (z : ℤ) : ptrunc (inorb (tpow t z x0)).
  Proof.
    revert z. refine (ℤ_ind_prop _ (fun _ => ptrunc_isProp) _ _).
    - intro k. apply trunc. induction k as [|k IH].
      + exact (inorb_ox 0%nat (leq_succ (leq_zero_l d0))).
      + exact (inorb_t _ IH).
    - intros [k]. apply trunc. induction k as [|k IH].
      + exact (inorb_ox 0%nat (leq_succ (leq_zero_l d0))).
      + exact (inorb_tinv _ IH).
  Defined.

  (** The list [x_s, x_{s+1}, …, x_{s+m-1}]. *)
  Fixpoint seg (s m : ℕ) : list X
    := match m with
       | O => nil
       | S m' => cons (ox s) (seg (S s) m')
       end.

  Definition seg_notin (y : X) : forall m s,
    (forall j, (s <= j)%nat -> (j < m + s)%nat -> y ≠ ox j) -> notin y (seg s m).
  Proof.
    intro m. induction m as [|m IH]; intros s h.
    - exact tt.
    - refine (h s (leq_refl s) (leq_succ (leq_add_l s m)); IH (S s) _).
      intros j l l'. apply (h j (leq_succ_l l)).
      exact (trp (fun z => (j < z)%nat) (nat_add_succ_r m s) l').
  Defined.

  Definition seg_distinct : forall m s, (m + s <= S d0)%nat -> distinct (seg s m).
  Proof.
    intro m. induction m as [|m IH]; intros s lm.
    - exact tt.
    - change (notin (ox s) (seg (S s) m) × distinct (seg (S s) m)).
      refine (_; _); [|exact (IH (S s) (trp (fun z => (z <= S d0)%nat) (nat_add_succ_r m s)^ lm))].
      apply seg_notin. intros j l l' e.
      refine (ox_lt_ne l _ e).
      exact (lt_lt_leq_trans (trp (fun z => (j < z)%nat) (nat_add_succ_r m s) l') lm).
  Defined.

  (** [next] on a segment maps [x_k] to [x_{k+1}], and the last element
      to [h]. *)
  Definition next_seg (h : X) : forall m s k,
    (s <= k)%nat -> (k < m + s)%nat -> (m + s <= S d0)%nat ->
    ((S k < m + s)%nat -> next dA (seg s m) h (ox k) = ox (S k))
    × (S k = (m + s)%nat -> next dA (seg s m) h (ox k) = h).
  Proof.
    intro m. induction m as [|m IH]; intros s k ls lk lm.
    - destruct (lt_irrefl k (lt_lt_leq_trans lk ls)).
    - cbn [seg next].
      destruct (deceq dA (ox k) (ox s)) as [e|ne].
      + assert (p : k = s).
        { exact (ox_idx_inj (lt_lt_leq_trans lk lm)
                   (lt_leq_lt_trans ls (lt_lt_leq_trans lk lm)) e). }
        destruct p. destruct m as [|m].
        * exact ((fun l => match lt_irrefl _ l with end); (fun _ => refl)).
        * refine ((fun _ => refl); _). intro e'.
          pose (e'' := path_nat_succ _ _ e' : k = S (m + k)%nat).
          destruct (lt_irrefl k (trp (fun z => (k < z)%nat) e''^ (leq_succ (leq_add_l k m)))).
      + destruct (equiv_leq_lt_or_eq ls) as [l|q]; [|destruct (ne (ap ox q^))].
        pose (E := nat_add_succ_r m s).
        destruct (IH (S s) k l (trp (fun z => (k < z)%nat) E^ lk)
                    (trp (fun z => (z <= S d0)%nat) E^ lm)) as [a b].
        exact ((fun l2 => a (trp (fun z => (S k < z)%nat) E^ l2));
               (fun e2 => b (e2 @ E^))).
  Defined.

  (** The cyclic permutation [(x₀ x₁ ⋯ x_{d₀})]. *)
  Definition orbit_cyc : X -> X := cyc dA x0 (seg 1 d0).

  Definition orbit_distinct : distinct (cons x0 (seg 1 d0))
    := seg_distinct (S d0) 0
         (trp (fun z => (z <= S d0)%nat) (nat_add_zero_r (S d0))^ (leq_refl _)).

  Definition orbit_cyc_ox (k : ℕ) (lk : (k < S d0)%nat)
    : orbit_cyc (ox k) = fst t (ox k).
  Proof.
    pose (E := nat_add_zero_r (S d0)).
    destruct (next_seg x0 (S d0) 0 k (leq_zero_l k) (trp (fun z => (k < z)%nat) E^ lk)
                (trp (fun z => (z <= S d0)%nat) E^ (leq_refl _))) as [a b].
    destruct (equiv_leq_lt_or_eq lk) as [l|q].
    - exact (a (trp (fun z => (S k < z)%nat) E^ l)).
    - exact (b (q @ E^) @ ox_period^ @ (ap ox q)^).
  Defined.

  Definition orbit_cyc_in (y : X) (w : inorb y) : orbit_cyc y = fst t y
    := ap orbit_cyc (snd (snd w)) @ orbit_cyc_ox (fst w) (fst (snd w))
       @ (ap (fst t) (snd (snd w)))^.

  Definition orbit_cyc_out (y : X) (nw : ¬ inorb y) : orbit_cyc y = y.
  Proof.
    refine (next_notin dA (seg 0 (S d0)) x0 y _).
    apply seg_notin. intros j _ l e.
    exact (nw (j; (trp (fun z => (j < z)%nat) (nat_add_zero_r (S d0)) l; e))).
  Defined.

  (** If [(X,t)] is a cycle, every element is in the orbit of [x₀], and
      [X ≃ {k | k < d₀+1}]. *)
  Definition cycle_inorb (cy : isCycle t) (y : X) : inorb y.
  Proof.
    destruct (inorb_dec y) as [w|nw]; [exact w|].
    refine (match _ : False with end).
    refine (ptrunc_rec False_isProp _ (snd cy x0 y)). intros [z e].
    refine (ptrunc_rec False_isProp _ (inorb_tpow z)). intro w.
    exact (nw (trp inorb e^ w)).
  Defined.

  Definition cycle_count_eqv (cy : isCycle t) : X ≃ FinNat (S d0).
  Proof.
    refine (mkEqv (fun y => (fst (cycle_inorb cy y); fst (snd (cycle_inorb cy y))))
                  (fun w => ox (fst w)) _ _).
    - intro y. exact (snd (snd (cycle_inorb cy y)))^.
    - intros [i l]. apply (path_sigma_prop (fun _ => IsHProp_isProp (P := (_ < _)%nat))).
      exact (ox_idx_inj (fst (snd (cycle_inorb cy (ox i)))) l
               (snd (snd (cycle_inorb cy (ox i))))^).
  Defined.

End Orbit.


Definition notin_isProp `{Funext} {A : Type} (x : A) (l : list A) : isProp (notin x l).
Proof.
  induction l as [|b r IH].
  - intros [] []. exact refl.
  - exact (prod_isProp (fun_isProp False_isProp) IH).
Defined.

Definition distinct_isProp `{Funext} {A : Type} (l : list A) : isProp (distinct l).
Proof.
  induction l as [|b r IH].
  - intros [] []. exact refl.
  - exact (prod_isProp (notin_isProp b r) IH).
Defined.

(** Finite sets given by an identification [Fin n = X], as an injection
    into [{k | k < n}]. *)
Section FinCode.

  Context `{Funext} {X : Type} {n : ℕ} (e : Fin n = X :> Type).

  Definition fin_codeEqv : X ≃ FinNat n
    := Eqv_comp (idtoeqv e^) (Eqv_of_Equiv (equiv_fin_finnat n)).

  Definition fin_code (x : X) : ℕ := fst (fst fin_codeEqv x).

  Definition fin_code_lt (x : X) : (fin_code x < n)%nat := snd (fst fin_codeEqv x).

  Definition fin_code_inj (x x' : X) (p : fin_code x = fin_code x') : x = x'
    := Eqv_inj fin_codeEqv
         (path_sigma_prop (fun _ => IsHProp_isProp (P := (_ < _)%nat)) (u := fst fin_codeEqv x) (v := fst fin_codeEqv x') p).

End FinCode.

(** Remark [rem:cycle-vs-cycle], first part: for a cycle [(X,t)] with [X]
    an [n]-element set and [x₀ : X], the permutation [t] is the cyclic
    permutation [(x₀ t(x₀) ⋯ t^{n-1}(x₀))], and these elements are
    pairwise distinct.
    (Placed after [xca:perm-prod-transpositions], since it uses the cyclic permutations [cyc] defined there.) *)
Definition cycle_as_cyc `{Univalence} {X : Type} (dA : isDecSet X) (t : X ≃ X)
  (cy : isCycle t) (n : ℕ) (hn : ptrunc (Fin n = X :> Type)) (x0 : X)
  : distinct (cons x0 (seg t x0 1 (nat_pred n)))
    × (forall x, cyc dA x0 (seg t x0 1 (nat_pred n)) x = fst t x).
Proof.
  refine (ptrunc_rec (prod_isProp (distinct_isProp _) (Pi_isProp (fun x => fst (dA _ _)))) _ hn).
  intro e.
  pose (d := d0 dA t x0 n (fin_code e) (fin_code_lt e) (fin_code_inj e)).
  assert (nd : n = S d).
  { refine (nat_eq_fin_equiv n (S d) (Equiv_of_Eqv _)).
    refine (Eqv_comp (idtoeqv e) (Eqv_comp (cycle_count_eqv dA t x0 n _ _ _ cy) _)).
    exact (Eqv_inv (Eqv_of_Equiv (equiv_fin_finnat (S d)))). }
  refine (trp (fun j => distinct (cons x0 (seg t x0 1 j))
                        × (forall x, cyc dA x0 (seg t x0 1 j) x = fst t x))
              (ap nat_pred nd)^ _).
  refine (orbit_distinct dA t x0 n _ _ _; _).
  intro x. exact (orbit_cyc_in dA t x0 n _ _ _ x (cycle_inorb dA t x0 n _ _ _ cy x)).
Defined.

(** Remark [rem:cycle-vs-cycle], second part: a permutation [t] of a set
    [X] is the sum of cycles, one for each orbit [q : X/∼] (the
    components of the covering [∑_{z:S1} E(z)], by [quot_eqv]). *)
Section CycleDecomposition.

  Context `{Univalence} {X : Type} (sX : isSet X) (t : X ≃ X).

  Local Notation R := (conn_by t).

  Local Notation clsR := (cls R).

  Definition orbit (q : Q t) : Type := fiber clsR q.

  Definition orbit_isSet (q : Q t) : isSet (orbit q)
    := Sigma_isSet sX (fun _ => prop_is_set (quot_isSet R _ _)).

  Definition cls_t (x : X) : clsR (fst t x) = clsR x
    := snd (cls_eq_iff R (conn_by_refl t) (conn_by_sym sX t) (conn_by_trans sX t) _ _)
         (conn_by_sym sX t x (fst t x) (trunc (iplus 1; refl))).

  Definition cls_tinv (y : X) : clsR (eqinv (snd t) y) = clsR y
    := (cls_t (eqinv (snd t) y))^ @ ap clsR (eqinv_r (snd t) y).

  (** The restriction [t_q] of [t] to the orbit [q]. *)
  Definition orbit_t_fun (q : Q t) (w : orbit q) : orbit q
    := (fst t (fst w); snd w @ (cls_t (fst w))^).

  Definition orbit_t_inv (q : Q t) (w : orbit q) : orbit q
    := (eqinv (snd t) (fst w); snd w @ (cls_tinv (fst w))^).

  Definition orbit_t (q : Q t) : orbit q ≃ orbit q.
  Proof.
    refine (mkEqv (orbit_t_fun q) (orbit_t_inv q) _ _);
      intro w; apply (path_sigma_prop (fun _ => quot_isSet R _ _)).
    - exact (eqinv_l (snd t) (fst w)).
    - exact (eqinv_r (snd t) (fst w)).
  Defined.

  Definition orbit_tpow (q : Q t) (z : ℤ) (w : orbit q)
    : fst (tpow (orbit_t q) z w) = tpow t z (fst w).
  Proof.
    revert z w. refine (ℤ_ind_prop _ (fun z => Pi_isProp (fun w => sX _ _)) _ _).
    - intros k w. induction k as [|k IH].
      + exact refl.
      + exact (ap (fst t) IH).
    - intros [k] w. induction k as [|k IH].
      + exact refl.
      + exact (ap fst (eqinv_mkEqv (orbit_t_fun q) (orbit_t_inv q) _ _ _) @ ap (eqinv (snd t)) IH).
  Defined.

  (** Each [(orbit q, t_q)] is a cycle, so its covering over [S1] is
      connected (theorem [thm:cycset-connS1cover]). *)
  Definition orbit_isCycle (q : Q t) : isCycle (orbit_t q).
  Proof.
    refine (_; _).
    - exact (im_ind R (fun q => ptrunc (orbit q)) (fun _ => ptrunc_isProp)
               (fun x => trunc (x; refl)) q).
    - intros [x p] [x' p'].
      refine (ptrunc_rec ptrunc_isProp _
                (fst (cls_eq_iff R (conn_by_refl t) (conn_by_sym sX t) (conn_by_trans sX t) x x')
                   (p^ @ p'))).
      intros [z e]. apply trunc. refine (z; _).
      apply (path_sigma_prop (fun _ => quot_isSet R _ _)).
      exact (e @ (orbit_tpow q z (x; p))^).
  Defined.

  Definition orbit_conn (q : Q t) : isConn (AE (orbit_t q))
    := isCycle_conn (orbit_isSet q) (orbit_t q) (orbit_isCycle q).

  (** [X ≃ ∑_{q : X/∼} orbit(q)], and under this equivalence [t]
      corresponds to [∑_q t_q]. *)
  Definition cycle_decomp : X ≃ {q : Q t & orbit q} := total_fibers clsR.

  Definition cycle_decomp_t (w : {q : Q t & orbit q})
    : fst (snd ((fst w; orbit_t_fun (fst w) (snd w)) : {q : Q t & orbit q}))
      = fst t (fst (snd w))
    := refl.

End CycleDecomposition.

(** Composites of transpositions. *)
Section Transpositions.

  Context `{Funext} {X : Type} (dA : isDecSet X).

  (** [τ(l) :≡ (a_k b_k) ⋯ (a₁ b₁)] for [l = ((a₁,b₁), …, (a_k,b_k))]. *)
  Fixpoint transpsL (l : list (X × X)) : X -> X
    := match l with
       | nil => idmap
       | cons p l' => fun x => transpsL l' (transp dA (fst p) (snd p) x)
       end.

  Fixpoint pairsL (a : X) (r : list X) : list (X × X)
    := match r with
       | nil => nil
       | cons b r' => cons ((a; b) : X × X) (pairsL a r')
       end.

  Definition transps_pairsL (a : X) (r : list X) (x : X)
    : transps dA a r x = transpsL (pairsL a r) x.
  Proof. revert x. induction r as [|b r IH]; intro x; [exact refl | exact (IH _)]. Defined.

  Fixpoint lapp (l l' : list (X × X)) : list (X × X)
    := match l with
       | nil => l'
       | cons p l1 => cons p (lapp l1 l')
       end.

  Definition transpsL_app (l l' : list (X × X)) (x : X)
    : transpsL (lapp l l') x = transpsL l' (transpsL l x).
  Proof. revert x. induction l as [|p l IH]; intro x; [exact refl | exact (IH _)]. Defined.

  Context (n : ℕ) (E : X ≃ FinNat n).

  Definition ecode (x : X) : ℕ := fst (fst E x).

  Definition ecode_lt (x : X) : (ecode x < n)%nat := snd (fst E x).

  Definition ecode_inj (x x' : X) (p : ecode x = ecode x') : x = x'
    := Eqv_inj E (path_sigma_prop (fun _ => IsHProp_isProp (P := (_ < _)%nat))
                    (u := fst E x) (v := fst E x') p).

  (** Peeling off the cycle of [y₀] from a permutation [σ']: [σ' = c σ''],
      where [c] is the cyclic permutation of the orbit of [y₀], and [σ'']
      fixes that orbit and agrees with [σ'] elsewhere. *)
  Section Peel.

    Context (σ' : X ≃ X) (y0 : X).

    Local Notation IN := (inorb dA σ' y0 n ecode ecode_lt ecode_inj).
    Local Notation c := (orbit_cyc dA σ' y0 n ecode ecode_lt ecode_inj).

    Definition peel_fun (x : X) : X
      := match inorb_dec dA σ' y0 n ecode ecode_lt ecode_inj x with
         | inl _ => x
         | inr _ => fst σ' x
         end.

    Definition peel_inv (x : X) : X
      := match inorb_dec dA σ' y0 n ecode ecode_lt ecode_inj x with
         | inl _ => x
         | inr _ => eqinv (snd σ') x
         end.

    Definition peel_fun_in (x : X) (w : IN x) : peel_fun x = x.
    Proof.
      unfold peel_fun. destruct (inorb_dec _ _ _ _ _ _ _ x) as [_|nw]; [exact refl | destruct (nw w)].
    Defined.

    Definition peel_fun_out (x : X) (nw : ¬ IN x) : peel_fun x = fst σ' x.
    Proof.
      unfold peel_fun. destruct (inorb_dec _ _ _ _ _ _ _ x) as [w|_]; [destruct (nw w) | exact refl].
    Defined.

    Definition peel_inv_in (x : X) (w : IN x) : peel_inv x = x.
    Proof.
      unfold peel_inv. destruct (inorb_dec _ _ _ _ _ _ _ x) as [_|nw]; [exact refl | destruct (nw w)].
    Defined.

    Definition peel_inv_out (x : X) (nw : ¬ IN x) : peel_inv x = eqinv (snd σ') x.
    Proof.
      unfold peel_inv. destruct (inorb_dec _ _ _ _ _ _ _ x) as [w|_]; [destruct (nw w) | exact refl].
    Defined.

    Definition out_t (x : X) (nw : ¬ IN x) : ¬ IN (fst σ' x)
      := fun w => nw (trp (fun y => IN y) (eqinv_l (snd σ') x) (inorb_tinv _ _ _ _ _ _ _ _ w)).

    Definition out_tinv (x : X) (nw : ¬ IN x) : ¬ IN (eqinv (snd σ') x)
      := fun w => nw (trp (fun y => IN y) (eqinv_r (snd σ') x) (inorb_t _ _ _ _ _ _ _ _ w)).

    Definition peelEqv : X ≃ X.
    Proof.
      refine (mkEqv peel_fun peel_inv _ _); intro x;
        destruct (inorb_dec dA σ' y0 n ecode ecode_lt ecode_inj x) as [w|nw].
      - exact (ap peel_inv (peel_fun_in x w) @ peel_inv_in x w).
      - exact (ap peel_inv (peel_fun_out x nw) @ peel_inv_out _ (out_t x nw) @ eqinv_l (snd σ') x).
      - exact (ap peel_fun (peel_inv_in x w) @ peel_fun_in x w).
      - exact (ap peel_fun (peel_inv_out x nw) @ peel_fun_out _ (out_tinv x nw)
               @ eqinv_r (snd σ') x).
    Defined.

    Definition peel_factor (x : X) : fst σ' x = c (peel_fun x).
    Proof.
      destruct (inorb_dec dA σ' y0 n ecode ecode_lt ecode_inj x) as [w|nw].
      - exact ((orbit_cyc_in _ _ _ _ _ _ _ x w)^ @ ap c (peel_fun_in x w)^).
      - exact ((orbit_cyc_out _ _ _ _ _ _ _ _ (out_t x nw))^ @ ap c (peel_fun_out x nw)^).
    Defined.

    Definition peel_list : list (X × X)
      := pairsL y0 (seg σ' y0 1 (d0 dA σ' y0 n ecode ecode_lt ecode_inj)).

    Definition c_transpsL (x : X) : c x = transpsL peel_list x
      := cyc_transps dA y0 _ (orbit_distinct _ _ _ _ _ _ _) x @ transps_pairsL _ _ x.

  End Peel.

  (** The invariant after treating the elements with code [< i]. *)
  Definition PeelInv (σ : X ≃ X) (i : ℕ) : Type
    := {l : list (X × X) & {σ' : X ≃ X &
         (forall x, fst σ x = transpsL l (fst σ' x))
         × (forall x, (ecode x < i)%nat -> fst σ' x = x)}}.

  Definition peel_step (σ : X ≃ X) (i : ℕ) (v : PeelInv σ i) : PeelInv σ (S i).
  Proof.
    destruct v as [l [σ' [hs hf]]].
    destruct (dec (i < n)%nat) as [li|nli].
    - pose (y0 := eqinv (snd E) ((i; li) : FinNat n)).
      assert (cy0 : ecode y0 = i) by exact (ap fst (eqinv_r (snd E) ((i; li) : FinNat n))).
      refine (lapp (peel_list σ' y0) l; (peelEqv σ' y0; (_; _))).
      + intro x. refine (hs x @ ap (transpsL l) (peel_factor σ' y0 x @ c_transpsL σ' y0 _) @ _).
        exact (transpsL_app _ _ _)^.
      + intros x lx. change (peel_fun σ' y0 x = x).
        destruct (lt_succ_cases lx) as [l'|q].
        * destruct (inorb_dec dA σ' y0 n ecode ecode_lt ecode_inj x) as [w|nw].
          -- exact (peel_fun_in σ' y0 x w).
          -- exact (peel_fun_out σ' y0 x nw @ hf x l').
        * apply peel_fun_in.
          refine (trp (fun y => inorb dA σ' y0 n ecode ecode_lt ecode_inj y)
                    (ecode_inj y0 x (cy0 @ q^)) _).
          exact (inorb_ox _ _ _ _ _ _ _ 0%nat (leq_succ (leq_zero_l _))).
    - refine (l; (σ'; (hs; _))). intros x lx. apply hf.
      exact (lt_lt_leq_trans (ecode_lt x) (Overture.fst geq_iff_not_lt nli)).
  Defined.

  Definition peel_all (σ : X ≃ X) : forall i, PeelInv σ i.
  Proof.
    intro i. induction i as [|i IH].
    - exact (nil; (σ; ((fun x => refl); (fun x l => match not_lt_zero_r _ l with end)))).
    - exact (peel_step σ i IH).
  Defined.

  Definition perm_transps_fin (σ : X ≃ X)
    : {l : list (X × X) & forall x, fst σ x = transpsL l x}.
  Proof.
    destruct (peel_all σ n) as [l [σ' [hs hf]]].
    exact (l; fun x => hs x @ ap (transpsL l) (hf x (ecode_lt x))).
  Defined.

End Transpositions.

(** Corollary: any permutation of a finite set is a composite of
    transpositions. *)
Definition perm_transpositions `{Univalence} {X : Type} (h : isFinSet X) (σ : X ≃ X)
  : ptrunc {l : list (X × X) & forall x, fst σ x = transpsL (finset_isDecSet h) l x}
  := ptrunc_rec ptrunc_isProp
       (fun w => trunc (perm_transps_fin (finset_isDecSet h) (fst w)
                          (Eqv_comp (idtoeqv (snd w)) (Eqv_of_Equiv (equiv_fin_finnat (fst w))))
                          σ))
       h.

(** The corollary with genuine transpositions, i.e. with [a ≠ b] for each
    pair [(a, b)] in the list. *)
Fixpoint all_pairs_ne {X : Type} (l : list (X × X)) : Type
  := match l with nil => Unit | cons p l' => (fst p ≠ snd p) × all_pairs_ne l' end.

Definition perm_transpositions_ne_stmt `{Univalence} : Type
  := forall (X : Type) (h : isFinSet X) (σ : X ≃ X),
       ptrunc {l : list (X × X) & all_pairs_ne l
                 × (forall x, fst σ x = transpsL (finset_isDecSet h) l x)}.

(** Dropping the pairs [(a, a)], which give the identity. *)
Fixpoint filter_ne {X : Type} (dA : isDecSet X) (l : list (X × X)) : list (X × X)
  := match l with
     | nil => nil
     | cons p l' => match deceq dA (fst p) (snd p) with
                    | inl _ => filter_ne dA l'
                    | inr _ => cons p (filter_ne dA l')
                    end
     end.

Definition filter_ne_all {X : Type} (dA : isDecSet X) (l : list (X × X))
  : all_pairs_ne (filter_ne dA l).
Proof.
  induction l as [|p l IH]; [exact tt|]. cbn.
  destruct (deceq dA (fst p) (snd p)) as [_|n]; [exact IH | exact (n; IH)].
Defined.

Definition transp_same {X : Type} (dA : isDecSet X) (a x : X) : transp dA a a x = x.
Proof.
  unfold transp. destruct (deceq dA x a) as [e|n]; [exact e^ | exact refl].
Defined.

Definition transpsL_filter_ne {X : Type} (dA : isDecSet X) (l : list (X × X)) (x : X)
  : transpsL dA l x = transpsL dA (filter_ne dA l) x.
Proof.
  revert x. induction l as [|[a b] l IH]; intro x; [exact refl|]. cbn.
  destruct (deceq dA a b) as [e|_].
  - destruct e. exact (ap (transpsL dA l) (transp_same dA a x) @ IH x).
  - exact (IH _).
Defined.

Definition perm_transpositions_ne `{Univalence} : perm_transpositions_ne_stmt.
Proof.
  intros X h σ.
  refine (ptrunc_rec ptrunc_isProp _ (perm_transpositions h σ)). intros [l hl].
  exact (trunc (filter_ne _ l; (filter_ne_all _ l;
                                fun x => hl x @ transpsL_filter_ne _ l x))).
Defined.

(** The exercise on binomial coefficients (the exercise after
    [def:support-permutation]): a set [A] of cardinality [n] has
    [n!/(k!(n-k)!)] subsets with [k] elements ([xca_binomial_subsets]),
    and [n!/(k!(n-k)!) ⋅ (k-1)!] [k]-cycle permutations for [2 ≤ k ≤ n]
    ([xca_kcycles]); we avoid division by multiplying out.  The book
    assumes [2 ≤ k ≤ n]; the subsets are counted for all [k ≤ n].

    Subsets: a [k]-element subset of [Fin n] is decidable, so it is given
    by its characteristic map [Fin n → Bool] with [k] values [true]
    ([KSub_eqv]); these are counted by Pascal's rule ([fcard_KS], with the
    library's [nat_choose]). *)
Definition b2n (b : Bool) : ℕ := if b then 1%nat else 0%nat.

Fixpoint cnt (n : ℕ) : (Fin n -> Bool) -> ℕ
  := match n with
     | O => fun _ => 0%nat
     | S n' => fun f => (b2n (f (inr tt)) + cnt n' (fun i => f (inl i)))%nat
     end.

Definition KS (n k : ℕ) : Type := {f : Fin n -> Bool & cnt n f = k}.

Definition fun_sum_unit `{Funext} (Y : Type) (B : Type)
  : (Y + Unit -> B) <~> (Y -> B) × B.
Proof.
  srapply equiv_adjointify.
  - exact (fun f => ((fun y => f (inl y)); f (inr tt)) : (Y -> B) × B).
  - exact (fun p => sum_ind _ (fst p) (fun _ => snd p)).
  - intros [g b]. reflexivity.
  - intro f. apply path_forall. intros [y|[]]; reflexivity.
Defined.

Definition split_bool {G : Type} (c : G -> ℕ) (k : ℕ)
  : {p : G × Bool & (b2n (snd p) + c (fst p))%nat = k}
    <~> {g : G & S (c g) = k} + {g : G & c g = k}.
Proof.
  srapply equiv_adjointify.
  - intros [[g [|]] e]; [exact (inl (g; e)) | exact (inr (g; e))].
  - intros [[g e]|[g e]]; [exact (((g; true) : G × Bool); e) | exact (((g; false) : G × Bool); e)].
  - intros [[g e]|[g e]]; reflexivity.
  - intros [[g [|]] e]; reflexivity.
Defined.

Definition KS_split `{Funext} (n k : ℕ)
  : KS (S n) k <~> {g : Fin n -> Bool & S (cnt n g) = k} + KS n k
  := split_bool (cnt n) k oE equiv_functor_sigma' (fun_sum_unit (Fin n) Bool) (fun f => 1%equiv).

Definition finite_Bool : Finite Bool.
Proof.
  refine (finite_equiv' (Fin 2) _ _).
  srapply equiv_adjointify.
  - intros [[[]|_]|_]; [exact false | exact true].
  - intros [|]; [exact (inr tt) | exact (inl (inr tt))].
  - intros [|]; reflexivity.
  - intros [[[]|[]]|[]]; reflexivity.
Defined.

#[local] Existing Instance finite_Bool.

#[local] Instance KS_finite `{Funext} (n k : ℕ) : Finite (KS n k)
  := finite_sigma _ (H0 := fun f => finite_decidable_hprop _).

Definition succ_zero_empty (n : ℕ)
  : {g : Fin n -> Bool & S (cnt n g) = 0%nat} <~> Empty.
Proof.
  srapply equiv_adjointify.
  - intros [g e]. exact (neq_nat_zero_succ _ e^).
  - intros [].
  - intros [].
  - intros [g e]. destruct (neq_nat_zero_succ _ e^).
Defined.

Definition succ_KS (n k : ℕ)
  : {g : Fin n -> Bool & S (cnt n g) = S k} <~> KS n k
  := equiv_functor_sigma_id (fun g => equiv_iff_hprop (path_nat_succ _ _) (ap S)).

Definition fcard_KS `{Funext} (n : ℕ) : forall k, fcard (KS n k) = nat_choose n k.
Proof.
  induction n as [|n IH]; intros [|k].
  - refine (@fcard_equiv' (KS 0 0) Unit _ _ _ @ (refl : fcard Unit = 1%nat)).
    srapply equiv_adjointify.
    + exact (fun _ => tt).
    + exact (fun _ => ((fun e : Fin 0 => match e with end); refl) : KS 0 0).
    + intros []; reflexivity.
    + intros [f e]. apply path_sigma_hprop. apply path_forall. intros [].
  - refine (@fcard_equiv' (KS 0 (S k)) Empty _ _ _ @ (refl : fcard Empty = 0%nat)).
    srapply equiv_adjointify.
    + intros [f e]. exact (neq_nat_zero_succ _ e). 
    + intros [].
    + intros [].
    + intros [f e]. destruct (neq_nat_zero_succ _ e).
  - refine (fcard_equiv' (KS_split n 0) @ fcard_sum _ _ @ _).
    refine (ap011 nat_add (@fcard_equiv' _ Empty (succ_zero_empty n) _ finite_empty) (IH 0%nat)
            @ _).
    exact refl.
  - refine (fcard_equiv' (KS_split n (S k)) @ fcard_sum _ _ @ _).
    refine (ap011 nat_add (fcard_equiv' (succ_KS n k) @ IH k) (IH (S k)) @ _).
    exact refl.
Defined.

Definition fcard_btrue (b : Bool) `{Finite (b = true)} : fcard (b = true) = b2n b.
Proof.
  destruct b.
  - exact (@fcard_equiv' _ Unit (@equiv_contr_contr (true = true) Unit (contr_inhabited_hprop _ refl) _) _ finite_unit).
  - exact (@fcard_equiv' _ Empty (equiv_to_empty (fun e => false_ne_true e)) _ finite_empty).
Defined.

Definition trues_succ (n : ℕ) (f : Fin (S n) -> Bool)
  : {i : Fin (S n) & f i = true} <~> {i : Fin n & f (inl i) = true} + (f (inr tt) = true).
Proof.
  srapply equiv_adjointify.
  - intros [[i|[]] e]; [exact (inl (i; e)) | exact (inr e)].
  - intros [[i e]|e]; [exact (inl i; e) | exact (inr tt; e)].
  - intros [[i e]|e]; reflexivity.
  - intros [[i|[]] e]; reflexivity.
Defined.

Definition cnt_fcard (n : ℕ) : forall f : Fin n -> Bool, fcard {i : Fin n & f i = true} = cnt n f.
Proof.
  induction n as [|n IH]; intro f.
  - exact (@fcard_equiv' _ Empty (equiv_to_empty (fun w : {i : Fin 0 & f i = true} => match fst w with end)) _ finite_empty).
  - refine (fcard_equiv' (trues_succ n f) @ fcard_sum _ _ @ _).
    refine (nat_add_comm _ _ @ ap011 nat_add (fcard_btrue _) (IH _)).
Defined.

(** [k]-element subsets in the book's sense. *)
Definition KSub (A : Type) (k : ℕ) : Type := {P : Sub A & ptrunc (Fin k = carrier P :> Type)}.

Definition KSub_finite `{Univalence} {A : Type} {k : ℕ} (P : Sub A)
  (h : ptrunc (Fin k = carrier P :> Type)) : Finite (carrier P)
  := ptrunc_rec (@IsHProp_isProp _ (ishprop_finite _))
       (fun p => finite_equiv' (Fin k) (equiv_path _ _ p) _) h.

Definition KSub_dec `{Univalence} {n k : ℕ} (P : Sub (Fin n))
  (h : ptrunc (Fin k = carrier P :> Type)) (i : Fin n) : Decidable (fst (P i))
  := @detachable_finite_subset _ _ (fun i => fst (P i)) (fun i => isProp_IsHProp (snd (P i)))
       (KSub_finite P h) i.

Definition KSub_to@{u +| Set < u +} `{Univalence} (n k : ℕ) (w : KSub (Fin n : Type@{u}) k) : KS n k.
Proof.
  destruct w as [P h].
  pose (d := KSub_dec P h).
  refine (chi d; (cnt_fcard n (chi d))^ @ _).
  refine (@fcard_equiv' _ (carrier P) _ _ (KSub_finite P h) @ _).
  - exact (equiv_functor_sigma_id (fun i => equiv_iff_hprop (A := chi d i = true) (B := fst (P i))
             (IsHProp1 := isProp_IsHProp (snd (P i))) (fst (chi_spec d i)) (snd (chi_spec d i)))).
  - refine (ptrunc_rec (ℕ_isSet _ _) _ h). intro p.
    exact (@fcard_equiv' _ (Fin k) (equiv_path _ _ p)^-1 _ _).
Defined.

Definition trueSub {X : Type} (f : X -> Bool) : Sub X
  := fun x => ((f x = true); IsHProp_isProp).

Definition KSub_from@{u +| Set < u +} `{Univalence} (n k : ℕ) (w : KS n k) : KSub (Fin n : Type@{u}) k.
Proof.
  destruct w as [f e].
  refine (trueSub f; _).
  refine (Trunc_functor (-1) (fun E => _) (merely_equiv_fin {i : Fin n & f i = true})).
  exact (path_universe (trp (fun m => {i : Fin n & f i = true} <~> Fin m) (cnt_fcard n f @ e) E)^-1).
Defined.

Definition bool_ext (b c : Bool) (h : (b = true -> c = true) × (c = true -> b = true)) : b = c.
Proof.
  destruct b, c.
  - exact refl.
  - exact (fst h refl)^.
  - exact (snd h refl).
  - exact refl.
Defined.

Definition KSub_eqv@{u +| Set < u +} `{Univalence} (n k : ℕ) : KSub (Fin n : Type@{u}) k <~> KS n k.
Proof.
  srapply (equiv_adjointify (KSub_to n k : KSub (Fin n : Type@{u}) k -> KS n k) (KSub_from n k : KS n k -> KSub (Fin n : Type@{u}) k)).
  - intros [f e]. apply path_sigma_hprop. apply path_forall. intro i.
    exact (bool_ext _ _ (chi_spec (P := trueSub f) _ i)).
  - intros [P h]. apply (path_sigma_prop (fun _ => ptrunc_isProp)). apply path_forall. intro i.
    apply (path_sigma_prop (fun X => isProp_isProp X)).
    exact (path_universe (equiv_iff_hprop (IsHProp1 := isProp_IsHProp (snd (P i)))
                            (fst (chi_spec _ i)) (snd (chi_spec _ i)))).
Defined.

Definition choose_mul (n k : ℕ) (l : (k <= n)%nat)
  : mul (nat_choose n k) (mul (fact k) (fact (n - k))) = fact n
  := ap (fun z => mul z _) (nat_choose_factorial n k l)
     @ nat_mul_div_cancel_r _ _ (nat_divides_factorial_mul_factorial_add' n k l).

Definition xca_binomial_subsets `{Univalence} (A : Type) (h : isFinSet A) (k : ℕ)
  (l : (k <= cardF h)%nat)
  : {hS : isFinSet {P : Sub A & ptrunc (Fin k = carrier P :> Type)} &
      mul (cardF hS) (mul (fact k) (fact (cardF h - k))) = fact (cardF h)}.
Proof.
  pose (F := isFinSet_Finite h).
  pose (l' := trp (fun z => (k <= z)%nat) (cardF_fcard h) l).
  refine (ptrunc_rec (Sigma_isProp ptrunc_isProp (fun _ => ℕ_isSet _ _)) _
            (merely_equiv_fin A)).
  intro e.
  pose (E := (KSub_eqv (fcard A) k oE equiv_path _ _ (ap (fun X => KSub X k) (path_universe e)))).
  pose (FK := finite_equiv' _ E^-1 _ : Finite (KSub A k)).
  pose (hS := Finite_isFinSet FK).
  refine (hS; _).
  refine (ap (fun z => mul z _) (cardF_fcard _ @ _) @ _).
  - exact (@fcard_equiv' _ _ E _ _ @ fcard_KS (fcard A) k).
  - refine (_ @ choose_mul (fcard A) k l' @ ap fact (cardF_fcard h)^).
    exact (ap (fun z => mul _ (mul _ (fact (z - k)))) (cardF_fcard h)).
Defined.

(** [k]-cycles: the distinct lists of length [k] number [n!/(n-k)!]
    ([fcard_DL]); a [k]-cycle [σ] is [(a₁ ⋯ a_k)] for exactly [k] such
    lists, one for each element [a₁] of its support ([fcard_F]), since
    such a list is the orbit list [a₁, σ(a₁), …, σ^{k-1}(a₁)]
    ([list_seg]).  The [k]-cycles are the image of the lists
    ([sum_F_eqv]). *)
Definition isKCycle {A : Type} (dA : isDecSet A) (k : ℕ) (σ : A ≃ A) : Type
  := ptrunc {a1 : A & {r : list A & (length r = pred k) × distinct (cons a1 r)
                                    × (forall x, fst σ x = cyc dA a1 r x)}}.

Section DistinctLists.

  Context `{Univalence} {A : Type} (dA : isDecSet A) `{Finite A}.

  #[local] Instance notin_hprop (x : A) (l : list A) : IsHProp (notin x l)
    := isProp_IsHProp (notin_isProp x l).

  #[local] Instance notin_dec (x : A) (l : list A) : Decidable (notin x l).
  Proof.
    induction l as [|b r IH].
    - exact (inl tt).
    - destruct (deceq dA x b) as [e|ne].
      + exact (inr (fun h => fst h e)).
      + destruct IH as [h|nh]; [exact (inl (ne; h)) | exact (inr (fun h => nh (snd h)))].
  Defined.

  (** Distinct lists of length [k]. *)
  Definition DL (k : ℕ) : Type := {l : list A & (length l = k) × distinct l}.

  Definition DL_pr_isProp (k : ℕ) (l : list A) : isProp ((length l = k) × distinct l)
    := prod_isProp (ℕ_isSet _ _) (distinct_isProp l).

  Definition DL_succ (k : ℕ) : DL (S k) <~> {w : DL k & {x : A & notin x (fst w)}}.
  Proof.
    srapply equiv_adjointify.
    - intros [[|x l] [e d]].
      + destruct (neq_nat_zero_succ _ e).
      + exact ((l; (path_nat_succ _ _ e; snd d)); (x; fst d)).
    - intros [[l [e d]] [x nx]]. exact (cons x l; (ap S e; (nx; d))).
    - intros [[l [e d]] [x nx]].
      exact (ap (fun z : length l = k =>
                   (((l; (z; d)) : DL k); ((x; nx) : {x : A & notin x l}))
                   : {w : DL k & {x : A & notin x (fst w)}})
                (ℕ_isSet _ _ _ _)).
    - intros [[|x l] [e d]].
      + destruct (neq_nat_zero_succ _ e).
      + exact (ap (fun z => (cons x l; z) : DL (S k)) (DL_pr_isProp (S k) (cons x l) _ _)).
  Defined.

  #[local] Instance DL_finite (k : ℕ) : Finite (DL k).
  Proof.
    induction k as [|k IH].
    - refine (finite_contr _ (Contr0 := Build_Contr _ (nil; (refl; tt)) _)).
      intros [[|x l] [e d]].
      + exact (ap (fun z => (nil; z) : DL 0) (DL_pr_isProp 0 nil _ _)).
      + destruct (neq_nat_zero_succ _ e^).
    - exact (finite_equiv' _ (DL_succ k)^-1 _).
  Defined.

  (** The elements of a distinct list [l] are [length l] many. *)
  Definition inl_cons_eqv (b : A) (r : list A) (nb : notin b r)
    : {x : A & ~ notin x (cons b r)} <~> Unit + {x : A & ~ notin x r}.
  Proof.
    srapply equiv_adjointify.
    - intros [x nn]. destruct (deceq dA x b) as [e|ne].
      + exact (inl tt).
      + exact (inr (x; fun h => nn (ne; h))).
    - intros [_|[x nn]].
      + exact (b; fun h => fst h refl).
      + exact (x; fun h => nn (snd h)).
    - intros [[]|[x nn]].
      + cbn. destruct (deceq dA b b) as [_|nbb]; [exact refl | destruct (nbb refl)].
      + cbn. destruct (deceq dA x b) as [e|ne].
        * destruct e. destruct (nn nb).
        * exact (ap (fun z => inr (x; z)) (path_ishprop _ _)).
    - intros [x nn]. cbn. destruct (deceq dA x b) as [e|ne].
      + destruct e. exact (ap (fun z => (x; z)) (path_ishprop _ _)).
      + exact (ap (fun z => (x; z)) (path_ishprop _ _)).
  Defined.

  Definition fcard_in (l : list A) (d : distinct l)
    : fcard {x : A & ~ notin x l} = length l.
  Proof.
    induction l as [|b r IH].
    - exact (@fcard_equiv' _ Empty (equiv_to_empty (fun w : {x : A & ~ notin x nil} => snd w tt)) _ finite_empty).
    - refine (fcard_equiv' (inl_cons_eqv b r (fst d)) @ fcard_sum _ _ @ _).
      exact (ap S (IH (snd d))).
  Defined.

  Definition fcard_notin (l : list A) (d : distinct l)
    : fcard {x : A & notin x l} = (fcard A - length l)%nat.
  Proof.
    refine (_ @ ap (fun z => (z - length l)%nat)
              ((fcard_equiv' (equiv_decidable_sum (fun x => notin x l)))
               @ fcard_sum _ _)^).
    refine (_ @ ap (fun z => (_ + z - length l)%nat) (fcard_in l d)^).
    exact (nat_add_sub_cancel_r _ _)^.
  Defined.

  Definition sub_succ (n k : ℕ) (l : (k < n)%nat) : (n - k)%nat = S (n - S k)
    := (nat_succ_pred _ (equiv_lt_lt_sub n k l))^ @ ap S (nat_sub_succ_r n k)^.

  Definition fcard_DL (k : ℕ) : (k <= fcard A)%nat ->
    (fcard (DL k) * factorial (fcard A - k) = factorial (fcard A))%nat.
  Proof.
    induction k as [|k IH]; intro lk.
    - exact (nat_mul_one_l _ @ ap factorial (nat_sub_zero_r _)).
    - assert (e : fcard (DL (S k)) = (fcard (DL k) * (fcard A - k))%nat).
      { refine (fcard_equiv' (DL_succ k) @ fcard_sigma _ @ _).
        refine (_ @ finadd_const (DL k) (fcard A - k)%nat).
        unfold finadd. apply fcard_equiv'. apply equiv_functor_sigma_id. intros [l [el dl]].
        exact (equiv_path _ _ (ap Fin (fcard_notin l dl @ ap (fun z => (fcard A - z)%nat) el))). }
      refine (ap (fun z => (z * _)%nat) e @ _).
      refine ((nat_mul_assoc _ _ _)^ @ _ @ IH (leq_succ_l lk)).
      refine (ap (fun z => (fcard (DL k) * z)%nat) _).
      refine (_ @ ap factorial (sub_succ _ _ lk)^).
      refine (ap (fun z => (z * _)%nat) (sub_succ _ _ lk)).
  Defined.

End DistinctLists.

Section KCycleLists.

  Context `{Funext} {A : Type} (dA : isDecSet A).

  Definition next_app (p s : list A) (h x : A) (nx : notin x p)
    : next dA (app p (cons x s)) h x = match s with nil => h | cons c _ => c end.
  Proof.
    induction p as [|q p IH].
    - cbn. destruct (deceq dA x x) as [_|nxx]; [exact refl | destruct (nxx refl)].
    - cbn. destruct (deceq dA x q) as [e|_]; [destruct (fst nx e) | exact (IH (snd nx))].
  Defined.

  Definition notin_app_r (q : A) (p w : list A) (n : notin q (app p w)) : notin q w.
  Proof. induction p as [|b p IH]; [exact n | exact (IH (snd n))]. Defined.

  Definition distinct_app_notin (p : list A) (x : A) (s : list A)
    (d : distinct (app p (cons x s))) : notin x p.
  Proof.
    induction p as [|q p IH].
    - exact tt.
    - exact ((fun e => fst (notin_app_r q p (cons x s) (fst d)) e^); IH (snd d)).
  Defined.

  Context (σ : A ≃ A).

  Definition seg_snoc (x0 : A) : forall m s,
    seg σ x0 s (S m) = app (seg σ x0 s m) (cons (ox σ x0 (m + s)) nil).
  Proof.
    intro m. induction m as [|m IH]; intro s.
    - exact refl.
    - refine (ap (cons (ox σ x0 s)) (IH (S s) @ _)).
      exact (ap (fun z => app (seg σ x0 (S s) m) (cons (ox σ x0 z) nil)) (nat_add_succ_r m s)).
  Defined.

  Definition length_seg (x0 : A) : forall m s, length (seg σ x0 s m) = m.
  Proof.
    intro m. induction m as [|m IH]; intro s; [exact refl | exact (ap S (IH (S s)))].
  Defined.

  Definition seg_mem (y x0 : A) : forall m s, notin y (seg σ x0 s m) ->
    forall j, (s <= j)%nat -> (j < m + s)%nat -> y ≠ ox σ x0 j.
  Proof.
    intro m. induction m as [|m IH]; intros s n j l1 l2.
    - destruct (lt_irrefl _ (lt_leq_lt_trans l1 l2)).
    - destruct (equiv_leq_lt_or_eq l1) as [lt|eq].
      + exact (IH (S s) (snd n) j lt (trp (fun z => (j < z)%nat) (nat_add_succ_r m s)^ l2)).
      + destruct eq. exact (fst n).
  Defined.

  Definition seg_in (y x0 : A) : forall m s, ~ notin y (seg σ x0 s m) ->
    {j : ℕ & ((s <= j)%nat × (j < m + s)%nat) × (y = ox σ x0 j)}.
  Proof.
    intro m. induction m as [|m IH]; intros s nn.
    - destruct (nn tt).
    - destruct (deceq dA y (ox σ x0 s)) as [e|ne].
      + exact (s; ((leq_refl s; leq_succ (leq_add_l s m)); e)).
      + destruct (IH (S s) (fun h => nn (ne; h))) as [j [[l1 l2] e]].
        exact (j; ((leq_succ_l l1; trp (fun z => (j < z)%nat) (nat_add_succ_r m s) l2); e)).
  Defined.

  Definition head_eq {a c : A} {r w : list A} (e : cons a r = cons c w) : a = c
    := ap (fun L => match L with nil => a | cons x _ => x end) e.

  Definition tail_eq {a c : A} {r w : list A} (e : cons a r = cons c w) : r = w
    := ap (fun L => match L with nil => r | cons _ t => t end) e.

  (** A list [(a₁ ⋯ a_k)] whose cyclic permutation is [σ] is the orbit
      list [a₁, σ(a₁), …, σ^{k-1}(a₁)], and [σ^k(a₁) = a₁]. *)
  Section ListOfCyc.

    Context (a1 : A) (r : list A) (d : distinct (cons a1 r))
      (hσ : forall x, fst σ x = cyc dA a1 r x).

    Definition suffix_seg : forall w p j, cons a1 r = app p w -> length p = j ->
      (forall c w', w = cons c w' -> c = ox σ a1 j) -> w = seg σ a1 j (length w).
    Proof.
      intro w. induction w as [|c w IH]; intros p j E lp hd.
      - exact refl.
      - pose (hc := hd c w refl).
        refine (ap011 cons hc (IH (app p (cons c nil)) (S j) _ _ _)).
        + exact (E @ app_assoc p (cons c nil) w).
        + exact (length_app p (cons c nil) @ ap (fun z => (z + 1)%nat) lp @ nat_add_comm j 1).
        + intros c' w' ew. symmetry in ew. destruct ew.
          pose (nx := distinct_app_notin p c (cons c' w') (trp distinct E d)).
          exact ((hσ c @ ap (fun L => next dA L a1 c) E @ next_app p (cons c' w') a1 c nx)^
                 @ ap (fst σ) hc).
    Defined.

    Definition list_seg : cons a1 r = seg σ a1 0 (S (length r))
      := suffix_seg (cons a1 r) nil 0 refl refl (fun c w' e => (head_eq e)^).

    Definition r_seg : r = seg σ a1 1 (length r) := tail_eq list_seg.

    Definition ox_ret : ox σ a1 (S (length r)) = a1.
    Proof.
      pose (m := length r).
      pose (E := list_seg @ seg_snoc a1 m 0).
      pose (nx := distinct_app_notin _ _ nil (trp distinct E d)).
      refine (ap (fun z => fst σ (ox σ a1 z)) (nat_add_zero_r m)^ @ hσ _ @ _).
      exact (ap (fun L => next dA L a1 _) E @ next_app _ nil a1 _ nx).
    Defined.

    Definition a1_ne_ox (i : ℕ) (l1 : (1 <= i)%nat) (l2 : (i <= length r)%nat)
      : a1 ≠ ox σ a1 i
      := seg_mem a1 a1 (length r) 1 (trp (notin a1) r_seg (fst d)) i l1
           (trp (fun z => (i < z)%nat) (nat_add_comm (length r) 1)^ (leq_succ l2)).

  End ListOfCyc.

End KCycleLists.

Section CycleFiber.

  Context `{Funext} {A : Type} (dA : isDecSet A) (σ : A ≃ A)
    (n : ℕ) (code : A -> ℕ) (code_lt : forall x, (code x < n)%nat)
    (code_inj : forall x x', code x = code x' -> x = x').

  Local Notation D x0 := (d0 dA σ x0 n code code_lt code_inj).
  Local Notation inorbA x0 := (inorb dA σ x0 n code code_lt code_inj).

  Definition A_isSet : isSet A := fun x y => fst (dA x y).

  (** The lists [(a ⋯)] with [σ = (a ⋯)], of a given length. *)
  Definition CycFrom (m : ℕ) (a : A) : Type
    := {r : list A & ((length r = m) × distinct (cons a r)) × (forall x, fst σ x = cyc dA a r x)}.

  Definition G_isProp (m : ℕ) (a : A) : isProp (CycFrom m a).
  Proof.
    intros [r [[e dd] h]] [r' [[e' dd'] h']].
    refine (path_sigma_prop (fun r => prod_isProp (prod_isProp (ℕ_isSet _ _) (distinct_isProp _))
                                         (Pi_isProp (fun x => A_isSet _ _))) _).
    exact (r_seg dA σ a r dd h @ ap (seg σ a 1) (e @ e'^) @ (r_seg dA σ a r' dd' h')^).
  Defined.

  Definition period_eq (x0 : A) (m : ℕ) (ret : ox σ x0 (S m) = x0)
    (ne : forall i, (1 <= i)%nat -> (i <= m)%nat -> x0 ≠ ox σ x0 i) : D x0 = m.
  Proof.
    destruct (nat_trichotomy (D x0) m) as [[lt|eq]|gt].
    - destruct (ne (S (D x0)) (leq_succ (leq_zero_l _)) lt
                  (ox_period dA σ x0 n code code_lt code_inj)^).
    - exact eq.
    - destruct (ox_minimal dA σ x0 n code code_lt code_inj m gt ret).
  Defined.

  Definition inorb_iter (x0 : A) : forall p, inorbA x0 (iter (fst σ) p x0).
  Proof.
    intro p. induction p as [|p IH].
    - exact (inorb_ox dA σ x0 n code code_lt code_inj 0 (leq_succ (leq_zero_l _))).
    - exact (inorb_t dA σ x0 n code code_lt code_inj _ IH).
  Defined.

  Context (m : ℕ) (m1 : (1 <= m)%nat) (b : A) (r0 : list A) (lr0 : length r0 = m)
    (d : distinct (cons b r0)) (hσ : forall x, fst σ x = cyc dA b r0 x).

  Definition ret_b : ox σ b (S m) = b
    := ap (fun z => ox σ b (S z)) lr0^ @ ox_ret dA σ b r0 d hσ.

  Definition ne_b (i : ℕ) (l1 : (1 <= i)%nat) (l2 : (i <= m)%nat) : b ≠ ox σ b i
    := a1_ne_ox dA σ b r0 d hσ i l1 (trp (fun z => (i <= z)%nat) lr0^ l2).

  Definition D_b : D b = m := period_eq b m ret_b ne_b.

  Definition list_b : cons b r0 = seg σ b 0 (S m)
    := list_seg dA σ b r0 d hσ @ ap (fun z => seg σ b 0 (S z)) lr0.

  Definition in_list (y : A) (nn : ~ notin y (cons b r0))
    : {j : ℕ & (j < S m)%nat × (y = ox σ b j)}.
  Proof.
    destruct (seg_in dA σ y b (S m) 0 (trp (fun L => ~ notin y L) list_b nn))
      as [j [[_ l2] e]].
    exact (j; (trp (fun z => (j < z)%nat) (nat_add_zero_r _) l2; e)).
  Defined.

  Definition notin_fixed (y : A) (mv : moved σ y) : ~ notin y (cons b r0)
    := fun h => mv (hσ y @ cyc_fixes dA b r0 y h).

  Section Moved.

    Context (a : A) (mv : moved σ a).

    Let J := in_list a (notin_fixed a mv).
    Let j := fst J.
    Let lj : (j < S m)%nat := fst (snd J).
    Let ea : a = ox σ b j := snd (snd J).

    Definition iter_ox (i : ℕ) : iter (fst σ) i a = ox σ b (i + j)
      := ap (iter (fst σ) i) ea @ (ox_add σ b i j)^.

    Definition b_from_a : iter (fst σ) (S m - j) a = b
      := iter_ox _ @ ap (ox σ b) (nat_add_comm _ _ @ nat_add_sub_r_cancel (leq_succ_l lj))
         @ ret_b.

    Definition ret_a : ox σ a (S m) = a
      := iter_ox (S m) @ ap (ox σ b) (nat_add_comm _ _) @ ox_add σ b j (S m)
         @ ap (iter (fst σ) j) ret_b @ ea^.

    Definition iter_comm (p q : ℕ) (x : A)
      : iter (fst σ) p (iter (fst σ) q x) = iter (fst σ) q (iter (fst σ) p x)
      := (nat_iter_add p q (fst σ) x)^ @ ap (fun z => iter (fst σ) z x) (nat_add_comm p q)
         @ nat_iter_add q p (fst σ) x.

    Definition ne_a (i : ℕ) (l1 : (1 <= i)%nat) (l2 : (i <= m)%nat) : a ≠ ox σ a i.
    Proof.
      intro e. apply (ne_b i l1 l2).
      refine (b_from_a^ @ ap (iter (fst σ) (S m - j)) e @ _).
      exact (iter_comm _ _ a @ ap (iter (fst σ) i) b_from_a).
    Defined.

    Definition D_a : D a = m := period_eq a m ret_a ne_a.

    Definition inorb_a (y : A) (mvy : moved σ y) : inorbA a y.
    Proof.
      destruct (in_list y (notin_fixed y mvy)) as [i [_ ey]].
      refine (trp (inorbA a) _ (inorb_iter a (i + (S m - j)))).
      exact (nat_iter_add i _ (fst σ) a @ ap (iter (fst σ) i) b_from_a @ ey^).
    Defined.

    Definition G_of_moved : CycFrom m a.
    Proof.
      refine (seg σ a 1 (D a);
              ((length_seg σ a (D a) 1 @ D_a; orbit_distinct dA σ a n code code_lt code_inj); _)).
      intro y.
      destruct (inorb_dec dA σ a n code code_lt code_inj y) as [w|nw].
      - exact (orbit_cyc_in dA σ a n code code_lt code_inj y w)^.
      - refine (_ @ (orbit_cyc_out dA σ a n code code_lt code_inj y nw)^).
        destruct (deceq dA (fst σ y) y) as [e|ne]; [exact e|].
        destruct (nw (inorb_a y ne)).
    Defined.

  End Moved.

  Definition moved_of_G (a : A) (g : CycFrom m a) : moved σ a.
  Proof.
    destruct g as [[|c r'] [[e dd] h]].
    - destruct (lt_irrefl 0 (trp (fun z => (1 <= z)%nat) e^ m1)).
    - intro fx.
      exact (fst (fst dd) (fx^ @ h a @ next_app dA nil (cons c r') a a tt)).
  Defined.

  Definition moved_of_in (y : A) (nn : ~ notin y (cons b r0)) : moved σ y.
  Proof.
    destruct (in_list y nn) as [j [lj ey]]. destruct ey^. intro fx.
    pose (lt' := fun i (l : (i < S m)%nat) => trp (fun z => (i < S z)%nat) D_b^ l).
    destruct (equiv_leq_lt_or_eq (leq_pred' lj)) as [l|q].
    - exact (lt_irrefl _ (trp (fun z => (z < S j)%nat)
               (ox_idx_inj dA σ b n code code_lt code_inj (lt' _ (leq_succ l))
                  (lt' _ lj) fx)^ (leq_refl _))).
    - pose (e0 := ox_idx_inj dA σ b n code code_lt code_inj (lt' _ (leq_succ (leq_zero_l _)))
                    (lt' _ lj) (ret_b^ @ ap (fun z => ox σ b (S z)) q^ @ fx)).
      exact (lt_irrefl 0 (trp (fun z => (1 <= z)%nat) (e0 @ q)^ m1)).
  Defined.

End CycleFiber.

Section KCount.

  Context `{Univalence} {A : Type} (dA : isDecSet A) (FA : Finite A) (m : ℕ) (m1 : (1 <= m)%nat).

  Local Notation F σ := {a : A & CycFrom dA σ m a}.

  (** [(a₁ a₂ ⋯ a_k)] as an equivalence, via [xca:perm-prod-transpositions]. *)
  Fixpoint transpsE (a1 : A) (r : list A) : A ≃ A
    := match r with
       | nil => idEqv A
       | cons b r' => Eqv_comp (transpEqv dA a1 b) (transpsE a1 r')
       end.

  Definition transpsE_fst (a1 : A) (r : list A) (x : A)
    : fst (transpsE a1 r) x = transps dA a1 r x.
  Proof.
    revert x. induction r as [|b r IH]; intro x; [exact refl | exact (IH _)].
  Defined.

  Definition cycEqv (a1 : A) (r : list A) (d : distinct (cons a1 r)) : A ≃ A
    := (cyc dA a1 r;
        isEquiv_homotopic _ _ (fun x => transpsE_fst a1 r x @ (cyc_transps dA a1 r d x)^)
          (snd (transpsE a1 r))).

  Definition Aut_isSet : isSet (A ≃ A)
    := Sigma_isSet (Pi_isSet (fun _ => A_isSet dA))
         (fun f => prop_is_set (isEquiv_isProp f)).

  Definition DLp_isProp (l : list A) (k : ℕ) : isProp ((length l = k) × distinct l)
    := prod_isProp (ℕ_isSet _ _) (distinct_isProp l).

  Definition Gp_isProp (σ : A ≃ A) (a : A) (r : list A)
    : isProp (((length r = m) × distinct (cons a r)) × (forall x, fst σ x = cyc dA a r x))
    := prod_isProp (prod_isProp (ℕ_isSet _ _) (distinct_isProp _))
         (Pi_isProp (fun x => A_isSet dA _ _)).

  (** The map from distinct lists of length [k] to permutations. *)
  Definition Psi (w : @DL A (S m)) : A ≃ A.
  Proof.
    destruct w as [[|a r] [e d]].
    - destruct (neq_nat_zero_succ _ e).
    - exact (cycEqv a r d).
  Defined.

  Definition F_hfiber (σ : A ≃ A) : F σ <~> hfiber Psi σ.
  Proof.
    srapply equiv_adjointify.
    - intros [a [r [[e d] h]]].
      refine ((cons a r; (ap S e; d)); _).
      exact (path_sigma_prop (fun f => isEquiv_isProp f) (u := cycEqv a r d) (v := σ)
               (path_forall _ _ (fun x => (h x)^))).
    - intros [[[|a r] [e d]] p].
      + destruct (neq_nat_zero_succ _ e).
      + exact (a; (r; ((path_nat_succ _ _ e; d); fun x => (ap10 (ap fst p) x)^))).
    - intros [[[|a r] [e d]] p].
      + destruct (neq_nat_zero_succ _ e).
      + refine (path_sigma_prop (fun w => Aut_isSet _ _) _).
        exact (ap (fun z => (cons a r; z) : @DL A (S m)) (DLp_isProp _ _ _ _)).
    - intros [a [r [[e d] h]]].
      exact (ap (fun z => (a; (r; z)) : F σ) (Gp_isProp σ a r _ _)).
  Defined.

  #[local] Instance Aut_finite : Finite (A ≃ A)
    := finite_equiv' _ (Equiv_of_Eqv (Equiv_Eqv_eqv A A)) (finite_aut A).

  #[local] Instance F_finite (σ : A ≃ A) : Finite (F σ)
    := finite_equiv' _ (F_hfiber σ)^-1 (finite_hfiber Psi σ (H := @DL_finite _ A dA FA m.+1)).

  Definition KCyc : Type := {σ : A ≃ A & isKCycle dA (S m) σ}.

  #[local] Instance KCyc_finite : Finite KCyc
    := finite_detachable_subset _ (H1 := fun σ => decidable_merely_finite (F σ)).

  Definition sum_F_eqv : {c : KCyc & F (fst c)} <~> @DL A (S m).
  Proof.
    refine ((equiv_fibration_replacement Psi)^-1 oE _).
    refine (equiv_functor_sigma_id F_hfiber oE _).
    srapply equiv_adjointify.
    - exact (fun w => (fst (fst w); snd w)).
    - exact (fun w => ((fst w; trunc (snd w)); snd w)).
    - intro w. exact refl.
    - intros [[σ t] f].
      exact (ap (fun z => (((σ; z) : KCyc); f) : {c : KCyc & F (fst c)}) (ptrunc_isProp _ _)).
  Defined.

End KCount.

Definition fcard_F `{Univalence} {A : Type} (dA : isDecSet A) (FA : Finite A) (m : ℕ)
  (m1 : (1 <= m)%nat) (n : ℕ) (code : A -> ℕ) (code_lt : forall x, (code x < n)%nat)
  (code_inj : forall x x', code x = code x' -> x = x') (σ : A ≃ A)
  (c : isKCycle dA (S m) σ)
  : @fcard _ (F_finite dA FA m σ) = S m.
Proof.
  refine (ptrunc_rec (ℕ_isSet _ _) _ c). intros [b [r0 [[lr0 d] hσ]]].
  pose (E1 := equiv_functor_sigma_id (fun a => equiv_iff_hprop
                (IsHProp0 := isProp_IsHProp (G_isProp dA σ m a))
                (moved_of_G dA σ m m1 a)
                (G_of_moved dA σ n code code_lt code_inj m b r0 lr0 d hσ a))).
  pose (E2 := equiv_functor_sigma_id (fun y => equiv_iff_hprop
                (notin_fixed dA σ b r0 hσ y)
                (moved_of_in dA σ n code code_lt code_inj m m1 b r0 lr0 d hσ y))).
  exact (fcard_equiv' (E2 oE E1) @ fcard_in dA (cons b r0) d @ ap S lr0).
Defined.

(** The exercise on binomial coefficients, second part: a set of
    cardinality [n] has [n!/(k!(n-k)!) ⋅ (k-1)!] [k]-cycle permutations for
    [k ≥ 2]. *)
Definition xca_kcycles `{Univalence} (A : Type) (h : isFinSet A) (k : ℕ)
  (k2 : (2 <= k)%nat) (lk : (k <= cardF h)%nat)
  : {hC : isFinSet {σ : A ≃ A & isKCycle (finset_isDecSet h) k σ} &
      mul (cardF hC) (mul (fact k) (fact (cardF h - k)))
      = mul (fact (cardF h)) (fact (pred k))}.
Proof.
  destruct k as [|m]; [destruct (not_lt_zero_r _ k2)|].
  pose (m1 := leq_pred' k2 : (1 <= m)%nat).
  pose (dA := finset_isDecSet h). pose (FA := isFinSet_Finite h).
  refine (Finite_isFinSet (KCyc_finite dA FA m); _).
  refine (ptrunc_rec (ℕ_isSet _ _) _ h). intros [n p].
  pose (C := @fcard _ (KCyc_finite dA FA m)).
  pose (FD := @DL_finite _ A dA FA (S m)).
  assert (hC : (C * S m)%nat = fcard (@DL A (S m))).
  { refine (_ @ (fcard_equiv' (sum_F_eqv dA m))).
    refine ((finadd_const _ _)^ @ _ @ (@fcard_sigma _ _ (KCyc_finite dA FA m) (fun c => F_finite dA FA m (fst c)))^).
    apply (ap (@finadd _ (KCyc_finite dA FA m))). apply path_forall. intros [σ c].
    exact (fcard_F dA FA m m1 n (fin_code p^) (fin_code_lt p^) (fin_code_inj p^) σ c)^. }
  pose (hD := @fcard_DL _ A dA FA (S m) (trp (fun z => (S m <= z)%nat) (cardF_fcard h) lk)).
  refine (ap (fun z => mul z _) (cardF_fcard _ @ fcard_equiv' 1%equiv) @ _).
  refine (_ @ ap (fun z => mul (fact z) _) (cardF_fcard h)^).
  refine (ap (fun z => mul C (mul (fact (S m)) (fact (z - S m)))) (cardF_fcard h) @ _).
  change (C * ((S m * factorial m) * factorial (fcard A - S m)) = factorial (fcard A) * factorial m)%nat.
  refine (_ @ ap (fun z => (z * factorial m)%nat) hD).
  refine (_ @ ap (fun z => (z * factorial (fcard A - S m) * factorial m)%nat) hC).
  rewrite (nat_mul_comm (S m) (factorial m)).
  rewrite <- (nat_mul_assoc (factorial m)).
  rewrite (nat_mul_comm (factorial m)).
  rewrite !nat_mul_assoc. exact refl.
Defined.
