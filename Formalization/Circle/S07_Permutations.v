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

    Left out (statements only, no proofs yet)
    - That [(ℤ, zs)] is not a cyclic permutation ([zs_not_cyc_stmt]).
    - The corollary with [a ≠ b] for each pair [(a, b)] in the list
      ([perm_transpositions_ne_stmt]); it holds for the pairs we produce.
    - The exercise on binomial coefficients and the number of [k]-cycles
      ([xca_binomial_subsets_stmt], [xca_kcycles_stmt], with
      [isKCycle]).

    Left out (not formalized)
    - The claim in [rem:cycle-vs-cycle] that turning a transposition
      into a cycle requires decidability (a statement about what cannot
      be proved). *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Spaces.Nat.Core Spaces.Int
  Spaces.Circle Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
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

(** Hence the infinite cycle [(ℤ, zs)] is not a cyclic permutation
    (statement only). *)
Definition zs_not_cyc_stmt : Type
  := forall (dZ : isDecSet ℤ) (a1 : ℤ) (r : list ℤ), ¬ (forall x, zs x = cyc dZ a1 r x).

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
    pair [(a, b)] in the list (statement only). *)
Fixpoint all_pairs_ne {X : Type} (l : list (X × X)) : Type
  := match l with nil => Unit | cons p l' => (fst p ≠ snd p) × all_pairs_ne l' end.

Definition perm_transpositions_ne_stmt `{Univalence} : Type
  := forall (X : Type) (h : isFinSet X) (σ : X ≃ X),
       ptrunc {l : list (X × X) & all_pairs_ne l
                 × (forall x, fst σ x = transpsL (finset_isDecSet h) l x)}.

(** The exercise on binomial coefficients (statements only): a set of
    cardinality [n] has [n!/(k!(n-k)!)] subsets with [k] elements, and
    [n!/(k!(n-k)!) ⋅ (k-1)!] [k]-cycle permutations for [k ≥ 1]; we avoid
    division by multiplying out. *)
Definition xca_binomial_subsets_stmt `{Univalence} : Type
  := forall (A : Type) (h : isFinSet A) (k : ℕ), (k <= cardF h)%nat ->
       {hS : isFinSet {P : Sub A & ptrunc (Fin k = carrier P :> Type)} &
         mul (cardF hS) (mul (fact k) (fact (cardF h - k))) = fact (cardF h)}.

Definition isKCycle {A : Type} (dA : isDecSet A) (k : ℕ) (σ : A ≃ A) : Type
  := ptrunc {a1 : A & {r : list A & (length r = pred k) × distinct (cons a1 r)
                                    × (forall x, fst σ x = cyc dA a1 r x)}}.

Definition xca_kcycles_stmt `{Univalence} : Type
  := forall (A : Type) (h : isFinSet A) (k : ℕ), (1 <= k)%nat -> (k <= cardF h)%nat ->
       {hC : isFinSet {σ : A ≃ A & isKCycle (finset_isDecSet h) k σ} &
         mul (cardF hC) (mul (fact k) (fact (cardF h - k)))
         = mul (fact (cardF h)) (fact (pred k))}.
