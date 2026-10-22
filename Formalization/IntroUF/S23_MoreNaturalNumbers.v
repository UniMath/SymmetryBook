(** * Section 2.23 More on natural numbers

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - The book's order [m ≤ n :≡ ∑_k (k + m = n)] and [<] ([le], [lt]),
      shown equivalent to the library's inductive [<=] and [<] (written
      with [%nat]), whose lemmas are reused; [pred := nat_pred].
    - [≤] and [<] are propositions; exercise [xca:try-your-luck-N]
      (injectivity of [succ], commutativity, associativity and
      distributivity, transitivity, monotonicity, [≤] iff [<] or [=],
      antisymmetry, asymmetry of [<]).
    - [lem:dec-eq+order-N], and [ℕ] is a set by Hedberg's theorem.
    - [def:Nwellordered]: bounded search [μ_P] as in the book, its
      correctness, and [min(P)] for decidable [P] that merely has a
      witness.
    - [lem:PHP], with explicit witnesses; the proof searches first for a
      collision with [f(N+1)] and only otherwise uses the book's [g].
    - [cor:Fin-n-injective], derived from [Fin(m) = Fin(n) → m = n]
      (library [nat_eq_fin_equiv]) instead of from PHP.
    - [lem:euclid-div] as contractibility of the type of quotients and
      remainders, using the library's division instead of bounded search.
    - Exercise [xca:ints-as-quotient] from 2.22, placed here: [A/R ≃ Z]
      ([ints_quot_Z]) for [A :≡ ℕ × ℕ],
      [R((w₁,d₁),(w₂,d₂)) :≡ (w₁ + d₂ = w₂ + d₁)] and
      [Z :≡ {(w,d) | (d = 0) ∨ (w = 0 ∧ d ≠ 0)}], with [f([(w,d)]) = (w,d)]
      for [(w,d,p) : Z] ([intsZ_cls]).  Following a hint by the author,
      [f] is induced by the normal form [nf], sending [(w,d)] to
      [(w - d, 0)] if [w ≥ d] and to [(0, d - w)] otherwise.  Key facts:
      [R(x, nf(x))] ([RZ_nf]), and elements of [Z] related by [R] are
      equal ([NF_unique]).
      NOTE for the book text: the author's hint could be added to the
      exercise. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S22_SetOperations.

Local Open Scope uf_scope.

(** ** 2.23 More on natural numbers *)

Definition ℕ_isSet : isSet ℕ := IsHSet_isSet ishset_nat.

(** The predecessor [pred(0) :≡ 0], [pred(succ(n)) :≡ n] is the library's
    [nat_pred]. *)
Definition pred : ℕ -> ℕ := nat_pred.

Definition pred_0 : pred 0%nat = 0%nat := refl.
Definition pred_succ (n : ℕ) : pred (succ n) = n := refl.

(** Definition [def:orderonN]. *)
Definition le (m n : ℕ) : Type := {k : ℕ & add k m = n}.
Definition lt (m n : ℕ) : Type := {k : ℕ & (add k m = n) × (k ≠ 0%nat)}.

(** Comparison with the library's order. *)
Definition le_leq {m n : ℕ} (h : le m n) : (m <= n)%nat
  := trp (fun t => (m <= t)%nat) (snd h) (leq_add_r m (fst h)).

Definition leq_le {m n : ℕ} (h : (m <= n)%nat) : le m n
  := let w := equiv_leq_add m n h in (fst w; nat_add_comm m (fst w) @ snd w).

Definition lt_ltlib {m n : ℕ} (h : lt m n) : (m < n)%nat.
Proof.
  destruct h as [k [e nz]]. destruct k as [|k].
  - destruct (nz refl).
  - apply (trp (fun t => (m < t)%nat) e).
    exact (trp (fun t => (S m <= t)%nat) (nat_add_succ_r m k)^
             (leq_succ (leq_add_r m k))).
Defined.

Definition ltlib_lt {m n : ℕ} (h : (m < n)%nat) : lt m n.
Proof.
  destruct (equiv_leq_add (S m) n h) as [k e].
  refine (S k; (_; fun z => zero_ne_succ k z⁻¹)).
  exact (nat_add_succ_r m k @ ap S (nat_add_comm m k) @ (nat_add_succ_r k m)^ @ e).
Defined.

(** Both [m ≤ n] and [m < n] are propositions. *)
Definition le_isProp (m n : ℕ) : isProp (le m n).
Proof.
  intros [k e] [k' e'].
  apply (path_sigma_prop (fun _ => ℕ_isSet _ _)).
  exact (isinj_nat_add_l m k k' (e @ e'^)).
Defined.

Definition lt_isProp `{Funext} (m n : ℕ) : isProp (lt m n).
Proof.
  intros [k [e nz]] [k' [e' nz']].
  apply (path_sigma_prop (fun k => prod_isProp (ℕ_isSet _ _) (neg_isProp _))).
  exact (isinj_nat_add_l m k k' (e @ e'^)).
Defined.

(** Exercise [xca:try-your-luck-N]. *)
Section TryYourLuck.

  Definition succ_inj {n m : ℕ}
    : ((succ n = succ m) -> n = m) × (n = m -> succ n = succ m)
    := (path_nat_succ n m; ap succ).

  Definition add_comm (n m : ℕ) : add n m = add m n := nat_add_comm m n.

  Definition add_assoc (n m k : ℕ) : add n (add m k) = add (add n m) k
    := (nat_add_assoc k m n)^.

  Definition mul_comm (n m : ℕ) : mul n m = mul m n := nat_mul_comm n m.

  Definition mul_assoc (n m k : ℕ) : mul n (mul m k) = mul (mul n m) k
    := nat_mul_assoc n m k.

  Definition mul_add_distr (m n k : ℕ)
    : mul m (add n k) = add (mul m n) (mul m k)
    := nat_dist_l m k n.

  Definition le_trans {m n k : ℕ} (h : le m n) (h' : le n k) : le m k
    := leq_le (leq_trans (le_leq h) (le_leq h')).

  Definition lt_trans' {m n k : ℕ} (h : lt m n) (h' : lt n k) : lt m k
    := ltlib_lt (lt_trans (lt_ltlib h) (lt_ltlib h')).

  Definition le_add {m n : ℕ} (p : ℕ) (h : le m n) : le (add m p) (add n p)
    := leq_le (nat_add_l_monotone p (le_leq h)).

  Definition lt_add {m n : ℕ} (p : ℕ) (h : lt m n) : lt (add m p) (add n p)
    := ltlib_lt (nat_add_l_strictly_monotone p (lt_ltlib h)).

  Definition le_mul {m n : ℕ} (p : ℕ) (h : le m n) : le (mul m p) (mul n p)
    := leq_le (nat_mul_r_monotone p (le_leq h)).

  Definition le_refl (n : ℕ) : le n n := (0%nat; nat_add_zero_r n).

  Definition le_iff_lt_or_eq (m n : ℕ)
    : (le m n -> lt m n ⨿ (m = n)) × (lt m n ⨿ (m = n) -> le m n).
  Proof.
    split.
    - intros [k e]. destruct k as [|k].
      + exact (inr ((nat_add_zero_r m)^ @ e)).
      + exact (inl (S k; (e; fun z => zero_ne_succ k z⁻¹))).
    - intros [[k [e _]]|e].
      + exact (k; e).
      + exact (0%nat; nat_add_zero_r m @ e).
  Defined.

  Definition le_antisym (m n : ℕ)
    : (le m n × le n m -> m = n) × (m = n -> le m n × le n m)
    := (fun h => leq_antisym (le_leq (fst h)) (le_leq (snd h));
        fun e => match e with refl => (le_refl m; le_refl m) end).

  Definition lt_asym (m n : ℕ) : ¬ (lt m n × lt n m)
    := fun h => lt_irrefl m (lt_trans (lt_ltlib (fst h)) (lt_ltlib (snd h))).

End TryYourLuck.

(** Lemma [lem:dec-eq+order-N]. *)
Definition eq_dec (n m : ℕ) : isDecidable (n = m) := dec_paths n m.

Definition le_dec (m n : ℕ) : isDecidable (le m n)
  := match dec (m <= n)%nat with
     | inl h => inl (leq_le h)
     | inr nh => inr (fun l => nh (le_leq l))
     end.

Definition lt_dec (m n : ℕ) : isDecidable (lt m n)
  := match dec (m < n)%nat with
     | inl h => inl (ltlib_lt h)
     | inr nh => inr (fun l => nh (lt_ltlib l))
     end.

(** By Hedberg's theorem, [ℕ] is a (decidable) set. *)
Definition ℕ_isDecSet : isDecSet ℕ := hedberg eq_dec.

(** Construction [def:Nwellordered]: the least number principle for
    decidable, non-empty subsets of [ℕ], by bounded search [μ_P]. *)
Section LeastNumber.

  Context (P : ℕ -> PropU) (d : forall n, isDecidable (fst (P n))).

  Definition Pmin (n : ℕ) : Type
    := fst (P n) × (forall m, fst (P m) -> le n m).

  (** Bounded search: [μ_P(0) :≡ 0]; [μ_P(succ(n)) :≡ μ_P(n)] if
      [μ_P(n) < n], and otherwise [n] if [P(n)] and [succ(n)] if not. *)
  Fixpoint mu (n : ℕ) : ℕ
    := match n with
       | O => O
       | S n' => match dec (mu n' < n')%nat with
                 | inl _ => mu n'
                 | inr _ => match d n' with
                            | inl _ => n'
                            | inr _ => S n'
                            end
                 end
       end.

  Definition mu_spec1 (n : ℕ)
    : (mu n <= n)%nat × ((mu n < n)%nat -> fst (P (mu n))).
  Proof.
    induction n as [|n IH].
    - exact (leq_refl 0; fun l => match lt_irrefl 0 l with end).
    - cbn. destruct (dec (mu n < n)%nat) as [l|nl].
      + exact (leq_trans (fst IH) (leq_succ_r (leq_refl n)); fun _ => snd IH l).
      + destruct (d n) as [p|np].
        * exact (leq_succ_r (leq_refl n); fun _ => p).
        * exact (leq_refl (S n); fun l => match lt_irrefl _ l with end).
  Defined.

  Definition mu_spec2 (n m : ℕ) (pm : fst (P m)) : (mu n <= m)%nat.
  Proof.
    induction n as [|n IH].
    - exact (leq_zero_l m).
    - cbn. destruct (dec (mu n < n)%nat) as [l|nl].
      + exact IH.
      + assert (e : mu n = n)
          by exact (leq_antisym (fst (mu_spec1 n)) (Overture.fst leq_iff_not_gt nl)).
        assert (le_nm : (n <= m)%nat) by exact (trp (fun t => (t <= m)%nat) e IH).
        destruct (d n) as [p|np].
        * exact le_nm.
        * assert (ne : n <> m) by (intro q; destruct q; exact (np pm)).
          destruct (Overture.fst neq_iff_lt_or_gt ne) as [lt_nm|gt_nm].
          -- exact lt_nm.
          -- destruct (lt_irrefl _ (lt_leq_lt_trans le_nm gt_nm)).
  Defined.

  Definition mu_Pmin (n : ℕ) (p : fst (P n)) : Pmin (mu (S n))
    := (snd (mu_spec1 (S n)) (leq_succ (mu_spec2 (S n) n p));
        fun m pm => leq_le (mu_spec2 (S n) m pm)).

  Definition Pmin_isProp `{Funext} : isProp {n : ℕ & Pmin n}.
  Proof.
    intros [n [p h]] [n' [p' h']].
    apply (path_sigma_prop (fun n => prod_isProp (snd (P n))
             (Pi_isProp (fun m => fun_isProp (le_isProp n m))))).
    exact (leq_antisym (le_leq (h n' p')) (le_leq (h' n p))).
  Defined.

  (** The function [min(P)] of equation [eqn:min]. *)
  Definition min `{Funext} : ptrunc {n : ℕ & fst (P n)} -> {n : ℕ & Pmin n}
    := ptrunc_rec Pmin_isProp (fun w => (mu (S (fst w)); mu_Pmin (fst w) (snd w))).

End LeastNumber.

(** Remark [rem:computations-can-decide]: decisions are used in
    computations, e.g. [dec (mu n < n)] above. *)

(** Bounded search for a decidable property. *)
Definition lt_succ_cases {k b : ℕ} (l : (k < S b)%nat) : (k < b)%nat ⨿ (k = b).
Proof.
  pose (l' := leq_pred' l : (k <= b)%nat).
  destruct (dec_paths k b) as [e|ne].
  - exact (inr e).
  - destruct (Overture.fst neq_iff_lt_or_gt ne) as [lt_kb|gt_kb].
    + exact (inl lt_kb).
    + destruct (lt_irrefl _ (lt_leq_lt_trans l' gt_kb)).
Defined.

Definition bounded_dec (Q : ℕ -> Type) (dq : forall k, isDecidable (Q k))
  : forall b : ℕ, {k : ℕ & (k < b)%nat × Q k} ⨿ (forall k, (k < b)%nat -> ¬ Q k).
Proof.
  intro b. induction b as [|b IH].
  - right. intros k l. destruct (not_lt_zero_r k l).
  - destruct IH as [[k [l q]]|nq].
    + left. exact (k; (lt_trans l (leq_refl (S b)); q)).
    + destruct (dq b) as [q|nq'].
      * left. exact (b; (leq_refl (S b); q)).
      * right. intros k l.
        destruct (lt_succ_cases l) as [l'|e].
        -- exact (nq k l').
        -- destruct e. exact nq'.
Defined.

(** Lemma [lem:PHP], the pigeonhole principle.  We produce the witnesses
    explicitly.  The proof differs slightly from the book's: we first
    search for an [n < N+1] with [f(n) = f(N+1)], and only otherwise
    apply the induction hypothesis to the book's [g]. *)
Definition PHP_lib (N : ℕ) (f : ℕ -> ℕ)
  (hf : forall n, (n < S N)%nat -> (f n < N)%nat)
  : {m : ℕ & {n : ℕ & (m < n)%nat × ((n < S N)%nat × (f n = f m))}}.
Proof.
  revert f hf. induction N as [|N IH]; intros f hf.
  - destruct (not_lt_zero_r _ (hf 0%nat (leq_refl 1))).
  - destruct (bounded_dec (fun k => f k = f (S N)) (fun k => dec_paths _ _) (S N))
      as [[k [lk ek]]|nc].
    + exact (k; (S N; (lk; (leq_refl (S (S N)); ek⁻¹)))).
    + pose (g := fun k => match dec_paths (f k) N with
                          | inl _ => f (S N)
                          | inr _ => f k
                          end).
      assert (hfSN : (f (S N) < S N)%nat) by exact (hf (S N) (leq_refl _)).
      assert (hg : forall k, (k < S N)%nat -> (g k < N)%nat).
      { intros k lk. unfold g. destruct (dec_paths (f k) N) as [e|ne].
        - destruct (lt_succ_cases hfSN) as [l|e2].
          + exact l.
          + destruct (nc k lk (e @ e2^)).
        - destruct (lt_succ_cases (hf k (lt_trans lk (leq_refl _)))) as [l|e2].
          + exact l.
          + destruct (ne e2). }
      destruct (IH g hg) as [m [n [lmn [ln e]]]].
      refine (m; (n; (lmn; (lt_trans ln (leq_refl _); _)))).
      unfold g in e.
      destruct (dec_paths (f n) N) as [en|nen], (dec_paths (f m) N) as [em|nem].
      * exact (en @ em^).
      * destruct (nc m (lt_trans lmn ln) e^).
      * destruct (nc n ln e).
      * exact e.
Defined.

Definition PHP (N : ℕ) (f : ℕ -> ℕ)
  (hf : forall n, lt n (succ N) -> lt (f n) N)
  : {m : ℕ & {n : ℕ & lt m n × (lt n (succ N) × (f n = f m))}}.
Proof.
  destruct (PHP_lib N f (fun n l => lt_ltlib (hf n (ltlib_lt l))))
    as [m [n [lmn [ln e]]]].
  exact (m; (n; (ltlib_lt lmn; (ltlib_lt ln; e)))).
Defined.

(** Exercise [xca:finite-types], part 3: [Fin(n) ≃ ∑_k (k < n)], via the
    library's [equiv_fin_finnat].
    (From 2.24; placed here since [cor:Fin-n-injective] uses it.) *)
Definition Fin_lt_eqv `{Funext} (n : ℕ) : Fin n ≃ {k : ℕ & lt k n}
  := Eqv_comp (Eqv_of_Equiv (equiv_fin_finnat n))
       (tot (fun k (l : (k < n)%nat) => ltlib_lt l);
        tot_isEquiv _ (fun k => snd (Eqv_of_props (IsHProp_isProp (P := (k < n)%nat))
                                       (lt_isProp k n) ltlib_lt lt_ltlib))).

(** Exercise [xca:finite-types], part 4: [Fin m = Fin n] implies [m = n],
    via the library's [nat_eq_fin_equiv].
    (From 2.24; placed here since [cor:Fin-n-injective] uses it.) *)
Definition Fin_paths_eq {m n : ℕ} (e : Fin m = Fin n :> Type) : m = n
  := nat_eq_fin_equiv m n (Equiv_of_Eqv (idtoeqv e)).

(** Corollary [cor:Fin-n-injective].  We derive it from part 4 of
    [xca:finite-types] rather than from the pigeonhole principle.
    (Placed after [xca:finite-types], which it uses.) *)
Definition Fin_n_injective `{Funext} {m n : ℕ} (l : lt m n)
  : ({k : ℕ & lt k m} = {k : ℕ & lt k n}) -> False.
Proof.
  intro e.
  pose (E := Eqv_comp (Fin_lt_eqv m) (Eqv_comp (idtoeqv e) (Eqv_inv (Fin_lt_eqv n)))).
  pose (q := nat_eq_fin_equiv m n (Equiv_of_Eqv E)).
  destruct q. exact (lt_irrefl _ (lt_ltlib l)).
Defined.

(** Lemma [lem:euclid-div].  We use the library's division with
    remainder ([nat_div], [nat_mod]) instead of the book's bounded
    search. *)
Definition euclid_div `{Funext} (n m : ℕ) (pos : lt 0%nat m)
  : isContr {q : ℕ & {r : ℕ & lt r m × (n = add (mul q m) r)}}.
Proof.
  pose (pos' := lt_ltlib pos).
  pose (e0 := nat_div_mod_spec n m @ ap (fun t => (t + n mod m)%nat) (nat_mul_comm m _)
              @ nat_add_comm _ _ : n = add (mul (n / m) m) (n mod m)).
  refine ((n / m; (n mod m; (ltlib_lt (nat_mod_lt_r n m pos'); e0)))%nat; _).
  - intros [q [r [l e]]].
    pose (e' := ((nat_div_mod_spec n m)^ @ e
                 @ nat_add_comm _ _ @ ap (fun t => (t + r)%nat) (nat_mul_comm q m))
                : (m * (n / m) + n mod m = m * q + r)%nat).
    destruct (nat_div_mod_unique m _ _ _ _ (nat_mod_lt_r n m pos') (lt_ltlib l) e')
      as [eq er].
    destruct eq, er.
    exact (ap (fun w => ((n / m)%nat; ((n mod m)%nat; w)))
              (prod_isProp (lt_isProp _ _) (ℕ_isSet _ _) _ _)).
Defined.

(** Exercise [xca:ints-as-quotient] from 2.22, placed here since it uses
    the results on [ℕ] of 2.23. *)
Section IntsAsQuotient.

  Context `{Univalence}.

  Definition NN : Type := ℕ × ℕ.

  Definition NN_isSet : isSet NN := Sigma_isSet ℕ_isSet (fun _ => ℕ_isSet).

  (** [R((w₁,d₁),(w₂,d₂)) :≡ (w₁ + d₂ = w₂ + d₁)]. *)
  Definition RZ (x y : NN) : PropU
    := ((add (fst x) (snd y) = add (fst y) (snd x)); ℕ_isSet _ _).

  Definition nat_add_swap (a b c : ℕ) : (a + (b + c) = b + (a + c))%nat
    := nat_add_assoc a b c @ ap (fun t => (t + c)%nat) (nat_add_comm a b)
       @ (nat_add_assoc b a c)^.

  Definition RZ_refl (x : NN) : fst (RZ x x) := refl.

  Definition RZ_sym (x y : NN) : fst (RZ x y) -> fst (RZ y x) := fun r => r⁻¹.

  Definition RZ_trans (x y z : NN) : fst (RZ x y) -> fst (RZ y z) -> fst (RZ x z).
  Proof.
    destruct x as [w1 d1], y as [w2 d2], z as [w3 d3].
    change ((d2 + w1 = d1 + w2)%nat -> (d3 + w2 = d2 + w3)%nat
            -> (d3 + w1 = d1 + w3)%nat).
    intros h1 h2. apply (isinj_nat_add_l d2).
    exact (nat_add_swap d2 d3 w1 @ ap (nat_add d3) h1 @ nat_add_swap d3 d1 w2
           @ ap (nat_add d1) h2 @ nat_add_swap d1 d2 w3).
  Defined.

  (** Following a hint by the author: [(w,d)] is sent to [(w - d, 0)] if
      [w ≥ d], and to [(0, d - w)] otherwise. *)
  Definition nf (x : NN) : NN
    := match leq_dichotomy (snd x) (fst x) with
       | inl _ => ((fst x - snd x)%nat; 0%nat)
       | inr _ => (0%nat; (snd x - fst x)%nat)
       end.

  Definition RZ_nf (x : NN) : fst (RZ x (nf x)).
  Proof.
    destruct x as [w d]. unfold nf.
    destruct (leq_dichotomy (snd (w; d)) (fst (w; d))) as [l|l]; unfold RZ; cbn.
    - exact (nat_add_sub_r_cancel l)^.
    - exact (nat_add_sub_l_cancel (leq_succ_l l) @ (nat_add_zero_r d)^).
  Defined.

  (** [Z :≡ {(w,d) | (d = 0) ∨ (w = 0 ∧ d ≠ 0)}]. *)
  Definition isNF (x : NN) : Type := (snd x = 0%nat) ∨ ((fst x = 0%nat) × (snd x ≠ 0%nat)).

  Definition Z : Type := {x : NN & isNF x}.

  Definition Z_isSet : isSet Z := Sigma_isSet NN_isSet (fun _ => prop_is_set ptrunc_isProp).

  Definition nf_isNF (x : NN) : isNF (nf x).
  Proof.
    destruct x as [w d]. unfold nf.
    destruct (leq_dichotomy (snd (w; d)) (fst (w; d))) as [l|l]; apply trunc.
    - exact (inl refl).
    - exact (inr (refl; fun e => lt_irrefl w (leq_trans l (equiv_nat_sub_leq^-1 e)))).
  Defined.

  Definition add_eq_zero (n m : ℕ) : (n + m = 0)%nat -> n = 0%nat.
  Proof. destruct n; intro e; [exact refl | destruct (neq_nat_zero_succ _ e^)]. Defined.

  (** Elements of [Z] related by [R] are equal. *)
  Definition NF_unique (z z' : Z) : fst (RZ (fst z) (fst z')) -> fst z = fst z'.
  Proof.
    destruct z as [[w d] p], z' as [[w' d'] p']. cbn.
    change ((d' + w = d + w')%nat -> ((w; d) : NN) = (w'; d')).
    revert p. refine (ptrunc_rec (fun_isProp (NN_isSet _ _)) _). intro p.
    revert p'. refine (ptrunc_rec (fun_isProp (NN_isSet _ _)) _). intro p'.
    destruct p as [e|[e n]], p' as [e'|[e' n']]; cbn in *.
    - destruct e^, e'^. intro r. exact (ap (fun t => (t; 0%nat) : NN) r).
    - destruct e^, e'^. intro r. destruct (n' (add_eq_zero d' w r)).
    - destruct e^, e'^. intro r. destruct (n (add_eq_zero d w' r^)).
    - destruct e^, e'^. intro r.
      exact (ap (fun t => (0%nat; t) : NN) ((nat_add_zero_r d)^ @ r^ @ nat_add_zero_r d')).
  Defined.

  Definition nfZ (x : NN) : Z := (nf x; nf_isNF x).

  Definition nf_Z (z : Z) : nfZ (fst z) = z
    := path_sigma_prop (fun _ => ptrunc_isProp)
         (NF_unique (nfZ (fst z)) z (RZ_sym _ _ (RZ_nf (fst z)))).

  Definition nfZ_resp (x y : NN) (r : fst (RZ x y)) : nfZ x = nfZ y
    := path_sigma_prop (fun _ => ptrunc_isProp)
         (NF_unique (nfZ x) (nfZ y)
            (RZ_trans _ _ _ (RZ_trans _ _ _ (RZ_sym _ _ (RZ_nf x)) r) (RZ_nf y))).

  (** The equivalence [f : A/R ≃ Z], with [f([(w,d)]) = (w,d)] for
      [(w,d,p) : Z]. *)
  Definition intsZ : quot RZ -> Z := fbar RZ RZ_refl Z_isSet nfZ nfZ_resp.

  Definition intsZ_cls (z : Z) : intsZ (cls RZ (fst z)) = z := nf_Z z.

  Definition ints_quot_Z : quot RZ ≃ Z.
  Proof.
    refine (mkEqv intsZ (fun z => cls RZ (fst z)) _ intsZ_cls).
    refine (im_ind RZ _ (fun q => quot_isSet RZ _ _) _). intro x.
    exact (snd (cls_eq_iff RZ RZ_refl RZ_sym RZ_trans (nf x) x)
             (RZ_sym _ _ (RZ_nf x))).
  Defined.

End IntsAsQuotient.
