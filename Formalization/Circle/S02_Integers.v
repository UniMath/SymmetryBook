(** * Section 3.2 The integers

    Part of Chapter 3 ([circle.tex]); see [Circle.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - [def:zet]: the higher inductive type [ℤ] with [ι₊ : ℕ → ℤ],
      [ι₋ : ℕ⁻ → ℤ] and [zeq : ι₋(-0) = ι₊(0)] is realized as the library's
      [Pushout] of [-0 : ℕ⁻] and [0 : ℕ] over [𝟙], with [ι₊ :≡ pushr],
      [ι₋ :≡ pushl], [zeq :≡ pglue(triv)]; the induction principle
      computes on [ι₊] and [ι₋] by definition, with the computation rule
      [ℤ_ind_zeq] for [zeq].
    - [ℤ] is a set with decidable equality, via an equivalence [ℤ ≃ Int]
      with the library's inductive integers.  Hence families of
      identifications in a set need no [zeq] case ([ℤ_ind_prop]).
    - Negation (an involution, with [ap_-(zeq) :≡ zeq⁻¹]), the successor
      [zs] (with [ap_s(zeq) :≡ refl_1]) and the predecessor, so that [zs]
      is an equivalence; the iteration [f^z] of any equivalence
      [f : X ≃ X] for [z : ℤ]; addition [z + y :≡ zs^y(z)], subtraction,
      the fact that they are mutually inverse, and multiplication
      [zy :≡ (w ↦ z + w)^y(0)].
    - Exercises [xca:addition-on-Z-and-N] and [xca:commutative-add-Z].
      These, and the inverse of [w ↦ z + w], are proved by comparing the
      operations with those of the library's [Int] ([toInt_zadd],
      [toInt_zmul]) and reusing its lemmas.
    - The order [z ≤ y :≡ ∑_n (y = z + ι₊(n))], which extends [≤] on [ℕ]
      and is a proposition ([zle_isProp]), and [z < y :≡ s(z) ≤ y] ([zlt]).
    - Towards exercise [xca:euclid-div-Z]: Euclidean division on [ℤ]
      ([euclid_div_Z]), stated as contractibility of the type of [(q, r)]
      with [0 ≤ r < m] and [n = qm + r], as for [lem:euclid-div].  It is
      proved on the library's
      [Int] ([int_euclid_exists], [int_euclid_unique]): for [n ≥ 0] by
      division on [ℕ]; for [n = -(b+1)] with [b = Qm + R] we take
      [q :≡ -(Q+1)] and [r :≡ m - (R+1)], which avoids a case distinction
      on [R = 0]; uniqueness by showing that [dm + r = r'] with
      [r, r' < m] forces [d = 0].  [int_of_nat_inj] moved here from 3.8.
      For use in 3.8, the variants [euclid_div_Sk] and [euclid_unique_Sk]
      for [m = k+1], with the remainder in [ℕ].
    - Exercise [xca:euclid-div-Z], for [m = k+1]: [φ(k, n) :≡ k + mn] is
      an equivalence [𝟙m × ℤ ≃ ℤ] ([euclid_phi], [euclid_div_Z_eqv]),
      with inverse given by [euclid_div_Sk]; placed after
      [xca:commutative-add-Z], as in the book.
      NOTE for the book: [<] on [ℤ] is only mentioned ("ordering
      relations"), not defined.
    - The alternative form of [ℤ]-induction from [f(0)], [g'] and [h']
      ([ℤ_ind']), with the computation rules by [refl]; the value at [-0]
      is [f(0)] transported along [zeq], so [f(-0) ≡ f(0)] holds only
      over [zeq].
    - Numerals in patterns are written [O], since [0] in patterns refers
      to [trunc_index]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Colimits.Coeq Colimits.Pushout
  Spaces.Nat.Core Spaces.Nat.Division Spaces.Int Spaces.Circle Spaces.Finite.FinNat.
From SymmetryBook Require Export Circle.S01_Circle.

Local Open Scope uf_scope.

(** ** 3.2 The integers

    Footnote [ft:many-integers]: alternative definitions of the integers;
    [ℤ_Int] below relates ours to the library's [Int]. *)

(** Definition [def:zet]: the higher inductive type [ℤ] with constructors
    [ι₊ : ℕ → ℤ], [ι₋ : ℕ⁻ → ℤ] and [zeq : ι₋(-0) = ι₊(0)] is the
    pushout of [-0 : ℕ⁻] and [0 : ℕ] over [𝟙], the library's [Pushout].
    Its induction principle computes on [ι₊] and [ι₋] by definition. *)
Definition ℤ : Type := Pushout (fun _ : True => negN 0%nat) (fun _ : True => 0%nat).

Definition iplus (n : ℕ) : ℤ := pushr n.
Definition iminus (m : NNN) : ℤ := pushl m.
Definition zeq : iminus (negN 0) = iplus 0 := pglue tt.

Definition ℤ_ind (T : ℤ -> Type) (g : forall n, T (iplus n))
  (h : forall m, T (iminus m)) (q : PathOver T zeq (h (negN 0)) (g 0%nat))
  : forall z, T z
  := Pushout_ind T h g (fun t => match t with tt => q end).

Definition ℤ_ind_plus T g h q n : ℤ_ind T g h q (iplus n) = g n := refl.
Definition ℤ_ind_minus T g h q m : ℤ_ind T g h q (iminus m) = h m := refl.
Definition ℤ_ind_zeq T g h q : apd (ℤ_ind T g h q) zeq = q
  := Pushout_ind_beta_pglue T h g _ tt.

Definition ℤ_rec (T : Type) (g : ℕ -> T) (h : NNN -> T) (q : h (negN 0) = g 0%nat)
  : ℤ -> T
  := Pushout_rec T h g (fun _ => q).

Definition ℤ_rec_zeq T g h q : ap (ℤ_rec T g h q) zeq = q
  := Pushout_rec_beta_pglue T h g _ tt.

(** [ℤ] is a set with decidable equality: it is equivalent to the
    library's inductive type [Int]. *)
Definition toInt : ℤ -> Int
  := ℤ_rec Int int_of_nat (fun m => int_neg (int_of_nat (unneg m))) refl.

Definition fromInt (x : Int) : ℤ
  := match x with
     | negS n => iminus (negN (S n))
     | zero => iplus 0
     | posS n => iplus (S n)
     end.

Definition toInt_fromInt (x : Int) : toInt (fromInt x) = x
  := match x with negS _ | zero | posS _ => refl end.

Definition fromInt_toInt (z : ℤ) : fromInt (toInt z) = z.
Proof.
  pose (g := fun n : ℕ => match n as n' return fromInt (toInt (iplus n')) = iplus n' with
                      | O => refl | S _ => refl end).
  pose (h := fun m : NNN => match m as m' return fromInt (toInt (iminus m')) = iminus m' with
                      | negN n =>
                          match n as n' return fromInt (toInt (iminus (negN n')))
                                               = iminus (negN n') with
                          | O => zeq⁻¹ | S _ => refl end
                      end).
  refine (ℤ_ind (fun z => fromInt (toInt z) = z) g h _ z).
  - refine (trp_paths_fg (fun z => fromInt (toInt z)) idmap zeq zeq⁻¹ @ _).
    refine (ap (fun r => (ap idmap zeq ⋅ zeq⁻¹) ⋅ r⁻¹)
              (ap_compose toInt fromInt zeq @ ap (ap fromInt) (ℤ_rec_zeq _ _ _ _)) @ _).
    refine (trans_1p _ @ _).
    exact (ap (fun r => r ⋅ zeq⁻¹) (ap_idmap zeq) @ trans_Vp zeq).
Defined.

Definition ℤ_Int : ℤ ≃ Int := mkEqv toInt fromInt fromInt_toInt toInt_fromInt.

Definition Int_isSet : isSet Int := IsHSet_isSet ishset_int.

Definition ℤ_isSet : isSet ℤ := is_ntype_Eqv 0 (Eqv_inv ℤ_Int) Int_isSet.

Definition toInt_inj {x y : ℤ} (e : toInt x = toInt y) : x = y
  := (fromInt_toInt x)^ @ ap fromInt e @ fromInt_toInt y.

Definition ℤ_isDecSet : isDecSet ℤ
  := hedberg (fun x y => match dec_paths (toInt x) (toInt y) with
                         | inl e => inl (toInt_inj e)
                         | inr n => inr (fun e => n (ap toInt e))
                         end).

(** Since [ℤ] is a set, families of identifications in [ℤ] (or in any
    set) need no loop case. *)
Definition ℤ_ind_prop (T : ℤ -> Type) (hT : forall z, isProp (T z))
  (g : forall n, T (iplus n)) (h : forall m, T (iminus m)) : forall z, T z
  := ℤ_ind T g h (hT _ _ _).

(** Negation, with [ap_-(zeq) :≡ zeq⁻¹]; it is its own inverse. *)
Definition zneg : ℤ -> ℤ
  := ℤ_rec ℤ (fun n => iminus (negN n)) (fun m => iplus (unneg m)) zeq⁻¹.

Definition zneg_zneg (z : ℤ) : zneg (zneg z) = z.
Proof.
  refine (ℤ_ind_prop _ (fun z => ℤ_isSet _ _) _ _ z).
  - intro n. exact refl.
  - intros [n]. exact refl.
Defined.

Definition znegEqv : ℤ ≃ ℤ := mkEqv zneg zneg zneg_zneg zneg_zneg.

(** The successor [zs], with [ap_s(zeq) :≡ refl_1], and the predecessor
    [zp], its inverse. *)
Definition zs : ℤ -> ℤ
  := ℤ_rec ℤ (fun n => iplus (S n))
       (fun m => match m with
                 | negN O => iplus 1
                 | negN (S n) => iminus (negN n)
                 end)
       refl.

Definition zp : ℤ -> ℤ
  := ℤ_rec ℤ (fun n => match n with O => iminus (negN 1) | S n => iplus n end)
       (fun m => iminus (negN (S (unneg m))))
       refl.

Definition zp_zs (z : ℤ) : zp (zs z) = z.
Proof.
  refine (ℤ_ind_prop _ (fun z => ℤ_isSet _ _) _ _ z).
  - intro n. exact refl.
  - intros [[|n]]; [exact zeq⁻¹ | exact refl].
Defined.

Definition zs_zp (z : ℤ) : zs (zp z) = z.
Proof.
  refine (ℤ_ind_prop _ (fun z => ℤ_isSet _ _) _ _ z).
  - intros [|n]; [exact zeq | exact refl].
  - intros [n]. exact refl.
Defined.

Definition zsEqv : ℤ ≃ ℤ := mkEqv zs zp zp_zs zs_zp.

(** The inverse of an equivalence built by [mkEqv] is the given one. *)
Definition eqinv_mkEqv {X Y : Type} (f : X -> Y) (g : Y -> X) gf fg (y : Y)
  : eqinv (snd (mkEqv f g gf fg)) y = g y
  := ap (eqinv (snd (mkEqv f g gf fg))) (fg y)^ @ eqinv_l _ (g y).

(** Iteration [f^z] of an equivalence [f : X ≃ X], for [z : ℤ]:
    [f^{ι₊(n)} :≡ f^n], [f^{ι₋(-n)} :≡ (f⁻¹)^n], and [f^0 ≡ id ≡ f^{-0}]. *)
Definition iterZ {X : Type} (f : X ≃ X) : ℤ -> X -> X
  := ℤ_rec (X -> X) (fun n => iter (fst f) n)
       (fun m => iter (eqinv (snd f)) (unneg m)) refl.

(** Addition [z + y :≡ zs^y(z)], subtraction [z - y :≡ z + (-y)]. *)
Definition zadd (z y : ℤ) : ℤ := iterZ zsEqv y z.
Definition zsub (z y : ℤ) : ℤ := zadd z (zneg y).

(** Comparison of the operations with those of the library's [Int]. *)
Definition toInt_zs (x : ℤ) : toInt (zs x) = int_succ (toInt x).
Proof.
  refine (ℤ_ind_prop _ (fun _ => Int_isSet _ _) _ _ x).
  - intros [|n]; exact refl.
  - intros [[|[|n]]]; exact refl.
Defined.

Definition toInt_zp (x : ℤ) : toInt (zp x) = int_pred (toInt x).
Proof.
  refine (ℤ_ind_prop _ (fun _ => Int_isSet _ _) _ _ x).
  - intros [|[|n]]; exact refl.
  - intros [[|n]]; exact refl.
Defined.

Definition toInt_zneg (x : ℤ) : toInt (zneg x) = int_neg (toInt x).
Proof.
  refine (ℤ_ind_prop _ (fun _ => Int_isSet _ _) _ _ x).
  - intro n. exact refl.
  - intros [[|n]]; exact refl.
Defined.

Definition int_pred_neg (n : ℕ)
  : int_pred (int_neg (int_of_nat n)) = int_neg (int_of_nat (S n))
  := match n with O => refl | S _ => refl end.

Definition toInt_zadd (z y : ℤ) : toInt (zadd z y) = int_add (toInt z) (toInt y).
Proof.
  refine (ℤ_ind_prop _ (fun _ => Int_isSet _ _) _ _ y).
  - intro n. change (toInt (iter zs n z) = int_add (toInt z) (int_of_nat n)).
    induction n as [|n IH].
    + exact (int_add_0_r _)^.
    + exact (toInt_zs _ @ ap int_succ IH @ (int_add_succ_r _ _)^
             @ ap (int_add (toInt z)) (int_nat_succ n)).
  - intros [n].
    change (toInt (iter (eqinv (snd zsEqv)) n z)
            = int_add (toInt z) (int_neg (int_of_nat n))).
    induction n as [|n IH].
    + exact (int_add_0_r _)^.
    + exact (ap toInt (eqinv_mkEqv zs zp zp_zs zs_zp _) @ toInt_zp _
             @ ap int_pred IH @ (int_add_pred_r _ _)^
             @ ap (int_add (toInt z)) (int_pred_neg n)).
Defined.

(** Exercise [xca:addition-on-Z-and-N], for addition. *)
Definition iplus_add (n m : ℕ) : iplus (add n m) = zadd (iplus n) (iplus m)
  := toInt_inj (x := iplus (add n m)) ((int_nat_add m n)^ @ int_add_comm _ _ @ (toInt_zadd (iplus n) (iplus m))^).

(** Addition and subtraction are mutually inverse. *)
Definition zsub_zadd (w z : ℤ) : zsub (zadd w z) z = w.
Proof.
  apply toInt_inj. unfold zsub.
  refine (toInt_zadd _ _ @ ap011 int_add (toInt_zadd _ _) (toInt_zneg _) @ _).
  exact ((int_add_assoc _ _ _)^ @ ap (int_add (toInt w)) (int_add_neg_r _)
         @ int_add_0_r _).
Defined.

Definition zadd_zsub (w z : ℤ) : zadd (zsub w z) z = w.
Proof.
  apply toInt_inj. unfold zsub.
  refine (toInt_zadd _ _ @ ap (fun t => int_add t (toInt z))
            (toInt_zadd _ _ @ ap (int_add (toInt w)) (toInt_zneg _)) @ _).
  exact ((int_add_assoc _ _ _)^ @ ap (int_add (toInt w)) (int_add_neg_l _)
         @ int_add_0_r _).
Defined.

(** Hence [w ↦ z + w] is an equivalence, which we iterate to define
    multiplication [zy :≡ (w ↦ z + w)^y(0)]. *)
Definition zaddEqv (z : ℤ) : ℤ ≃ ℤ.
Proof.
  refine (mkEqv (zadd z) (fun w => fromInt (int_add (int_neg (toInt z)) (toInt w))) _ _).
  - intro w. refine (_ @ fromInt_toInt w). apply ap.
    exact (ap (int_add _) (toInt_zadd z w) @ int_add_assoc _ _ _
           @ ap (fun t => int_add t (toInt w)) (int_add_neg_l _)).
  - intro w. apply toInt_inj.
    exact (toInt_zadd _ _ @ ap (int_add (toInt z)) (toInt_fromInt _)
           @ int_add_assoc _ _ _
           @ ap (fun t => int_add t (toInt w)) (int_add_neg_r _)).
Defined.

Definition zmul (z y : ℤ) : ℤ := iterZ (zaddEqv z) y (iplus 0).

Definition toInt_zmul (z y : ℤ) : toInt (zmul z y) = int_mul (toInt z) (toInt y).
Proof.
  refine (ℤ_ind_prop _ (fun _ => Int_isSet _ _) _ _ y).
  - intro n. change (toInt (iter (zadd z) n (iplus 0)) = int_mul (toInt z) (int_of_nat n)).
    induction n as [|n IH].
    + exact (int_mul_0_r _)^.
    + exact (toInt_zadd _ _ @ ap (int_add (toInt z)) IH @ (int_mul_succ_r _ _)^
             @ ap (int_mul (toInt z)) (int_nat_succ n)).
  - intros [n].
    change (toInt (iter (eqinv (snd (zaddEqv z))) n (iplus 0))
            = int_mul (toInt z) (int_neg (int_of_nat n))).
    induction n as [|n IH].
    + exact (int_mul_0_r _)^.
    + exact (ap toInt (eqinv_mkEqv (zadd z)
                         (fun w => fromInt (int_add (int_neg (toInt z)) (toInt w))) _ _ _)
             @ toInt_fromInt _
             @ ap (int_add (int_neg (toInt z))) IH @ (int_mul_pred_r _ _)^
             @ ap (int_mul (toInt z)) (int_pred_neg n)).
Defined.

(** Exercise [xca:addition-on-Z-and-N], for multiplication. *)
Definition iplus_mul (n m : ℕ) : iplus (mul n m) = zmul (iplus n) (iplus m)
  := toInt_inj (x := iplus (mul n m)) ((int_nat_mul n m)^ @ (toInt_zmul (iplus n) (iplus m))^).

(** The order [z ≤ y :≡ ∑_{n:ℕ} (y = z + ι₊(n))] extends the order on [ℕ]. *)
Definition zle (z y : ℤ) : Type := {n : ℕ & y = zadd z (iplus n)}.

Definition nat_of_int (x : Int) : ℕ
  := match x with posS n => S n | _ => 0%nat end.

Definition iplus_inj {n m : ℕ} (e : iplus n = iplus m) : n = m.
Proof.
  pose (c := fun k : ℕ => match k as k' return nat_of_int (toInt (iplus k')) = k' with
                          | O => refl | S _ => refl end).
  exact ((c n)^ @ ap (fun z => nat_of_int (toInt z)) e @ c m).
Defined.

Definition le_zle (m n : ℕ)
  : (le m n -> zle (iplus m) (iplus n)) × (zle (iplus m) (iplus n) -> le m n).
Proof.
  refine (_; _).
  - intros [k e]. exact (k; ap iplus (e^ @ add_comm k m) @ iplus_add m k).
  - intros [k e]. exact (k; add_comm k m @ iplus_inj (iplus_add m k @ e^)).
Defined.

(** The strict order [z < y :≡ s(z) ≤ y]. *)
Definition zlt (z y : ℤ) : Type := zle (zs z) y.

Definition int_of_nat_inj {a b : ℕ} (e : int_of_nat a = int_of_nat b) : a = b
  := iplus_inj (toInt_inj (x := iplus a) (y := iplus b) e).

Definition int_add_cancel_l {x y z : Int} (e : int_add x y = int_add x z) : y = z
  := (int_add_assoc _ _ _ @ ap (fun t => int_add t y) (int_add_neg_l x))^
     @ ap (int_add (int_neg x)) e
     @ int_add_assoc _ _ _ @ ap (fun t => int_add t z) (int_add_neg_l x).

(** [≤] on [ℤ] is a proposition. *)
Definition zle_isProp (z y : ℤ) : isProp (zle z y).
Proof.
  intros [a e] [b e'].
  assert (p : a = b).
  { apply int_of_nat_inj, (@int_add_cancel_l (toInt z)).
    exact ((toInt_zadd _ _)^ @ ap toInt (e^ @ e') @ toInt_zadd _ _). }
  destruct p. exact (ap (fun w => (a; w)) (ℤ_isSet _ _ _ _)).
Defined.

(** [z ≤ y] in terms of the library's [Int]. *)
Definition zle_Int {z y : ℤ} (h : zle z y)
  : {n : ℕ & toInt y = int_add (toInt z) (int_of_nat n)}
  := (h.1; ap toInt h.2 @ toInt_zadd _ _).

Definition Int_zle {z y : ℤ} (n : ℕ) (e : toInt y = int_add (toInt z) (int_of_nat n))
  : zle z y
  := (n; toInt_inj (e @ (toInt_zadd z (iplus n))^)).

(** [m ≤ (k+1)m + r]. *)
Definition leq_mul_succ_add (m k r : ℕ) : (m <= S k * m + r)%nat.
Proof.
  change (m <= (m + k * m) + r)%nat.
  rewrite <- nat_add_assoc. exact _.
Defined.

(** Towards exercise [xca:euclid-div-Z]: Euclidean division on the
    library's [Int], by a positive [m : ℕ].  The key to uniqueness: if [dm + r = r'] with [r, r' < m], then [d = 0]. *)
Definition int_euclid_unique0 (d : Int) (m r r' : ℕ)
  (hr : (r < m)%nat) (hr' : (r' < m)%nat)
  (e : int_add (int_mul d (int_of_nat m)) (int_of_nat r) = int_of_nat r')
  : d = zero.
Proof.
  destruct d as [k| |k].
  - (* d = -(k+1): then r = (k+1)m + r' ≥ m *)
    change (negS k) with (int_neg (int_of_nat (S k))) in e.
    rewrite int_mul_neg_l, int_nat_mul in e.
    assert (e' : int_of_nat r = int_of_nat (S k * m + r')%nat).
    { refine (_ @ int_nat_add _ _). rewrite <- e, int_add_assoc, int_add_neg_r.
      exact refl. }
    destruct (lt_irrefl m
                (lt_leq_lt_trans (leq_mul_succ_add m k r')
                   (transport (fun t => (t < m)%nat) (int_of_nat_inj e') hr))).
  - exact refl.
  - (* d = k+1: then (k+1)m + r = r' ≥ m *)
    change (posS k) with (int_of_nat (S k)) in e.
    rewrite int_nat_mul, int_nat_add in e.
    destruct (lt_irrefl m
                (lt_leq_lt_trans (leq_mul_succ_add m k r)
                   (transport (fun t => (t < m)%nat) (int_of_nat_inj e)^ hr'))).
Defined.

Definition int_euclid_unique (q q' : Int) (m r r' : ℕ)
  (hr : (r < m)%nat) (hr' : (r' < m)%nat)
  (e : int_add (int_mul q m) r = int_add (int_mul q' m) r')
  : (q = q') × (r = r').
Proof.
  assert (e0 : int_add (int_mul (int_add q (int_neg q')) m) r = r').
  { rewrite int_dist_r, int_mul_neg_l, (int_add_comm (int_mul q m)),
      <- int_add_assoc, e, int_add_assoc, int_add_neg_l.
    exact refl. }
  pose (d0 := int_euclid_unique0 _ m r r' hr hr' e0).
  refine (_; int_of_nat_inj ((ap (fun d => int_add (int_mul d m) r) d0)^ @ e0)).
  exact ((int_add_0_r q)^ @ ap (int_add q) (int_add_neg_l q')^ @ int_add_assoc _ _ _
         @ ap (fun t => int_add t q') d0).
Defined.

Definition int_euclid_exists (x : Int) (m : ℕ) (pos : (0 < m)%nat)
  : {q : Int & {r : ℕ & (r < m)%nat × (x = int_add (int_mul q m) r)}}.
Proof.
  pose (spec := fun a : ℕ =>
          nat_div_mod_spec a m @ ap (fun t => (t + a mod m)%nat) (nat_mul_comm m _)).
  destruct x as [b| |a].
  - (* -(b+1) = -(Q+1)m + (m - (R+1)), where b = Qm + R *)
    pose (Q := (b / m)%nat). pose (R := (b mod m)%nat).
    pose (hR := nat_mod_lt_r b m pos : (S R <= m)%nat).
    pose (r := (m - S R)%nat).
    assert (E : (S Q * m = S b + r)%nat).
    { refine (_ @ ap (fun t => (S t + r)%nat) (spec b)^).
      change (m + Q * m = S (Q * m + R) + r)%nat.
      refine (nat_add_comm _ _ @ _).
      exact (ap (nat_add (Q * m)) (nat_add_sub_r_cancel hR)^ @ nat_add_assoc _ _ _
             @ ap (fun t => (t + r)%nat) (nat_add_succ_r _ _)). }
    refine (negS Q; (r; (_; _))).
    + refine (transport (fun t => (S r <= t)%nat) (nat_add_sub_l_cancel hR) _).
      rewrite nat_add_succ_r. exact (leq_succ (leq_add_r r R)).
    + change (negS Q) with (int_neg (int_of_nat (S Q))).
      rewrite int_mul_neg_l, int_nat_mul, E, <- int_nat_add, int_neg_add,
        <- int_add_assoc, int_add_neg_l, int_add_0_r.
      exact refl.
  - exact (zero; (0%nat; (pos; refl))).
  - refine (int_of_nat (S a / m); ((S a) mod m; (nat_mod_lt_r _ m pos; _)))%nat.
    change (posS a) with (int_of_nat (S a)).
    rewrite int_nat_mul, int_nat_add. exact (ap int_of_nat (spec (S a))).
Defined.

(** Towards exercise [xca:euclid-div-Z]: for [m > 0] the type of [(q, r)] with
    [0 ≤ r < m] and [n = qm + r] is contractible. *)
Definition euclid_div_Z (n m : ℤ) (pos : zlt (iplus 0) m)
  : isContr {q : ℤ & {r : ℤ & zle (iplus 0) r × (zlt r m × (n = zadd (zmul q m) r))}}.
Proof.
  destruct (zle_Int pos) as [k ek].
  pose (em := ek @ int_nat_add 1 k : toInt m = int_of_nat (S k)).
  pose (pos' := _ : (0 < S k)%nat).
  pose (toInt_qmr := fun q r => toInt_zadd (zmul q m) r
                       @ ap (fun t => int_add t (toInt r))
                           (toInt_zmul q m @ ap (int_mul (toInt q)) em)).
  destruct (int_euclid_exists (toInt n) (S k) pos') as [q0 [r0 [hr e]]].
  pose (h1 := Int_zle (z := zs (iplus r0)) (y := m) (S k - S r0)%nat
                (em @ ap int_of_nat (nat_add_sub_r_cancel hr)^ @ (int_nat_add _ _)^)).
  pose (e0 := toInt_inj (e @ ap (fun t => int_add (int_mul t _) r0) (toInt_fromInt q0)^
                         @ (toInt_qmr (fromInt q0) (iplus r0))^)
              : n = zadd (zmul (fromInt q0) m) (iplus r0)).
  refine ((fromInt q0; (iplus r0; (Int_zle (z := iplus 0) (y := iplus r0) r0 refl;
                                   (h1; e0)))); _).
  intros [q [r [h0 [h1' e']]]].
    destruct (zle_Int h0) as [r1 er]. change (toInt r = int_of_nat r1) in er.
    destruct (zle_Int h1') as [j ej].
    assert (hr1 : (r1 < S k)%nat).
    { pose (ej' := em^ @ ej @ ap (fun t => int_add t j) (toInt_zs r @ ap int_succ er
                                                    @ int_nat_succ r1)
                   @ int_nat_add _ _).
      exact (transport (fun t => (S r1 <= t)%nat) (int_of_nat_inj ej')^ (leq_add_r _ _)). }
    destruct (int_euclid_unique q0 (toInt q) (S k) r0 r1 hr hr1
                (e^ @ ap toInt e' @ toInt_qmr _ _ @ ap (int_add _) er)) as [eq er'].
    assert (pq : fromInt q0 = q) by exact (ap fromInt eq @ fromInt_toInt q).
    assert (pr : iplus r0 = r) by exact (toInt_inj (x := iplus r0) (ap int_of_nat er' @ er^)).
    destruct pq, pr.
    apply (ap (fun w => (fromInt q0; (iplus r0; w)))).
    exact (prod_isProp (zle_isProp _ _) (prod_isProp (zle_isProp _ _) (ℤ_isSet _ _)) _ _).
Defined.

(** Variants of [euclid_div_Z] for [m = k+1], with the remainder in
    [ℕ], for use in 3.8. *)
Definition euclid_div_Sk (n : ℤ) (k : ℕ)
  : {q : ℤ & {r : ℕ & (r < S k)%nat × (n = zadd (zmul q (iplus (S k))) (iplus r))}}.
Proof.
  destruct (int_euclid_exists (toInt n) (S k) _) as [q0 [r0 [hr e]]].
  refine (fromInt q0; (r0; (hr; toInt_inj _))).
  exact (e @ ap (fun t => int_add (int_mul t _) r0) (toInt_fromInt q0)^
         @ ap (fun t => int_add t _) (toInt_zmul _ (iplus (S k)))^
         @ (toInt_zadd _ (iplus r0))^).
Defined.

Definition euclid_unique_Sk {k : ℕ} (q q' : ℤ) (r r' : ℕ)
  (hr : (r < S k)%nat) (hr' : (r' < S k)%nat)
  (e : zadd (zmul q (iplus (S k))) (iplus r) = zadd (zmul q' (iplus (S k))) (iplus r'))
  : (q = q') × (r = r').
Proof.
  pose (E := fun q r => toInt_zadd (zmul q (iplus (S k))) (iplus r)
                        @ ap (fun t => int_add t _) (toInt_zmul _ (iplus (S k)))).
  destruct (int_euclid_unique (toInt q) (toInt q') (S k) r r' hr hr'
              ((E q r)^ @ ap toInt e @ E q' r')) as [eq er].
  exact (toInt_inj eq; er).
Defined.

(** The alternative form of [ℤ]-induction: given [f(0)], [g'] and [h'],
    with [f(z+1) ≡ g'(z, f(z))] for [z ≥ 0] and [f(z-1) ≡ h'(z, f(z))] for
    [z ≤ 0]; the value at [-0] is [f(0)] transported along [zeq]. *)
Definition ℤ_ind' (T : ℤ -> Type) (f0 : T (iplus 0))
  (g' : forall n, T (iplus n) -> T (iplus (S n)))
  (h' : forall n, T (iminus (negN n)) -> T (iminus (negN (S n))))
  : forall z, T z
  := ℤ_ind T (fun n => nat_rect (fun n => T (iplus n)) f0 g' n)
       (fun m => match m with
                 | negN n => nat_rect (fun n => T (iminus (negN n))) (trp T zeq⁻¹ f0) h' n
                 end)
       (transport_pV T zeq f0).

Definition ℤ_ind'_0 T f0 g' h' : ℤ_ind' T f0 g' h' (iplus 0) = f0 := refl.

Definition ℤ_ind'_plus T f0 g' h' (n : ℕ)
  : ℤ_ind' T f0 g' h' (iplus (S n)) = g' n (ℤ_ind' T f0 g' h' (iplus n)) := refl.

Definition ℤ_ind'_minus T f0 g' h' (n : ℕ)
  : ℤ_ind' T f0 g' h' (iminus (negN (S n))) = h' n (ℤ_ind' T f0 g' h' (iminus (negN n))) := refl.

(** Exercise [xca:commutative-add-Z]. *)
Definition zadd_comm (x y : ℤ) : zadd x y = zadd y x
  := toInt_inj (toInt_zadd x y @ int_add_comm _ _ @ (toInt_zadd y x)^).

Definition zmul_comm (x y : ℤ) : zmul x y = zmul y x
  := toInt_inj (toInt_zmul x y @ int_mul_comm _ _ @ (toInt_zmul y x)^).

(** Exercise [xca:euclid-div-Z], for [m = k+1]: [φ(k, n) :≡ k + mn] is an
    equivalence [𝟙m × ℤ ≃ ℤ], with [𝟙m] represented as [∑_{i:ℕ} (i < m)];
    the inverse is Euclidean division ([euclid_div_Sk], [euclid_unique_Sk]). *)
Definition euclid_phi (k : ℕ) (u : FinNat (S k) × ℤ) : ℤ
  := zadd (iplus (fst (fst u))) (zmul (iplus (S k)) (snd u)).

Definition euclid_phi_qmr (k : ℕ) (u : FinNat (S k) × ℤ)
  : euclid_phi k u = zadd (zmul (snd u) (iplus (S k))) (iplus (fst (fst u)))
  := zadd_comm _ _ @ ap (fun t => zadd t _) (zmul_comm _ _).

Definition euclid_psi (k : ℕ) (n : ℤ) : FinNat (S k) × ℤ
  := let w := euclid_div_Sk n k in ((fst (snd w); fst (snd (snd w))); fst w).

Definition euclid_div_Z_eqv (k : ℕ) : FinNat (S k) × ℤ ≃ ℤ.
Proof.
  refine (mkEqv (euclid_phi k) (euclid_psi k) _ _); unfold euclid_psi; cbv zeta.
  - intro u. destruct (euclid_div_Sk (euclid_phi k u) k) as [q [r [hr e]]].
    destruct u as [[r0 l0] q0]. cbn.
    destruct (euclid_unique_Sk q q0 r r0 hr l0 (e^ @ euclid_phi_qmr k ((r0; l0); q0)))
      as [eq er].
    destruct eq, er.
    exact (ap (fun l => ((r; l); q)) (IsHProp_isProp _ _)).
  - intro n. destruct (euclid_div_Sk n k) as [q [r [hr e]]].
    exact (euclid_phi_qmr k ((r; hr); q) @ e^).
Defined.
