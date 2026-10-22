(** * Section 2.5 Identity types

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Rule (E3) as [path_ind := paths_ind]; [symm := inverse].
    - Own definition [trans], by induction on the second argument as in
      the book, so that [p ∙ refl ≡ p] (the library's [concat] recurses on
      both arguments), with the notation [q ⋅ p :≡ trans p q] in the
      order of function composition.  Coq-HoTT reserves [⋅] without
      associativity, so iterated compositions need parentheses.
    - All six parts of [xca:path-groupoid-laws]; powers [p ^^ n] with
      [p^(n+1) :≡ p · p^n], and negative powers.
    - [trp := transport], and both transport exercises, by path
      induction; the transport-of-structure example for [T(x) :≡ (x = x)],
      with the added fact (not stated in the text) that this transport is
      conjugation.
    - The informal examples about triangles are left out.
    - Bridges: [p⁻¹] is the library's [p^], [trp] is [transport], and
      [q ⋅ p = p @ q]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S04_NaturalNumbers.

Local Open Scope uf_scope.

(** ** 2.5 Identity types

    Rules (E1) - (E3) [rules-for-equality]. *)

(** Rule (E1) [E1]: the identity type [a = b] (HoTT's [paths], which
    lives in the same universe as [X]). *)

(** Rule (E2) [E2]: [refl a : a = a]. *)

(** Rule (E3) [E3]: based path induction, with its computation rule
    holding by definition.  Possible further parameters of [P] can be
    absorbed into [P]. *)

Definition path_ind {X : Type} (a : X) (P : forall b : X, a = b -> Type)
  (p : P a refl) : forall (b : X) (e : a = b), P b e
  := paths_ind a P p.

Definition path_ind_refl {X : Type} (a : X) P p
  : path_ind a P p a refl = p := refl.

(** Example: [refl_2 : fact(2) = 2]. *)
Definition fact_2 : fact 2%nat = 2%nat := refl 2%nat.

(** Definition [def:eq-symm]: path inverse, [symm_{a,a}(refl a) :≡ refl a]. *)
Definition symm {X : Type} {a b : X} (p : a = b) : b = a := inverse p.

Notation "p ⁻¹" := (symm p) : uf_scope.

Definition symm_refl {X : Type} (a : X) : (refl a)⁻¹ = refl a := refl.

(** Definition [def:eq-trans]: path composition, defined by induction on
    the second argument: [trans_{a,b,b}(p)(refl b) :≡ p].  The library's
    [concat] is defined by induction on both arguments, so it does not
    satisfy this equation by definition. *)
Definition trans {X : Type} {a b c : X} (p : a = b) (q : b = c) : a = c
  := match q with refl => p end.

(** Notation in the order of function composition: [q ⋅ p :≡ p ∙ q]. *)
Notation "q ⋅ p" := (trans p q) : uf_scope.

Definition trans_refl_jdeq {X : Type} {a b : X} (p : a = b)
  : refl ⋅ p = p := refl.

(** Comparison with the library. *)
Definition trans_is_concat {X : Type} {a b c : X} (p : a = b) (q : b = c)
  : q ⋅ p = p @ q.
Proof. destruct q, p. exact refl. Defined.

(** Exercise [xca:path-groupoid-laws]. *)
Section PathGroupoidLaws.

  Context {X : Type} {a b c d : X}.

  (** 1. [p ∙ refl_b = p] (holds by definition). *)
  Definition trans_p1 (p : a = b) : refl ⋅ p = p := refl.

  (** 2. [refl_a ∙ p = p]. *)
  Definition trans_1p (p : a = b) : p ⋅ refl = p
    := match p with refl => refl end.

  (** 3. [(p ∙ q) ∙ r = p ∙ (q ∙ r)]. *)
  Definition trans_assoc (p : a = b) (q : b = c) (r : c = d)
    : r ⋅ (q ⋅ p) = (r ⋅ q) ⋅ p
    := match r with refl => refl end.

  (** 4. [p⁻¹ ∙ p = refl_b]. *)
  Definition trans_Vp (p : a = b) : p ⋅ p⁻¹ = refl
    := match p with refl => refl end.

  (** 5. [p ∙ p⁻¹ = refl_a]. *)
  Definition trans_pV (p : a = b) : p⁻¹ ⋅ p = refl
    := match p with refl => refl end.

  (** 6. [(p⁻¹)⁻¹ = p]. *)
  Definition symm_symm (p : a = b) : (p⁻¹)⁻¹ = p
    := match p with refl => refl end.

End PathGroupoidLaws.

(** Powers of a symmetry [p : a = a]: [p^0 :≡ refl_a] and
    [p^(n+1) :≡ p · p^n]; negative powers [p^(-n) :≡ (p⁻¹)^n]. *)
Fixpoint path_pow {X : Type} {a : X} (p : a = a) (n : ℕ) : a = a
  := match n with
     | O => refl
     | S n' => p ⋅ path_pow p n'
     end.

Notation "p ^^ n" := (path_pow p n) (at level 30) : uf_scope.

Definition path_pow_neg {X : Type} {a : X} (p : a = a) (n : ℕ) : a = a
  := (p⁻¹) ^^ n.

(** Definition [def:transport]: [trp^T_{refl a} :≡ id_{T(a)}]. *)
Definition trp {X : Type} (T : X -> Type) {a b : X} (e : a = b)
  : T a -> T b
  := transport T e.

Definition trp_refl {X : Type} (T : X -> Type) (a : X)
  : trp T (refl a) = id (T a) := refl.

(** Exercise [xca:trp-compose]: [trp_{e' ∘ e} = trp_{e'} ∘ trp_e].
    This is an identification of functions; no function extensionality
    is needed, since after induction on [e'] both sides are [trp_e]
    by definition. *)
Definition trp_compose {X : Type} (T : X -> Type) {a b c : X}
  (e : a = b) (e' : b = c)
  : trp T (e' ⋅ e) = trp T e' ∘ trp T e
  := match e' with refl => refl end.

(** Exercise [xca:trp-nondep]: in a constant family [trp^Y_p = id_Y]. *)
Definition trp_const {X Y : Type} {a b : X} (p : a = b)
  : trp (fun _ => Y) p = id Y
  := match p with refl => refl end.

(** Example: transport of structure in [T(x) :≡ (x = x)], which transports
    a symmetry of [a] to a symmetry of [b]. *)
Definition trp_symmetry {X : Type} {a b : X} (e : a = b)
  : (a = a) -> (b = b)
  := trp (fun x => x = x) e.

(** By induction, this is conjugation: [trp_e(s) = e · s · e⁻¹]. *)
Definition trp_symmetry_conj {X : Type} {a b : X} (e : a = b) (s : a = a)
  : trp_symmetry e s = (e ⋅ s) ⋅ e⁻¹
  := match e with refl => (trans_1p s)⁻¹ end.

(** *** Bridges to Coq-HoTT *)

Definition symm_is_inverse {X : Type} {a b : X} (p : a = b)
  : p⁻¹ = p^ := refl.

Definition trp_is_transport {X : Type} (T : X -> Type) {a b : X} (e : a = b)
  : trp T e = transport T e := refl.

Definition trans_is_concat' {X : Type} {a b c : X} (p : a = b) (q : b = c)
  : trans p q = concat p q
  := trans_is_concat p q.
