(** * Section 2.4 The type of natural numbers

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - [ℕ := nat], [succ := S], rule (P4) as [ind_ℕ := nat_ind], with both
      computation rules holding by definition; recursion and iteration
      ([iter] from [nat_iter]).
    - Addition [add n m := nat_add m n] (the book recurses on the second
      argument, the library on the first), [mul := nat_mul] and
      [fact := factorial], whose defining equations all hold by
      definition, as do [2+2 ≡ 4] and [fact 3 ≡ 6]; the alternative
      definitions via iteration are equal by definition to [add], [mul].
    - Numerals need [%nat], because they otherwise default to the
      library's truncation levels; [+] and [·] are written [add], [mul].
    - Bridges: [add n m = nat_add n m] (by commutativity) and
      [mul = nat_mul]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S03_Universes.

Local Open Scope uf_scope.

(** ** 2.4 The type of natural numbers

    Peano's rules (P1) - (P4). *)

(** Rule (P1) [P1]: [ℕ : U_0]. *)
Definition ℕ : Type0 := nat.
Bind Scope nat_scope with ℕ.

(** Rule (P2) [P2]: [0 : ℕ] is Rocq's [0%nat]. *)

(** Rule (P3) [P3]: [succ : ℕ -> ℕ]. *)
Definition succ : ℕ -> ℕ := S.

(** Rule (P4) [P4]: induction on ℕ, with its two computation rules holding by
    definition. *)
Definition ind_ℕ (X : ℕ -> Type) (a : X 0%nat)
  (g : forall m, X m -> X (succ m)) : forall m, X m
  := nat_ind X a g.

Definition ind_ℕ_0 X a g : ind_ℕ X a g 0%nat = a := refl.
Definition ind_ℕ_succ X a g m
  : ind_ℕ X a g (succ m) = g m (ind_ℕ X a g m) := refl.

(** The recursion principle is the special case of a constant family. *)
Definition rec_ℕ (Y : Type) (a : Y) (g : ℕ -> Y -> Y) : ℕ -> Y
  := ind_ℕ (fun _ => Y) a g.

(** Iteration: [e^0 :≡ id_Y] and [e^(succ m) :≡ e ∘ e^m]. *)
Definition iter {Y : Type} (e : Y -> Y) (m : ℕ) : Y -> Y
  := fun y => nat_iter m e y.

Definition iter_0 {Y : Type} (e : Y -> Y) : iter e 0%nat = id Y := refl.
Definition iter_succ {Y : Type} (e : Y -> Y) m
  : iter e (succ m) = e ∘ iter e m := refl.

(** Addition, by induction on the second argument:
    [n + 0 :≡ n] and [n + succ(m) :≡ succ(n + m)].  This is the library's
    [nat_add] with its arguments swapped. *)
Definition add (n m : ℕ) : ℕ := nat_add m n.

(** Multiplication, by induction on the first argument:
    [0 · n :≡ 0] and [succ(m) · n :≡ (m · n) + n]. *)
Definition mul (m n : ℕ) : ℕ := nat_mul m n.

(** The factorial function:
    [fact(0) :≡ 1] and [fact(succ(m)) :≡ succ(m) · fact(m)]. *)
Definition fact : ℕ -> ℕ := factorial.

Section NaturalNumbers.

  Local Open Scope nat_scope.

  Definition add_0 (n : ℕ) : add n 0 = n := refl.
  Definition add_succ (n m : ℕ) : add n (succ m) = succ (add n m) := refl.

  Definition mul_0 (n : ℕ) : mul 0 n = 0 := refl.
  Definition mul_succ (m n : ℕ) : mul (succ m) n = add (mul m n) n := refl.

  Definition fact_0 : fact 0 = 1 := refl.
  Definition fact_succ (m : ℕ) : fact (succ m) = mul (succ m) (fact m) := refl.

  Definition two_plus_two : add 2 2 = 4 := refl.
  Definition fact_3 : fact 3 = 6 := refl.

  (** Examples from 2.2: [m ↦ (n ↦ m + n)] and [2 + _]. *)
  Check (fun m => (fun n => add m n)) : ℕ -> (ℕ -> ℕ).
  Check (fun n => add 2 n) : ℕ -> ℕ.

  (** Alternative definitions via iteration, [n + m :≡ succ^m(n)] and
      [m · n :≡ (i ↦ i + n)^m(0)], are equal by definition to the ones
      above. *)
  Definition add_iter (n m : ℕ) : add n m = iter succ m n := refl.
  Definition mul_iter (m n : ℕ) : mul m n = iter (fun i => add i n) m 0
    := refl.

End NaturalNumbers.

(** *** Bridges to Coq-HoTT *)

Definition add_is_nat_add_swap (n m : ℕ) : add n m = nat_add m n := refl.

Definition add_is_nat_add (n m : ℕ) : add n m = nat_add n m
  := nat_add_comm m n.

Definition mul_is_nat_mul (m n : ℕ) : mul m n = nat_mul m n := refl.
