(** * Section 2.7 Identifying elements in members of families of types

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - The finite types used from here on (from 2.12): [False := Empty],
      [True := Unit] and [Bool], with [triv], [yes], [no] as notations
      for the constructors.
    - Paths over paths [PathOver := DPath] (so that [po_p] holds by
      definition), [po_inv := dp_inverse], [apd := apD] and
      [apap := ap011D].
    - Own composition [⊙] of paths over paths, over the book's [trans].
    - Exercise [xca:cp]: four laws for paths over paths (left unit, right
      unit, inverse, double inverse), stated by transporting along the
      corresponding laws for paths where needed.
    - Bridges: [PathOver] is [DPath], [apd] is [apD], [apap] is
      [ap011D]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S06_ProductTypes.

Local Open Scope uf_scope.

(** The finite types of 2.12, used throughout: [False] (the book's [∅]),
    [True] with its element [triv], and [Bool] with [yes] and [no]. *)
Definition False : Type0 := Empty.
Definition True : Type0 := Unit.
Notation triv := tt.
Notation yes := true.
Notation no := false.

(** ** 2.7 Identifying elements in members of families of types *)

(** Definition [def:pathsoverpaths]: the type [y =^Y_p y'] of paths from
    [y] to [y'] over [p].  The book defines it by induction on [p], with
    [y =^Y_{refl a} y' :≡ (y = y')]; the library's [DPath Y p y y'],
    defined as [transport Y p y = y'], satisfies this by definition. *)
Definition PathOver {X : Type} (Y : X -> Type) {a a' : X} (p : a = a')
  : Y a -> Y a' -> Type
  := DPath Y p.

Definition PathOver_refl {X : Type} (Y : X -> Type) {a : X} (y y' : Y a)
  : PathOver Y refl y y' = (y = y') := refl.

(** Footnote [ft:path-over-pic]: a picture of a path over [p]
    (informal). *)

(** Remark: for a constant family the types of paths over [p] and of
    paths can be identified, by induction on [p].  (This is an
    identification of types, no univalence is needed.) *)
Definition PathOver_const {X Z : Type} {a a' : X} (p : a = a') (z z' : Z)
  : PathOver (fun _ => Z) p z z' = (z = z').
Proof. destruct p. exact refl. Defined.

(** Definition [def:pathover-trp]: [po_p : (y =^Y_p y') = (trp^Y_p(y) = y')],
    which holds by definition since paths over paths are [DPath]s. *)
Definition po {X : Type} {Y : X -> Type} {a a' : X} (p : a = a')
  (y : Y a) (y' : Y a') : PathOver Y p y y' = (trp Y p y = y')
  := refl.

(** Definition [def:pathovercomposition]: composition of paths over paths,
    by induction on [p'] and then on [q']. *)
Definition po_comp {X : Type} {Y : X -> Type} {x x' x'' : X}
  {p : x = x'} {p' : x' = x''} {y : Y x} {y' : Y x'} {y'' : Y x''}
  (q' : PathOver Y p' y' y'') (q : PathOver Y p y y')
  : PathOver Y (p' ⋅ p) y y''.
Proof. destruct p'. cbn in q'. destruct q'. exact q. Defined.

Notation "q' ⊙ q" := (po_comp q' q) (at level 40, left associativity) : uf_scope.

(** The inverse of a path over a path: the library's [dp_inverse]. *)
Definition po_inv {X : Type} {Y : X -> Type} {x x' : X} {p : x = x'}
  {y : Y x} {y' : Y x'} (q : PathOver Y p y y') : PathOver Y p⁻¹ y' y
  := dp_inverse q.

(** Exercise [xca:cp]: some groupoid laws for paths over paths.  Where the
    paths underneath are not equal by definition, we transport along the
    corresponding law from [xca:path-groupoid-laws]. *)
Section PathOverLaws.

  Context {X : Type} {Y : X -> Type} {x x' : X} {p : x = x'}
    {y : Y x} {y' : Y x'} (q : PathOver Y p y y').

  Definition po_comp_1q : (refl : PathOver Y refl y' y') ⊙ q = q
    := refl.

  Definition po_comp_q1
    : trp (fun r => PathOver Y r y y') (trans_1p p)
        (q ⊙ (refl : PathOver Y refl y y)) = q.
  Proof. destruct p. cbn in q. destruct q. exact refl. Defined.

  Definition po_comp_Vq
    : trp (fun r => PathOver Y r y y) (trans_pV p) (po_inv q ⊙ q) = refl.
  Proof. destruct p. cbn in q. destruct q. exact refl. Defined.

  Definition po_inv_inv
    : trp (fun r => PathOver Y r y y') (symm_symm p) (po_inv (po_inv q)) = q.
  Proof. destruct p. cbn in q. destruct q. exact refl. Defined.

End PathOverLaws.

(** Definition [def:apd]: dependent application of [f] to paths,
    [apd_f(refl x) :≡ refl_{f(x)}]: the library's [apD]. *)
Definition apd {X : Type} {Y : X -> Type} (f : forall x, Y x)
  {x x' : X} (p : x = x') : PathOver Y p (f x) (f x')
  := apD f p.

Definition apd_refl {X : Type} {Y : X -> Type} (f : forall x, Y x) (x : X)
  : apd f (refl x) = refl := refl.

(** Definition [def:applfun2]: application of a function of two variables
    to a path and a path over it, [apap_g(refl x)(refl y) :≡ refl]: the
    library's [ap011D]. *)
Definition apap {X Z : Type} {Y : X -> Type} (g : forall x, Y x -> Z)
  {x x' : X} {y : Y x} {y' : Y x'} (p : x = x') (q : PathOver Y p y y')
  : g x y = g x' y'
  := ap011D g p q.

(** Definition [def:applfun2comp]. *)
Definition apap_refl {X Z : Type} {Y : X -> Type} (g : forall x, Y x -> Z)
  {x : X} {y y' : Y x} (q : y = y')
  : apap g refl q = ap (g x) q
  := match q with refl => refl end.

(** *** Bridges to Coq-HoTT *)

Definition PathOver_is_DPath {X : Type} (Y : X -> Type) {a a' : X}
  (p : a = a') (y : Y a) (y' : Y a')
  : PathOver Y p y y' = DPath Y p y y' := refl.

Definition apd_is_apD {X : Type} {Y : X -> Type} (f : forall x, Y x)
  {x x' : X} (p : x = x') : apd f p = apD f p := refl.

Definition apap_is_ap011D {X Z : Type} {Y : X -> Type}
  (g : forall x, Y x -> Z) {x x' : X} {y : Y x} {y' : Y x'}
  (p : x = x') (q : PathOver Y p y y')
  : apap g p q = ap011D g p q := refl.
