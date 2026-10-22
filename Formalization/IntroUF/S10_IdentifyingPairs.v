(** * Section 2.10 Identifying pairs

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - The pair-path map [pair⁼(p,q) :≡ apap pair p q] ([pathpair]) and its
      inverse [Ψ] ([pathsplit]); [lem:isEq-pair=] and
      [cor:isEq-pair=].
    - [snd(pair⁼(p,q)) = q]: taken literally, the two sides have
      different types.  It is stated together with the [fst] part as
      [Ψ(pair⁼(p,q)) = (p,q)]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S09_Equivalences.

Local Open Scope uf_scope.

(** ** 2.10 Identifying pairs *)

Section IdentifyingPairs.

  Context {X : Type} {Y : X -> Type}.

  (** Definition [def:pairtopath]. *)
  Definition pair : forall x : X, Y x -> Tot Y := exist Y.

  Definition pathpair {x x' : X} {y : Y x} {y' : Y x'}
    (p : x = x') (q : PathOver Y p y y') : (x; y) = (x'; y')
    := apap pair p q.

  (** Construction [cor:isEq-pair=]. *)
  Definition pathpair_refl {x : X} {y y' : Y x} (q : y = y')
    : pathpair refl q = ap (pair x) q
    := apap_refl pair q.

  (** The inverse map [Ψ], for arbitrary elements of the sum type. *)
  Definition pathsplit {w w' : Tot Y} (r : w = w')
    : {p : fst w = fst w' & PathOver Y p (snd w) (snd w')}
    := match r with refl => (refl; refl) end.

  Definition pathsplit_pathpair {x x' : X} {y : Y x} {y' : Y x'}
    (p : x = x') (q : PathOver Y p y y')
    : pathsplit (pathpair p q) = (p; q).
  Proof. destruct p. cbn in q. destruct q. exact refl. Defined.

  Definition pathpair_pathsplit {w w' : Tot Y} (r : w = w')
    : pathpair (fst (pathsplit r)) (snd (pathsplit r)) = r.
  Proof. destruct r. exact refl. Defined.

  (** Lemma [lem:isEq-pair=]. *)
  Definition pathpair_isEquiv {x x' : X} {y : Y x} {y' : Y x'}
    : isEquiv (fun pq : {p : x = x' & PathOver Y p y y'} =>
              pathpair (fst pq) (snd pq))
    := iso_to_isEquiv _ pathsplit
         (fun pq => pathsplit_pathpair (fst pq) (snd pq))
         pathpair_pathsplit.

  Definition path_sigma_eqv {x x' : X} {y : Y x} {y' : Y x'}
    : {p : x = x' & PathOver Y p y y'} ≃ ((x; y) = (x'; y'))
    := (_; pathpair_isEquiv).

  (** [fst(pair^=(p,q)) = p], [snd(pair^=(p,q)) = q] (combined in
      [pathsplit_pathpair] above), and [r = pair^=(fst(r), snd(r))]
      (this is [pathpair_pathsplit]). *)
  Definition ap_fst_pathpair {x x' : X} {y : Y x} {y' : Y x'}
    (p : x = x') (q : PathOver Y p y y')
    : ap fst (pathpair p q) = p.
  Proof. destruct p. cbn in q. destruct q. exact refl. Defined.

  Definition fst_pathsplit {w w' : Tot Y} (r : w = w')
    : fst (pathsplit r) = ap fst r
    := match r with refl => refl end.

End IdentifyingPairs.
