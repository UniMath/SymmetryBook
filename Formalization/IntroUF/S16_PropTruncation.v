(** * Section 2.16 Propositional truncation and logic

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - The propositional truncation [‖T‖ :≡ ptrunc T :≡ Trunc (-1) T] with
      [trunc :≡ tr]; its induction principle is the library's
      [Trunc_ind], so [f(|t|) ≡ g(t)] holds by definition.  The notation
      [‖T‖] is used only in comments (a notation whose opening and closing
      delimiters coincide cannot be parsed reliably).
    - [‖T‖] is a proposition; induction and recursion principles; the
      universal property [(‖T‖ → P) ≃ (T → P)] for propositions [P].
    - Own definitions: [nonempty], [PropU] (the book's [Prop], a reserved
      word in Rocq), disjunction [∨], [Ex] (the book's [∃]; [exists] is a
      keyword) and [ExUnique].
    - Exercises: [∃_{t:T} (x = |t|)] for [x : ‖T‖]; [P ≃ ‖P‖] for
      propositions [P].
    - Connected components and connectedness; [∅] is not connected.
    - Exercise [xca:component-connected]: components are connected, and
      elements in the same component have the same propositional
      properties ([P x = P y] in [Prop], via univalence).
    - Exercises [xca:connected-trivia], [xca:connected-trivia-1] and
      [xca:connected-trivia-2].
    - A preliminary shows that contractibility, being a proposition and
      being an [n]-type are invariant under equivalence. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S15_PropsSetsGroupoids.

Local Open Scope uf_scope.

(** ** Preliminaries

    Contractibility, propositions and [n]-types are invariant under
    equivalence. *)

Definition isContr_Eqv {X Y : Type} (e : X ≃ Y) (c : isContr X) : isContr Y
  := (fst e (fst c);
      fun y => eqinv_r (snd e) y ⋅ ap (fst e) (snd c (eqinv (snd e) y))).

Definition isProp_Eqv {X Y : Type} (e : X ≃ Y) (h : isProp X) : isProp Y
  := fun y y' => eqinv_r (snd e) y' ⋅ ap (fst e) (h _ _) ⋅ (eqinv_r (snd e) y)⁻¹.

Definition is_ntype_Eqv (n : ℕ) {X Y : Type} (e : X ≃ Y) (h : is_ntype n X)
  : is_ntype n Y
  := IsTrunc_ntype n
       (@istrunc_equiv_istrunc X Y (Equiv_of_Eqv e) _ (ntype_IsTrunc n h)).

(** A contractible type is a proposition, and an inhabited proposition is
    contractible. *)
Definition isContr_isProp' {X : Type} (c : isContr X) : isProp X
  := isContr_center c.

Definition isProp_inhabited_isContr {X : Type} (h : isProp X) (x : X)
  : isContr X
  := (x; h x).

(** Identity types: the equivalences [(s = w) ≃ (t = w)] and
    [(w = s) ≃ (w = t)] for [e : s = t], and symmetry. *)
Definition eq_l_eqv {X : Type} {s t w : X} (e : s = t) : (s = w) ≃ (t = w).
Proof. destruct e. exact (idEqv _). Defined.

Definition eq_r_eqv {X : Type} {s t w : X} (e : s = t) : (w = s) ≃ (w = t).
Proof. destruct e. exact (idEqv _). Defined.

Definition symm_eqv {X : Type} {x y : X} : (x = y) ≃ (y = x)
  := mkEqv symm symm symm_symm symm_symm.

(** ** 2.16 Propositional truncation and logic *)

(** Definition [def:prop-trunc]: the propositional truncation [‖T‖] is the
    library's [Trunc (-1) T], with element constructor [trunc :≡ tr], written
    [|t|] in the book.  Its induction principle satisfies
    [f(|t|) ≡ g(t)] by definition. *)
Definition ptrunc (T : Type) : Type := Trunc (-1) T.

Definition trunc {T : Type} : T -> (ptrunc T) := tr.

(** The identification constructor: [‖T‖] is a proposition. *)
Definition ptrunc_isProp {T : Type} : isProp (ptrunc T)
  := @IsHProp_isProp _ (istrunc_truncation (-1) T).

(** The induction principle, for families of propositions. *)
Definition ptrunc_ind {T : Type} (P : (ptrunc T) -> Type)
  (hP : forall x, isProp (P x)) (g : forall t, P (trunc t))
  : forall x, P x
  := Trunc_ind P (Pt := fun x => isProp_IsHProp (hP x)) g.

Definition ptrunc_ind_trunc {T : Type} (P : (ptrunc T) -> Type) hP g (t : T)
  : ptrunc_ind P hP g (trunc t) = g t := refl.

(** The recursion principle, for a constant family. *)
Definition ptrunc_rec {T P : Type} (hP : isProp P) (g : T -> P) : (ptrunc T) -> P
  := ptrunc_ind (fun _ => P) (fun _ => hP) g.

(** The universal property of propositional truncation:
    [(‖T‖ → P) ≃ (T → P)] by precomposition with [|_|]. *)
Definition ptrunc_univ_prop `{Funext} (T : Type) {P : Type} (hP : isProp P)
  : ((ptrunc T) -> P) ≃ (T -> P)
  := mkEqv (fun h => h ∘ trunc) (ptrunc_rec hP)
       (fun h => ptw_inv (ptrunc_ind (fun x => ptrunc_rec hP (h ∘ trunc) x = h x)
                            (fun x => prop_is_set hP _ _) (fun t => refl)))
       (fun g => refl).

(** Definition [def:non-empty]. *)
Definition nonempty (T : Type) : Type := (ptrunc T).

(** The type [Prop_U :≡ ∑_{X:U} isProp(X)].  ([Prop] is a reserved word
    in Rocq, hence the name [PropU].) *)
Definition PropU : Type := {X : Type & isProp X}.

Definition ptrunc_PropU (T : Type) : PropU := ((ptrunc T); ptrunc_isProp).

(** Disjunction, existence, and unique existence. *)
Definition disj (P Q : Type) : Type := (ptrunc (P ⨿ Q)).
Notation "P ∨ Q" := (disj P Q) (at level 85, right associativity) : uf_scope.

Definition Ex {X : Type} (P : X -> Type) : Type := (ptrunc ({x : X & P x})).

Definition ExUnique {X : Type} (P : X -> Type) : Type
  := isContr {x : X & P x}.

(** Exercise: for [x : ‖T‖], [∃_{t:T} (x = |t|)]. *)
Definition ptrunc_exists_trunc {T : Type} (x : (ptrunc T))
  : Ex (fun t : T => x = trunc t)
  := ptrunc_ind (fun x => Ex (fun t : T => x = trunc t))
       (fun _ => ptrunc_isProp) (fun t => trunc (t; refl)) x.

(** Exercise [xca:prop-trivia-1]: [P ≃ ‖P‖] for a proposition [P]. *)
Definition prop_ptrunc_eqv {P : Type} (h : isProp P) : P ≃ (ptrunc (P))
  := Eqv_of_props h ptrunc_isProp trunc (ptrunc_rec h idmap).

(** Definition [def:connected]: connected components and connectedness. *)
Definition component (A : Type) (a : A) : Type := {x : A & (ptrunc (a = x))}.

Definition isConn (A : Type) : Type := (ptrunc (A)) × (forall x y : A, (ptrunc (x = y))).

(** The empty type is not connected. *)
Definition False_not_isConn : ¬ isConn False
  := fun c => ptrunc_rec False_isProp idmap (fst c).

(** Exercise [xca:component-connected], first part. *)
Definition component_isConn {A : Type} (a : A) : isConn (component A a).
Proof.
  refine (trunc ((a; trunc refl) : component A a); _).
  intros [x p] [y q].
  revert p.
  refine (ptrunc_ind (fun p => (ptrunc (((x; p) : component A a) = (y; q))))
            (fun _ => ptrunc_isProp) _).
  intro p0. revert q.
  refine (ptrunc_ind (fun q => (ptrunc (((x; trunc p0) : component A a) = (y; q))))
            (fun _ => ptrunc_isProp) _).
  intro q0.
  exact (trunc (pathpair (q0 ⋅ p0⁻¹) (ptrunc_isProp _ _))).
Defined.

(** Identifications in [Prop_U] come from logical equivalences, using
    univalence. *)
Definition path_PropU `{Univalence} {P Q : PropU}
  (f : fst P -> fst Q) (g : fst Q -> fst P) : P = Q
  := pathpair (etop (Eqv_of_props (snd P) (snd Q) f g))
       (isProp_isProp (fst Q) _ _).

(** Exercise [xca:component-connected], second part: elements in the same
    component have the same propositional properties. *)
Definition same_component_props `{Univalence} {A : Type} (P : A -> PropU)
  {x y : A} (h : ptrunc (x = y)) : P x = P y.
Proof.
  pose (fg := ptrunc_rec
                (prod_isProp (fun_isProp (snd (P y))) (fun_isProp (snd (P x))))
                (fun e => (trp (fun z => fst (P z)) e;
                           trp (fun z => fst (P z)) e⁻¹)) h).
  exact (path_PropU (fst fg) (snd fg)).
Defined.

(** Exercise [xca:connected-trivia]. *)
Definition conn_loops_prop_isContr {A : Type} (c : isConn A)
  (h : forall a : A, isProp (a = a)) : isContr A.
Proof.
  assert (hp : forall x y : A, isProp (x = y)).
  { intros x y p q. destruct q. exact (h x p refl). }
  assert (hA : isProp A).
  { intros x y. exact (ptrunc_rec (hp x y) idmap (snd c x y)). }
  exact (isProp_inhabited_isContr hA (ptrunc_rec hA idmap (fst c))).
Defined.

Definition conn_set_isContr {A : Type} (c : isConn A) (s : isSet A)
  : isContr A
  := conn_loops_prop_isContr c (fun a => s a a).

(** Exercise [xca:connected-trivia-1]. *)
Definition Sigma_isConn {A : Type} {B : A -> Type} (cA : isConn A)
  (cB : forall x, isConn (B x)) : isConn {x : A & B x}.
Proof.
  refine (ptrunc_rec ptrunc_isProp
            (fun a => ptrunc_rec ptrunc_isProp (fun b => trunc (a; b))
                        (fst (cB a))) (fst cA); _).
  intros [a b] [a' b'].
  refine (ptrunc_rec ptrunc_isProp _ (snd cA a a')). intro p.
  refine (ptrunc_rec ptrunc_isProp _ (snd (cB a') (trp B p b) b')). intro q.
  exact (trunc (pathpair p q)).
Defined.

(** Exercise [xca:connected-trivia-2]. *)
Definition Sigma_ptrunc_isConn {A : Type} {B : A -> Type}
  (c : isConn {a : A & B a}) : isConn {a : A & ptrunc (B a)}.
Proof.
  pose (t := tot (fun a => @trunc (B a))).
  refine (ptrunc_rec ptrunc_isProp (fun w => trunc (t w)) (fst c); _).
  intros [a u] [a' u'].
  revert u.
  refine (ptrunc_ind
            (fun u => ptrunc (((a; u) : {a : A & ptrunc (B a)}) = (a'; u')))
            (fun _ => ptrunc_isProp) _).
  intro b. revert u'.
  refine (ptrunc_ind
            (fun u' => ptrunc (((a; trunc b) : {a : A & ptrunc (B a)}) = (a'; u')))
            (fun _ => ptrunc_isProp) _).
  intro b'.
  exact (ptrunc_rec ptrunc_isProp (fun r => trunc (ap t r)) (snd c (a; b) (a'; b'))).
Defined.

(** Definition [def:merely]: merely constructing an element of [T] means
    constructing an element of [‖T‖]. *)
