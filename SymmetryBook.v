(* This file depends on having installed UniMath, available at https://github.com/UniMath/UniMath *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Local Set Implicit Arguments.
(* Local Unset Strict Implicit. *)

Definition cast (X Y:Type) (p:X=Y) : X≃Y.
Proof.
  induction p. exact (idweq _).
Defined.

Lemma foo (X:Type) (x:X) : iscontr (∑ y, x=y).
Proof.
  use tpair.
  - use tpair.
    + exact x.
    + reflexivity.
  - intros [y p].
    induction p.
    reflexivity.
Defined.

Section Coverings.
  Context (B:Type).
  Definition Covering := ∑ A (f:A -> B), ∏ b, isaset (hfiber f b).
  Definition CoveringMap (A A':Covering) := ∑ (g : pr1 A -> pr1 A'), pr12 A' ∘ g = pr12 A.
  Definition CoveringEquivalence (A A':Covering) := ∑ (g : pr1 A ≃ pr1 A'), pr12 A' ∘ g = pr12 A.
  Definition pathToEquiv (A A':Covering) : A=A' -> CoveringEquivalence A A'.
  Proof.
    intros p. induction p. exists (idweq _). reflexivity.
  Defined.
  Theorem coveringUnivalence (A A':Covering) : isweq (@pathToEquiv A A').
  Abort.
End Coverings.

Theorem total2_paths_equiv {A : Type} (B : A -> Type) (x y : ∑ x, B x) :
  x = y  ≃  x ╝ y.
Proof.
  use tpair.
  - intros e.
    induction e.
    exists (idpath (pr1 x)).
    change (pr2 x = pr2 x).
    exact (idpath (pr2 x)).
  - use isweq_iso.
    + intros [p q].
      induction x as [a b], y as [a' b'].
      change (a=a') in p.
      change (transportf _ p b = b') in q.
      induction p.
      change (b=b') in q.
      induction q.
      reflexivity.
    + intros e. induction e. reflexivity.
    + induction x as [a b], y as [a' b']. intros [p q].
      change (a=a') in p.
      change (transportf _ p b = b') in q.
      induction p.
      induction q.
      reflexivity.
Defined.

Definition PathPair' {A : Type} {B : A -> Type} (x y : ∑ x, B x) :=
  ∑ p : pr1 x = pr1 y, PathOver (pr2 x) (pr2 y) p.

Local Open Scope pathsover.

Definition sectionPathOver {A : Type} {B : A -> Type} (f : ∏ x, B x) (x x':A) (p : x = x') :
  PathOver (f x) (f x') p = (f x = f x).
Proof.
  induction p. reflexivity.
Defined.

Definition sectionPathOver' {A : Type} {B : A -> Type} (f : ∏ x, B x) (x x':A) (p : x = x') :
  PathOver (f x) (f x') p = (f x' = f x').
Proof.
  induction p. reflexivity.
Defined.

Definition sectionPathPairMap {A : Type} {B : A -> Type} (f : ∏ x, B x) (x x':A) :
  PathPair' (x,,f x) (x',,f x') -> (x=x') × (f x = f x).
Proof.
  intros [p q].
  cbn in *.
  induction p.
  exists (idpath x).
  exact q.
Defined.

Definition sectionPathPair_eq {A : Type} {B : A -> Type} (f : ∏ x, B x) (x x':A) :
  (PathPair' (x,,f x) (x',,f x')) = ((x=x') × (f x = f x)).
Proof.
  unfold PathPair'; cbn.
  unfold dirprod; cbn.
  apply maponpaths.
  apply funextsec; intros p.
  induction p.
  reflexivity.
Defined.

Definition sectionPathPair_weq {A : Type} {B : A -> Type} (f : ∏ x, B x) (x x':A) :
  (PathPair' (x,,f x) (x',,f x')) ≃ ((x=x') × (f x = f x)).
Proof.
  exact (cast (sectionPathPair_eq f x x')).
Defined.

Definition sectionPathPair_weq' {A : Type} {B : A -> Type} (f : ∏ x, B x) (x x':A) :
  PathPair' (x,,f x) (x',,f x') ≃ (x=x') × (f x = f x).
Proof.
  unfold PathPair'.
  cbn.
  apply weqfibtototal.          (* the proof above avoids weqfibtototal *)
  intros p.
  induction p.
  apply idweq.
Defined.

Definition sectionPathPairCompute {A : Type} {B : A -> Type} (f : ∏ x, B x) (x x':A)
           (pq : PathPair' (x,,f x) (x',,f x')) :
  sectionPathPairMap f pq = sectionPathPair_weq f x x' pq.
Proof.
  induction pq as [p q].
  cbn in *.
  induction p.
  Fail reflexivity.             (* the simpler proof doesn't compute as well *)
Abort.

Definition sectionPathPairCompute {A : Type} {B : A -> Type} (f : ∏ x, B x) (x x':A)
           (pq : PathPair' (x,,f x) (x',,f x')) :
  sectionPathPairMap f pq = sectionPathPair_weq' f x x' pq.
Proof.
  induction pq as [p q].
  cbn in *.
  induction p.
  reflexivity.
Defined.

Definition sectionPathPair'_weq' {A : Type} {B : A -> Type} (f : ∏ x, B x) (x x':A) :
  PathPair' (x,,f x) (x',,f x') ≃ (x=x') × (f x' = f x').
Proof.
  unfold PathPair'.
  cbn.
  apply weqfibtototal.
  intros p.
  induction p.
  apply idweq.
Defined.

Definition composePathPair' {A : Type} {B : A -> Type} (x y z : ∑ x, B x) :
  PathPair' x y -> PathPair' y z -> PathPair' x z.
Proof.
  induction x as [a b].
  induction y as [a' b'].
  induction z as [a'' b''].
  intros [p q] [r s].
  cbn in *.
  induction p, q, r, s.
  exists (idpath a).
  exact (idpath b).
Defined.

Theorem total2_paths_equiv' {A : Type} (B : A -> Type) (x y : ∑ x, B x) :
  x = y  ≃  PathPair' x y.
Proof.
  use tpair.
  - intros e.
    induction e.
    exists (idpath (pr1 x)).
    change (pr2 x = pr2 x).
    exact (idpath (pr2 x)).
  - use isweq_iso.
    + intros [p q].
      induction x as [a b], y as [a' b'].
      change (a=a') in p.
      induction p.
      change (b=b') in q.
      induction q.
      reflexivity.
    + intros e. induction e. reflexivity.
    + induction x as [a b], y as [a' b']. intros [p q].
      change (a=a') in p.
      induction p.
      change (b = b') in q.
      induction q.
      reflexivity.
Defined.

Definition toPathPair {A : Type} (B : A -> Type) (x y : ∑ x, B x) : x = y  ->  PathPair' x y.
Proof.
  intros e.
  induction e.
  exists (idpath (pr1 x)).
  change (pr2 x = pr2 x).
  exact (idpath (pr2 x)).
Defined.

Definition toPairPath {A : Type} (B : A -> Type) (x y : ∑ x, B x) : PathPair' x y -> x = y.
Proof.
  intros [p q].
  induction x as [a b], y as [a' b'].
  change (a=a') in p.
  induction p.
  change (b=b') in q.
  apply maponpaths.
  assumption.
Defined.

Definition sectionPath {A : Type} {B : A -> Type} (f : ∏ x, B x) (x x':A) :
  (x,,f x) = (x',,f x') ≃ (x=x') × (f x = f x).
Proof.
  intermediate_weq (PathPair' (x,,f x) (x',,f x')).
  - apply total2_paths_equiv'.
  - apply sectionPathPair_weq'.
Defined.

Definition sectionPathInvMap {A : Type} {B : A -> Type} (f : ∏ x, B x) (x x':A) :
  (x=x') × (f x = f x) -> (x,,f x) = (x',,f x').
Proof.
  intros [p q]. induction p. apply maponpaths. exact q.
Defined.

Definition sectionPathInvMapCompute {A : Type} {B : A -> Type} (f : ∏ x, B x) (x x':A)
           (p : x=x') (q : f x = f x) :
  invmap (sectionPath f x x') (p,,q) = sectionPathInvMap f (p,,q).
Proof.
  induction p. reflexivity.
Defined.

Definition sectionPath' {A : Type} {B : A -> Type} (f : ∏ x, B x) (x x':A) :
  (x,,f x) = (x',,f x') ≃ (x=x') × (f x' = f x').
Proof.
  intermediate_weq (PathPair' (x,,f x) (x',,f x')).
  - apply total2_paths_equiv'.
  - apply sectionPathPair'_weq'.
Defined.

Definition sectionPathInvMap' {A : Type} {B : A -> Type} (f : ∏ x, B x) (x x':A) :
  (x=x') × (f x' = f x') -> (x,,f x) = (x',,f x').
Proof.
  intros [p q]. induction p. apply maponpaths. exact q.
Defined.

Definition sectionPathInvMapCompute' {A : Type} {B : A -> Type} (f : ∏ x, B x) (x x':A)
           (p : x=x') (q : f x' = f x') :
  invmap (sectionPath' f x x') (p,,q) = sectionPathInvMap' f (p,,q).
Proof.
  induction p.
  reflexivity.
Defined.

Lemma toPathPair_isweq{A : Type} (B : A -> Type) (x y : ∑ x, B x) : isweq (@toPairPath A B x y).
Proof.
  intros p.
  use tpair.
  - use tpair.
    + exact (toPathPair B p).
    + cbn beta.
      induction p.
      reflexivity.
  - cbn beta. intros [v r].
Abort.

Lemma toPathPair_isweq{A : Type} (B : A -> Type) (x y : ∑ x, B x) : isweq (@toPathPair A B x y).
Proof.
  intros p.
  apply iscontraprop1.
  - apply invproofirrelevance.
    intros [v r] [w s].
Abort.

Definition transport_f_f' {X : Type} (P : X ->Type) {x y z : X} (e : x = y)
           (e' : y = z) (p : P x) :
  transportf P (e @ e') p = transportf P e' (transportf P e p).
Proof.
  intros. induction e', e. reflexivity.
Defined.

Theorem total2_paths_composition {A : Type} (B : A -> Type) (x y z : ∑ x, B x)
        (p : x = y) (q : y = z)
        (p' := toPathPair B p) (q' := toPathPair B q) (pq' := toPathPair _ (p @ q)) :
  pq' = composePathPair' p' q'.
Proof.
  induction q, p.
  reflexivity.
Defined.

Section Composition.

  Notation "p · q" := (q @ p).  (* notation as in the book *)

  Definition act {A : Type} {B : A -> Type} (f : ∏ x, B x) (x x':A)
             (q : f x' = f x') (p : x = x')
    : f x = f x.
  Proof.
    induction p. exact q.
  Defined.

  (* We put p to the right of q in the definition above so the equation below has
     the terms in the same order on both sides, namely q p' p.  Thus the action is
     "on the right". *)

  Definition act_transitivity {A : Type} {B : A -> Type} (f : ∏ x, B x) (x x' x'':A)
             (p : x = x') (p' : x' = x'') (q : f x'' = f x'')
    : act f (act f q p') p = act f q (p' · p).
  Proof.
    induction p, p'. reflexivity.
  Defined.

  Definition sectionPathsComposition {A : Type} {B : A -> Type} (f : ∏ x, B x) (x x' x'':A)
             (p : x = x') (q : f x = f x)
             (p' : x' = x'') (q' : f x' = f x') :
    sectionPathInvMap f (p',,q') · sectionPathInvMap f (p,,q)
    =
    sectionPathInvMap f ((p' · p),,(act f q' p · q)).
  Proof.
    induction p.
    change (p' · idpath x) with p'.
    change (act f q' (idpath x)) with q'.
    induction p'.
    cbn.
    apply pathsinv0.
    apply maponpathscomp0.
  Defined.

  Definition sectionPathsComposition1 {A : Type} {B : A -> Type} (f : ∏ x, B x) (x:A)
             (p : x = x) (q : f x = f x)
             (p' : x = x) (q' : f x = f x) :
    sectionPathInvMap f (p',,q') · sectionPathInvMap f (p,,q)
    =
    sectionPathInvMap f ((p' · p),,(act f q' p · q)).
  Proof.
    apply sectionPathsComposition.
  Defined.

End Composition.

Section Composition'.

  Definition sectionPathsComposition' {A : Type} {B : A -> Type} (f : ∏ x, B x) (x x' x'':A)
             (p : x = x') (q : f x' = f x')
             (p' : x' = x'') (q' : f x'' = f x'') :
    sectionPathInvMap' f (p,,q) @ sectionPathInvMap' f (p',,q')
    =
    sectionPathInvMap' f ((p @ p'),,(transportf (λ a, f a = f a) p' q @ q')).
  Proof.
    induction p.
    change (idpath x @ p') with p'.
    induction p'.
    change (transportf (λ a : A, f a = f a) (idpath x) q) with q.
    cbn.
    apply pathsinv0.
    apply maponpathscomp0.
  Defined.

  Definition sectionPathsComposition1' {A : Type} {B : A -> Type} (f : ∏ x, B x) (x:A)
             (p : x = x) (q : f x = f x)
             (p' : x = x) (q' : f x = f x) :
    sectionPathInvMap' f (p,,q) @ sectionPathInvMap' f (p',,q')
    =
    sectionPathInvMap' f ((p @ p'),,(transportf (λ a, f a = f a) p' q @ q')).
  Proof.
    apply sectionPathsComposition'.
  Defined.

End Composition'.

(*
 Local Variables:
 coq-prog-args: ("-emacs" "-w" "-notation-overridden" "-type-in-type")
 compile-command: "coqc -w -notation-overridden -type-in-type SymmetryBook.v "
 End:
 *)