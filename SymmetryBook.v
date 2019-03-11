Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Local Set Implicit Arguments.
Local Unset Strict Implicit.

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

Theorem total2_paths_equiv {A : UU} (B : A -> UU) (x y : ∑ x, B x) :
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

Definition PathPair' {A : UU} {B : A -> UU} (x y : ∑ x, B x) :=
  ∑ p : pr1 x = pr1 y, PathOver (pr2 x) (pr2 y) p.

Local Open Scope pathsover.

Definition sectionPathOver {A : UU} {B : A -> UU} (f : ∏ x, B x) (x x':A) (p : x = x') :
  PathOver (f x) (f x') p ≃ (f x = f x).
Proof.
  use weq_iso.
  - intros q.
    induction p.
    exact q.
  - intros q.
    induction p.
    exact q.
  - cbn.
    intros q.
    induction p.
    reflexivity.
  - cbn.
    intros q.
    induction p.
    reflexivity.
Defined.

Definition sectionPathOver' {A : UU} {B : A -> UU} (f : ∏ x, B x) (x x':A) (p : x = x') :
  PathOver (f x) (f x') p ≃ (f x' = f x').
Proof.
  use weq_iso.
  - intros q.
    induction p.
    exact q.
  - intros q.
    induction p.
    exact q.
  - cbn.
    intros q.
    induction p.
    reflexivity.
  - cbn.
    intros q.
    induction p.
    reflexivity.
Defined.

Definition sectionPathPairMap {A : UU} {B : A -> UU} (f : ∏ x, B x) (x x':A) :
  PathPair' (x,,f x) (x',,f x') -> (x=x') × (f x = f x).
Proof.
  intros [p q].
  cbn in *.
  induction p.
  exists (idpath x).
  exact q.
Defined.

Definition sectionPathPair {A : UU} {B : A -> UU} (f : ∏ x, B x) (x x':A) :
  PathPair' (x,,f x) (x',,f x') ≃ (x=x') × (f x = f x).
Proof.
  unfold PathPair'.
  cbn.
  apply weqfibtototal.
  intros p.
  apply sectionPathOver.
Defined.

Definition sectionPathPairCompute {A : UU} {B : A -> UU} (f : ∏ x, B x) (x x':A)
           (pq : PathPair' (x,,f x) (x',,f x')) :
  sectionPathPairMap pq = sectionPathPair f x x' pq.
Proof.
  induction pq as [p q].
  cbn in *.
  induction p.
  reflexivity.
Defined.

Definition sectionPathPair' {A : UU} {B : A -> UU} (f : ∏ x, B x) (x x':A) :
  PathPair' (x,,f x) (x',,f x') ≃ (x=x') × (f x' = f x').
Proof.
  unfold PathPair'.
  cbn.
  apply weqfibtototal.
  intros p.
  apply sectionPathOver'.
Defined.

Definition composePathPair' {A : UU} {B : A -> UU} (x y z : ∑ x, B x) :
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

Theorem total2_paths_equiv' {A : UU} (B : A -> UU) (x y : ∑ x, B x) :
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

Definition toPathPair {A : UU} (B : A -> UU) (x y : ∑ x, B x) : x = y  ->  PathPair' x y.
Proof.
  intros e.
  induction e.
  exists (idpath (pr1 x)).
  change (pr2 x = pr2 x).
  exact (idpath (pr2 x)).
Defined.

Definition toPairPath {A : UU} (B : A -> UU) (x y : ∑ x, B x) : PathPair' x y -> x = y.
Proof.
  intros [p q].
  induction x as [a b], y as [a' b'].
  change (a=a') in p.
  induction p.
  change (b=b') in q.
  apply maponpaths.
  assumption.
Defined.

Definition sectionPath {A : UU} {B : A -> UU} (f : ∏ x, B x) (x x':A) :
  (x,,f x) = (x',,f x') ≃ (x=x') × (f x = f x).
Proof.
  intermediate_weq (PathPair' (x,,f x) (x',,f x')).
  - apply total2_paths_equiv'.
  - apply sectionPathPair.
Defined.

Definition sectionPathInvMap {A : UU} {B : A -> UU} (f : ∏ x, B x) (x x':A) :
  (x=x') × (f x = f x) -> (x,,f x) = (x',,f x').
Proof.
  intros [p q].
  induction p.
  apply toPairPath.
  exists (idpath x).
  cbn.
  exact q.
Defined.

Definition sectionPathInvMapCompute {A : UU} {B : A -> UU} (f : ∏ x, B x) (x x':A)
           (p : x=x') (q : f x = f x) :
  invmap (sectionPath f x x') (p,,q) = sectionPathInvMap (p,,q).
Proof.
  induction p.
  reflexivity.
Defined.

Definition sectionPath' {A : UU} {B : A -> UU} (f : ∏ x, B x) (x x':A) :
  (x,,f x) = (x',,f x') ≃ (x=x') × (f x' = f x').
Proof.
  intermediate_weq (PathPair' (x,,f x) (x',,f x')).
  - apply total2_paths_equiv'.
  - apply sectionPathPair'.
Defined.

Definition sectionPathInvMap' {A : UU} {B : A -> UU} (f : ∏ x, B x) (x x':A) :
  (x=x') × (f x' = f x') -> (x,,f x) = (x',,f x').
Proof.
  intros [p q].
  induction p.
  apply toPairPath.
  exists (idpath x).
  cbn.
  exact q.
Defined.

Definition sectionPathInvMapCompute' {A : UU} {B : A -> UU} (f : ∏ x, B x) (x x':A)
           (p : x=x') (q : f x' = f x') :
  invmap (sectionPath' f x x') (p,,q) = sectionPathInvMap' (p,,q).
Proof.
  induction p.
  reflexivity.
Defined.

Lemma toPathPair_isweq{A : UU} (B : A -> UU) (x y : ∑ x, B x) : isweq (@toPairPath A B x y).
Proof.
  intros p.
  use tpair.
  - use tpair.
    + exact (toPathPair p).
    + cbn beta.
      induction p.
      reflexivity.
  - cbn beta. intros [v r].
Abort.

Lemma toPathPair_isweq{A : UU} (B : A -> UU) (x y : ∑ x, B x) : isweq (@toPathPair A B x y).
Proof.
  intros p.
  apply iscontraprop1.
  - apply invproofirrelevance.
    intros [v r] [w s].
Abort.

Definition transport_f_f' {X : UU} (P : X ->UU) {x y z : X} (e : x = y)
           (e' : y = z) (p : P x) :
  transportf P (e @ e') p = transportf P e' (transportf P e p).
Proof.
  intros. induction e', e. reflexivity.
Defined.

Theorem total2_paths_composition {A : UU} (B : A -> UU) (x y z : ∑ x, B x)
        (p : x = y) (q : y = z)
        (p' := toPathPair p) (q' := toPathPair q) (pq' := toPathPair (p @ q)) :
  pq' = composePathPair' p' q'.
Proof.
  induction q, p.
  reflexivity.
Defined.

Theorem total2_paths_composition' {A : UU} (B : A -> UU) (x y z : ∑ x, B x)
        (p : x ╝ y) (q : y ╝ z) : unit.
Proof.
  set (r := total2_paths_equiv _ _ (invmap (total2_paths_equiv _ _) p @ invmap (total2_paths_equiv _ _) q)).
  induction p as [p p'].
  induction q as [q q'].
  induction x as [a b].
  induction y as [a' b'].
  induction z as [a'' b''].
  cbn in p, p', q, q'.
  transparent assert (s : (a,, b ╝ a'',, b'')).
  { exact ((p @ q),,(transport_f_f' p q b @ maponpaths (transportf B q) p' @ q')). }
  assert (r = s).
  { induction p, p', q, q'. reflexivity. }
Abort.

Definition sectionPathsComposition {A : UU} {B : A -> UU} (f : ∏ x, B x) (x x' x'':A)
           (p : x = x') (q : f x = f x)
           (p' : x' = x'') (q' : f x' = f x') :
  sectionPathInvMap (p,,q) @ sectionPathInvMap (p',,q')
  =
  sectionPathInvMap ((p @ p'),,(q @ transportb (λ a, f a = f a) p q')).
Proof.
  induction p.
  change (idpath x @ p') with p'.
  change (transportb (λ a : A, f a = f a) (idpath x) q') with q'.
  induction p'.
  cbn.
  apply pathsinv0.
  apply maponpathscomp0.
Defined.

Definition sectionPathsComposition1 {A : UU} {B : A -> UU} (f : ∏ x, B x) (x:A)
           (p : x = x) (q : f x = f x)
           (p' : x = x) (q' : f x = f x) :
  sectionPathInvMap (p,,q) @ sectionPathInvMap (p',,q')
  =
  sectionPathInvMap ((p @ p'),,(q @ transportb (λ a, f a = f a) p q')).
Proof.
  apply sectionPathsComposition.
Defined.

Definition sectionPathsComposition' {A : UU} {B : A -> UU} (f : ∏ x, B x) (x x' x'':A)
           (p : x = x') (q : f x' = f x')
           (p' : x' = x'') (q' : f x'' = f x'') :
  sectionPathInvMap' (p,,q) @ sectionPathInvMap' (p',,q')
  =
  sectionPathInvMap' ((p @ p'),,(transportf (λ a, f a = f a) p' q @ q')).
Proof.
  induction p.
  change (idpath x @ p') with p'.
  induction p'.
  change (transportf (λ a : A, f a = f a) (idpath x) q) with q.
  cbn.
  apply pathsinv0.
  apply maponpathscomp0.
Defined.

Definition sectionPathsComposition1' {A : UU} {B : A -> UU} (f : ∏ x, B x) (x:A)
           (p : x = x) (q : f x = f x)
           (p' : x = x) (q' : f x = f x) :
  sectionPathInvMap' (p,,q) @ sectionPathInvMap' (p',,q')
  =
  sectionPathInvMap' ((p @ p'),,(transportf (λ a, f a = f a) p' q @ q')).
Proof.
  apply sectionPathsComposition'.
Defined.
