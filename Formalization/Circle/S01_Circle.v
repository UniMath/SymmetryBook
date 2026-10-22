(** * Section 3.1 The circle and its universal property

    Part of Chapter 3 ([circle.tex]); see [Circle.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - [def:circle]: the circle is the library's [Circle], with [base] and
      [loop] (same names), induction [S1_ind :≡ Circle_ind] (its loop case
      is a [PathOver], i.e. the library's [DPath]) and recursion
      [S1_rec :≡ Circle_rec], both computing on [base] by definition, with
      the computation rules for [loop].
    - [lem:freeloopspace], following the book's proof: the general result
      [S1_fun_path] (from [p : f(base) = g(base)] and
      [q : f(loop) = p⁻¹ · g(loop) · p] to [f = g]) by circle induction,
      using [lem:trp-in-fx=Ygx].
    - [cor:circle-loopspace], by the direct proof of the footnote (inverse
      [l ↦ (ve(a,l), refl_a)]).
    - Remark [rem:dep-univ-prop-circle]: the dependent universal property.
    - [lem:circleisconnected].
    - The remark that [∏_{z:S1}(base = z)] contradicts univalence
      ([no_base_paths]), via [loop ≠ refl] ([loop_ne_refl], using the
      loop [swap] of [Bool] in the universe). *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Colimits.Coeq Colimits.Pushout
  Spaces.Nat.Core Spaces.Int Spaces.Circle.
From SymmetryBook Require Export IntroUF.IntroUF.

Local Open Scope uf_scope.

(** Chapter introduction, items [it:one-out] and [it:prop-in]: maps
    [𝟙 → A] correspond to elements of [A] ([xca:Xequiv1toX] in 2.9), and
    maps [A → Prop] to subtypes of [A] ([lem:Sub(T)=Inj(T)] in 2.20). *)

(** ** 3.1 The circle and its universal property *)

(** Definition [def:circle]: the circle is the library's [Circle], with
    the constructors [base] and [loop] (same names as in the book).  The
    induction principle is the library's [Circle_ind]: its loop case is
    a path over [loop] (the book's [PathOver] is the library's [DPath],
    i.e. [trp_loop(a) = a]), and it computes on [base] by definition. *)
Definition S1 : Type := Circle.

Definition S1_ind (A : S1 -> Type) (a : A base) (l : PathOver A loop a a)
  : forall x : S1, A x
  := Circle_ind A a l.

Definition S1_ind_base (A : S1 -> Type) (a : A base) (l : PathOver A loop a a)
  : S1_ind A a l base = a := refl.

Definition S1_ind_loop (A : S1 -> Type) (a : A base) (l : PathOver A loop a a)
  : apd (S1_ind A a l) loop = l
  := Circle_ind_beta_loop A a l.

Definition S1_rec (A : Type) (a : A) (l : a = a) : S1 -> A := Circle_rec A a l.

Definition S1_rec_base (A : Type) (a : A) (l : a = a) : S1_rec A a l base = a
  := refl.

Definition S1_rec_loop (A : Type) (a : A) (l : a = a)
  : ap (S1_rec A a l) loop = l
  := Circle_rec_beta_loop A a l.

(** A family of propositions over [S1] is given by its value at [base]. *)
Definition S1_ind_prop (A : S1 -> Type) (hA : forall x, isProp (A x)) (a : A base)
  : forall x : S1, A x
  := S1_ind A a (hA base _ _).

(** Theorem [lem:freeloopspace]. *)
Section FreeLoopSpace.

  Context {A : Type}.

  Definition ev (g : S1 -> A) : {a : A & a = a} := (g base; ap g loop).

  Definition ve (w : {a : A & a = a}) : S1 -> A := S1_rec A (fst w) (snd w).

  (** The more general result in the proof: for [p : f(base) = g(base)]
      and [q : f(loop) = p⁻¹ · g(loop) · p] we get [f = g]. *)
  Definition conj_cancel {x y : A} (p : x = y) (s : x = y)
    : (s ⋅ (p⁻¹ ⋅ s)⁻¹) = p.
  Proof. destruct p. exact (trans_Vp s). Defined.

  Definition S1_htpy {f g : S1 -> A} (p : f base = g base)
    (q : ap f loop = p⁻¹ ⋅ (ap g loop ⋅ p))
    : forall x, f x = g x.
  Proof.
    refine (S1_ind (fun x => f x = g x) p _).
    refine (trp_paths_fg f g loop p @ _).
    refine (ap (fun r => (ap g loop ⋅ p) ⋅ r⁻¹) q @ _).
    exact (conj_cancel p (ap g loop ⋅ p)).
  Defined.

  Definition S1_fun_path `{Funext} {f g : S1 -> A} (p : f base = g base)
    (q : ap f loop = p⁻¹ ⋅ (ap g loop ⋅ p))
    : f = g
    := ptw_inv (S1_htpy p q).

  Definition ev_isEquiv `{Funext} : isEquiv ev.
  Proof.
    refine (iso_to_isEquiv ev ve _ _).
    - intro f. exact (S1_fun_path (f := ve (ev f)) (g := f) refl
                        (S1_rec_loop _ _ _ @ (trans_1p _)^)).
    - intros [a l]. exact (ap (fun r => (a; r) : {a : A & a = a}) (S1_rec_loop A a l)).
  Defined.

  Definition ev_Eqv `{Funext} : (S1 -> A) ≃ {a : A & a = a} := (ev; ev_isEquiv).

End FreeLoopSpace.

Arguments ev A g : clear implicits.
Arguments ve A w : clear implicits.

(** The circle pointed at [base]. *)
Definition S1star : Ustar := (S1; base).

(** Corollary [cor:circle-loopspace].  We follow the direct proof of the
    footnote: the inverse sends [l] to [(ve(a,l), refl_a)]. *)
Section CircleLoopSpace.

  Context {A : Type}.

  Definition evp (a : A) (g : S1star →* (A; a)) : a = a
    := (snd g)⁻¹ ⋅ (ap (fst g) loop ⋅ snd g).

  Definition evp_inv (a : A) (l : a = a) : S1star →* (A; a)
    := (ve A (a; l); refl).

  Definition evp_inv_evp `{Funext} (a : A) (g : S1star →* (A; a))
    : evp_inv a (evp a g) = g.
  Proof.
    destruct g as [f p]. change (S1 -> A) in f. change (a = f base) in p.
    revert a p. refine (paths_ind_r _ _ _).
    refine (eqinv (snd (ptw_star _ _)) _).
    exact (S1_htpy (f := ve A (f base; evp (f base) (f; refl))) (g := f) refl
             (S1_rec_loop _ _ _); refl).
  Defined.

  Definition evp_isEquiv `{Funext} (a : A) : isEquiv (evp a)
    := iso_to_isEquiv (evp a) (evp_inv a) (evp_inv_evp a)
         (fun l => trans_1p _ @ S1_rec_loop A a l).

End CircleLoopSpace.

(** Remark [rem:dep-univ-prop-circle]: the dependent universal property. *)
Section DepUnivProp.

  Context {A : S1 -> Type}.

  Definition evd (g : forall x, A x) : {a : A base & PathOver A loop a a}
    := exist (fun a : A base => PathOver A loop a a) (g base) (apd g loop).

  Definition evd_isEquiv `{Funext} : isEquiv evd.
  Proof.
    refine (iso_to_isEquiv evd (fun w => S1_ind A (fst w) (snd w)) _ _).
    - intro g. apply ptw_inv.
      refine (S1_ind _ refl _).
      refine (trp_paths_dep _ g loop refl @ _). cbn.
      refine (ap (fun r => (po_to_trp (apd g loop) ⋅ refl) ⋅ (po_to_trp r)⁻¹)
                 (S1_ind_loop _ _ _) @ _).
      exact (ap (fun r => r ⋅ (po_to_trp (apd g loop))⁻¹) (trans_1p _) @ trans_Vp _).
    - intros [a l]. exact (ap (fun r => (a; r) : {a : A base & PathOver A loop a a})
                              (S1_ind_loop A a l)).
  Defined.

End DepUnivProp.

(** [loop ≠ refl], via the loop [swap] of [Bool] in the universe. *)
Definition loop_ne_refl `{Univalence} : loop ≠ refl.
Proof.
  intro e.
  pose (F := S1_rec Type Bool (etop swapEqv)).
  assert (q : ap F loop = etop swapEqv) by exact (S1_rec_loop _ _ _).
  apply yes_ne_no.
  refine (_ @ ptw (ap fst (ptoe_etop swapEqv)) yes).
  exact (ap (fun r => ptoe r yes) (q^ @ ap (ap F) e))^.
Defined.

(** The remark after [lem:circleisconnected]: an element of
    [∏_{z:S1}(base = z)] contradicts univalence. *)
Definition no_base_paths `{Univalence} : (forall z : S1, base = z) -> False.
Proof.
  intro c. apply loop_ne_refl.
  pose (d := apD c loop).
  rewrite transport_paths_r in d.
  exact (cancelL (c base) _ _ (d @ (concat_p1 _)^)).
Defined.

(** Lemma [lem:circleisconnected]. *)
Definition S1_base_paths : forall z : S1, ptrunc (base = z)
  := S1_ind_prop (fun z => ptrunc (base = z)) (fun _ => ptrunc_isProp) (trunc refl).

Definition S1_isConn : isConn S1
  := (trunc base;
      fun x y => ptrunc_rec ptrunc_isProp
                   (fun p => ptrunc_rec ptrunc_isProp (fun q => trunc (q ⋅ p⁻¹))
                               (S1_base_paths y))
                   (S1_base_paths x)).
