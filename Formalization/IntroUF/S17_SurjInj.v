(** * Section 2.17 More on equivalences; surjections and injections

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Surjections (and split surjections with their sections) and
      injections, with the book's convention [y = f x] (the library's
      versions use [f x = y]); exercise [xca:inj-sets], including a
      function [True → Set] that is not injective (it maps to [Bool], and
      uses [refl ≠ swap] from 2.13); [SetU] is the book's [Set], a
      reserved word in Rocq.
    - [lem:inj+surj], [cor:inj+connected] and
      [lem:whenisbasespaceconnected].
    - [con:fib-vs-path], following the book's chain of equivalences, and
      [lem:inj-ap].
    - [cor:fib-vs-path]: parts 1 and 2 are proved for any property [Q] of
      types invariant under equivalence, and instantiated with [is_ntype n]
      ([n ≥ 0]), [isProp] ([n = -1]) and [isContr] ([n = -2]); parts 3
      and 4 for connected types.
    - Exercise [xca:sum-equivalences].
    - The image [im f] and the factorization [f = i ∘ p], which commutes
      by definition, with [p] surjective and [i] injective; exercises
      [xca:prop-image-is-set] and [xca:all-prop-image].
    - Exercise [xca:unique-fact-image], second part: the type [ImFact]
      of image factorizations is contractible ([ImFact_isContr]).  It
      suffices that [ImFact] is a proposition.  Following a hint by the
      author, two factorizations [(C,g,h)] and [(C',g',h')] give
      [e : C → C'] with [e(c)] in the fiber of [h'] at [h(c)]: that fiber
      is a proposition, so we may assume [a : A] with [c = g(a)] and take
      [g'(a)] ([fact_map]).  The same construction in the other direction
      gives an inverse ([fact_Eqv]).  To avoid transporting [f = h ∘ g]
      along [ua(e)], the 6-tuples are reordered as
      [(C, h, isInj h, (g, f = h ∘ g), isSurj g)] ([ImFact_reorder]); for
      injective [h], [∑_g (f = h ∘ g)] is a proposition ([lift_isProp]),
      being a retract of [∏_a h⁻¹(f(a))].  So only [(C, h)] has to be
      identified, by induction on the path [ua(e)] ([fact_path]).
      NOTE for the book text: the author's hint, together with the
      observation that [∑_g (f = h ∘ g)] is a proposition when [h] is
      injective, could be added to the exercise. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S16_PropTruncation.

Local Open Scope uf_scope.

(** ** 2.17 More on equivalences; surjections and injections *)

(** Definition [def:surjection]. *)
Definition isSurj {A B : Type} (f : A -> B) : Type
  := forall b : B, Ex (fun a : A => b = f a).

(** Footnote: split surjections, and their sections. *)
Definition isSplitSurj {A B : Type} (f : A -> B) : Type
  := forall b : B, fiber f b.

Definition splitSurj_section `{Funext} {A B : Type} {f : A -> B}
  (s : isSplitSurj f)
  : {g : B -> A & f ∘ g = id B}
  := ((fun b => fst (s b)); ptw_inv (fun b => (snd (s b))⁻¹)).

(** Definition [def:injection]. *)
Definition isInj {A B : Type} (f : A -> B) : Type
  := forall b : B, isProp (fiber f b).

(** Exercise [xca:inj-sets]. *)
Definition isInj_cancel {A B : Type} {f : A -> B} (j : isInj f)
  : forall a a' : A, f a = f a' -> a = a'
  := fun a a' e => ap fst (j (f a') (a; e⁻¹) (a'; refl)).

Definition cancel_isInj {A B : Type} (sB : isSet B) {f : A -> B}
  (c : forall a a' : A, f a = f a' -> a = a') : isInj f.
Proof.
  intros b [a p] [a' p'].
  exact (pathpair (c a a' (p' ⋅ p⁻¹)) (sB _ _ _ _)).
Defined.

(** The type [Set_U :≡ ∑_{X:U} isSet(X)] ([Set] is reserved in Rocq). *)
Definition SetU : Type := {X : Type & isSet X}.

(** A function [True → Set] that is not injective. *)
Definition Bool_SetU : True -> SetU := fun _ => (Bool; isSet_bool).

Definition Bool_SetU_not_isInj `{Univalence} : ¬ isInj Bool_SetU.
Proof.
  intro j.
  pose (f := Bool_SetU).
  pose (g := fun w : fiber f (f triv) =>
               match fst w as t return (f triv = f t) -> (f triv = f triv) with
               | triv => idmap
               end (snd w)).
  pose (e2 := pathpair swap (isSet_isProp Bool _ _) : f triv = f triv).
  pose (r := ap g (j (f triv) (triv; refl) (triv; e2)) : refl = e2).
  apply refl_ne_swap.
  exact (ap_fst_pathpair swap _ ⋅ ap (ap fst) r).
Defined.

(** Lemma [lem:inj+surj]. *)
Definition isEquiv_isInj {A B : Type} {f : A -> B} (t : isEquiv f) : isInj f
  := fun b => isContr_isProp' (t b).

Definition isEquiv_isSurj {A B : Type} {f : A -> B} (t : isEquiv f)
  : isSurj f
  := fun b => trunc (fst (t b)).

Definition inj_surj_isEquiv `{Funext} {A B : Type} {f : A -> B}
  (j : isInj f) (s : isSurj f) : isEquiv f
  := fun b => ptrunc_rec (isContr_isProp _)
                (fun w => isProp_inhabited_isContr (j b) w) (s b).

(** Corollary [cor:inj+connected]. *)
Definition inj_conn_isEquiv `{Funext} {A B : Type} {f : A -> B}
  (nA : (ptrunc (A))) (cB : isConn B) (j : isInj f) : isEquiv f.
Proof.
  apply (inj_surj_isEquiv j). intro b.
  refine (ptrunc_rec ptrunc_isProp _ nA). intro a.
  exact (ptrunc_rec ptrunc_isProp (fun p => trunc (a; p)) (snd cB b (f a))).
Defined.

(** Lemma [lem:whenisbasespaceconnected]. *)
Definition surj_isConn {X Y : Type} {f : X -> Y} (s : isSurj f)
  (cX : isConn X) : isConn Y.
Proof.
  refine (ptrunc_rec ptrunc_isProp (fun x => trunc (f x)) (fst cX); _).
  intros y y'.
  refine (ptrunc_rec ptrunc_isProp _ (s y)). intros [x p].
  refine (ptrunc_rec ptrunc_isProp _ (s y')). intros [x' p'].
  refine (ptrunc_rec ptrunc_isProp _ (snd cX x x')). intro q.
  exact (trunc ((p'⁻¹ ⋅ ap f q) ⋅ p)).
Defined.

(** Construction [con:fib-vs-path]:
    [(z = z') ≃ ap_f⁻¹(snd(z') · snd(z)⁻¹)] (equation [eq:fib_vs-path]), following the chain of
    equivalences in the book. *)
Definition trp_fiber_path {A B : Type} (f : A -> B) {b : B} {a a' : A}
  (q : a = a') (p : b = f a)
  : trp (fun x => b = f x) q p = ap f q ⋅ p
  := match q with refl => refl end.

Definition cancel_eqv {X : Type} {b c d : X} (r : c = d) (p : b = c)
  (p' : b = d) : (r ⋅ p = p') ≃ (p' ⋅ p⁻¹ = r).
Proof.
  refine (Eqv_comp _ symm_eqv).
  destruct p.
  exact (Eqv_comp (eq_l_eqv (trans_1p r)) (eq_r_eqv (trans_1p p')⁻¹)).
Defined.

Definition fib_vs_path {A B : Type} (f : A -> B) {b : B} (z z' : fiber f b)
  : (z = z') ≃ fiber (ap f) (snd z' ⋅ (snd z)⁻¹).
Proof.
  destruct z as [a p], z' as [a' p'].
  refine (Eqv_comp (Eqv_inv (path_sigma_eqv (Y := fun x => b = f x))) _).
  pose (E := fun q : a = a' =>
               Eqv_comp (eq_l_eqv (trp_fiber_path f q p)) (cancel_eqv (ap f q) p p')).
  exact (tot (fun q => fst (E q)); tot_isEquiv _ (fun q => snd (E q))).
Defined.

(** Lemma [lem:inj-ap]. *)
Definition isInj_ap_isEquiv {A B : Type} {f : A -> B} (j : isInj f)
  : forall a a' : A, isEquiv (@ap A B f a a').
Proof.
  intros a a' r.
  pose (z := (a; refl) : fiber f (f a)).
  pose (z' := (a'; r) : fiber f (f a)).
  pose (c := Overture.fst (isProp_iff_paths_contr _) (j (f a)) z z').
  exact (trp (fun s => isContr (fiber (ap f) s)) (trans_1p r)
           (isContr_Eqv (fib_vs_path f z z') c)).
Defined.

Definition ap_isEquiv_isInj {A B : Type} {f : A -> B}
  (h : forall a a' : A, isEquiv (@ap A B f a a')) : isInj f
  := fun b z z' => eqinv (snd (fib_vs_path f z z'))
                     (fst (h (fst z) (fst z') (snd z' ⋅ (snd z)⁻¹))).

(** Corollary [cor:fib-vs-path].  We state the first two parts for any
    property [Q] of types that is invariant under equivalence; the book's
    statements are the instances [Q :≡ is_ntype n] (for [n ≥ 0]), and
    also [Q :≡ isProp] ([n = -1]) and [Q :≡ isContr] ([n = -2], which is
    [lem:inj-ap]).  Note that [is_ntype (succ n) X] is by definition
    [∏_{x,y:X} is_ntype n (x = y)]. *)
Section FibVsPath.

  Context {A B : Type} (f : A -> B) (Q : Type -> Type)
    (Qinv : forall X Y : Type, X ≃ Y -> Q X -> Q Y).

  (** Part [set-fib-vs-path]. *)
  Definition fibers_paths_Q
    : (forall (b : B) (z z' : fiber f b), Q (z = z'))
      -> forall (a a' : A) (r : f a = f a'), Q (fiber (ap f) r)
    := fun h a a' r =>
         trp (fun s => Q (fiber (ap f) s)) (trans_1p r)
           (Qinv _ _ (fib_vs_path f (a; refl) (a'; r)) (h (f a) _ _)).

  Definition Q_paths_fibers
    : (forall (a a' : A) (r : f a = f a'), Q (fiber (ap f) r))
      -> forall (b : B) (z z' : fiber f b), Q (z = z')
    := fun h b z z' => Qinv _ _ (Eqv_inv (fib_vs_path f z z')) (h _ _ _).

  (** Part [set-fib-vs-path-point], for [Q] proposition-valued. *)
  Definition Q_paths_fibers_point `{Funext} (Qprop : forall X, isProp (Q X))
    (cA : isConn A) (a : A)
    : (forall r : f a = f a, Q (fiber (@ap A B f a a) r))
      -> forall (b : B) (z z' : fiber f b), Q (z = z').
  Proof.
    intro h. apply Q_paths_fibers. intros a1 a2.
    refine (ptrunc_rec (Pi_isProp (fun _ => Qprop _)) _ (snd cA a a1)). intro p1.
    refine (ptrunc_rec (Pi_isProp (fun _ => Qprop _)) _ (snd cA a a2)). intro p2.
    destruct p1, p2. exact h.
  Defined.

End FibVsPath.

Definition isContr_Qinv : forall X Y : Type, X ≃ Y -> isContr X -> isContr Y
  := fun X Y => isContr_Eqv.

Definition isProp_Qinv : forall X Y : Type, X ≃ Y -> isProp X -> isProp Y
  := fun X Y => isProp_Eqv.

Definition is_ntype_Qinv (n : ℕ)
  : forall X Y : Type, X ≃ Y -> is_ntype n X -> is_ntype n Y
  := fun X Y => is_ntype_Eqv n.

(** Part [set-fib-vs-path] for [n]-types, [n ≥ 0]: all fibers of [f] are
    [(n+1)]-types iff all fibers of the maps [ap f] are [n]-types. *)
Definition fibers_ntype_iff {A B : Type} (f : A -> B) (n : ℕ)
  : ((forall b : B, is_ntype (succ n) (fiber f b))
      -> forall (a a' : A) (r : f a = f a'), is_ntype n (fiber (ap f) r))
    × ((forall (a a' : A) (r : f a = f a'), is_ntype n (fiber (ap f) r))
      -> forall b : B, is_ntype (succ n) (fiber f b))
  := (fibers_paths_Q f (is_ntype n) (is_ntype_Qinv n);
      Q_paths_fibers f (is_ntype n) (is_ntype_Qinv n)).

(** Part [conn-fib-vs-path]. *)
Definition conn_isEquiv_iff `{Funext} {A B : Type} (f : A -> B)
  (cA : isConn A) (cB : isConn B)
  : (isEquiv f -> forall a a' : A, isEquiv (@ap A B f a a'))
    × ((forall a a' : A, isEquiv (@ap A B f a a')) -> isEquiv f)
  := (fun t => isInj_ap_isEquiv (isEquiv_isInj t);
      fun h => inj_conn_isEquiv (fst cA) cB (ap_isEquiv_isInj h)).

(** Part [conn-fib-vs-path-point]. *)
Definition conn_isEquiv_iff_point `{Funext} {A B : Type} (f : A -> B)
  (cA : isConn A) (cB : isConn B) (a : A)
  : (isEquiv f -> isEquiv (@ap A B f a a))
    × (isEquiv (@ap A B f a a) -> isEquiv f).
Proof.
  refine ((fun t => fst (conn_isEquiv_iff f cA cB) t a a); _).
  intro h.
  apply (inj_conn_isEquiv (fst cA) cB).
  intro b. apply (Overture.snd (isProp_iff_paths_contr _)).
  exact (Q_paths_fibers_point f isContr isContr_Qinv isContr_isProp cA a h b).
Defined.

(** Exercise [xca:sum-equivalences]. *)
Definition sum_equivalences {A B : Type} {F : A -> Type} {G : B -> Type}
  (f : A ≃ B) (g : forall a, F a ≃ G (fst f a))
  : {a : A & F a} ≃ {b : B & G b}
  := Eqv_comp (tot (fun a => fst (g a)); tot_isEquiv _ (fun a => snd (g a)))
       (Eqv_of_Equiv (equiv_functor_sigma_pb (Q := G) (Equiv_of_Eqv f))).

(** Definition [def:prop-image]: the (propositional) image. *)
Definition im {A B : Type} (f : A -> B) : Type
  := {y : B & Ex (fun x : A => y = f x)}.

(** Exercise [xca:unique-fact-image], first part: the factorization
    [f = i ∘ p], which commutes by definition, with [p] surjective and
    [i] injective. *)
Section ImageFactorization.

  Context {A B : Type} (f : A -> B).

  Definition im_p : A -> im f := fun x => (f x; trunc (x; refl)).

  Definition im_i : im f -> B := fst.

  Definition im_factor : f = im_i ∘ im_p := refl.

  Definition im_p_isSurj : isSurj im_p.
  Proof.
    intros [y u]. revert u.
    refine (ptrunc_ind
              (fun u => Ex (fun x : A => ((y; u) : im f) = im_p x))
              (fun _ => ptrunc_isProp) _).
    intros [x e].
    exact (trunc (x; pathpair e (ptrunc_isProp _ _))).
  Defined.

  Definition im_i_isInj : isInj im_i.
  Proof.
    intros b [[y u] e] [[y' u'] e'].
    change (b = y) in e. change (b = y') in e'.
    destruct e, e'.
    exact (ap (fun u0 => (((b; u0) : im f); refl) : fiber im_i b)
              (ptrunc_isProp u u')).
  Defined.

End ImageFactorization.

(** Exercise [xca:unique-fact-image], second part: the type of image
    factorizations is contractible. *)
Section ImageFactorizationUnique.

  Context `{Univalence} {A B : Type} (f : A -> B).

  (** The type of image factorizations of [f]. *)
  Definition ImFact : Type
    := {C : Type & {g : A -> C & {h : C -> B &
         (f = h ∘ g) × isSurj g × isInj h}}}.

  Definition im_fact : ImFact
    := (im f; (im_p f; (im_i f; ((refl; im_p_isSurj f); im_i_isInj f)))).

  Definition isSurj_isProp {X Y : Type} (g : X -> Y) : isProp (isSurj g)
    := Pi_isProp (fun _ => ptrunc_isProp).

  (** If [h] is injective, then [∑_{g : A → C} (f = h ∘ g)] is a
      proposition: it is a retract of [∏_{a:A} h⁻¹(f(a))]. *)
  Definition lift_isProp {C : Type} {h : C -> B} (j : isInj h)
    : isProp {g : A -> C & f = h ∘ g}.
  Proof.
    pose (s := fun w : {g : A -> C & f = h ∘ g} =>
                 (fun a => (fst w a; ptw (snd w) a)) : forall a, fiber h (f a)).
    pose (r := fun F : forall a, fiber h (f a) =>
                 ((fun a => fst (F a)); ptw_inv (fun a => snd (F a)))
                 : {g : A -> C & f = h ∘ g}).
    assert (rs : forall w, r (s w) = w).
    { intros [g φ]. exact (ap (fun φ' => (g; φ') : {g : A -> C & f = h ∘ g})
                              (eqinv_l (funext _ _) φ)). }
    intros w w'.
    exact ((rs w)^ @ ap r (Pi_isProp (fun a => j (f a)) (s w) (s w')) @ rs w').
  Defined.

  (** The factorizations, reordered: first [C] and the injection [h]. *)
  Definition FactRest (C : Type) (h : C -> B) : Type
    := {j : isInj h & {w : {g : A -> C & f = h ∘ g} & isSurj (fst w)}}.

  Definition FactRest_isProp (C : Type) (h : C -> B) : isProp (FactRest C h)
    := Sigma_isProp (Pi_isProp (fun _ => isProp_isProp _))
         (fun j => Sigma_isProp (lift_isProp j) (fun w => isSurj_isProp _)).

  Definition ImFact' : Type := {C : Type & {h : C -> B & FactRest C h}}.

  Definition ImFact_reorder : ImFact ≃ ImFact'.
  Proof.
    refine (mkEqv (fun x : ImFact => match x with (C; (g; (h; ((φ; s); j)))) =>
                              ((C; (h; (j; ((g; φ); s)))) : ImFact') end)
                  (fun x : ImFact' => match x with (C; (h; (j; ((g; φ); s)))) =>
                              ((C; (g; (h; ((φ; s); j)))) : ImFact) end) _ _).
    - intros [C [g [h [[φ s] j]]]]. exact refl.
    - intros [C [h [j [[g φ] s]]]]. exact refl.
  Defined.

  (** Following a hint by the author: for factorizations [(C,g,h)] and
      [(C',g',h')], define [e(c)] in the fiber of [h'] at [h(c)], which is
      a proposition; so we may assume [a : A] with [c = g(a)], and take
      [g'(a)]. *)
  Definition fact_map {C C' : Type} {h : C -> B} {h' : C' -> B}
    (r : FactRest C h) (r' : FactRest C' h') (c : C) : fiber h' (h c).
  Proof.
    destruct r as [j [[g φ] s]], r' as [j' [[g' φ'] s']].
    refine (ptrunc_rec (j' (h c)) _ (s c)). intros [a p].
    exact (g' a; ap h p @ (ptw φ a)^ @ ptw φ' a).
  Defined.

  Definition fact_Eqv {C C' : Type} {h : C -> B} {h' : C' -> B}
    (r : FactRest C h) (r' : FactRest C' h') : C ≃ C'.
  Proof.
    refine (mkEqv (fun c => fst (fact_map r r' c))
                  (fun c' => fst (fact_map r' r c')) _ _).
    - intro c. exact (ap fst (fst r (h c)
        (_; snd (fact_map r r' c) @ snd (fact_map r' r _)) (c; refl))).
    - intro c'. exact (ap fst (fst r' (h' c')
        (_; snd (fact_map r' r c') @ snd (fact_map r r' _)) (c'; refl))).
  Defined.

  Definition fact_path {C C' : Type} (p : C = C') {h : C -> B} {h' : C' -> B}
    (hh : forall c, h c = h' (ptoe p c)) (r : FactRest C h) (r' : FactRest C' h')
    : ((C; (h; r)) : ImFact') = (C'; (h'; r')).
  Proof.
    destruct p. destruct (ptw_inv hh : h = h').
    exact (ap (fun r0 => ((C; (h; r0)) : ImFact')) (FactRest_isProp C h r r')).
  Defined.

  Definition ImFact'_isProp : isProp ImFact'.
  Proof.
    intros [C [h r]] [C' [h' r']].
    pose (E := fact_Eqv r r').
    refine (fact_path (etop E) _ r r').
    intro c. exact (snd (fact_map r r' c) @ ap h' (ptw (ap fst (ptoe_etop E)) c)^).
  Defined.

  (** Exercise [xca:unique-fact-image], second part. *)
  Definition ImFact_isContr : isContr ImFact
    := isProp_inhabited_isContr
         (isProp_Eqv (Eqv_inv ImFact_reorder) ImFact'_isProp) im_fact.

End ImageFactorizationUnique.

(** Exercise [xca:prop-image-is-set]. *)
Definition im_isSet {A B : Type} (f : A -> B) (sB : isSet B) : isSet (im f).
Proof.
  apply IsHSet_isSet. pose proof (isSet_IsHSet sB).
  unfold im, Ex, ptrunc. exact _.
Defined.

(** Exercise [xca:all-prop-image]. *)
Definition all_prop_image {A B : Type} (f : A -> B) (P : B -> Type)
  (hP : forall b, isProp (P b))
  : ((forall z : im f, P (fst z)) -> forall a : A, P (f a))
    × ((forall a : A, P (f a)) -> forall z : im f, P (fst z))
  := (fun h a => h (im_p f a);
      fun k z => ptrunc_rec (hP (fst z))
                   (fun w => trp P (snd w)⁻¹ (k (fst w))) (snd z)).
