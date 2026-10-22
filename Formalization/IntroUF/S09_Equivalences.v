(** * Section 2.9 Equivalences

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Own definitions, since the library's differ: [isContr X :≡
      Σ c, ∏ x, (c = x)] (the library's [Contr] is a class), fibers
      [fiber f y :≡ Σ x, (y = f x)] with the book's convention, [isEquiv f
      :≡ ∏ y, isContr (fiber f y)] and the type [X ≃ Y] of equivalences.
    - [lem:thepathspaceiscontractible], [lem:weq-iso] (the converse, which
      the book cites from the HoTT Book, via Coq-HoTT's
      [isequiv_adjointify]), inverses and composition of equivalences,
      [xca:2-out-of-3], [lem:contract-away] and [cor:contract-away] (the
      footnote's alternative proof is left out).
    - Fiberwise maps [tot := functor_sigma idmap], [lem:fiberwise],
      [xca:fiberwise] and [lem:fiberwise-equiv-from-tot] (Thm 4.7.7 of the
      HoTT Book, via Coq-HoTT's [isequiv_from_functor_sigma]).
    - Function extensionality as the book's principle [funext : isEquiv
      ptw], from Coq-HoTT's axiom [isequiv_apD10], and its inverse
      [ptw⁻¹]; exercise [xca:substitute-away].
    - Exercises [xca:Xequiv1toX], [xca:XequivXtimes1], [xca:AC-in-TT],
      [xca:Sigma-curry], [xca:Sigma-distrib], [xca:Sigma-comm],
      [xca:fib-of-comp], [xca:section-above-f] and [xca:sum-equiv-base];
      the round trips of the Σ-manipulations hold by definition.
      [xca:sum-equiv-base] uses Coq-HoTT's [equiv_functor_sigma_pb],
      because a direct proof needs half-adjoint coherence, which the book
      hasn't introduced yet.
    - Bridges: [tot] is [functor_sigma idmap]; [ptw⁻¹] is
      [path_forall]; [fiber f y ≃ hfiber f y] (the conventions [y = f x]
      and [f x = y] differ by path inversion); [isContr X] versus
      [Contr X]; [Equiv_of_Eqv : (X ≃ Y) → (X <~> Y)]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S08_SumTypes.

Local Open Scope uf_scope.

(** ** 2.9 Equivalences *)

(** Definition [def:contractible]. *)
Definition isContr (X : Type) : Type := {c : X & forall x : X, c = x}.

(** Any element of a contractible type can serve as the center. *)
Definition isContr_center {X : Type} (H : isContr X) (a : X)
  : forall x : X, a = x
  := fun x => snd H x ⋅ (snd H a)⁻¹.

(** Lemma [lem:thepathspaceiscontractible]: singleton types are
    contractible. *)
Definition singleton_contr {X : Type} (a : X) : isContr {x : X & a = x}.
Proof.
  exists (a; refl).
  intros [x i]. destruct i. exact refl.
Defined.

(** Definition [def:fiber], with the convention [y = f x]. *)
Definition fiber {X Y : Type} (f : X -> Y) (y : Y) : Type
  := {x : X & y = f x}.

(** Definition [def:equivalence]. *)
Definition isEquiv {X Y : Type} (f : X -> Y) : Type
  := forall y : Y, isContr (fiber f y).

(** Definition [def:type-of-equivalences]. *)
Definition Eqv (X Y : Type) : Type := {f : X -> Y & isEquiv f}.

Notation "X ≃ Y" := (Eqv X Y) (at level 85) : uf_scope.

(** The inverse of an equivalence: [g(y) :≡ fst(fst(t(y)))]. *)
Section Inverse.

  Context {X Y : Type} {f : X -> Y} (t : isEquiv f).

  Definition eqinv : Y -> X := fun y => fst (fst (t y)).

  Definition eqinv_r (y : Y) : f (eqinv y) = y := (snd (fst (t y)))⁻¹.

  Definition eqinv_l (x : X) : eqinv (f x) = x
    := ap fst (snd (t (f x)) (x; refl)).

End Inverse.

(** The identity function is an equivalence: its fibers are singletons
    (by definition, thanks to the convention [y = f x]). *)
Definition id_isEquiv (X : Type) : isEquiv (id X) := fun a => singleton_contr a.

(** Transport is an equivalence. *)
Definition trp_isEquiv {X : Type} (T : X -> Type) {x y : X} (e : x = y)
  : isEquiv (trp T e)
  := match e with refl => id_isEquiv (T x) end.

(** *** Bridge to Coq-HoTT's [IsEquiv] *)

(** Contractibility is preserved by retracts. *)
Definition isContr_retract {A B : Type} (r : A -> B) (s : B -> A)
  (rs : forall b, r (s b) = b) : isContr A -> isContr B.
Proof.
  intros [c h]. exists (r c).
  intro b. exact (rs b ⋅ ap r (h (s b))).
Defined.

Definition isEquiv_of_IsEquiv {X Y : Type} (f : X -> Y) `{IsEquiv X Y f}
  : isEquiv f.
Proof.
  intro y.
  refine (isContr_retract (A := hfiber f y) (B := fiber f y)
            (fun w => (fst w; (snd w)^)) (fun w => (fst w; (snd w)^)) _ _).
  - intros [x p]. cbn. exact (ap (fun q => (x; q)) (inv_V p)).
  - exact (center (hfiber f y); contr).
Defined.

Definition IsEquiv_of_isEquiv {X Y : Type} {f : X -> Y} (t : isEquiv f)
  : IsEquiv f
  := isequiv_adjointify f (eqinv t) (eqinv_r t) (eqinv_l t).

(** Construction [lem:weq-iso].
    (Placed before [xca:equivalence-invers], which uses it.) *)
Definition isEquiv_to_iso {X Y : Type} {f : X -> Y} (t : isEquiv f)
  : {g : Y -> X & (forall x, g (f x) = x) * (forall y, f (g y) = y)}
  := (eqinv t; (eqinv_l t, eqinv_r t)).

Definition iso_to_isEquiv {X Y : Type} (f : X -> Y) (g : Y -> X)
  (gf : forall x, g (f x) = x) (fg : forall y, f (g y) = y) : isEquiv f
  := isEquiv_of_IsEquiv f (H := isequiv_adjointify f g fg gf).

Definition mkEqv {X Y : Type} (f : X -> Y) (g : Y -> X)
  (gf : forall x, g (f x) = x) (fg : forall y, f (g y) = y) : X ≃ Y
  := (f; iso_to_isEquiv f g gf fg).

Definition Eqv_of_Equiv {X Y : Type} (e : X <~> Y) : X ≃ Y
  := (equiv_fun e; isEquiv_of_IsEquiv e).

(** Exercise [xca:equivalence-invers]. *)
Definition eqinv_isEquiv {X Y : Type} {f : X -> Y} (t : isEquiv f)
  : isEquiv (eqinv t)
  := iso_to_isEquiv (eqinv t) f (eqinv_r t) (eqinv_l t).

Definition Eqv_inv {X Y : Type} : (X ≃ Y) -> (Y ≃ X)
  := fun e => (eqinv (snd e); eqinv_isEquiv (snd e)).

(** Exercise [xca:equivalence-comp]. *)
Definition comp_isEquiv {X Y Z : Type} {f : X -> Y} {g : Y -> Z}
  (s : isEquiv f) (t : isEquiv g) : isEquiv (comp g f).
Proof.
  refine (iso_to_isEquiv _ (comp (eqinv s) (eqinv t)) _ _); intro; unfold comp.
  - exact (ap (eqinv s) (eqinv_l t _) @ eqinv_l s _).
  - exact (ap g (eqinv_r s _) @ eqinv_r t _).
Defined.

Definition Eqv_comp {X Y Z : Type} : (X ≃ Y) -> ((Y ≃ Z) -> (X ≃ Z))
  := fun e e' => (comp (fst e') (fst e); comp_isEquiv (snd e) (snd e')).

(** Exercise [xca:2-out-of-3], with [e : hf = g]. *)
Section TwoOutOfThree.

  Context {A B C : Type} (f : A -> B) (g : A -> C) (h : B -> C)
    (e : comp h f = g).

  Let E (a : A) : h (f a) = g a := ptw e a.

  Definition two_of_three_g (sf : isEquiv f) (sh : isEquiv h) : isEquiv g.
  Proof.
    refine (iso_to_isEquiv g (comp (eqinv sf) (eqinv sh)) _ _); intro; unfold comp.
    - exact (ap (fun c => eqinv sf (eqinv sh c)) (E _)^
               @ ap (eqinv sf) (eqinv_l sh _) @ eqinv_l sf _).
    - exact ((E _)^ @ ap h (eqinv_r sf _) @ eqinv_r sh _).
  Defined.

  Definition two_of_three_h (sf : isEquiv f) (sg : isEquiv g) : isEquiv h.
  Proof.
    refine (iso_to_isEquiv h (comp f (eqinv sg)) _ _); intro b; unfold comp.
    - exact (ap (fun c => f (eqinv sg c))
               (ap h (eqinv_r sf b)^ @ E (eqinv sf b))
             @ ap f (eqinv_l sg _) @ eqinv_r sf b).
    - exact (E _ @ eqinv_r sg b).
  Defined.

  Definition two_of_three_f (sg : isEquiv g) (sh : isEquiv h) : isEquiv f.
  Proof.
    refine (iso_to_isEquiv f (comp (eqinv sg) h) _ _); intro b; unfold comp.
    - exact (ap (eqinv sg) (E b) @ eqinv_l sg b).
    - exact ((eqinv_l sh _)^
             @ ap (eqinv sh) (E _ @ eqinv_r sg (h b)) @ eqinv_l sh b).
  Defined.

End TwoOutOfThree.

(** Lemma [lem:contract-away]. *)
Section ContractAway.

  Context {X : Type} (a : X) (B : forall x, a = x -> Type).

  Definition ca_map : {x : X & {i : a = x & B x i}} -> B a refl
    := fun w => path_ind a (fun x i => B x i -> B a refl) (id _)
                  (fst w) (fst (snd w)) (snd (snd w)).

  Definition ca_map_isEquiv : isEquiv ca_map.
  Proof.
    refine (iso_to_isEquiv ca_map (fun b => (a; refl; b)) _ _).
    - intros [x [i b]]. destruct i. exact refl.
    - intro b. exact refl.
  Defined.

End ContractAway.

(** Footnote [ft:Sigma-assoc]: associativity of sum types. *)
Definition sigma_assoc (X : Type) (Y : X -> Type)
  (Z : forall x, Y x -> Type)
  : {x : X & {y : Y x & Z x y}} ≃ {w : {x : X & Y x} & Z (fst w) (snd w)}
  := mkEqv (fun w : {x : X & {y : Y x & Z x y}} =>
              ((fst w; fst (snd w)) : {x : X & Y x}; snd (snd w)))
           (fun w : {w : {x : X & Y x} & Z (fst w) (snd w)} =>
              (fst (fst w); snd (fst w); snd w))
           (fun _ => refl) (fun _ => refl).

(** Corollary [cor:contract-away]; here [(a = x) × B(x)] is the sum over
    a constant family, see 2.11. *)
Definition contract_away {X : Type} (a : X) (B : X -> Type)
  : {x : X & {_ : a = x & B x}} ≃ B a
  := (ca_map a (fun x _ => B x); ca_map_isEquiv a (fun x _ => B x)).

(** Exercise [xca:sum-equiv-base]. *)
Definition sum_equiv_base {X Y : Type} {f : X -> Y} (t : isEquiv f)
  (B : X -> Type) : {x : X & B x} ≃ {y : Y & B (eqinv t y)}
  := Eqv_of_Equiv (equiv_inverse
       (equiv_functor_sigma_pb (Q := B)
          (Build_Equiv _ _ (eqinv t) (IsEquiv_of_isEquiv (eqinv_isEquiv t))))).

(** Definition [def:fiberwise]: totalization of a map of families,
    [tot(f)(x,y) :≡ (x, f(x)(y))]: the library's [functor_sigma idmap]. *)
Definition tot {X : Type} {Y Z : X -> Type} (f : forall x, Y x -> Z x)
  : Tot Y -> Tot Z
  := functor_sigma idmap f.

Definition tot_pair {X : Type} {Y Z : X -> Type} (f : forall x, Y x -> Z x)
  (x : X) (y : Y x) : tot f (x; y) = (x; f x y) := refl.

(** Lemma [lem:fiberwise] and Exercise [xca:fiberwise]. *)
Definition tot_isEquiv {X : Type} {Y Z : X -> Type} (f : forall x, Y x -> Z x)
  (t : forall x, isEquiv (f x)) : isEquiv (tot f).
Proof.
  refine (iso_to_isEquiv (tot f) (tot (fun x => eqinv (t x))) _ _).
  - intros [x y]. exact (ap (fun y' => (x; y')) (eqinv_l (t x) y)).
  - intros [x z]. exact (ap (fun z' => (x; z')) (eqinv_r (t x) z)).
Defined.

(** Lemma [lem:fiberwise-equiv-from-tot] (Theorem 4.7.7 of the HoTT Book). *)
Definition isEquiv_from_tot {X : Type} {Y Z : X -> Type}
  (f : forall x, Y x -> Z x) (t : isEquiv (tot f)) : forall x, isEquiv (f x)
  := fun x => isEquiv_of_IsEquiv (f x)
       (H := @isequiv_from_functor_sigma X Y Z f (IsEquiv_of_isEquiv t) x).

(** Principle [def:funext]: function extensionality postulates
    [funext : isEquiv(ptw_{f,g})].  Since [ptw] is [apD10], this follows
    from Coq-HoTT's axiom [isequiv_apD10], available under [Funext]. *)
Definition funext `{Funext} {X : Type} {Y : X -> Type} (f g : forall x, Y x)
  : isEquiv (@ptw X Y f g)
  := isEquiv_of_IsEquiv ptw (H := isequiv_apD10 X Y f g).

(** The inverse [ptw⁻¹] given by [funext]. *)

Definition ptw_inv `{Funext} {X : Type} {Y : X -> Type} {f g : forall x, Y x}
  : (forall x, f x = g x) -> f = g
  := eqinv (funext f g).

(** Exercise [xca:substitute-away].
    (Placed after [def:funext], which it uses.) *)
Definition substitute_away `{Funext} {X : Type} (a : X) (B : X -> Type)
  : (forall x, a = x -> B x) ≃ B a.
Proof.
  refine (mkEqv (fun h => h a refl) (fun b x i => trp B i b) _ _).
  - intro h. apply ptw_inv; intro x. apply ptw_inv; intro i.
    destruct i. exact refl.
  - intro b. exact refl.
Defined.

(** Exercise [xca:Xequiv1toX]. *)
Definition True_to_X_eqv `{Funext} (X : Type) : (True -> X) ≃ X.
Proof.
  refine (mkEqv (fun f => f triv) (fun x => cst x) _ _).
  - intro f. apply ptw_inv. intros []. exact refl.
  - intro x. exact refl.
Defined.

(** Exercise [xca:XequivXtimes1]. *)
Definition sum_True_eqv (X : Type) : {_ : X & True} ≃ X.
Proof.
  refine (mkEqv fst (fun x => (x; triv)) _ _).
  - intros [x []]. exact refl.
  - intro x. exact refl.
Defined.

(** Exercise [xca:Sigma-distrib]. *)
Definition sigma_distrib (X Y : Type) (Z : Y -> Type)
  : {_ : X & {y : Y & Z y}} ≃ {y : Y & {_ : X & Z y}}
  := mkEqv (fun w : {_ : X & {y : Y & Z y}} => (fst (snd w); fst w; snd (snd w)))
           (fun w : {y : Y & {_ : X & Z y}} => (fst (snd w); fst w; snd (snd w)))
           (fun _ => refl) (fun _ => refl).

(** Exercise [xca:Sigma-comm]. *)
Definition sigma_comm (X Y : Type) (Z : X -> Y -> Type)
  : {x : X & {y : Y & Z x y}} ≃ {y : Y & {x : X & Z x y}}
  := mkEqv (fun w : {x : X & {y : Y & Z x y}} => (fst (snd w); fst w; snd (snd w)))
           (fun w : {y : Y & {x : X & Z x y}} => (fst (snd w); fst w; snd (snd w)))
           (fun _ => refl) (fun _ => refl).

(** Exercise [xca:fib-of-comp]. *)
Definition fib_of_comp {X Y Z : Type} (f : X -> Y) (g : Y -> Z) (z : Z)
  : fiber (comp g f) z ≃ {w : fiber g z & fiber f (fst w)}.
Proof.
  refine (mkEqv (fun v : fiber (comp g f) z =>
                   ((f (fst v); snd v) : fiber g z; (fst v; refl) : fiber f _))
                (fun w : {w : fiber g z & fiber f (fst w)} =>
                   (fst (snd w); ap g (snd (snd w)) ⋅ snd (fst w)))
                (fun _ => refl) _).
  intros [[y p] [x q]]. cbn in *.
  revert y q p. refine (paths_ind_r _ _ _). intro p. exact refl.
Defined.

(** Exercise [xca:AC-in-TT]: holds with round trips by definition. *)
Definition type_theoretic_AC (X Y : Type) (Z : X -> Y -> Type)
  : (forall x, {y : Y & Z x y}) ≃ {f : X -> Y & forall x, Z x (f x)}
  := mkEqv (fun h : forall x, {y : Y & Z x y} =>
              ((fun x => fst (h x)); (fun x => snd (h x)))
              : {f : X -> Y & forall x, Z x (f x)})
           (fun w : {f : X -> Y & forall x, Z x (f x)} =>
              fun x => (fst w x; snd w x) : {y : Y & Z x y})
           (fun _ => refl) (fun _ => refl).

(** Exercise [xca:section-above-f]. *)
Section SectionAboveF.

  Context {X Z : Type} {Y : X -> Type} (f : Z -> X).

  Let fwd (s : forall z, Y (f z))
    : {g : Z -> {x : X & Y x} & f = comp fst g}
    := ((fun z => (f z; s z)); refl).

  Let bwd (w : {g : Z -> {x : X & Y x} & f = comp fst g})
    : forall z, Y (f z)
    := fun z => trp Y (ptw (snd w) z)⁻¹ (snd (fst w z)).

  Local Definition fwd_bwd_gen (g1 : Z -> X) (g2 : forall z, Y (g1 z))
    (e : f = g1)
    : fwd (bwd ((fun z => (g1 z; g2 z)); e)) = ((fun z => (g1 z; g2 z)); e).
  Proof. destruct e. exact refl. Defined.

  Definition section_above_f
    : (forall z, Y (f z)) ≃ {g : Z -> {x : X & Y x} & f = comp fst g}.
  Proof.
    refine (mkEqv fwd bwd (fun _ => refl) _).
    intros [g e]. exact (fwd_bwd_gen (comp fst g) (fun z => snd (g z)) e).
  Defined.

End SectionAboveF.

(** Exercise [xca:Sigma-curry]. *)
Definition sigma_curry (X Z : Type) (Y : X -> Type)
  : ({x : X & Y x} -> Z) ≃ (forall x, Y x -> Z)
  := mkEqv (fun (h : {x : X & Y x} -> Z) x y => h (x; y))
           (fun (k : forall x, Y x -> Z) (w : {x : X & Y x}) => k (fst w) (snd w))
           (fun _ => refl) (fun _ => refl).

(** *** Bridges to Coq-HoTT *)

Definition tot_is_functor_sigma {X : Type} {Y Z : X -> Type}
  (f : forall x, Y x -> Z x) : tot f = functor_sigma idmap f := refl.

Definition ptw_inv_is_path_forall `{Funext} {X : Type} {Y : X -> Type}
  {f g : forall x, Y x} (h : forall x, f x = g x)
  : ptw_inv h = path_forall f g h
  := ap (eqinv (funext f g)) (eisretr apD10 h)^
     @ eqinv_l (funext f g) (path_forall f g h).

Definition fiber_hfiber {X Y : Type} (f : X -> Y) (y : Y)
  : fiber f y ≃ hfiber f y
  := mkEqv (fun w : fiber f y => (fst w; (snd w)^) : hfiber f y)
           (fun w : hfiber f y => (pr1 w; (pr2 w)^) : fiber f y)
           (fun w => ap (fun r => (fst w; r) : fiber f y) (inv_V (snd w)))
           (fun w => ap (fun r => (pr1 w; r) : hfiber f y) (inv_V (pr2 w))).

Definition Contr_of_isContr {X : Type} (h : isContr X) : Contr X
  := Build_Contr X (fst h) (snd h).

Definition isContr_of_Contr {X : Type} `{Contr X} : isContr X
  := (center X; contr).

Definition Equiv_of_Eqv {X Y : Type} (e : X ≃ Y) : X <~> Y
  := Build_Equiv X Y (fst e) (IsEquiv_of_isEquiv (snd e)).

Definition Equiv_of_Eqv_fun {X Y : Type} (e : X ≃ Y)
  : equiv_fun (Equiv_of_Eqv e) = fst e := refl.
