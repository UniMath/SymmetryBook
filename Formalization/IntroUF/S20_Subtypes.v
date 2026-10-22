(** * Section 2.20 Predicates and subtypes

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Decidable predicates and characteristic functions; exercise
      [xca:decidability].
    - [Sub(T)], the underlying type [T_P] (written [carrier P]), and
      [lem:subtype-eq-=] (the first projection is an injection; the book
      uses [cor:contract-away], we show directly that its fibers are
      propositions).
    - [lem:Prop-in-Set] ([Prop] is a set), hence [Sub(T)] is a set.
    - Exercise [xca:subtype-univ-prop], via [xca:section-above-f].
    - [Inj(T)] and [lem:Sub(T)=Inj(T)] / exercise [xca:Sub(T)=Inj(T)]:
      [Sub(T) ≃ Inj(T)] for [T : U], by univalence.
    - [cor:subtype-same-level] for propositions and [n]-types, [n ≥ 0].
    - Exercise [xca:subsets-inclusion]: [⊆] is a proposition-valued
      partial order with least and greatest elements.
    - Decidable sets, and Hedberg's theorem (the library's
      [hset_decpaths]). *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S19_Replacement.

Local Open Scope uf_scope.

(** ** 2.20 Predicates and subtypes *)

(** Definition [def:predicate]: a predicate on [T] is a family of
    propositions, i.e. a map [T → Prop]. *)
Definition isDecPred {T : Type} (P : T -> PropU) : Type
  := forall t, isDecidable (fst (P t)).

(** The characteristic function of a decidable predicate. *)
Definition chi {T : Type} {P : T -> PropU} (d : isDecPred P) : T -> Bool
  := fun t => match d t with inl _ => yes | inr _ => no end.

Definition chi_spec {T : Type} {P : T -> PropU} (d : isDecPred P) (t : T)
  : ((chi d t = yes) -> fst (P t)) × (fst (P t) -> chi d t = yes).
Proof.
  unfold chi. destruct (d t) as [p|np].
  - exact ((fun _ => p); (fun _ => refl)).
  - exact ((fun e => match yes_ne_no e⁻¹ with end);
           (fun p => match np p with end)).
Defined.

(** Exercise [xca:decidability]. *)
Definition bool_pred {T : Type} (f : T -> Bool) : T -> PropU
  := fun t => ((f t = yes); isSet_bool _ _).

Definition bool_pred_isDec {T : Type} (f : T -> Bool) : isDecPred (bool_pred f).
Proof.
  intro t. unfold bool_pred; cbn. destruct (f t).
  - exact (inl refl).
  - exact (inr (fun e => yes_ne_no e⁻¹)).
Defined.

Definition dec_prop_True_False {P : Type} (hP : isProp P) (d : isDecidable P)
  : (P ≃ True) ⨿ (P ≃ False)
  := match d with
     | inl p => inl (Eqv_of_props hP True_isProp (fun _ => triv) (fun _ => p))
     | inr np => inr (Eqv_of_props hP False_isProp np
                       (fun x => match x with end))
     end.

(** Definition [def:subtype]: the type of subtypes [Sub(T) :≡ (T → Prop)]
    and the underlying type [T_P :≡ ∑_{t:T} P(t)]. *)
Definition Sub (T : Type) : Type := T -> PropU.

Definition carrier {T : Type} (P : T -> PropU) : Type := {t : T & fst (P t)}.

(** Lemma [lem:subtype-eq-=].  The first projection is an injection: we
    show directly that its fibers are propositions (the book uses
    [cor:contract-away]), and apply [lem:inj-ap]. *)
Definition fst_isInj {T : Type} {Q : T -> Type} (hQ : forall t, isProp (Q t))
  : isInj (@fst T Q).
Proof.
  intros t [[y u] e] [[y' u'] e'].
  change (t = y) in e. change (t = y') in e'.
  destruct e, e'.
  exact (ap (fun u0 => (((t; u0) : {t : T & Q t}); refl) : fiber fst t)
            (hQ t u u')).
Defined.

Definition subtype_paths_eqv {T : Type} {Q : T -> Type}
  (hQ : forall t, isProp (Q t)) (w w' : {t : T & Q t})
  : (w = w') ≃ (fst w = fst w')
  := (ap fst; isInj_ap_isEquiv (fst_isInj hQ) w w').

Definition subtype_eq {T : Type} (P : T -> PropU) (w w' : carrier P)
  : isEquiv (@ap (carrier P) T fst w w')
  := snd (subtype_paths_eqv (fun t => snd (P t)) w w').

(** Remark [rem:subtype-convention]: by [lem:subtype-eq-=] we need not
    distinguish carefully between elements of [T_P] and of [T]
    (informal convention). *)

(** Example [def:Prop-Set]: [Prop_U] and [Set_U] (here [PropU] and [SetU],
    from 2.16 and 2.17) are subtypes of [U]. *)
Definition PropU_paths_eqv `{Funext} (P Q : PropU) : (P = Q) ≃ (fst P = fst Q)
  := subtype_paths_eqv (fun X => isProp_isProp X) P Q.

(** Lemma [lem:Prop-in-Set]. *)
Definition PropU_isSet `{Univalence} : isSet PropU.
Proof.
  intros P Q.
  apply (isProp_Eqv (Eqv_inv (PropU_paths_eqv P Q))).
  apply (isProp_Eqv (Eqv_inv ((@idtoeqv (fst P) (fst Q)); ua (fst P) (fst Q)))).
  exact (Sigma_isProp (fun_isProp (snd Q)) (fun f => isEquiv_isProp f)).
Defined.

(** Hence [Sub(T)] is a set.  Footnote [ft:caution-subtype]: identifying
    subtypes as elements of [Sub(T)] differs from identifying their
    underlying types (informal). *)
Definition Sub_isSet `{Univalence} (T : Type) : isSet (Sub T).
Proof.
  apply IsHSet_isSet. pose proof (isSet_IsHSet PropU_isSet).
  unfold Sub. exact _.
Defined.

(** Exercise [xca:subtype-univ-prop]: the universal property of
    subtypes; footnote [ft:subtype-univ-prop] is the diagram. *)
Definition subtype_univ_prop `{Funext} {T X : Type} (f : X -> T)
  (P : T -> PropU)
  : ((forall x, fst (P (f x))) -> isContr {g : X -> carrier P & f = fst ∘ g})
    × (isContr {g : X -> carrier P & f = fst ∘ g} -> forall x, fst (P (f x)))
  := (fun h => isContr_Eqv (section_above_f (Y := fun t => fst (P t)) f)
                 (isProp_inhabited_isContr
                    (Pi_isProp (fun x => snd (P (f x)))) h);
      fun c => fst (Eqv_inv (section_above_f (Y := fun t => fst (P t)) f))
                 (fst c)).

(** Definition [def:injtype]: the type of injections into [T]. *)
Section SubInj.

  Universe u.
  Context (T : Type@{u}).

  Definition Inj : Type := {S : Type@{u} & {f : S -> T & isInj f}}.

  Definition isInj_isProp `{Funext} {S : Type} (f : S -> T) : isProp (isInj f)
    := Pi_isProp (fun t => isProp_isProp _).

  Definition Sub_to_Inj (P : T -> {X : Type@{u} & isProp X}) : Inj
    := (carrier P; (fst; fst_isInj (fun t => snd (P t)))).

  Definition Inj_to_Sub (w : Inj) : T -> {X : Type@{u} & isProp X}
    := fun t => (fiber (fst (snd w)) t; snd (snd w) t).

  (** Lemma [lem:Sub(T)=Inj(T)] and Exercise [xca:Sub(T)=Inj(T)].
      Footnote [ft:incl-vs-inj]: the full notation of a subtype as an
      element of [Inj(T)] is [Sub_to_Inj]. *)

  Definition Inj_Sub_Inj_carrier (w : Inj)
    : carrier (Inj_to_Sub w) ≃ fst w.
  Proof.
    destruct w as [S [i j]].
    refine (mkEqv (fun v => fst (snd v)) (fun s => (i s; (s; refl))) _ _).
    - intros [t [s e]]. cbn in e |- *.
      revert t e. refine (paths_ind_r _ _ _). exact refl.
    - intro s. exact refl.
  Defined.

  Definition trp_fun_dom {X Y : Type} {Z : Type} (e : X = Y) (g : X -> Z)
    : trp (fun W : Type => W -> Z) e g = g ∘ trp (fun W : Type => W) e⁻¹.
  Proof. destruct e. exact refl. Defined.

  Definition trp_sigma_fst {X Y : Type} {Z : Type}
    (Q : forall W : Type, (W -> Z) -> Type) (e : X = Y)
    (w : {f : X -> Z & Q X f})
    : fst (trp (fun W : Type => {f : W -> Z & Q W f}) e w)
      = trp (fun W : Type => W -> Z) e (fst w).
  Proof. destruct e. exact refl. Defined.

  Definition trp_inv_eqinv {X Y : Type} (e : X = Y) (E : X ≃ Y)
    (h : ptoe e = fst E) (y : Y)
    : trp (fun W : Type => W) e⁻¹ y = eqinv (snd E) y
    := (eqinv_l (snd E) _)^ @ ap (eqinv (snd E)) ((ptw h _)^ @ trp_trp_inv e y).

  Definition Sub_Inj_isEquiv `{Univalence} : isEquiv Sub_to_Inj.
  Proof.
    refine (iso_to_isEquiv Sub_to_Inj Inj_to_Sub _ _).
    - intro P. apply ptw_inv. intro t.
      exact (path_PropU (P := Inj_to_Sub (Sub_to_Inj P) t) (Q := P t)
               (fun w : fiber (@fst T (fun t => fst (P t))) t =>
                  trp (fun t => fst (P t)) (snd w)⁻¹ (snd (fst w)))
               (fun p => (((t; p) : carrier P); refl))).
    - intros [S [i j]].
      pose (E := Inj_Sub_Inj_carrier (S; (i; j))).
      refine (pathpair (etop E) _).
      apply (path_sigma_prop isInj_isProp).
      refine (trp_sigma_fst (fun W f => isInj f) (etop E) _ @ _).
      refine (trp_fun_dom (etop E) fst @ _).
      apply ptw_inv. intro s. cbn.
      refine (ap fst (trp_inv_eqinv (etop E) E (ap fst (ptoe_etop E)) s) @ _).
      pose (v := eqinv (snd E) s).
      exact (snd (snd v) @ ap i (eqinv_r (snd E) s)).
  Defined.

  Definition Sub_Inj_eqv `{Univalence}
    : (T -> {X : Type@{u} & isProp X}) ≃ Inj
    := (Sub_to_Inj; Sub_Inj_isEquiv).

End SubInj.

(** Corollary [cor:subtype-same-level]: for [n ≥ -1], subtypes of
    [n]-types are [n]-types. *)
Definition subtype_paths_Q (Q : Type -> Type)
  (Qinv : forall X Y : Type, X ≃ Y -> Q X -> Q Y)
  {T : Type} {R : T -> Type} (hR : forall t, isProp (R t))
  (h : forall x y : T, Q (x = y))
  : forall w w' : {t : T & R t}, Q (w = w')
  := fun w w' => Qinv _ _ (Eqv_inv (subtype_paths_eqv hR w w')) (h _ _).

Definition subtype_isProp {T : Type} {R : T -> Type}
  (hR : forall t, isProp (R t)) (hT : isProp T) : isProp {t : T & R t}
  := Sigma_isProp hT hR.

Definition subtype_ntype (n : ℕ) {T : Type} {R : T -> Type}
  (hR : forall t, isProp (R t)) (hT : is_ntype n T)
  : is_ntype n {t : T & R t}.
Proof.
  destruct n as [|n].
  - exact (subtype_paths_Q isProp isProp_Qinv hR hT).
  - exact (subtype_paths_Q (is_ntype n) (is_ntype_Qinv n) hR hT).
Defined.

(** Exercise [xca:subsets-inclusion]: inclusion of subtypes is a partial
    order (footnote [ft:partial-order]: reflexive, transitive,
    antisymmetric) with a least and a greatest element. *)
Definition subset_incl {T : Type} (P0 P1 : Sub T) : Type
  := forall t, fst (P0 t) -> fst (P1 t).

Notation "P ⊆ Q" := (subset_incl P Q) : uf_scope.

Section SubsetInclusion.

  Context {T : Type}.

  Definition subset_incl_isProp `{Funext} (P0 P1 : Sub T) : isProp (P0 ⊆ P1)
    := Pi_isProp (fun t => fun_isProp (snd (P1 t))).

  Definition subset_incl_refl (P : Sub T) : P ⊆ P := fun t p => p.

  Definition subset_incl_trans (P0 P1 P2 : Sub T)
    : P0 ⊆ P1 -> P1 ⊆ P2 -> P0 ⊆ P2
    := fun a b t p => b t (a t p).

  Definition subset_incl_antisym `{Univalence} (P0 P1 : Sub T)
    : P0 ⊆ P1 -> P1 ⊆ P0 -> P0 = P1
    := fun a b => ptw_inv (fun t => path_PropU (a t) (b t)).

  Definition empty_sub : Sub T := fun _ => (False; False_isProp).
  Definition full_sub : Sub T := fun _ => (True; True_isProp).

  Definition empty_sub_least (P : Sub T) : empty_sub ⊆ P
    := fun t x => match x with end.

  Definition full_sub_greatest (P : Sub T) : P ⊆ full_sub
    := fun t _ => triv.

End SubsetInclusion.

(** Definition [def:decidable-set]. *)
Definition isDecSet (A : Type) : Type
  := forall x y : A, isProp (x = y) × isDecidable (x = y).

(** Theorem [thm:hedberg]: the library's [hset_decpaths]. *)
Definition hedberg {A : Type} (d : forall x y : A, (x = y) ⨿ ¬ (x = y))
  : isDecSet A
  := fun x y => (IsHSet_isSet (@hset_decpaths A d) x y; d x y).
