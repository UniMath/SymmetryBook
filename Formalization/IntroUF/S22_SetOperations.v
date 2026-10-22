(** * Section 2.22 Operations that produce sets

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - [lem:Set-is-groupoid]: equivalences and identifications between
      propositions (sets) form propositions (sets); [Set] is a groupoid.
    - [thm:isset-inductive-types] for lists, following Simon Huber's
      method as in the book, and exercise [xca:set-sum] (binary sums).
      The other inductive types of 2.12 are left to the reader in the
      book; [ℕ] is shown to be a set in 2.23 via Hedberg's theorem.
    - Set truncation [‖T‖₀ :≡ strunc T :≡ Trunc 0 T] with [|t|₀ :≡ tr t]
      (its induction principle computes by definition): induction and
      recursion principles and the universal property; exercise
      [xca:sum-of-conn-components] (components [A_(z)] for [z : ‖A‖₀] with
      [A_(|a|₀) ≡ A_(a)], [A ≃ ∑_z A_(z)], and [A] connected iff [‖A‖₀]
      contractible, using the library's [equiv_path_Tr]); exercise
      [xca:subset-of-set-trunc].
    - Weakly constant maps and [thm:wconstant-elim], via the image.
    - Set quotients: the book's [A/R] as the image of
      [R : A → (A → Prop)] ([quot], with classes [cls]);
      [lem:equiv-class-prop], [thm:quotient-property] (both parts, with
      [f̄([x]) ≡ f(x)]), exercise [xca:A/True-prop-trunc]; the quotient as
      a higher inductive type ([def:quotient-as-HIT]) is the library's
      [Quotient] ([QuotHIT]), and exercise [xca:quotients-equivalence]
      gives [A/R ≃ QuotHIT]; remark [rem:set-trunc-as-quotient]; exercise
      [xca:map-induces-quotient] (the unique equivalence
      [e_f : A/≡_f ≃ ‖im(f)‖₀]).
    - Exercise [xca:ints-as-quotient] is in 2.23, since it uses the
      results on [ℕ] there. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S21_PointedTypes.

Local Open Scope uf_scope.

(** ** Preliminaries *)

Definition Pi_isSet `{Funext} {A : Type} {B : A -> Type}
  (h : forall a, isSet (B a)) : isSet (forall a, B a).
Proof.
  apply IsHSet_isSet. pose proof (fun a => isSet_IsHSet (h a)). exact _.
Defined.

Definition Sigma_isSet {A : Type} {B : A -> Type} (sA : isSet A)
  (sB : forall a, isSet (B a)) : isSet {a : A & B a}.
Proof.
  apply IsHSet_isSet. pose proof (isSet_IsHSet sA).
  pose proof (fun a => isSet_IsHSet (sB a)). exact _.
Defined.

(** Every type is equivalent to the sum of the fibers of a map into it. *)
Definition total_fibers {X Y : Type} (f : X -> Y) : X ≃ {y : Y & fiber f y}.
Proof.
  refine (mkEqv (fun x => (f x; (x; refl)))
                (fun w => fst (snd w)) (fun x => refl) _).
  intros [y [x p]]. cbn in p |- *.
  revert y p. refine (paths_ind_r _ _ _). exact refl.
Defined.

(** Induction on the image, for families of propositions. *)
Definition im_ind {A B : Type} (f : A -> B) (Q : im f -> Type)
  (hQ : forall z, isProp (Q z)) (g : forall a, Q (im_p f a)) : forall z, Q z.
Proof.
  intros [y u]. revert u.
  refine (ptrunc_ind (fun u => Q (y; u)) (fun _ => hQ _) _).
  intros [a e]. revert y e. refine (paths_ind_r _ _ _). exact (g a).
Defined.

(** ** 2.22 Operations that produce sets *)

(** Lemma [lem:Set-is-groupoid]. *)
Definition Eqv_props_isProp `{Funext} {X Y : Type} (hY : isProp Y)
  : isProp (X ≃ Y)
  := Sigma_isProp (fun_isProp hY) (fun f => isEquiv_isProp f).

Definition paths_props_isProp `{Univalence} {X Y : Type} (hY : isProp Y)
  : isProp (X = Y)
  := isProp_Eqv (Eqv_inv (idtoeqv; ua X Y)) (Eqv_props_isProp hY).

Definition Eqv_sets_isSet `{Funext} {X Y : Type} (sY : isSet Y)
  : isSet (X ≃ Y)
  := subtype_ntype 0 (fun f => isEquiv_isProp f) (Pi_isSet (fun _ => sY)).

Definition paths_sets_isSet `{Univalence} {X Y : Type} (sY : isSet Y)
  : isSet (X = Y)
  := is_ntype_Eqv 0 (Eqv_inv (idtoeqv; ua X Y)) (Eqv_sets_isSet sY).

(** [Prop] is a set ([PropU_isSet] in 2.20) and [Set] is a
    groupoid. *)
Definition SetU_isGrpd `{Univalence} : isGrpd SetU
  := fun S T => is_ntype_Eqv 0
       (Eqv_inv (subtype_paths_eqv (fun X => isSet_isProp X) S T))
       (paths_sets_isSet (snd T)).

(** Theorem [thm:isset-inductive-types], for lists, following Simon
    Huber's method as in the book.  For a function of two non-dependent
    arguments the book's [apap] is the library's [ap011]. *)
Section ListsAreSets.

  Context {X : Type}.

  Definition T_list (l l' : X^*) : l = l' -> Type
    := match l as l0, l' as l0' return l0 = l0' -> Type with
       | nil, nil => fun p => p = refl
       | cons x l, cons x' l' =>
           fun p => {q : x = x' & {r : l = l' & p = ap011 cons q r}}
       | _, _ => fun _ => False
       end.

  Definition T_list_all (l l' : X^*) (p : l = l') : T_list l l' p.
  Proof.
    destruct p, l.
    - exact refl.
    - exact (refl; (refl; refl)).
  Defined.

  Definition list_loops (sX : isSet X) : forall (l : X^*) (p : l = l), p = refl.
  Proof.
    intro l. induction l as [|x l IH]; intro p.
    - exact (T_list_all _ _ p).
    - destruct (T_list_all _ _ p) as [q [r s]].
      exact (s @ ap011 (ap011 cons) (sX x x q refl) (IH r)).
  Defined.

  Definition list_isSet (sX : isSet X) : isSet (X^*).
  Proof. intros l l' p q. destruct q. exact (list_loops sX l p). Defined.

End ListsAreSets.

(** Exercise [xca:set-sum]. *)
Definition sum_isSet {X Y : Type} (sX : isSet X) (sY : isSet Y)
  : isSet (X ⨿ Y).
Proof.
  intros [x|y] [x'|y'].
  - exact (isProp_Eqv (Eqv_inv (path_inl_eqv x x')) (sX x x')).
  - intros p. destruct (inl_ne_inr x y' p).
  - intros p. destruct (encode_inr (X := X) p).
  - exact (isProp_Eqv (Eqv_inv (path_inr_eqv y y')) (sY y y')).
Defined.

(** Definition [def:set-truncation]: the set truncation [‖T‖₀] is the
    library's [Trunc 0 T], with element constructor [|t|₀ :≡ tr t].  Its
    induction principle satisfies [f(|t|₀) ≡ g(t)] by definition. *)
Definition strunc (T : Type) : Type := Trunc 0 T.

Definition settrunc {T : Type} : T -> strunc T := tr.

Definition strunc_isSet {T : Type} : isSet (strunc T)
  := @IsHSet_isSet _ (istrunc_truncation 0 T).

Definition strunc_ind {T : Type} (S : strunc T -> Type)
  (hS : forall x, isSet (S x)) (g : forall t, S (settrunc t))
  : forall x, S x
  := Trunc_ind S (Pt := fun x => isSet_IsHSet (hS x)) g.

Definition strunc_ind_trunc {T : Type} (S : strunc T -> Type) hS g (t : T)
  : strunc_ind S hS g (settrunc t) = g t := refl.

Definition strunc_rec {T S : Type} (hS : isSet S) (g : T -> S)
  : strunc T -> S
  := strunc_ind (fun _ => S) (fun _ => hS) g.

(** Induction into a family of propositions. *)
Definition strunc_ind_prop {T : Type} (S : strunc T -> Type)
  (hS : forall x, isProp (S x)) (g : forall t, S (settrunc t))
  : forall x, S x
  := strunc_ind S (fun x => prop_is_set (hS x)) g.

(** The universal property of set truncation. *)
Definition strunc_univ_prop `{Funext} (T : Type) {S : Type} (hS : isSet S)
  : (strunc T -> S) ≃ (T -> S)
  := mkEqv (fun h => h ∘ settrunc) (strunc_rec hS)
       (fun h => ptw_inv (strunc_ind_prop
                            (fun x => strunc_rec hS (h ∘ settrunc) x = h x)
                            (fun x => hS _ _) (fun t => refl)))
       (fun g => refl).

(** Exercise [xca:sum-of-conn-components]. *)
Section SumOfComponents.

  Context `{Univalence} {A : Type}.

  Definition strunc_component_pred : strunc A -> A -> PropU
    := strunc_rec (Pi_isSet (fun _ => PropU_isSet))
         (fun a x => ptrunc_PropU (a = x)).

  (** The connected component [A_(z)] for [z : ‖A‖₀]. *)
  Definition component_z (z : strunc A) : Type
    := {x : A & fst (strunc_component_pred z x)}.

  Definition component_z_trunc (a : A)
    : component_z (settrunc a) = component A a := refl.

  Definition component_z_iff (z : strunc A) (x : A)
    : ((z = settrunc x) -> fst (strunc_component_pred z x))
      × (fst (strunc_component_pred z x) -> z = settrunc x).
  Proof.
    revert z.
    refine (strunc_ind_prop _ (fun z => prod_isProp
              (fun_isProp (snd (strunc_component_pred z x)))
              (fun_isProp (strunc_isSet _ _))) _).
    intro a. cbn.
    exact ((fun e => equiv_inverse (equiv_path_Tr (n := -1) a x) e);
           ptrunc_rec (strunc_isSet _ _) (ap settrunc)).
  Defined.

  Definition sum_of_components : A ≃ {z : strunc A & component_z z}.
  Proof.
    refine (Eqv_comp (total_fibers settrunc) _).
    pose (F := fun z x => Eqv_of_props (strunc_isSet z (settrunc x))
                            (snd (strunc_component_pred z x))
                            (fst (component_z_iff z x)) (snd (component_z_iff z x))).
    pose (Fz := fun z => (tot (fun x => fst (F z x)) ;
                          tot_isEquiv _ (fun x => snd (F z x)))
                         : fiber settrunc z ≃ component_z z).
    exact (tot (fun z => fst (Fz z)); tot_isEquiv _ (fun z => snd (Fz z))).
  Defined.

  Definition isConn_strunc_isContr (c : isConn A) : isContr (strunc A).
  Proof.
    refine (ptrunc_rec (isContr_isProp _) _ (fst c)). intro a.
    refine (settrunc a; _).
    refine (strunc_ind_prop _ (fun z => strunc_isSet _ _) _). intro x.
    exact (ptrunc_rec (strunc_isSet _ _) (ap settrunc) (snd c a x)).
  Defined.

  Definition strunc_isContr_isConn (c : isContr (strunc A)) : isConn A.
  Proof.
    refine (strunc_ind_prop (fun _ => ptrunc A) (fun _ => ptrunc_isProp)
              trunc (fst c); _).
    intros x y.
    exact (equiv_inverse (equiv_path_Tr (n := -1) x y)
             (isContr_isProp' c (settrunc x) (settrunc y))).
  Defined.

End SumOfComponents.

(** Exercise [xca:subset-of-set-trunc]. *)
Definition subset_of_strunc `{Funext} {A : Type} (P : strunc A -> PropU)
  : strunc {a : A & fst (P (settrunc a))} ≃ {b : strunc A & fst (P b)}.
Proof.
  pose (sS := Sigma_isSet strunc_isSet (fun b => prop_is_set (snd (P b)))).
  pose (e := strunc_rec sS (fun w : {a : A & fst (P (settrunc a))} =>
                              (settrunc (fst w); snd w) : {b : strunc A & fst (P b)})).
  pose (inv := fun w : {b : strunc A & fst (P b)} =>
                 strunc_ind (fun b => fst (P b) -> strunc {a : A & fst (P (settrunc a))})
                   (fun b => Pi_isSet (fun _ => strunc_isSet))
                   (fun a p => settrunc ((a; p) : {a : A & fst (P (settrunc a))}))
                   (fst w) (snd w)).
  refine (mkEqv e inv _ _).
  - refine (strunc_ind_prop _ (fun w => strunc_isSet _ _) _). intro w. exact refl.
  - intros [b p]. revert b p.
    refine (strunc_ind_prop (fun b => forall p, e (inv (b; p)) = (b; p))
              (fun b => Pi_isProp (fun p => sS _ _)) _).
    intros a p. exact refl.
Defined.

(** *** Weakly constant maps *)

Definition wconst {A B : Type} (f : A -> B) : Type
  := forall x x' : A, f x = f x'.

Definition wconst_isProp `{Funext} {A B : Type} (sB : isSet B) (f : A -> B)
  : isProp (wconst f)
  := Pi_isProp (fun x => Pi_isProp (fun x' => sB _ _)).

(** The image of a weakly constant map into a set is a proposition. *)
Definition im_isProp_wconst {A B : Type} {f : A -> B} (sB : isSet B)
  (c : wconst f) : isProp (im f).
Proof.
  intros [y1 z1] [y2 z2].
  pose (sI := im_isSet f sB).
  revert z1. refine (ptrunc_ind _ (fun _ => sI _ _) _). intros [x1 e1].
  revert z2. refine (ptrunc_ind _ (fun _ => sI _ _) _). intros [x2 e2].
  exact (path_sigma_prop (u := (y1; trunc (x1; e1)) : im f)
           (v := (y2; trunc (x2; e2)) : im f)
           (fun _ => ptrunc_isProp) (e2⁻¹ ⋅ (c x1 x2 ⋅ e1))).
Defined.

(** Theorem [thm:wconstant-elim]. *)
Definition wconst_elim {A B : Type} {f : A -> B} (sB : isSet B)
  (c : wconst f) : ptrunc A -> B
  := im_i f ∘ ptrunc_rec (im_isProp_wconst sB c) (im_p f).

Definition wconst_elim_trunc {A B : Type} {f : A -> B} (sB : isSet B)
  (c : wconst f) (x : A) : wconst_elim sB c (trunc x) = f x := refl.

(** *** Set quotients

    Footnote [ft:equiv-rel]: an equivalence relation is reflexive,
    symmetric and transitive ([rr], [rs], [rt] below). *)

Section Quotients.

  Context `{Univalence} {A : Type} (R : A -> A -> PropU)
    (rr : forall x, fst (R x x))
    (rs : forall x y, fst (R x y) -> fst (R y x))
    (rt : forall x y z, fst (R x y) -> fst (R y z) -> fst (R x z)).

  (** Definition [def:quotient-set]: [A/R] is the image of
      [R : A → (A → Prop)], with equivalence predicates [[a]]. *)
  Definition quot : Type := im R.

  Definition quot_isSet : isSet quot
    := im_isSet R (Pi_isSet (fun _ => PropU_isSet)).

  Definition cls (a : A) : quot := im_p R a.

  Definition cls_def (a : A) : cls a = (R a; trunc (a; refl)) := refl.

  (** Lemma [lem:equiv-class-prop]. *)
  Definition equiv_class_prop (P : quot) (a : A)
    : ((P = cls a) -> fst (fst P a)) × (fst (fst P a) -> P = cls a).
  Proof.
    refine ((fun e : P = cls a => trp (fun Q : quot => fst (fst Q a)) e⁻¹ (rr a)); _).
    intro h.
    pose (C := fun Q : quot => fst (fst Q a) -> forall x,
                 (fst (fst Q x) -> fst (R a x)) × (fst (R a x) -> fst (fst Q x))).
    assert (c' : forall Q, C Q).
    { refine (im_ind R C _ _).
      - intro Q. apply Pi_isProp. intro. apply Pi_isProp. intro x.
        exact (prod_isProp (fun_isProp (snd (R a x))) (fun_isProp (snd (fst Q x)))).
      - intros b hb x.
        exact ((fun rbx => rt a b x (rs b a hb) rbx);
               (fun rax => rt b a x hb rax)). }
    pose (c := c' P h).
    apply (path_sigma_prop (fun _ => ptrunc_isProp)).
    apply ptw_inv. intro x.
    exact (path_PropU (fst (c x)) (snd (c x))).
  Defined.

  (** Theorem [thm:quotient-property], first part. *)
  Definition cls_eq_iff (x x' : A)
    : ((cls x = cls x') -> fst (R x x')) × (fst (R x x') -> cls x = cls x')
    := equiv_class_prop (cls x) x'.

  (** Theorem [thm:quotient-property], second part (the universal
      property), with center [f̄] satisfying [f̄([x]) ≡ f(x)]. *)
  Section UniversalProperty.

    Context {B : Type} (sB : isSet B) (f : A -> B)
      (fr : forall x x', fst (R x x') -> f x = f x').

    Definition quot_wconst (z : quot)
      : wconst (fun w : {x : A & fst z = R x} => f (fst w)).
    Proof.
      intros [x e] [x' e']. apply fr.
      exact (trp (fun S : A -> PropU => fst (S x')) (e' ⋅ e⁻¹)⁻¹ (rr x')).
    Defined.

    Definition fbar : quot -> B
      := fun z => wconst_elim sB (quot_wconst z) (snd z).

    Definition fbar_cls (x : A) : fbar (cls x) = f x := refl.

    Definition quot_univ_prop : isContr {g : quot -> B & f = g ∘ cls}.
    Proof.
      refine ((fbar; refl); _).
      intros [g e].
      refine (pathpair (ptw_inv (im_ind R (fun z => fbar z = g z)
                                    (fun z => sB _ _) (fun x => ptw e x))) _).
      exact (Pi_isSet (fun _ => sB) _ _ _ _).
    Defined.

  End UniversalProperty.

End Quotients.

(** Exercise [xca:A/True-prop-trunc]. *)
Section QuotientByTrue.

  Context `{Univalence} (A : Type).

  Let R : A -> A -> PropU := fun _ _ => (True; True_isProp).

  Definition quot_True_isProp : isProp (quot R).
  Proof.
    intros z. revert z.
    refine (im_ind R _ (fun z => Pi_isProp (fun z' => quot_isSet R _ _)) _).
    intro x.
    refine (im_ind R _ (fun z' => quot_isSet R _ _) _). intro x'.
    exact (snd (cls_eq_iff R (fun _ => triv) (fun _ _ _ => triv)
                  (fun _ _ _ _ _ => triv) x x') triv).
  Defined.

  Definition quot_True_ptrunc : quot R ≃ ptrunc A
    := Eqv_of_props quot_True_isProp ptrunc_isProp
         (fbar R (fun _ => triv) (prop_is_set ptrunc_isProp) trunc
               (fun _ _ _ => ptrunc_isProp _ _))
         (ptrunc_rec quot_True_isProp (cls R)).

End QuotientByTrue.

Section QuotientsHIT.

  Context `{Univalence} {A : Type} (R : A -> A -> PropU)
    (rr : forall x, fst (R x x))
    (rs : forall x y, fst (R x y) -> fst (R y x))
    (rt : forall x y z, fst (R x y) -> fst (R y z) -> fst (R x z)).

  (** Definition [def:quotient-as-HIT]: the quotient as a higher inductive
      type is the library's [Quotient], whose induction principle into
      families of sets has the book's form (with paths over [qglue]) and
      computes by definition on [class_of]. *)
  Definition QuotHIT : Type := Quotient (A := A) (fun x y => fst (R x y)).

  (** Exercise [xca:quotients-equivalence]. *)
  Definition quot_QuotHIT : quot R ≃ QuotHIT.
  Proof.
    pose (sQ := @IsHSet_isSet QuotHIT (ishset_quotient _)).
    pose (to := fbar R rr sQ (class_of _) (fun x y r => qglue r)).
    pose (from := @Quotient_rec A (fun x y => fst (R x y)) (quot R)
                    (isSet_IsHSet (quot_isSet R)) (cls R)
                    (fun x y r => snd (cls_eq_iff R rr rs rt x y) r)).
    refine (mkEqv to from _ _).
    - refine (im_ind R _ (fun z => quot_isSet R _ _) _). intro a. exact refl.
    - refine (Quotient_ind_hprop _ (fun w => to (from w) = w) _). intro a.
      exact refl.
  Defined.

End QuotientsHIT.


(** Remark [rem:set-trunc-as-quotient]: the set truncation as the quotient
    by [R(x,y) :≡ ‖x = y‖]. *)
Section SetTruncAsQuotient.

  Context `{Univalence} (A : Type).

  Definition trunc_paths_rel : A -> A -> PropU
    := fun x y => ptrunc_PropU (x = y).

  Definition tpr_refl (x : A) : fst (trunc_paths_rel x x) := trunc refl.

  Definition tpr_sym (x y : A)
    : fst (trunc_paths_rel x y) -> fst (trunc_paths_rel y x)
    := ptrunc_rec ptrunc_isProp (fun p => trunc p⁻¹).

  Definition tpr_trans (x y z : A)
    : fst (trunc_paths_rel x y) -> fst (trunc_paths_rel y z)
      -> fst (trunc_paths_rel x z)
    := fun u v => ptrunc_rec ptrunc_isProp
                    (fun p => ptrunc_rec ptrunc_isProp (fun q => trunc (q ⋅ p)) v) u.

  Definition strunc_quot_paths (x y : A)
    : ((cls trunc_paths_rel x = cls trunc_paths_rel y) -> ptrunc (x = y))
      × (ptrunc (x = y) -> cls trunc_paths_rel x = cls trunc_paths_rel y)
    := cls_eq_iff trunc_paths_rel tpr_refl tpr_sym tpr_trans x y.

  Definition strunc_quot_rec {S : Type} (sS : isSet S) (g : A -> S)
    : quot trunc_paths_rel -> S
    := fbar trunc_paths_rel tpr_refl sS g
         (fun x y => ptrunc_rec (sS _ _) (ap g)).

  Definition strunc_quot_rec_cls {S : Type} (sS : isSet S) (g : A -> S)
    (x : A) : strunc_quot_rec sS g (cls trunc_paths_rel x) = g x := refl.

End SetTruncAsQuotient.

(** Exercise [xca:map-induces-quotient]. *)
Section MapInducesQuotient.

  Context `{Univalence} {A B : Type} (f : A -> B).

  Definition eq_f : A -> A -> PropU := fun a a' => ptrunc_PropU (f a = f a').

  Definition eq_f_refl (a : A) : fst (eq_f a a) := trunc refl.
  Definition eq_f_sym (a a' : A) : fst (eq_f a a') -> fst (eq_f a' a)
    := ptrunc_rec ptrunc_isProp (fun p => trunc p⁻¹).
  Definition eq_f_trans (a a' a'' : A)
    : fst (eq_f a a') -> fst (eq_f a' a'') -> fst (eq_f a a'')
    := fun u v => ptrunc_rec ptrunc_isProp
                    (fun p => ptrunc_rec ptrunc_isProp (fun q => trunc (q ⋅ p)) v) u.

  Definition e_f_resp (a a' : A)
    : fst (eq_f a a') -> (settrunc ∘ im_p f) a = (settrunc ∘ im_p f) a'
    := ptrunc_rec (strunc_isSet _ _)
         (fun p : f a = f a' =>
            ap settrunc (path_sigma_prop (u := im_p f a) (v := im_p f a')
                           (fun _ => ptrunc_isProp) p)).

  Definition e_f : quot eq_f -> strunc (im f)
    := fbar eq_f eq_f_refl strunc_isSet (settrunc ∘ im_p f) e_f_resp.

  Definition e_f_commutes : settrunc ∘ im_p f = e_f ∘ cls eq_f := refl.

  (** Uniqueness of [e_f]. *)
  Definition e_f_unique
    : isContr {g : quot eq_f -> strunc (im f) & settrunc ∘ im_p f = g ∘ cls eq_f}
    := quot_univ_prop eq_f eq_f_refl strunc_isSet (settrunc ∘ im_p f) e_f_resp.

  Definition e_f_inv : strunc (im f) -> quot eq_f.
  Proof.
    refine (strunc_rec (quot_isSet eq_f) _). intro w.
    refine (@wconst_elim _ _ (fun v : fiber f (fst w) => cls eq_f (fst v))
              (quot_isSet eq_f) _ (snd w)).
    intros [a e] [a' e'].
    exact (snd (cls_eq_iff eq_f eq_f_refl eq_f_sym eq_f_trans a a')
             (trunc (e' ⋅ e⁻¹))).
  Defined.

  Definition e_f_isEquiv : isEquiv e_f.
  Proof.
    refine (iso_to_isEquiv e_f e_f_inv _ _).
    - refine (im_ind eq_f _ (fun z => quot_isSet eq_f _ _) _). intro a.
      exact refl.
    - refine (strunc_ind_prop _ (fun w => strunc_isSet _ _) _).
      intros [y u]. revert u.
      refine (ptrunc_ind _ (fun _ => strunc_isSet _ _) _).
      intros [a e]. revert y e. refine (paths_ind_r _ _ _). exact refl.
  Defined.

End MapInducesQuotient.
