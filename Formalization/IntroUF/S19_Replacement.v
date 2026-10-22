(** * Section 2.19 The replacement principle

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Essentially and locally [U]-small types ([essSmall], [locSmall]);
      essential smallness is invariant under equivalence and implies
      local smallness; small types are essentially small; a reflexive
      relation [Eq_A] inducing equivalences shows local smallness.
    - Being essentially small is a proposition (by univalence).
    - Exercise: [U] is locally [U]-small (using the book's class
      [UnivalenceUF] as hypothesis), and locally small types are closed
      under products over a small type.  Other closure properties are not
      investigated.
    - Remark: propositional resizing makes propositions essentially small
      and sets locally small.
    - The replacement principle as a definition [Replacement] (used as a
      hypothesis), and exercise [xca:comp-loc-small-ess-small]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S18_Decidability.

Local Open Scope uf_scope.

(** ** Preliminaries *)

(** Identifications in a sum type with proposition-valued second
    component. *)
Definition path_sigma_prop {A : Type} {P : A -> Type}
  (hP : forall a, isProp (P a)) {u v : {a : A & P a}} (e : fst u = fst v)
  : u = v
  := pathpair (Y := P) (y := snd u) (y' := snd v) e (hP _ _ _).

(** A sum of contractible types over a contractible type is contractible. *)
Definition Sigma_isContr {A : Type} {B : A -> Type} (cA : isContr A)
  (cB : forall a, isContr (B a)) : isContr {a : A & B a}.
Proof.
  refine ((fst cA; fst (cB (fst cA))); _).
  intros [a b].
  exact (pathpair (snd cA a) (isContr_isProp' (cB a) _ _)).
Defined.

(** A map between contractible types is an equivalence. *)
Definition contr_map_isEquiv {A B : Type} (cA : isContr A) (cB : isContr B)
  (f : A -> B) : isEquiv f
  := iso_to_isEquiv f (fun _ => fst cA) (fun a => snd cA a)
       (fun b => isContr_isProp' cB _ _).

(** Equivalences of families of types induce equivalences of products. *)
Definition Pi_eqv `{Funext} {A : Type} {B C : A -> Type}
  (e : forall a, B a ≃ C a) : (forall a, B a) ≃ (forall a, C a)
  := mkEqv (fun k a => fst (e a) (k a)) (fun k a => eqinv (snd (e a)) (k a))
       (fun k => ptw_inv (fun a => eqinv_l (snd (e a)) (k a)))
       (fun k => ptw_inv (fun a => eqinv_r (snd (e a)) (k a))).

(** The type [∑_{b:B} (b = c)] is contractible. *)
Definition singleton_contr' {B : Type} (c : B) : isContr {b : B & b = c}.
Proof.
  refine ((c; refl); _).
  intros [b p]. revert b p. refine (paths_ind_r _ _ _). exact refl.
Defined.

(** ** 2.19 The replacement principle *)

Section Smallness.

  Universe u.

  (** Definition [def:ess-loc-small]. *)
  Definition essSmall (A : Type) : Type := {X : Type@{u} & A ≃ X}.

  Definition locSmall (A : Type) : Type := forall x y : A, essSmall (x = y).

  (** Essential smallness is invariant under equivalence. *)
  Definition essSmall_Eqv {A B : Type} (e : A ≃ B) (s : essSmall B)
    : essSmall A
    := (fst s; Eqv_comp e (snd s)).

  (** Any [A : U] is essentially small. *)
  Definition small_essSmall (A : Type@{u}) : essSmall A := (A; idEqv A).

  (** Any essentially small type is locally small. *)
  Definition essSmall_locSmall {A : Type} (s : essSmall A) : locSmall A.
  Proof.
    intros x y.
    pose (E := IsEquiv_of_isEquiv (snd (snd s))).
    exact ((fst (snd s) x = fst (snd s) y);
           (ap (fst (snd s)); isEquiv_of_IsEquiv _ (H := isequiv_ap x y))).
  Defined.

  (** A reflexive relation [Eq_A : A → A → U] that induces, by path
      induction, equivalences [(x = y) ≃ Eq_A(x,y)] shows that [A] is
      locally small. *)
  Definition locSmall_of_Eq {A : Type} (Eq : A -> A -> Type@{u})
    (r : forall x, Eq x x)
    (h : forall x y, isEquiv (path_ind x (fun y _ => Eq x y) (r x) y))
    : locSmall A
    := fun x y => (Eq x y; (_; h x y)).

  (** Exercise: [U] is locally [U]-small, by univalence. *)
  Definition U_locSmall `{UnivalenceUF} : locSmall Type@{u}
    := fun X Y => ((X ≃ Y); (idtoeqv; ua X Y)).

  (** Exercise: closure under products over a small type. *)
  Definition Pi_locSmall `{Funext} {A : Type@{u}} {B : A -> Type}
    (h : forall a, locSmall (B a)) : locSmall (forall a, B a).
  Proof.
    intros f g.
    exact ((forall a, fst (h a (f a) (g a)));
           Eqv_comp (ptw; funext f g) (Pi_eqv (fun a => snd (h a (f a) (g a))))).
  Defined.

  (** Being essentially small is a proposition, by univalence. *)
  Definition Eqv_precomp `{Funext} {A X X' : Type} (e : A ≃ X)
    : (X ≃ X') ≃ (A ≃ X').
  Proof.
    refine (mkEqv (fun d => Eqv_comp e d) (fun d => Eqv_comp (Eqv_inv e) d) _ _).
    - intro d. apply path_Eqv. apply ptw_inv. intro x.
      exact (ap (fst d) (eqinv_r (snd e) x)).
    - intro d. apply path_Eqv. apply ptw_inv. intro a.
      exact (ap (fst d) (eqinv_l (snd e) a)).
  Defined.

  Definition essSmall_isProp `{Univalence} (A : Type) : isProp (essSmall A).
  Proof.
    intros s s'. revert s'.
    apply isContr_isProp'.
    destruct s as [X e].
    refine (isContr_Eqv _ (singleton_contr X)).
    exact (tot (fun X' (p : X = X') => fst (Eqv_precomp e) (idtoeqv p));
           tot_isEquiv _ (fun X' => snd (Eqv_comp (idtoeqv; ua X X') (Eqv_precomp e)))).
  Defined.

End Smallness.

(** Remark: propositional resizing says that any proposition is
    essentially small, and then any set is locally small. *)
Section ResizingSmall.

  Universes u v.
  Constraint u < v.

  (** Propositional resizing from [U] to [U'] ([PropResizing] in
      2.18), with the lifting map written out at levels [u], [v]. *)
  Definition lift_uv (P : {X : Type@{u} & isProp X}) : {X : Type@{v} & isProp X}
    := exist (fun X : Type@{v} => isProp X) (fst P) (fun a b => snd P a b).

  Definition resizing_essSmall (r : isEquiv lift_uv)
    (P : {X : Type@{v} & isProp X}) : {X : Type@{u} & fst P ≃ X}.
  Proof.
    pose (e := eqinv_r r P).
    exact (exist (fun X : Type@{u} => fst P ≃ X) (fst (eqinv r P))
             (Eqv_inv (idtoeqv (ap fst e)))).
  Defined.

  Definition resizing_set_locSmall (r : isEquiv lift_uv) (A : Type@{v})
    (s : isSet A) (x y : A) : {X : Type@{u} & (x = y) ≃ X}
    := resizing_essSmall r ((x = y); s x y).

End ResizingSmall.

(** Principle [pri:replacement]. *)
Definition Replacement : Type
  := forall (A B : Type) (f : A -> B), essSmall A -> locSmall B
       -> essSmall (im f).

(** Exercise [xca:comp-loc-small-ess-small]: under replacement, the
    connected component of an element of a locally small type is
    essentially small. *)
Definition component_im_eqv {A : Type} (a : A)
  : component A a ≃ im (fun _ : True => a)
  := (tot (fun x => ptrunc_rec ptrunc_isProp
                      (fun p : a = x => trunc ((triv; p⁻¹) : {_ : True & x = a}))) ;
      tot_isEquiv _ (fun x =>
        snd (Eqv_of_props ptrunc_isProp ptrunc_isProp
               (ptrunc_rec ptrunc_isProp
                  (fun p : a = x => trunc ((triv; p⁻¹) : {_ : True & x = a})))
               (ptrunc_rec ptrunc_isProp
                  (fun w : {_ : True & x = a} => trunc (snd w)⁻¹))))).

Definition replacement_component (rep : Replacement) {A : Type}
  (h : locSmall A) (a : A) : essSmall (component A a)
  := essSmall_Eqv (component_im_eqv a)
       (rep True A (fun _ => a) (small_essSmall True) h).
