(** * Section 4.3 Abstract groups

    Part of Chapter 4 ([group.tex]); see [Group.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:abstractgroup]: [AbsGroup], a record with the
      underlying set [ag_S], the unit [ag_e], the multiplication [ag_mul]
      (written [g₁ · g₂]), the inverse [ag_inv], and the unit laws, the
      associativity law and the law of inverses.  The library's
      [Algebra.Groups.Group] is a record of type classes and not
      definitionally the book's notion, so we keep our own.
    - Lemma [lem:idtypesgiveabstractgroups] and definition [def:abstrG]:
      [abstr G] on [USym G], with [e :≡ refl], [g⁻¹ :≡ symm g] and
      [h · g :≡ trans g h], i.e., [h ⋅ g] in our notation; the laws are
      those of [xca:path-groupoid-laws] (Section 2.5).  The equations
      [e⁻¹ ≡ e] and [e · g ≡ g] hold by [refl].
    - Exercise [xca:abstract-group-of-maps]: the pointwise abstract group
      on [X → S] ([ag_maps]), using [Funext]; it is abelian if [G] is
      ([ag_maps_isAb]).  We also give the converse for non-empty [X]
      ([‖X‖], [def:non-empty]; [ag_maps_isAb_conv]), which the book no
      longer states (for [X] empty, [X → S] is trivial, hence abelian,
      for any [G]).
    - The law of left inverses ([ag_linv]) and a bridge to the library's
      groups ([AbsGroup_to_lib]). *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core.
Require HoTT.Algebra.Groups.Group.
From SymmetryBook Require Export Group.S02_TypeOfGroups.

Local Open Scope uf_scope.

(** ** 4.3 Abstract groups *)

(** The laws [it:right-unit], [it:left-unit], [it:associativity] and
    [it:inverse] of the symmetries [a = a] in a groupoid are exercise
    [xca:path-groupoid-laws] in 2.5. *)

(** Definition [def:abstractgroup]. *)
Record AbsGroup : Type := {
  (** [struc:under-set] *)
  ag_S : Type;
  ag_isSet : isSet ag_S;
  (** [struc:unit] *)
  ag_e : ag_S;
  (** [struc:mult-op] *)
  ag_mul : ag_S -> ag_S -> ag_S;
  (** [struc:inv-op] *)
  ag_inv : ag_S -> ag_S;
  (** [axiom:unit-laws] *)
  ag_runit : forall g, ag_mul g ag_e = g;
  ag_lunit : forall g, ag_mul ag_e g = g;
  (** [axiom:ass-law] *)
  ag_assoc : forall g1 g2 g3, ag_mul g1 (ag_mul g2 g3) = ag_mul (ag_mul g1 g2) g3;
  (** [axiom:inv-law] *)
  ag_rinv : forall g, ag_mul g (ag_inv g) = ag_e
}.

(** The law of left inverses follows. *)
Definition ag_linv (G : AbsGroup) (g : ag_S G) : ag_mul G (ag_inv G g) g = ag_e G.
Proof.
  pose (h := ag_inv G g).
  refine ((ag_runit G _)^ @ _).
  refine (ap (ag_mul G _) (ag_rinv G h)^ @ _).
  refine (ag_assoc G _ _ _ @ _).
  refine (ap (fun k => ag_mul G k _) (ag_assoc G _ _ _)^ @ _).
  refine (ap (fun k => ag_mul G (ag_mul G h k) _) (ag_rinv G g) @ _).
  refine (ap (fun k => ag_mul G k _) (ag_runit G h) @ _).
  exact (ag_rinv G h).
Defined.

(** Bridge to the library's groups [HoTT.Algebra.Groups.Group.Group]. *)
Definition AbsGroup_to_lib (G : AbsGroup) : HoTT.Algebra.Groups.Group.Group.
Proof.
  refine (HoTT.Algebra.Groups.Group.Build_Group (ag_S G) (ag_mul G) (ag_e G) (ag_inv G) _).
  repeat split.
  - exact (isSet_IsHSet (ag_isSet G)).
  - exact (ag_assoc G).
  - exact (ag_lunit G).
  - exact (ag_runit G).
  - exact (ag_linv G).
  - exact (ag_rinv G).
Defined.

(** Abelian abstract groups. *)
Definition ag_isAb (G : AbsGroup) : Type
  := forall g h : ag_S G, ag_mul G g h = ag_mul G h g.

(** Lemma [lem:idtypesgiveabstractgroups] and definition [def:abstrG]. *)
Definition abstr (G : Group) : AbsGroup
  := {| ag_S := USym G;
        ag_isSet := USym_isSet G;
        ag_e := refl;
        ag_mul := fun h g => h ⋅ g;
        ag_inv := fun g => g⁻¹;
        ag_runit := fun g => trans_1p g;
        ag_lunit := fun g => trans_p1 g;
        ag_assoc := fun g1 g2 g3 => trans_assoc g3 g2 g1;
        ag_rinv := fun g => trans_Vp g |}.

(** The equations that hold by definition. *)
Definition abstr_inv_e (G : Group) : ag_inv (abstr G) (ag_e (abstr G)) = ag_e (abstr G)
  := refl.

Definition abstr_lunit_jdeq (G : Group) (g : USym G) : ag_mul (abstr G) (ag_e (abstr G)) g = g
  := refl.

(** [G] is abelian iff [abstr(G)] is. *)
Definition isAb_abstr (G : Group) : isAb G -> ag_isAb (abstr G) := fun a => a.

(** Exercise [xca:abstract-group-of-maps]. *)
Section AbstractGroupOfMaps.

  Context `{Funext} (G : AbsGroup) (X : Type).

  Local Notation S := (ag_S G).
  Local Notation "g · h" := (ag_mul G g h) (at level 40, left associativity).

  Definition ag_maps : AbsGroup
    := {| ag_S := X -> S;
          ag_isSet := Pi_isSet (fun _ => ag_isSet G);
          ag_e := cst (ag_e G);
          ag_mul := fun f g x => f x · g x;
          ag_inv := fun f x => ag_inv G (f x);
          ag_runit := fun f => ptw_inv (fun x => ag_runit G (f x));
          ag_lunit := fun f => ptw_inv (fun x => ag_lunit G (f x));
          ag_assoc := fun f g h => ptw_inv (fun x => ag_assoc G (f x) (g x) (h x));
          ag_rinv := fun f => ptw_inv (fun x => ag_rinv G (f x)) |}.

  Definition ag_maps_isAb (a : ag_isAb G) : ag_isAb ag_maps
    := fun f g => ptw_inv (fun x => a (f x) (g x)).

  Definition ag_maps_isAb_conv (x0 : ptrunc X) (a : ag_isAb ag_maps) : ag_isAb G.
  Proof.
    intros g h.
    refine (ptrunc_rec (ag_isSet G _ _) _ x0). intro x.
    exact (ptw (a (cst g) (cst h)) x).
  Defined.

End AbstractGroupOfMaps.
