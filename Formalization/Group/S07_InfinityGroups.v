(** * Section 4.7 Infinity groups (∞-groups)

    Part of Chapter 4 ([group.tex]); see [Group.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:inftygps]: pointed connected types [UUpconn] and
      [InfGroup :≡ Copy(UUpconn)], with constructor [mkinfgroup] and
      destructor [Binf]; definition [def:classifyingspace] ([BGinf],
      [shinf]).
    - The automorphism [∞]-group [AutInf A a] of any [a : A].
    - Remark [rem:autinfgp]: the component of [U] at a set [S] is a
      groupoid ([component_U_set_isGrpd]), so [Aut_U(S)] is an ordinary
      group ([AutU_set], formed as [AutG] at [(S, !)] of this component,
      since [AutG] needs a groupoid); the inclusion [Group ↪ InfGroup]
      ([group_to_inf]) is injective ([group_to_inf_isInj]).
    - Homomorphisms of [∞]-groups ([HomInf], [mkhominf], [Bfinf]).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core.
From SymmetryBook Require Export Group.S06_Bicycles.

Local Open Scope uf_scope.

(** ** 4.7 Infinity groups *)

(** Definition [def:inftygps]. *)
Definition UUpconn : Type := {A : Type & A × isConn A}.

Definition InfGroup : Type := Copy UUpconn.

Definition mkinfgroup (X : UUpconn) : InfGroup := inc X.

Definition Binf (G : InfGroup) : UUpconn := out G.

(** Remark [rem:pointedtypes]: [∞]-group is a synonym for pointed
    connected type, wrapped with a constructor ([mkinfgroup]). *)

(** Definition [def:classifyingspace]. *)
Definition BGinf (G : InfGroup) : Ustar := (fst (Binf G); fst (snd (Binf G))).

Definition shinf (G : InfGroup) : utype (BGinf G) := pt (BGinf G).

(** The automorphism [∞]-group of [a : A]. *)
Definition AutInf {A : Type} (a : A) : InfGroup
  := mkinfgroup (component A a; ((a; trunc refl); component_isConn a)).

(** Remark [rem:autinfgp]. *)
Definition component_U_set_isGrpd `{Univalence} (S : Type) (sS : isSet S)
  : isGrpd (component Type S).
Proof.
  intros [X p] [Y q].
  refine (is_ntype_Eqv 0
            (Eqv_inv (subtype_paths_eqv (fun _ => ptrunc_isProp) (X; p) (Y; q))) _).
  refine (ptrunc_rec (isSet_isProp _) _ p). intro p'. destruct p'.
  refine (ptrunc_rec (isSet_isProp _) _ q). intro q'. destruct q'.
  exact (paths_sets_isSet sS).
Defined.

Definition AutU_set `{Univalence} (S : Type) (sS : isSet S) : Group
  := AutG (component_U_set_isGrpd S sS) (S; trunc refl).

(** The inclusion of groups into [∞]-groups forgets that the classifying
    type is a groupoid; it is injective. *)
Definition group_to_inf (G : Group) : InfGroup
  := mkinfgroup (fst (B G); (fst (snd (B G)); fst (snd (snd (B G))))).

Definition ap_isEquiv_of {X Y : Type} {f : X -> Y} (t : isEquiv f) (x y : X)
  : isEquiv (@ap _ _ f x y)
  := isEquiv_of_IsEquiv _ (H := @isequiv_ap _ _ f (IsEquiv_of_isEquiv t) x y).

Definition UUscone_to_pconn (X : UUscone) : UUpconn
  := (fst X; (fst (snd X); fst (snd (snd X)))).

Definition UUscone_to_pconn_isInj `{Funext} : isInj UUscone_to_pconn.
Proof.
  pose (g := fun X : UUscone => ((fst X; (fst (snd X); fst (snd (snd X))));
                                 snd (snd (snd X)))
               : {Y : UUpconn & isGrpd (fst Y)}).
  assert (tg : isEquiv g).
  { refine (iso_to_isEquiv g (fun w => (fst (fst w); (fst (snd (fst w));
                                 (snd (snd (fst w)); snd w))) : UUscone) _ _);
      intro; exact refl. }
  apply ap_isEquiv_isInj. intros X X'.
  refine (isEquiv_homotopic (@ap _ _ fst (g X) (g X') ∘ @ap _ _ g X X') _ _
            (comp_isEquiv (ap_isEquiv_of tg X X')
               (isInj_ap_isEquiv (fst_isInj (fun Y : UUpconn => isGrpd_isProp (fst Y))) _ _))).
  intro r. destruct r. exact refl.
Defined.

Definition group_to_inf_isInj `{Funext} : isInj group_to_inf.
Proof.
  apply ap_isEquiv_isInj. intros G K.
  refine (isEquiv_homotopic
            (@ap _ _ inc _ _ ∘ @ap _ _ UUscone_to_pconn (out G) (out K) ∘ @ap _ _ out G K) _ _ _).
  - intro r. destruct r. exact refl.
  - refine (comp_isEquiv (comp_isEquiv (ap_isEquiv_of (snd (Copy_eqv _)) G K)
              (isInj_ap_isEquiv UUscone_to_pconn_isInj _ _))
              (ap_isEquiv_of (snd (Eqv_inv (Copy_eqv _))) _ _)).
Defined.

(** Homomorphisms of [∞]-groups. *)
Definition HomInf (G H : InfGroup) : Type := Copy (BGinf G →* BGinf H).

Definition mkhominf {G H : InfGroup} (k : BGinf G →* BGinf H) : HomInf G H := inc k.

Definition Bfinf {G H : InfGroup} (f : HomInf G H) : BGinf G →* BGinf H := out f.
