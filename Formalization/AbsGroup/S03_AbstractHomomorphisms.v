(** * Section 7.3 Abstract homomorphisms

    Part of Chapter 7 ([absgroup.tex]); see [AbsGroup.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Exercise [xca:onlymult-hom]: [absHom_unit], [absHom_inv].
    - Definition [def:abstrisfunctor]: [absHom G H], a set
      ([absHom_isSet]); [abstr_hom f :≡ (USymf f, !)] using
      [USymf_comp] of Section 4.4; [path_absHom] (identifications are
      determined by the underlying functions).
    - Remark [rem:monoid-hom]: [MonoidHom]; footnote [ft:monoid-hom]: the
      map [1 → ({0,1}, ·)] with value [0] preserves the multiplication but
      not the unit ([mult_not_unit], with [bool_mul_monoid]).
    - Exercise [xca:abshomcomposition]: [absHom_comp], [absHom_id],
      [abstr_id], [abstr_comp] (from [USym_compose]); the monoids
      [absHom_monoid G] and [Hom_monoid G] (with the monoid laws of
      pointed maps [pcomp_pid_l], [pcomp_pid_r], [pcomp_assoc], now in
      Section 6.2 as the laws of the wild category of pointed types).
    - Example [ex:conjhom]: [conj_absHom].
    - Exercise [xca:abs-homgroup]: [ptw_mul_hom_of_isAb] and, for the
      converse, it suffices that [id · id] is a homomorphism
      ([isAb_of_ptw_mul_hom]).

    Left out (statements only, no proofs yet; time limit per result)
    - In example [ex:conjhom]: transport along [conj^g] in
      [absHom(H, -)] ([conjhom_trp_stmt]), and [abstr(Binn)(g) = conj^g]
      ([abstr_Binn_stmt]).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core.
From SymmetryBook Require Export AbsGroup.S02_Monoids.

Local Open Scope uf_scope.
Local Open Scope ag_scope.
Local Notation "g · h" := (ag_mul _ g h) (at level 40, left associativity) : ag_scope.

(** ** 7.3 Abstract homomorphisms *)

(** Exercise [xca:onlymult-hom]: preserving the multiplication implies
    preserving the unit and the inverses. *)
Section OnlyMult.

  Context {G H : AbsGroup} (f : ag_S G -> ag_S H) (hf : isAbsHomFun G H f).

  Definition absHom_unit : f (ag_e G) = ag_e H.
  Proof.
    apply (ag_cancel_l H (f (ag_e G))).
    refine ((hf _ _)^ @ _). refine (ap f (ag_runit G _) @ _).
    exact (ag_runit H _)^.
  Defined.

  Definition absHom_inv (s : ag_S G) : f (ag_inv G s) = ag_inv H (f s).
  Proof.
    apply ag_inv_unique.
    refine ((hf _ _)^ @ _). refine (ap f (ag_rinv G s) @ _).
    exact absHom_unit.
  Defined.

End OnlyMult.

(** Definition [def:abstrisfunctor]. *)
Definition absHom (G H : AbsGroup) : Type := {f : ag_S G -> ag_S H & isAbsHomFun G H f}.

Definition isAbsHomFun_isProp `{Funext} (G H : AbsGroup) (f : ag_S G -> ag_S H)
  : isProp (isAbsHomFun G H f)
  := Pi_isProp (fun _ => Pi_isProp (fun _ => ag_isSet H _ _)).

Definition absHom_isSet `{Funext} (G H : AbsGroup) : isSet (absHom G H)
  := Sigma_isSet (Pi_isSet (fun _ => ag_isSet H))
       (fun f => prop_is_set (isAbsHomFun_isProp G H f)).

Definition path_absHom `{Funext} {G H : AbsGroup} (f g : absHom G H)
  (h : forall s, fst f s = fst g s) : f = g
  := path_sigma_prop (fun k => isAbsHomFun_isProp G H k) (ptw_inv h).

Definition abstr_hom {G H : Group} (f : Hom G H) : absHom (abstr G) (abstr H)
  := (USymf f; fun s t => USymf_comp f t s).

(** Remark [rem:monoid-hom]: homomorphisms of monoids, and the example of
    footnote [ft:monoid-hom] of a map preserving the multiplication but
    not the unit. *)
Definition MonoidHom (M N : Monoid) : Type
  := {f : mo_S M -> mo_S N & (f (mo_e M) = mo_e N)
                             × forall s s', f (mo_mul M s s') = mo_mul N (f s) (f s')}.

Definition triv_monoid : Monoid
  := {| mo_S := True; mo_isSet := prop_is_set True_isProp; mo_e := triv;
        mo_mul := fun _ _ => triv; mo_runit := fun g => True_paths _ _;
        mo_lunit := fun g => True_paths _ _;
        mo_assoc := fun _ _ _ => refl |}.

Definition bool_mul_monoid : Monoid.
Proof.
  refine {| mo_S := Bool; mo_isSet := isSet_bool; mo_e := yes; mo_mul := andb |}.
  - intros []; exact refl.
  - intros []; exact refl.
  - intros [] [] []; exact refl.
Defined.

Definition mult_not_unit
  : {h : True -> Bool & (forall s s', h (triv) = andb (h s) (h s'))
                        × ¬ (h triv = yes)}
  := (fun _ => no; (fun _ _ => refl; fun r => yes_ne_no r^)).

(** Exercise [xca:abshomcomposition]. *)
Definition absHom_id (G : AbsGroup) : absHom G G := (id _; fun s t => refl).

Definition absHom_comp {G H K : AbsGroup} (g : absHom H K) (f : absHom G H)
  : absHom G K
  := (fst g ∘ fst f; fun s t => ap (fst g) (snd f s t) @ snd g _ _).

Definition abstr_id `{Funext} (G : Group) : abstr_hom (idG G) = absHom_id (abstr G).
Proof.
  apply path_absHom. intro s. cbn.
  exact (loops_fun_refl (id _) s @ ap_id s).
Defined.

Definition abstr_comp `{Funext} {G0 G1 G2 : Group} (f0 : Hom G0 G1) (f1 : Hom G1 G2)
  : abstr_hom (compG f1 f0) = absHom_comp (abstr_hom f1) (abstr_hom f0).
Proof.
  apply path_absHom. intro s. exact (ptw (USym_compose f0 f1) s).
Defined.

(** [absHom(G,G)] and [Hom(G,G)] are monoids under composition. *)
Definition absHom_monoid `{Funext} (G : AbsGroup) : Monoid
  := {| mo_S := absHom G G; mo_isSet := absHom_isSet G G; mo_e := absHom_id G;
        mo_mul := absHom_comp;
        mo_runit := fun f => path_absHom (absHom_comp f (absHom_id G)) f (fun s => refl);
        mo_lunit := fun f => path_absHom (absHom_comp (absHom_id G) f) f (fun s => refl);
        mo_assoc := fun f g h => path_absHom (absHom_comp f (absHom_comp g h))
                                    (absHom_comp (absHom_comp f g) h) (fun s => refl) |}.

Definition Hom_monoid `{Funext} (G : Group) : Monoid.
Proof.
  refine {| mo_S := Hom G G; mo_isSet := Hom_isSet G G; mo_e := idG G;
            mo_mul := compG |}.
  - intros [k]. exact (ap mkhom (pcomp_pid_r k)).
  - intros [k]. exact (ap mkhom (pcomp_pid_l k)).
  - intros [k1] [k2] [k3]. exact (ap mkhom (pcomp_assoc k1 k2 k3)).
Defined.

(** Example [ex:conjhom]: conjugation as an abstract homomorphism. *)
Definition conj_absHom (G : AbsGroup) (g : ag_S G) : absHom G G
  := (conj G g; conj_mul G g).

(** The rest of example [ex:conjhom] (statements only): transport along
    [conj^g] is postcomposition with [conj^g] in [absHom(H, -)] and
    precomposition with [conj^{h⁻¹}] in [absHom(-, G)]; and
    [abstr(Binn)(g) = conj^g]. *)
Definition conjhom_trp_stmt `{Univalence} : Type
  := (forall (H G : AbsGroup) (g : ag_S G) (f : absHom H G),
        trp (absHom H) (conj_path G g) f = absHom_comp (conj_absHom G g) f)
     × (forall (H G : AbsGroup) (h : ag_S H) (f : absHom H G),
          trp (fun K => absHom K G) (conj_path H h) f
          = absHom_comp f (conj_absHom H (ag_inv H h))).

Definition abstr_Binn_stmt `{Univalence} : Type
  := forall (G : Group) (g : USym G),
       ap (fun c : component Group G => abstr (fst c)) (loops_fun (Binn G) g)
       = conj_path (abstr G) g.

(** Exercise [xca:abs-homgroup]: the pointwise product of homomorphisms
    into [G] is again a homomorphism for all [f, g] (and all [H]) iff [G]
    is abelian. *)
Definition ptw_mul {H G : AbsGroup} (f g : ag_S H -> ag_S G) : ag_S H -> ag_S G
  := fun t => f t · g t.

Definition ptw_mul_hom_of_isAb {H G : AbsGroup} (a : ag_isAb G)
  (f g : absHom H G) : isAbsHomFun H G (ptw_mul (fst f) (fst g)).
Proof.
  intros s t. unfold ptw_mul.
  rewrite (snd f s t), (snd g s t).
  rewrite <- !ag_assoc. apply (ap (ag_mul G (fst f s))).
  rewrite !ag_assoc. apply (ap (fun x => x · fst g t)).
  exact (a _ _)^.
Defined.

Definition isAb_of_ptw_mul_hom (G : AbsGroup)
  (h : forall f g : absHom G G, isAbsHomFun G G (ptw_mul (fst f) (fst g)))
  : ag_isAb G.
Proof.
  intros s t.
  pose (r := h (absHom_id G) (absHom_id G) s t). unfold ptw_mul in r. cbn in r.
  unfold id in r.
  rewrite <- !ag_assoc in r. apply (ag_cancel_l G s) in r.
  rewrite !ag_assoc in r. apply (ag_cancel_r G t) in r.
  exact r^.
Defined.
