(** * Section 5.5 The classifying type is the type of torsors

    Part of Chapter 5 ([actions.tex]); see [Actions.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:Gtorsor]: [Torsor G], the component of [G-Set] at
      the principal torsor; it is connected.
    - Exercise [xca:torsor=free+transitive] ([torsor_free_trans],
      [free_trans_torsor]); for a free transitive [X] with [x : X(sh_G)],
      the map [p ↦ p · x : P_{sh_G} → X] is an equivalence.
    - Definition [def:BG2TorsG]: [pathsp_tors] and the pointed
      [pathsp_ptd : BG →* (Torsor_G, P_{sh_G})].
    - Remark [rem:pathsptransport] ([hom_of_path_pathsp]: transport in
      [P_] is [p ↦ p q⁻¹]) and lemma [lem:pathsptransportiseq]
      ([pathsp_ap_isEquiv]), with the inverse [Q(f) :≡ f_y(refl_y)⁻¹] of
      the book's footnote; the second round trip uses that maps out of
      the transitive [P_y] are determined by their value at [refl_y].
    - Theorem [lem:BGbytorsor]: [BG ≃ Torsor_G] ([BG_Torsor_eqv]).
    - Definition [def:restrictandinduce] ([restrict], [induce]) and
      remark [rem:coinduced-Hset] ([coinduce]); exercises
      [xca:adjunction-_!-^*] (second part, [adj_induce_restrict]) and
      [xca:adjunction-^*-_*] ([adj_restrict_coinduce]).
    - Construction [con:inducedtorsor]: [η] ([eta_path]), [π]
      ([pi_path]), the pointed map [f_! : Torsor_G →* Torsor_H]
      ([induce_tors_ptd]) and the square [f_! P^G = P^H Bf]
      ([induce_tors_square]).

    - Remarks [rem:^*-_!-as-(pre)image] and [rem:coinduced-subset]:
      preimage, image and coinduced subset ([sub_preimage], [sub_image],
      [sub_coinduced]); the remarks' claims hold by definition.

    Left out (statements only, no proofs yet; time limit per result)
    - Exercise [xca:why-setTrunc_f_!] ([xca_why_setTrunc_stmt]), the
      first part of [xca:adjunction-_!-^*] ([xca_induce_iso_stmt]), and
      lemma [lem:epifullyfaithful] ([lem_epifullyfaithful_stmt]).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Truncations.SeparatedTrunc Cubical.DPath.
From SymmetryBook Require Export Actions.S04_Orbits.

Local Open Scope uf_scope.

(** ** 5.5 The classifying type is the type of torsors *)

Section Torsors.

  Context `{Univalence} (G : Group).

  (** Definition [def:Gtorsor]: [Torsor_G :≡ ∑_X ‖P_{sh_G} = X‖], the
      component of [G-Set] at the principal torsor. *)
  Definition Torsor : Type := component (GSet G) (princ G).

  Definition Torsor_isConn : isConn Torsor := component_isConn (princ G).

  (** The action type of [P_y] is contractible. *)
  Definition pathsp_tot_contr (y : utype (BG G)) : isContr (TotG (pathsp y))
    := singleton_contr y.

  Definition pathsp_trans (y : utype (BG G)) : istrans (pathsp y).
  Proof.
    apply trans_of_conn.
    pose (c := pathsp_tot_contr y).
    exact (trunc (fst c); fun a b => trunc (isContr_isProp' c a b)).
  Defined.

  (** Exercise [xca:torsor=free+transitive]. *)
  Definition contr_isConn {T : Type} (c : isContr T) : isConn T
    := (trunc (fst c); fun a b => trunc (isContr_isProp' c a b)).

  Definition contr_isSet {T : Type} (c : isContr T) : isSet T
    := prop_is_set (isContr_isProp' c).

  Definition torsor_free_trans (X : GSet G) (t : ptrunc (princ G = X))
    : isFreeG X × istrans X.
  Proof.
    refine (ptrunc_rec (prod_isProp (Pi_isProp (fun _ => isContr_isProp _))
                          (istrans_isProp X)) _ t).
    intro e. destruct e.
    exact (XhG_set_free _ (contr_isSet (pathsp_tot_contr (sh G)));
           pathsp_trans (sh G)).
  Defined.

  Definition free_trans_torsor (X : GSet G) (f : isFreeG X) (t : istrans X)
    : ptrunc (princ G = X).
  Proof.
    refine (ptrunc_rec ptrunc_isProp _ t). intros [x hx].
    apply trunc. refine (@path_GSet _ G (princ G) X _). intro z.
    refine ((fun p : sh G = z => act X p x); _).
    refine (ptrunc_rec (isEquiv_isProp _) _ (snd (BG_isConn G) (sh G) z)). intro q.
    destruct q.
    refine (inj_surj_isEquiv (cancel_isInj (el_isSet X _)
              (fun g g' e => Overture.fst (free_pt_char X x) (f x) g g' e)) _).
    intro y. refine (Trunc_functor (-1) _ (hx y)). intros [g e].
    exact (g⁻¹; (act_inv_l X g y)⁻¹ @ ap (act X g⁻¹) e⁻¹).
  Defined.

  (** Definition [def:BG2TorsG]: [P_ : BG →* (Torsor_G, P_{sh_G})]. *)
  Definition TorsorStar : Ustar := (Torsor; (princ G; trunc refl)).

  Definition pathsp_tors (y : utype (BG G)) : Torsor
    := (pathsp y; Trunc_functor (-1) (fun q => ap pathsp q) (snd (BG_isConn G) (sh G) y)).

  Definition pathsp_ptd : BG G →* TorsorStar
    := (pathsp_tors; @path_sigma_prop (GSet G) (fun X => ptrunc (princ G = X))
                       (fun _ => ptrunc_isProp) (princ G; trunc refl) (pathsp_tors (sh G)) refl).

  (** Remark [rem:pathsptransport]: the transport in [P_] is
      precomposition with the inverse. *)
  Definition hom_of_path_pathsp {y z : utype (BG G)} (q : y = z) (w : utype (BG G))
    (p : y = w) : hom_of_path (ap pathsp q) w p = p ⋅ q⁻¹.
  Proof. destruct q. exact (trans_1p p)^. Defined.

  (** Lemma [lem:pathsptransportiseq], with the inverse [Q] of the
      book's footnote. *)
  Definition pathsp_Q {y z : utype (BG G)} (f : pathsp y = pathsp z) : y = z
    := (hom_of_path f y refl)⁻¹.

  Definition pathsp_ap_isEquiv (y z : utype (BG G))
    : isEquiv (fun q : y = z => ap pathsp q).
  Proof.
    refine (iso_to_isEquiv _ pathsp_Q _ _).
    - intro q. destruct q. exact refl.
    - intro f. apply hom_of_path_cancel.
      apply (evisinj_trans (pathsp_trans y) (refl : y = y)).
      refine (hom_of_path_pathsp _ y refl @ _). unfold pathsp_Q.
      exact (symm_symm _).
  Defined.

  (** Theorem [lem:BGbytorsor]: [BG ≃ Torsor_G]. *)
  Definition BG_Torsor_isEquiv : isEquiv pathsp_tors.
  Proof.
    apply (snd (conn_isEquiv_iff_point pathsp_tors (BG_isConn G) Torsor_isConn (sh G))).
    pose (s := subtype_paths_eqv (fun _ : GSet G => @ptrunc_isProp (princ G = _))
                 (pathsp_tors (sh G)) (pathsp_tors (sh G))).
    refine (isEquiv_homotopic (eqinv (snd s) ∘ (fun q => ap pathsp q)) _ _
              (comp_isEquiv (pathsp_ap_isEquiv _ _) (eqinv_isEquiv (snd s)))).
    intro q. apply (isInj_cancel (isEquiv_isInj (snd s))).
    refine (eqinv_r (snd s) _ @ _).
    exact (ap_compose pathsp_tors fst q).
  Defined.

  Definition BG_Torsor_eqv : utype (BG G) ≃ Torsor := (pathsp_tors; BG_Torsor_isEquiv).

End Torsors.

(** ** 5.5.1 Homomorphisms and torsors *)
Section RestrictInduce.

  Context `{Funext} {G K : Group} (f : Hom G K).

  Local Notation Bf0 := (fst (Bf f)).

  (** Definition [def:restrictandinduce]: restriction [f^*Y :≡ Y ∘ Bf] and
      the induced [H]-set [f_!X(w) :≡ ‖∑_z (Bf(z) = w) × X(z)‖₀].
      Footnote [ft:f_!X(w)-orbitset]: [f_!X(w)] is also a set of orbits
      (informal). *)
  Definition restrict (Y : GSet K) : GSet G := fun z => Y (Bf0 z).

  Definition induce_type (X : GSet G) (w : utype (BG K)) : Type
    := {z : utype (BG G) & (Bf0 z = w) × el X z}.

  Definition induce (X : GSet G) : GSet K
    := fun w => (strunc (induce_type X w); strunc_isSet).

End RestrictInduce.

(** Exercise [xca:why-setTrunc_f_!] (statement only): without the set
    truncation, [f_!X] need not be an [H]-set.  (The book's solution:
    [G :≡ ℤ], [H] trivial, [X] constant [𝟙], where the type is the
    circle.) *)
Definition xca_why_setTrunc_stmt `{Funext} : Type
  := {G : Group & {K : Group & {f : Hom G K & {X : GSet G &
       {w : utype (BG K) & ¬ isSet (induce_type f X w)}}}}}.

(** Exercise [xca:adjunction-_!-^*], first part (statement only): for an
    isomorphism [f], [f_!X ≃ X ∘ Bf⁻¹]. *)
Definition xca_induce_iso_stmt `{Funext} : Type
  := forall (G K : Group) (f : Hom G K) (i : isIso f) (X : GSet G) (w : utype (BG K)),
       el (induce f X) w ≃ el X (eqinv i w).

Section AdjInduce.

  Context `{Funext} {G K : Group} (f : Hom G K).

  Local Notation Bf0 := (fst (Bf f)).

  (** Exercise [xca:adjunction-_!-^*], second part. *)
  Definition adj_induce_restrict (X : GSet G) (Y : GSet K)
    : HomGs (induce f X) Y ≃ HomGs X (restrict f Y).
  Proof.
    refine (Eqv_comp (Pi_eqv (fun w => strunc_univ_prop (induce_type f X w) (el_isSet Y w))) _).
    refine (mkEqv (fun (h : forall w, induce_type f X w -> el Y w) z x => h (Bf0 z) (z; (refl; x)))
                  (fun (k : HomGs X (restrict f Y)) w (u : induce_type f X w) =>
                     trp (el Y) (fst (snd u)) (k (fst u) (snd (snd u)))) _ _).
    - intro h. apply ptw_inv. intro w. apply ptw_inv. intros [z [p x]].
      destruct p. exact refl.
    - intro k. exact refl.
  Defined.

End AdjInduce.

(** Remark [rem:^*-_!-as-(pre)image]: for subsets, [f^*] is the preimage
    and [∃_f] (with propositional truncation) the image. *)
Definition sub_preimage {A B : Type} (f : A -> B) (Y : Sub B) : Sub A := fun a => Y (f a).

Definition sub_image {A B : Type} (f : A -> B) (X : Sub A) : Sub B
  := fun b => (Ex (fun a => (f a = b) × fst (X a)); ptrunc_isProp).

Section Coinduce.

  Context `{Funext} {G K : Group} (f : Hom G K).

  Local Notation Bf0 := (fst (Bf f)).

  (** Remark [rem:coinduced-Hset]: the coinduced [H]-set. *)
  Definition coinduce (X : GSet G) : GSet K
    := fun w => ((forall z, Bf0 z = w -> el X z);
                 Pi_isSet (fun z => Pi_isSet (fun _ => el_isSet X z))).

End Coinduce.

(** Remark [rem:coinduced-subset]: [∀_f :≡ f_*] on subsets. *)
Definition sub_coinduced `{Funext} {A B : Type} (f : A -> B) (X : Sub A) : Sub B
  := fun b => ((forall a, f a = b -> fst (X a)); Pi_isProp (fun a => fun_isProp (snd (X a)))).

Section AdjCoinduce.

  Context `{Funext} {G K : Group} (f : Hom G K).

  Local Notation Bf0 := (fst (Bf f)).

  (** Exercise [xca:adjunction-^*-_*]. *)
  Definition adj_restrict_coinduce (Y : GSet K) (X : GSet G)
    : HomGs (restrict f Y) X ≃ HomGs Y (coinduce f X).
  Proof.
    refine (mkEqv (fun h w y z p => h z (trp (el Y) p⁻¹ y))
                  (fun k z y => k (Bf0 z) y z refl) _ _).
    - intro h. exact refl.
    - intro k. apply ptw_inv. intro w. apply ptw_inv. intro y.
      apply ptw_inv. intro z. apply ptw_inv. intro p. destruct p. exact refl.
  Defined.

End AdjCoinduce.

(** Construction [con:inducedtorsor]. *)
Section InducedTorsor.

  Context `{Univalence} {G K : Group} (f : Hom G K).

  Local Notation Bf0 := (fst (Bf f)).

  (** [η_w : f_! P_x(w) ≃ P_{Bf(x)}(w)], contracting away [z]. *)
  Definition induce_pathsp_type_eqv (x : utype (BG G)) (w : utype (BG K))
    : induce_type f (pathsp x) w ≃ (Bf0 x = w).
  Proof.
    refine (mkEqv (fun u : induce_type f (pathsp x) w => fst (snd u) ⋅ ap Bf0 (snd (snd u)))
                  (fun e => (x; (e; refl))) _ _).
    - intros [z [p q]]. destruct q. cbn. destruct p. exact refl.
    - intro e. destruct e. exact refl.
  Defined.

  Definition strunc_set_eqv {T : Type} (s : isSet T) : strunc T ≃ T
    := Eqv_inv (settrunc; isEquiv_of_IsEquiv _ (H := isequiv_tr 0 T (IsTrunc0 := isSet_IsHSet s))).

  Definition eta_path (x : utype (BG G)) : induce f (pathsp x) = pathsp (Bf0 x)
    := @path_GSet _ K (induce f (pathsp x)) (pathsp (Bf0 x))
         (fun w => Eqv_comp (strunc_set_eqv
                     (is_ntype_Eqv 0 (Eqv_inv (induce_pathsp_type_eqv x w))
                        (BG_isGrpd K _ _)))
                   (induce_pathsp_type_eqv x w)).

  (** [π : P_{sh_K} = P_{Bf(sh_G)}] and the pointing [η⁻¹ π]. *)
  Definition pi_path : princ K = pathsp (Bf0 (sh G)) := ap pathsp (snd (Bf f)).

  Definition induce_tors (T : Torsor G) : Torsor K
    := (induce f (fst T);
        Trunc_functor (-1) (fun e : princ G = fst T =>
                              ap (induce f) e ⋅ ((eta_path (sh G))⁻¹ ⋅ pi_path)) (snd T)).

  Definition induce_tors_ptd : TorsorStar G →* TorsorStar K
    := (induce_tors;
        @path_sigma_prop (GSet K) (fun X => ptrunc (princ K = X)) (fun _ => ptrunc_isProp)
          (princ K; trunc refl) (induce_tors (princ G; trunc refl))
          ((eta_path (sh G))⁻¹ ⋅ pi_path)).

  (** The square [f_! P^G = P^H Bf]. *)
  Definition induce_tors_square (x : utype (BG G))
    : induce_tors (pathsp_tors G x) = pathsp_tors K (Bf0 x)
    := @path_sigma_prop (GSet K) (fun X => ptrunc (princ K = X)) (fun _ => ptrunc_isProp)
         (induce_tors (pathsp_tors G x)) (pathsp_tors K (Bf0 x)) (eta_path x).

End InducedTorsor.

(** Lemma [lem:epifullyfaithful] (statement only): if [Uf] is
    surjective, then [f^*] is an injection. *)
Definition lem_epifullyfaithful_stmt `{Funext} : Type
  := forall (G K : Group) (f : Hom G K), isSurj (USymf f) -> isInj (restrict f).
