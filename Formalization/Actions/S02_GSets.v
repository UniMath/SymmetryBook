(** * Section 5.2 Group actions (G-sets)

    Part of Chapter 5 ([actions.tex]); see [Actions.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:Gset]: [GSet G :≡ (BG → Set)], with [el X z] for
      the elements of [X(z)] and the action [act X p] ([p ·_X _]).
    - Examples: trivial [G]-sets [trivG], [pathsp y] ([P_y]) and the
      principal torsor [princ G], the adjoint [G]-set [Ad G] (acting by
      conjugation, [act_Ad]), and [HomG_set H G] ([Hom(H,G)(y)]).
    - Identifications of [G]-sets from pointwise equivalences
      ([path_GSet]); exercise [xca:HomZGvsAdG] ([Ad_HomZG]).
    - Definition [def:map-of-Gsets] ([HomGs], a set), exercise
      [xca:equivariant-map-totalization] ([HomGs_tot_eqv]), remark
      [rem:map-of-Gsets] ([HomGs_equivariant]).
    - Definition [def:Gsubset] ([SubG], [GSet_sub]); exercise
      [xca:SubGX-closedSubXshG] ([SubG_closed_eqv]); the inverse sends a
      closed subset [Q] to [z, x ↦ ∏_{p : sh_G = z} Q(p⁻¹ · x)].
    - Exercise [xca:ptd-conn-to-comp] ([to_compB_isEquiv]), remark
      [rem:GSet=SetHomG] ([GSet_eqv : G-Set ≃ ∑_S Hom(G, Σ_S)]) and
      definition [def:Gaction].
    - Exercise [xca:Ad-triv-abelian] ([Ad_triv_of_isAb],
      [isAb_of_Ad_triv]); for abelian [G], [(z = z) ≃ UG] is conjugation
      along any [p : sh_G = z], independent of [p] ([wconst_elim]).
    - Exercise [xca:Ad-princ-trivial] ([Ad_princ_of_trivial],
      [trivial_of_Ad_princ], [trivial_of_Ad_princ_TG]), with "trivial"
      meaning that [BG] is contractible.
    - Definition [def:finite-G-set] ([isFinGSet]).
    - Definition [def:transitiveGset] ([istrans]), lemma [lem:conistrans]
      ([conn_of_trans], [trans_of_conn]), lemma
      [lem:evisinjwhentransitive] ([evisinj_trans], [ev_Hom_isInj]), and
      its consequence for identifications ([hom_of_path_cancel],
      [ev_path_isInj]).
    - Definition [def:normal-action] ([isNormalG]) and exercise
      [xca:normal-action-equiv] ([normalG_from_one]).
    - Definitions [def:action] ([ActionIn], [ActionOn], [ActionIn_eqv])
      and [std-action]; the standard [Σ_n]-set and the [Σ_n]-set of
      decidable subsets; the footnote that the standard [Σ_n]-set is
      transitive for [n > 0] ([std_SGset_trans], by transpositions).

    - Example [ex:S2-acts-on-C3] ([S2onC3], with [EndoFam], [C3pt]).

    Left out (statements only, no proofs yet; time limit per result)
    - Exercise [xca:not-normal] ([xca_not_normal_stmt], with the wedge
      [WedgeS1S1] assumed a connected groupoid) and exercise
      [xca:AutC3] ([xca_AutC3_stmt], identifying [S2onC3] at [𝟚] with
      [C_3], which is [CG 2]: [CG k] is the cyclic group of order [k+1]).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Spaces.Circle Colimits.Pushout Spaces.Nat.Core.
From SymmetryBook Require Export Group.Group.

Local Open Scope uf_scope.

(** ** 5.2 Group actions ([G]-sets) *)

(** Definition [def:Gset]: [G-Set :≡ (BG → Set)]; the underlying set
    [X(sh_G)] and the action [p ·_X a :≡ trp_X(p)(a)]. *)
Definition GSet (G : Group) : Type := utype (BG G) -> SetU.

Definition el {G : Group} (X : GSet G) (z : utype (BG G)) : Type := fst (X z).

Definition el_isSet {G : Group} (X : GSet G) (z : utype (BG G)) : isSet (el X z)
  := snd (X z).

Definition act {G : Group} (X : GSet G) {z w : utype (BG G)} (p : z = w)
  : el X z -> el X w
  := trp (el X) p.

(** Example [def:trivGset]. *)
Definition trivG (G : Group) (S : SetU) : GSet G := fun _ => S.

(** Remark [rem:G-set-vs-set-bundle]: [G]-sets are the coverings over
    [BG] ([lem:Prop-Set-pointed-families] in 2.25); the two names reflect
    a different focus (informal). *)

(** Example [def:principaltorsor]: [P_y(z) :≡ (y = z)] and the principal
    torsor [P_{sh_G}]; [pathsp] is the map [eq:pathsp]. *)
Definition pathsp {G : Group} (y : utype (BG G)) : GSet G
  := fun z => ((y = z); BG_isGrpd G y z).

Definition princ (G : Group) : GSet G := pathsp (sh G).

Definition princ_underlying (G : Group) : el (princ G) (sh G) = USym G := refl.

(** Transport in [P_y] is post-composition. *)
Definition act_pathsp {G : Group} {y z w : utype (BG G)} (p : z = w) (q : y = z)
  : act (pathsp y) p q = p ⋅ q.
Proof. destruct p. exact refl. Defined.

(** Example [def:adjointrep]: [Ad_G(z) :≡ (z = z)], acting by
    conjugation. *)
Definition Ad (G : Group) : GSet G := fun z => ((z = z); BG_isGrpd G z z).

(** Footnote [ft:adjoint-transport]: transport in [Ad_G] is
    conjugation. *)
Definition act_Ad {G : Group} {z w : utype (BG G)} (p : z = w) (q : z = z)
  : act (Ad G) p q = p ⋅ (q ⋅ p⁻¹).
Proof. destruct p. exact (trans_1p q)^. Defined.

(** Example [ex:HomHGasGset]: [Hom(H,G)(y) :≡ Hom(H, mkgroup(BG_÷, y))]. *)
Definition HomG_set `{Funext} (H G : Group) : GSet G
  := fun y => (Hom H (regroup G y); Hom_isSet H (regroup G y)).

(** Identifications of [G]-sets from pointwise equivalences (univalence). *)
Definition path_SetU `{Univalence} {S T : SetU} (e : fst S ≃ fst T) : S = T
  := path_sigma_prop (fun X => isSet_isProp X) (etop e).

Definition path_GSet `{Univalence} {G : Group} {X Y : GSet G}
  (e : forall z, el X z ≃ el Y z) : X = Y
  := ptw_inv (fun z => path_SetU (e z)).

(** Exercise [xca:HomZGvsAdG]: [Ad_G = Hom(ℤ, G)]. *)
Definition Ad_HomZG `{Univalence} (G : Group) : Ad G = HomG_set ZZ G
  := @path_GSet _ G (Ad G) (HomG_set ZZ G)
       (fun y => Eqv_inv (Hom_ZZ_eqv (regroup G y))).

(** Definition [def:map-of-Gsets]. *)
Definition HomGs {G : Group} (X Y : GSet G) : Type
  := forall z : utype (BG G), el X z -> el Y z.

Definition HomGs_isSet `{Funext} {G : Group} (X Y : GSet G) : isSet (HomGs X Y)
  := Pi_isSet (fun z => Pi_isSet (fun _ => el_isSet Y z)).

(** Exercise [xca:equivariant-map-totalization]. *)
Section Totalization.

  Context `{Funext} {G : Group} (X Y : GSet G).

  Local Notation TX := {z : utype (BG G) & el X z}.
  Local Notation TY := {z : utype (BG G) & el Y z}.

  Definition tot_of_hom (h : HomGs X Y) : {f : TX -> TY & (fun w => fst w) = (fun w => fst (f w))}
    := ((fun w => (fst w; h (fst w) (snd w))); refl).

  Definition hom_of_tot (u : {f : TX -> TY & (fun w => fst w) = (fun w => fst (f w))})
    : HomGs X Y
    := fun z x => trp (el Y) (ptw (snd u) (z; x))⁻¹ (snd (fst u (z; x))).

  Definition tot_of_hom_of_tot (f1 : TX -> utype (BG G)) (f2 : forall w, el Y (f1 w))
    (e : (fun w => fst w) = f1)
    : tot_of_hom (hom_of_tot ((fun w => (f1 w; f2 w)); e)) = ((fun w => (f1 w; f2 w)); e).
  Proof. destruct e. exact refl. Defined.

  Definition HomGs_tot_eqv
    : HomGs X Y ≃ {f : TX -> TY & (fun w => fst w) = (fun w => fst (f w))}.
  Proof.
    refine (mkEqv tot_of_hom hom_of_tot (fun h => refl) _).
    intros [f e]. exact (tot_of_hom_of_tot (fun w => fst (f w)) (fun w => snd (f w)) e).
  Defined.

End Totalization.

(** Remark [rem:map-of-Gsets]: maps of [G]-sets are equivariant. *)
Definition HomGs_equivariant {G : Group} {X Y : GSet G} (f : HomGs X Y)
  {z w : utype (BG G)} (g : z = w) (x : el X z)
  : f w (act X g x) = act Y g (f z x).
Proof. destruct g. exact refl. Defined.

(** Definition [def:Gsubset]: [Sub_G(X) :≡ ∏_z Sub(X(z))], and the
    underlying [G]-set [X_P]. *)
Definition SubG {G : Group} (X : GSet G) : Type := forall z, el X z -> PropU.

(** [Sub_G(X)] is a set; footnote [ft:SubTotX]: uncurried it is
    [Sub(Tot(X))]. *)
Definition SubG_isSet `{Univalence} {G : Group} (X : GSet G) : isSet (SubG X)
  := Pi_isSet (fun z => Pi_isSet (fun _ => PropU_isSet)).

Definition GSet_sub {G : Group} (X : GSet G) (P : SubG X) : GSet G
  := fun z => ({x : el X z & fst (P z x)};
               Sigma_ntype 0 (el_isSet X z) (fun x => prop_ntype 0 _ (snd (P z x)))).

(** Exercise [xca:SubGX-closedSubXshG]: [G]-subsets are the subsets of
    the underlying set that are closed under the action. *)
Section SubGClosed.

  Context `{Univalence} {G : Group} (X : GSet G).

  Definition SubG_equivariant (P : SubG X) {z w : utype (BG G)} (g : z = w) (x : el X z)
    : P w (act X g x) = P z x.
  Proof. destruct g. exact refl. Defined.

  Definition closedSub : Type
    := {Q : el X (sh G) -> PropU &
         forall x, fst (Q x) -> forall g : USym G, fst (Q (act X g x))}.

  Definition SubG_to_closed (P : SubG X) : closedSub
    := (P (sh G); fun x q g => trp (fun T : PropU => fst T)
                                   (SubG_equivariant P g x)⁻¹ q).

  Definition closed_to_SubG (Q : closedSub) : SubG X
    := fun z x => ((forall p : sh G = z, fst (fst Q (act X p⁻¹ x)));
                   Pi_isProp (fun p => snd (fst Q (act X p⁻¹ x)))).

  Definition SubG_closed_eqv : SubG X ≃ closedSub.
  Proof.
    refine (mkEqv SubG_to_closed closed_to_SubG _ _).
    - intro P. apply ptw_inv. intro z. apply ptw_inv. intro x.
      refine (path_PropU _ _).
      + intro h. refine (ptrunc_rec (snd (P z x)) _ (snd (BG_isConn G) (sh G) z)).
        intro p. exact (trp (fun T : PropU => fst T) (SubG_equivariant P p⁻¹ x) (h p)).
      + intros h p. exact (trp (fun T : PropU => fst T) (SubG_equivariant P p⁻¹ x)⁻¹ h).
    - intros [Q c].
      refine (path_sigma_prop (fun Q' => Pi_isProp (fun x => Pi_isProp (fun _ =>
                Pi_isProp (fun g => snd (Q' (act X g x)))))) _).
      apply ptw_inv. intro x. refine (path_PropU _ _).
      + intro h. exact (h refl).
      + intros q g. exact (c x q g⁻¹).
  Defined.

End SubGClosed.

(** Exercise [xca:ptd-conn-to-comp] (generalizing [to_comp] of
    Section 4.4). *)
Section PtdConnToComp.

  Context `{Funext} (X : Ustar) (cX : isConn (utype X)) {B : Type} (b : B).

  Definition compB : Ustar := (component B b; (b; trunc refl)).

  Definition to_compB (k : X →* (B; b)) : X →* compB
    := ((fun x => (fst k x; ptrunc_rec ptrunc_isProp
                              (fun q : pt X = x => trunc (ap (fst k) q ⋅ snd k))
                              (snd cX (pt X) x)) : component B b);
        @path_sigma_prop B (fun x => ptrunc (b = x)) (fun _ => ptrunc_isProp)
          (b; trunc refl) (fst k (pt X); _) (snd k)).

  Definition from_compB (m : X →* compB) : X →* (B; b)
    := ((fun x => fst (fst m x)); ap fst (snd m)).

  Definition to_compB_isEquiv : isEquiv to_compB.
  Proof.
    refine (iso_to_isEquiv _ from_compB _ _).
    - intros [k0 kp]. unfold from_compB, to_compB; cbn.
      exact (ap (fun r => ((k0; r) : X →* (B; b)))
               (@ap_fst_pathpair B (fun x => ptrunc (b = x)) _ _ _ _ kp _)).
    - intros [m0 mp].
      refine (eqinv (snd (ptw_star _ _)) _).
      unshelve refine (_; _).
      + intro x. apply (path_sigma_prop (fun _ => ptrunc_isProp)). exact refl.
      + pose (e := isInj_ap_isEquiv (fst_isInj (fun x : B => @ptrunc_isProp (b = x)))
                     (b; trunc refl) (m0 (pt X))).
        refine ((eqinv_l e _)^ @ ap (eqinv e) _ @ eqinv_l e _).
        refine (ap_trans _ _ _ @ _).
        exact (ap011 (fun r s => r ⋅ s) (ap_fst_pathpair _ _) (ap_fst_pathpair _ _)).
  Defined.

End PtdConnToComp.

(** Remark [rem:GSet=SetHomG]: [G-Set ≃ ∑_{S:Set} Hom(G, Σ_S)], and
    definition [def:Gaction]. *)
Definition Gaction `{Univalence} (G : Group) (S : SetU) : Type := Hom G (SG_S S).

Definition GSet_eqv `{Univalence} (G : Group)
  : GSet G ≃ {S : SetU & Gaction G S}
  := Eqv_comp (BGtotype_12 G (A := SetU)) (BGtotype_34 G SetU_isGrpd).

(** Exercise [xca:Ad-triv-abelian]. *)
Section AdTrivAbelian.

  Context `{Univalence} (G : Group).

  (** For abelian [G], conjugation [(z = z) → U G] along [p : sh = z] does
      not depend on [p]. *)
  Definition conj_to_sh (z : utype (BG G)) (p : sh G = z) (q : z = z) : USym G
    := p⁻¹ ⋅ (q ⋅ p).

  Definition conj_to_sh_isEquiv (z : utype (BG G)) (p : sh G = z) : isEquiv (conj_to_sh z p).
  Proof.
    refine (iso_to_isEquiv _ (fun g => p ⋅ (g ⋅ p⁻¹)) _ _); destruct p; intro q; cbn.
    - exact (ap (fun r => r ⋅ refl) (trans_1p q) @ trans_1p q).
    - exact (ap (fun r => r ⋅ refl) (trans_1p q) @ trans_1p q).
  Defined.

  Definition conj_wconst (a : isAb G) (z : utype (BG G))
    : wconst (fun p : sh G = z => ((conj_to_sh z p; conj_to_sh_isEquiv z p) : (z = z) ≃ USym G)).
  Proof.
    intros p p'. destruct p'.
    apply path_Eqv. apply ptw_inv. intro q. unfold conj_to_sh; cbn.
    exact (ap (fun r => p⁻¹ ⋅ r) (a q p) @ trans_assoc q p p⁻¹
           @ ap (fun r => r ⋅ q) (trans_pV p) @ (trans_1p q)^).
  Defined.

  Definition Ad_triv_of_isAb (a : isAb G) : Ad G = trivG G (USym G; USym_isSet G).
  Proof.
    refine (@path_GSet _ G (Ad G) (trivG G (USym G; USym_isSet G)) _). intro z.
    exact (wconst_elim (Eqv_sets_isSet (USym_isSet G)) (conj_wconst a z)
             (snd (BG_isConn G) (sh G) z)).
  Defined.

  Definition isAb_of_Ad_triv (e : Ad G = trivG G (USym G; USym_isSet G)) : isAb G.
  Proof.
    pose (f := (fun z => trp (fun T : SetU => fst T) (ptw e z))
               : HomGs (Ad G) (trivG G (USym G; USym_isSet G))).
    assert (c : forall g q : USym G, g ⋅ (q ⋅ g⁻¹) = q).
    { intros g q.
      pose (t := trp_isEquiv (fun T : SetU => fst T) (ptw e (sh G))).
      refine ((eqinv_l t _)^ @ ap (eqinv t) _ @ eqinv_l t _).
      refine (ap (f (sh G)) (act_Ad g q)^ @ HomGs_equivariant f g q @ _).
      exact (ptw (trp_const g) _). }
    intros g h.
    refine (_ @ (ap (fun r => r ⋅ g) (c g h)^ @ (trans_assoc g (h ⋅ g⁻¹) g)^
                 @ ap (fun r => g ⋅ r) (trans_assoc g g⁻¹ h)^
                 @ ap (fun r => g ⋅ (h ⋅ r)) (trans_pV g)
                 @ ap (fun r => g ⋅ r) (trans_1p h))^).
    exact refl.
  Defined.

End AdTrivAbelian.

(** Exercise [xca:Ad-princ-trivial], with "[G] is trivial" expressed as
    contractibility of [BG] (equivalently [G = 𝟙], by [path_Group_contr]). *)
Section AdPrincTrivial.

  Context `{Univalence} (G : Group).

  Definition Ad_princ_of_trivial (c : isContr (utype (BG G))) : Ad G = princ G.
  Proof.
    refine (@path_GSet _ G (Ad G) (princ G) _). intro z.
    pose (pc := fun x y : utype (BG G) =>
                  isProp_inhabited_isContr (prop_is_set (isContr_isProp' c) x y)
                    (isContr_isProp' c x y)).
    exact (_; map_contr_isEquiv (pc z z) (pc (sh G) z) (fun _ => isContr_isProp' c _ _)).
  Defined.

  Definition trivial_of_Ad_princ (e : Ad G = princ G) : isContr (utype (BG G))
    := (sh G; fun z => trp (fun T : SetU => fst T) (ptw e z) refl).

  Definition trivial_of_Ad_princ_TG (e : Ad G = princ G) : G = TG
    := path_Group_contr (trivial_of_Ad_princ e) TG_contr.

End AdPrincTrivial.

(** Definition [def:finite-G-set]. *)
Definition isFinGSet {G : Group} (X : GSet G) : Type := isFinSet (el X (sh G)).

(** ** 5.2.1 Transitive [G]-sets *)

(** Definition [def:transitiveGset]. *)
Definition istrans {G : Group} (X : GSet G) : Type
  := Ex (fun x : el X (sh G) => forall y : el X (sh G), Ex (fun g : USym G => x = act X g y)).

(** The equivalent condition [eq:Gset-trans-gen] over all [z : BG] is not
    formalized separately. *)

Definition TotG {G : Group} (X : GSet G) : Type := {z : utype (BG G) & el X z}.

Definition tot_path_act {G : Group} (X : GSet G) {z w : utype (BG G)} (p : z = w)
  (a : el X z) : ((z; a) : TotG X) = (w; act X p a).
Proof. destruct p. exact refl. Defined.

Definition act_ap_fst {G : Group} (X : GSet G) {u v : TotG X} (r : u = v)
  : act X (ap fst r) (snd u) = snd v.
Proof. destruct r. exact refl. Defined.

(** Lemma [lem:conistrans]. *)
Definition conn_of_trans {G : Group} (X : GSet G) (t : istrans X) : isConn (TotG X).
Proof.
  refine (ptrunc_rec ptrunc_isProp (fun w => trunc ((sh G; fst w) : TotG X)) t; _).
  assert (h : forall a b : el X (sh G), ptrunc (((sh G; a) : TotG X) = (sh G; b))).
  { intros a b.
    refine (ptrunc_rec ptrunc_isProp _ t). intros [x hx].
    refine (ptrunc_rec ptrunc_isProp _ (hx a)). intros [g eg].
    refine (ptrunc_rec ptrunc_isProp _ (hx b)). intros [k ek].
    apply trunc.
    exact ((tot_path_act X k b)^ ⋅ (ap (fun c => (sh G; c) : TotG X) (ek ⋅ eg⁻¹)
                                     ⋅ tot_path_act X g a)). }
  intros [z a] [w b].
  refine (ptrunc_rec ptrunc_isProp _ (snd (BG_isConn G) z (sh G))). intro p.
  refine (ptrunc_rec ptrunc_isProp _ (snd (BG_isConn G) w (sh G))). intro q.
  refine (ptrunc_rec ptrunc_isProp _ (h (act X p a) (act X q b))). intro r.
  exact (trunc ((tot_path_act X q b)⁻¹ ⋅ (r ⋅ tot_path_act X p a))).
Defined.

Definition trans_of_conn {G : Group} (X : GSet G) (c : isConn (TotG X)) : istrans X.
Proof.
  refine (ptrunc_rec ptrunc_isProp _ (fst c)). intros [z a].
  refine (ptrunc_rec ptrunc_isProp _ (snd (BG_isConn G) z (sh G))). intro p.
  apply trunc. refine (act X p a; _). intro y.
  refine (ptrunc_rec ptrunc_isProp _ (snd c (sh G; y) (sh G; act X p a))). intro r.
  exact (trunc (ap fst r; (act_ap_fst X r)⁻¹)).
Defined.

(** Lemma [lem:evisinjwhentransitive]. *)
Definition evisinj_trans `{Funext} {G : Group} {X Y : GSet G} (t : istrans X)
  {z : utype (BG G)} (x : el X z) (f f' : HomGs X Y) (h : f z x = f' z x) : f = f'.
Proof.
  apply ptw_inv. intro w. apply ptw_inv. intro x'.
  refine (ptrunc_rec (el_isSet Y w _ _) _ (snd (conn_of_trans X t) (z; x) (w; x'))).
  intro r.
  refine (ap (f w) (act_ap_fst X r)⁻¹ @ _ @ ap (f' w) (act_ap_fst X r)).
  exact (HomGs_equivariant f _ x @ ap (act Y (ap fst r)) h @ (HomGs_equivariant f' _ x)^).
Defined.

Definition ev_Hom {G : Group} {X Y : GSet G} {z : utype (BG G)} (x : el X z)
  : HomGs X Y -> el Y z := fun f => f z x.

Definition ev_Hom_isInj `{Funext} {G : Group} {X Y : GSet G} (t : istrans X)
  {z : utype (BG G)} (x : el X z) : isInj (@ev_Hom G X Y z x)
  := cancel_isInj (el_isSet Y z) (fun f f' h => evisinj_trans t x f f' h).

(** Identifications of [G]-sets give maps of [G]-sets. *)
Definition hom_of_path {G : Group} {X Y : GSet G} (e : X = Y) : HomGs X Y
  := fun z => trp (fun T : SetU => fst T) (ptw e z).

(** Exercise [xca:not-normal] (statement only), for the group of the
    wedge [S1 ∨ S1] (the pushout of the two base points, assumed a
    connected groupoid here): a transitive [G]-set [X] with [X = X]
    contractible, for which [ev_x] is not surjective. *)
Definition WedgeS1S1 : Type := Pushout (fun _ : True => base) (fun _ : True => base).

Definition xca_not_normal_stmt `{Univalence} : Type
  := forall (c : isConn WedgeS1S1) (g : isGrpd WedgeS1S1),
       let G := mkgroup (WedgeS1S1; (pushl base; (c; g))) in
       {X : GSet G & istrans X × isContr (X = X)
                     × {x : el X (sh G) & ¬ isSurj (fun e : X = X => hom_of_path e (sh G) x)}}.

(** Definition [def:normal-action]. *)
Definition ev_path {G : Group} {X : GSet G} {z : utype (BG G)} (x : el X z)
  : (X = X) -> el X z := fun e => hom_of_path e z x.

Definition isNormalG {G : Group} (X : GSet G) : Type
  := istrans X × (forall z (x : el X z), isEquiv (ev_path x)).

(** Exercise [xca:normal-action-equiv]. *)
Definition normalG_from_one `{Funext} {G : Group} (X : GSet G) (t : istrans X)
  {z : utype (BG G)} (x : el X z) (h : isEquiv (ev_path x)) : isNormalG X.
Proof.
  refine (t; _). intros w x'.
  refine (ptrunc_rec (isEquiv_isProp _) _ (snd (conn_of_trans X t) (z; x) (w; x'))).
  intro r.
  refine (isEquiv_homotopic (act X (ap fst r) ∘ ev_path x) _ _
            (comp_isEquiv h (trp_isEquiv (el X) (ap fst r)))).
  intro e. unfold ev_path.
  exact ((HomGs_equivariant (hom_of_path e) (ap fst r) x)^
         @ ap (hom_of_path e w) (act_ap_fst X r)).
Defined.

(** Via univalence, [X = Y] is a subtype of [Hom_G(X,Y)]: [hom_of_path]
    is injective, hence so is evaluation [ev_x : (X = Y) → Y(z)] for
    transitive [X]. *)
Definition SetU_path_cancel `{Univalence} {S T : SetU} (p q : S = T)
  (h : trp (fun T : SetU => fst T) p = trp (fun T : SetU => fst T) q) : p = q.
Proof.
  pose (j := isInj_ap_isEquiv (fst_isInj (fun X => isSet_isProp X)) S T).
  refine ((eqinv_l j p)^ @ ap (eqinv j) _ @ eqinv_l j q).
  refine ((etop_ptoe _)^ @ ap etop _ @ etop_ptoe _).
  apply path_Eqv. exact ((trp_ap idmap fst p)^ @ h @ trp_ap idmap fst q).
Defined.

Definition hom_of_path_cancel `{Univalence} {G : Group} {X Y : GSet G} (e e' : X = Y)
  (h : hom_of_path e = hom_of_path e') : e = e'.
Proof.
  refine ((eqinv_l (funext X Y) e)^ @ ap ptw_inv _ @ eqinv_l (funext X Y) e').
  apply ptw_inv. intro z. apply SetU_path_cancel. exact (ptw h z).
Defined.

Definition ev_path_isInj `{Univalence} {G : Group} {X Y : GSet G} (t : istrans X)
  {z : utype (BG G)} (x : el X z) : isInj (fun e : X = Y => hom_of_path e z x)
  := cancel_isInj (el_isSet Y z)
       (fun e e' h => hom_of_path_cancel e e' (evisinj_trans t x _ _ h)).

(** ** 5.2.2 Actions in a type *)

(** Definition [def:action]: an action of [G] in [A] is a map [BG → A];
    an action on [a : A] (for a groupoid [A]) is a homomorphism
    [G → Aut_A(a)], and these correspond. *)
Definition ActionIn (G : Group) (A : Type) : Type := utype (BG G) -> A.

Definition ActionOn `{Funext} (G : Group) {A : Type} (gA : isGrpd A) (a : A) : Type
  := Hom G (AutG gA a).

Definition ActionIn_eqv `{Funext} (G : Group) {A : Type} (gA : isGrpd A)
  : ActionIn G A ≃ {a : A & ActionOn G gA a}
  := Eqv_comp (BGtotype_12 G (A := A)) (BGtotype_34 G gA).

(** Definition [std-action]: the standard action of [G] on [sh_G]. *)
Definition std_action (G : Group) : ActionIn G (utype (BG G)) := idmap.

(** The standard [Σ_n]-set and the action on decidable subsets of
    [Fin n]. *)
Definition std_SGset `{Univalence} (n : ℕ) : GSet (SG n) := fun A => fst A.

(** The footnote: the standard [Σ_n]-set is transitive for [n > 0];
    the transposition [(y x)] carries [y] to [x]. *)
Definition std_SGset_trans_stmt `{Univalence} : Type
  := forall n : ℕ, (0 < n)%nat -> istrans (std_SGset n).

Definition std_SGset_trans `{Univalence} : std_SGset_trans_stmt.
Proof.
  intros [|m] l; [destruct (not_lt_zero_r _ l)|].
  apply trunc. refine (inr tt; _). intro y. apply trunc.
  pose (σ := transpEqv (finset_isDecSet (comp_isFinSet (sh (SG m.+1)))) y (inr tt)).
  refine (perm_of (sh (SG m.+1)) σ; _).
  refine ((transp_a (sh (SG m.+1)) y (inr tt))^ @ _).
  refine ((ap (fun e => fst e y) (ptoe_etop σ))^ @ _).
  refine ((ap (fun q => ptoe q y) (ap_fst_fst_perm_of (sh (SG m.+1)) σ))^ @ _).
  exact (ptoe_ap (fun B => fst (fst B)) (perm_of (sh (SG m.+1)) σ) y).
Defined.

Definition decsub_SGset `{Univalence} (n : ℕ) : GSet (SG n)
  := fun A => ((fst (fst A) -> Bool); Pi_isSet (fun _ => isSet_bool)).

(** Example [ex:S2-acts-on-C3]: the action of [Σ_2] on [C_3], with
    [G(S) :≡ Aut_{∑_{X:Set} S → X → X}(𝟙 ⨿ S, f)], [f_s(inl 0) :≡ inr s],
    [f_s(inr s) :≡ inr(swap s)], [f_s(inr(swap s)) :≡ inl 0]. *)
Section S2actsC3.

  Context `{Univalence}.

  Definition EndoFam (S : Type) : Type := {X : SetU & S -> fst X -> fst X}.

  Definition EndoFam_isGrpd (S : Type) : isGrpd (EndoFam S)
    := Sigma_ntype 1 SetU_isGrpd
         (fun X => set_ntype 1 (Pi_isSet (fun _ => Pi_isSet (fun _ => snd X)))).

  Definition BSG2_FinSet (S : BSG2) : FinSet_n 2
    := (fst S; ptrunc_rec ptrunc_isProp (fun q => trunc (ap fst q)) (snd S)).

  Definition f3 (S : BSG2) (s : el2 S) (x : True ⨿ el2 S) : True ⨿ el2 S
    := match x with
       | inl _ => inr s
       | inr s' => match el2_dec S s' s with
                   | inl _ => inr (other (BSG2_FinSet S) s)
                   | inr _ => inl triv
                   end
       end.

  Definition C3pt (S : BSG2) : EndoFam (el2 S)
    := ((True ⨿ el2 S; sum_isSet (prop_is_set True_isProp) (el2_isSet S)); f3 S).

  Definition S2onC3 (S : BSG2) : Group := AutG (EndoFam_isGrpd (el2 S)) (C3pt S).

  (** Exercise [xca:AutC3] (statement only): this action identifies
      [BΣ_2] with the component of [C_3] in [Group]. *)
  Definition xca_AutC3_stmt : Type
    := (S2onC3 (sh (SG 2)) = CG 2)
       × (forall m : forall S, ptrunc (CG 2 = S2onC3 S),
            isEquiv (fun S : BSG2 => ((S2onC3 S; m S) : component Group (CG 2)))).

End S2actsC3.
