(** * Section 9.4 The action on the set of subgroups

    Part of Chapter 9 ([subgroups.tex]); see [Subgroups.v] for an
    overview of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Size issue: [Mono(G)] and [Sub(G)] live in a larger universe than
      [Set_U], so the [G]-sets [Mono(G)] and [Sub(G)] are families of types
      over [BG] ([MonoFam], [SubFam]) with transport as action.  As in the
      book, [MonoFam G (sh G)] and [SubFam G (sh G)] are [Mono] and
      [SubGrp] of [mkgroup(BG_÷, sh_G)], which for [SubFam] is [SubGrp G]
      by definition.
    - Remark [rem:action-Mono(G)] ([moveshape], [act_MonoFam]; on
      symmetries [USymf_moveshape]).
    - Lemma [lem:conj-abstract] / exercise [xca:conj-abstract]: the core,
      [USymf_conj_mono]: the conjugate monomorphism has [USym] the
      conjugate [g (USymf f h) g⁻¹].  The transfer of the family to an
      [abstr(G)]-set through [actions_eqv] (7.6) is not stated (size
      issue).
    - The action of [Sub(G)] ([act_SubFam]); the map [E] ([Emono], [Ez],
      with the transitive [G]-set [fibGSet] of fibers of a monomorphism,
      [fibGSet_trans]).

    - Remark [rem:typeofsubgpstrivifab] ([rem_typeofsubgpstrivifab]:
      [isAb_conj], [conj_isAb], and the trivial action for abelian [G]).
      NOTE: the book's converse (trivial [Mono(G)] implies abelian) fails
      for [Q_8], all of whose subgroups are normal; the statement is
      restated with only the implication.

    - Exercise [xca:Sub(Sigma3)], first part ([xca_Sub_Sigma3]): the
      trivial and the full subgroup ([trivSub], [fullSub]) are fixed by
      the action, so transitivity makes them equal and [BG] contractible;
      conversely all subgroups of a trivial group are equal
      ([Sub_contr_eq]).

    Left out (statements only)
    - That [E] is an equivalence (with [lem:SubG=MonoG], Section 5.3);
      the orbit structure of [Sub(Σ_3)] in [xca:Sub(Sigma3)] is not
      formalized.
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core.
From SymmetryBook Require Export Subgroups.S03_Images.

Local Open Scope uf_scope.

(** ** 9.4 The action on the set of subgroups *)

(** The definition of the [G]-set [Mono(G)], [z ↦ Mono(mkgroup(BG_÷, z))].
    Size issue: [Mono(G)] lives in a larger universe than the sets of
    [Set_U], so we take it as a family of types over [BG] with transport
    as action, not as an element of [G-Set]. *)
Definition MonoFam (G : Group) (z : utype (BG G)) : Type := Mono (regroup G z).

(** Moving the shape: [mkgroup(id_BG, p⁻¹) : Hom(mkgroup(BG_÷, z),
    mkgroup(BG_÷, z'))] for [p : z = z']. *)
Definition moveshape (G : Group) {z z' : utype (BG G)} (p : z = z')
  : Hom (regroup G z) (regroup G z')
  := @mkhom (regroup G z) (regroup G z') (idmap; p⁻¹).

(** Remark [rem:action-Mono(G)]: the action of [Mono(G)] along [p] is
    postcomposition with [mkgroup(id_BG, p⁻¹)], called conjugation; on
    symmetries this is [q ↦ p q p⁻¹]. *)
Definition act_MonoFam `{fe : Funext} {G : Group} {z z' : utype (BG G)} (p : z = z')
  (H : Group) (f : Hom H (regroup G z)) (m : ismono f) (m' : ismono (compG (moveshape G p) f))
  : trp (MonoFam G) p (H; (f; m)) = (H; (compG (moveshape G p) f; m')).
Proof.
  destruct p. apply (ap (fun w => (H; w) : MonoFam G z)).
  exact (path_sigma_prop (fun k => isInj_isProp _ (USymf k))
             (u := (f; m)) (v := (compG (moveshape G refl) f; m')) (compG_idG_l f)^).
Defined.

Definition loops_moveshape {X : Type} {z z' : X} (p : z = z') (q : z = z)
  : loops_fun ((idmap; p⁻¹) : ((X; z) : Ustar) →* (X; z')) q = p ⋅ (q ⋅ p⁻¹).
Proof. destruct p. exact (ap (fun r => r ⋅ refl) (ap_idmap q)). Defined.

Definition USymf_moveshape (G : Group) {z z' : utype (BG G)} (p : z = z') (q : z = z)
  : USymf (moveshape G p) q = p ⋅ (q ⋅ p⁻¹)
  := loops_moveshape p q.

(** Lemma [lem:conj-abstract] and exercise [xca:conj-abstract]: the core
    of the lemma, that the conjugate [(H, mkgroup(id, g⁻¹) f)] has
    [USym] the abstract conjugate [conj^g ∘ USymf f]
    ([USymf_conj_mono]).  The transfer of the whole family [Mono(G)] to
    an [abstr(G)]-set through [actions_eqv] (7.6) is not stated, by the
    size issue above. *)
Definition USymf_conj_mono `{fe : Funext} {G H : Group} (f : Hom H (regroup G (sh G)))
  (g : USym G) (h : USym H)
  : USymf (compG (moveshape G g) f) h = g ⋅ (USymf f h ⋅ g⁻¹)
  := ap (fun u => u h) (USym_compose f (moveshape G g)) @ USymf_moveshape G g (USymf f h).

(** Remark [rem:typeofsubgpstrivifab]: [G] is abelian iff all
    conjugations are trivial, and then the action of [Mono(G)] is
    trivial.  NOTE: the book also claims the converse, that [G] is
    abelian if the [G]-set [Mono(G)] is trivial.  That fails for the
    quaternion group [Q_8]: all its subgroups are normal, so conjugation
    fixes every element of the set [Mono(Q_8)], but [Q_8] is not
    abelian.  The [G]-set [Mono(G)] is trivial iff all subgroups are
    normal.  We state and prove only the implication. *)
Definition rem_typeofsubgpstrivifab_stmt `{fe : Funext} : Type
  := forall G : Group,
       (isAb G <-> forall g q : USym G, g ⋅ (q ⋅ g⁻¹) = q)
       × (isAb G -> forall (g : USym G) (m : MonoFam G (sh G)), trp (MonoFam G) g m = m).

Definition isAb_conj {G : Group} (ab : isAb G) (g q : USym G) : g ⋅ (q ⋅ g⁻¹) = q
  := trans_assoc _ _ _ @ ap (fun r => r ⋅ g⁻¹) (ab g q) @ (trans_assoc _ _ _)^
     @ ap (fun r => q ⋅ r) (trans_Vp g) @ trans_1p q.

Definition conj_isAb {G : Group} (c : forall g q : USym G, g ⋅ (q ⋅ g⁻¹) = q) : isAb G
  := fun g h => (trans_1p (g ⋅ h))^ @ ap (fun r => (g ⋅ h) ⋅ r) (trans_pV g)^
                @ trans_assoc _ _ _ @ ap (fun r => r ⋅ g) (trans_assoc _ _ _)^
                @ ap (fun r => r ⋅ g) (c g h).

Definition rem_typeofsubgpstrivifab `{fe : Funext} : rem_typeofsubgpstrivifab_stmt.
Proof.
  intro G. refine ((isAb_conj, conj_isAb); _).
  intros ab g [H [f mf]].
  assert (E : compG (moveshape G g) f = f).
  { apply USymf_cancel. apply ptw_inv. intro h0.
    exact (USymf_conj_mono f g h0 @ isAb_conj ab g (USymf f h0)). }
  refine (act_MonoFam g H f mf (trp ismono E^ mf) @ _).
  exact (ap (fun w => (H; w) : MonoFam G (sh G))
            (path_sigma_prop ismono_isProp (u := (_; trp ismono E^ mf)) (v := (f; mf)) E)).
Defined.

(** The definition of the [G]-set [Sub(G)], [z ↦ Sub(mkgroup(BG_÷, z))],
    again as a family of types (size issue); [SubGrp] is a set
    ([SubGrp_isSet], Section 5.3).  The action leaves [X] alone and
    moves the point. *)
Definition SubFam (G : Group) (z : utype (BG G)) : Type := SubGrp (regroup G z).

Definition act_SubFam {G : Group} {z z' : utype (BG G)} (p : z = z') (X : GSet G)
  (x : el X z) (t : istrans (G := regroup G z) X) (t' : istrans (G := regroup G z') X)
  (ht : forall t1 t2 : istrans (G := regroup G z') X, t1 = t2)
  : trp (SubFam G) p (X; (x; t)) = (X; (act X p x; t')).
Proof. destruct p. exact (ap (fun s => (X; (x; s)) : SubFam G z) (ht t t')). Defined.

(** The definition of [E : Hom_G(Mono(G), Sub(G))],
    [E_z(H, f) :≡ ((Bf)⁻¹, (sh_H, Bf_pt))]: the fibers of [Bf] form a
    transitive [G]-set, pointed at [(sh_H, Bf_pt)].  [E_{sh_G}] is the
    inverse of the map [F] of [lem:SubG=MonoG] (Section 5.3); that [E] is
    an equivalence is left out with that lemma. *)
Section EMap.

  Context `{ua : Univalence} {H K : Group} (f : Hom H K) (m : ismono f).

  Local Notation k0 := (fst (Bf f)).
  Local Notation kp := (snd (Bf f)).

  Definition fibGSet : GSet K := fun w => (fiber k0 w; ismono_isCovering f m w).

  Definition act_fibGSet {w w' : utype (BG K)} (g : w = w') (z : utype (BG H)) (p : w = k0 z)
    : act fibGSet g ((z; p) : fiber k0 w) = ((z; g^ @ p) : fiber k0 w').
  Proof. destruct g. exact (ap (fun q => (z; q) : fiber k0 w) (concat_1p p)^). Defined.

  Definition fibGSet_trans : istrans fibGSet.
  Proof.
    apply trunc. exists ((sh H; kp) : fiber k0 (sh K)).
    intros [z p].
    refine (ptrunc_rec ptrunc_isProp _ (snd (BG_isConn H) (sh H) z)). intro q.
    destruct q. apply trunc. exists (p @ kp^).
    refine (_ @ (act_fibGSet _ _ _)^).
    apply (ap (fun r => (sh H; r) : fiber k0 (sh K))).
    exact ((ap (fun r => r @ p) (inv_pp p kp^) @ concat_pp_p _ _ _
            @ ap (fun r => (kp^)^ @ r) (concat_Vp p) @ concat_p1 _ @ inv_V kp)^).
  Defined.

  Definition Emono : SubGrp K := (fibGSet; ((sh H; kp); fibGSet_trans)).

End EMap.

Definition Ez `{ua : Univalence} {G : Group} (z : utype (BG G)) : MonoFam G z -> SubFam G z
  := fun w => Emono (fst (snd w)) (snd (snd w)).

(** Exercise [xca:Sub(Sigma3)] (first part, proved below): [Sub(G)] is
    transitive iff [G] is trivial.  The orbit structure of [Sub(Σ_3)] is
    not formalized. *)
Definition xca_Sub_Sigma3_stmt `{ua : Univalence} : Type
  := forall G : Group,
       Ex (fun x : SubFam G (sh G) =>
             forall y : SubFam G (sh G), Ex (fun g : USym G => x = trp (SubFam G) g y))
       <-> isContr (utype (BG G)).

(** Proof of the first part of [xca:Sub(Sigma3)].  The trivial subgroup
    ([trivSub], the principal torsor) and the full subgroup ([fullSub])
    are defined at every [z : BG], so they are fixed by the action
    ([trp_section]).  If [Sub(G)] is transitive they are equal, so
    [sh_G = z] is [‖sh_G = z‖] for every [z].  (The full subgroup is
    [w ↦ ‖z = w‖], a proposition in the universe of [BG].)  Conversely, if [BG] is
    contractible, any two subgroups are equal ([Sub_contr_eq]). *)
Definition trp_section {A : Type} (P : A -> Type) (s : forall a, P a) {a b : A} (p : a = b)
  : trp P p (s a) = s b
  := match p with refl => refl end.

Definition trp_paths_r {A : Type} {z a b : A} (p : a = b) (q : z = a)
  : trp (fun w => z = w) p q = q @ p.
Proof. destruct p. exact (concat_p1 q)^. Defined.

Definition contr_contr_eqv {X Y : Type} (cX : isContr X) (cY : isContr Y) : X ≃ Y
  := mkEqv (fun _ => fst cY) (fun _ => fst cX) (snd cX) (snd cY).

Section SubSigma3.

  Context `{ua : Univalence} {G : Group}.

  Definition trivSub (z : utype (BG G)) : SubFam G z.
  Proof.
    refine ((fun w => ((z = w); BG_isGrpd G z w)); (refl; _)).
    apply trunc. exists refl. intro y. apply trunc. exists y⁻¹.
    exact (trp_paths_r y⁻¹ y @ concat_pV y)^.
  Defined.

  Definition fullSub (z : utype (BG G)) : SubFam G z.
  Proof.
    refine ((fun w => (ptrunc (z = w); prop_is_set ptrunc_isProp)); (trunc refl; _)).
    apply trunc. exists (trunc refl). intro y. apply trunc. exists refl. exact (ptrunc_isProp _ _).
  Defined.

  Definition Sub_trans_contr
    : Ex (fun x : SubFam G (sh G) =>
            forall y : SubFam G (sh G), Ex (fun g : USym G => x = trp (SubFam G) g y))
      -> isContr (utype (BG G)).
  Proof.
    refine (ptrunc_rec (isContr_isProp _) _). intros [x hx].
    refine (ptrunc_rec (isContr_isProp _) _ (hx (trivSub (sh G)))). intros [g1 e1].
    refine (ptrunc_rec (isContr_isProp _) _ (hx (fullSub (sh G)))). intros [g2 e2].
    pose (E := (e1 @ trp_section (SubFam G) trivSub g1)^ @ e2 @ trp_section (SubFam G) fullSub g2
               : trivSub (sh G) = fullSub (sh G)).
    pose (T := fun z => ap (fun s : SubGrp G => fst (sg_X s z)) E : (sh G = z) = ptrunc (sh G = z)).
    exact (sh G; fun z => trp (fun A : Type => A) (T z)⁻¹ (snd (BG_isConn G) (sh G) z)).
  Defined.

  Definition Sub_contr_eq (c : isContr (utype (BG G))) (S : SubGrp G) : trivSub (sh G) = S.
  Proof.
    destruct S as [Y [y0 t]].
    pose (cp := fun z => isProp_inhabited_isContr (prop_is_set (isContr_isProp' c) (sh G) z)
                           (isContr_isProp' c (sh G) z)).
    assert (pY : isProp (el Y (sh G))).
    { intros y1 y2.
      refine (ptrunc_rec (el_isSet Y _ _ _) _ t). intros [x hx].
      refine (ptrunc_rec (el_isSet Y _ _ _) _ (hx y1)). intros [g1 e1].
      refine (ptrunc_rec (el_isSet Y _ _ _) _ (hx y2)). intros [g2 e2].
      exact (ap (fun g => act Y g y1) (isContr_isProp' (cp (sh G)) refl g1) @ e1^ @ e2
             @ ap (fun g => act Y g y2) (isContr_isProp' (cp (sh G)) g2 refl)). }
    pose (cY := fun z => isContr_Eqv (idtoeqv (ap (el Y) (isContr_isProp' c (sh G) z)))
                           (isProp_inhabited_isContr pY y0)).
    refine (SubGrp_path _ (pY _ _)).
    apply ptw_inv. intro z.
    exact (path_sigma_prop (fun _ => isSet_isProp _)
             (u := ((sh G = z); BG_isGrpd G (sh G) z)) (v := Y z)
             (etop (contr_contr_eqv (cp z) (cY z)))).
  Defined.

End SubSigma3.

Definition xca_Sub_Sigma3 `{ua : Univalence} : xca_Sub_Sigma3_stmt
  := fun G => (Sub_trans_contr,
               fun c => trunc (trivSub (sh G); fun y => trunc (refl; Sub_contr_eq c y))).
