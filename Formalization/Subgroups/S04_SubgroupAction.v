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

    Left out (statements only)
    - That [E] is an equivalence (with [lem:SubG=MonoG], Section 5.3);
      exercise [xca:Sub(Sigma3)], first part ([xca_Sub_Sigma3_stmt]); the
      orbit structure of [Sub(Σ_3)] is not formalized.
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

(** Exercise [xca:Sub(Sigma3)] (statement only, first part): [Sub(G)] is
    transitive iff [G] is trivial.  The orbit structure of [Sub(Σ_3)] is
    not formalized. *)
Definition xca_Sub_Sigma3_stmt `{ua : Univalence} : Type
  := forall G : Group,
       Ex (fun x : SubFam G (sh G) =>
             forall y : SubFam G (sh G), Ex (fun g : USym G => x = trp (SubFam G) g y))
       <-> isContr (utype (BG G)).
