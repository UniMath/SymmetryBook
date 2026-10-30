(** * Section 7.6 Actions, from abstract to concrete and back

    Part of Chapter 7 ([absgroup.tex]); see [AbsGroup.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Inverses of abstract isomorphisms ([AbsIso_inv]) and postcomposition
      with an isomorphism as an equivalence ([absHom_postcomp]).
    - [abstr(Σ_S) ≅ Perm(S)] ([SG_Perm_iso]), using [idtoeqv_trans].
    - Lemma [lem:actionsconcr2abstr]: [GSet G ≃ absGSet(abstr G)]
      ([actions_eqv]), by the book's chain of equivalences through
      [GSet_eqv] (Section 5.2) and [abstr_hom_eqv] (Section 7.5); the
      underlying set of [ev(X)] is [X(sh_G)] by definition
      ([actions_eqv_set]).
    - The action of [ev(X)] is transport in [X] ([actions_eqv_gact]).
    - Example [ex:abstrandconj] and lemma [lem:abstrandconj]
      ([lem_abstrandconj], with [e :≡ abstr_hom_eqv]; transport in
      [Hom(H, -)] is conjugation, [USymf_trp_regroup]).
    - Exercise [xca:f^*-abs(f)^*] ([xca_restrict_abstr]): the
      identification is transport along the pointing path of [Bf].

    Left out (statements only, no proofs yet; time limit per result)
    - Exercise [xca:f_!-abs(f)_!] ([xca_induce_abstr_stmt]).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core.
From SymmetryBook Require Export AbsGroup.S05_Homomorphisms.

Local Open Scope uf_scope.

(** ** 7.6 Actions, from abstract to concrete and back *)

(** Inverse and composition of abstract isomorphisms. *)
Definition AbsIso_inv {A B : AbsGroup} (i : AbsIso A B) : AbsIso B A.
Proof.
  refine (Eqv_inv (fst i); _). intros x y. cbn.
  apply (isInj_cancel (isEquiv_isInj (snd (fst i)))).
  refine (eqinv_r (snd (fst i)) _ @ _). refine (_ @ (snd i _ _)^).
  exact (ap011 (ag_mul B) (eqinv_r (snd (fst i)) x)^ (eqinv_r (snd (fst i)) y)^).
Defined.

(** Postcomposition with an isomorphism is an equivalence of the sets of
    homomorphisms. *)
Definition absHom_postcomp `{Funext} (K : AbsGroup) {A B : AbsGroup} (i : AbsIso A B)
  : absHom K A ≃ absHom K B.
Proof.
  pose (i' := ((fst (fst i); snd i) : absHom A B)).
  pose (j := (fst (fst (AbsIso_inv i)); snd (AbsIso_inv i)) : absHom B A).
  refine (mkEqv (absHom_comp i') (absHom_comp j) _ _); intro f.
  - apply path_absHom. intro s. exact (eqinv_l (snd (fst i)) _).
  - apply path_absHom. intro s. exact (eqinv_r (snd (fst i)) _).
Defined.

(** [abstr(Σ_S)] is isomorphic to the abstract permutation group of [S]. *)
Definition idtoeqv_trans `{Funext} {X Y Z : Type} (p : X = Y) (q : Y = Z)
  : idtoeqv (q ⋅ p) = Eqv_comp (idtoeqv p) (idtoeqv q).
Proof. destruct q, p. apply path_Eqv. exact refl. Defined.

Definition SG_Perm_iso `{Univalence} (S : SetU) : AbsIso (abstr (SG_S S)) (ag_Perm S).
Proof.
  refine (Eqv_comp (USym_SG_S_eqv S) (idtoeqv; ua _ _); _).
  intros u v. cbn.
  refine (ap idtoeqv (ap (ap fst) (ap_trans fst v u) @ ap_trans fst _ _) @ _).
  exact (idtoeqv_trans _ _).
Defined.

(** Lemma [lem:actionsconcr2abstr]: [G-Set ≃ abstr(G)-Set], by the chain
    [G-Set ≃ ∑_S Hom(G, Σ_S) ≃ ∑_S absHom(abstr G, abstr Σ_S)
     ≃ ∑_S absHom(abstr G, Perm(S))]. *)
Definition actions_eqv `{Univalence} (G : Group) : GSet G ≃ absGSet (abstr G).
Proof.
  refine (Eqv_comp (GSet_eqv G) _).
  pose (E := fun S : SetU => Eqv_comp (abstr_hom_eqv G (SG_S S))
                               (absHom_postcomp (abstr G) (SG_Perm_iso S))).
  exact (tot (fun S => fst (E S)); tot_isEquiv _ (fun S => snd (E S))).
Defined.

(** The underlying set of [ev(X)] is [X(sh_G)]. *)
Definition actions_eqv_set `{Univalence} (G : Group) (X : GSet G)
  : fst (fst (fst (actions_eqv G) X)) = el X (sh G)
  := refl.

(** The action of [ev(X)] is transport in [X]. *)
Definition ptoe_ap_fst_fst {S : SetU} {c c' : component SetU S} (q : c = c') (y : fst (fst c))
  : ptoe (ap fst (ap fst q)) y = trp (fun c0 : component SetU S => fst (fst c0)) q y.
Proof. destruct q. exact refl. Defined.

Definition trp_fst_fst_inv {S : SetU} {c c' : component SetU S} (q : c = c') (y : fst (fst c'))
  : trp (fun c0 : component SetU S => fst (fst c0)) q⁻¹ y = ptoe (ap fst (ap fst q))⁻¹ y.
Proof. destruct q. exact refl. Defined.

Definition actions_eqv_gact `{Univalence} (G : Group) (X : GSet G) (g : USym G)
  (x : el X (sh G)) : gact (fst (actions_eqv G) X) g x = trp (el X) g x.
Proof.
  pose (K := to_comp G SetU_isGrpd (X (sh G)) (X; refl)).
  pose (F := fun c0 : component SetU (X (sh G)) => fst (fst c0)).
  change (ptoe (ap fst (ap fst (loops_fun K g))) x = trp (el X) g x).
  refine (ptoe_ap_fst_fst (loops_fun K g) x @ _). unfold loops_fun.
  pose (x' := x : F (pt (BG (AutG SetU_isGrpd (X (sh G)))))).
  refine (trp_trans_gen F (ap (fst K) g ⋅ snd K) (snd K)⁻¹ x' @ _).
  refine (ap (trp F (snd K)⁻¹) (trp_trans_gen F (snd K) (ap (fst K) g) x') @ _).
  assert (e : ap fst (ap fst (snd K)) = refl)
    by exact (ap (ap fst) (ap_fst_path_sigma_prop _ _)).
  refine (trp_fst_fst_inv _ _ @ ap (fun s => ptoe s⁻¹ _) e @ _).
  change (trp F (ap (fst K) g) (trp F (snd K) x) = trp (el X) g x).
  refine (ap (trp F _) ((ptoe_ap_fst_fst (snd K) x)^ @ ap (fun s => ptoe s x) e) @ _).
  exact (ptw (trp_ap F (fst K) g) x)^.
Defined.

(** Example [ex:abstrandconj] and lemma [lem:abstrandconj]: [ev] sends
    the [G]-set [Hom(H,G)] to [absHom(abstr H, abstr G)] with [g] acting
    by postcomposition with [conj^g]. *)
Definition lem_abstrandconj_stmt `{Univalence} : Type
  := forall H G : Group,
       {e : gset (fst (actions_eqv G) (HomG_set H G)) ≃ absHom (abstr H) (abstr G) &
         forall (g : USym G) f,
           fst e (gact (fst (actions_eqv G) (HomG_set H G)) g f)
           = absHom_comp (conj_absHom (abstr G) g) (fst e f)}.

Definition USymf_trp_regroup {H G : Group} {z : utype (BG G)} (p : sh G = z)
  (f : Hom H (regroup G (sh G))) (h : USym H)
  : USymf (trp (fun y => Hom H (regroup G y)) p f) h = trp (fun y => y = y) p (USymf f h).
Proof. destruct p. exact refl. Defined.

Definition lem_abstrandconj `{ua : Univalence} : lem_abstrandconj_stmt.
Proof.
  intros H [Y].
  refine (abstr_hom_eqv H (inc Y); fun g f => _).
  refine (ap (abstr_hom) (actions_eqv_gact (inc Y) (HomG_set H (inc Y)) g f) @ _).
  apply path_absHom. intro h.
  exact (USymf_trp_regroup g f h @ trp_loop_conj g _).
Defined.

(** Exercises [xca:f^*-abs(f)^*] and [xca:f_!-abs(f)_!] (the second
    stated only): [ev] commutes with restriction and with induction (the latter
    up to isomorphism, with [φ_!] from Section 7.4, which lives in a
    higher universe). *)
Definition xca_restrict_abstr_stmt `{Univalence} : Type
  := forall (G H : Group) (f : Hom G H) (Y : GSet H),
       fst (actions_eqv G) (restrict f Y) = abs_restrict (abstr_hom f) (fst (actions_eqv H) Y).

Definition trp_conj_loop {A : Type} (F : A -> Type) {a b : A} (p : a = b) (q : b = b) (x : F b)
  : trp F p⁻¹ (trp F q x) = trp F (p⁻¹ ⋅ (q ⋅ p)) (trp F p⁻¹ x).
Proof. destruct p. exact (ap (fun r => trp F r x) (trans_1p q)^). Defined.

Definition trp_V_trp {A : Type} (F : A -> Type) {a b : A} (p : a = b) (x : F a)
  : trp F p⁻¹ (trp F p x) = x.
Proof. destruct p. exact refl. Defined.

Definition trp_trp_V {A : Type} (F : A -> Type) {a b : A} (p : a = b) (y : F b)
  : trp F p (trp F p⁻¹ y) = y.
Proof. destruct p. exact refl. Defined.

(** [ev] commutes with restriction: the identification is given by
    transport along the pointing path of [Bf], which is equivariant
    since [U(f)(g) = f_pt⁻¹ · Bf(g) · f_pt]. *)
Definition xca_restrict_abstr `{ua : Univalence} : xca_restrict_abstr_stmt.
Proof.
  intros G H f Y. apply path_absGSet.
  pose (kp := snd (Bf f)).
  refine (mkEqv (trp (el Y) kp⁻¹) (trp (el Y) kp) (trp_trp_V (el Y) kp) (trp_V_trp (el Y) kp);
          fun s x => _).
  refine (ap (trp (el Y) kp⁻¹) (actions_eqv_gact G (restrict f Y) s x) @ _).
  refine (ap (trp (el Y) kp⁻¹) (ptw (trp_ap (el Y) (fst (Bf f)) s) x) @ _).
  refine (trp_conj_loop (el Y) kp _ x @ _).
  exact (actions_eqv_gact H Y _ _)^.
Defined.

Definition xca_induce_abstr_stmt `{Univalence} : Type
  := forall (G H : Group) (f : Hom G H) (X : GSet G),
       gIso (fst (actions_eqv H) (induce f X)) (phi_shriek (abstr_hom f) (fst (actions_eqv G) X)).
