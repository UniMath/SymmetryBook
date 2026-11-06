(** * Section 10.2 Lagrange's theorem, counting version

    Part of Chapter 10 ([fingp.tex]); see [FinGroups.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    Finiteness is the library's [Finite] with cardinality [fcard], as in
    Section 5.7; [FinGroup_Finite] converts [isFinGroup] (Section 4.2,
    definition [def:finitegrd]).
    - Lemma [lem:Lagrangeascounting], first part ([Lagrangeascounting]),
      from [lagrange_card] of Section 5.3, assuming [G/H] finite.
    - The corollary on products ([card_prodG], with [prodG_Finite]).

    - For a decidable subgroup ([isDecSubGrp]): [G/H] is finite
      ([GH_Finite]: [G/H] is the quotient of [USym(G)] by the decidable
      relation [g · pt = g' · pt], via the library's [finite_quotient]),
      and the second part of [lem:Lagrangeascounting]
      ([Lagrangeascounting_full]).  Corollary [cor:cyclicgroupsaresimple]
      ([cor_cyclicgroupsaresimple]), with [C_m] finite of cardinality [m]
      ([USym_CG_eqv], from [cor:id-m-cycle], and [CG_Finite]).  NOTE:
      the book does not assume decidability, but without it the
      finiteness of [G/H] and [H] is not provable: for a proposition [P],
      the subgroup [{e} ∪ {σ | P}] of [C_2] is finite, or has a finite
      [G/H], only if [P] is decidable.  The statements
      [Lagrangeascounting_stmt] and [cor_cyclicgroupsaresimple_stmt]
      assume the subgroup decidable.
    - From Section 8.2: [D_n] has [2n] elements ([dihedral_card], for
      [dihedral_card_stmt]), since its symmetries are pairs
      ([USym_semidirect_eqv]), [Σ_2] has [2] symmetries ([SG2_card], via
      [fcard_aut]) and [C_n] has [n] ([USym_CG_eqv]); [cardF_eqv]:
      cardinality is invariant under equivalence.
    - From Section 8.2: [Q_8] and [D_4] are not isomorphic ([Q8_not_D4],
      for [Q8_not_D4_stmt]), for any action of [Σ_2] (the hypothesis on
      [C_4] is not used).  In [Q_8] every element of order [2] is a
      square ([Q8_inv_square]: symmetries of the quaternion bicycle are
      determined by their value at [k0], [ev_inj], with
      [ev(g g) = sq(ev g)], [ev_sq], and [k0 ↦ k1] squares to the only
      element of order [2]); in [Σ_2 ⋉ A], [(swap, 1)] has order [2] but
      is not a square, since squares have first component [1]
      ([D_inv_nonsquare]).  Iso groups are equal ([path_Group]).

    Left out (statements only)
    - Corollary [cor:whatSylow2needs].
    - Informal: the chapter introduction, its examples, remark
      [rem:noofsubgps], the example of orders and the remark on [C_2^n].
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core
  Spaces.Finite.Fin Spaces.Finite.Finite Spaces.Nat.Core Spaces.Nat.Division Colimits.Quotient
  Spaces.List.Core Spaces.Int.
From SymmetryBook Require Export Subgroups.Subgroups.

Local Open Scope uf_scope.

(** The introduction of the chapter (the example with [13] and [8], the
    examples on [Σ_3], [Σ_4], [Σ_n]) and remark [rem:noofsubgps] are
    informal. *)

(** ** 10.2 Lagrange's theorem, counting version *)

(** Definition [def:finitegrd]: [isFinGroup] and [CardG] (Section 4.2).
    Below finiteness is the library's [Finite], with cardinality
    [fcard], as in Section 5.7. *)
Definition FinGroup_Finite `{ua : Univalence} (G : Group) (h : isFinGroup G) : Finite (USym G)
  := isFinSet_Finite h.

(** The example after [def:finitegrd] (orders of the trivial, cyclic and
    permutation groups) is informal. *)

(** Lemma [lem:Lagrangeascounting], first part: [|G| = |G/H| · |H|], with
    [G/H] the set [X(sh_G)] of the subgroup [(X, pt_X, !)] (Section 5.3,
    [lagrange_card]).  We assume [G/H] finite here.  For a decidable
    subgroup this follows from the finiteness of [G]
    ([Lagrangeascounting_full], with the second part).  NOTE: without
    decidability it does not: for a proposition [P], the symmetries
    [{e} ∪ {σ | P}] of [C_2] form a subgroup, and finiteness of [G/H]
    (or of [H]) would decide [P].  So [Lagrangeascounting_stmt] assumes
    the subgroup decidable. *)
Definition Lagrangeascounting `{fe : Funext} {G : Group} (S : SubGrp G)
  (FG : Finite (USym G)) (FX : Finite (el (sg_X S) (sh G)))
  : fcard (USym G) = (fcard (el (sg_X S) (sh G)) * @fcard _ (subgrp_Finite S FG FX))%nat
  := lagrange_card S FG FX.

Definition Lagrangeascounting_stmt `{ua : Univalence} : Type
  := forall (G : Group) (S : SubGrp G) (FG : Finite (USym G)), isDecSubGrp S ->
       {FX : Finite (el (sg_X S) (sh G)) &
         @fcard _ (subgrp_Finite S FG FX) = fcard (USym G) -> isContr (el (sg_X S) (sh G))}.

(** The proof: [G/H] is the quotient of [USym(G)] by the decidable
    relation [g · pt = g' · pt] ([quot_surj_eqv], [quot_isFinSet]); if
    [|H| = |G|], then [|G/H| = 1] since [|G| > 0]. *)
Section LagrangeCounting.

  Context `{ua : Univalence} {G : Group} (S : SubGrp G) (FG : Finite (USym G))
    (d : isDecSubGrp S).

  Local Notation X := (sg_X S).
  Local Notation pt0 := (sg_pt S).

  Definition orbmap (g : USym G) : el X (sh G) := act X g pt0.

  Definition orbmap_isSurj : isSurj orbmap.
  Proof.
    intro y.
    refine (Trunc_functor (-1) (fun r => (ap fst r; (act_ap_fst X r)^))
              (snd (conn_of_trans X (sg_trans S)) (sh G; pt0) (sh G; y))).
  Defined.

  Definition orbrel (g g' : USym G) : Type := orbmap g = orbmap g'.

  Definition orbquot_map : Quotient orbrel -> el X (sh G)
    := Quotient_rec orbrel _ (IsHSet0 := isSet_IsHSet (el_isSet X (sh G))) orbmap (fun g g' r => r).

  Definition orbquot_isEquiv : isEquiv orbquot_map.
  Proof.
    refine (inj_surj_isEquiv (cancel_isInj (el_isSet X (sh G)) _) _).
    - refine (Quotient_ind_hprop _ _ _). intro g.
      refine (Quotient_ind_hprop _ _ _). intros g' r.
      exact (qglue r).
    - intro y. refine (Trunc_functor (-1) _ (orbmap_isSurj y)). intros [g e].
      exact (class_of _ g; e).
  Defined.

  Definition GH_Finite : Finite (el X (sh G)).
  Proof.
    pose (rs := fun x y : USym G => @isSet_IsHSet _ (el_isSet X (sh G)) (orbmap x) (orbmap y)).
    refine (finite_equiv' (Quotient orbrel) (Equiv_of_Eqv (orbquot_map; orbquot_isEquiv)) _).
    refine (@finite_quotient ua _ FG orbrel rs _ _ _ _).
    - intro g. exact refl.
    - intros g g' g'' r r'. exact (r @ r').
    - intros g g' r. exact r^.
    - intros g g'. exact (snd (d _ _)).
  Defined.

End LagrangeCounting.

Definition S_ne_0 {k : ℕ} (e : S k = 0%nat) : Empty
  := trp (fun m : ℕ => match m with S _ => Unit | _ => Empty end) e tt.

Definition add_S_ne (m k : ℕ) : (m + S k)%nat = m -> Empty.
Proof.
  induction m as [|m IH]; intro e.
  - exact (S_ne_0 e).
  - exact (IH (ap (fun j : ℕ => match j with S p => p | _ => 0%nat end) e)).
Defined.

Definition mul_self_one (a N : ℕ) (nz : N = 0%nat -> Empty) (e : N = (a * N)%nat) : a = 1%nat.
Proof.
  destruct N as [|n]; [destruct (nz refl)|].
  destruct a as [|[|b]].
  - destruct (S_ne_0 e).
  - exact refl.
  - apply Empty_rec. refine (add_S_ne (S n) (n + b * S n) _).
    exact (e^ @ ap S (ap (fun j => (n + j)%nat) (refl : (S n + b * S n)%nat = S (n + b * S n)))^)
          || exact e^.
Defined.

Definition Fin1_isContr : isContr (Fin 1)
  := (inr tt; fun x => (Fin1_elems x)^).

Definition fcard_one_contr `{Funext} {A : Type} `{FA : Finite A} (e : fcard A = 1%nat) : isContr A
  := ptrunc_rec (isContr_isProp _)
       (fun f => isContr_Eqv (Eqv_inv (Eqv_of_Equiv (trp (fun n => A <~> Fin n) e f))) Fin1_isContr)
       (merely_equiv_fin A).

Definition Lagrangeascounting_full `{ua : Univalence} : Lagrangeascounting_stmt.
Proof.
  intros G S FG d. refine (GH_Finite S FG d; _). intro e.
  pose (FX := GH_Finite S FG d).
  assert (nz : fcard (USym G) = 0%nat -> Empty).
  { intro z. exact (ptrunc_rec False_isProp
                      (fun f : USym G <~> Fin (fcard (USym G)) => trp Fin z (f refl))
                      (merely_equiv_fin (USym G))). }
  pose (a1 := mul_self_one _ _ nz (lagrange_card S FG FX @ ap (fun h => (fcard _ * h)%nat) e)).
  exact (@fcard_one_contr _ _ FX a1).
Defined.


(** Corollary [cor:cyclicgroupsaresimple]; [CG k] is [C_{k+1}].  As for
    the lemma, we assume the subgroup decidable. *)
Definition cor_cyclicgroupsaresimple_stmt `{ua : Univalence} : Type
  := forall (k : ℕ), IsPrime (S k) -> forall S : SubGrp (CG k), isDecSubGrp S ->
       isContr (USym (subgrp_group S)) + isContr (el (sg_X S) (sh (CG k))).

(** [C_m] has [m] elements: its symmetries are those of the cycle
    [(Fin m, zs)], which are [Fin m] by [cor:id-m-cycle] ([idm_eqv]). *)
Definition cyc_of_eqv `{ua : Univalence} : {w : Endo & CycP w} ≃ Cyc
  := mkEqv cyc_of
       (fun c => (cyc_endo c; (snd (fst c); (snd (fst (snd c)); snd (snd c)))) : {w : Endo & CycP w})
       (fun _ => refl) (fun _ => refl).

Definition USym_CG_eqv `{ua : Univalence} (k : ℕ) : USym (CG k) ≃ Fin (S k).
Proof.
  pose (u := eqinv (snd cyc_of_eqv) (Fincyc k)).
  refine (Eqv_comp (USym_AutG_eqv Cyc_isGrpd (Fincyc k)) _).
  refine (Eqv_comp (Eqv_inv (Eqv_of_Equiv (equiv_ap' (Equiv_of_Eqv cyc_of_eqv) u u))) _).
  refine (Eqv_comp (subtype_paths_eqv CycP_isProp u u) _).
  exact (idm_eqv k).
Defined.

Definition CG_Finite `{ua : Univalence} (k : ℕ) : Finite (USym (CG k))
  := Build_Finite _ (S k) (tr (Equiv_of_Eqv (USym_CG_eqv k))).

(** The cardinality of a finite set only depends on its equivalence
    class. *)
Definition cardF_eqv `{ua : Univalence} {A B : Type} (e : A ≃ B) (hA : isFinSet A)
  (hB : isFinSet B) : cardF hA = cardF hB
  := cardF_fcard hA @ @fcard_equiv' _ _ (Equiv_of_Eqv e) _ _ @ (cardF_fcard hB)^.

(** The statement [dihedral_card_stmt] of Section 8.2 ([D_n] has [2n]
    elements), proved here since it uses [USym_CG_eqv]: the symmetries
    of [Σ_2 ⋉ A] are pairs ([USym_semidirect_eqv]), [Σ_2] has
    [2! = 2] symmetries ([card_Aut]) and [C_n] has [n]. *)
Definition USym_SG2_eqv `{Univalence} : USym (SG 2) ≃ (Fin 2 <~> Fin 2)
  := Eqv_comp (Eqv_comp (USym_SG_S_eqv (FinSetU 2)) (idtoeqv; ua _ _))
       (Eqv_inv (Equiv_Eqv_eqv (Fin 2) (Fin 2))).

Definition SG2_Finite `{Univalence} : Finite (USym (SG 2))
  := finite_equiv' _ (Equiv_of_Eqv (Eqv_inv USym_SG2_eqv)) _.

Definition SG2_card `{Univalence} : cardF (Finite_isFinSet SG2_Finite) = 2%nat
  := cardF_fcard _ @ @fcard_equiv' _ _ (Equiv_of_Eqv USym_SG2_eqv) _ _ @ @fcard_aut _ (Fin 2) _.

Definition dihedral_card `{ua : Univalence} : dihedral_card_stmt.
Proof.
  intros k A e.
  pose (hX := Finite_isFinSet SG2_Finite).
  pose (eY := Eqv_comp (idtoeqv (ap USym e)) (USym_CG_eqv k)).
  pose (hY := Finite_isFinSet (finite_equiv' _ (Equiv_of_Eqv (Eqv_inv eY)) _)
              : isFinSet (USym (A (sh (SG 2))))).
  pose (hS := isFinSet_Eqv (binprod_prod _ _)
                (Finite_isFinSet (@finite_prod _ _ (isFinSet_Finite hX) (isFinSet_Finite hY)))
              : isFinSet (USym (SG 2) × USym (A (sh (SG 2))))).
  exists (isFinSet_Eqv (USym_semidirect_eqv (SG 2) A) hS).
  refine (cardF_eqv (USym_semidirect_eqv (SG 2) A) _ hS @ _).
  refine (card_sum_const hX hY (fun _ => USym (A (sh (SG 2)))) (fun _ => idEqv _) hS @ _).
  exact (ap011 mul SG2_card (cardF_fcard hY @ @fcard_equiv' _ _ (Equiv_of_Eqv eY) _ _)).
Defined.

(** The statement [Q8_not_D4_stmt] of Section 8.2 ([Q_8] and [D_4] are
    not isomorphic), proved here since it uses [USym_SG_S_eqv] as above.
    The invariant: every element of order [2] is a square.  This holds in
    [Q_8], whose only element of order [2] sends [k0] to [k4], the square
    of [k0 ↦ k1] ([Q8_inv_square]: symmetries are determined by their
    value at [k0], [ev_inj], and [ev(g g) = sq(ev g)], [ev_sq]).  It
    fails in [Σ_2 ⋉ A] for any action [A]: [(swap, 1)] has order [2] but
    is not a square, as squares have first component [p p = 1]
    ([D_inv_nonsquare]). *)
Section Q8NotD4.

  Context `{Univalence}.

  Local Notation QB := QuaternionBicyc.

  Definition toP (g : USym Q8) : QB = QB := fst (USym_AutG_eqv Bicyc_isGrpd QB) g.

  Definition toE (g : USym Q8) : BicycEqv QB QB := path_to_BicycEqv (toP g).

  Definition Wq (g : USym Q8) : Eight -> Eight := fst (fst (toE g)).

  Definition evq (g : USym Q8) : Eight := Wq g k0.

  Definition pBE_trans {B B' B'' : Bicyc} (P : B = B') (Q : B' = B'')
    : fst (fst (path_to_BicycEqv (Q ⋅ P))) = fst (fst (path_to_BicycEqv Q)) ∘ fst (fst (path_to_BicycEqv P)).
  Proof. destruct Q, P. exact refl. Defined.

  Definition Wq_trans (g g' : USym Q8) : Wq (g' ⋅ g) = Wq g' ∘ Wq g
    := ap (fun P => fst (fst (path_to_BicycEqv P))) (ap_trans (fun w => fst w) g g') @ pBE_trans _ _.

  Definition ev_inj {g g' : USym Q8} (h : evq g = evq g') : g = g'.
  Proof.
    refine (Eqv_inj (USym_AutG_eqv Bicyc_isGrpd QB) _).
    refine (Eqv_inj (path_to_BicycEqv; path_to_BicycEqv_isEquiv QB QB) _).
    exact (BicycEqv_path _ _ (evisinj_bicycle (B := QB) (B' := QB) k0 (toE g) (toE g') h)).
  Defined.

  Definition lstq (x : Eight) : list (ℤ ⨿ ℤ)
    := match x with
       | k0 => nil
       | k1 => cons (inl (iplus 1)) nil
       | k2 => cons (inl (iplus 1)) (cons (inr (iplus 1)) nil)
       | k3 => cons (inl (iplus 2)) (cons (inr (iplus 1)) nil)
       | k4 => cons (inl (iplus 2)) nil
       | k5 => cons (inl (iplus 3)) nil
       | k6 => cons (inl (iplus 3)) (cons (inr (iplus 1)) nil)
       | k7 => cons (inr (iplus 1)) nil
       end.

  Definition lstq_spec (x : Eight) : sem qaEqv qbEqv (lstq x) k0 = x.
  Proof. destruct x; exact refl. Defined.

  Definition sq (x : Eight) : Eight := sem qaEqv qbEqv (lstq x) x.

  Definition ev_sq (g : USym Q8) : evq (g ⋅ g) = sq (evq g)
    := ap (fun h => h k0) (Wq_trans g g) @ ap (Wq g) (lstq_spec (evq g))^
       @ BicycEqv_sem (toE g) (lstq (evq g)) k0.

  (** The symmetry [k0 ↦ k1]. *)
  Definition e1 (k : Eight) : Eight
    := match k with
       | k0 => k1 | k1 => k4 | k2 => k7 | k3 => k2
       | k4 => k5 | k5 => k0 | k6 => k3 | k7 => k6 end.

  Definition e1' (k : Eight) : Eight
    := match k with
       | k1 => k0 | k4 => k1 | k7 => k2 | k2 => k3
       | k5 => k4 | k0 => k5 | k3 => k6 | k6 => k7 end.

  Definition e1Eqv : Eight ≃ Eight.
  Proof. refine (mkEqv e1 e1' _ _); intros []; exact refl. Defined.

  Definition E1 : BicycEqv QB QB.
  Proof.
    refine (e1Eqv; (ptw_inv (f := e1 ∘ qa) (g := qa ∘ e1) _; ptw_inv (f := e1 ∘ qb) (g := qb ∘ e1) _));
      intros []; exact refl.
  Defined.

  Definition v1 : USym Q8 := eqinv (snd (USym_AutG_eqv Bicyc_isGrpd QB)) (BicycEqv_to_path E1).

  Definition evq_v1 : evq v1 = k1.
  Proof.
    refine (ap (fun w : BicycEqv QB QB => fst (fst w) k0)
              (ap path_to_BicycEqv (eqinv_r (snd (USym_AutG_eqv Bicyc_isGrpd QB)) _)
               @ eqinv_r (path_to_BicycEqv_isEquiv QB QB) E1)).
  Defined.

  Definition eight_disc {k l : Eight} (h : k = l) : eight_eqb k l = true
    := trp (fun l => eight_eqb k l = true) h (eight_eqb_refl k).

  Definition Q8_inv_square (w : USym Q8) (ww : w ⋅ w = refl) (nw : w ≠ refl)
    : {v : USym Q8 & v ⋅ v = w}.
  Proof.
    assert (hsq : sq (evq w) = k0) by exact ((ev_sq w)^ @ ap evq ww).
    assert (hne : evq w ≠ k0) by exact (fun h => nw (ev_inj (g' := refl) h)).
    assert (E : evq w = k4).
    { revert hsq hne. generalize (evq w) as x. intros [] hsq hne;
        first [ exact refl | destruct (hne refl)
              | destruct (Bool.false_ne_true (eight_disc hsq)) ]. }
    exists v1. apply ev_inj.
    exact (ev_sq v1 @ ap sq evq_v1 @ E^).
  Defined.

  (** The symmetry [swap] of [Σ_2]. *)
  Definition sw2 (x : Fin 2) : Fin 2
    := match x with inl (inl e) => match e with end | inl (inr t) => inr t | inr t => inl (inr t) end.

  Definition sw2Eqv : Fin 2 ≃ Fin 2.
  Proof. refine (mkEqv sw2 sw2 _ _); intros [[[]|[]]|[]]; exact refl. Defined.

  Definition USym_SG2_Eqv : USym (SG 2) ≃ (Fin 2 ≃ Fin 2)
    := Eqv_comp (USym_SG_S_eqv (FinSetU 2)) (idtoeqv; ua _ _).

  Definition s0 : USym (SG 2) := eqinv (snd USym_SG2_Eqv) sw2Eqv.

  Definition s0_ne_refl : s0 ≠ refl.
  Proof.
    intro h.
    pose (E := ap (fun e : Fin 2 ≃ Fin 2 => fst e (inr triv))
                 ((eqinv_r (snd USym_SG2_Eqv) sw2Eqv)^ @ ap (fst USym_SG2_Eqv) h)).
    exact (Bool.false_ne_true
             (ap (fun x : Fin 2 => match x with inl _ => false | inr _ => true end) E)).
  Defined.

  Definition psa_refl' {X : Type} {Y : X -> Type} (f : forall x, Y x) {x x' : X} (p : x = x')
    : psa f p refl = refl.
  Proof. destruct p. exact refl. Defined.

  Definition D_inv_nonsquare (A : utype (BG (SG 2)) -> Group)
    : {s : USym (Dihedral A) & (s ⋅ s = refl) × (s ≠ refl) × (forall g, g ⋅ g ≠ s)}.
  Proof.
    pose (eD := USym_semidirect_eqv (SG 2) A).
    pose (s := eqinv (snd eD) ((s0; refl) : USym (SG 2) × USym (A (sh (SG 2))))).
    assert (es : fst eD s = (s0; refl)) by exact (eqinv_r (snd eD) _).
    exists s. refine ((_; _); _).
    - apply (Eqv_inj eD).
      refine (USym_semidirect_mult (SG 2) A s0 s0 refl refl @ _).
      refine (ap011 (fun a b => (a; b) : USym (SG 2) × USym (A (sh (SG 2))))
                (SG2_sq s0) (ap (fun x => x ⋅ refl) (psa_refl' (sd_sec_fun (SG 2) A) s0)) @ _).
      exact refl.
    - intro h. apply s0_ne_refl.
      exact ((ap (fun w => fst w) es)^ @ ap (fun h => fst (fst eD h)) h).
    - intros g e. apply s0_ne_refl.
      refine ((ap (fun w => fst w) es)^ @ _).
      refine ((ap (fun h => fst (fst eD h)) e)^ @ _).
      refine ((ap (fun h => fst (fst eD (h ⋅ h))) (eqinv_l (snd eD) g))^ @ _).
      refine (ap (fun w => fst w) (USym_semidirect_mult (SG 2) A _ _ _ _) @ _).
      exact (SG2_sq _).
  Defined.

End Q8NotD4.

Definition Q8_not_D4 `{ua : Univalence} : Q8_not_D4_stmt.
Proof.
  intros A _ [phi i].
  pose (P := fun G : Group => forall w : USym G, w ⋅ w = refl -> w ≠ refl -> {v : USym G & v ⋅ v = w}).
  pose (p := path_Group ((Bf phi; i) : BG Q8 ≃* BG (Dihedral A))).
  destruct (D_inv_nonsquare A) as [s [[ss ns] nsq]].
  destruct (trp P p Q8_inv_square s ss ns) as [v hv].
  exact (nsq v hv).
Defined.

Definition cor_cyclicgroupsaresimple `{ua : Univalence} : cor_cyclicgroupsaresimple_stmt.
Proof.
  intros k P Sg d.
  pose (FG := CG_Finite k). pose (FX := GH_Finite Sg FG d).
  pose (FH := subgrp_Finite Sg FG FX).
  pose (L := lagrange_card Sg FG FX : (S k = fcard _ * @fcard _ FH)%nat).
  destruct (isprime (@fcard _ FH) (fcard (el (sg_X Sg) (sh (CG k))); L^)) as [e|e].
  - left. exact (@fcard_one_contr _ _ FH e).
  - right. exact (snd (Lagrangeascounting_full (CG k) Sg FG d) e).
Defined.

(** Corollary [cor:whatSylow2needs] (statement only): [H] is a subgroup of
    the kernel [N]; surjectivity of [f] is surjectivity on symmetries. *)
Definition cor_whatSylow2needs_stmt `{ua : Univalence} : Type
  := forall (G G' H : Group) (f : Hom G G') (s : isSurj (USymf f)) (i : Hom H G) (m : ismono i)
            (FH : Finite (USym H)) (FG' : Finite (USym G')),
       nat_gcd (fcard (USym H)) (fcard (USym G')) = 1%nat ->
       {j : Hom H (Ker f) & compG (kermap f) j = i}.

(** The corollary on products: [|G × G'| = |G| · |G'|]. *)
Section CardProd.

  Context `{fe : Funext} (G G' : Group) {FG : Finite (USym G)} {FG' : Finite (USym G')}.

  Definition USym_prodG_prod : USym (prodG G G') <~> USym G * USym G'
    := Equiv_of_Eqv (Eqv_comp (USym_prodG G G') (binprod_prod _ _)).

  Definition prodG_Finite : Finite (USym (prodG G G'))
    := finite_equiv' _ USym_prodG_prod^-1 _.

  Definition card_prodG
    : @fcard _ prodG_Finite = (fcard (USym G) * fcard (USym G'))%nat
    := fcard_equiv' USym_prodG_prod @ fcard_prod _ _.

End CardProd.

(** The remark after it ([C_2^n] has order [2^n]) is informal. *)
