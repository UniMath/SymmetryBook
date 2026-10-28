(** * Section 4.6 Bicycles

    Part of Chapter 4 ([group.tex]); see [Group.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Iteration of equivalences over the integers [iterZ] (Section 3.2):
      [iterZ_neg_l] (inverse powers) and naturality [iterZ_nat].
    - The meaning [sem a b ℓ] ([⟦ℓ⟧]) of a list [ℓ : (ℤ ⨿ ℤ)^*], with
      [sem_app], inverse lists [invl] ([sem_invl], [sem_invl_r]) and
      [sem_isEquiv]; connectedness [isConnBy a b], which follows from
      reachability from one element ([connBy_from_base]).
    - Definition [def:bicycle]: [Bicyc], a groupoid ([Bicyc_isGrpd]).
    - Definition [def:Dinfty-Q]: the standard infinite dihedral bicycle
      ([DihedralBicyc]) and [Dinfty]; the standard quaternion bicycle
      ([QuaternionBicyc]) and [Q8].  The quaternion bicycle lives on an
      inductive 8-element type [Eight] instead of [Fin 8], so that its
      connectedness is checked by computation; [a] and [b] are given by
      their tables.
    - Identifications of bicycles: an identification gives an
      equivalence commuting with [a] and [b] ([BicycEqv],
      [path_to_BicycEqv]); by univalence this map is an equivalence
      ([path_to_BicycEqv_isEquiv], via contractibility of the total space
      [Bicyc_total_isContr]; inverse [BicycEqv_to_path]).  The results
      on symmetries are stated for [BicycEqv].
    - Lemma [lem:evisinj-bicycle] ([evisinj_bicycle], [ev_bicyc_isInj]),
      via [BicycEqv_sem]: commuting equivalences commute with [⟦ℓ⟧].
    - Definition [def:normal-bicycle] ([isNormal]), exercise
      [xca:normal-bicycle-equiv] ([normal_from_one]), and definition
      [def:cbid-bicycle] ([cbid], with [cbid_spec] and [cbid_refl]).
    - The exercises after [def:cbid-bicycle]: normality iff [H_x = H_y]
      ([Hx], [xca_normal_Hx]; for the converse, a symmetry [x ↦ y] is
      built by relabelling, [relabel], [relabel_sym]); commuting bicycles
      are normal ([isCommuting], [commuting_isNormal]); lists with the
      same value at [x₀] have the same meaning ([xca_lists_equiv]).
    - Remark [rem:bicycle-list-concat] ([rem_bicycle_list_concat], with
      [BicycEqv_comp]).
    - Remark [rem:inf-dihedral-frieze] and the exercise after it: the
      infinite dihedral bicycle is normal ([dihedral_isNormal], with
      translations [dtr_sym] and reflections [dre_sym]); [T] is
      translation by [-1] and [R] the reflection [ρ_0] ([dT_spec],
      [dR_spec]), and [inl(n) ↦ inl(-n)], [inr(n) ↦ inr(n)] identifies
      [(X,a,b)] with [(X,T,R)] ([xca_frieze]).  We give the commuting
      equivalence; [BicycEqv_to_path] turns it into an identification.
    - The two [6]-element bicycles of the last exercise ([HexagonBicyc],
      [PrismBicyc], on an inductive type [Six], connected by
      computation) and the exercise ([xca_six_bicycles]): they are in
      different components ([hex_ne_prism]: in the hexagon [a² = id], in
      the prism not), and both automorphism groups are [Σ_3]
      ([SG3_AutHex], [SG3_AutPrism]).  Both bicycles are Cayley bicycles
      [(Fin 3 ≃ Fin 3, - ∘ σa, - ∘ σb)] of [Σ_3] (two transpositions,
      resp. a 3-cycle and a transposition; [hexEqv], [prismEqv]).  The
      Cayley bicycle extends to a map [Kc] from the component of [Fin 3]
      in [Set] to [Bicyc], [S ↦ (Fin 3 ≃ S, - ∘ σa, - ∘ σb)], which is
      an equivalence onto its component ([Kc'_isEquiv]): on loops it is
      postcomposition ([ap_Kc_post]), an equivalence by
      [lem:evisinj-bicycle] ([post_isEquiv0]).  Hence [SG3_AutKc].

    Deviations
    - The commuting-bicycles exercise is only half formalized: its
      second part is false as stated (NOTE for the book): [(𝟚, swap,
      swap)] is a commuting bicycle ([SwapBicyc], [SwapBicyc_isCommuting])
      that is not of the form [(X × Y, t × id, id × u)]
      ([SwapBicyc_not_product]).  A fix is to restrict to commuting
      bicycles with [aⁿ = bᵐ] only if [aⁿ = id]; this is for the authors
      to decide.
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Types.Sum Truncations.Core Spaces.Nat.Core
  Spaces.List.Core Spaces.Int Spaces.Finite.Fin.
From SymmetryBook Require Export Group.S05_Sign.

Local Open Scope uf_scope.

(** ** 4.6 Bicycles *)

(** ** Iteration of equivalences *)

Definition iter_succ_r {Y : Type} (f : Y -> Y) (n : ℕ) (y : Y)
  : iter f (S n) y = iter f n (f y).
Proof.
  induction n as [|n IH].
  - exact refl.
  - exact (ap f IH).
Defined.

Definition iter_inv_l {X : Type} (t : X ≃ X) (n : ℕ) (y : X)
  : iter (eqinv (snd t)) n (iter (fst t) n y) = y.
Proof.
  revert y. induction n as [|n IH]; intro y.
  - exact refl.
  - refine (iter_succ_r _ n _ @ _).
    exact (ap (iter (eqinv (snd t)) n) (eqinv_l (snd t) _) @ IH y).
Defined.

Definition iter_inv_r {X : Type} (t : X ≃ X) (n : ℕ) (y : X)
  : iter (fst t) n (iter (eqinv (snd t)) n y) = y.
Proof.
  revert y. induction n as [|n IH]; intro y.
  - exact refl.
  - refine (iter_succ_r _ n _ @ _).
    exact (ap (iter (fst t) n) (eqinv_r (snd t) _) @ IH y).
Defined.

Definition iterZ_neg_l {X : Type} (sX : isSet X) (t : X ≃ X) (z : ℤ) (y : X)
  : iterZ t (zneg z) (iterZ t z y) = y.
Proof.
  revert z. refine (ℤ_ind_prop _ (fun z => sX _ _) _ _).
  - intro n. exact (iter_inv_l t n y).
  - intros [n]. exact (iter_inv_r t n y).
Defined.

(** Naturality of iteration. *)
Definition iterZ_nat {X Y : Type} (sY : isSet Y) (t : X ≃ X) (u : Y ≃ Y)
  (f : X -> Y) (h : forall x, f (fst t x) = fst u (f x)) (z : ℤ) (x : X)
  : f (iterZ t z x) = iterZ u z (f x).
Proof.
  revert z. refine (ℤ_ind_prop _ (fun z => sY _ _) _ _).
  - intro n. induction n as [|n IH].
    + exact refl.
    + exact (h _ @ ap (fst u) IH).
  - intros [n]. induction n as [|n IH].
    + exact refl.
    + change (f (eqinv (snd t) (iter (eqinv (snd t)) n x))
              = eqinv (snd u) (iter (eqinv (snd u)) n (f x))).
      refine (_ @ ap (eqinv (snd u)) IH).
      refine ((eqinv_l (snd u) _)^ @ ap (eqinv (snd u)) _).
      exact ((h _)^ @ ap f (eqinv_r (snd t) _)).
Defined.

(** ** The meaning of a list *)

Section Meaning.

  Context {X : Type} (a b : X ≃ X).

  (** [⟦ε⟧ :≡ id], [⟦inl(n) ℓ⟧ :≡ aⁿ ∘ ⟦ℓ⟧], [⟦inr(n) ℓ⟧ :≡ bⁿ ∘ ⟦ℓ⟧]. *)
  Fixpoint sem (l : list (ℤ ⨿ ℤ)) : X -> X
    := match l with
       | nil => id X
       | cons (inl n) l' => iterZ a n ∘ sem l'
       | cons (inr n) l' => iterZ b n ∘ sem l'
       end.

  Definition sem_app (l l' : list (ℤ ⨿ ℤ)) (x : X)
    : sem (app l l') x = sem l (sem l' x).
  Proof.
    induction l as [|[n|n] l IH]; cbn.
    - exact refl.
    - exact (ap (iterZ a n) IH).
    - exact (ap (iterZ b n) IH).
  Defined.

  Definition negc (c : ℤ ⨿ ℤ) : ℤ ⨿ ℤ
    := match c with inl n => inl (zneg n) | inr n => inr (zneg n) end.

  (** The inverse list. *)
  Fixpoint invl (l : list (ℤ ⨿ ℤ)) : list (ℤ ⨿ ℤ)
    := match l with
       | nil => nil
       | cons c l' => app (invl l') (cons (negc c) nil)
       end.

  Definition sem_invl (sX : isSet X) (l : list (ℤ ⨿ ℤ)) (x : X)
    : sem (invl l) (sem l x) = x.
  Proof.
    induction l as [|[n|n] l IH]; cbn.
    - exact refl.
    - refine (sem_app _ _ _ @ _); cbn.
      exact (ap (sem (invl l)) (iterZ_neg_l sX a n _) @ IH).
    - refine (sem_app _ _ _ @ _); cbn.
      exact (ap (sem (invl l)) (iterZ_neg_l sX b n _) @ IH).
  Defined.

  Definition isConnBy : Type
    := forall x x' : X, Ex (fun l : list (ℤ ⨿ ℤ) => x' = sem l x).

  (** Connectedness follows from reachability from one element. *)
  Definition connBy_from_base (sX : isSet X) (x0 : X)
    (h : forall x, Ex (fun l : list (ℤ ⨿ ℤ) => x = sem l x0)) : isConnBy.
  Proof.
    intros x x'.
    refine (ptrunc_rec ptrunc_isProp _ (h x)). intros [l1 e1].
    refine (ptrunc_rec ptrunc_isProp _ (h x')). intros [l2 e2].
    refine (trunc (app l2 (invl l1); _)).
    refine (e2 @ _ @ (sem_app _ _ _)^).
    apply ap. exact ((sem_invl sX l1 x0)^ @ ap (sem (invl l1)) e1^).
  Defined.

End Meaning.

(** Definition [def:bicycle]. *)
Definition Bicyc `{Funext} : Type
  := {X : SetU & {a : fst X ≃ fst X & {b : fst X ≃ fst X &
       ptrunc (fst X) × isConnBy a b}}}.

Definition Bicyc_isGrpd `{Univalence} : isGrpd Bicyc.
Proof.
  refine (Sigma_ntype 1 SetU_isGrpd (fun X => Sigma_ntype 1 _
            (fun a => Sigma_ntype 1 _ (fun b => prop_ntype 1 _ _)))).
  - exact (set_ntype 1 (Eqv_sets_isSet (snd X))).
  - exact (set_ntype 1 (Eqv_sets_isSet (snd X))).
  - exact (prod_isProp ptrunc_isProp
             (Pi_isProp (fun x => Pi_isProp (fun x' => ptrunc_isProp)))).
Defined.

(** Remark [rem:F2-first-look]: bicycles are the connected coverings of
    [S1 ∨ S1], see 8.7 (informal). *)

(** Definition [def:Dinfty-Q]: the standard infinite dihedral bicycle on
    [ℤ ⨿ ℤ], with [a(inl n) :≡ inl(n+1)], [a(inr n) :≡ inr(n-1)] and
    [b] swapping the summands. *)
Section Dihedral.

  Context `{Univalence}.

  Definition da (x : ℤ ⨿ ℤ) : ℤ ⨿ ℤ
    := match x with inl n => inl (zs n) | inr n => inr (zp n) end.

  Definition da' (x : ℤ ⨿ ℤ) : ℤ ⨿ ℤ
    := match x with inl n => inl (zp n) | inr n => inr (zs n) end.

  Definition daEqv : (ℤ ⨿ ℤ) ≃ (ℤ ⨿ ℤ).
  Proof.
    refine (mkEqv da da' _ _); intros [n|n]; cbn.
    - exact (ap inl (zp_zs n)).
    - exact (ap inr (zs_zp n)).
    - exact (ap inl (zs_zp n)).
    - exact (ap inr (zp_zs n)).
  Defined.

  Definition db (x : ℤ ⨿ ℤ) : ℤ ⨿ ℤ
    := match x with inl n => inr n | inr n => inl n end.

  Definition dbEqv : (ℤ ⨿ ℤ) ≃ (ℤ ⨿ ℤ).
  Proof. refine (mkEqv db db _ _); intros [n|n]; exact refl. Defined.

  Definition ZZ_isSet : isSet (ℤ ⨿ ℤ) := sum_isSet ℤ_isSet ℤ_isSet.

  Definition da_iter (z : ℤ) : iterZ daEqv z (inl (iplus 0)) = inl z.
  Proof.
    revert z. refine (ℤ_ind_prop _ (fun z => ZZ_isSet _ _) _ _).
    - intro n. induction n as [|n IH].
      + exact refl.
      + exact (ap da IH).
    - intros [n]. induction n as [|n IH].
      + exact (ap inl zeq⁻¹).
      + exact (ap da' IH).
  Defined.

  Definition dihedral_connBy : isConnBy daEqv dbEqv.
  Proof.
    refine (connBy_from_base _ _ ZZ_isSet (inl (iplus 0)) _).
    intros [z|z].
    - exact (trunc (cons (inl z) nil; (da_iter z)^)).
    - exact (trunc (cons (inr (iplus 1)) (cons (inl z) nil); (ap db (da_iter z))^)).
  Defined.

  Definition DihedralBicyc : Bicyc
    := ((ℤ ⨿ ℤ; ZZ_isSet); (daEqv; (dbEqv; (trunc (inl (iplus 0)); dihedral_connBy)))).

  Definition Dinfty : Group := AutG Bicyc_isGrpd DihedralBicyc.

End Dihedral.

(** The standard quaternion bicycle, on an 8-element set [Eight] (with
    elements [k0], ..., [k7] for [0, ..., 7]) instead of [Fin 8]:
    [a(k) :≡ k+1] for even and [k+3] for odd [k], [b(k) :≡ k-1] for even
    and [k-3] for odd [k], modulo 8. *)
Inductive Eight : Type0 := k0 | k1 | k2 | k3 | k4 | k5 | k6 | k7.

Section Quaternion.

  Context `{Univalence}.

  Definition qa (k : Eight) : Eight
    := match k with
       | k0 => k1 | k1 => k4 | k2 => k3 | k3 => k6
       | k4 => k5 | k5 => k0 | k6 => k7 | k7 => k2 end.

  Definition qa' (k : Eight) : Eight
    := match k with
       | k1 => k0 | k4 => k1 | k3 => k2 | k6 => k3
       | k5 => k4 | k0 => k5 | k7 => k6 | k2 => k7 end.

  Definition qb (k : Eight) : Eight
    := match k with
       | k0 => k7 | k1 => k6 | k2 => k1 | k3 => k0
       | k4 => k3 | k5 => k2 | k6 => k5 | k7 => k4 end.

  Definition qb' (k : Eight) : Eight
    := match k with
       | k7 => k0 | k6 => k1 | k1 => k2 | k0 => k3
       | k3 => k4 | k2 => k5 | k5 => k6 | k4 => k7 end.

  Definition qaEqv : Eight ≃ Eight.
  Proof. refine (mkEqv qa qa' _ _); intros []; exact refl. Defined.

  Definition qbEqv : Eight ≃ Eight.
  Proof. refine (mkEqv qb qb' _ _); intros []; exact refl. Defined.

  Definition eight_eqb (k l : Eight) : Bool
    := match k, l with
       | k0, k0 | k1, k1 | k2, k2 | k3, k3 | k4, k4 | k5, k5 | k6, k6 | k7, k7 => true
       | _, _ => false end.

  Definition eight_eqb_refl (k : Eight) : eight_eqb k k = true.
  Proof. destruct k; exact refl. Defined.

  Definition Eight_isDecSet : isDecSet Eight.
  Proof.
    apply hedberg. intros k l.
    destruct (dec_paths (eight_eqb k l) true) as [e|n].
    - left. destruct k, l; try exact refl; destruct (false_ne_true e).
    - right. intro p. destruct p. exact (n (eight_eqb_refl k)).
  Defined.

  Definition Eight_isSet : isSet Eight := fun k l => fst (Eight_isDecSet k l).

  Definition quaternion_connBy : isConnBy qaEqv qbEqv.
  Proof.
    refine (connBy_from_base _ _ Eight_isSet k0 _).
    intros []; apply trunc.
    - exact (nil; refl).
    - exact (cons (inl (iplus 1)) nil; refl).
    - exact (cons (inl (iplus 1)) (cons (inr (iplus 1)) nil); refl).
    - exact (cons (inl (iplus 2)) (cons (inr (iplus 1)) nil); refl).
    - exact (cons (inl (iplus 2)) nil; refl).
    - exact (cons (inl (iplus 3)) nil; refl).
    - exact (cons (inl (iplus 3)) (cons (inr (iplus 1)) nil); refl).
    - exact (cons (inr (iplus 1)) nil; refl).
  Defined.

  Definition QuaternionBicyc : Bicyc
    := ((Eight; Eight_isSet); (qaEqv; (qbEqv; (trunc k0; quaternion_connBy)))).

  Definition Q8 : Group := AutG Bicyc_isGrpd QuaternionBicyc.

End Quaternion.

(** ** Identifications of bicycles

    An identification [(X,a,b) = (X',a',b')] gives an equivalence
    [e : X ≃ X'] with [ea = a'e] and [eb = b'e] ([path_to_BicycEqv]); by
    univalence this is an equivalence ([path_to_BicycEqv_isEquiv] below).
    We state the results about symmetries in terms of such equivalences. *)
Section BicycleIds.

  Context `{Univalence}.

  Definition bX (B : Bicyc) : Type := fst (fst B).
  Definition bX_isSet (B : Bicyc) : isSet (bX B) := snd (fst B).
  Definition ba (B : Bicyc) : bX B ≃ bX B := fst (snd B).
  Definition bb (B : Bicyc) : bX B ≃ bX B := fst (snd (snd B)).
  Definition bconn (B : Bicyc) : isConnBy (ba B) (bb B) := snd (snd (snd (snd B))).

  Definition BicycEqv (B B' : Bicyc) : Type
    := {e : bX B ≃ bX B' & (fst e ∘ fst (ba B) = fst (ba B') ∘ fst e)
                           × (fst e ∘ fst (bb B) = fst (bb B') ∘ fst e)}.

  Definition path_to_BicycEqv {B B' : Bicyc} (p : B = B') : BicycEqv B B'
    := match p with refl => (idEqv _; (refl; refl)) end.

  (** Equivalences commuting with [a] and [b] commute with [⟦ℓ⟧]. *)
  Definition BicycEqv_sem {B B' : Bicyc} (w : BicycEqv B B') (l : list (ℤ ⨿ ℤ))
    (x : bX B) : fst (fst w) (sem (ba B) (bb B) l x) = sem (ba B') (bb B') l (fst (fst w) x).
  Proof.
    induction l as [|[n|n] l IH]; cbn.
    - exact refl.
    - refine (iterZ_nat (bX_isSet B') _ _ _ (fun y => ptw (fst (snd w)) y) n _ @ _).
      exact (ap (iterZ (ba B') n) IH).
    - refine (iterZ_nat (bX_isSet B') _ _ _ (fun y => ptw (snd (snd w)) y) n _ @ _).
      exact (ap (iterZ (bb B') n) IH).
  Defined.

  (** Lemma [lem:evisinj-bicycle]: evaluation at [x₀] is injective. *)
  Definition evisinj_bicycle {B B' : Bicyc} (x0 : bX B) (w w' : BicycEqv B B')
    (h : fst (fst w) x0 = fst (fst w') x0) : fst (fst w) = fst (fst w').
  Proof.
    apply ptw_inv. intro x.
    refine (ptrunc_rec (bX_isSet B' _ _) _ (bconn B x0 x)). intros [l e].
    destruct e^.
    exact (BicycEqv_sem w l x0 @ ap (sem _ _ l) h @ (BicycEqv_sem w' l x0)^).
  Defined.

  Definition BicycEqv_path {B B' : Bicyc} (w w' : BicycEqv B B')
    (h : fst (fst w) = fst (fst w')) : w = w'.
  Proof.
    refine (path_sigma_prop _ (path_Eqv _ _ h)).
    intro e. apply prod_isProp; apply (Pi_isSet (fun _ => bX_isSet B')).
  Defined.

  Definition ev_bicyc (B : Bicyc) (x : bX B) : BicycEqv B B -> bX B
    := fun w => fst (fst w) x.

  Definition ev_bicyc_isInj (B : Bicyc) (x : bX B) : isInj (ev_bicyc B x)
    := cancel_isInj (bX_isSet B)
         (fun w w' h => BicycEqv_path w w' (evisinj_bicycle x w w' h)).

  (** Definition [def:normal-bicycle]. *)
  Definition isNormal (B : Bicyc) : Type := forall x : bX B, isEquiv (ev_bicyc B x).

  (** [⟦ℓ⟧] is an equivalence. *)
  Definition sem_invl_r {X : Type} (sX : isSet X) (a b : X ≃ X) (l : list (ℤ ⨿ ℤ)) (x : X)
    : sem a b l (sem a b (invl l) x) = x.
  Proof.
    revert x. induction l as [|[n|n] l IH]; intro x; cbn.
    - exact refl.
    - refine (ap (iterZ a n) (ap (sem a b l) (sem_app _ _ _ _ _)) @ _); cbn.
      refine (ap (iterZ a n) (IH _) @ _).
      exact (ap (fun m => iterZ a m _) (zneg_zneg n)^ @ iterZ_neg_l sX a (zneg n) x).
    - refine (ap (iterZ b n) (ap (sem a b l) (sem_app _ _ _ _ _)) @ _); cbn.
      refine (ap (iterZ b n) (IH _) @ _).
      exact (ap (fun m => iterZ b m _) (zneg_zneg n)^ @ iterZ_neg_l sX b (zneg n) x).
  Defined.

  Definition sem_isEquiv {X : Type} (sX : isSet X) (a b : X ≃ X) (l : list (ℤ ⨿ ℤ))
    : isEquiv (sem a b l)
    := iso_to_isEquiv _ (sem a b (invl l)) (sem_invl a b sX l) (sem_invl_r sX a b l).

  (** Exercise [xca:normal-bicycle-equiv]. *)
  Definition normal_from_one (B : Bicyc) (x : bX B) (t : isEquiv (ev_bicyc B x))
    : isNormal B.
  Proof.
    intro x'.
    refine (ptrunc_rec (isEquiv_isProp _) _ (bconn B x x')). intros [l e].
    refine (isEquiv_homotopic (sem (ba B) (bb B) l ∘ ev_bicyc B x) _ _
              (comp_isEquiv t (sem_isEquiv (bX_isSet B) _ _ l))).
    intro w. unfold ev_bicyc. exact ((BicycEqv_sem w l x)^ @ ap (fst (fst w)) e^).
  Defined.

  (** Definition [def:cbid-bicycle]: the symmetry [x ↦ x'] of a normal
      bicycle, with [x ↦ x] the identity. *)
  Definition cbid {B : Bicyc} (nB : isNormal B) (x x' : bX B) : BicycEqv B B
    := eqinv (nB x) x'.

  Definition cbid_spec {B : Bicyc} (nB : isNormal B) (x x' : bX B)
    : fst (fst (cbid nB x x')) x = x'
    := eqinv_r (nB x) x'.

  Definition cbid_refl {B : Bicyc} (nB : isNormal B) (x : bX B)
    : cbid nB x x = path_to_BicycEqv refl
    := eqinv_l (nB x) (path_to_BicycEqv refl).

End BicycleIds.

(** ** Identifications of bicycles are commuting equivalences *)

Section BicycPaths.

  Context `{Univalence}.

  (** The total space of [BicycEqv B] is contractible. *)
  Definition Bicyc_total_isContr (B : Bicyc) : isContr {B' : Bicyc & BicycEqv B B'}.
  Proof.
    refine ((B; path_to_BicycEqv refl); _).
    intros [B' w].
    destruct B as [[X sX] [a [b c]]], B' as [[Y sY] [a' [b' c']]], w as [e [ha hb]].
    cbn in *.
    revert sY a' b' c' ha hb.
    enough (G : forall p : X = Y, forall (sY : isSet Y) (a' b' : Y ≃ Y)
                  (c' : ptrunc Y × isConnBy a' b')
                  (ha : fst (idtoeqv p) ∘ fst a = fst a' ∘ fst (idtoeqv p))
                  (hb : fst (idtoeqv p) ∘ fst b = fst b' ∘ fst (idtoeqv p)),
                  ((((X; sX); (a; (b; c))) : Bicyc); path_to_BicycEqv refl)
                  = ((((Y; sY); (a'; (b'; c'))) : Bicyc); (idtoeqv p; (ha; hb)))).
    { intros sY a' b' c' ha hb.
      pose (q := ptoe_etop e). clearbody q. revert ha hb. revert q.
      generalize (etop e). intros p q. destruct q. intros ha hb.
      exact (G p sY a' b' c' ha hb). }
    intro p. destruct p. intros sY a' b' c' ha hb.
    destruct (path_Eqv a a' ha). destruct (path_Eqv b b' hb).
    destruct (isSet_isProp X sX sY).
    destruct (prod_isProp ptrunc_isProp
                (Pi_isProp (fun x => Pi_isProp (fun x' => ptrunc_isProp))) c c').
    refine (pathpair refl _).
    exact (BicycEqv_path (B := ((X; sX); (a; (b; c)))) (B' := ((X; sX); (a; (b; c))))
             (path_to_BicycEqv refl) (idtoeqv refl; (ha; hb)) refl).
  Defined.

  (** Identifications of bicycles are the equivalences commuting with
      [a] and [b]. *)
  Definition path_to_BicycEqv_isEquiv (B B' : Bicyc) : isEquiv (@path_to_BicycEqv _ B B')
    := isEquiv_from_tot (fun B' => @path_to_BicycEqv _ B B')
         (contr_map_isEquiv (singleton_contr B) (Bicyc_total_isContr B) _) B'.

  Definition BicycEqv_to_path {B B' : Bicyc} (w : BicycEqv B B') : B = B'
    := eqinv (path_to_BicycEqv_isEquiv B B') w.

End BicycPaths.

Section BicycExercises.

  Context `{Univalence}.

  (** An evaluation map with merely inhabited fibers is an equivalence. *)
  Definition ev_isEquiv_of_surj (B : Bicyc) (x : bX B)
    (s : forall y, ptrunc (fiber (ev_bicyc B x) y)) : isEquiv (ev_bicyc B x)
    := fun y => isProp_inhabited_isContr (ev_bicyc_isInj B x y)
                  (ptrunc_rec (ev_bicyc_isInj B x y) idmap (s y)).

  (** Relabelling: if every list fixing [x] fixes [y], then [⟦ℓ⟧(x) ↦ ⟦ℓ⟧(y)]
      is a well-defined map. *)
  Section Relabel.

    Context (B : Bicyc) (x y : bX B)
      (HH : forall l, sem (ba B) (bb B) l x = x -> sem (ba B) (bb B) l y = y).

    Local Notation sm := (sem (ba B) (bb B)).

    Definition relabel_wd (l1 l2 : list (ℤ ⨿ ℤ)) (e : sm l1 x = sm l2 x)
      : sm l1 y = sm l2 y.
    Proof.
      pose (h := HH (app (invl l2) l1)
                   (sem_app _ _ _ _ _ @ ap (sm (invl l2)) e @ sem_invl _ _ (bX_isSet B) l2 x)).
      refine ((sem_invl_r (bX_isSet B) _ _ l2 _)^ @ ap (sm l2) _).
      exact ((sem_app _ _ _ _ _)^ @ h).
    Defined.

    Definition RelT (z : bX B) : Type
      := {y' : bX B & Ex (fun l => (z = sm l x) × (y' = sm l y))}.

    Definition RelT_isProp (z : bX B) : isProp (RelT z).
    Proof.
      intros [y1 h1] [y2 h2].
      refine (path_sigma_prop (fun _ => ptrunc_isProp) _).
      refine (ptrunc_rec (bX_isSet B _ _) _ h1). intros [l1 [e1 f1]].
      refine (ptrunc_rec (bX_isSet B _ _) _ h2). intros [l2 [e2 f2]].
      exact (f1 @ relabel_wd l1 l2 (e1^ @ e2) @ f2^).
    Defined.

    Definition RelT_isContr (z : bX B) : isContr (RelT z).
    Proof.
      refine (ptrunc_rec (isContr_isProp _) _ (bconn B x z)). intros [l e].
      exact (isProp_inhabited_isContr (RelT_isProp z) (sm l y; trunc (l; (e; refl)))).
    Defined.

    Definition relabel (z : bX B) : bX B := fst (fst (RelT_isContr z)).

    Definition relabel_sem (l : list (ℤ ⨿ ℤ)) : relabel (sm l x) = sm l y
      := ap fst (RelT_isProp _ (fst (RelT_isContr _)) (sm l y; trunc (l; (refl; refl)))).

    (** [relabel] commutes with any [f] with [f ∘ ⟦ℓ⟧ = ⟦cℓ⟧] for a fixed [c]. *)
    Definition relabel_comm (f : bX B -> bX B) (c : ℤ ⨿ ℤ)
      (hf : forall z, f z = sm (cons c nil) z) (z : bX B)
      : relabel (f z) = f (relabel z).
    Proof.
      refine (ptrunc_rec (bX_isSet B _ _) _ (bconn B x z)). intros [l e]. destruct e^.
      refine (ap relabel (hf _) @ _ @ (hf _)^ @ ap f (relabel_sem l)^).
      exact ((ap relabel (sem_app _ _ (cons c nil) l x))^ @ relabel_sem (app (cons c nil) l)
             @ sem_app _ _ (cons c nil) l y).
    Defined.

  End Relabel.

  Definition sem_one_a (B : Bicyc) (z : bX B)
    : fst (ba B) z = sem (ba B) (bb B) (cons (inl (iplus 1)) nil) z := refl.

  Definition sem_one_b (B : Bicyc) (z : bX B)
    : fst (bb B) z = sem (ba B) (bb B) (cons (inr (iplus 1)) nil) z := refl.

  (** A symmetry mapping [x] to [y] if [x] and [y] are fixed by the same lists. *)
  Definition relabel_sym (B : Bicyc) (x y : bX B)
    (HH : forall l, sem (ba B) (bb B) l x = x <-> sem (ba B) (bb B) l y = y)
    : {w : BicycEqv B B & fst (fst w) x = y}.
  Proof.
    pose (H1 := fun l => Overture.fst (HH l)). pose (H2 := fun l => Overture.snd (HH l)).
    pose (f := relabel B x y H1). pose (g := relabel B y x H2).
    assert (gf : forall z, g (f z) = z).
    { intro z. refine (ptrunc_rec (bX_isSet B _ _) _ (bconn B x z)). intros [l e]. destruct e^.
      exact (ap g (relabel_sem B x y H1 l) @ relabel_sem B y x H2 l). }
    assert (fg : forall z, f (g z) = z).
    { intro z. refine (ptrunc_rec (bX_isSet B _ _) _ (bconn B y z)). intros [l e]. destruct e^.
      exact (ap f (relabel_sem B y x H2 l) @ relabel_sem B x y H1 l). }
    refine (((f; iso_to_isEquiv f g gf fg);
             (ptw_inv (relabel_comm B x y H1 _ _ (sem_one_a B));
              ptw_inv (relabel_comm B x y H1 _ _ (sem_one_b B)))); _).
    exact (relabel_sem B x y H1 nil).
  Defined.

  (** [H_x], the lists fixing [x]. *)
  Definition Hx (B : Bicyc) (x : bX B) (l : list (ℤ ⨿ ℤ)) : Type
    := sem (ba B) (bb B) l x = x.

  (** The first exercise after [def:cbid-bicycle]: a bicycle is normal
      iff [H_x = H_y] for all [x, y]. *)
  Definition xca_normal_Hx (B : Bicyc)
    : isNormal B <-> (forall x y l, Hx B x l <-> Hx B y l).
  Proof.
    split.
    - intros nB x y l. unfold Hx. split; intro h.
      + pose (w := cbid nB x y).
        exact (ap (sem _ _ l) (cbid_spec nB x y)^ @ (BicycEqv_sem w l x)^
               @ ap (fst (fst w)) h @ cbid_spec nB x y).
      + pose (w := cbid nB y x).
        exact (ap (sem _ _ l) (cbid_spec nB y x)^ @ (BicycEqv_sem w l y)^
               @ ap (fst (fst w)) h @ cbid_spec nB y x).
    - intros HH x. apply ev_isEquiv_of_surj. intro y.
      destruct (relabel_sym B x y (HH x y)) as [w e].
      exact (trunc (w; e^)).
  Defined.

  (** Commuting bicycles. *)
  Definition isCommuting (B : Bicyc) : Type
    := fst (ba B) ∘ fst (bb B) = fst (bb B) ∘ fst (ba B).

  Definition sem_comm (B : Bicyc) (cB : isCommuting B) (f : bX B ≃ bX B)
    (hf : (f = ba B) + (f = bb B)) (l : list (ℤ ⨿ ℤ)) (z : bX B)
    : fst f (sem (ba B) (bb B) l z) = sem (ba B) (bb B) l (fst f z).
  Proof.
    induction l as [|[n|n] l IH]; cbn.
    - exact refl.
    - refine (iterZ_nat (bX_isSet B) (ba B) (ba B) (fst f) _ n _ @ ap (iterZ (ba B) n) IH).
      intro u. destruct hf as [e|e]; destruct e^.
      + exact refl.
      + exact (ptw cB u)^.
    - refine (iterZ_nat (bX_isSet B) (bb B) (bb B) (fst f) _ n _ @ ap (iterZ (bb B) n) IH).
      intro u. destruct hf as [e|e]; destruct e^.
      + exact (ptw cB u).
      + exact refl.
  Defined.

  (** The second exercise after [def:cbid-bicycle], on commuting
      bicycles, first part: they are normal. *)
  Definition commuting_isNormal (B : Bicyc) (cB : isCommuting B) : isNormal B.
  Proof.
    intro x. apply ev_isEquiv_of_surj. intro y.
    refine (ptrunc_rec ptrunc_isProp _ (bconn B x y)). intros [l e].
    refine (trunc (((sem _ _ l; sem_isEquiv (bX_isSet B) _ _ l);
                    (ptw_inv (fun z => (sem_comm B cB _ (inl refl) l z)^);
                     ptw_inv (fun z => (sem_comm B cB _ (inr refl) l z)^))); e)).
  Defined.

  (** The second part fails as stated (NOTE for the book): the commuting
      bicycle [(𝟚, swap, swap)] is not of the form
      [(X × Y, t × id, id × u)], since [t × id = id × u] forces [t = id]
      and [u = id]. *)
  Definition swap_connBy : isConnBy swapEqv swapEqv.
  Proof.
    refine (connBy_from_base _ _ (IsHSet_isSet _) yes _).
    intros []; apply trunc.
    - exact (nil; refl).
    - exact (cons (inl (iplus 1)) nil; refl).
  Defined.

  Definition SwapBicyc : Bicyc
    := ((Bool; IsHSet_isSet _); (swapEqv; (swapEqv; (trunc yes; swap_connBy)))).

  Definition SwapBicyc_isCommuting : isCommuting SwapBicyc := refl.

  Definition SwapBicyc_not_product
    : ¬ {X : Type & {Y : Type & {t : X ≃ X & {u : Y ≃ Y & {e : X × Y ≃ Bool &
          (forall x y, fst e (fst t x; y) = negb (fst e (x; y)))
          × (forall x y, fst e (x; fst u y) = negb (fst e (x; y)))}}}}}.
  Proof.
    intros [X [Y [t [u [e [ht hu]]]]]].
    pose (w := eqinv (snd e) yes). destruct w as [x y].
    assert (E : (fst t x; y) = (x; fst u y) :> X × Y)
      by exact (Eqv_inj e (ht x y @ (hu x y)^)).
    pose (E1 := ap fst E). cbn in E1.
    pose (h := ht x y). rewrite E1 in h.
    destruct (fst e (x; y)); exact (Bool.false_ne_true h^) || exact (Bool.false_ne_true h).
  Defined.

  (** The third exercise after [def:cbid-bicycle]: for a normal bicycle,
      lists are equivalent ([⟦ℓ⟧(x₀) = ⟦ℓ'⟧(x₀)]) iff [⟦ℓ⟧ = ⟦ℓ'⟧]. *)
  Definition xca_lists_equiv (B : Bicyc) (nB : isNormal B) (x0 : bX B)
    (l l' : list (ℤ ⨿ ℤ))
    : sem (ba B) (bb B) l x0 = sem (ba B) (bb B) l' x0
      <-> sem (ba B) (bb B) l = sem (ba B) (bb B) l'.
  Proof.
    split.
    - intro h. apply ptw_inv. intro x.
      pose (w := cbid nB x0 x).
      exact (ap (sem _ _ l) (cbid_spec nB x0 x)^ @ (BicycEqv_sem w l x0)^
             @ ap (fst (fst w)) h @ BicycEqv_sem w l' x0
             @ ap (sem _ _ l') (cbid_spec nB x0 x)).
    - intro h. exact (ptw h x0).
  Defined.

  (** Composition of symmetries. *)
  Definition BicycEqv_comp {B B' B'' : Bicyc} (w : BicycEqv B B') (w' : BicycEqv B' B'')
    : BicycEqv B B''.
  Proof.
    refine (Eqv_comp (fst w) (fst w'); (ptw_inv _; ptw_inv _)); intro x.
    - exact (ap (fst (fst w')) (ptw (fst (snd w)) x) @ ptw (fst (snd w')) (fst (fst w) x)).
    - exact (ap (fst (fst w')) (ptw (snd (snd w)) x) @ ptw (snd (snd w')) (fst (fst w) x)).
  Defined.

  (** Remark [rem:bicycle-list-concat]. *)
  Definition rem_bicycle_list_concat (B : Bicyc) (nB : isNormal B) (x0 : bX B)
    (l l' : list (ℤ ⨿ ℤ))
    : (fst (fst (cbid nB x0 (sem (ba B) (bb B) l x0)))
         ∘ fst (fst (cbid nB x0 (sem (ba B) (bb B) l' x0)))
       = fst (fst (cbid nB x0 (sem (ba B) (bb B) (app l' l) x0))))
      × (fst (fst (cbid nB (sem (ba B) (bb B) l x0) x0))
           ∘ fst (fst (cbid nB (sem (ba B) (bb B) l' x0) x0))
         = fst (fst (cbid nB (sem (ba B) (bb B) (app l l') x0) x0))).
  Proof.
    split.
    - refine (evisinj_bicycle x0 (BicycEqv_comp (cbid nB x0 (sem _ _ l' x0)) (cbid nB x0 (sem _ _ l x0)))
                (cbid nB x0 (sem _ _ (app l' l) x0)) _).
      exact (ap (fst (fst (cbid nB x0 (sem _ _ l x0)))) (cbid_spec nB x0 (sem _ _ l' x0))
             @ BicycEqv_sem _ l' x0 @ ap (sem _ _ l') (cbid_spec nB x0 (sem _ _ l x0))
             @ (sem_app _ _ l' l x0)^ @ (cbid_spec nB x0 _)^).
    - refine (evisinj_bicycle (sem _ _ (app l l') x0)
                (BicycEqv_comp (cbid nB (sem _ _ l' x0) x0) (cbid nB (sem _ _ l x0) x0))
                (cbid nB (sem _ _ (app l l') x0) x0) _).
      refine (ap (fun z => fst (fst (cbid nB (sem _ _ l x0) x0))
                             (fst (fst (cbid nB (sem _ _ l' x0) x0)) z)) (sem_app _ _ l l' x0) @ _).
      refine (ap (fst (fst (cbid nB (sem _ _ l x0) x0)))
                (BicycEqv_sem _ l (sem _ _ l' x0) @ ap (sem _ _ l) (cbid_spec nB (sem _ _ l' x0) x0)) @ _).
      exact (cbid_spec nB (sem _ _ l x0) x0 @ (cbid_spec nB (sem _ _ (app l l') x0) x0)^).
  Defined.

End BicycExercises.

Section Frieze.

  Context `{Univalence}.

  Definition zneg_zs (n : ℤ) : zneg (zs n) = zp (zneg n).
  Proof.
    apply toInt_inj.
    refine (toInt_zneg _ @ ap int_neg (toInt_zs _) @ int_neg_succ _ @ _).
    exact (ap int_pred (toInt_zneg n)^ @ (toInt_zp _)^).
  Defined.

  Definition zneg_zp (n : ℤ) : zneg (zp n) = zs (zneg n).
  Proof.
    apply toInt_inj.
    refine (toInt_zneg _ @ ap int_neg (toInt_zp _) @ int_neg_pred _ @ _).
    exact (ap int_succ (toInt_zneg n)^ @ (toInt_zs _)^).
  Defined.

  Definition zneg_0 : zneg (iplus 0) = iplus 0 := toInt_inj (x := zneg (iplus 0)) (y := iplus 0) (toInt_zneg _).

  Definition zadd_zs_l (m n : ℤ) : zadd (zs m) n = zs (zadd m n).
  Proof.
    apply toInt_inj.
    refine (toInt_zadd _ _ @ ap (fun u => int_add u _) (toInt_zs _) @ int_add_succ_l _ _ @ _).
    exact (ap int_succ (toInt_zadd _ _)^ @ (toInt_zs _)^).
  Defined.

  Definition zadd_zp_l (m n : ℤ) : zadd (zp m) n = zp (zadd m n).
  Proof.
    apply toInt_inj.
    refine (toInt_zadd _ _ @ ap (fun u => int_add u _) (toInt_zp _) @ int_add_pred_l _ _ @ _).
    exact (ap int_pred (toInt_zadd _ _)^ @ (toInt_zp _)^).
  Defined.

  Definition zadd_0_l' (n : ℤ) : zadd (iplus 0) n = n
    := toInt_inj (y := n) (toInt_zadd (iplus 0) n).

  Local Notation D := DihedralBicyc.
  Local Notation x0 := (inl (iplus 0) : bX DihedralBicyc).

  (** Translations [τ_n] and reflections [ρ_n] of the dihedral bicycle. *)
  Definition dtr (n : ℤ) (x : ℤ ⨿ ℤ) : ℤ ⨿ ℤ
    := match x with inl m => inl (zadd m n) | inr m => inr (zadd m n) end.

  Definition dre (n : ℤ) (x : ℤ ⨿ ℤ) : ℤ ⨿ ℤ
    := match x with inl m => inr (zadd (zneg m) n) | inr m => inl (zadd (zneg m) n) end.

  Definition dtr_eqv (n : ℤ) : (ℤ ⨿ ℤ) ≃ (ℤ ⨿ ℤ).
  Proof.
    refine (mkEqv (dtr n) (dtr (zneg n)) _ _); intros [m|m]; cbn; apply ap.
    - exact (zsub_zadd m n).
    - exact (zsub_zadd m n).
    - exact (zadd_zsub m n).
    - exact (zadd_zsub m n).
  Defined.

  Definition dre_inv (n : ℤ) (x : ℤ ⨿ ℤ) : dre n (dre n x) = x.
  Proof.
    destruct x as [m|m]; cbn; apply ap; apply toInt_inj;
      refine (toInt_zadd _ _ @ ap (fun u => int_add u _) (toInt_zneg _) @ _);
      refine (ap (fun u => int_add (int_neg u) _) (toInt_zadd _ _) @ _);
      refine (ap (fun u => int_add (int_neg (int_add u _)) _) (toInt_zneg _) @ _);
      refine (ap (fun u => int_add u _) (int_neg_add _ _) @ _);
      refine ((int_add_assoc _ _ _)^ @ _);
      exact (ap (int_add _) (int_add_neg_l _) @ int_add_0_r _ @ int_neg_neg _).
  Defined.

  Definition dre_eqv (n : ℤ) : (ℤ ⨿ ℤ) ≃ (ℤ ⨿ ℤ) := mkEqv (dre n) (dre n) (dre_inv n) (dre_inv n).

  Definition dtr_sym (n : ℤ) : BicycEqv D D.
  Proof.
    refine (dtr_eqv n; (ptw_inv _; ptw_inv _)); intros [m|m]; cbn.
    - exact (ap inl (zadd_zs_l m n)).
    - exact (ap inr (zadd_zp_l m n)).
    - exact refl.
    - exact refl.
  Defined.

  Definition dre_sym (n : ℤ) : BicycEqv D D.
  Proof.
    refine (dre_eqv n; (ptw_inv _; ptw_inv _)); intros [m|m]; cbn.
    - exact (ap inr (ap (fun u => zadd u n) (zneg_zs m) @ zadd_zp_l _ _)).
    - exact (ap inl (ap (fun u => zadd u n) (zneg_zp m) @ zadd_zs_l _ _)).
    - exact refl.
    - exact refl.
  Defined.

  (** The infinite dihedral bicycle is normal. *)
  Definition dihedral_isNormal : isNormal D.
  Proof.
    apply (normal_from_one D x0). apply ev_isEquiv_of_surj.
    intros [n|n]; apply trunc.
    - exact (dtr_sym n; ap inl (zadd_0_l' n)^).
    - refine (dre_sym n; ap inr _).
      exact (ap (fun u => zadd u n) zneg_0 @ zadd_0_l' n)^.
  Defined.

  (** [T] and [R] of [rem:inf-dihedral-frieze], concretely: [T] is the
      translation by [-1] and [R] the reflection [ρ_0]. *)
  Definition dT (x : ℤ ⨿ ℤ) : ℤ ⨿ ℤ := match x with inl m => inl (zp m) | inr m => inr (zp m) end.

  Definition dR (x : ℤ ⨿ ℤ) : ℤ ⨿ ℤ
    := match x with inl m => inr (zneg m) | inr m => inl (zneg m) end.

  Definition dT_spec (nD : isNormal D)
    : fst (fst (cbid nD (fst (ba D) x0) x0)) = dT.
  Proof.
    pose (w := dtr_sym (zneg (iplus 1))).
    assert (E : cbid nD (fst (ba D) x0) x0 = w).
    { refine (_ @ eqinv_l (nD (fst (ba D) x0)) w).
      apply ap. cbn. apply ap.
      exact (zsub_zadd (iplus 0) (iplus 1))^. }
    refine (ap (fun w => fst (fst w)) E @ _).
    apply ptw_inv. intros [m|m]; cbn; apply ap; apply toInt_inj;
      refine (toInt_zadd _ _ @ _ @ (toInt_zp _)^);
      exact (int_add_pred_r _ _ @ ap int_pred (int_add_0_r _)).
  Defined.

  Definition dR_spec (nD : isNormal D)
    : fst (fst (cbid nD (fst (bb D) x0) x0)) = dR.
  Proof.
    pose (w := dre_sym (iplus 0)).
    assert (E : cbid nD (fst (bb D) x0) x0 = w).
    { refine (_ @ eqinv_l (nD (fst (bb D) x0)) w).
      apply ap. cbn. apply ap.
      exact (ap (fun u => zadd u _) zneg_0 @ zadd_0_l' _)^. }
    refine (ap (fun w => fst (fst w)) E @ _).
    apply ptw_inv. intros [m|m]; exact refl.
  Defined.

  Definition dE (x : ℤ ⨿ ℤ) : ℤ ⨿ ℤ := match x with inl m => inl (zneg m) | inr m => inr m end.

  Definition dE_eqv : (ℤ ⨿ ℤ) ≃ (ℤ ⨿ ℤ).
  Proof. refine (mkEqv dE dE _ _); intros [m|m]; cbn; try exact refl; exact (ap inl (zneg_zneg m)). Defined.

  (** The exercise after [rem:inf-dihedral-frieze]: the infinite dihedral
      bicycle [(X,a,b)] is identified with [(X,T,R)], via
      [inl(n) ↦ inl(-n)], [inr(n) ↦ inr(n)]. *)
  Definition xca_frieze (nD : isNormal D)
    : let T := fst (cbid nD (fst (ba D) x0) x0) in
      let R := fst (cbid nD (fst (bb D) x0) x0) in
      {e : bX D ≃ bX D & (fst e ∘ fst (ba D) = fst T ∘ fst e)
                         × (fst e ∘ fst (bb D) = fst R ∘ fst e)}.
  Proof.
    cbn. refine (dE_eqv; (_; _)).
    - rewrite (dT_spec nD). apply ptw_inv. intros [m|m]; cbn.
      + exact (ap inl (zneg_zs m)).
      + exact refl.
    - rewrite (dR_spec nD). apply ptw_inv. intros [m|m]; cbn.
      + exact (ap inr (zneg_zneg m)^).
      + exact refl.
  Defined.

End Frieze.

(** The two [6]-element bicycles of the last exercise: the hexagon, with
    [a = (0 1)(2 3)(4 5)] and [b = (1 2)(3 4)(5 0)], and the prism, with
    [a] rotating the inner triangle [p0 ← p1 ← p2 ← p0] and the outer one
    [p3 → p4 → p5 → p3], and [b] swapping [pᵢ] and [p(i+3)]. *)
Inductive Six : Type0 := p0 | p1 | p2 | p3 | p4 | p5.

Section SixBicycles.

  Context `{Univalence}.

  Definition six_eqb (k l : Six) : Bool
    := match k, l with
       | p0, p0 | p1, p1 | p2, p2 | p3, p3 | p4, p4 | p5, p5 => true
       | _, _ => false end.

  Definition Six_isDecSet : isDecSet Six.
  Proof.
    apply hedberg. intros k l.
    destruct (dec_paths (six_eqb k l) true) as [e|n].
    - left. destruct k, l; try exact refl; destruct (false_ne_true e).
    - right. intro p. destruct p. destruct k; exact (n refl).
  Defined.

  Definition Six_isSet : isSet Six := fun k l => fst (Six_isDecSet k l).

  Definition ha (k : Six) : Six
    := match k with p0 => p1 | p1 => p0 | p2 => p3 | p3 => p2 | p4 => p5 | p5 => p4 end.

  Definition hb (k : Six) : Six
    := match k with p0 => p5 | p5 => p0 | p1 => p2 | p2 => p1 | p3 => p4 | p4 => p3 end.

  Definition haEqv : Six ≃ Six.
  Proof. refine (mkEqv ha ha _ _); intros []; exact refl. Defined.

  Definition hbEqv : Six ≃ Six.
  Proof. refine (mkEqv hb hb _ _); intros []; exact refl. Defined.

  Definition hexagon_connBy : isConnBy haEqv hbEqv.
  Proof.
    refine (connBy_from_base _ _ Six_isSet p0 _).
    intros []; apply trunc.
    - exact (nil; refl).
    - exact (cons (inl (iplus 1)) nil; refl).
    - exact (cons (inr (iplus 1)) (cons (inl (iplus 1)) nil); refl).
    - exact (cons (inl (iplus 1)) (cons (inr (iplus 1)) (cons (inl (iplus 1)) nil)); refl).
    - exact (cons (inr (iplus 1)) (cons (inl (iplus 1)) (cons (inr (iplus 1))
               (cons (inl (iplus 1)) nil))); refl).
    - exact (cons (inr (iplus 1)) nil; refl).
  Defined.

  Definition HexagonBicyc : Bicyc
    := ((Six; Six_isSet); (haEqv; (hbEqv; (trunc p0; hexagon_connBy)))).

  Definition pa (k : Six) : Six
    := match k with p1 => p0 | p2 => p1 | p0 => p2 | p3 => p4 | p4 => p5 | p5 => p3 end.

  Definition pa' (k : Six) : Six
    := match k with p0 => p1 | p1 => p2 | p2 => p0 | p4 => p3 | p5 => p4 | p3 => p5 end.

  Definition pb (k : Six) : Six
    := match k with p0 => p3 | p3 => p0 | p1 => p4 | p4 => p1 | p2 => p5 | p5 => p2 end.

  Definition paEqv : Six ≃ Six.
  Proof. refine (mkEqv pa pa' _ _); intros []; exact refl. Defined.

  Definition pbEqv : Six ≃ Six.
  Proof. refine (mkEqv pb pb _ _); intros []; exact refl. Defined.

  Definition prism_connBy : isConnBy paEqv pbEqv.
  Proof.
    refine (connBy_from_base _ _ Six_isSet p0 _).
    intros []; apply trunc.
    - exact (nil; refl).
    - exact (cons (inl (iplus 2)) nil; refl).
    - exact (cons (inl (iplus 1)) nil; refl).
    - exact (cons (inr (iplus 1)) nil; refl).
    - exact (cons (inr (iplus 1)) (cons (inl (iplus 2)) nil); refl).
    - exact (cons (inr (iplus 1)) (cons (inl (iplus 1)) nil); refl).
  Defined.

  Definition PrismBicyc : Bicyc
    := ((Six; Six_isSet); (paEqv; (pbEqv; (trunc p0; prism_connBy)))).

End SixBicycles.

(** ** Permutations of [Fin 3] *)

Definition q0 : Fin 3 := inl (inl (inr tt)).
Definition q1 : Fin 3 := inl (inr tt).
Definition q2 : Fin 3 := inr tt.

Definition fin3_cases (P : Fin 3 -> Type) (h0 : P q0) (h1 : P q1) (h2 : P q2) (x : Fin 3) : P x.
Proof. destruct x as [[[[]|[]]|[]]|[]]; assumption. Defined.

Ltac fin3_destruct u := destruct u as [[[[]|[]]|[]]|[]].

Ltac fin3_absurd :=
  match goal with
  | n : ?a <> ?a |- _ => destruct (n refl)
  end.

(** An equivalence of [Fin 3] is determined by its values at [0] and [1]. *)
Definition fin3_perm_ext `{Funext} (f g : Fin 3 ≃ Fin 3)
  (e0 : fst f q0 = fst g q0) (e1 : fst f q1 = fst g q1) : f = g.
Proof.
  apply path_Eqv. apply ptw_inv.
  refine (fin3_cases _ e0 e1 _).
  assert (nf0 : fst f q2 <> fst f q0) by (intro h; exact (inl_ne_inr _ _ (Eqv_inj f h)^)).
  assert (nf1 : fst f q2 <> fst f q1) by (intro h; exact (inl_ne_inr _ _ (Eqv_inj f h)^)).
  assert (ng0 : fst g q2 <> fst g q0) by (intro h; exact (inl_ne_inr _ _ (Eqv_inj g h)^)).
  assert (ng1 : fst g q2 <> fst g q1) by (intro h; exact (inl_ne_inr _ _ (Eqv_inj g h)^)).
  assert (n01 : fst f q0 <> fst f q1).
  { intro h. pose (h' := ap (fun x : Fin 3 => match x with inl (inl _) => true | _ => false end)
                          (Eqv_inj f h)). exact (Bool.false_ne_true h'^). }
  revert nf0 nf1 ng0 ng1 n01. rewrite e0, e1.
  generalize (fst g q0) (fst g q1) (fst f q2) (fst g q2).
  intros u0 u1 u2 v2. fin3_destruct u0; fin3_destruct u1; fin3_destruct u2; fin3_destruct v2;
    intros; try exact refl; fin3_absurd.
Defined.

(** Naturality of [⟦ℓ⟧] for maps commuting with the generators. *)
Definition sem_nat {X Y : Type} (sY : isSet Y) (a b : X ≃ X) (a' b' : Y ≃ Y) (f : X -> Y)
  (ha : forall x, f (fst a x) = fst a' (f x)) (hb : forall x, f (fst b x) = fst b' (f x))
  (l : list (ℤ ⨿ ℤ)) (x : X) : f (sem a b l x) = sem a' b' l (f x).
Proof.
  induction l as [|[n|n] l IH]; cbn.
  - exact refl.
  - exact (iterZ_nat sY a a' f ha n _ @ ap (iterZ a' n) IH).
  - exact (iterZ_nat sY b b' f hb n _ @ ap (iterZ b' n) IH).
Defined.

Section Cayley.

  Context `{Univalence}.

  (** The set of bijections from [Fin 3] to a set [S]. *)
  Definition E3 (S : SetU) : SetU := ((Fin 3 ≃ fst S); Eqv_sets_isSet (snd S)).

  Definition Aut3 : Type := fst (E3 (FinSetU 3)).

  Definition Aut3_isSet : isSet Aut3 := snd (E3 (FinSetU 3)).

  (** Pre- and postcomposition. *)
  Definition preEqv {S : SetU} (σ : Aut3) : fst (E3 S) ≃ fst (E3 S).
  Proof.
    refine (mkEqv (fun f => Eqv_comp σ f) (fun f => Eqv_comp (Eqv_inv σ) f) _ _);
      intro f; apply path_Eqv; apply ptw_inv; intro x; cbn.
    - exact (ap (fst f) (eqinv_r (snd σ) x)).
    - exact (ap (fst f) (eqinv_l (snd σ) x)).
  Defined.

  Definition postEqv {S S' : SetU} (σ : fst S ≃ fst S') : fst (E3 S) ≃ fst (E3 S').
  Proof.
    refine (mkEqv (fun f => Eqv_comp f σ) (fun f => Eqv_comp f (Eqv_inv σ)) _ _);
      intro f; apply path_Eqv; apply ptw_inv; intro x; cbn.
    - exact (eqinv_l (snd σ) _).
    - exact (eqinv_r (snd σ) _).
  Defined.

  Definition isConnBy_isProp {X : Type} (a b : X ≃ X) : isProp (isConnBy a b)
    := Pi_isProp (fun _ => Pi_isProp (fun _ => ptrunc_isProp)).

  (** Section variables of type [Aut3] make elaboration very slow
      (universe constraints), so [σa], [σb] are explicit arguments. *)
  Definition isCayleyConn (σa σb : Aut3) : Type
    := isConnBy (preEqv (S := FinSetU 3) σa) (preEqv (S := FinSetU 3) σb).

  (** A bicycle [B0] with an equivalence [E : bX B0 ≃ Aut3] turning [a] and
      [b] into [- ∘ σa] and [- ∘ σb] gives connectivity of the latter. *)
  Definition cayley_conn0 (σa σb : Aut3) (B0 : Bicyc) (E : bX B0 ≃ Aut3)
    (hEa : forall x, fst E (fst (ba B0) x) = fst (preEqv (S := FinSetU 3) σa) (fst E x))
    (hEb : forall x, fst E (fst (bb B0) x) = fst (preEqv (S := FinSetU 3) σb) (fst E x))
    : isCayleyConn σa σb.
  Proof.
    intros f g.
    refine (ptrunc_rec ptrunc_isProp _ (bconn B0 (eqinv (snd E) f) (eqinv (snd E) g))).
    intros [l e]. refine (trunc (l; _)).
    refine ((eqinv_r (snd E) g)^ @ ap (fst E) e @ _).
    refine (sem_nat (is_ntype_Eqv 0 E (bX_isSet B0)) (ba B0) (bb B0) _ _ (fst E) hEa hEb l _ @ _).
    exact (ap (sem _ _ l) (eqinv_r (snd E) f)).
  Defined.

  Local Notation C3 := (component SetU (FinSetU 3)).

  Definition cbase : C3 := (FinSetU 3; trunc refl).

  Definition cayley_conn (σa σb : Aut3) (c0 : isCayleyConn σa σb)
    (S : SetU) (p : ptrunc (FinSetU 3 = S))
    : isConnBy (preEqv (S := S) σa) (preEqv (S := S) σb).
  Proof.
    refine (ptrunc_rec (isConnBy_isProp _ _) _ p).
    intro q. destruct q. exact c0.
  Defined.

  (** The Cayley bicycle [(Fin 3 ≃ S, - ∘ σa, - ∘ σb)] of a [3]-element set [S]. *)
  Definition Kc (σa σb : Aut3) (c0 : isCayleyConn σa σb) (u : C3) : Bicyc.
  Proof.
    refine (E3 (fst u); _).
    refine (preEqv σa; _). refine (preEqv σb; _). refine (_; _).
    - exact (ptrunc_rec ptrunc_isProp (fun p : FinSetU 3 = fst u => trunc (idtoeqv (ap fst p)))
               (snd u)).
    - exact (cayley_conn σa σb c0 (fst u) (snd u)).
  Defined.

  Definition E_Kc (σa σb : Aut3) (B0 : Bicyc) (E : bX B0 ≃ Aut3)
    (hEa : forall x, fst E (fst (ba B0) x) = fst (preEqv (S := FinSetU 3) σa) (fst E x))
    (hEb : forall x, fst E (fst (bb B0) x) = fst (preEqv (S := FinSetU 3) σb) (fst E x))
    : BicycEqv B0 (Kc σa σb (cayley_conn0 σa σb B0 E hEa hEb) cbase)
    := (E; (ptw_inv hEa; ptw_inv hEb)).

  Definition post (σa σb : Aut3) (c0 : isCayleyConn σa σb) {u v : C3}
    (σ : fst (fst u) ≃ fst (fst v)) : BicycEqv (Kc σa σb c0 u) (Kc σa σb c0 v).
  Proof.
    refine (postEqv (S := fst u) (S' := fst v) σ; (ptw_inv _; ptw_inv _));
      intro f; apply path_Eqv; exact refl.
  Defined.

  Definition ap_Kc_post (σa σb : Aut3) (c0 : isCayleyConn σa σb) {u v : C3} (p : u = v)
    : path_to_BicycEqv (ap (Kc σa σb c0) p)
      = post σa σb c0 (idtoeqv (ap (fun w : C3 => fst (fst w)) p)).
  Proof.
    destruct p. apply BicycEqv_path. apply ptw_inv. intro f. apply path_Eqv. exact refl.
  Defined.

  Definition post_isEquiv0 (σa σb : Aut3) (c0 : isCayleyConn σa σb)
    : isEquiv (@post σa σb c0 cbase cbase).
  Proof.
    refine (iso_to_isEquiv _ (fun w => fst (fst w) (idEqv (Fin 3))) _ _).
    - intro σ. apply path_Eqv. exact refl.
    - intro w. refine (BicycEqv_path (B := Kc σa σb c0 cbase) (B' := Kc σa σb c0 cbase) _ _ _).
      apply (evisinj_bicycle (B := Kc σa σb c0 cbase) (B' := Kc σa σb c0 cbase) (idEqv (Fin 3))).
      apply path_Eqv. exact refl.
  Defined.

  Definition C3_carrier_ap_isEquiv (u v : C3)
    : isEquiv (@ap _ _ (fun w : C3 => fst (fst w)) u v).
  Proof.
    refine (isEquiv_homotopic (fun p : u = v => ap fst (ap fst p)) _ _ _).
    - intro p. exact (ap_compose fst fst p)^.
    - exact (comp_isEquiv (isInj_ap_isEquiv (fst_isInj (fun _ => ptrunc_isProp)) u v)
               (isInj_ap_isEquiv (fst_isInj (fun X => isSet_isProp X)) _ _)).
  Defined.

  Definition ap_Kc_isEquiv (σa σb : Aut3) (c0 : isCayleyConn σa σb)
    : isEquiv (@ap _ _ (Kc σa σb c0) cbase cbase).
  Proof.
    refine (two_of_three_f (ap (Kc σa σb c0))
              (fun p => post σa σb c0 (idtoeqv (ap (fun w : C3 => fst (fst w)) p)))
              path_to_BicycEqv (ptw_inv (ap_Kc_post σa σb c0)) _ (path_to_BicycEqv_isEquiv _ _)).
    exact (comp_isEquiv (comp_isEquiv (C3_carrier_ap_isEquiv cbase cbase) (ua _ _))
             (post_isEquiv0 σa σb c0)).
  Defined.

  (** [Kc] as a map of components. *)
  Definition Kc' (σa σb : Aut3) (c0 : isCayleyConn σa σb) (u : C3)
    : component Bicyc (Kc σa σb c0 cbase)
    := (Kc σa σb c0 u; ptrunc_rec ptrunc_isProp (fun p : cbase = u => trunc (ap (Kc σa σb c0) p))
                         (snd (component_isConn (FinSetU 3)) cbase u)).

  Definition Kc'_isEquiv (σa σb : Aut3) (c0 : isCayleyConn σa σb) : isEquiv (Kc' σa σb c0).
  Proof.
    refine (snd (conn_isEquiv_iff_point _ (component_isConn _) (component_isConn _) cbase) _).
    refine (two_of_three_f (ap (Kc' σa σb c0)) (ap (Kc σa σb c0)) (ap fst)
              (ptw_inv (fun p => (ap_compose (Kc' σa σb c0) fst p)^))
              (ap_Kc_isEquiv σa σb c0) _).
    exact (isInj_ap_isEquiv (fst_isInj (fun _ => ptrunc_isProp)) _ _).
  Defined.

  (** [Σ_3] is the automorphism group of the Cayley bicycle. *)
  Definition SG3_AutKc (σa σb : Aut3) (c0 : isCayleyConn σa σb)
    : SG 3 = AutG Bicyc_isGrpd (Kc σa σb c0 cbase).
  Proof.
    apply path_Group.
    refine ((Kc' σa σb c0; _); Kc'_isEquiv σa σb c0).
    exact (path_sigma_prop (fun _ => ptrunc_isProp)
             (u := ((Kc σa σb c0 cbase; trunc refl) : component Bicyc (Kc σa σb c0 cbase)))
             (v := Kc' σa σb c0 cbase) refl).
  Defined.

End Cayley.

(** ** The six bicycles *)

Section SixCayley.

  Context `{Univalence}.


  Definition pm (v0 v1 v2 : Fin 3) (x : Fin 3) : Fin 3
    := match x with inl (inl (inr _)) => v0 | inl (inr _) => v1 | _ => v2 end.

  Definition idp : Aut3. Proof. exact (idEqv (Fin 3)). Defined.
  Definition s01 : Aut3. Proof. refine (mkEqv (pm q1 q0 q2) (pm q1 q0 q2) _ _); intro x; fin3_destruct x; exact refl. Defined.
  Definition s12 : Aut3. Proof. refine (mkEqv (pm q0 q2 q1) (pm q0 q2 q1) _ _); intro x; fin3_destruct x; exact refl. Defined.
  Definition s02 : Aut3. Proof. refine (mkEqv (pm q2 q1 q0) (pm q2 q1 q0) _ _); intro x; fin3_destruct x; exact refl. Defined.
  Definition cyc3 : Aut3. Proof. refine (mkEqv (pm q1 q2 q0) (pm q2 q0 q1) _ _); intro x; fin3_destruct x; exact refl. Defined.
  Definition cyc3i : Aut3. Proof. refine (mkEqv (pm q2 q0 q1) (pm q1 q2 q0) _ _); intro x; fin3_destruct x; exact refl. Defined.

  Definition Aut3_inj01 (f : Aut3) : fst f q0 <> fst f q1.
  Proof.
    intro h. pose (h' := ap (fun x : Fin 3 => match x with inl (inl _) => true | _ => false end)
                          (Eqv_inj f h)). exact (Bool.false_ne_true h'^).
  Defined.

  (** Decoding a permutation from its values at [0] and [1]. *)
  Definition dec6 (k01 k10 k12 k21 k20 k02 : Six) (u v : Fin 3) : Six
    := match u, v with
       | inl (inl (inr _)), inl (inr _) => k01
       | inl (inr _), inl (inl (inr _)) => k10
       | inl (inr _), inr _ => k12
       | inr _, inl (inr _) => k21
       | inr _, inl (inl (inr _)) => k20
       | inl (inl (inr _)), inr _ => k02
       | _, _ => p0 end.

  Definition hexE (k : Six) : Aut3
    := match k with p0 => idp | p1 => s01 | p2 => cyc3 | p3 => s02 | p4 => cyc3i | p5 => s12 end.

  Definition hexE_dec' (u v : Fin 3) (n : u <> v) (f : Fin 3 ≃ Fin 3)
    (e0 : fst f q0 = u) (e1 : fst f q1 = v) : hexE (dec6 p0 p1 p2 p3 p4 p5 u v) = f.
  Proof.
    apply fin3_perm_ext; [refine (_ @ e0^) | refine (_ @ e1^)]; clear e0 e1; revert n;
      fin3_destruct u; fin3_destruct v; intros; try exact refl; fin3_absurd.
  Defined.

  Definition hexE_dec (f : Fin 3 ≃ Fin 3) : hexE (dec6 p0 p1 p2 p3 p4 p5 (fst f q0) (fst f q1)) = f
    := hexE_dec' _ _ (Aut3_inj01 f) f refl refl.

  Definition hexEqv : bX HexagonBicyc ≃ Aut3.
  Proof.
    refine (mkEqv hexE (fun f => dec6 p0 p1 p2 p3 p4 p5 (fst f q0) (fst f q1)) _ _).
    - intros []; exact refl.
    - exact hexE_dec.
  Defined.

  Definition prismE (k : Six) : Aut3
    := match k with p0 => idp | p1 => cyc3i | p2 => cyc3 | p3 => s01 | p4 => s12 | p5 => s02 end.

  Definition prismE_dec' (u v : Fin 3) (n : u <> v) (f : Fin 3 ≃ Fin 3)
    (e0 : fst f q0 = u) (e1 : fst f q1 = v) : prismE (dec6 p0 p3 p2 p5 p1 p4 u v) = f.
  Proof.
    apply fin3_perm_ext; [refine (_ @ e0^) | refine (_ @ e1^)]; clear e0 e1; revert n;
      fin3_destruct u; fin3_destruct v; intros; try exact refl; fin3_absurd.
  Defined.

  Definition prismE_dec (f : Fin 3 ≃ Fin 3) : prismE (dec6 p0 p3 p2 p5 p1 p4 (fst f q0) (fst f q1)) = f
    := prismE_dec' _ _ (Aut3_inj01 f) f refl refl.

  Definition prismEqv : bX PrismBicyc ≃ Aut3.
  Proof.
    refine (mkEqv prismE (fun f => dec6 p0 p3 p2 p5 p1 p4 (fst f q0) (fst f q1)) _ _).
    - intros []; exact refl.
    - exact prismE_dec.
  Defined.

  Definition hexEa : forall x, fst hexEqv (fst (ba HexagonBicyc) x) = fst (preEqv (S := FinSetU 3) s01) (fst hexEqv x).
  Proof. intros []; apply fin3_perm_ext; exact refl. Defined.
  Definition hexEb : forall x, fst hexEqv (fst (bb HexagonBicyc) x) = fst (preEqv (S := FinSetU 3) s12) (fst hexEqv x).
  Proof. intros []; apply fin3_perm_ext; exact refl. Defined.
  Definition prismEa : forall x, fst prismEqv (fst (ba PrismBicyc) x) = fst (preEqv (S := FinSetU 3) cyc3) (fst prismEqv x).
  Proof. intros []; apply fin3_perm_ext; exact refl. Defined.
  Definition prismEb : forall x, fst prismEqv (fst (bb PrismBicyc) x) = fst (preEqv (S := FinSetU 3) s01) (fst prismEqv x).
  Proof. intros []; apply fin3_perm_ext; exact refl. Defined.

  Definition SG3_AutHex : SG 3 = AutG Bicyc_isGrpd HexagonBicyc
    := ap (AutG Bicyc_isGrpd) (BicycEqv_to_path (E_Kc s01 s12 _ hexEqv hexEa hexEb))⁻¹
       ⋅ SG3_AutKc s01 s12 _.

  Definition SG3_AutPrism : SG 3 = AutG Bicyc_isGrpd PrismBicyc
    := ap (AutG Bicyc_isGrpd) (BicycEqv_to_path (E_Kc cyc3 s01 _ prismEqv prismEa prismEb))⁻¹
       ⋅ SG3_AutKc cyc3 s01 _.

  Definition hex_ne_prism : ¬ ptrunc (HexagonBicyc = PrismBicyc).
  Proof.
    refine (ptrunc_rec (fun e : Empty => match e with end) _).
    intro p. pose (w := path_to_BicycEqv p).
    pose (sq := fun y => ptw (fst (snd w)) y).
    pose (x := eqinv (snd (fst w)) p0).
    assert (hh : forall y, ha (ha y) = y) by (intros []; exact refl).
    assert (e : pa (pa (fst (fst w) x)) = fst (fst w) x).
    { exact (ap pa (sq x)^ @ (sq (ha x))^ @ ap (fst (fst w)) (hh x)). }
    rewrite (eqinv_r (snd (fst w)) p0) in e. discriminate e.
  Defined.

End SixCayley.

(** The last exercise of the section: the hexagon and the prism are in
    different components of [Bicyc], but their automorphism groups are
    isomorphic to each other and to [Σ_3]. *)
Definition xca_six_bicycles `{Univalence}
  : ¬ ptrunc (HexagonBicyc = PrismBicyc)
    × Iso (AutG Bicyc_isGrpd HexagonBicyc) (AutG Bicyc_isGrpd PrismBicyc)
    × Iso (AutG Bicyc_isGrpd HexagonBicyc) (SG 3)
.
Proof.
  refine ((_; _); _).
  - exact hex_ne_prism.
  - exact (fst (path_Group_Iso_eqv _ _) (SG3_AutPrism ⋅ SG3_AutHex⁻¹)).
  - exact (fst (path_Group_Iso_eqv _ _) SG3_AutHex⁻¹).
Defined.
