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
      [path_to_BicycEqv]).  That this map is an equivalence (by
      univalence) is left out; the following results are stated for
      [BicycEqv] instead of identity types.
    - Lemma [lem:evisinj-bicycle] ([evisinj_bicycle], [ev_bicyc_isInj]),
      via [BicycEqv_sem]: commuting equivalences commute with [⟦ℓ⟧].
    - Definition [def:normal-bicycle] ([isNormal]), exercise
      [xca:normal-bicycle-equiv] ([normal_from_one]), and definition
      [def:cbid-bicycle] ([cbid], with [cbid_spec] and [cbid_refl]).

    - The two [6]-element bicycles of the last exercise ([HexagonBicyc],
      [PrismBicyc], on an inductive type [Six], connected by
      computation).

    Left out (statements only, no proofs yet; time limit per section)
    - The equivalence [((X,a,b) = (X',a',b')) ≃ BicycEqv]
      ([path_to_BicycEqv_isEquiv_stmt]), the exercises on [H_x]
      ([xca_normal_Hx_stmt]), commuting bicycles ([xca_commuting_stmt])
      and the equivalence relation on lists ([xca_lists_equiv_stmt]),
      remark [rem:bicycle-list-concat] ([rem_bicycle_list_concat_stmt]),
      the frieze identification ([xca_frieze_stmt]) and the isomorphisms
      with [Σ_3] ([xca_six_bicycles_stmt]).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Types.Sum Truncations.Core Spaces.Nat.Core
  Spaces.List.Core.
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
    [e : X ≃ X'] with [ea = a'e] and [eb = b'e] ([path_to_BicycEqv]); the
    book shows by univalence that this is an equivalence.  We state the
    results about symmetries in terms of such equivalences. *)
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

(** ** Left-out results of this section (statements only) *)
Section BicycleStatements.

  Context `{Univalence}.

  (** Identifications of bicycles are the equivalences commuting with
      [a] and [b]. *)
  Definition path_to_BicycEqv_isEquiv_stmt : Type
    := forall B B' : Bicyc, isEquiv (@path_to_BicycEqv _ B B').

  (** [H_x], the lists [ℓ] with [⟦ℓ⟧(x) = x]; the exercise: a bicycle is
      normal iff [H_x = H_y] for all [x, y]. *)
  Definition Hx (B : Bicyc) (x : bX B) (l : list (ℤ ⨿ ℤ)) : Type
    := sem (ba B) (bb B) l x = x.

  Definition xca_normal_Hx_stmt : Type
    := forall B : Bicyc, isNormal B <-> (forall x y l, Hx B x l <-> Hx B y l).

  (** Commuting bicycles are normal, and [Cyc × Cyc] is equivalent to the
      type of commuting bicycles, via [(X,t),(Y,u) ↦ (X × Y, t × id, id × u)]. *)
  Definition isCommuting (B : Bicyc) : Type := fst (ba B) ∘ fst (bb B) = fst (bb B) ∘ fst (ba B).

  Definition xca_commuting_stmt : Type
    := (forall B : Bicyc, isCommuting B -> isNormal B)
       × {e : Cyc × Cyc ≃ {B : Bicyc & isCommuting B} &
           forall c : Cyc × Cyc,
             bX (fst (fst e c)) = fst (fst (fst c)) × fst (fst (snd c))}.

  (** Lists are equivalent (have the same value at [x₀]) iff they have the
      same meaning, for a normal bicycle. *)
  Definition xca_lists_equiv_stmt : Type
    := forall (B : Bicyc) (nB : isNormal B) (x0 : bX B) (l l' : list (ℤ ⨿ ℤ)),
         sem (ba B) (bb B) l x0 = sem (ba B) (bb B) l' x0
         <-> sem (ba B) (bb B) l = sem (ba B) (bb B) l'.

  (** Remark [rem:bicycle-list-concat]. *)
  Definition rem_bicycle_list_concat_stmt : Type
    := forall (B : Bicyc) (nB : isNormal B) (x0 : bX B) (l l' : list (ℤ ⨿ ℤ)),
         (fst (fst (cbid nB x0 (sem (ba B) (bb B) l x0)))
            ∘ fst (fst (cbid nB x0 (sem (ba B) (bb B) l' x0)))
          = fst (fst (cbid nB x0 (sem (ba B) (bb B) (app l' l) x0))))
         × (fst (fst (cbid nB (sem (ba B) (bb B) l x0) x0))
              ∘ fst (fst (cbid nB (sem (ba B) (bb B) l' x0) x0))
            = fst (fst (cbid nB (sem (ba B) (bb B) (app l l') x0) x0))).

  (** Remark [rem:inf-dihedral-frieze] and the exercise after it: the
      infinite dihedral bicycle is identified with [(X, T, R)], where
      [T :≡ x ↦_{a x₀} x₀] and [R :≡ x ↦_{b x₀} x₀] (given normality). *)
  Definition xca_frieze_stmt : Type
    := forall nD : isNormal DihedralBicyc,
         let x0 := inl (iplus 0) : bX DihedralBicyc in
         let T := fst (cbid nD (fst (ba DihedralBicyc) x0) x0) in
         let R := fst (cbid nD (fst (bb DihedralBicyc) x0) x0) in
         {e : bX DihedralBicyc ≃ bX DihedralBicyc &
           (fst e ∘ fst (ba DihedralBicyc) = fst T ∘ fst e)
           × (fst e ∘ fst (bb DihedralBicyc) = fst R ∘ fst e)}.

End BicycleStatements.

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

  (** The exercise (statement only): the two bicycles are in different
      components, but their automorphism groups are isomorphic to each
      other and to [Σ_3]. *)
  Definition xca_six_bicycles_stmt : Type
    := ¬ ptrunc (HexagonBicyc = PrismBicyc)
       × Iso (AutG Bicyc_isGrpd HexagonBicyc) (AutG Bicyc_isGrpd PrismBicyc)
       × Iso (AutG Bicyc_isGrpd HexagonBicyc) (SG 3).

End SixBicycles.
