(** * Section 2.24 The type of finite sets

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - [Fin] is the library's [Fin] ([Fin(succ(n)) ≡ Succ(Fin(n))] by
      definition), [Succ] is [SuccT]; exercise [xca:finite-types]: the
      elements of [Fin 0], [Fin 1], [Fin 2]; [Fin 1 ≃ True],
      [Fin 2 ≃ Bool]; [Fin(n) ≃ ∑_k (k < n)] (via the library's
      [equiv_fin_finnat]); [Fin m = Fin n → m = n] (from 2.23).
    - [isFinSet], [lem:maxonefinitetype], [FinSet], [FinSet_n], [Card];
      [FinSet ≃ ∑_n FinSet_n]; [FinSet_0] and [FinSet_1] are contractible.
    - Exercise [xca:finsets-decidable].
    - Exercise [xca:2-element-sets]: [T = T] is a 2-element set;
      [¬ ∏_{T : FinSet_2} (T = 𝟚)] (by univalence); and, uniformly in
      [T : FinSet_2], [(T = T) = 𝟚] ([two_element_loops_Bool]) and
      [T = (𝟚 = T)] ([two_element_paths_Bool]).
      NOTE for the book text, following a hint by the author: the last
      two parts first show that [∑_{x:T} ¬(x = t)] is a proposition for
      [t : T] ([compl_isProp]), so that "the other element" of [t] is
      well defined without choice ([other]); and they repeatedly use
      that, to prove a proposition about all [T : FinSet_2], one may
      assume [T ≡ 𝟚] ([FinSet2_prop_ind]).  The book could give these two
      hints with the exercise.
    - Exercise [xca:tabulation] ([lookup]) and [cor:lists-truncated].
    - Remark [rem:subset-of-fin-set]: a proposition is a finite set iff
      it is decidable.
    - Exercise [xca:dec-quant-finset].
    - Exercises [xca:fin-sum-of-finsets] and [xca:dec-quot-finite-set],
      via a bridge between [isFinSet] and the library's class [Finite].
    - The remark that [FinSet] is essentially small requires an extra
      lemma, [sigma_contr_fibers], and is proved in 2.27. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S23_MoreNaturalNumbers.

Local Open Scope uf_scope.

(** ** 2.24 The type of finite sets *)

(** Definition [def:finiteset]: [Succ(X) :≡ X ⨿ True], and
    [Fin(0) :≡ ∅], [Fin(succ(n)) :≡ Succ(Fin(n))]: this is the library's
    [Fin], which has the same name. *)
Definition SuccT (X : Type) : Type := X ⨿ True.

Definition Fin_0 : Fin 0 = False := refl.
Definition Fin_succ (n : ℕ) : Fin (succ n) = SuccT (Fin n) := refl.

(** Exercise [xca:finite-types], parts 1 and 2. *)
Definition fin1_0 : Fin 1 := inr triv.
Definition fin2_0 : Fin 2 := inl (inr triv).
Definition fin2_1 : Fin 2 := inr triv.

Definition Fin0_elems : Fin 0 -> False := idmap.

Definition Fin1_elems (x : Fin 1) : x = fin1_0
  := match x with inl e => match e with end | inr t => match t with triv => refl end end.

Definition Fin2_elems (x : Fin 2) : (x = fin2_0) ⨿ (x = fin2_1)
  := match x with
     | inl y => inl (ap inl (Fin1_elems y))
     | inr t => inr (match t with triv => refl end)
     end.

Definition Fin1_isProp : isProp (Fin 1)
  := fun x y => (Fin1_elems y)⁻¹ ⋅ Fin1_elems x.

Definition Fin1_True : Fin 1 ≃ True
  := Eqv_of_props Fin1_isProp True_isProp (fun _ => triv) (fun _ => fin1_0).

Definition Fin2_Bool : Fin 2 ≃ Bool.
Proof.
  refine (mkEqv (fun x => match x with inl _ => no | inr _ => yes end)
                (fun b => if b then fin2_1 else fin2_0) _ _).
  - intro x. destruct (Fin2_elems x) as [e|e]; destruct e^; exact refl.
  - intros []; exact refl.
Defined.

(** Definition [def:is-finite]. *)
Definition isFinSet (X : Type) : Type := Ex (fun n : ℕ => X = Fin n).

(** Lemma [lem:maxonefinitetype]. *)
Section MaxOneFiniteType.

  Context {X : Type}.

  Definition card_type : Type := {n : ℕ & ptrunc (X = Fin n)}.

  Definition card_type_isProp : isProp card_type.
  Proof.
    intros [n p] [m q].
    apply (path_sigma_prop (fun _ => ptrunc_isProp)).
    refine (ptrunc_rec (ℕ_isSet _ _) _ p). intro e.
    refine (ptrunc_rec (ℕ_isSet _ _) _ q). intro e'.
    exact (Fin_paths_eq (e' ⋅ e⁻¹)).
  Defined.

  Definition card_type_iff
    : (card_type -> isFinSet X) × (isFinSet X -> card_type)
    := (fun w : card_type =>
          ptrunc_rec ptrunc_isProp
            (fun e : X = Fin (fst w) => trunc ((fst w; e) : {n : ℕ & X = Fin n}))
            (snd w);
        ptrunc_rec card_type_isProp
          (fun w : {n : ℕ & X = Fin n} => (fst w; trunc (snd w)) : card_type)).

End MaxOneFiniteType.

(** Definition [def:groupoidFin]. *)
Definition FinSet : Type := {S : SetU & isFinSet (fst S)}.

Definition FinSet_n (n : ℕ) : Type := {S : SetU & ptrunc (Fin n = fst S :> Type)}.

Definition Card (S : FinSet) : ℕ := fst (snd card_type_iff (snd S)).

Definition Card_spec (S : FinSet) : ptrunc (fst (fst S) = Fin (Card S))
  := snd (snd card_type_iff (snd S)).

(** Remark after [def:groupoidFin]: the fact that [FinSet] is essentially
    [U]-small requires an extra lemma, [sigma_contr_fibers] (a sum of
    contractible types is equivalent to its base), and is proved in 2.27
    ([FinSet_essSmall] in [S27_StuffStructure.v]). *)

(** [FinSet ≃ ∑_{n:ℕ} FinSet_n], by [lem:maxonefinitetype]. *)
Definition FinSet_sum_eqv : FinSet ≃ {n : ℕ & FinSet_n n}.
Proof.
  refine (Eqv_comp (tot (fun S => snd card_type_iff);
                    tot_isEquiv _ (fun S => snd (Eqv_of_props ptrunc_isProp
                                                   card_type_isProp _
                                                   (fst card_type_iff)))) _).
  refine (Eqv_comp (sigma_comm SetU ℕ (fun S n => ptrunc (fst S = Fin n))) _).
  pose (F := fun (n : ℕ) (S : SetU) => Eqv_of_props (ptrunc_isProp (T := fst S = Fin n))
                          (ptrunc_isProp (T := Fin n = fst S :> Type))
                          (ptrunc_rec ptrunc_isProp (fun e => trunc e⁻¹))
                          (ptrunc_rec ptrunc_isProp (fun e => trunc e⁻¹))).
  pose (Fn := fun n => (tot (fun S => fst (F n S)); tot_isEquiv _ (fun S => snd (F n S)))
                       : {S : SetU & ptrunc (fst S = Fin n)} ≃ FinSet_n n).
  exact (tot (fun n => fst (Fn n)); tot_isEquiv _ (fun n => snd (Fn n))).
Defined.

(** [FinSet_0] and [FinSet_1] are contractible. *)
Definition FinSet_0_isContr `{Univalence} : isContr (FinSet_n 0).
Proof.
  refine ((exist (fun X : Type => isSet X) (Fin 0) (prop_is_set False_isProp);
           trunc refl); _).
  intros [[S sS] u].
  apply (path_sigma_prop (fun _ => ptrunc_isProp)).
  apply (path_sigma_prop (fun X => isSet_isProp X)). cbn.
  pose (nS := ptrunc_rec (neg_isProp S)
                (fun e : Fin 0 = S :> Type => fun s => ptoe e⁻¹ s) u).
  exact (etop (Eqv_of_props False_isProp (fun a b => match nS a with end)
                 (fun x => match x with end) (fun s => match nS s with end))).
Defined.

Definition FinSet_1_isContr `{Univalence} : isContr (FinSet_n 1).
Proof.
  refine ((exist (fun X : Type => isSet X) (Fin 1) (prop_is_set Fin1_isProp);
           trunc refl); _).
  intros [[S sS] u].
  apply (path_sigma_prop (fun _ => ptrunc_isProp)).
  apply (path_sigma_prop (fun X => isSet_isProp X)). cbn.
  pose (hs := ptrunc_rec (Sigma_isProp (isProp_isProp S) (fun h => h))
                (fun e : Fin 1 = S :> Type =>
                   ((isProp_Eqv (idtoeqv e) Fin1_isProp; ptoe e fin1_0)
                    : {h : isProp S & S})) u).
  exact (etop (Eqv_of_props Fin1_isProp (fst hs) (fun _ => snd hs) (fun _ => fin1_0))).
Defined.

(** Exercise [xca:finsets-decidable]. *)
Definition isDecSet_isProp `{Funext} (X : Type) : isProp (isDecSet X)
  := Pi_isProp (fun x => Pi_isProp (fun y =>
       Sigma_isProp (isProp_isProp (x = y)) (fun h => lem_isProp h))).

Definition Fin_isDecSet (n : ℕ) : isDecSet (Fin n)
  := hedberg (fun x y => dec_paths x y).

Definition finset_isDecSet `{Funext} {X : Type} (h : isFinSet X) : isDecSet X.
Proof.
  refine (ptrunc_rec (isDecSet_isProp X) _ h). intros [n e].
  exact (trp isDecSet e⁻¹ (Fin_isDecSet n)).
Defined.

(** Exercise [xca:2-element-sets]. *)
Section TwoElementSets.

  Context `{Univalence}.

  (** [Bool = Bool] is equivalent to [Bool] (using exercise [xca:C2] of 2.13). *)
  Definition BoolPaths_Bool : (Bool = Bool :> Type) ≃ Bool.
  Proof.
    pose (swap_no := ptw (ap fst (ptoe_etop swapEqv)) yes : ptoe swap yes = no).
    pose (back := fun b : Bool => if b then (refl : Bool = Bool :> Type) else swap).
    refine (mkEqv (fun p : Bool = Bool :> Type => ptoe p yes) back _ _).
    - intro p. destruct (Bool_paths_cases p) as [e|e].
      + revert p e. refine (paths_ind_r _ _ _). exact refl.
      + revert p e. refine (paths_ind_r _ _ _). exact (ap back swap_no).
    - intros []; [exact refl | exact swap_no].
  Defined.

  Definition paths_conj_eqv {A B : Type} (e : A = B) : (A = A) ≃ (B = B).
  Proof. destruct e. exact (idEqv _). Defined.

  Definition Fin2_Bool_path : Fin 2 = Bool :> Type := etop Fin2_Bool.

  (** [T = T] is a 2-element set for every 2-element set [T]. *)
  Definition self_paths_two_element (T : FinSet_n 2)
    : isSet (fst (fst T) = fst (fst T))
      × ptrunc (Fin 2 = (fst (fst T) = fst (fst T)) :> Type).
  Proof.
    destruct T as [[X sX] u]. cbn.
    refine (paths_sets_isSet sX; _).
    refine (ptrunc_rec ptrunc_isProp _ u). intro e.
    apply trunc.
    exact (ap (fun Y : Type => Y = Y) e
           ⋅ etop (Eqv_comp Fin2_Bool
                     (Eqv_inv (Eqv_comp (paths_conj_eqv Fin2_Bool_path) BoolPaths_Bool)))).
  Defined.

  (** [¬ ∏_{T : FinSet_2} (T = 𝟚)]: the swap of [Fin 2] gives a loop at
      [Fin 2] in [FinSet_2], along which such a family would have to be
      invariant. *)
  Definition swapFin : Fin 2 -> Fin 2
    := fun x => match x with inl _ => fin2_1 | inr _ => fin2_0 end.

  Definition swapFin_invol (x : Fin 2) : swapFin (swapFin x) = x.
  Proof. destruct (Fin2_elems x) as [e|e]; destruct e^; exact refl. Defined.

  Definition swapFinEqv : Fin 2 ≃ Fin 2
    := mkEqv swapFin swapFin swapFin_invol swapFin_invol.

  Definition swapF : Fin 2 = Fin 2 :> Type := etop swapFinEqv.

  Definition swapF_ne_refl : swapF ≠ refl.
  Proof.
    intro e.
    pose (h := ap fst (ptoe_etop swapFinEqv) : ptoe swapF = swapFin).
    pose (h' := ap ptoe e ⋅ h⁻¹ : swapFin = ptoe (refl (Fin 2 : Type))).
    exact (inl_ne_inr (inr triv) triv (ptw h' fin2_1)).
  Defined.

  Definition Fin2_isSet : isSet (Fin 2) := fun x y => fst (Fin_isDecSet 2 x y).

  Definition Fin2_FinSet2 : FinSet_n 2
    := (exist (fun X : Type => isSet X) (Fin 2) Fin2_isSet; trunc refl).

  Definition cancel_loop {A B : Type} (q : A = A) (x : A = B)
    : trans q⁻¹ x = x -> q = refl.
  Proof.
    destruct x. intro h. exact ((symm_symm q)^ @ ap symm h).
  Defined.

  Definition not_all_two_element_paths
    : ¬ (forall T : FinSet_n 2, fst (fst T) = Fin 2).
  Proof.
    intro s.
    pose (l := path_sigma_prop (u := Fin2_FinSet2) (v := Fin2_FinSet2)
                 (fun _ => ptrunc_isProp)
                 (path_sigma_prop (u := fst Fin2_FinSet2) (v := fst Fin2_FinSet2)
                    (fun X => isSet_isProp X) swapF)).
    pose (a := apD s l).
    assert (t : forall (T T' : FinSet_n 2) (r : T = T') (x : fst (fst T) = Fin 2),
               transport (fun T : FinSet_n 2 => fst (fst T) = Fin 2) r x
               = trans (ap (fun T : FinSet_n 2 => fst (fst T)) r)⁻¹ x).
    { intros T T' r x. destruct r. exact (trans_1p x)⁻¹. }
    assert (ap1 : ap (fun T : FinSet_n 2 => fst (fst T)) l = swapF).
    { refine (ap_compose fst fst l @ _).
      refine (ap (ap fst) (ap_fst_pathpair _ _) @ _).
      exact (ap_fst_pathpair _ _). }
    apply swapF_ne_refl.
    exact (ap1^ @ cancel_loop _ (s Fin2_FinSet2) ((t _ _ l _)^ @ a)).
  Defined.

  (** Exercise [xca:2-element-sets], last two parts, following a hint by
      the author: first show that [∑_{x:T} ¬(x = t)] is a proposition, and
      use that, for propositions, a 2-element set may be assumed to be [𝟚]. *)

  Definition Bool2 : FinSet_n 2
    := (exist (fun X : Type => isSet X) Bool isSet_bool; trunc Fin2_Bool_path).

  (** Every 2-element set is merely equal to [Bool2]. *)
  Definition FinSet2_conn (T : FinSet_n 2) : ptrunc (Bool2 = T).
  Proof.
    refine (ptrunc_rec ptrunc_isProp _ (snd T)). intro e. apply trunc.
    exact (path_sigma_prop (u := Bool2) (v := T) (fun _ => ptrunc_isProp)
             (path_sigma_prop (u := fst Bool2) (v := fst T)
                (fun X => isSet_isProp X) (e ⋅ Fin2_Bool_path⁻¹))).
  Defined.

  (** To prove a proposition about all 2-element sets, we may assume
      that the 2-element set is [Bool]. *)
  Definition FinSet2_prop_ind (P : FinSet_n 2 -> Type)
    (hP : forall T, isProp (P T)) (b : P Bool2) (T : FinSet_n 2) : P T
    := ptrunc_rec (hP T) (fun e => trp P e b) (FinSet2_conn T).

  Definition Bool_compl (t x : Bool) : x ≠ t -> x = negb t.
  Proof.
    destruct t, x; intro n;
      solve [exact refl | destruct (n refl)].
  Defined.

  Definition negb_ne (t : Bool) : negb t ≠ t.
  Proof. destruct t; intro e; [exact (yes_ne_no e⁻¹) | exact (yes_ne_no e)]. Defined.

  (** For [t : T], the complement [∑_{x:T} ¬(x = t)] is a proposition. *)
  Definition compl_isProp (T : FinSet_n 2) (t : fst (fst T))
    : isProp {x : fst (fst T) & x ≠ t}.
  Proof.
    revert t.
    refine (FinSet2_prop_ind (fun T => forall t : fst (fst T), isProp {x : fst (fst T) & x ≠ t})
              (fun T => Pi_isProp (fun t => isProp_isProp _)) _ T).
    intros t [x f] [y g].
    apply (path_sigma_prop (fun _ => neg_isProp _)).
    exact (Bool_compl t x f @ (Bool_compl t y g)⁻¹).
  Defined.

  (** Hence it is contractible, its center being "the other element". *)
  Definition compl (T : FinSet_n 2) : forall t : fst (fst T), {x : fst (fst T) & x ≠ t}
    := FinSet2_prop_ind (fun T => forall t : fst (fst T), {x : fst (fst T) & x ≠ t})
         (fun T => Pi_isProp (compl_isProp T)) (fun t => (negb t; negb_ne t)) T.

  Definition other (T : FinSet_n 2) (t : fst (fst T)) : fst (fst T) := fst (compl T t).

  Definition other_ne (T : FinSet_n 2) (t : fst (fst T)) : other T t ≠ t
    := snd (compl T t).

  Definition other_unique (T : FinSet_n 2) {t x : fst (fst T)} (n : x ≠ t)
    : x = other T t
    := ap fst (compl_isProp T t (x; n) (compl T t)).

  (** Last part: [∏_{T:FinSet_2} (T = (𝟚 = T))].  An element [t] gives the
      equivalence [𝟚 ≃ T] mapping [yes] to [t] and [no] to the other element. *)
  Definition pick (T : FinSet_n 2) (t : fst (fst T)) : Bool -> fst (fst T)
    := fun b => if b then t else other T t.

  Definition pick_isEquiv (T : FinSet_n 2) (t : fst (fst T)) : isEquiv (pick T t).
  Proof.
    revert t.
    refine (FinSet2_prop_ind (fun T => forall t, isEquiv (pick T t))
              (fun T => Pi_isProp (fun t => isEquiv_isProp _)) _ T).
    intro t.
    assert (h : (fun b : Bool => if b then t else negb t) = pick Bool2 t).
    { apply ptw_inv. intros []; [exact refl | exact (other_unique Bool2 (negb_ne t))]. }
    refine (trp isEquiv h _).
    pose (inv := fun b : Bool => if b then t else negb t).
    refine (iso_to_isEquiv inv inv _ _);
      intro b; destruct t, b; exact refl.
  Defined.

  Definition pickEqv (T : FinSet_n 2) (t : fst (fst T)) : Bool ≃ fst (fst T)
    := (pick T t; pick_isEquiv T t).

  Definition Eqv_inj {X Y : Type} (e : X ≃ Y) {x x' : X} : fst e x = fst e x' -> x = x'
    := fun p => (eqinv_l (snd e) x)^ @ ap (eqinv (snd e)) p @ eqinv_l (snd e) x'.

  Definition elems_Bool_Eqv (T : FinSet_n 2) : fst (fst T) ≃ (Bool ≃ fst (fst T)).
  Proof.
    refine (mkEqv (pickEqv T) (fun e => fst e yes) (fun t => refl) _).
    intro e. apply path_Eqv, ptw_inv. intros [].
    - exact refl.
    - exact (other_unique T (fun p => yes_ne_no (Eqv_inj e p)^))^.
  Defined.

  Definition two_element_paths_Bool (T : FinSet_n 2)
    : fst (fst T) = (Bool = fst (fst T) :> Type) :> Type
    := etop (Eqv_comp (elems_Bool_Eqv T) (Eqv_inv (idtoeqv; ua Bool (fst (fst T))))).

  (** Third part: [∏_{T:FinSet_2} ((T = T) = 𝟚)].  A loop [p : T = T] is
      sent to [yes] iff [p = refl], which is decidable. *)
  Definition swap_ne_refl : swap ≠ refl := fun e => refl_ne_swap e⁻¹.

  Definition loop_refl_dec (T : FinSet_n 2) (p : fst (fst T) = fst (fst T))
    : (p = refl) ⨿ ¬ (p = refl).
  Proof.
    revert p.
    refine (FinSet2_prop_ind
              (fun T => forall p : fst (fst T) = fst (fst T), (p = refl) ⨿ ¬ (p = refl))
              (fun T => Pi_isProp (fun p => lem_isProp
                                            (paths_sets_isSet (snd (fst T)) p refl))) _ T).
    intro p. destruct (Bool_paths_cases p) as [e|e].
    - exact (inl e).
    - exact (inr (fun e' => swap_ne_refl (e' ⋅ e⁻¹))).
  Defined.

  Definition loop_Bool (T : FinSet_n 2) (p : fst (fst T) = fst (fst T)) : Bool
    := match loop_refl_dec T p with inl _ => yes | inr _ => no end.

  Definition loop_Bool_isEquiv (T : FinSet_n 2) : isEquiv (loop_Bool T).
  Proof.
    refine (FinSet2_prop_ind (fun T => isEquiv (loop_Bool T))
              (fun T => isEquiv_isProp _) _ T).
    assert (h : (fun p : Bool = Bool :> Type => fst BoolPaths_Bool p) = loop_Bool Bool2).
    { apply ptw_inv. intro p. unfold loop_Bool.
      destruct (loop_refl_dec Bool2 p) as [e|n];
        destruct (Bool_paths_cases p) as [e'|e'].
      - exact (ap (fun q => fst BoolPaths_Bool q) e').
      - destruct (swap_ne_refl (e ⋅ e'⁻¹)).
      - destruct (n e').
      - exact (ap (fun q => fst BoolPaths_Bool q) e'
               @ ptw (ap fst (ptoe_etop swapEqv)) yes). }
    exact (trp isEquiv h (snd BoolPaths_Bool)).
  Defined.

  Definition two_element_loops_Bool (T : FinSet_n 2)
    : (fst (fst T) = fst (fst T)) = Bool :> Type
    := etop (loop_Bool T; loop_Bool_isEquiv T).

End TwoElementSets.

(** Exercise [xca:tabulation]: [lookup : X^* ≃ ∑_{n:ℕ} (Fin(n) → X)].  A
    list [x ℓ] is sent to [(succ(n), i ↦ …)] where the new element [x] is
    at index [inr(triv)] and the elements of [ℓ] at the indices [inl(i)]. *)
Section Tabulation.

  Context {X : Type}.

  Definition lookup_step (x : X) (w : {n : ℕ & Fin n -> X})
    : {n : ℕ & Fin n -> X}
    := (S (fst w); fun i => match i with inl i' => snd w i' | inr _ => x end).

  Fixpoint lookup (l : X^*) : {n : ℕ & Fin n -> X}
    := match l with
       | nil => (0%nat; fun i : Fin 0 => match i with end)
       | cons x l' => lookup_step x (lookup l')
       end.

  Fixpoint unlookup_n (n : ℕ) : (Fin n -> X) -> X^*
    := match n with
       | O => fun _ => nil
       | S n' => fun f => cons (f (inr triv)) (unlookup_n n' (fun i => f (inl i)))
       end.

  Definition unlookup (w : {n : ℕ & Fin n -> X}) : X^* := unlookup_n (fst w) (snd w).

  Definition lookup_isEquiv `{Funext} : isEquiv lookup.
  Proof.
    refine (iso_to_isEquiv lookup unlookup _ _).
    - intro l. induction l as [|x l IH].
      + exact refl.
      + exact (ap (cons x) IH).
    - intros [n f]. revert f. induction n as [|n IH]; intro f.
      + exact (ap (fun g => (0%nat; g) : {n : ℕ & Fin n -> X})
                  (ptw_inv (fun i : Fin 0 => match i with end))).
      + refine (ap (lookup_step (f (inr triv))) (IH (fun i => f (inl i))) @ _).
        refine (ap (fun g => (S n; g) : {n : ℕ & Fin n -> X}) (ptw_inv _)).
        intros [i|t]; [exact refl | destruct t; exact refl].
  Defined.

  Definition lookup_eqv `{Funext} : X^* ≃ {n : ℕ & Fin n -> X}
    := (lookup; lookup_isEquiv).

End Tabulation.

(** Corollary [cor:lists-truncated]: for [n ≥ 0], lists of [n]-types are
    [n]-types. *)
Definition prop_ntype (n : ℕ) : forall X : Type, isProp X -> is_ntype n X.
Proof.
  induction n as [|n IH]; intros X h.
  - exact (prop_is_set h).
  - exact (fun x y => IH _ (prop_is_set h x y)).
Defined.

Definition set_ntype (n : ℕ) {X : Type} (s : isSet X) : is_ntype n X
  := match n with
     | O => s
     | S n' => fun x y => prop_ntype n' _ (s x y)
     end.

Definition list_ntype `{Funext} (n : ℕ) {X : Type} (h : is_ntype n X)
  : is_ntype n (X^*)
  := is_ntype_Eqv n (Eqv_inv lookup_eqv)
       (Sigma_ntype n (set_ntype n ℕ_isSet) (fun k => fun_ntype n h)).

(** Remark [rem:subset-of-fin-set]: a proposition is a finite set if and
    only if it is decidable. *)
Definition cardF {X : Type} (h : isFinSet X) : ℕ := fst (snd card_type_iff h).

Definition finprop_dec `{Funext} {p : Type} (hp : isProp p) (f : isFinSet p)
  : isDecidable p.
Proof.
  destruct (snd card_type_iff f) as [n u].
  refine (ptrunc_rec (lem_isProp hp) _ u). intro e.
  destruct n as [|n].
  - exact (inr (fun x => ptoe e x)).
  - exact (inl (ptoe e⁻¹ (inr triv))).
Defined.

Definition dec_finprop `{Univalence} {p : Type} (hp : isProp p)
  (d : isDecidable p) : isFinSet p
  := match d with
     | inl x => trunc (1%nat; etop (Eqv_of_props hp Fin1_isProp
                                     (fun _ => fin1_0) (fun _ => x)))
     | inr nx => trunc (0%nat; etop (Eqv_of_props hp False_isProp nx
                                     (fun e => match e with end)))
     end.

(** Exercise [xca:dec-quant-finset]. *)
Definition Fin_dec_quant `{Funext}
  : forall (n : ℕ) (P : Fin n -> PropU) (d : forall x, isDecidable (fst (P x))),
    isDecidable (Ex (fun x => fst (P x))) × isDecidable (forall x, fst (P x)).
Proof.
  intro n. induction n as [|n IH]; intros P d.
  - exact (inr (ptrunc_rec False_isProp
                  (fun w : {x : Fin 0 & fst (P x)} => match fst w with end));
           inl (fun x : Fin 0 => match x with end)).
  - destruct (IH (fun x => P (inl x)) (fun x => d (inl x))) as [ex al].
    refine (_; _).
    + destruct (d (inr triv)) as [p|np].
      * exact (inl (trunc (inr triv; p))).
      * destruct ex as [u|nu].
        -- exact (inl (ptrunc_rec ptrunc_isProp
                         (fun w : {x : Fin n & fst (P (inl x))} => trunc ((inl (fst w); snd w)
                                          : {x : Fin (S n) & fst (P x)})) u)).
        -- refine (inr (ptrunc_rec False_isProp _)).
           intros [[x|t] q].
           ++ exact (nu (trunc (x; q))).
           ++ destruct t. exact (np q).
    + destruct (d (inr triv)) as [p|np].
      * destruct al as [a|na].
        -- refine (inl _). intros [x|t].
           ++ exact (a x).
           ++ destruct t. exact p.
        -- exact (inr (fun h : forall x, fst (P x) => na (fun x => h (inl x)))).
      * exact (inr (fun h : forall x, fst (P x) => np (h (inr triv)))).
Defined.

Definition dec_quant_path `{Funext} {X : Type} {n : ℕ} (e : X = Fin n :> Type)
  : forall (P : X -> PropU) (d : forall x, isDecidable (fst (P x))),
    isDecidable (Ex (fun x => fst (P x))) × isDecidable (forall x, fst (P x)).
Proof. revert X e. refine (paths_ind_r _ _ _). exact (Fin_dec_quant n). Defined.

Definition finset_dec_quant `{Funext} {X : Type} (h : isFinSet X)
  (P : X -> PropU) (d : forall x, isDecidable (fst (P x)))
  : isDecidable (Ex (fun x => fst (P x))) × isDecidable (forall x, fst (P x))
  := ptrunc_rec (prod_isProp (lem_isProp ptrunc_isProp)
                   (lem_isProp (Pi_isProp (fun x => snd (P x)))))
       (fun w => dec_quant_path (snd w) P d) h.

(** Finite sets in the book's sense versus Coq-HoTT's class [Finite]. *)
Definition isFinSet_Finite `{Univalence} {X : Type} (h : isFinSet X) : Finite X
  := ptrunc_rec (@IsHProp_isProp _ (ishprop_finite X))
       (fun w => Build_Finite X (fst w) (tr (Equiv_of_Eqv (idtoeqv (snd w))))) h.

Definition Finite_isFinSet `{Univalence} {X : Type} (F : Finite X) : isFinSet X
  := ptrunc_rec ptrunc_isProp
       (fun e => trunc ((fcard X; etop (Eqv_of_Equiv e)) : {n : ℕ & X = Fin n}))
       (merely_equiv_fin X).

Definition cardF_fcard `{Univalence} {X : Type} (h : isFinSet X)
  : cardF h = @fcard X (isFinSet_Finite h)
  := ptrunc_ind (fun h => cardF h = @fcard X (isFinSet_Finite h))
       (fun _ => ℕ_isSet _ _) (fun w => refl) h.

Definition isFinSet_Eqv `{Univalence} {A B : Type} (e : A ≃ B)
  (h : isFinSet B) : isFinSet A
  := ptrunc_rec ptrunc_isProp
       (fun w => trunc ((fst w; snd w ⋅ etop e) : {n : ℕ & A = Fin n})) h.

(** Exercise [xca:fin-sum-of-finsets]. *)
Definition sum_finsets_isFinSet `{Univalence} {X : Type} (hX : isFinSet X)
  (F : X -> FinSet) : isFinSet {x : X & fst (fst (F x))}
  := Finite_isFinSet (@finite_sigma X (fun x => fst (fst (F x)))
                        (isFinSet_Finite hX) (fun x => isFinSet_Finite (snd (F x)))).

Definition card_sum_const `{Univalence} {X Y : Type} (hX : isFinSet X)
  (hY : isFinSet Y) (F : X -> Type) (e : forall x, F x ≃ Y)
  (hS : isFinSet {x : X & F x})
  : cardF hS = mul (cardF hX) (cardF hY).
Proof.
  pose (FX := isFinSet_Finite hX). pose (FY := isFinSet_Finite hY).
  pose (FS := isFinSet_Finite hS).
  pose (E := Eqv_comp (tot (fun x => fst (e x)); tot_isEquiv _ (fun x => snd (e x)))
               (binprod_prod X Y)).
  refine (cardF_fcard hS @ _ @ (ap011 nat_mul (cardF_fcard hX) (cardF_fcard hY))^).
  exact (@fcard_equiv' _ _ (Equiv_of_Eqv E) FS (@finite_prod X Y FX FY)
         @ @fcard_prod X Y FX FY).
Defined.

(** The arithmetical sum [∑_{x:X} f(x)] of [f : X → ℕ] over a finite set,
    via the library's [finadd]. *)
Definition finsum `{Univalence} {X : Type} (h : isFinSet X) (f : X -> ℕ) : ℕ
  := @finadd X (isFinSet_Finite h) f.

(** Exercise [xca:dec-quot-finite-set], via the library's [finite_quotient]
    and [xca:quotients-equivalence]. *)
Definition quot_isFinSet `{Univalence} {X : Type} (hX : isFinSet X)
  (R : X -> X -> PropU)
  (rr : forall x, fst (R x x))
  (rs : forall x y, fst (R x y) -> fst (R y x))
  (rt : forall x y z, fst (R x y) -> fst (R y z) -> fst (R x z))
  (dR : forall x y, isDecidable (fst (R x y)))
  : isFinSet (quot R)
  := isFinSet_Eqv (quot_QuotHIT R rr rs rt)
       (Finite_isFinSet (@finite_quotient _ X (isFinSet_Finite hX)
                           (fun x y => fst (R x y))
                           (fun x y => isProp_IsHProp (snd (R x y)))
                           rr rt rs dR)).
