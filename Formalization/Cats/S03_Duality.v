(** * Section 6.3 Abstract notions and duality

    Part of Chapter 6 ([cats.tex]); see [Cats.v] for an overview of the
    chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definitions [def:terminal-obj] and [def:initial-obj]
      ([isTerminal], [isInitial]); exercise [xca:terminal-prop]
      ([terminal_isProp]).
    - The examples: [𝟙] is terminal and [∅] initial in types, [𝟙] is
      terminal in sets, the trivial group is terminal and initial in
      groups ([TG_terminal], [TG_initial], via [pmap_contr_dom]);
      exercise [xca:unit-ptd-types] ([UnitPtd_terminal],
      [UnitPtd_initial]).
    - Definition [def:op-cat] ([Op]) and lemma [lem:op-idem] ([Op_Op],
      [Op_isEquiv]); the coslice ([CosliceCat]) as the dual of the slice.
    - Definitions [def:mono-in-cat] and [def:epi-in-cat] ([isMono],
      [isEpi], dual by definition: [isMono_Op_isEpi]), and their
      cancellation form in precategories ([isMono_cancel],
      [isEpi_cancel]).
    - Exercise [xca:monos-epis-sets-types]: monos in types are the
      injections ([isMono_TypeCat_isInj]); surjections are epis in sets
      ([isSurj_isEpi_SetCat]).
    - Exercise [xca:monos-epis-preorder] ([preorder_isMono],
      [preorder_isEpi]).

    Left out (statements only, no proofs yet)
    - Exercise [xca:monos-epis-sets-types], that epis in sets are
      surjections ([isEpi_SetCat_isSurj_stmt]).  The usual proof tests
      against the set of propositions, which is not in the same universe
      as [A] and [B]; without propositional resizing another argument is
      needed.  NOTE for the book text: a hint would help here.
    - Exercise [xca:mono-cat-grp] ([xca_mono_cat_grp_stmt]).  It needs
      that a homomorphism is determined by its action on symmetries,
      which is only proved in Chapter 7 ([abstr_hom_eqv]). *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Types.Unit Truncations.Core Spaces.Nat.Core.
From SymmetryBook Require Export Cats.S02_Categories.

Local Open Scope uf_scope.

(** ** 6.3 Abstract notions and duality *)

(** Definitions [def:terminal-obj] and [def:initial-obj]. *)
Definition isTerminal {C : WildPreCat} (T : Ob C) : Type := forall A : Ob C, isContr (homC A T).

Definition isInitial {C : WildPreCat} (I : Ob C) : Type := forall A : Ob C, isContr (homC I A).

Definition isTerminal_isProp `{Funext} {C : WildPreCat} (T : Ob C) : isProp (isTerminal T)
  := Pi_isProp (fun A => isContr_isProp _).

Definition isInitial_isProp `{Funext} {C : WildPreCat} (I : Ob C) : isProp (isInitial I)
  := Pi_isProp (fun A => isContr_isProp _).

(** Exercise [xca:terminal-prop]: in a univalent wild precategory the
    type of terminal objects is a proposition. *)
Definition terminal_isProp `{Funext} (C : WildPreCat) (u : isUnivalent C)
  : isProp {T : Ob C & isTerminal T}.
Proof.
  intros [T t] [T' t'].
  apply (path_sigma_prop isTerminal_isProp (u := (T; t)) (v := (T'; t'))). cbn.
  refine (eqinv (u T T') (fst (t' T); ((fst (t T'); _); (fst (t T'); _)))).
  - exact (isContr_isProp' (t' T') _ _).
  - exact (isContr_isProp' (t T) _ _).
Defined.

(** Terminal and initial objects in the examples. *)
Definition True_isContr : isContr True := (triv; fun x => match x with triv => refl end).

Definition True_terminal `{Funext} : isTerminal (C := TypeCat) True
  := fun A => ((fun _ => triv); fun f => ptw_inv (fun a => isContr_isProp' True_isContr _ _)).

Definition False_initial `{Funext} : isInitial (C := TypeCat) False
  := fun A => ((fun x : False => match x with end); fun f => ptw_inv (fun x : False => match x with end)).

Definition True_terminal_Set `{Funext} : isTerminal (C := SetCat) ((True; prop_is_set True_isProp) : Ob SetCat)
  := fun A => True_terminal (fst A).

(** The trivial group is terminal in the category of groups. *)
Definition TG_terminal `{Univalence} : isTerminal (C := GroupCat) TG.
Proof.
  intro G. refine (isContr_Eqv (Eqv_inv (Copy_eqv _)) _).
  refine (eqinv (snd (isContr_Contr_eqv _)) _).
  pose (c := fst (isContr_Contr_eqv _) TG_contr). exact _.
Defined.

(** Pointed maps out of a contractible pointed type form a contractible
    type; hence the trivial group is also initial. *)
Definition pmap_contr_dom `{Funext} (X Y : Ustar) (c : isContr (utype X)) : isContr (X →* Y).
Proof.
  pose (cX := Build_Contr (utype X) (pt X) (fun y => (snd c (pt X))^ @ snd c y)).
  refine (isContr_Eqv (Eqv_inv (Eqv_of_Equiv (equiv_functor_sigma'
             (Q := fun y : utype Y => pt Y = y)
             (@equiv_contr_forall _ (utype X) cX (fun _ => utype Y))
             (fun g => equiv_idmap)))) (singleton_contr (pt Y))).
Defined.

Definition TG_initial `{Univalence} : isInitial (C := GroupCat) TG
  := fun G => isContr_Eqv (Eqv_inv (Copy_eqv _)) (pmap_contr_dom (BG TG) (BG G) TG_contr).

(** Exercise [xca:unit-ptd-types]: [(𝟙, triv)] is terminal and initial
    in the wild category of pointed types. *)
Definition UnitPtd : Ustar := (True; triv).

Definition UnitPtd_terminal `{Funext} : isTerminal (C := PtdCat) UnitPtd.
Proof.
  intro X. exact (eqinv (snd (isContr_Contr_eqv _)) _).
Defined.

Definition UnitPtd_initial `{Funext} : isInitial (C := PtdCat) UnitPtd.
Proof.
  intro X.
  refine (isContr_Eqv (Eqv_of_Equiv (equiv_functor_sigma_pb
             (Q := fun g : True -> utype X => pt X = g triv)
             (equiv_unit_rec (utype X)))) (singleton_contr (pt X))).
Defined.

(** Definition [def:op-cat]: the opposite, swapping [λ] and [ρ] and
    using [α⁻¹]. *)
Definition Op (C : WildPreCat) : WildPreCat
  := {| Ob := Ob C;
        homC := fun A B => homC (w := C) B A;
        idC := fun A => idC A;
        compC := fun A B D g f => f ∘c g;
        lamC := fun A B f => rhoC f;
        rhoC := fun A B f => lamC f;
        alphaC := fun A B D E f g h => (alphaC h g f)^ |}.

Definition Op_isPreCat (C : WildPreCat) (pc : isPreCat C) : isPreCat (Op C)
  := fun A B => pc B A.

(** Lemma [lem:op-idem]: [(C^op)^op = C], so taking opposites is an
    equivalence. *)
Definition Op_Op `{Funext} (C : WildPreCat) : Op (Op C) = C.
Proof.
  destruct C as [O h i c l r a]. unfold Op. cbn.
  refine (ap (fun a' => {| Ob := O; homC := h; idC := i; compC := c; lamC := l; rhoC := r;
                           alphaC := a' |}) _).
  apply ptw_inv; intro A; apply ptw_inv; intro B; apply ptw_inv; intro D;
    apply ptw_inv; intro E; apply ptw_inv; intro f; apply ptw_inv; intro g;
    apply ptw_inv; intro k.
  exact (inv_V _).
Defined.

Definition Op_isEquiv `{Funext} : isEquiv Op := iso_to_isEquiv Op Op Op_Op Op_Op.

(** The coslice [C₀/C], dual to the slice. *)
Definition CosliceCat `{Funext} (C : WildPreCat) (pc : isPreCat C) (C0 : Ob C) : WildPreCat
  := Op (SliceCat (Op C) (Op_isPreCat C pc) C0).

(** Definitions [def:mono-in-cat] and [def:epi-in-cat]. *)
Section MonoEpi.

  Context {C : WildPreCat}.

  Definition isMono {A B : Ob C} (f : homC A B) : Type
    := forall D : Ob C, isInj (fun k : homC D A => f ∘c k).

  Definition isEpi {A B : Ob C} (f : homC A B) : Type
    := forall D : Ob C, isInj (fun k : homC B D => k ∘c f).

  (** In a precategory these are the cancellation properties. *)
  Definition isMono_cancel (pc : isPreCat C) {A B : Ob C} (f : homC A B)
    : isMono f <-> (forall D (g h : homC D A), f ∘c g = f ∘c h -> g = h)
    := (fun m D => isInj_cancel (m D), fun c D => cancel_isInj (pc D B) (c D)).

  Definition isEpi_cancel (pc : isPreCat C) {A B : Ob C} (f : homC A B)
    : isEpi f <-> (forall D (g h : homC B D), g ∘c f = h ∘c f -> g = h)
    := (fun m D => isInj_cancel (m D), fun c D => cancel_isInj (pc A D) (c D)).

End MonoEpi.

(** Mono and epi are dual notions. *)
Definition isMono_Op_isEpi (C : WildPreCat) {A B : Ob C} (f : homC A B)
  : @isMono (Op C) B A f = isEpi f := refl.

(** Exercise [xca:mono-cat-grp]: the monomorphisms in the category of
    groups are those of definition [def:typeofmono] (statement only). *)
Definition xca_mono_cat_grp_stmt `{Funext} : Type
  := forall (H G : Group) (f : Hom H G), isMono (C := GroupCat) f <-> ismono f.

(** Exercise [xca:monos-epis-sets-types], first part: the monomorphisms
    in the wild category of types are the injections. *)
Definition postcomp_fiber_eqv `{Funext} {A B D : Type} (f : A -> B) (k : D -> B)
  : (forall d, fiber f (k d)) ≃ fiber (fun g : D -> A => f ∘ g) k.
Proof.
  refine (Eqv_comp (Eqv_of_Equiv (equiv_sig_coind (fun _ => A) (fun d a => k d = f a))^-1) _).
  exact (tot (fun g (p : forall d, k d = f (g d)) => ptw_inv p);
         tot_isEquiv _ (fun g => snd (Eqv_inv (ptw; funext k (f ∘ g))))).
Defined.

Definition isMono_TypeCat_isInj `{Funext} {A B : Type} (f : A -> B)
  : isMono (C := TypeCat) f <-> isInj f.
Proof.
  split.
  - intros m b.
    refine (isProp_Eqv (Eqv_comp (Eqv_inv (postcomp_fiber_eqv f (fun _ : True => b)))
                          (Eqv_of_Equiv (equiv_unit_rec (fiber f b))^-1)) (m True _)).
  - intros j D k. exact (isProp_Eqv (postcomp_fiber_eqv f k) (Pi_isProp (fun d => j (k d)))).
Defined.

(** Second part: the epimorphisms in the category of sets are the
    surjections. *)
Definition SetCat_isPreCat `{Funext} : isPreCat SetCat := fun A B => Pi_isSet (fun _ => snd B).

Definition isSurj_isEpi_SetCat `{Funext} {A B : Ob SetCat} (f : homC A B)
  : isSurj f -> isEpi f.
Proof.
  intro s. apply (Overture.snd (isEpi_cancel SetCat_isPreCat f)). intros D g h e.
  apply ptw_inv. intro b.
  refine (ptrunc_rec (snd D _ _) _ (s b)). intros [a p].
  exact (ap g p @ ap (fun u => u a) e @ (ap h p)^).
Defined.

(** The converse (statement only).  The usual proof tests against two
    maps into the set of propositions, which lives in a larger universe
    than [A] and [B], so it is not an object of the same category of
    sets; without propositional resizing one needs another argument (for
    instance via the pushout of [f] along itself). *)
Definition isEpi_SetCat_isSurj_stmt `{Funext} : Type
  := forall (A B : Ob SetCat) (f : homC A B), isEpi f -> isSurj f.

(** Exercise [xca:monos-epis-preorder]: in a preorder every morphism is
    both a mono and an epi. *)
Definition prop_map_isInj {A B : Type} (hA : isProp A) (hB : isProp B) (f : A -> B) : isInj f
  := fun b u v => path_sigma_prop (fun a => prop_is_set hB _ _) (u := u) (v := v) (hA _ _).

Definition preorder_isMono (C : WildPreCat) (p : isPreorder C) {A B : Ob C} (f : homC A B)
  : isMono f
  := fun D => prop_map_isInj (p D A) (p D B) _.

Definition preorder_isEpi (C : WildPreCat) (p : isPreorder C) {A B : Ob C} (f : homC A B)
  : isEpi f
  := fun D => prop_map_isInj (p B D) (p A D) _.
