(** * Section 6.2 Categories

    Part of Chapter 6 ([cats.tex]); see [Cats.v] for an overview of the
    chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:wild-cat]: the record [WildPreCat] with [Ob],
      [homC], [idC], [compC] (notation [g ∘c f]), [lamC], [rhoC],
      [alphaC]; definitions [def:precategory] ([isPreCat]),
      [def:iso-in-cat] ([isIsoC], [IsoC]; named with a [C] to avoid a clash
      with the group isomorphisms [isIso], [Iso] of Section 4.4),
      [def:univalent-cat] ([idtoiso], [isUnivalent]) and [def:category]
      ([WildCat], [PreCat], [Cat]).
    - The claims after [def:iso-in-cat]: [isIsoC f] is a proposition in
      any wild precategory ([isIsoC_isProp], as in the book's footnote,
      via [postcomp_isEquiv] and [precomp_isEquiv]); identities are
      isomorphisms; inverses and composites of isomorphisms.
    - The examples: types ([TypeCat], univalent by univalence,
      [TypeCat_isUnivalent], with isomorphisms the equivalences),
      pointed types ([PtdCat], with the laws of remark [rem:wild], and
      univalent), families ([FamCat], univalent), sets ([SetCat], a
      category), groups ([GroupCat], a category, via
      [path_Group_Iso_eqv]) and [G]-sets ([GSetCat], a category).  The
      univalence proofs use a common criterion ([isUnivalent_from]).
    - Definition [def:full-subcat] ([FullSub]), a precategory or
      univalent if [C] is; lemma [lem:obj-gpd] ([Ob_isGrpd]).
    - Example [ex:poset]: preorders and posets ([isPreorder],
      [isPoset]); in a poset the objects form a set ([poset_isSet]); a
      preorder is univalent iff its objects form a set and it is
      antisymmetric ([poset_antisym], [antisym_isUnivalent]); [(ℕ, ≤)],
      [(Prop, →)] and [(Sub(S), ⊆)] are posets; [𝟚] with the always true
      relation is not univalent ([BoolTrue_not_univalent]).
    - Definition [def:wild-pre-groupoid] ([isPreGrpd]) and example
      [ex:path-groupoid] ([PathGrpd], univalent, a precategory for a
      [1]-type).
    - Example [def:slice-cat] ([SliceCat], a precategory) and exercise
      [xca:univ-slice-cat] ([UnivSlice], with morphisms given by
      pointwise identifications).
    - The laws for pointed maps ([pcomp_pid_l], [pcomp_pid_r],
      [pcomp_assoc]) moved here from Section 7.3.

    Left out (statements only, no proofs yet)
    - Exercise [xca:order-poset] ([xca_order_poset]).
    - That [(ℤ, ≤)] is a poset ([IntLeq_isPoset_stmt], with [ZLe]).
    - The coherences of remark [rem:wild] that wild precategories lack
      ([hasUnitCoh], [hasPentagon]).
    - That the slice of a category is univalent
      ([SliceCat_isUnivalent_stmt]).

    Left out (not formalized)
    - Remark [rem:cat-sizes] (universe levels, implicit in Rocq's
      universe polymorphism). *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Spaces.Nat.Core Spaces.Int.
From SymmetryBook Require Export Actions.Actions.

Local Open Scope uf_scope.

(** ** 6.2 Categories *)

(** Definition [def:wild-cat]: a wild precategory, with composition
    written in the order of function composition. *)
Record WildPreCat : Type := {
  (** [struc:cat-ob] *)
  Ob : Type;
  (** [struc:cat-mor] *)
  homC : Ob -> Ob -> Type;
  (** [struc:cat-id] *)
  idC : forall A, homC A A;
  (** [struc:cat-comp] *)
  compC : forall A B C, homC B C -> homC A B -> homC A C;
  (** [struc:cat-unit-laws] *)
  lamC : forall A B (f : homC A B), compC A B B (idC B) f = f;
  rhoC : forall A B (f : homC A B), compC A A B f (idC A) = f;
  (** [struct:cat-assoc] *)
  alphaC : forall A B C D (f : homC A B) (g : homC B C) (h : homC C D),
      compC A C D h (compC A B C g f) = compC A B D (compC B C D h g) f
}.

Arguments homC {w} A B.
Arguments idC {w} A.
Arguments compC {w A B C} g f.
Arguments lamC {w A B} f.
Arguments rhoC {w A B} f.
Arguments alphaC {w A B C D} f g h.

Notation "g ∘c f" := (compC g f) (at level 40, left associativity) : uf_scope.

(** Remark [rem:wild]: two of the coherences that a wild precategory
    does not require, the identification of [λ] and [ρ] at an identity,
    and the pentagon [eq:pentagon] for four composable arrows
    (formulations only). *)
Definition hasUnitCoh (C : WildPreCat) : Type
  := forall A : Ob C, lamC (idC A) = rhoC (idC A).

Definition hasPentagon (C : WildPreCat) : Type
  := forall (A B D E F : Ob C) (f : homC A B) (g : homC B D) (h : homC D E) (k : homC E F),
       ap (fun u => k ∘c u) (alphaC f g h) @ alphaC f (h ∘c g) k
         @ ap (fun u => u ∘c f) (alphaC g h k)
       = alphaC (g ∘c f) h k @ alphaC f g (k ∘c h).

(** Definition [def:precategory]. *)
Definition isPreCat (C : WildPreCat) : Type := forall A B : Ob C, isSet (homC A B).

(** Definition [def:iso-in-cat]. *)
Section Isos.

  Context {C : WildPreCat}.

  Definition isIsoC {A B : Ob C} (f : homC A B) : Type
    := {g : homC B A & f ∘c g = idC B} × {h : homC B A & h ∘c f = idC A}.

  Definition IsoC (A B : Ob C) : Type := {f : homC A B & isIsoC f}.

  Definition id_isIsoC (A : Ob C) : isIsoC (idC A)
    := ((idC A; lamC (idC A)); (idC A; lamC (idC A))).

  Definition idIsoC (A : Ob C) : IsoC A A := (idC A; id_isIsoC A).

  (** The two inverses of an isomorphism agree. *)
  Definition isIsoC_inv_eq {A B : Ob C} {f : homC A B} (i : isIsoC f)
    : fst (snd i) = fst (fst i).
  Proof.
    destruct i as [[g s] [h r]]. cbn.
    refine ((rhoC h)^ @ _ @ lamC g).
    refine (ap (fun k => h ∘c k) s^ @ _ @ ap (fun k => k ∘c g) r).
    exact (alphaC g f h).
  Defined.

  (** Post- and precomposition with an isomorphism are equivalences. *)
  Definition postcomp_isEquiv {A B : Ob C} {f : homC A B} (i : isIsoC f) (D : Ob C)
    : isEquiv (fun k : homC D A => f ∘c k).
  Proof.
    destruct i as [[g s] [h r]].
    refine (iso_to_isEquiv _ (fun k => h ∘c k) _ _).
    - intro k. exact (alphaC k f h @ ap (fun u => u ∘c k) r @ lamC k).
    - intro k. refine (ap (fun u => f ∘c (u ∘c k)) (isIsoC_inv_eq ((g; s); (h; r))) @ _).
      exact (alphaC k g f @ ap (fun u => u ∘c k) s @ lamC k).
  Defined.

  Definition precomp_isEquiv {A B : Ob C} {f : homC A B} (i : isIsoC f) (D : Ob C)
    : isEquiv (fun k : homC B D => k ∘c f).
  Proof.
    destruct i as [[g s] [h r]].
    refine (iso_to_isEquiv _ (fun k => k ∘c g) _ _).
    - intro k. exact ((alphaC g f k)^ @ ap (fun u => k ∘c u) s @ rhoC k).
    - intro k. refine (ap (fun u => (k ∘c u) ∘c f) (isIsoC_inv_eq ((g; s); (h; r)))^ @ _).
      exact ((alphaC f h k)^ @ ap (fun u => k ∘c u) r @ rhoC k).
  Defined.

  (** [isIsoC(f)] is a proposition: each factor is contractible, being a
      fiber of an equivalence. *)
  Definition isIsoC_isProp `{Funext} {A B : Ob C} (f : homC A B) : isProp (isIsoC f).
  Proof.
    intros i i'. apply isContr_isProp'.
    refine (Sigma_isContr _ (fun _ => _)).
    - refine (isContr_Eqv _ (postcomp_isEquiv i B (idC B))).
      exact (tot (fun g (p : idC B = f ∘c g) => p^);
             tot_isEquiv _ (fun g => snd (symm_eqv (x := idC B) (y := f ∘c g)))).
    - refine (isContr_Eqv _ (precomp_isEquiv i A (idC A))).
      exact (tot (fun h (p : idC A = h ∘c f) => p^);
             tot_isEquiv _ (fun h => snd (symm_eqv (x := idC A) (y := h ∘c f)))).
  Defined.

  Definition path_IsoC `{Funext} {A B : Ob C} {e e' : IsoC A B} (p : fst e = fst e') : e = e'
    := path_sigma_prop (fun f => isIsoC_isProp f) (u := e) (v := e') p.

  (** The inverse [f⁻¹] of an isomorphism. *)
  Definition invC {A B : Ob C} (e : IsoC A B) : homC B A := fst (fst (snd e)).

  Definition IsoC_inv {A B : Ob C} (e : IsoC A B) : IsoC B A.
  Proof.
    destruct e as [f i]. pose (q := isIsoC_inv_eq i).
    destruct i as [[g s] [h r]]. cbn in q.
    refine (g; ((f; trp (fun u => u ∘c f = idC A) q r); (f; s))).
  Defined.

  (** Composition of isomorphisms. *)
  Definition IsoC_comp {A B D : Ob C} (e' : IsoC B D) (e : IsoC A B) : IsoC A D.
  Proof.
    destruct e as [f [[g s] [h r]]], e' as [f' [[g' s'] [h' r']]].
    refine (f' ∘c f; ((g ∘c g'; _); (h ∘c h'; _))).
    - refine (alphaC _ _ _ @ ap (fun u => u ∘c g') ((alphaC _ _ _)^) @ _).
      refine (ap (fun u => (f' ∘c u) ∘c g') s @ ap (fun u => u ∘c g') (rhoC f') @ s').
    - refine (alphaC _ _ _ @ ap (fun u => u ∘c f) ((alphaC _ _ _)^) @ _).
      refine (ap (fun u => (h ∘c u) ∘c f) r' @ ap (fun u => u ∘c f) (rhoC h) @ r).
  Defined.

  (** Definition [def:univalent-cat]. *)
  Definition idtoiso {A B : Ob C} (p : A = B) : IsoC A B
    := match p with refl => idIsoC A end.

End Isos.

Definition isUnivalent (C : WildPreCat) : Type
  := forall A B : Ob C, isEquiv (@idtoiso C A B).

(** Definition [def:category]. *)
Definition WildCat : Type := {C : WildPreCat & isUnivalent C}.

Definition PreCat : Type := {C : WildPreCat & isPreCat C}.

Definition Cat : Type := {C : WildPreCat & isPreCat C × isUnivalent C}.

Definition isSet_Eqv {X Y : Type} (e : X ≃ Y) (h : isSet X) : isSet Y
  := IsHSet_isSet (@istrunc_equiv_istrunc X Y (Equiv_of_Eqv e) 0 (isSet_IsHSet h)).

(** *** Examples *)

(** The wild category of types: all laws hold by [refl]. *)
Definition TypeCat : WildPreCat
  := {| Ob := Type;
        homC := fun A B => A -> B;
        idC := fun A => id A;
        compC := fun A B C g f => g ∘ f;
        lamC := fun A B f => refl;
        rhoC := fun A B f => refl;
        alphaC := fun A B C D f g h => refl |}.

(** Isomorphisms in [TypeCat] are the equivalences. *)
Definition isIsoC_isEquiv `{Funext} {A B : Type} (f : A -> B)
  : (isIsoC (C := TypeCat) f) ≃ isEquiv f.
Proof.
  refine (Eqv_of_props (isIsoC_isProp (C := TypeCat) f) (isEquiv_isProp f) _ _).
  - intros [[g s] [h r]].
    refine (iso_to_isEquiv f g _ (ptw s)).
    intro x. exact (ap (fun u => u (f x)) (isIsoC_inv_eq (C := TypeCat) ((g; s); (h; r)))^
                    @ ptw r x).
  - intro t. exact ((eqinv t; ptw_inv (eqinv_r t)); (eqinv t; ptw_inv (eqinv_l t))).
Defined.

Definition IsoC_Eqv_TypeCat `{Funext} (A B : Type) : IsoC (C := TypeCat) A B ≃ (A ≃ B)
  := (tot (fun f => fst (isIsoC_isEquiv f)); tot_isEquiv _ (fun f => snd (isIsoC_isEquiv f))).

(** The wild category of types is univalent, by the univalence axiom. *)
Definition TypeCat_isUnivalent `{Univalence} : isUnivalent TypeCat.
Proof.
  intros A B.
  refine (isEquiv_homotopic (fst (Eqv_inv (IsoC_Eqv_TypeCat A B)) ∘ idtoeqv) _ _ _).
  - intro p. destruct p. apply (path_IsoC (C := TypeCat)). exact refl.
  - exact (comp_isEquiv (ua A B) (snd (Eqv_inv (IsoC_Eqv_TypeCat A B)))).
Defined.

(** The unit and associativity laws for pointed maps. *)
Definition pcomp_pid_l {X Y : Ustar} (f : X →* Y) : pcomp (pid Y) f = f.
Proof.
  destruct f as [f fp]. unfold pcomp, pid. cbn.
  exact (ap (fun q => (f; q)) (trans_1p _ @ ap_id fp)).
Defined.

Definition pcomp_pid_r {X Y : Ustar} (f : X →* Y) : pcomp f (pid X) = f.
Proof.
  destruct f as [f fp]. unfold pcomp, pid. cbn.
  exact refl.
Defined.

Definition pcomp_assoc {X Y Z W : Ustar} (h : Z →* W) (g : Y →* Z) (f : X →* Y)
  : pcomp h (pcomp g f) = pcomp (pcomp h g) f.
Proof.
  destruct X as [A a], Y as [B b], Z as [C c], W as [D d],
    f as [f fp], g as [g gp], h as [h hp]. cbn in *.
  revert d hp. refine (paths_ind_r _ _ _).
  revert c gp h. refine (paths_ind_r _ _ _). intro h.
  revert b fp g h. refine (paths_ind_r _ _ _). intros g h.
  exact refl.
Defined.

(** Remark [rem:wild]: the wild category of pointed types, with the laws
    of the exercise. *)
Definition PtdCat `{Funext} : WildPreCat
  := {| Ob := Ustar;
        homC := fun A B => A →* B;
        idC := pid;
        compC := fun A B C g f => pcomp g f;
        lamC := fun A B f => pcomp_pid_l f;
        rhoC := fun A B f => pcomp_pid_r f;
        alphaC := fun A B C D f g h => pcomp_assoc h g f |}.

(** The wild category of families over [X], with fiberwise maps. *)
Definition FamCat (X : Type) : WildPreCat
  := {| Ob := X -> Type;
        homC := fun A B => forall x, A x -> B x;
        idC := fun A x a => a;
        compC := fun A B C g f x a => g x (f x a);
        lamC := fun A B f => refl;
        rhoC := fun A B f => refl;
        alphaC := fun A B C D f g h => refl |}.

(** Definition [def:full-subcat]: the full subcategory on a predicate.
    (Placed among the examples after [def:category], before the category of sets, which is defined as a full subcategory.) *)
Definition FullSub (C : WildPreCat) (P : Ob C -> PropU) : WildPreCat
  := {| Ob := {A : Ob C & fst (P A)};
        homC := fun A B => homC (fst A) (fst B);
        idC := fun A => idC (fst A);
        compC := fun A B D g f => g ∘c f;
        lamC := fun A B f => lamC f;
        rhoC := fun A B f => rhoC f;
        alphaC := fun A B D E f g h => alphaC f g h |}.

Definition FullSub_isPreCat (C : WildPreCat) (P : Ob C -> PropU) (pc : isPreCat C)
  : isPreCat (FullSub C P)
  := fun A B => pc (fst A) (fst B).

Definition idtoiso_FullSub (C : WildPreCat) (P : Ob C -> PropU)
  {A B : Ob (FullSub C P)} (p : A = B)
  : fst (idtoiso p) = fst (idtoiso (ap fst p)).
Proof. destruct p. exact refl. Defined.

Definition FullSub_isUnivalent `{Funext} (C : WildPreCat) (P : Ob C -> PropU)
  (u : isUnivalent C) : isUnivalent (FullSub C P).
Proof.
  intros A B.
  pose (e := Eqv_comp (subtype_paths_eqv (fun A => snd (P A)) A B) (idtoiso; u (fst A) (fst B))).
  refine (isEquiv_homotopic (fun p => (fst (fst e p); snd (fst e p)) : IsoC (C := FullSub C P) A B)
            _ _ _).
  - intro p. apply (path_IsoC (C := FullSub C P)). exact (idtoiso_FullSub C P p)^.
  - refine (iso_to_isEquiv _ (fun i => eqinv (snd e) ((fst i; snd i) : IsoC (fst A) (fst B))) _ _).
    + intro p. exact (eqinv_l (snd e) p).
    + intro i. pose (q := eqinv_r (snd e) ((fst i; snd i) : IsoC (fst A) (fst B))).
      apply (path_IsoC (C := FullSub C P)). exact (ap fst q).
Defined.

(** The category of sets. *)
Definition isSetU `{Funext} (A : Ob TypeCat) : PropU := (isSet A; isSet_isProp A).

Definition SetCat `{Funext} : WildPreCat := FullSub TypeCat isSetU.

Definition SetCat_isCat `{Univalence} : isPreCat SetCat × isUnivalent SetCat
  := ((fun A B => Pi_isSet (fun _ => snd B));
      FullSub_isUnivalent TypeCat isSetU TypeCat_isUnivalent).

(** The category of groups. *)
Definition compG_idG_l {G H : Group} (f : Hom G H) : compG (idG H) f = f.
Proof. destruct f as [k]. exact (ap inc (pcomp_pid_l k)). Defined.

Definition compG_idG_r {G H : Group} (f : Hom G H) : compG f (idG G) = f.
Proof. destruct f as [k]. exact (ap inc (pcomp_pid_r k)). Defined.

Definition compG_assoc {G H K L : Group} (h : Hom K L) (g : Hom H K) (f : Hom G H)
  : compG h (compG g f) = compG (compG h g) f.
Proof. destruct f as [f], g as [g], h as [h]. exact (ap inc (pcomp_assoc h g f)). Defined.

Definition GroupCat `{Funext} : WildPreCat
  := {| Ob := Group;
        homC := Hom;
        idC := idG;
        compC := fun G H K g f => compG g f;
        lamC := fun G H f => compG_idG_l f;
        rhoC := fun G H f => compG_idG_r f;
        alphaC := fun G H K L f g h => compG_assoc h g f |}.

(** The category of [G]-sets. *)
Definition GSetCat (G : Group) : WildPreCat
  := {| Ob := GSet G;
        homC := HomGs;
        idC := fun X z x => x;
        compC := fun X Y Z g f z x => g z (f z x);
        lamC := fun X Y f => refl;
        rhoC := fun X Y f => refl;
        alphaC := fun X Y Z W f g h => refl |}.

(** The category of groups is univalent: compare with
    [path_Group_Iso_eqv] (Section 4.4). *)
Definition GroupCat_isIso_isIso `{fe : Funext} {G H : Group} (f : Hom G H)
  (i : isIsoC (C := GroupCat) f) : isIso f.
Proof.
  destruct i as [[g s] [h r]].
  refine (fst (isIsoC_isEquiv (fst (Bf f)))
            ((fst (Bf g); ap (fun u : Hom H H => fst (Bf u)) s);
             (fst (Bf h); ap (fun u : Hom G G => fst (Bf u)) r))).
Defined.

Definition GroupCat_idtoiso_hom `{Univalence} {G K : Group} (p : G = K)
  : fst (idtoiso (C := GroupCat) p) = fst (fst (path_Group_Iso_eqv G K) p).
Proof. destruct p. destruct G as [X]. exact refl. Defined.

Definition GroupCat_isUnivalent `{Univalence} : isUnivalent GroupCat.
Proof.
  intros G K.
  pose (Φ := path_Group_Iso_eqv G K).
  pose (toC := fun (f : Hom G K) (t : isIso f) =>
                 let p := eqinv (snd Φ) ((f; t) : Iso G K) in
                 trp (fun u => isIsoC (C := GroupCat) u)
                   (GroupCat_idtoiso_hom p @ ap fst (eqinv_r (snd Φ) ((f; t) : Iso G K)))
                   (snd (idtoiso (C := GroupCat) p))).
  pose (Ψ := (tot (fun f => fst (Eqv_of_props (isEquiv_isProp _) (isIsoC_isProp (C := GroupCat) f)
                                    (toC f) (GroupCat_isIso_isIso f)));
              tot_isEquiv _ (fun f => snd (Eqv_of_props (isEquiv_isProp _)
                                             (isIsoC_isProp (C := GroupCat) f)
                                             (toC f) (GroupCat_isIso_isIso f))))
             : Iso G K ≃ IsoC (C := GroupCat) G K).
  refine (isEquiv_homotopic (fst Ψ ∘ fst Φ) _ _ (comp_isEquiv (snd Φ) (snd Ψ))).
  intro p. apply (path_IsoC (C := GroupCat)). exact (GroupCat_idtoiso_hom p)^.
Defined.

(** The category of [G]-sets is univalent: isomorphisms are the
    fiberwise equivalences. *)
Section GSetUnivalent.

  Context `{Univalence} {G : Group} (X Y : GSet G).

  Definition GSetIso_fw (e : forall z, el X z ≃ el Y z) : IsoC (C := GSetCat G) X Y.
  Proof.
    refine ((fun z => fst (e z)); ((fun z => eqinv (snd (e z)); _); (fun z => eqinv (snd (e z)); _))).
    - apply ptw_inv. intro z. apply ptw_inv. intro y. exact (eqinv_r (snd (e z)) y).
    - apply ptw_inv. intro z. apply ptw_inv. intro x. exact (eqinv_l (snd (e z)) x).
  Defined.

  Definition GSetIso_bw (i : IsoC (C := GSetCat G) X Y) (z : utype (BG G)) : el X z ≃ el Y z
    := (fst i z;
        fst (isIsoC_isEquiv (fst i z))
          ((fst (fst (snd i)) z; ap (fun u => u z) (snd (fst (snd i))));
           (fst (snd (snd i)) z; ap (fun u => u z) (snd (snd (snd i)))))).

  Definition GSetIso_eqv : (forall z, el X z ≃ el Y z) ≃ IsoC (C := GSetCat G) X Y.
  Proof.
    refine (mkEqv GSetIso_fw GSetIso_bw _ _).
    - intro e. apply ptw_inv. intro z. apply path_Eqv. exact refl.
    - intro i. apply (path_IsoC (C := GSetCat G)). exact refl.
  Defined.

  Definition GSet_paths_eqv : (X = Y) ≃ (forall z, el X z ≃ el Y z).
  Proof.
    refine (Eqv_comp (ptw; funext X Y) _).
    refine (Eqv_of_Equiv (equiv_functor_forall_id (fun z => Equiv_of_Eqv _))).
    exact (Eqv_comp (subtype_paths_eqv (fun A => isSet_isProp A) (X z) (Y z)) (idtoeqv; ua _ _)).
  Defined.

End GSetUnivalent.

Definition GSetCat_isUnivalent `{Univalence} (G : Group) : isUnivalent (GSetCat G).
Proof.
  intros X Y.
  refine (isEquiv_homotopic (fst (GSetIso_eqv X Y) ∘ fst (GSet_paths_eqv X Y)) _ _
            (comp_isEquiv (snd (GSet_paths_eqv X Y)) (snd (GSetIso_eqv X Y)))).
  intro p. destruct p. apply (path_IsoC (C := GSetCat G)). exact refl.
Defined.

Definition GSetCat_isPreCat `{Funext} (G : Group) : isPreCat (GSetCat G)
  := fun X Y => HomGs_isSet X Y.

Definition GroupCat_isPreCat `{Funext} : isPreCat GroupCat := Hom_isSet.

(** A criterion for univalence: the identity types are equivalent to a
    type of morphisms with a property implied by being an isomorphism,
    compatibly with [idtoiso]. *)
Definition isUnivalent_from `{Funext} (C : WildPreCat)
  (Q : forall A B : Ob C, homC A B -> Type) (hQ : forall A B f, isProp (Q A B f))
  (toQ : forall A B (f : homC A B), isIsoC f -> Q A B f)
  (Φ : forall A B : Ob C, (A = B) ≃ {f : homC A B & Q A B f})
  (L : forall A B (p : A = B), fst (idtoiso p) = fst (fst (Φ A B) p))
  : isUnivalent C.
Proof.
  intros A B.
  pose (toC := fun (f : homC A B) (q : Q A B f) =>
                 let p := eqinv (snd (Φ A B)) (f; q) in
                 trp (fun u => isIsoC u) (L A B p @ ap fst (eqinv_r (snd (Φ A B)) (f; q)))
                   (snd (idtoiso p))).
  pose (Ψ := (tot (fun f => fst (Eqv_of_props (hQ A B f) (isIsoC_isProp f) (toC f) (toQ A B f)));
              tot_isEquiv _ (fun f => snd (Eqv_of_props (hQ A B f) (isIsoC_isProp f)
                                             (toC f) (toQ A B f))))
             : {f : homC A B & Q A B f} ≃ IsoC A B).
  refine (isEquiv_homotopic (fst Ψ ∘ fst (Φ A B)) _ _ (comp_isEquiv (snd (Φ A B)) (snd Ψ))).
  intro p. apply path_IsoC. exact (L A B p)^.
Defined.

(** The wild category of pointed types is univalent. *)
Definition PtdCat_isUnivalent `{Univalence} : isUnivalent PtdCat.
Proof.
  refine (isUnivalent_from PtdCat (fun X Y f => isEquiv (fst f)) (fun X Y f => isEquiv_isProp _)
            _ (fun X Y => (path_to_pEqv; path_to_pEqv_isEquiv X Y)) _).
  - intros X Y f [[g s] [h r]].
    exact (fst (isIsoC_isEquiv (fst f))
              ((fst g; ap (fun u : Y →* Y => fst u) s); (fst h; ap (fun u : X →* X => fst u) r))).
  - intros X Y p. destruct p. exact refl.
Defined.

(** The wild category of families over [X] is univalent. *)
Definition FamPaths_eqv `{Univalence} {X : Type} (A B : X -> Type)
  : (A = B) ≃ {f : (forall x, A x -> B x) & forall x, isEquiv (f x)}.
Proof.
  refine (Eqv_comp (ptw; funext A B) _).
  refine (Eqv_comp (Eqv_of_Equiv (equiv_functor_forall_id
                                    (fun x => Equiv_of_Eqv (idtoeqv; ua (A x) (B x))))) _).
  exact (Eqv_of_Equiv (equiv_sig_coind (fun x => A x -> B x) (fun x (f : A x -> B x) => isEquiv f))^-1).
Defined.

Definition FamCat_isUnivalent `{Univalence} (X : Type) : isUnivalent (FamCat X).
Proof.
  refine (isUnivalent_from (FamCat X) (fun A B f => forall x, isEquiv (f x))
            (fun A B f => Pi_isProp (fun x => isEquiv_isProp _)) _ FamPaths_eqv _).
  - intros A B f [[g s] [h r]] x.
    exact (fst (isIsoC_isEquiv (f x))
              ((g x; ap (fun u => u x) s); (h x; ap (fun u => u x) r))).
  - intros A B p. destruct p. exact refl.
Defined.

(** In a precategory the hom-types of isomorphisms are sets. *)
Definition IsoC_isSet `{Funext} {C : WildPreCat} (pc : isPreCat C) (A B : Ob C)
  : isSet (IsoC A B)
  := Sigma_isSet (pc A B) (fun f => prop_is_set (isIsoC_isProp f)).

(** Lemma [lem:obj-gpd]: the type of objects of a category is a groupoid. *)
Definition Ob_isGrpd `{Funext} (C : Cat) : isGrpd (Ob (fst C)).
Proof.
  intros A B. refine (isSet_Eqv _ (IsoC_isSet (fst (snd C)) A B)).
  exact (Eqv_inv (idtoiso; snd (snd C) A B)).
Defined.

(** Example [ex:poset]: preorders and posets. *)
Definition isPreorder (C : WildPreCat) : Type := forall A B : Ob C, isProp (homC A B).

Definition isPoset (C : WildPreCat) : Type := isPreorder C × isUnivalent C.

Definition preorder_isPreCat (C : WildPreCat) (p : isPreorder C) : isPreCat C
  := fun A B => prop_is_set (p A B).

Definition preorder_IsoC_isProp `{Funext} (C : WildPreCat) (p : isPreorder C) (A B : Ob C)
  : isProp (IsoC A B)
  := Sigma_isProp (p A B) (fun f => isIsoC_isProp f).

Definition antisymmetric (C : WildPreCat) : Type
  := forall A B : Ob C, homC A B -> homC B A -> A = B.

(** In a poset the type of objects is a set. *)
Definition poset_isSet `{Funext} (C : WildPreCat) (p : isPoset C) : isSet (Ob C)
  := fun A B => isProp_Eqv (Eqv_inv (idtoiso; snd p A B)) (preorder_IsoC_isProp C (fst p) A B).

(** A preorder is univalent iff its type of objects is a set and the
    relation is antisymmetric. *)
Definition poset_antisym (C : WildPreCat) (p : isPoset C) : antisymmetric C
  := fun A B f g => eqinv (snd p A B) (f; ((g; fst p B B _ _); (g; fst p A A _ _))).

Definition antisym_isUnivalent `{Funext} (C : WildPreCat) (p : isPreorder C)
  (sO : isSet (Ob C)) (a : antisymmetric C) : isUnivalent C
  := fun A B => snd (Eqv_of_props (sO A B) (preorder_IsoC_isProp C p A B) idtoiso
                       (fun e => a A B (fst e) (fst (fst (snd e))))).

(** A preorder from a family of propositions with reflexivity and
    transitivity. *)
Definition mkPreorder (P : Type) (le : P -> P -> PropU)
  (rf : forall x, fst (le x x)) (tr : forall x y z, fst (le x y) -> fst (le y z) -> fst (le x z))
  : WildPreCat
  := {| Ob := P;
        homC := fun x y => fst (le x y);
        idC := rf;
        compC := fun x y z g f => tr x y z f g;
        lamC := fun x y f => snd (le x y) _ _;
        rhoC := fun x y f => snd (le x y) _ _;
        alphaC := fun x y z w f g h => snd (le x w) _ _ |}.

Definition mkPreorder_isPreorder P le rf tr : isPreorder (mkPreorder P le rf tr)
  := fun x y => snd (le x y).

(** [(ℕ, ≤)] is a poset. *)
Definition leqU (m n : ℕ) : PropU := ((m <= n)%nat; IsHProp_isProp).

Definition NatLeq : WildPreCat
  := mkPreorder ℕ leqU (fun n => leq_refl n) (fun x y z l l' => leq_trans l l').

Definition NatLeq_isPoset `{Funext} : isPoset NatLeq
  := (mkPreorder_isPreorder _ _ _ _;
      antisym_isUnivalent NatLeq (mkPreorder_isPreorder _ _ _ _) ℕ_isSet
        (fun m n l l' => leq_antisym l l')).

(** [(ℤ, ≤)], with [x ≤ y] iff [y = x + n] for some [n : ℕ]; that it
    is a poset is stated only. *)
Definition zadd_assoc (x y z : ℤ) : zadd (zadd x y) z = zadd x (zadd y z).
Proof.
  apply toInt_inj. rewrite !toInt_zadd. exact (int_add_assoc _ _ _)^.
Defined.

Definition ZLe (x y : ℤ) : PropU := (ptrunc {n : ℕ & y = zadd x (iplus n)}; ptrunc_isProp).

Definition IntLeq : WildPreCat
  := mkPreorder ℤ ZLe (fun x => trunc (0%nat; refl))
       (fun x y z l l' => ptrunc_rec ptrunc_isProp (fun w => ptrunc_rec ptrunc_isProp (fun w' =>
          trunc (add (fst w) (fst w');
                 snd w' @ ap (fun u => zadd u (iplus (fst w'))) (snd w)
                 @ zadd_assoc x (iplus (fst w)) (iplus (fst w'))
                 @ ap (zadd x) (iplus_add (fst w) (fst w'))^)) l') l).

Definition IntLeq_isPoset_stmt : Type := isPoset IntLeq.

(** [(Prop, →)] is a poset. *)
Definition PropImp `{Funext} : WildPreCat
  := mkPreorder PropU (fun P Q => ((fst P -> fst Q); fun_isProp (snd Q)))
       (fun P x => x) (fun P Q R f g x => g (f x)).

Definition PropImp_isPoset `{Univalence} : isPoset PropImp
  := (mkPreorder_isPreorder _ _ _ _;
      antisym_isUnivalent PropImp (mkPreorder_isPreorder _ _ _ _) PropU_isSet
        (fun P Q f g => path_PropU f g)).

(** [(Sub(S), ⊆)] is a poset. *)
Definition SubIncl `{Funext} (S : Type) : WildPreCat
  := mkPreorder (Sub S)
       (fun P Q => (P ⊆ Q; Pi_isProp (fun s => fun_isProp (snd (Q s)))))
       (fun P s x => x) (fun P Q R f g s x => g s (f s x)).

Definition SubIncl_isPoset `{Univalence} (S : Type) : isPoset (SubIncl S)
  := (mkPreorder_isPreorder _ _ _ _;
      antisym_isUnivalent (SubIncl S) (mkPreorder_isPreorder _ _ _ _)
        (Pi_isSet (fun _ => PropU_isSet))
        (fun P Q f g => ptw_inv (fun s => path_PropU (f s) (g s)))).

(** The two-element type with the always true relation is a preorder
    that is not univalent. *)
Definition BoolTrue : WildPreCat
  := mkPreorder Bool (fun _ _ => (True; True_isProp)) (fun _ => triv) (fun _ _ _ _ _ => triv).

Definition BoolTrue_not_univalent : ¬ isUnivalent BoolTrue
  := fun u => yes_ne_no (eqinv (u yes no) (triv; ((triv; refl); (triv; refl)))).

(** Exercise [xca:order-poset]: the orders with divisibility form a poset
    (statement only). *)
Definition OrderDiv `{Univalence} : WildPreCat
  := mkPreorder Order (fun d k => (divides d k; Pi_isProp (fun n => fun_isProp (snd (HO d n)))))
       (fun d n x => x) (fun d k l f g n x => f n (g n x)).

Definition xca_order_poset `{Univalence} : Type := isPoset OrderDiv.

(** Definition [def:wild-pre-groupoid]. *)
Definition isPreGrpd (C : WildPreCat) : Type := forall (A B : Ob C) (f : homC A B), isIsoC f.

(** Example [ex:path-groupoid]: the path groupoid of a type, with
    composition [q ⋅ p]. *)
Definition PathGrpd (X : Type) : WildPreCat
  := {| Ob := X;
        homC := fun x y => x = y;
        idC := fun x => refl;
        compC := fun x y z q p => q ⋅ p;
        lamC := fun x y p => trans_p1 p;
        rhoC := fun x y p => trans_1p p;
        alphaC := fun x y z w p q r => trans_assoc p q r |}.

Definition PathGrpd_isPreGrpd (X : Type) : isPreGrpd (PathGrpd X)
  := fun x y p => ((p⁻¹; trans_Vp p); (p⁻¹; trans_pV p)).

Definition PathGrpd_isUnivalent `{Funext} (X : Type) : isUnivalent (PathGrpd X).
Proof.
  intros x y. refine (iso_to_isEquiv _ fst _ _).
  - intro p. destruct p. exact refl.
  - intro e. apply (path_IsoC (C := PathGrpd X)).
    destruct e as [p i]. destruct p. exact refl.
Defined.

Definition PathGrpd_isPreCat (X : Type) (g : isGrpd X) : isPreCat (PathGrpd X) := g.

(** Example [def:slice-cat]: the slice precategory [C/C₀] of a
    precategory. *)
Section Slice.

  Context `{Funext} (C : WildPreCat) (pc : isPreCat C) (C0 : Ob C).

  Definition SliceOb : Type := {A : Ob C & homC A C0}.

  Definition SliceHom (A A' : SliceOb) : Type
    := {g : homC (fst A) (fst A') & snd A' ∘c g = snd A}.

  Definition path_SliceHom {A A' : SliceOb} (g g' : SliceHom A A') (p : fst g = fst g') : g = g'
    := path_sigma_prop (fun _ => pc _ _ _ _) (u := g) (v := g') p.

  Definition slice_id (A : SliceOb) : SliceHom A A := (idC (fst A); rhoC (snd A)).

  Definition slice_comp {A A' A'' : SliceOb} (g' : SliceHom A' A'') (g : SliceHom A A')
    : SliceHom A A''
    := (fst g' ∘c fst g;
        alphaC (fst g) (fst g') (snd A'') @ ap (fun u => u ∘c fst g) (snd g') @ snd g).

  Definition SliceCat : WildPreCat
    := {| Ob := SliceOb;
          homC := SliceHom;
          idC := slice_id;
          compC := @slice_comp;
          lamC := fun A A' g => path_SliceHom (slice_comp (slice_id A') g) g (lamC (fst g));
          rhoC := fun A A' g => path_SliceHom (slice_comp g (slice_id A)) g (rhoC (fst g));
          alphaC := fun A A' A'' A''' f g h =>
                      path_SliceHom (slice_comp h (slice_comp g f)) (slice_comp (slice_comp h g) f)
                        (alphaC (fst f) (fst g) (fst h)) |}.

  Definition SliceCat_isPreCat : isPreCat SliceCat
    := fun A A' => Sigma_isSet (pc _ _) (fun g => prop_is_set (pc _ _ _ _)).

  (** If [C] is univalent, then so is [C/C₀] (statement only). *)
  Definition SliceCat_isUnivalent_stmt : Type := isUnivalent C -> isUnivalent SliceCat.

End Slice.

(** Exercise [xca:univ-slice-cat]: the slice [U/B] of the universe, a
    wild precategory, with morphisms [g : A → A'] and homotopies
    [f(a) = f'(g(a))]. *)
Definition UnivSlice `{Funext} (B : Type) : WildPreCat
  := {| Ob := {A : Type & A -> B};
        homC := fun A A' => {g : fst A -> fst A' & forall a, snd A a = snd A' (g a)};
        idC := fun A => (id (fst A); fun a => refl);
        compC := fun A A' A'' g' g =>
                   (fst g' ∘ fst g; fun a => snd g' (fst g a) ⋅ snd g a);
        lamC := fun A A' g => refl;
        rhoC := fun A A' g => ap (fun h => (fst g; h)) (ptw_inv (fun a => trans_1p (snd g a)));
        alphaC := fun A A' A'' A''' f g h =>
                    ap (fun k => (fst h ∘ fst g ∘ fst f; k))
                       (ptw_inv (fun a => trans_assoc (snd f a) (snd g (fst f a))
                                            (snd h (fst g (fst f a))))) |}.
