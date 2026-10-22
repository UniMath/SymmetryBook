(** * Section 6.6 The Yoneda Lemma

    Part of Chapter 6 ([cats.tex]); see [Cats.v] for an overview of the
    chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:yoneda]: presheaves [PSh C :≡ Set^{C^op}] (the
      functor precategory of Section 6.4), the representables
      [yo_ob C₀ :≡ Hom(-, C₀)] and the Yoneda embedding [yo].
    - Theorem [thm:yoneda-lemma]: [Hom(yo(C₀), F) ≃ F(C₀)] by evaluation
      at the identity ([yoneda_eqv]), natural in [F] ([yoneda_nat_F], by
      [refl]) and in [C₀] ([yoneda_nat_C]).
    - Corollary [cor:yo-ff] ([yo_ff]).
    - Definition [def:repr] ([isRepr]).

    Left out (statements only, no proofs yet)
    - Corollaries [cor:yo-emb-obj] ([cor_yo_emb_obj_stmt]) and
      [cor:repr-prop] ([cor_repr_prop_stmt]); both need the univalence of
      the presheaf category (exercise [xca:functor-cat-univalent]).
    - Lemma [lem:adj-via-repr] ([lem_adj_via_repr_stmt]) and corollary
      [cor:adj-unique] ([cor_adj_unique_stmt]). *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Types.Unit Truncations.Core Spaces.Nat.Core.
From SymmetryBook Require Export Cats.S05_Adjunctions.

Local Open Scope uf_scope.

(** ** 6.6 The Yoneda Lemma *)

Section Yoneda.

  Context `{Funext} (C : WildPreCat) (pc : isPreCat C).

  (** The precategory [Set^{C^op}] of presheaves. *)
  Definition PSh : WildPreCat := FunctorCat (Op C) SetCat SetCat_isPreCat.

  (** The contravariant representable functor [h_{C₀} :≡ Hom(-, C₀)],
      into sets. *)
  Definition yo_ob (C0 : Ob C) : Ob PSh
    := Build_Functor (Op C) SetCat (fun A : Ob C => ((homC (w := C) A C0; pc A C0) : Ob SetCat))
         (fun A B (f : homC (w := C) B A) (k : homC (w := C) A C0) => @compC C B A C0 k f)
         (fun A => ptw_inv (fun k : homC (w := C) A C0 => rhoC k))
         (fun A B E (f : homC (w := C) B A) (g : homC (w := C) E B) =>
            ptw_inv (fun k : homC (w := C) A C0 => alphaC g f k)).

  Definition yo_map {C0 C1 : Ob C} (f : homC C0 C1) : homC (w := PSh) (yo_ob C0) (yo_ob C1)
    := ((fun A (k : homC (w := C) A C0) => f ∘c k);
        fun A B (g : homC (w := C) B A) => ptw_inv (fun k : homC (w := C) A C0 => (alphaC g k f)^)).

  Definition yo_fid (C0 : Ob C) : yo_map (idC C0) = idC (yo_ob C0)
    := path_NatTrans SetCat_isPreCat (yo_map (idC C0)) (idC (yo_ob C0))
         (fun A => ptw_inv (fun k : homC (w := C) A C0 => lamC k)).

  Definition yo_fcomp {C0 C1 C2 : Ob C} (f : homC C0 C1) (g : homC C1 C2)
    : yo_map (g ∘c f) = yo_map g ∘c yo_map f
    := path_NatTrans SetCat_isPreCat (yo_map (g ∘c f)) (yo_map g ∘c yo_map f)
         (fun A => ptw_inv (fun k : homC (w := C) A C0 => (alphaC k f g)^)).

  (** Definition [def:yoneda]: the Yoneda embedding [yo : C → Set^{C^op}]. *)
  Definition yo : Functor C PSh
    := Build_Functor C PSh yo_ob (fun C0 C1 f => yo_map f) yo_fid
         (fun C0 C1 C2 f g => yo_fcomp f g).

  (** Theorem [thm:yoneda-lemma]: evaluation at [id_{C₀}] gives
      [Hom(yo(C₀), F) ≃ F(C₀)]. *)
  Definition yo_ev (C0 : Ob C) (F : Ob PSh) (a : homC (w := PSh) (yo_ob C0) F)
    : fst (fob F C0)
    := fst a C0 (idC C0).

  Definition yo_inv (C0 : Ob C) (F : Ob PSh) (x : fst (fob F C0))
    : homC (w := PSh) (yo_ob C0) F.
  Proof.
    refine ((fun A (k : homC (w := C) A C0) => fmap F (A := C0) (B := A) k x); _).
    intros A B g. apply ptw_inv. intro k.
    exact (ap (fun u => u x) (fcomp F (A := C0) (B := A) (E := B) k g))^.
  Defined.

  Definition yoneda_eqv (C0 : Ob C) (F : Ob PSh)
    : homC (w := PSh) (yo_ob C0) F ≃ fst (fob F C0).
  Proof.
    refine (mkEqv (yo_ev C0 F) (yo_inv C0 F) _ _).
    - intro a. apply (path_NatTrans SetCat_isPreCat). intro A. apply ptw_inv. intro k.
      exact (ap (fun u => u (idC C0)) (snd a C0 A k) @ ap (fst a A) (lamC k)).
    - intro x. exact (ap (fun u => u x) (fid F C0)).
  Defined.

  (** Naturality in [F] and in [C₀]. *)
  Definition yoneda_nat_F (C0 : Ob C) {F F' : Ob PSh} (b : homC (w := PSh) F F')
    (a : homC (w := PSh) (yo_ob C0) F)
    : yo_ev C0 F' (b ∘c a) = fst b C0 (yo_ev C0 F a)
    := refl.

  Definition yoneda_nat_C (C0 C1 : Ob C) (g : homC (w := C) C1 C0) (F : Ob PSh)
    (a : homC (w := PSh) (yo_ob C0) F)
    : yo_ev C1 F (a ∘c yo_map g) = fmap F (A := C0) (B := C1) g (yo_ev C0 F a).
  Proof.
    unfold yo_ev. cbn.
    refine (ap (fst a C1) (rhoC g @ (lamC g)^) @ _).
    exact (ap (fun u => u (idC C0)) (snd a C0 C1 g))^.
  Defined.

  (** Corollary [cor:yo-ff]: the Yoneda embedding is fully faithful. *)
  Definition yo_ff : isFullyFaithful yo.
  Proof.
    intros C0 C1.
    refine (isEquiv_homotopic (yo_inv C0 (yo_ob C1)) _ _ (snd (Eqv_inv (yoneda_eqv C0 (yo_ob C1))))).
    intro f. apply (path_NatTrans SetCat_isPreCat). intro A. exact refl.
  Defined.

  (** Corollary [cor:yo-emb-obj] (statement only): for a category, [yo]
      is injective on objects. *)
  Definition cor_yo_emb_obj_stmt : Type := isUnivalent C -> isInj (fob yo).

  (** Definition [def:repr]. *)
  Definition isRepr (F : Ob PSh) : Type := {C0 : Ob C & IsoC (C := PSh) (yo_ob C0) F}.

  (** Corollary [cor:repr-prop] (statement only). *)
  Definition cor_repr_prop_stmt : Type := isUnivalent C -> forall F : Ob PSh, isProp (isRepr F).

End Yoneda.

(** Lemma [lem:adj-via-repr] (statement only): a map on objects [G] with
    natural isomorphisms [Hom_D(F -, D) ≅ yo(G(D))] extends uniquely to a
    right adjoint. *)
Definition lem_adj_via_repr_stmt `{Funext} : Type
  := forall (C D : WildPreCat) (pc : isPreCat C) (pd : isPreCat D) (F : Functor C D)
       (G0 : Ob D -> Ob C)
       (a : forall B (A : Ob C), homC (fob F A) B ≃ homC A (G0 B))
       (an : forall B A A' (h : homC (w := C) A' A) (f : homC (fob F A) B),
               fst (a B A') (f ∘c fmap F h) = fst (a B A) f ∘c h),
       isContr {adj : Adjunction C D &
                 {p : ladj adj = F & {q : fob (radj adj) = G0 &
                   forall A B, trp (fun G1 : Ob D -> Ob C => homC (fob F A) B ≃ homC A (G1 B))
                                   q (trp (fun F1 : Functor C D => homC (fob F1 A) B ≃ homC A (fob (radj adj) B))
                                          p (adjeqv adj A B))
                               = a B A}}}.

(** Corollary [cor:adj-unique] (statement only): for a functor defined
    on a category, the data of a right adjoint is a proposition. *)
Definition cor_adj_unique_stmt `{Funext} : Type
  := forall (C : Cat) (D : WildPreCat) (F : Functor (fst C) D),
       isProp {adj : Adjunction (fst C) D & ladj adj = F}.
