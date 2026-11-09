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
    - Corollaries [cor:yo-emb-obj] ([cor_yo_emb_obj]) and [cor:repr-prop]
      ([cor_repr_prop]), under univalence (so that [Set], and hence the
      presheaf category, is a category: [PSh_isUnivalent]).  A fully
      faithful functor between categories is injective on objects
      ([ff_isInj], via [ff_reflects_iso] and [ff_ap_isEquiv]), and
      [isRepr(F)] is equivalent to the fiber of [yo] over [F].

    - Lemma [lem:adj-via-repr] ([lem_adj_via_repr], from
      [adj_via_repr], which does not need [D] to be a precategory): the
      action on arrows is forced, [G(g) :≡ α(g ∘ α⁻¹(id))] ([avr_fm]),
      and the rest consists of identifications of arrows of [C].
    - Corollary [cor:adj-unique] ([cor_adj_unique]): for each [D] the
      pairs [(C₀, α)] with [α] natural form a proposition when [C] is a
      category ([AdjRep_isProp], via the isomorphism [β(α⁻¹(id))]), so
      the data of the adjunction ([AdjData]) form a proposition.

    Nothing in this section is left out. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Types.Unit Truncations.Core Spaces.Nat.Core.
From SymmetryBook Require Export Cats.S05_Adjunctions.

Local Open Scope uf_scope.

(** ** 6.6 The Yoneda Lemma *)

(** A fully faithful functor between categories is injective on
    objects (in the strong sense of [isInj]): [ap(F)] is the composite
    of [idtoiso], the action on isomorphisms and [idtoiso⁻¹]. *)
Section FFEmbedding.

  Context `{Funext} {C D : WildPreCat} (F : Functor C D) (ff : isFullyFaithful F).

  Definition ff_reflects_iso {A B : Ob C} (f : homC A B) (i : isIsoC (fmap F f)) : isIsoC f.
  Proof.
    destruct i as [[g s] [h r]].
    refine ((eqinv (ff B A) g; _); (eqinv (ff B A) h; _)).
    - refine ((eqinv_l (ff B B) _)^ @ ap (eqinv (ff B B)) _ @ eqinv_l (ff B B) (idC B)).
      exact (fcomp F _ _ @ ap (fun k => fmap F f ∘c k) (eqinv_r (ff B A) g) @ s @ (fid F B)^).
    - refine ((eqinv_l (ff A A) _)^ @ ap (eqinv (ff A A)) _ @ eqinv_l (ff A A) (idC A)).
      exact (fcomp F _ _ @ ap (fun k => k ∘c fmap F f) (eqinv_r (ff B A) h) @ r @ (fid F A)^).
  Defined.

  Definition fmap_iso {A B : Ob C} (e : IsoC A B) : IsoC (fob F A) (fob F B)
    := (fmap F (fst e); fmap_isIso F (snd e)).

  Definition fmap_iso_isEquiv (A B : Ob C) : isEquiv (@fmap_iso A B).
  Proof.
    refine (iso_to_isEquiv _ (fun e => (eqinv (ff A B) (fst e);
                                        ff_reflects_iso _ (trp isIsoC (eqinv_r (ff A B) (fst e))^
                                                            (snd e)))) _ _).
    - intro e. apply path_IsoC. exact (eqinv_l (ff A B) (fst e)).
    - intro e. apply path_IsoC. exact (eqinv_r (ff A B) (fst e)).
  Defined.

  Definition idtoiso_ap_fob {A B : Ob C} (p : A = B)
    : idtoiso (ap (fob F) p) = fmap_iso (idtoiso p).
  Proof. destruct p. apply path_IsoC. exact (fid F A)^. Defined.

  Definition ff_ap_isEquiv (uC : isUnivalent C) (uD : isUnivalent D) (A B : Ob C)
    : isEquiv (@ap _ _ (fob F) A B).
  Proof.
    refine (isEquiv_homotopic (eqinv (uD _ _) ∘ (fmap_iso ∘ idtoiso)) _ _
              (comp_isEquiv (comp_isEquiv (uC A B) (fmap_iso_isEquiv A B))
                 (eqinv_isEquiv (uD _ _)))).
    intro p. unfold comp.
    exact (ap (eqinv (uD _ _)) (idtoiso_ap_fob p)^ @ eqinv_l (uD _ _) _).
  Defined.

  Definition ff_isInj (uC : isUnivalent C) (uD : isUnivalent D) : isInj (fob F)
    := ap_isEquiv_isInj (ff_ap_isEquiv uC uD).

End FFEmbedding.

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

  (** Corollary [cor:yo-emb-obj] (proved below as [cor_yo_emb_obj]): for
      a category, [yo] is injective on objects. *)
  Definition cor_yo_emb_obj_stmt : Type := isUnivalent C -> isInj (fob yo).

  (** Definition [def:repr]. *)
  Definition isRepr (F : Ob PSh) : Type := {C0 : Ob C & IsoC (C := PSh) (yo_ob C0) F}.

  (** Corollary [cor:repr-prop]. *)
  Definition cor_repr_prop_stmt : Type := isUnivalent C -> forall F : Ob PSh, isProp (isRepr F).

  (** Both corollaries, given that [Set] is a category (which holds
      under univalence, see [cor_yo_emb_obj] and [cor_repr_prop] below). *)
  Definition PSh_isUnivalent (us : isUnivalent SetCat) : isUnivalent PSh
    := FunctorCat_isUnivalent (Op C) SetCat SetCat_isPreCat us.

  Definition yo_isInj (us : isUnivalent SetCat) : cor_yo_emb_obj_stmt
    := fun u => ff_isInj yo yo_ff u (PSh_isUnivalent us).

  Definition repr_isProp (us : isUnivalent SetCat) : cor_repr_prop_stmt.
  Proof.
    intros u F.
    refine (isProp_Eqv (_ ; tot_isEquiv
              (fun C0 (p : F = yo_ob C0) => idtoiso (C := PSh) p⁻¹)
              (fun C0 => comp_isEquiv (snd symm_eqv) (PSh_isUnivalent us _ _)))
              (yo_isInj us u F)).
  Defined.

End Yoneda.

Definition cor_yo_emb_obj `{Univalence} (C : WildPreCat) (pc : isPreCat C)
  : cor_yo_emb_obj_stmt C pc
  := yo_isInj C pc (snd SetCat_isCat).

Definition cor_repr_prop `{Univalence} (C : WildPreCat) (pc : isPreCat C)
  : cor_repr_prop_stmt C pc
  := repr_isProp C pc (snd SetCat_isCat).

(** Lemma [lem:adj-via-repr] (proved below as [lem_adj_via_repr]): a map on objects [G] with
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

(** Corollary [cor:adj-unique] (proved below): for a functor defined
    on a category, the data of a right adjoint is a proposition. *)
Definition cor_adj_unique_stmt `{Funext} : Type
  := forall (C : Cat) (D : WildPreCat) (F : Functor (fst C) D),
       isProp {adj : Adjunction (fst C) D & ladj adj = F}.

(** The proof of lemma [lem:adj-via-repr] ([adj_via_repr]): the action
    of the right adjoint on arrows must be [G(g) :≡ α(g ∘ ε)] with
    [ε :≡ α⁻¹(id)] ([avr_fm]), by naturality in [D] at [(G(D), ε)]; it
    is a functor and [α] is natural in [D] since [α] is natural in [C]
    ([avr_counit], [avr_natB]).  All remaining data are identifications
    of arrows of [C], hence propositions.  Neither the statement nor
    the proof needs [D] to be a precategory. *)
Section AdjViaRepr.

  Context `{Funext} (C D : WildPreCat) (pc : isPreCat C) (F : Functor C D)
    (G0 : Ob D -> Ob C) (a : forall B (A : Ob C), homC (fob F A) B ≃ homC A (G0 B))
    (an : forall B A A' (h : homC (w := C) A' A) (f : homC (fob F A) B),
            fst (a B A') (f ∘c fmap F h) = fst (a B A) f ∘c h).

  Local Notation e B A := (fst (a B A)).
  Local Notation einv B A := (eqinv (snd (a B A))).

  Definition avr_eps (B : Ob D) : homC (fob F (G0 B)) B := einv B (G0 B) (idC (G0 B)).

  Definition avr_fm (B B' : Ob D) (g : homC B B') : homC (G0 B) (G0 B')
    := e B' (G0 B) (g ∘c avr_eps B).

  Definition avr_counit {A : Ob C} {B : Ob D} (f : homC (fob F A) B)
    : avr_eps B ∘c fmap F (e B A f) = f.
  Proof.
    refine ((eqinv_l (snd (a B A)) _)^ @ ap (einv B A) _ @ eqinv_l (snd (a B A)) f).
    refine (an B (G0 B) A (e B A f) (avr_eps B) @ _).
    exact (ap (fun k => k ∘c e B A f) (eqinv_r (snd (a B (G0 B))) (idC (G0 B))) @ lamC _).
  Defined.

  Definition avr_natB {A : Ob C} {B B' : Ob D} (f : homC (fob F A) B) (g : homC B B')
    : e B' A (g ∘c f) = avr_fm B B' g ∘c e B A f.
  Proof.
    refine (ap (fun k => e B' A (g ∘c k)) (avr_counit f)^ @ _).
    refine (ap (e B' A) (alphaC (fmap F (e B A f)) (avr_eps B) g) @ _).
    exact (an B' (G0 B) A (e B A f) (g ∘c avr_eps B)).
  Defined.

  Definition avr_fid (B : Ob D) : avr_fm B B (idC B) = idC (G0 B)
    := ap (e B (G0 B)) (lamC _) @ eqinv_r (snd (a B (G0 B))) (idC (G0 B)).

  Definition avr_fcomp (B B' B'' : Ob D) (g : homC B B') (g' : homC B' B'')
    : avr_fm B B'' (g' ∘c g) = avr_fm B' B'' g' ∘c avr_fm B B' g
    := ap (e B'' (G0 B)) (alphaC (avr_eps B) g g')^ @ avr_natB (g ∘c avr_eps B) g'.

  Definition avr_G : Functor D C := Build_Functor D C G0 avr_fm avr_fid avr_fcomp.

  Definition avr_nat (A' A : Ob C) (B B' : Ob D) (h : homC A' A) (f : homC (fob F A) B)
    (g : homC B B')
    : e B' A' (g ∘c (f ∘c fmap F h)) = avr_fm B B' g ∘c (e B A f ∘c h).
  Proof.
    refine (ap (e B' A') (alphaC (fmap F h) f g) @ _).
    refine (an B' A A' h (g ∘c f) @ _).
    refine (ap (fun k => k ∘c h) (avr_natB f g) @ _).
    exact (alphaC h (e B A f) (avr_fm B B' g))^.
  Defined.

  Definition avr_adj : Adjunction C D
    := Build_Adjunction C D F avr_G (fun A B => a B A) avr_nat.

  Definition AdjExt : Type
    := {adj : Adjunction C D &
         {p : ladj adj = F & {q : fob (radj adj) = G0 &
           forall A B, trp (fun G1 : Ob D -> Ob C => homC (fob F A) B ≃ homC A (G1 B))
                           q (trp (fun F1 : Functor C D => homC (fob F1 A) B ≃ homC A (fob (radj adj) B))
                                  p (adjeqv adj A B))
                       = a B A}}}.

End AdjViaRepr.

Definition adj_via_repr `{Funext} (C D : WildPreCat) (pc : isPreCat C) (F : Functor C D)
  (G0 : Ob D -> Ob C) (a : forall B (A : Ob C), homC (fob F A) B ≃ homC A (G0 B))
  (an : forall B A A' (h : homC (w := C) A' A) (f : homC (fob F A) B),
          fst (a B A') (f ∘c fmap F h) = fst (a B A) f ∘c h)
  : isContr (AdjExt C D F G0 a).
Proof.
  refine ((avr_adj C D F G0 a an; (refl; (refl; fun A B => refl))); _).
  intros [adj [p [q r]]]. destruct adj as [F' G' e' n']. cbn in p, q, r. destruct p.
  rename F' into F.
  destruct G' as [go gm gi gc]. cbn in q, r. destruct q. cbn in r.
  rename go into G0.
  assert (Er : (fun A B => a B A) = e')
    by exact (ptw_inv (fun A => ptw_inv (fun B => (r A B)^))).
  destruct Er.
  assert (Em : avr_fm C D F G0 a = gm).
  { apply ptw_inv; intro B. apply ptw_inv; intro B'. apply ptw_inv; intro g.
    refine (ap (fun k => fst (a B' (G0 B)) (g ∘c k))
              (ap (fun k => avr_eps C D F G0 a B ∘c k) (fid F (G0 B))
               @ rhoC (avr_eps C D F G0 a B))^ @ _).
    refine (n' (G0 B) (G0 B) B B' (idC (G0 B)) (avr_eps C D F G0 a B) g @ _).
    refine (ap (fun k => gm B B' g ∘c (k ∘c idC (G0 B))) (eqinv_r (snd (a B (G0 B))) _) @ _).
    exact (ap (fun k => gm B B' g ∘c k) (lamC _) @ rhoC _). }
  destruct Em.
  destruct (ptw_inv (fun B => pc _ _ _ _ (avr_fid C D F G0 a B) (gi B)) : avr_fid C D F G0 a = gi).
  destruct (ptw_inv (fun B => ptw_inv (fun B' => ptw_inv (fun B'' => ptw_inv (fun g =>
              ptw_inv (fun g' => pc _ _ _ _ (avr_fcomp C D F G0 a an B B' B'' g g')
                                   (gc B B' B'' g g'))))))
            : avr_fcomp C D F G0 a an = gc).
  destruct (ptw_inv (fun A' => ptw_inv (fun A => ptw_inv (fun B => ptw_inv (fun B' =>
              ptw_inv (fun h => ptw_inv (fun f => ptw_inv (fun g =>
                pc _ _ _ _ (avr_nat C D F G0 a an A' A B B' h f g) (n' A' A B B' h f g))))))))
            : avr_nat C D F G0 a an = n').
  destruct (ptw_inv (fun A => ptw_inv (fun B => Eqv_sets_isSet (pc A (G0 B)) _ _ refl (r A B)))
            : (fun A B => refl) = r).
  exact refl.
Defined.

Definition lem_adj_via_repr `{Funext} : lem_adj_via_repr_stmt
  := fun C D pc pd F G0 a an => adj_via_repr C D pc F G0 a an.

(** Corollary [cor:adj-unique].  For each [B], the pairs of an object
    [C₀] with a natural family [Hom_D(F -, B) ≃ Hom_C(-, C₀)] form a
    proposition when [C] is a category: two of them differ by the
    isomorphism [k :≡ β(α⁻¹(id))] ([adjrep_k], [AdjRep_isProp]). *)
Definition AdjRep {C D : WildPreCat} (F : Functor C D) (B : Ob D) : Type
  := {C0 : Ob C & {a : forall A, homC (fob F A) B ≃ homC A C0 &
       forall A A' (h : homC (w := C) A' A) (f : homC (fob F A) B),
         fst (a A') (f ∘c fmap F h) = fst (a A) f ∘c h}}.

Definition adjrep_path `{Funext} {C D : WildPreCat} (pc : isPreCat C) (F : Functor C D)
  (B : Ob D) {C0 C1 : Ob C} (P : C0 = C1) (a : forall A, homC (fob F A) B ≃ homC A C0) an
  (b : forall A, homC (fob F A) B ≃ homC A C1) bn
  (E : forall A f, fst (b A) f = fst (idtoiso P) ∘c fst (a A) f)
  : ((C0; (a; an)) : AdjRep F B) = (C1; (b; bn)).
Proof.
  destruct P.
  assert (Ea : a = b).
  { apply ptw_inv; intro A. apply path_Eqv. apply ptw_inv; intro f. exact ((lamC _)^ @ (E A f)^). }
  destruct Ea.
  destruct (ptw_inv (fun A => ptw_inv (fun A' => ptw_inv (fun h => ptw_inv (fun f =>
              pc _ _ _ _ (an A A' h f) (bn A A' h f))))) : an = bn).
  exact refl.
Defined.

Definition adjrep_counit {C D : WildPreCat} (F : Functor C D) (B : Ob D) (r : AdjRep F B)
  {A : Ob C} (f : homC (fob F A) B)
  : eqinv (snd (fst (snd r) (fst r))) (idC (fst r)) ∘c fmap F (fst (fst (snd r) A) f) = f.
Proof.
  destruct r as [C0 [a an]]. cbn.
  refine ((eqinv_l (snd (a A)) _)^ @ ap (eqinv (snd (a A))) _ @ eqinv_l (snd (a A)) f).
  refine (an C0 A (fst (a A) f) _ @ _).
  exact (ap (fun k => k ∘c fst (a A) f) (eqinv_r (snd (a C0)) (idC C0)) @ lamC _).
Defined.

(** For representations [(C₀, α)] and [(C₁, β)]: [β(f) = k ∘ α(f)]. *)
Definition adjrep_k {C D : WildPreCat} (F : Functor C D) (B : Ob D) (r r' : AdjRep F B)
  : homC (fst r) (fst r')
  := fst (fst (snd r') (fst r)) (eqinv (snd (fst (snd r) (fst r))) (idC (fst r))).

Definition adjrep_k_spec {C D : WildPreCat} (F : Functor C D) (B : Ob D) (r r' : AdjRep F B)
  {A : Ob C} (f : homC (fob F A) B)
  : fst (fst (snd r') A) f = adjrep_k F B r r' ∘c fst (fst (snd r) A) f
  := ap (fst (fst (snd r') A)) (adjrep_counit F B r f)^ @ snd (snd r') _ _ _ _.

Definition AdjRep_isProp `{Funext} (C : Cat) {D : WildPreCat} (F : Functor (fst C) D) (B : Ob D)
  : isProp (AdjRep F B).
Proof.
  intros r r'.
  pose (k := adjrep_k F B r r'). pose (k' := adjrep_k F B r' r).
  assert (kk : forall A (f : homC (fob F A) B),
             fst (fst (snd r) A) f = (k' ∘c k) ∘c fst (fst (snd r) A) f).
  { intros A f. refine (adjrep_k_spec F B r' r f @ _).
    exact (ap (fun u => k' ∘c u) (adjrep_k_spec F B r r' f) @ alphaC _ _ _). }
  assert (kk' : forall A (f : homC (fob F A) B),
             fst (fst (snd r') A) f = (k ∘c k') ∘c fst (fst (snd r') A) f).
  { intros A f. refine (adjrep_k_spec F B r r' f @ _).
    exact (ap (fun u => k ∘c u) (adjrep_k_spec F B r' r f) @ alphaC _ _ _). }
  pose (ε := fun r0 : AdjRep F B => eqinv (snd (fst (snd r0) (fst r0))) (idC (fst r0))).
  assert (e1 : k ∘c k' = idC (fst r')).
  { refine ((rhoC _)^ @ ap (fun u => (k ∘c k') ∘c u) (eqinv_r (snd (fst (snd r') (fst r'))) _)^
            @ (kk' _ (ε r'))^ @ eqinv_r (snd (fst (snd r') (fst r'))) _). }
  assert (e2 : k' ∘c k = idC (fst r)).
  { refine ((rhoC _)^ @ ap (fun u => (k' ∘c k) ∘c u) (eqinv_r (snd (fst (snd r) (fst r))) _)^
            @ (kk _ (ε r))^ @ eqinv_r (snd (fst (snd r) (fst r))) _). }
  pose (K := (k; ((k'; e1); (k'; e2))) : IsoC (fst r) (fst r')).
  pose (P := eqinv (snd (snd C) (fst r) (fst r')) K).
  destruct r as [C0 [a an]], r' as [C1 [b bn]].
  refine (adjrep_path (fst (snd C)) F B P a an b bn _).
  intros A f.
  refine (adjrep_k_spec F B (C0; (a; an)) (C1; (b; bn)) f @ _).
  exact (ap (fun u : IsoC C0 C1 => fst u ∘c fst (a A) f) (eqinv_r (snd (snd C) C0 C1) K)^).
Defined.

(** The data of an adjunction [F ⊣ G] are representations for all [D]
    together with an extension as in [lem:adj-via-repr]. *)
Definition AdjData `{Funext} {C D : WildPreCat} (F : Functor C D) : Type
  := {t : forall B, AdjRep F B &
       AdjExt C D F (fun B => fst (t B)) (fun B A => fst (snd (t B)) A)}.

Definition AdjData_isProp `{Funext} (C : Cat) {D : WildPreCat} (F : Functor (fst C) D)
  : isProp (AdjData F)
  := Sigma_isProp (Pi_isProp (fun B => AdjRep_isProp C F B))
       (fun t => isContr_isProp' (adj_via_repr (fst C) D (fst (snd C)) F _ _
                                    (fun B => snd (snd (t B))))).

Definition adj_to_data `{Funext} {C D : WildPreCat} (adj : Adjunction C D) : AdjData (ladj adj)
  := ((fun B => (fob (radj adj) B; ((fun A => adjeqv adj A B);
                                     fun A A' h f => adjnat_pre adj h f)));
      (adj; (refl; (refl; fun A B => refl)))).

Definition data_to_adj `{Funext} {C D : WildPreCat} {F : Functor C D} (s : AdjData F)
  : {adj : Adjunction C D & ladj adj = F}
  := (fst (snd s); fst (snd (snd s))).

Definition data_to_adj_trp `{Funext} {C D : WildPreCat} (adj : Adjunction C D) {F : Functor C D}
  (p : ladj adj = F)
  : data_to_adj (trp AdjData p (adj_to_data adj)) = (adj; p).
Proof. destruct p. exact refl. Defined.

Definition cor_adj_unique `{Funext} : cor_adj_unique_stmt.
Proof.
  intros C D F [adj p] [adj' p'].
  exact ((data_to_adj_trp adj p)^ @ ap data_to_adj (AdjData_isProp C F _ _)
         @ data_to_adj_trp adj' p').
Defined.
