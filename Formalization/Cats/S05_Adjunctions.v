(** * Section 6.5 Adjunctions

    Part of Chapter 6 ([cats.tex]); see [Cats.v] for an overview of the
    chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:adjunction]: the record [Adjunction], with [α]
      ([adjeqv]) natural in both arguments at once ([adjnat]); the unit
      and counit [eq:adj-unit-counit] ([adj_unit], [adj_counit]),
      naturality of the unit ([adj_unit_nat]), and exercise
      [xca:adj-triangles] ([adj_triangle_l], [adj_triangle_r]).
    - Example [ex:trunc-adj] ([TruncAdj], with the inclusion [InclFun]).
    - Example [ex:pt-unpt-adj] ([PlusAdj]).  NOTE for the book text: it
      reads "For [A : U_*] and [X : U]"; it should be [A : U] and
      [X : U_*].
    - Example [ex:Sigma-Pi-adj] for families of types: [f_! ⊣ f^*]
      ([SigPullAdj]) and [f^* ⊣ f_*] ([PullPiAdj]), and the special case
      [Σ_A ⊣ cst ⊣ Π_A] ([SigConstAdj], [ConstPiAdj]).
    - Remark [rem:adj-in-posets]: an adjunction between preorders gives
      the biimplication and conversely ([adj_preorder_iff],
      [preorder_iff_adj]); the propositional analog
      [∃_f ⊣ f^* ⊣ ∀_f] on subsets ([exists_pull_adj], [pull_forall_adj]).

    Left out (statements only, no proofs yet)
    - Exercise [xca:adj-from-triangles] ([xca_adj_from_triangles_stmt]).
    - The set-level [f_! ⊣ f^* ⊣ f_*] of example [ex:Sigma-Pi-adj]
      ([SigmaPi_Set_stmt]).

    Left out (not formalized)
    - The example [⌈-⌉ ⊣ ι ⊣ ⌊-⌋] for [ι : ℤ → ℚ] in remark
      [rem:adj-in-posets]: the formalization has no rationals. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Types.Unit Truncations.Core Spaces.Nat.Core.
From SymmetryBook Require Export Cats.S04_Functors.

Local Open Scope uf_scope.

(** ** 6.5 Adjunctions *)

(** Definition [def:adjunction]: functors [F : C → D], [G : D → C] and
    a family of equivalences [α : Hom_D(F A, B) ≃ Hom_C(A, G B)], natural
    in [A] and [B] at once:
    [α(g ∘ f ∘ F h) = G g ∘ α(f) ∘ h]. *)
Record Adjunction (C D : WildPreCat) : Type := {
  ladj : Functor C D;
  radj : Functor D C;
  adjeqv : forall A B, homC (fob ladj A) B ≃ homC A (fob radj B);
  adjnat : forall A' A B B' (h : homC A' A) (f : homC (fob ladj A) B) (g : homC B B'),
      fst (adjeqv A' B') (g ∘c (f ∘c fmap ladj h)) = fmap radj g ∘c (fst (adjeqv A B) f ∘c h)
}.

Arguments ladj {C D} _.
Arguments radj {C D} _.
Arguments adjeqv {C D} _ _ _.
Arguments adjnat {C D} _ {A' A B B'} _ _ _.

Section UnitCounit.

  Context {C D : WildPreCat} (adj : Adjunction C D).

  Local Notation F := (ladj adj).
  Local Notation G := (radj adj).
  Local Notation α A B := (fst (adjeqv adj A B)).
  Local Notation αinv A B := (eqinv (snd (adjeqv adj A B))).

  (** The unit [η] and counit [ε] ([eq:adj-unit-counit]). *)
  Definition adj_unit (A : Ob C) : homC A (fob G (fob F A)) := α A (fob F A) (idC (fob F A)).

  Definition adj_counit (B : Ob D) : homC (fob F (fob G B)) B := αinv (fob G B) B (idC (fob G B)).

  (** Two special cases of naturality. *)
  Definition adjnat_pre {A' A : Ob C} {B : Ob D} (h : homC A' A) (f : homC (fob F A) B)
    : α A' B (f ∘c fmap F h) = α A B f ∘c h.
  Proof.
    refine ((ap (α A' B) (lamC _))^ @ adjnat adj h f (idC B) @ _).
    exact (ap (fun k => k ∘c (α A B f ∘c h)) (fid G B) @ lamC _).
  Defined.

  Definition adjnat_post {A : Ob C} {B B' : Ob D} (f : homC (fob F A) B) (g : homC B B')
    : α A B' (g ∘c f) = fmap G g ∘c α A B f.
  Proof.
    refine (ap (fun k => α A B' (g ∘c k)) (ap (fun k => f ∘c k) (fid F A) @ rhoC f)^ @ _).
    exact (adjnat adj (idC A) f g @ ap (fun k => fmap G g ∘c k) (rhoC _)).
  Defined.

  (** Naturality of the unit. *)
  Definition adj_unit_nat {A B : Ob C} (f : homC A B)
    : fmap G (fmap F f) ∘c adj_unit A = adj_unit B ∘c f.
  Proof.
    refine ((adjnat_post (idC (fob F A)) (fmap F f))^ @ _).
    refine (ap (α A (fob F B)) (rhoC _ @ (lamC _)^) @ _).
    exact (adjnat_pre f (idC (fob F B))).
  Defined.

  (** Exercise [xca:adj-triangles]: the triangle laws. *)
  Definition adj_triangle_l (A : Ob C)
    : adj_counit (fob F A) ∘c fmap F (adj_unit A) = idC (fob F A).
  Proof.
    apply (Eqv_inj (adjeqv adj A (fob F A))).
    refine (adjnat_pre (adj_unit A) (adj_counit (fob F A)) @ _).
    exact (ap (fun k => k ∘c adj_unit A) (eqinv_r (snd (adjeqv adj _ _)) _) @ lamC _).
  Defined.

  Definition adj_triangle_r (B : Ob D)
    : fmap G (adj_counit B) ∘c adj_unit (fob G B) = idC (fob G B).
  Proof.
    refine ((adjnat_post (idC _) (adj_counit B))^ @ _).
    exact (ap (α (fob G B) B) (rhoC _) @ eqinv_r (snd (adjeqv adj _ _)) _).
  Defined.

End UnitCounit.

(** Exercise [xca:adj-from-triangles] (statement only): functors with a
    unit and counit satisfying the triangle laws give an adjunction, with
    [α(f) :≡ G(f) ∘ η]. *)
Definition xca_adj_from_triangles_stmt : Type
  := forall (C D : WildPreCat) (F : Functor C D) (G : Functor D C)
       (η : NatTrans (idF C) (compF G F)) (ε : NatTrans (compF F G) (idF D)),
       (forall A, fst ε (fob F A) ∘c fmap F (fst η A) = idC (fob F A)) ->
       (forall B, fmap G (fst ε B) ∘c fst η (fob G B) = idC (fob G B)) ->
       {adj : Adjunction C D & (ladj adj = F) × (radj adj = G)}.

(** Example [ex:trunc-adj]: [‖-‖_n ⊣ ι_n], with the unit [|-|_n]. *)
Definition InclFun (C : WildPreCat) (P : Ob C -> PropU) : Functor (FullSub C P) C
  := Build_Functor (FullSub C P) C (fun A => fst A) (fun A B f => f)
       (fun A => refl) (fun A B E f g => refl).

Definition trunc_adj_eqv `{Funext} (n : trunc_index) (A : Type) (B : Type) (tB : IsTrunc n B)
  : (Trunc n A -> B) ≃ (A -> B).
Proof.
  refine (mkEqv (fun k : Trunc n A -> B => fun a => k (tr a)) (fun g => Trunc_rec g) _ _).
  - intro k. apply ptw_inv. refine (Trunc_ind _ _). intro a. exact refl.
  - intro g. exact refl.
Defined.

Definition TruncAdj `{Funext} (n : trunc_index) : Adjunction TypeCat (FullSub TypeCat (isTruncU n))
  := Build_Adjunction TypeCat (FullSub TypeCat (isTruncU n)) (TruncFun n) (InclFun TypeCat (isTruncU n))
       (fun A B => trunc_adj_eqv n A (fst B) (snd B))
       (fun A' A B B' h f g => refl).

(** Example [ex:pt-unpt-adj]: [(-)_+ ⊣ (-)_÷], with [α] given by
    precomposition with [inl].  NOTE for the book text: the example reads
    "For [A : U_*] and [X : U]"; it should be [A : U] and [X : U_*]. *)
Definition plus_rec {A : Type} {X : Ustar} (k : A -> utype X) : plusPtd A →* X
  := ((fun x => match x with inl a => k a | inr _ => pt X end); refl).

Definition plus_adj_eqv `{Funext} (A : Type) (X : Ustar) : (plusPtd A →* X) ≃ (A -> utype X).
Proof.
  refine (mkEqv (fun f : plusPtd A →* X => fun a => fst f (inl a)) plus_rec _ _).
  - intros [f fp].
    refine (path_pmap_refl (X := plusPtd A) (Y := X) (fst (plus_rec (X := X) (fun a => f (inl a)))) f refl fp
              (fun x : A ⨿ True => match x with inl a => refl | inr t => match t with triv => fp end end) _).
    exact (trans_1p fp).
  - intro k. exact refl.
Defined.

Definition PlusAdj `{Funext} : Adjunction TypeCat PtdCat
  := Build_Adjunction TypeCat PtdCat PlusFun ForgetFun plus_adj_eqv
       (fun A' A B B' h f g => refl).

(** Example [ex:Sigma-Pi-adj], for families of types: [f_! ⊣ f^* ⊣ f_*]
    along [f : A → B]. *)
Section SigmaPi.

  Context `{Funext} {A B : Type} (f : A -> B).

  Definition PullFun : Functor (FamCat B) (FamCat A)
    := Build_Functor (FamCat B) (FamCat A) (fun Y a => Y (f a)) (fun Y Y' g a => g (f a))
         (fun Y => refl) (fun Y Y' Y'' g g' => refl).

  Definition SigFam (X : A -> Type) (b : B) : Type := {a : A & (f a = b) × X a}.

  Definition SigFun : Functor (FamCat A) (FamCat B)
    := Build_Functor (FamCat A) (FamCat B) SigFam
         (fun X X' g b w => (fst w; (fst (snd w); g (fst w) (snd (snd w)))))
         (fun X => refl) (fun X X' X'' g g' => refl).

  Definition PiFam (X : A -> Type) (b : B) : Type := forall a, f a = b -> X a.

  Definition PiFun : Functor (FamCat A) (FamCat B)
    := Build_Functor (FamCat A) (FamCat B) PiFam
         (fun X X' g b u a p => g a (u a p))
         (fun X => refl) (fun X X' X'' g g' => refl).

  Definition sig_pull_eqv (X : A -> Type) (Y : B -> Type)
    : (forall b, SigFam X b -> Y b) ≃ (forall a, X a -> Y (f a)).
  Proof.
    refine (mkEqv (fun (k : forall b, SigFam X b -> Y b) a (x : X a) => k (f a) (a; (refl; x)))
                  (fun (l : forall a, X a -> Y (f a)) b (w : SigFam X b) => match fst (snd w) as p in (_ = b') return Y b' with
                                | refl => l (fst w) (snd (snd w)) end) _ _).
    - intro k. apply ptw_inv. intro b. apply ptw_inv. intros [a [p x]]. destruct p. exact refl.
    - intro l. exact refl.
  Defined.

  Definition SigPullAdj : Adjunction (FamCat A) (FamCat B)
    := Build_Adjunction (FamCat A) (FamCat B) SigFun PullFun sig_pull_eqv
         (fun X' X Y Y' h k g => refl).

  Definition pull_pi_eqv (Y : B -> Type) (X : A -> Type)
    : (forall a, Y (f a) -> X a) ≃ (forall b, Y b -> PiFam X b).
  Proof.
    refine (mkEqv (fun (k : forall a, Y (f a) -> X a) b (y : Y b) a (p : f a = b) => k a (match p in (_ = b') return Y b' -> Y (f a) with
                                         | refl => fun y' => y' end y))
                  (fun (l : forall b, Y b -> PiFam X b) a (y : Y (f a)) => l (f a) y a refl) _ _).
    - intro k. exact refl.
    - intro l. apply ptw_inv. intro b. apply ptw_inv. intro y. apply ptw_inv. intro a.
      apply ptw_inv. intro p. destruct p. exact refl.
  Defined.

  Definition PullPiAdj : Adjunction (FamCat B) (FamCat A).
  Proof.
    refine (Build_Adjunction (FamCat B) (FamCat A) PullFun PiFun pull_pi_eqv _).
    intros Y' Y X X' h k g. apply ptw_inv. intro b. apply ptw_inv. intro y.
    apply ptw_inv. intro a. apply ptw_inv. intro p. destruct p. exact refl.
  Defined.

End SigmaPi.

(** The special case of [A → 𝟙]: [Σ_A ⊣ cst ⊣ Π_A], up to the
    equivalences [Σ_a (triv = triv) × X(a) ≃ Σ_a X(a)] and similarly for
    [Π]. *)
Definition SigConstAdj `{Funext} (A : Type) : Adjunction (FamCat A) (FamCat True)
  := SigPullAdj (fun _ : A => triv).

Definition ConstPiAdj `{Funext} (A : Type) : Adjunction (FamCat True) (FamCat A)
  := PullPiAdj (fun _ : A => triv).

(** The set-level version [f_! ⊣ f^* ⊣ f_*] on families of sets, with
    [f_!] set-truncated (statement only). *)
Definition isSetFam `{Funext} (A : Type) (X : Ob (FamCat A)) : PropU
  := ((forall a, isSet (X a)); Pi_isProp (fun a => isSet_isProp _)).

Definition SetFam `{Funext} (A : Type) : WildPreCat := FullSub (FamCat A) (isSetFam A).

Definition SigmaPi_Set_stmt `{Funext} : Type
  := forall (A B : Type) (f : A -> B),
       {adj : Adjunction (SetFam A) (SetFam B) &
         (forall X b, fst (fob (ladj adj) X) b = strunc (SigFam f (fst X) b))
         × (forall Y a, fst (fob (radj adj) Y) a = fst Y (f a))}
       × {adj : Adjunction (SetFam B) (SetFam A) &
           (forall Y a, fst (fob (ladj adj) Y) a = fst Y (f a))
           × (forall X b, fst (fob (radj adj) X) b = PiFam f (fst X) b)}.

(** Remark [rem:adj-in-posets]: for preorders, an adjunction amounts to
    [F(p) ≤ q ↔ p ≤ G(q)]; the propositional analog [∃_f ⊣ f^* ⊣ ∀_f]
    on subsets. *)
Definition adj_preorder_iff {P Q : WildPreCat} (adj : Adjunction P Q) (p : Ob P) (q : Ob Q)
  : homC (fob (ladj adj) p) q <-> homC p (fob (radj adj) q)
  := (fst (adjeqv adj p q), eqinv (snd (adjeqv adj p q))).

Definition preorder_iff_adj {P Q : WildPreCat} (hP : isPreorder P) (hQ : isPreorder Q)
  (F : Functor P Q) (G : Functor Q P)
  (e : forall p q, homC (fob F p) q <-> homC p (fob G q))
  : Adjunction P Q
  := Build_Adjunction P Q F G
       (fun p q => Eqv_of_props (hQ _ _) (hP _ _) (Overture.fst (e p q)) (Overture.snd (e p q)))
       (fun p' p q q' h f g => hP _ _ _ _).

Section SubAdj.

  Context {A B : Type} (f : A -> B).

  Definition sub_pull (Q : Sub B) : Sub A := fun a => Q (f a).

  Definition sub_exists (P : Sub A) : Sub B
    := fun b => (Ex (fun a => (b = f a) × fst (P a)); ptrunc_isProp).

  Definition sub_forall `{Funext} (P : Sub A) : Sub B
    := fun b => ((forall a, b = f a -> fst (P a)); Pi_isProp (fun a => fun_isProp (snd (P a)))).

  Definition exists_pull_adj (P : Sub A) (Q : Sub B)
    : (sub_exists P ⊆ Q) <-> (P ⊆ sub_pull Q).
  Proof.
    split.
    - intros h a x. exact (h (f a) (trunc (a; (refl; x)))).
    - intros h b. refine (ptrunc_rec (snd (Q b)) _). intros [a [p x]].
      exact (trp (fun b' => fst (Q b')) p^ (h a x)).
  Defined.

  Definition pull_forall_adj `{Funext} (Q : Sub B) (P : Sub A)
    : (sub_pull Q ⊆ P) <-> (Q ⊆ sub_forall P).
  Proof.
    split.
    - intros h b y a p. exact (h a (trp (fun b' => fst (Q b')) p y)).
    - intros h a y. exact (h (f a) y a refl).
  Defined.

End SubAdj.
