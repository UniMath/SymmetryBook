(** * Section 7.7 Heaps

    Part of Chapter 7 ([absgroup.tex]); see [AbsGroup.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definitions [def:bipt-conn-groupoid] ([UUconnGrpd], [UUppone]) and
      [def:heap] ([Heap :≡ Copy(UUppone)], [mkheap], [BH], start and end
      shapes [hstart], [hend], and [USymH :≡ (hstart = hend)]).
    - Exercise [xca:group+torsor-heap]: [heap_l], [heap_r : Heap ≃
      ∑_{G:Group} BG] and [heap_c : Group ≃ ∑_{H:Heap} USym(H)]; hence
      [Heap_isGrpd].
    - The symmetry groups of the endpoints are merely equal
      ([heap_groups_merely_eq]).

    - The heap operation [heap_op], abelian heaps ([isAbHeap]) and the
      structure map [heap_struct].

    Left out (statements only, no proofs yet; time limit per result)
    - The group of symmetries [r ↦ p q⁻¹ r] of [USym(H)]
      ([heap_maps_stmt]), the isomorphism of the endpoint groups of an
      abelian heap ([abheap_iso_stmt]), and exercise [xca:heap-variety]
      (heaps as a variety with a ternary operation;
      [xca_heap_variety_stmt]).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core.
From SymmetryBook Require Export AbsGroup.S06_Actions.

Local Open Scope uf_scope.

(** ** 7.7 Heaps *)

(** Definition [def:bipt-conn-groupoid]: [UU^{=1}] is the type of
    connected groupoids, and [UU_{**}^{=1} :≡ ∑_{A:UU^{=1}} A × A]. *)
Definition UUconnGrpd : Type := {A : Type & isConn A × isGrpd A}.

Definition UUppone : Type := {A : UUconnGrpd & fst A × fst A}.

(** Definition [def:heap]. *)
Definition Heap : Type := Copy UUppone.

Definition mkheap (X : UUppone) : Heap := inc X.

Definition BH (H : Heap) : UUppone := out H.

Definition hstart (H : Heap) : fst (fst (BH H)) := fst (snd (BH H)).

Definition hend (H : Heap) : fst (fst (BH H)) := snd (snd (BH H)).

(** The underlying identifications [ISym(A, a, a') :≡ (a = a')]. *)
Definition USymH (H : Heap) : Type := hstart H = hend H.

Definition USymH_isSet (H : Heap) : isSet (USymH H)
  := snd (snd (fst (BH H))) _ _.

(** Exercise [xca:group+torsor-heap]: two equivalences
    [l, r : Heap ≃ ∑_{G:Group} BG] (designating the start, resp. the end
    shape) and [c : Group ≃ ∑_{H:Heap} USym(H)]. *)
Definition heap_l : Heap ≃ {G : Group & utype (BG G)}.
Proof.
  refine (mkEqv
    (fun H => (mkgroup (fst (fst (BH H)); (hstart H; (fst (snd (fst (BH H)));
                                                      snd (snd (fst (BH H)))))); hend H)
              : {G : Group & utype (BG G)})
    (fun w => mkheap ((fst (B (fst w)); (BG_isConn (fst w); BG_isGrpd (fst w)));
                      (sh (fst w); snd w)))
    _ _).
  - intros [X]. exact refl.
  - intros [[X] z]. exact refl.
Defined.

Definition heap_r : Heap ≃ {G : Group & utype (BG G)}.
Proof.
  refine (mkEqv
    (fun H => (mkgroup (fst (fst (BH H)); (hend H; (fst (snd (fst (BH H)));
                                                    snd (snd (fst (BH H)))))); hstart H)
              : {G : Group & utype (BG G)})
    (fun w => mkheap ((fst (B (fst w)); (BG_isConn (fst w); BG_isGrpd (fst w)));
                      (snd w; sh (fst w))))
    _ _).
  - intros [X]. exact refl.
  - intros [[X] z]. exact refl.
Defined.

Definition heap_c : Group ≃ {H : Heap & USymH H}.
Proof.
  refine (mkEqv
    (fun G => (mkheap ((fst (B G); (BG_isConn G; BG_isGrpd G)); (sh G; sh G)); refl)
              : {H : Heap & USymH H})
    (fun w => mkgroup (fst (fst (BH (fst w))); (hstart (fst w);
                         (fst (snd (fst (BH (fst w)))); snd (snd (fst (BH (fst w))))))))
    _ _).
  - intros [X]. exact refl.
  - intros [[[A [a a']]] p]. revert p. unfold USymH, hstart, hend, BH. cbn.
    intro p. destruct p. exact refl.
Defined.

(** It follows that the type of heaps is a groupoid. *)
Definition Heap_isGrpd `{Univalence} : isGrpd Heap
  := is_ntype_Eqv 1 (Eqv_inv heap_l)
       (Sigma_isGrpd Group_isGrpd (fun G => BG_isGrpd G)).

(** The two endpoint groups of a heap. *)
Definition heap_start_group (H : Heap) : Group := fst (fst heap_l H).

Definition heap_end_group (H : Heap) : Group := fst (fst heap_r H).

(** The symmetry groups of the two endpoints are merely isomorphic (in
    fact merely equal): the classifying type is connected. *)
Definition heap_groups_merely_eq `{Univalence} (K : Heap)
  : ptrunc (heap_start_group K = heap_end_group K).
Proof.
  destruct K as [[[A [cA gA]] [a a']]].
  refine (ptrunc_rec ptrunc_isProp _ (snd cA a a')). intro p. destruct p.
  exact (trunc refl).
Defined.

(** The heap operation [(p, q, r) ↦ p q⁻¹ r] on [USym(H)]. *)
Definition heap_op (H : Heap) (p q r : USymH H) : USymH H := p ⋅ (q⁻¹ ⋅ r).

(** The maps [r ↦ p q⁻¹ r] of [USym(H)] (statement only): they are
    exactly the left multiplications by symmetries of the end shape, so
    they form the symmetry group of the end point. *)
Definition heap_maps_stmt : Type
  := forall (H : Heap) (φ : USymH H -> USymH H),
       Ex (fun pq : USymH H × USymH H => φ = heap_op H (fst pq) (snd pq))
       <-> Ex (fun l : hend H = hend H => φ = fun r => l ⋅ r).

(** Abelian heaps, whose endpoint groups are (purely) isomorphic
    (statement only). *)
Definition isAbHeap (H : Heap) : Type := forall p q r : USymH H, heap_op H p q r = heap_op H r q p.

Definition abheap_iso_stmt `{Funext} : Type
  := forall H : Heap, isAbHeap H -> Iso (heap_start_group H) (heap_end_group H).

(** Exercise [xca:heap-variety] (statement only): the fibers of [USym]
    over a set are sets, and the fibers of [H ↦ (USym(H), p q⁻¹ r)] are
    propositions, inhabited iff [S] is nonempty and [t] satisfies the
    heap equations. *)
Definition heap_struct (H : Heap) : {S : SetU & fst S -> fst S -> fst S -> fst S}
  := ((USymH H; USymH_isSet H); heap_op H).

Definition xca_heap_variety_stmt `{Univalence} : Type
  := (forall S : SetU, isSet {H : Heap & fst S = USymH H})
     × (forall (S : SetU) (t : fst S -> fst S -> fst S -> fst S),
          isProp (fiber heap_struct (S; t))
          × (fiber heap_struct (S; t)
             <-> ptrunc (fst S)
                 × (forall p q r s u, t (t p q r) s u = t p q (t r s u))
                 × (forall p q, t p p q = q) × (forall p q, t p q q = p))).
