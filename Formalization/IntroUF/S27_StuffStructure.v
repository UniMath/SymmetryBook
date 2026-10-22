(** * Section 2.27 Higher structure: stuff, structure, and properties

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Maps that forget at most [n]-structure, structure, properties, or
      nothing; forgetting properties is being an injection and forgetting
      nothing is being an equivalence, both by definition.
    - The refined image factorization
      [B ≃ ∑_a f⁻¹(a) → ∑_a ‖f⁻¹(a)‖₀ → ∑_a ‖f⁻¹(a)‖ → A], which commutes by
      definition; the fibers of the first map are connected, those of the
      second are nonempty sets (exercise [xca:0Im-to-Im]), and the last
      map is an injection.
    - Example [exa:stuff-struct-prop]: [fst : FinSet × FinSet → FinSet]
      forgets stuff, [fst : ∑_{A:FinSet} A → FinSet] forgets structure, and
      [FinSet_n → FinSet] forgets properties.  Exercise
      [xca:stuff-struct-prop] (more examples) has no single formal
      statement and is left out.
    - The remark after [def:groupoidFin] (2.24): [FinSet] is essentially
      [U]-small ([FinSet_essSmall]), given the replacement principle.
      NOTE for the book text, following a hint by the author: the proof
      does not go through [FinSet ≃ im(Fin : ℕ → U)] as the remark
      suggests, but uses that, by univalence, a sum over [U] such as
      [FinSet] is locally [U]-small; then replacement applies to the
      surjection [ℕ → FinSet], [n ↦ Fin n].  The book could mention this
      use of univalence explicitly. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S26_HigherTruncations.

Local Open Scope uf_scope.

(** ** 2.27 Higher structure: stuff, structure, and properties *)

(** Diagram [eq:forget-fibers]: [f] is [fst] after the equivalence
    [sum_of_fibers] of [lem:sum-of-fibers]; [f] forgets its fibers. *)

Section ForgetfulMaps.

  Context {B A : Type} (f : B -> A).

  Definition forgets_n_structure (n : ℕ) : Type
    := forall a, is_ntype n (fiber f a).
  Definition forgets_structure : Type := forall a, isSet (fiber f a).
  Definition forgets_properties : Type := forall a, isProp (fiber f a).
  Definition forgets_nothing : Type := forall a, isContr (fiber f a).

  (** A map forgets properties iff it is an injection, and nothing iff it
      is an equivalence (both by definition). *)
  Definition forgets_properties_isInj : forgets_properties = isInj f := refl.
  Definition forgets_nothing_isEquiv : forgets_nothing = isEquiv f := refl.

End ForgetfulMaps.

(** Fibers of a totalization. *)
Definition fiber_tot {A : Type} {P Q : A -> Type} (g : forall a, P a -> Q a)
  (a : A) (q : Q a) : fiber (tot g) (a; q) ≃ fiber (g a) q
  := Eqv_comp (fiber_hfiber _ _)
       (Eqv_comp (Eqv_of_Equiv (hfiber_functor_sigma_idmap P Q g a q))
                 (Eqv_inv (fiber_hfiber _ _))).

(** A sum of contractible types is equivalent to its base. *)
Definition sigma_contr_fibers {X : Type} {C : X -> Type}
  (c : forall x, isContr (C x)) : {x : X & C x} ≃ X
  := mkEqv fst (fun x => (x; fst (c x)))
       (fun w => pathpair (Y := C) (y := fst (c (fst w))) (y' := snd w)
                   refl (snd (c (fst w)) (snd w)))
       (fun x => refl).

Definition isConn_Eqv {X Y : Type} (e : X ≃ Y) (c : isConn X) : isConn Y
  := surj_isConn (isEquiv_isSurj (snd e)) c.

(** The refined image factorization of [f : B → A]:
    [B ≃ ∑_a f⁻¹(a) → ∑_a ‖f⁻¹(a)‖₀ → ∑_a ‖f⁻¹(a)‖ → A]. *)
Section RefinedImage.

  Context {B A : Type} (f : B -> A).

  Definition rf0 : B ≃ {a : A & fiber f a} := total_fibers f.

  Definition rf1 : {a : A & fiber f a} -> {a : A & strunc (fiber f a)}
    := tot (fun a => settrunc).

  (** The map [|_|' : ‖X‖₀ → ‖X‖] of exercise [xca:0Im-to-Im].
    (Placed here, before [exa:stuff-struct-prop], since the refined image factorization of the text before the example uses it.) *)
  Definition trunc' {X : Type} : strunc X -> ptrunc X
    := strunc_rec (prop_is_set ptrunc_isProp) trunc.

  Definition rf2 : {a : A & strunc (fiber f a)} -> {a : A & ptrunc (fiber f a)}
    := tot (fun a => trunc').

  Definition rf3 : {a : A & ptrunc (fiber f a)} -> A := fst.

  (** The factorization holds by definition, and the last two types are the
      book's [0]-image and [(-1)]-image ([im f]). *)
  Definition refined_factorization : f = rf3 ∘ rf2 ∘ rf1 ∘ fst rf0 := refl.

  Definition rf3_im : {a : A & ptrunc (fiber f a)} = im f := refl.

  (** The first map forgets pure higher structure: its fibers are
      connected. *)
  Definition settrunc_fiber_isConn `{Univalence} {X : Type} (z : strunc X)
    : isConn (fiber settrunc z).
  Proof.
    refine (_; _).
    - revert z. refine (strunc_ind_prop _ (fun _ => ptrunc_isProp) _). intro x.
      exact (trunc (x; refl)).
    - intros [x p] [y q].
      refine (ptrunc_rec ptrunc_isProp _
                (equiv_inverse (equiv_path_Tr (n := -1) x y) (q ⋅ p⁻¹))).
      intro r.
      exact (trunc (pathpair r (strunc_isSet z (settrunc y) _ q))).
  Defined.

  Definition rf1_fibers_isConn `{Univalence} (a : A) (z : strunc (fiber f a))
    : isConn (fiber rf1 (a; z))
    := isConn_Eqv (Eqv_inv (fiber_tot (fun a => settrunc) a z))
         (settrunc_fiber_isConn z).

  (** Exercise [xca:0Im-to-Im]: the fiber of the second map at [(a,p)] is
      equivalent to [‖f⁻¹(a)‖₀]: it forgets pure structure (the fibers are
      nonempty sets), and remembers which component of the fiber
      [f⁻¹(a)] we are in. *)
  Definition rf2_fiber_eqv (a : A) (p : ptrunc (fiber f a))
    : fiber rf2 (a; p) ≃ strunc (fiber f a)
    := Eqv_comp (fiber_tot (fun a => trunc') a p)
         (sigma_contr_fibers (fun x => isProp_inhabited_isContr
                                         (prop_is_set ptrunc_isProp _ _)
                                         (ptrunc_isProp _ _))).

  Definition rf2_fibers_isSet (a : A) (p : ptrunc (fiber f a))
    : isSet (fiber rf2 (a; p))
    := is_ntype_Eqv 0 (Eqv_inv (rf2_fiber_eqv a p)) strunc_isSet.

  Definition rf2_fibers_nonempty (a : A) (p : ptrunc (fiber f a))
    : ptrunc (fiber rf2 (a; p))
    := ptrunc_rec ptrunc_isProp
         (fun w => trunc (fst (Eqv_inv (rf2_fiber_eqv a p)) (settrunc w))) p.

  (** The last map forgets at most properties: it is the inclusion of the
      image. *)
  Definition rf3_isInj : isInj rf3 := im_i_isInj f.

End RefinedImage.

(** Example [exa:stuff-struct-prop]. *)
Section Examples.

  Context `{Univalence}.

  Definition FinSet_isGrpd : isGrpd FinSet
    := subtype_ntype 1 (fun S => ptrunc_isProp) SetU_isGrpd.

  (** [fst : FinSet × FinSet → FinSet] forgets [1]-structure (stuff). *)
  Definition fst_FinSet2_forgets_stuff
    : forgets_n_structure (@fst FinSet (fun _ => FinSet)) 1
    := fun S => is_ntype_Eqv 1 (fst_fiber_eqv (fun _ => FinSet) S) FinSet_isGrpd.

  (** [fst : ∑_{A:FinSet} A → FinSet] forgets structure (a point). *)
  Definition fst_pointed_FinSet_forgets_structure
    : forgets_structure (@fst FinSet (fun S => fst (fst S)))
    := fun S => is_ntype_Eqv 0 (fst_fiber_eqv (fun S => fst (fst S)) S)
                  (snd (fst S)).

  (** The inclusion [FinSet_n → FinSet] forgets properties. *)
  Definition FinSet_n_incl (n : ℕ) : FinSet_n n -> FinSet
    := tot (fun (S : SetU) (u : ptrunc (Fin n = fst S :> Type)) =>
              ptrunc_rec ptrunc_isProp
                (fun e => trunc ((n; e⁻¹) : {m : ℕ & fst S = Fin m})) u).

  Definition FinSet_n_incl_forgets_properties (n : ℕ)
    : forgets_properties (FinSet_n_incl n).
  Proof.
    intros [S h].
    refine (isProp_Eqv (Eqv_inv (fiber_tot _ S h)) _).
    exact (Sigma_isProp ptrunc_isProp (fun _ => prop_is_set ptrunc_isProp _ _)).
  Defined.

End Examples.

(** Exercise [xca:stuff-struct-prop] asks for more examples of this kind
    of analysis; it has no single formal statement. *)

(** Remark after [def:groupoidFin]: [FinSet] is essentially [U]-small, by
    the replacement principle applied to the surjection [ℕ → FinSet],
    [n ↦ Fin n]; [FinSet] is locally small by univalence.
    (From 2.24; placed here since it uses [sigma_contr_fibers] of this section.) *)
Section FinSetSmall.

  Universe u.
  Context `{Univalence}.

  (** The image of a surjection is equivalent to its codomain. *)
  Definition im_surj_eqv {X Y : Type} (f : X -> Y) (s : isSurj f) : im f ≃ Y
    := sigma_contr_fibers (fun y => isProp_inhabited_isContr ptrunc_isProp (s y)).

  Definition FinSet_U : Type := {S : {X : Type@{u} & isSet X} & isFinSet (fst S)}.

  Definition FinSet_locSmall
    : forall S T : FinSet_U, {Y : Type@{u} & (S = T) ≃ Y}.
  Proof.
    intros S T.
    refine (exist (fun Y : Type@{u} => (S = T) ≃ Y) (fst (fst S) ≃ fst (fst T)) _).
    refine (Eqv_comp (subtype_paths_eqv (fun _ => ptrunc_isProp) S T) _).
    refine (Eqv_comp (subtype_paths_eqv (fun X => isSet_isProp X) (fst S) (fst T)) _).
    exact (idtoeqv; ua _ _).
  Defined.

  Definition Fin_FinSet (n : ℕ) : FinSet_U
    := exist (fun S : {X : Type@{u} & isSet X} => isFinSet (fst S))
         (exist (fun X : Type@{u} => isSet X) (Fin n) (fun x y => fst (Fin_isDecSet n x y)))
         (trunc (exist (fun m : ℕ => (Fin n : Type@{u}) = Fin m) n refl)).

  Definition Fin_FinSet_isSurj : isSurj Fin_FinSet.
  Proof.
    intros [S h]. revert h.
    refine (ptrunc_ind _ (fun _ => ptrunc_isProp) _). intros [n e].
    exact (trunc (n; path_sigma_prop (u := (S; trunc (n; e)) : FinSet_U) (v := Fin_FinSet n)
                       (fun _ => ptrunc_isProp)
                       (path_sigma_prop (u := S) (v := fst (Fin_FinSet n))
                          (fun X => isSet_isProp X) e))).
  Defined.

  Definition FinSet_essSmall (rep : Replacement) : {Y : Type@{u} & FinSet_U ≃ Y}
    := essSmall_Eqv (Eqv_inv (im_surj_eqv Fin_FinSet Fin_FinSet_isSurj))
         (rep ℕ FinSet_U Fin_FinSet (small_essSmall ℕ) FinSet_locSmall).

End FinSetSmall.
