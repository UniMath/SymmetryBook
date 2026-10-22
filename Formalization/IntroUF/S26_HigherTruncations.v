(** * Section 2.26 Higher truncations

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - The specification of [def:join-construction-of-truncation], met by
      the library's [Trunc n] with unit [tr]: its universal property with
      respect to [n]-types.
    - The book's join construction, for any truncation level [n]: the
      [n]-truncated identity family [I_n], [‖A‖_{n+1} :≡ im(I_n)] with its
      unit, which is surjective; [‖A‖_{n+1}] is an [(n+1)]-type; the
      equivalence [eq:trunc-path-eq], [‖x = y‖_n ≃ (|x| = |y|)], proved as
      in the book via [(|x| = |y|) ≃ ∏_z (‖x = z‖_n ≃ ‖y = z‖_n)] and going
      backwards at [|refl_y|_n] (with a Yoneda argument for truncated
      identity types); the universal property of [‖A‖_{n+1}], obtained by
      showing that the comparison map from the library's [Trunc (n+1) A]
      is an equivalence (an injective surjection) rather than by the
      book's contractible-extensions argument; and the re-sizing of
      [‖A‖_{n+1}] into the universe of [A] by the replacement principle
      (a hypothesis of [TruncImg_essSmall]). *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S25_FamiliesMaps.

Local Open Scope uf_scope.

(** ** 2.26 Higher truncations *)

(** Construction [def:join-construction-of-truncation], specification:
    for every truncation level [n] the library's [Trunc n] with unit
    [tr] has the universal property with respect to [n]-types. *)
Definition trunc_univ_prop `{Funext} (n : trunc_index) (A B : Type)
  `{IsTrunc n B} : (Trunc n A -> B) ≃ (A -> B)
  := mkEqv (fun h => h ∘ tr) (Trunc_rec)
       (fun h => ptw_inv (Trunc_ind (fun x => Trunc_rec (h ∘ tr) x = h x)
                                    (fun a => refl)))
       (fun g => refl).

(** The book's implementation, the join construction: [‖A‖_{n+1}] is the
    image of the [n]-truncated identity family
    [I_n : A → (A → ∑_{X:U} isnType(X))], [x ↦ (y ↦ ‖x = y‖_n)]. *)
Definition prop_istrunc_succ (n : trunc_index) {X : Type} (h : isProp X)
  : IsTrunc n.+1 X.
Proof. pose proof (isProp_IsHProp h). destruct n as [|m]; exact _. Defined.

Section JoinConstruction.

  Context `{Univalence} (n : trunc_index) (A : Type).

  Definition nType : Type := {X : Type & IsTrunc n X}.

  Definition I_n : A -> A -> nType
    := fun x y => (Trunc n (x = y); istrunc_truncation n _).

  Definition TruncImg : Type := im I_n.

  Definition unitImg : A -> TruncImg := im_p I_n.

  Definition unitImg_def (x : A)
    : unitImg x = (I_n x; trunc (x; refl)) := refl.

  Definition unitImg_isSurj : isSurj unitImg := im_p_isSurj I_n.

  (** [‖A‖_{n+1}] is an [(n+1)]-type, since the type of [n]-types is an
      [(n+1)]-type. *)
  Definition TruncImg_istrunc : IsTrunc n.+1 TruncImg.
  Proof.
    unfold TruncImg, im, Ex, ptrunc, nType.
    assert (h : forall Y : Type, IsTrunc n.+1 (Trunc (-1) Y)).
    { intro Y. destruct n as [|m]; exact _. }
    exact _.
  Defined.

  (** The map [‖x = y‖_n → (|x|_{n+1} = |y|_{n+1})] of equation
      [eq:trunc-path-eq]. *)
  Definition path_img (x y : A) : Trunc n (x = y) -> unitImg x = unitImg y
    := @Trunc_rec n (x = y) _ (@istrunc_paths _ _ TruncImg_istrunc _ _)
         (ap unitImg).

  (** Families of maps out of [‖x = _‖_n] into [n]-types are determined
      by their value at [|refl_x|_n]. *)
  Definition yoneda_trunc {x : A} {T : A -> Type} `{forall z, IsTrunc n (T z)}
    (F G : forall z, Trunc n (x = z) -> T z) (h : F x (tr refl) = G x (tr refl))
    : forall z u, F z u = G z u.
  Proof. intros z u. revert u. refine (Trunc_ind _ _). intro q. destruct q. exact h. Defined.

  (** [(|x| = |y|) ≃ ∏_{z:A} (‖x = z‖_n ≃ ‖y = z‖_n)], as in the book. *)
  Definition Phi_eqv (x y : A)
    : (unitImg x = unitImg y) ≃ (forall z, Trunc n (x = z) ≃ Trunc n (y = z)).
  Proof.
    refine (Eqv_comp (subtype_paths_eqv (fun P => ptrunc_isProp)
                        (unitImg x) (unitImg y)) _).
    refine (Eqv_comp (ptw; funext (I_n x) (I_n y)) _).
    exact (Pi_eqv (fun z => Eqv_comp
             (subtype_paths_eqv (fun X => @IsHProp_isProp (IsTrunc n X) _)
                (I_n x z) (I_n y z))
             (idtoeqv; ua _ _))).
  Defined.

  Let Phi (x y : A) (r : unitImg x = unitImg y) (z : A)
    : Trunc n (x = z) -> Trunc n (y = z)
    := fst (fst (Phi_eqv x y) r z).

  Definition Phi_path_img (x : A)
    : forall y (s : Trunc n (x = y)), Phi x y (path_img x y s) y s = tr refl.
  Proof.
    intros y s. revert s. refine (Trunc_ind _ _). intro p. destruct p. exact refl.
  Defined.

  Definition Phi_path_img_aux (x : A)
    : forall y (r : unitImg x = unitImg y) (s : Trunc n (x = y)),
      Phi x y r y s = tr refl
      -> Phi x y (path_img x y s) x (tr refl) = Phi x y r x (tr refl).
  Proof.
    intros y r s. revert s. refine (Trunc_ind _ _). intro p.
    revert y p r. refine (paths_ind _ _ _). intros r h. exact h^.
  Defined.

  Definition path_img_key (x y : A) (r : unitImg x = unitImg y)
    (s : Trunc n (x = y)) (h : Phi x y r y s = tr refl)
    : path_img x y s = r.
  Proof.
    pose (t := snd (Phi_eqv x y)).
    refine ((eqinv_l t _)^ @ ap (eqinv t) _ @ eqinv_l t r).
    apply ptw_inv. intro z. apply path_Eqv. apply ptw_inv.
    exact (yoneda_trunc (T := fun z => Trunc n (y = z))
             (Phi x y (path_img x y s)) (Phi x y r)
             (Phi_path_img_aux x y r s h) z).
  Defined.

  (** Equation [eq:trunc-path-eq]: [‖x = y‖_n ≃ (|x|_{n+1} = |y|_{n+1})],
      with inverse given by going backwards at [|refl_y|_n]. *)
  Definition path_img_isEquiv (x y : A) : isEquiv (path_img x y).
  Proof.
    pose (psi := fun r => eqinv (snd (fst (Phi_eqv x y) r y)) (tr refl)).
    refine (iso_to_isEquiv (path_img x y) psi _ _).
    - intro s.
      exact ((ap (eqinv (snd (fst (Phi_eqv x y) (path_img x y s) y)))
                 (Phi_path_img x y s))^
             @ eqinv_l (snd (fst (Phi_eqv x y) (path_img x y s) y)) s).
    - intro r.
      exact (path_img_key x y r (psi r) (eqinv_r (snd (fst (Phi_eqv x y) r y)) _)).
  Defined.

  (** The universal property of [‖A‖_{n+1}], by comparison with the
      library's [Trunc (n+1)]. *)
  Definition truncImg_map : Trunc n.+1 A -> TruncImg
    := @Trunc_rec n.+1 A TruncImg TruncImg_istrunc unitImg.

  Definition truncImg_map_isEquiv : isEquiv truncImg_map.
  Proof.
    apply inj_surj_isEquiv.
    - apply ap_isEquiv_isInj.
      pose proof TruncImg_istrunc.
      assert (hP : forall a b : Trunc n.+1 A,
                 IsTrunc n.+1 (isEquiv (@ap _ _ truncImg_map a b)))
        by (intros; exact (prop_istrunc_succ n (isEquiv_isProp _))).
      refine (Trunc_ind _ _). intro x.
      refine (Trunc_ind _ _). intro y.
      pose (pT := equiv_path_Tr (n := n) x y).
      pose (pT' := equiv_inverse pT).
      refine (isEquiv_homotopic (path_img x y ∘ pT')
                (@ap _ _ truncImg_map (tr x) (tr y)) _
                (comp_isEquiv (isEquiv_of_IsEquiv pT') (path_img_isEquiv x y))).
      intro r. refine (_ @ ap (ap truncImg_map) (eisretr pT r)).
      change (path_img x y (pT' r) = ap truncImg_map (pT (pT' r))).
      generalize (pT' r). refine (Trunc_ind _ _). intro p.
      destruct p. exact refl.
    - intro z.
      exact (ptrunc_rec ptrunc_isProp
               (fun w : fiber unitImg z => trunc ((tr (fst w); snd w)
                                                 : fiber truncImg_map z))
               (unitImg_isSurj z)).
  Defined.

  Definition precomp_eqv `{Funext} {X Y Z : Type} (e : X ≃ Y)
    : (Y -> Z) ≃ (X -> Z)
    := mkEqv (fun h => h ∘ fst e) (fun k => k ∘ eqinv (snd e))
         (fun h => ptw_inv (fun y => ap h (eqinv_r (snd e) y)))
         (fun k => ptw_inv (fun x => ap k (eqinv_l (snd e) x))).

  Definition TruncImg_univ_prop (B : Type) `{IsTrunc n.+1 B}
    : (TruncImg -> B) ≃ (A -> B)
    := Eqv_comp (precomp_eqv (truncImg_map; truncImg_map_isEquiv))
         (trunc_univ_prop n.+1 A B).

  Definition TruncImg_univ_prop_map (B : Type) `{IsTrunc n.+1 B}
    (h : TruncImg -> B) : fst (TruncImg_univ_prop B) h = h ∘ unitImg := refl.

End JoinConstruction.

(** Finally, the book re-sizes [‖A‖_{n+1}] into the universe of [A] using
    the replacement principle: maps into the type of [n]-types form a
    locally small type, by univalence. *)
Section JoinResizing.

  Universe u.
  Context `{Univalence} (n : trunc_index) (A : Type@{u}).

  Definition nType_fun_locSmall
    : forall F G : A -> {X : Type@{u} & IsTrunc n X}, {Y : Type@{u} & (F = G) ≃ Y}.
  Proof.
    intros F G.
    refine (exist (fun Y : Type@{u} => (F = G) ≃ Y) (forall z, fst (F z) ≃ fst (G z)) _).
    exact (
           Eqv_comp (ptw; funext F G)
             (Pi_eqv (fun z => Eqv_comp
                (subtype_paths_eqv (fun X => @IsHProp_isProp (IsTrunc n X) _) (F z) (G z))
                (idtoeqv; ua _ _)))).
  Defined.

  Definition TruncImg_essSmall (rep : Replacement)
    : {Y : Type@{u} & TruncImg n A ≃ Y}
    := rep A _ (I_n n A) (small_essSmall A) nType_fun_locSmall.

End JoinResizing.
