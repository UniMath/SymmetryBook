(** * Section 5.6 Any symmetry is a symmetry in Set

    Part of Chapter 5 ([actions.tex]); see [Actions.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - The homomorphism [ρ_G : Hom(G, Σ_{UG})] ([rho]), classified by
      [z ↦ (z = sh_G)] ([Brho0]).  The book points it by reflexivity; as
      the component structure is only propositionally equal, we point it
      by a path [rho_pt] whose underlying identification of sets is
      [refl] ([apF_rho_pt]).
    - On symmetries, [ρ_G(g)] is [x ↦ x g⁻¹] ([USym_rho_act]).
    - Theorem [lem:allgpsarepermutationgps] (Cayley): [ρ_G] is a
      monomorphism ([cayley]).  We use the elementary argument of the
      remark following the theorem: [g] is recovered from the action of
      [ρ_G(g)] on [refl_{sh_G}].

    - Exercise [xca:PP-fixed-permutations] ([xca_PP_fixed], with
      [PermSet], [FixedPerms], [act_PermSet]: transport in [PermSet] is
      conjugation).  NOTE for the book text: a fixed [π] is
      [x ↦ x π(refl)] ([fixed_rmul]), so evaluation at [refl] reverses
      the order: [(π ∘ π')(refl) = π'(refl) π(refl)].  It is an
      anti-isomorphism, unless the fixed permutations get the opposite
      composition (or one evaluates [π ↦ π(refl)⁻¹]).  The statement
      first had the order the other way round; it is corrected.

    Left out (statements only, no proofs yet; time limit per result)
    - The description of the subgroup [E(G, ρ_G)]
      ([E_rho_symmetries_stmt]).

    Left out (not formalized)
    - The proof via [lem:BGbytorsor] (the theorem is proved otherwise) and
      remark [rem:CayleyOversize] (an explanation).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core.
From SymmetryBook Require Export Actions.S05_Torsors.

Local Open Scope uf_scope.

(** ** 5.6 Any symmetry is a symmetry in [Set] *)

Section Cayley.

  Context `{Univalence} (G : Group).

  Definition USymSet : SetU := (USym G; USym_isSet G).

  (** [Bρ_G :≡ P_(sh_G) : BG →* BΣ_{UG}], [z ↦ (z = sh_G)], pointed by
      [refl]. *)
  Definition Brho0 (z : utype (BG G)) : component SetU USymSet
    := (((z = sh G); BG_isGrpd G z (sh G));
        Trunc_functor (-1) (fun p : sh G = z => ap (fun y => ((y = sh G); BG_isGrpd G y (sh G)) : SetU) p)
          (snd (BG_isConn G) (sh G) z)).

  Definition rho_pt : ((USymSet; trunc refl) : component SetU USymSet) = Brho0 (sh G)
    := @path_sigma_prop SetU (fun S => ptrunc (USymSet = S)) (fun _ => ptrunc_isProp)
         (USymSet; trunc refl) (Brho0 (sh G)) refl.

  Definition rho : Hom G (SG_S USymSet) := @mkhom G (SG_S USymSet) (Brho0; rho_pt).

  Definition trp_paths_to (c : utype (BG G)) {z w : utype (BG G)} (g : z = w) (q : z = c)
    : trp (fun y => y = c) g q = q ⋅ g⁻¹.
  Proof. destruct g. exact (trans_1p q)^. Defined.

  Local Notation F := (fun S : component SetU USymSet => fst (fst S)).

  Definition apF_rho_pt : ap F rho_pt = refl
    := ap_compose fst fst rho_pt @ ap (ap fst) (ap_fst_pathpair refl _).

  Definition apF_USymf (g : USym G) : ap F (USymf rho g) = ap (fun z => z = sh G) g.
  Proof.
    change (ap F (rho_pt⁻¹ ⋅ (ap Brho0 g ⋅ rho_pt)) = ap (fun z => z = sh G) g).
    refine (ap_trans F _ _ @ _).
    refine (ap011 (fun a b => a ⋅ b) (ap_symm F rho_pt @ ap symm apF_rho_pt)
              (ap_trans F _ _ @ ap (fun a => _ ⋅ a) apF_rho_pt) @ _).
    refine (trans_1p _ @ _). exact (ap_compose Brho0 F g)^.
  Defined.

  (** On symmetries, [ρ_G(g)] acts on [UG] by [x ↦ x g⁻¹]. *)
  Definition USym_rho_act (g : USym G) (x : USym G)
    : trp F (USymf rho g) x = x ⋅ g⁻¹.
  Proof.
    refine (ptw (trp_ap idmap F (USymf rho g)) x @ _).
    refine (ap (fun r => trp idmap r x) (apF_USymf g) @ _).
    refine ((ptw (trp_ap idmap (fun z => z = sh G) g) x)^ @ _).
    exact (trp_paths_to (sh G) g x).
  Defined.

  (** Theorem [lem:allgpsarepermutationgps] (Cayley): [ρ_G] is a
      monomorphism. *)
  Definition cayley : ismono rho.
  Proof.
    refine (cancel_isInj (USym_isSet _) _). intros g g' e.
    pose (e' := (USym_rho_act g (refl (sh G)))^ @ ap (fun r : utype (loops (BG (SG_S USymSet))) => trp F r (refl (sh G))) e @ USym_rho_act g' (refl (sh G))).
    exact ((symm_symm g)^ @ ap symm e' @ symm_symm g').
  Defined.

  (** The description of the subgroup [E(G, ρ_G)] (statement only): its
      symmetries are the right multiplications [x ↦ x g⁻¹]. *)
  Definition E_rho_symmetries_stmt : Type
    := forall σ : USym (SG_S USymSet),
         ptrunc (fiber (USymf rho) σ) <-> Ex (fun g : USym G => forall x, trp F σ x = x ⋅ g⁻¹).

  (** Exercise [xca:PP-fixed-permutations]: the
      permutations of [UG] fixed by the action of [G] on
      [z ↦ ((sh_G = z) ≃ (sh_G = z))] are those with
      [π(g g') = g π(g')], and evaluation at [refl] is an equivalence from
      them to [UG] turning composition into the opposite multiplication
      (see the NOTE in the header). *)
  Definition PermSet (z : utype (BG G)) : SetU
    := (((sh G = z) ≃ (sh G = z)); Eqv_sets_isSet (BG_isGrpd G (sh G) z)).

  Definition FixedPerms : Type
    := {pi : USym G ≃ USym G & forall g g' : USym G, fst pi (g ⋅ g') = g ⋅ fst pi g'}.

  Definition xca_PP_fixed_stmt : Type
    := (forall pi : USym G ≃ USym G,
          (forall g : USym G, act PermSet g pi = pi)
          <-> (forall g g' : USym G, fst pi (g ⋅ g') = g ⋅ fst pi g'))
       × isEquiv (fun pi : FixedPerms => fst (fst pi) refl)
       × (forall pi pi' : FixedPerms,
            fst (fst pi) (fst (fst pi') refl) = fst (fst pi') refl ⋅ fst (fst pi) refl).

  (** Transport in [PermSet] is conjugation: [p · π = p π(p⁻¹ _)]. *)
  Definition act_PermSet {z : utype (BG G)} (p : sh G = z) (pi : el PermSet (sh G))
    (x : sh G = z) : fst (act PermSet p pi) x = p ⋅ fst pi (p⁻¹ ⋅ x).
  Proof. destruct p. exact refl. Defined.

  Definition fixed_hom (pi : USym G ≃ USym G) (h : forall g : USym G, act PermSet g pi = pi)
    (g g' : USym G) : fst pi (g ⋅ g') = g ⋅ fst pi g'.
  Proof.
    refine ((ap (fun s : USym G ≃ USym G => fst s (g ⋅ g')) (h g))^ @ act_PermSet g pi _ @ _).
    exact (ap (fun y => g ⋅ fst pi y) (trans_assoc g' g g⁻¹ @ ap (fun r => r ⋅ g') (trans_pV g))).
  Defined.

  Definition hom_fixed (pi : USym G ≃ USym G)
    (h : forall g g' : USym G, fst pi (g ⋅ g') = g ⋅ fst pi g') (g : USym G)
    : act PermSet g pi = pi.
  Proof.
    apply path_Eqv. apply ptw_inv. intro x.
    refine (act_PermSet g pi x @ ap (fun y => g ⋅ y) (h g⁻¹ x) @ _).
    exact (trans_assoc _ g⁻¹ g @ ap (fun r => r ⋅ fst pi x) (trans_Vp g)).
  Defined.

  (** The fixed permutation [x ↦ x h]. *)
  Definition rmul_eqv (h : USym G) : USym G ≃ USym G
    := mkEqv (fun x => x ⋅ h) (fun x => x ⋅ h⁻¹)
         (fun x => (trans_assoc h⁻¹ h x)^ @ ap (fun r => x ⋅ r) (trans_Vp h) @ trans_1p x)
         (fun x => (trans_assoc h h⁻¹ x)^ @ ap (fun r => x ⋅ r) (trans_pV h) @ trans_1p x).

  Definition rmul_fixed (h : USym G) : FixedPerms
    := (rmul_eqv h; fun g g' => (trans_assoc h g' g)^).

  Definition fixed_rmul (pi : FixedPerms) (x : USym G) : fst (fst pi) x = x ⋅ fst (fst pi) refl
    := ap (fst (fst pi)) (trans_1p x)^ @ snd pi x refl.

  (** The statement had [π(π'(refl)) = π(refl) π'(refl)], which fails for
      non-abelian [G]: evaluation at [refl] turns composition into the
      opposite multiplication. *)
  Definition xca_PP_fixed : xca_PP_fixed_stmt.
  Proof.
    refine (((fun pi => (fixed_hom pi, hom_fixed pi)); _); _).
    - refine (iso_to_isEquiv _ rmul_fixed _ (fun h => refl)).
      intro pi. refine (path_sigma_prop (fun _ => Pi_isProp (fun _ => Pi_isProp
                          (fun _ => USym_isSet G _ _))) _).
      apply path_Eqv. apply ptw_inv. intro x. exact (fixed_rmul pi x)^.
    - intros pi pi'. exact (fixed_rmul pi _).
  Defined.

End Cayley.
