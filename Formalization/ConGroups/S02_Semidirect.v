(** * Section 8.2 Semidirect products

    Part of Chapter 8 ([congp.tex]); see [ConGroups.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:semidirect-product]: [semidirect G H] for an action
      [H : BG → Group] in groups; for the trivial action it is the product
      ([semidirect_trivial], with the same classifying type).
    - Lemma [lem:pathpairsection] ([pathpair_section_eqv], for a section
      [f] of [Y]), definition [def:pathsectionaction] ([psa], [q'^p]),
      lemma [def:pathsectionactionassoc] ([psa_assoc]) and lemma
      [lem:pathpairsectionmult] ([pps_mult]); hence [U(G ⋉ H) ≃ UG × UH]
      ([USym_semidirect_eqv]) with multiplication
      [(p', q') (p, q) = (p' p, q'^p q)] ([USym_semidirect_mult]).
    - The projection [p] ([sd_proj]), its section [s] ([sd_sec], with
      [p ∘ s = id] by [refl]) and [j] ([sd_incl]); [j] is a monomorphism
      ([sd_incl_ismono]).

    - Definition [def:gen-dihedral] relative to an action of [Σ_2]
      ([Dihedral]).

    Left out (statements only, no proofs yet; time limit per result)
    - The action of [Σ_2] on [C_n] ([S2_on_Cn_stmt]), construction
      [con:bidirectional-bicycle] and its exercises
      ([con_bidirectional_bicycle_stmt]), the cardinality [2n] of [D_n]
      ([dihedral_card_stmt]), and the exercise that [Q_8] and [D_4] are
      not isomorphic ([Q8_not_D4_stmt]).
    - That [j] gives the kernel of [p] ([sd_kernel_stmt]; kernels are
      defined in a later chapter, as the book's footnote says).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core.
From SymmetryBook Require Export AbsGroup.AbsGroup.

Local Open Scope uf_scope.

(** ** 8.2 Semidirect products *)

(** Definition [def:semidirect-product]: for an action [H : BG → Group]
    of [G] in groups, [G ⋉ H :≡ mkgroup(∑_{t:BG} BH(t))], pointed at
    [(sh_G, sh_{H(sh_G)})]. *)
Definition semidirect `{Funext} (G : Group) (H : utype (BG G) -> Group) : Group
  := mkgroup ({t : utype (BG G) & utype (BG (H t))};
              ((sh G; sh (H (sh G)));
               (Sigma_isConn (BG_isConn G) (fun t => BG_isConn (H t));
                Sigma_isGrpd (BG_isGrpd G) (fun t => BG_isGrpd (H t))))).

(** For the trivial action we get the product of groups (the classifying
    types agree by definition). *)
Definition semidirect_trivial `{Univalence} (G K : Group)
  : semidirect G (fun _ => K) = prodG G K
  := path_Group ((pid _); id_isEquiv _).

(** Dihedral groups (statements only).  The action of [Σ_2] on [C_n]
    for an order [n] (by swapping the two directions of a cycle) and the
    bidirectional bicycles are not constructed; we state their existence,
    and define [D_n :≡ Σ_2 ⋉ C̃_n] relative to an action. *)
Section Dihedral.

  Context `{Univalence}.

  Definition S2_on_Cn_stmt : Type
    := forall n : Order,
         {A : utype (BG (SG 2)) -> Group &
           ptrunc {c : Cyc & (ord c = n) × (A (sh (SG 2)) = AutG Cyc_isGrpd c)}}.

  (** Definition [def:gen-dihedral], relative to an action [A]. *)
  Definition Dihedral (A : utype (BG (SG 2)) -> Group) : Group := semidirect (SG 2) A.

  (** Construction [con:bidirectional-bicycle] with its exercise, and the
      cardinality [2n] for finite [n]. *)
  Definition con_bidirectional_bicycle_stmt : Type
    := forall (A : utype (BG (SG 2)) -> Group),
         {B : Bicyc & isNormal B
                      × (BG (Dihedral A) ≃* ((component Bicyc B; (B; trunc refl)) : Ustar))}.

  Definition dihedral_card_stmt : Type
    := forall (k : ℕ) (A : utype (BG (SG 2)) -> Group), A (sh (SG 2)) = CG k ->
         {h : isFinGroup (Dihedral A) & CardG (Dihedral A) h = mul 2 (S k)}.

  (** The exercise that [Q_8] and [D_4] are not isomorphic; it holds for
      any action of [Σ_2] on [C_4]. *)
  Definition Q8_not_D4_stmt : Type
    := forall A : utype (BG (SG 2)) -> Group, A (sh (SG 2)) = CG 3 -> ¬ Iso Q8 (Dihedral A).

End Dihedral.

(** Lemma [lem:pathpairsection], definition [def:pathsectionaction],
    lemma [def:pathsectionactionassoc] and lemma [lem:pathpairsectionmult],
    for a section [f : ∏_x Y(x)]. *)
Section PathPairSection.

  Context {X : Type} {Y : X -> Type} (f : forall x, Y x).

  Definition po_sec {x x' : X} (p : x = x')
    : PathOver Y p (f x) (f x') -> (f x = f x)
    := match p with refl => fun q => q end.

  Definition po_sec_inv {x x' : X} (p : x = x')
    : (f x = f x) -> PathOver Y p (f x) (f x')
    := match p with refl => fun q => q end.

  Definition po_sec_inv_sec {x x' : X} (p : x = x') (r : PathOver Y p (f x) (f x'))
    : po_sec_inv p (po_sec p r) = r.
  Proof. destruct p. exact refl. Defined.

  Definition pps_fw {x x' : X} (e : ((x; f x) : Tot Y) = (x'; f x'))
    : (x = x') × (f x = f x)
    := (fst (pathsplit e); po_sec (fst (pathsplit e)) (snd (pathsplit e))).

  Definition pps_bw {x x' : X} (pq : (x = x') × (f x = f x))
    : ((x; f x) : Tot Y) = (x'; f x')
    := pathpair (fst pq) (po_sec_inv (fst pq) (snd pq)).

  Definition pps_fw_bw {x x' : X} (p : x = x') (q : f x = f x)
    : pps_fw (pps_bw (p; q)) = (p; q).
  Proof.
    destruct p.
    exact (ap (fun w : {p : x = x & PathOver Y p (f x) (f x)} =>
                 ((fst w; po_sec (fst w) (snd w)) : (x = x) × (f x = f x)))
              (pathsplit_pathpair refl q)).
  Defined.

  Definition pathpair_section_eqv (x x' : X)
    : (((x; f x) : Tot Y) = (x'; f x')) ≃ (x = x') × (f x = f x).
  Proof.
    refine (mkEqv pps_fw pps_bw _ _).
    - intro e. unfold pps_bw, pps_fw. cbn.
      refine (ap (pathpair _) (po_sec_inv_sec _ _) @ _).
      exact (pathpair_pathsplit e).
    - intros [p q]. exact (pps_fw_bw p q).
  Defined.

  (** The operation [q' ↦ q'^p]. *)
  Definition psa {x x' : X} (p : x = x') : (f x' = f x') -> (f x = f x)
    := match p with refl => fun q' => q' end.

  Definition psa_assoc {x x' x'' : X} (p : x = x') (p' : x' = x'') (q : f x'' = f x'')
    : psa p (psa p' q) = psa (p' ⋅ p) q.
  Proof. destruct p', p. exact refl. Defined.

  Definition pps_fw_ap_pair {x : X} (r : f x = f x)
    : pps_fw (ap (pair x) r) = (refl; r)
    := ap pps_fw (pathpair_refl r)^ @ pps_fw_bw refl r.

  Definition pps_mult {x x' x'' : X} (p : x = x') (q : f x = f x)
    (p' : x' = x'') (q' : f x' = f x')
    : pps_fw (pps_bw (p'; q') ⋅ pps_bw (p; q)) = (p' ⋅ p; psa p q' ⋅ q).
  Proof.
    destruct p', p. unfold pps_bw. cbn.
    refine (ap pps_fw (ap011 (fun a b => a ⋅ b) (pathpair_refl q') (pathpair_refl q)) @ _).
    refine (ap pps_fw (ap_trans (pair x) q q')^ @ _).
    exact (pps_fw_ap_pair _).
  Defined.

End PathPairSection.

Section SemidirectHoms.

  Context `{fe : Funext} (G : Group) (H : utype (BG G) -> Group).

  Local Notation GH := (semidirect G H).

  Definition sd_sec_fun (t : utype (BG G)) : utype (BG (H t)) := sh (H t).

  (** The symmetries of [G ⋉ H] are pairs, with the multiplication
      [(p', q') · (p, q) = (p' p, q'^p q)]. *)
  Definition USym_semidirect_eqv : USym GH ≃ USym G × USym (H (sh G))
    := pathpair_section_eqv sd_sec_fun (sh G) (sh G).

  Definition USym_semidirect_mult (p p' : USym G) (q q' : USym (H (sh G)))
    : fst USym_semidirect_eqv
        (eqinv (snd USym_semidirect_eqv) (p'; q') ⋅ eqinv (snd USym_semidirect_eqv) (p; q))
      = (p' ⋅ p; psa sd_sec_fun p q' ⋅ q)
    := pps_mult sd_sec_fun p q p' q'.

  (** The projection [p], the section [s] and the inclusion [j]. *)
  Definition sd_proj : Hom GH G := mkhom ((fst; refl) : BG GH →* BG G).

  Definition sd_sec : Hom G GH
    := mkhom (((fun t => (t; sh (H t))) : utype (BG G) -> utype (BG GH)); refl).

  Definition sd_proj_sec : compG sd_proj sd_sec = idG G := refl.

  Definition sd_incl : Hom (H (sh G)) GH
    := mkhom (((fun u => (sh G; u)) : utype (BG (H (sh G))) -> utype (BG GH)); refl).

  (** [j] is a monomorphism. *)
  Definition sd_incl_ismono : ismono sd_incl.
  Proof.
    apply (cancel_isInj (USym_isSet GH)). intros r r' e.
    pose (k0 := (fun u => (sh G; u)) : utype (BG (H (sh G))) -> utype (BG GH)).
    assert (e' : ap k0 r = ap k0 r').
    { exact ((loops_fun_refl k0 r)^ @ e @ loops_fun_refl k0 r'). }
    pose (sn := fun w : (sh G = sh G) × (sd_sec_fun (sh G) = sd_sec_fun (sh G)) => snd w).
    refine ((ap sn (pps_fw_ap_pair sd_sec_fun r))^ @ _
            @ ap sn (pps_fw_ap_pair sd_sec_fun r')).
    exact (ap (fun w => sn (pps_fw sd_sec_fun w)) e').
  Defined.

  (** That [j] gives the kernel of [p] (statement only; kernels are
      defined in a later chapter): [BH] is the fiber of [Bp] at [sh_G]. *)
  Definition sd_kernel_stmt : Type
    := {e : utype (BG (H (sh G))) ≃ fiber (fst (Bf sd_proj)) (sh G) &
         forall u, fst e u = ((sh G; u); refl)}.

End SemidirectHoms.
