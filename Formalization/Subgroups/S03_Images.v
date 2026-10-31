(** * Section 9.3 Images, kernels and cokernels

    Part of Chapter 9 ([subgroups.tex]); see [Subgroups.v] for an
    overview of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:kernel]: [Ker f :≡ Aut_{(Bf)⁻¹(sh_H)}(sh_G, Bf_pt)]
      (the book's footnote), [kermap] (the first projection, pointed by
      [refl]), [kermap_ismono], [ker f : Mono G].
    - Definition [def:cokernel] ([coker f : GSet H], with [act_coker]);
      lemma [lem:isTrans(coker)] ([coker_trans]); remark
      [rem:imageandcokernel] ([imsub f : SubGrp H]).
    - Lemma [lem:fibersofcomposites], for an arbitrary point [y] of
      [f₂⁻¹(x₂)] ([F1], [F2gen], [Hgen], [Hinv], [Hgen_isEquiv],
      [F2_Hgen]; at [(x₁, p₂)]: [F2], [Hcomp], [Hcomp_eqv]); pairs of
      paths are taken apart with [ap fst].  This general form is the [H']
      and [H''] of the proof of [cor:cokermaps].  Exercise
      [xca:ptd-fibersofcomposites]: the pointing data ([F2_pt], [F1_pt],
      [H_pt]); the pointed triangles are not stated.
    - Definition [def:Im(grphom)]: [Img f :≡ subgrp_group (imsub f)],
      whose classifying type is the set image [im_n 0 (Bf)] of Section 3.9
      by definition; [imincl] ([Bi(f) :≡ fst], pointed by [refl]), [Bp]
      (which is [im_p 0 (Bf)]) with pointing path [Bp_pt], [improj].
      Exercise [xca:p-epi-i-mono]: [imfact_comp] ([i(f) ∘ p(f) = f] as
      homomorphisms), [improj_isepi] (via [lem:trunc-n-connected]),
      [imincl_ismono], [imincl_ismonoC].
    - Definitions [def:Im-fact] ([EpiMono], [Imfact], with
      [EpiMono_comp]) and [def:image] ([img], [prjim]).
    - Lemma [lem:kerandcoker] ([lem_kerandcoker]): [(z, r) ↦ (z, ap_fst r)]
      is an equivalence of the components of the fibers of [Bp(f)] and
      [Bf] ([kc_eqv]); the inverse rebuilds [r] from its first component,
      the second lying in a set ([kc_snd]).
    - Corollary [cor:cokermaps], parts [it:F1] ([cor_cokermaps_F1]) and
      [it:F2-mono] ([cor_cokermaps_F2_mono]): [F₁], [F₂] are the maps of
      [lem:fibersofcomposites] on the components ([F1Hom], [F2Hom]),
      unique since kernel maps are monomorphisms; [F₂] is a
      monomorphism by [ismonoC_first] ([isF2_ismono]).  Part
      [it:monof2->isoF2] ([cor_cokermaps_monof2_isoF2]): [ap_{F₂}] is a
      bijection on loops ([F2k_ap_isInj], [F2k_ap_isSurj]: a loop [g] of
      [Ker(f₂f₁)] has [Uf₂(Uf₁ g) = 1], so [Uf₁ g = 1]), and
      [conn_isEquiv_iff_point].

    Left out (statements only; time limit per result)
    - The exercise after [rem:imageandcokernel] ([xca_ker_coker_stmt],
      with [trivhom]); the other parts of corollary [cor:cokermaps]
      ([cor_cokermaps_..._stmt], with [isF1], [isF2], [F1coker]); exercise
      [xca:abstract-kernel] ([xca_abstract_kernel_stmt], with [Xker]);
      lemma [lem:Im-fact-unique] ([lem_Im_fact_unique_stmt]); remark
      [rem:n-im-ptd-map] ([rem_n_im_ptd_map_stmt], with [Factp], [FactpN]);
      the parts of exercise [ex:charsurinj] not proved in 9.2/9.3
      ([ex_charsurinj_stmt]); the lemma on images of composites
      ([img_comp_stmt]); the exercise after [lem:kerandcoker]
      ([xca_mono_epi_img_stmt]), of which the first part is proved
      ([mono_img]: for a mono the fibers of [Bi] are sets, so [Bp(i)] is
      an equivalence onto the set image); the second part needs that
      epimorphisms are surjective ([epi_surjection_stmt], Section 9.2).
    - Informal: footnotes [ft:cmpnt:UUp->UUp], [ft:(i,p)-equiv], example
      [exa:fibersofcomposites], exercise [xca:fibersofcomposites] and the
      example from linear algebra.
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core.
From SymmetryBook Require Export Subgroups.S02_Epis.

Local Open Scope uf_scope.

(** ** 9.3 Images, kernels and cokernels *)

(** *** Kernels and cokernels *)

Section KerCoker.

  Context `{fe : Funext} {G H : Group} (f : Hom G H).

  Local Notation k0 := (fst (Bf f)).
  Local Notation kp := (snd (Bf f)).

  (** The fibers [(Bf)⁻¹(w)] are groupoids. *)
  Definition fiber_isGrpd (w : utype (BG H)) : isGrpd (fiber k0 w)
    := Sigma_ntype 1 (BG_isGrpd G) (fun z => set_ntype 1 (BG_isGrpd H w (k0 z))).

  Definition shKer : fiber k0 (sh H) := (sh G; kp).

  (** Definition [def:kernel]: [Ker(f) :≡ Aut_{(Bf)⁻¹(sh_H)}(sh_G, Bf_pt)]
      (the book's footnote), with [ker_f] the first projection, pointed
      by [refl]. *)
  Definition Ker : Group := AutG (fiber_isGrpd (sh H)) shKer.

  Definition kermap : Hom Ker G
    := @mkhom Ker G ((fun u : component (fiber k0 (sh H)) shKer => fst (fst u)); refl).

  Definition kermap_ismono : ismono kermap.
  Proof.
    refine (cancel_isInj (USym_isSet G) _). intros h h' e.
    refine (ap_fst_cancel (fun _ => prop_is_set ptrunc_isProp) h h' _).
    refine (ap_fst_cancel (fun z => BG_isGrpd H (sh H) (k0 z)) _ _ _).
    refine ((ap_compose fst fst h)^ @ _ @ ap_compose fst fst h').
    exact ((trans_1p _)^ @ e @ trans_1p _).
  Defined.

  Definition ker : Mono G := (Ker; (kermap; kermap_ismono)).

  (** Definition [def:cokernel]: [coker(f)(w) :≡ ‖(Bf)⁻¹(w)‖₀]. *)
  Definition coker : GSet H := fun w => (strunc (fiber k0 w); strunc_isSet).

  Definition act_coker {w w' : utype (BG H)} (g : w = w') (z : utype (BG G))
    (p : w = k0 z)
    : act coker g (settrunc ((z; p) : fiber k0 w)) = settrunc ((z; g^ @ p) : fiber k0 w').
  Proof. destruct g. exact (ap (fun q => settrunc ((z; q) : fiber k0 w)) (concat_1p p)^). Defined.

  (** Lemma [lem:isTrans(coker)]. *)
  Definition coker_trans : istrans coker.
  Proof.
    apply trunc. exists (settrunc shKer).
    refine (strunc_ind_prop _ (fun _ => ptrunc_isProp) _). intros [z p].
    refine (ptrunc_rec ptrunc_isProp _ (snd (BG_isConn G) (sh G) z)). intro q.
    destruct q. apply trunc. exists (p @ kp^).
    refine (_ @ (act_coker _ _ _)^).
    apply (ap (fun r => settrunc ((sh G; r) : fiber k0 (sh H)))).
    exact ((ap (fun r => r @ p) (inv_pp p kp^) @ concat_pp_p _ _ _
            @ ap (fun r => (kp^)^ @ r) (concat_Vp p) @ concat_p1 _ @ inv_V kp)^).
  Defined.

  (** Remark [rem:imageandcokernel]: the cokernel, pointed at
      [|(sh_G, Bf_pt)|₀], is a subgroup of [H]; the alternative proof via
      [lem:conistrans] is not formalized separately. *)
  Definition imsub : SubGrp H := (coker; (settrunc shKer; coker_trans)).

End KerCoker.

(** Footnote [ft:cmpnt:UUp->UUp]: a pointed map induces a pointed map
    of components (informal). *)

(** The trivial homomorphism, constant at the shape. *)
Definition trivhom (L G : Group) : Hom L G := @mkhom L G ((fun _ => sh G); refl).

(** The exercise after [rem:imageandcokernel] (statement only): (1)
    [f] is a monomorphism iff the kernel is trivial, (2) an epimorphism
    iff the cokernel is contractible, (3) the universal property of the
    kernel. *)
Definition xca_ker_coker_stmt `{Univalence} : Type
  := forall (G H : Group) (f : Hom G H),
       (ismono f <-> Mono_trivial (ker f))
       × (isepi f <-> isContr (el (coker f) (sh H)))
       × (forall (L : Group) (h : Hom L G),
            compG f h = trivhom L H ->
            isContr {k : Hom L (Ker f) & h = compG (kermap f) k}).

(** Lemma [lem:fibersofcomposites], for an arbitrary point [y] of
    [f₂⁻¹(x₂)] instead of [(x₁, p₂)]; this general form is the [H'] and
    [H''] of the proof of [cor:cokermaps].  Pairs of paths are taken
    apart with [ap fst] instead of matching on [pair⁼(p, r)]. *)
Section FibersOfComposites.

  Context {X0 X1 X2 : Type} (f1 : X0 -> X1) (f2 : X1 -> X2) (x2 : X2).

  Definition F1 (w : fiber (f2 ∘ f1) x2) : fiber f2 x2 := (f1 (fst w); snd w).

  Definition F2gen (y : fiber f2 x2) (v : fiber f1 (fst y)) : fiber (f2 ∘ f1) x2
    := (fst v; ap f2 (snd v) ⋅ snd y).

  Definition Hgen (y : fiber f2 x2) (u : fiber F1 y) : fiber f1 (fst y)
    := (fst (fst u); ap fst (snd u)).

  Definition trp_fiber {a b : X1} (p : a = b) (q : x2 = f2 a)
    : trp (fun c => x2 = f2 c) p q = ap f2 p ⋅ q.
  Proof. destruct p. exact refl. Defined.

  Definition Hinv (y : fiber f2 x2) (v : fiber f1 (fst y)) : fiber F1 y
    := ((fst v; trp (fun c => x2 = f2 c) (snd v) (snd y));
        pathpair (Y := fun c => x2 = f2 c) (snd v) refl).

  (** Part 1: [H] is an equivalence with inverse [H⁻¹]. *)
  Definition Hgen_Hinv (y : fiber f2 x2) (v : fiber f1 (fst y)) : Hgen y (Hinv y v) = v
    := ap (fun r => (fst v; r) : fiber f1 (fst y))
          (ap_fst_pathpair (Y := fun c => x2 = f2 c) (snd v) refl).

  Definition Hinv_Hgen (y : fiber f2 x2) (u : fiber F1 y) : Hinv y (Hgen y u) = u.
  Proof.
    destruct u as [[x q] e]. revert y e. refine (paths_ind_r _ _ _). exact refl.
  Defined.

  Definition Hgen_isEquiv (y : fiber f2 x2) : isEquiv (Hgen y)
    := iso_to_isEquiv (Hgen y) (Hinv y) (Hinv_Hgen y) (Hgen_Hinv y).

  (** Part 2: the lower square and its triangles commute by definition. *)
  Definition F1_fst (w : fiber (f2 ∘ f1) x2) : fst (F1 w) = f1 (fst w) := refl.

  (** Part 3: the left upper triangle [F₂ H = fst]. *)
  Definition F2_Hgen (y : fiber f2 x2) (u : fiber F1 y) : F2gen y (Hgen y u) = fst u.
  Proof.
    destruct u as [[x q] e]. revert y e. refine (paths_ind_r _ _ _). exact refl.
  Defined.

  (** The book's [H] and [F₂], at the point [(x₁, p₂)]. *)
  Context (x1 : X1) (p2 : x2 = f2 x1).

  Definition F2 : fiber f1 x1 -> fiber (f2 ∘ f1) x2 := F2gen (x1; p2).

  Definition Hcomp : fiber F1 (x1; p2) -> fiber f1 x1 := Hgen (x1; p2).

  Definition Hcomp_eqv : fiber F1 (x1; p2) ≃ fiber f1 x1 := (Hcomp; Hgen_isEquiv (x1; p2)).

End FibersOfComposites.

(** Exercise [xca:ptd-fibersofcomposites]: with [f₁] pointed by [p₁], the
    points [(x₀, f₂(p₁)p₂)], [(x₁, p₂)] and [(x₀, p₁)] of the three
    fibers make [F₂] pointed by [refl], [F₁] pointed by [pair⁼(p₁, !)],
    and [H] pointed (on the point [((x₀, f₂(p₁)p₂), F₁_pt)] of
    [F₁⁻¹(x₁, p₂)]); the commutation of the triangles as pointed maps is
    left out. *)
Section PtdFibersOfComposites.

  Context {X0 X1 X2 : Type} (f1 : X0 -> X1) (f2 : X1 -> X2) (x0 : X0) (x1 : X1) (x2 : X2)
    (p1 : x1 = f1 x0) (p2 : x2 = f2 x1).

  Definition F2_pt : ((x0; ap f2 p1 ⋅ p2) : fiber (f2 ∘ f1) x2) = F2 f1 f2 x2 x1 p2 (x0; p1)
    := refl.

  Definition F1_pt : ((x1; p2) : fiber f2 x2) = F1 f1 f2 x2 (x0; ap f2 p1 ⋅ p2)
    := pathpair (Y := fun c => x2 = f2 c) p1 (trp_fiber f2 x2 p1 p2).

  Definition H_pt : Hcomp f1 f2 x2 x1 p2 ((x0; ap f2 p1 ⋅ p2); F1_pt) = (x0; p1)
    := ap (fun r => (x0; r) : fiber f1 x1)
          (ap_fst_pathpair (Y := fun c => x2 = f2 c) p1 (trp_fiber f2 x2 p1 p2)).

End PtdFibersOfComposites.

(** Corollary [cor:cokermaps] (parts [it:F1], [it:F2-mono] and
    [it:monof2->isoF2] proved below).  The homomorphisms
    [F₁ : Ker(f₂f₁) → Ker(f₂)] and [F₂ : Ker(f₁) → Ker(f₂f₁)] are
    specified by their defining equations; parts [it:H-equiv],
    [it:Ker-f1-F1], [it:coker-f1-F1] and [it:monof2->isoF2] are stated for
    any such [F₁], [F₂].  Part [it:epif1->equivF'1] uses [F'₁(w)], which
    is [F1] above for the unpointed maps. *)
Section CokerMaps.

  Context `{ua : Univalence} {G0 G1 G2 : Group} (f1 : Hom G0 G1) (f2 : Hom G1 G2).

  Definition isF1 (F : Hom (Ker (compG f2 f1)) (Ker f2)) : Type
    := compG f1 (kermap (compG f2 f1)) = compG (kermap f2) F.

  Definition isF2 (F : Hom (Ker f1) (Ker (compG f2 f1))) : Type
    := kermap f1 = compG (kermap (compG f2 f1)) F.

  (** Part [it:H-equiv]. *)
  Definition cor_cokermaps_H_equiv_stmt : Type
    := forall F, isF1 F -> Iso (Ker F) (Ker f1).

  (** Part [it:F1]. *)
  Definition cor_cokermaps_F1_stmt : Type := isContr {F : _ & isF1 F}.

  (** Part [it:F2-mono]. *)
  Definition cor_cokermaps_F2_mono_stmt : Type
    := isContr {F : _ & isF2 F} × forall F, isF2 F -> ismono F.

  (** Part [it:Ker-f1-F1]. *)
  Definition cor_cokermaps_Ker_f1_F1_stmt : Type
    := forall F1 F2 (m : ismono F2), isF1 F1 -> isF2 F2 ->
         ((Ker f1; (F2; m)) : Mono (Ker (compG f2 f1))) = ker F1.

  (** Part [it:coker-f1-F1]. *)
  Definition cor_cokermaps_coker_f1_F1_stmt : Type
    := forall F1, isF1 F1 -> coker F1 = (fun u => coker f1 (fst (Bf (kermap f2)) u)).

  (** Part [it:monof2->isoF2]. *)
  Definition cor_cokermaps_monof2_isoF2_stmt : Type
    := ismono f2 -> forall F2, isF2 F2 -> isIso F2.

  (** Part [it:epif1->equivF'1]: [tot(‖F'₁(_)‖₀) : Hom_{G₂}(coker(f₂f₁), coker(f₂))]. *)
  Definition F1coker : HomGs (coker (compG f2 f1)) (coker f2)
    := fun w => strunc_rec strunc_isSet (fun d => settrunc (F1 (fst (Bf f1)) (fst (Bf f2)) w d)).

  Definition cor_cokermaps_epif1_equivF1_stmt : Type
    := isepi f1 -> forall w, isEquiv (F1coker w).

  (** Proofs of parts [it:F1] and [it:F2-mono]: [F₁] and [F₂] are the maps
      [F1] and [F2] of [lem:fibersofcomposites] on the components, pointed
      by [F1_pt] and [refl] ([F1Hom], [F2Hom]); they are unique since
      kernel maps are monomorphisms. *)
  Local Notation k1 := (fst (Bf f1)).
  Local Notation kp1 := (snd (Bf f1)).
  Local Notation k2 := (fst (Bf f2)).
  Local Notation kp2 := (snd (Bf f2)).

  Definition F1k (u : utype (BG (Ker (compG f2 f1)))) : utype (BG (Ker f2))
    := (F1 k1 k2 (sh G2) (fst u);
        ptrunc_rec ptrunc_isProp
          (fun r => trunc (F1_pt k1 k2 (sh G0) (sh G1) (sh G2) kp1 kp2 @ ap (F1 k1 k2 (sh G2)) r))
          (snd u)).

  Definition F1Hom : Hom (Ker (compG f2 f1)) (Ker f2)
    := @mkhom (Ker (compG f2 f1)) (Ker f2)
         (F1k; path_sigma_prop (fun _ => ptrunc_isProp)
                 (u := sh (Ker f2)) (v := F1k (sh (Ker (compG f2 f1))))
                 (F1_pt k1 k2 (sh G0) (sh G1) (sh G2) kp1 kp2)).

  Definition F1Hom_isF1 : isF1 F1Hom.
  Proof.
    apply (ap mkhom).
    refine (eqinv (snd (ptw_star (pcomp (Bf f1) (Bf (kermap (compG f2 f1))))
                                 (pcomp (Bf (kermap f2)) (Bf F1Hom))))
              ((fun u => refl); _)).
    refine (_ @ (trans_1p _)^).
    change (kp1 = ap (fun u : utype (BG (Ker f2)) => fst (fst u)) (snd (Bf F1Hom))).
    refine (_ @ (ap_compose (fun u : utype (BG (Ker f2)) => fst u)
                   (fun w : fiber k2 (sh G2) => fst w) (snd (Bf F1Hom)))^).
    refine (_ @ (ap (ap fst) (ap_fst_path_sigma_prop (fun _ => ptrunc_isProp)
                                (u := sh (Ker f2)) (v := F1k (sh (Ker (compG f2 f1))))
                                (F1_pt k1 k2 (sh G0) (sh G1) (sh G2) kp1 kp2)))^).
    exact (ap_fst_pathpair (Y := fun c => sh G2 = k2 c) kp1 (trp_fiber k2 (sh G2) kp1 kp2))^.
  Defined.

  Definition cor_cokermaps_F1 : cor_cokermaps_F1_stmt.
  Proof.
    refine (isProp_inhabited_isContr _ (F1Hom; F1Hom_isF1)).
    intros [F e] [F' e'].
    apply (path_sigma_prop (fun _ => Hom_isSet _ _ _ _)).
    exact (Overture.fst (ismonoC_cancel _) (ismono_ismonoC _ (kermap_ismono f2)) _ F F' (e^ @ e')).
  Defined.

  Definition F2k (u : utype (BG (Ker f1))) : utype (BG (Ker (compG f2 f1)))
    := (F2 k1 k2 (sh G2) (sh G1) kp2 (fst u);
        ptrunc_rec ptrunc_isProp (fun r => trunc (ap (F2 k1 k2 (sh G2) (sh G1) kp2) r)) (snd u)).

  Definition F2Hom : Hom (Ker f1) (Ker (compG f2 f1))
    := @mkhom (Ker f1) (Ker (compG f2 f1))
         (F2k; path_sigma_prop (fun _ => ptrunc_isProp)
                 (u := sh (Ker (compG f2 f1))) (v := F2k (sh (Ker f1))) refl).

  Definition F2Hom_isF2 : isF2 F2Hom.
  Proof.
    apply (ap mkhom).
    refine (eqinv (snd (ptw_star (Bf (kermap f1)) (pcomp (Bf (kermap (compG f2 f1))) (Bf F2Hom))))
              ((fun u => refl); _)).
    refine (_ @ (trans_1p _)^).
    change (refl = ap (fun u : utype (BG (Ker (compG f2 f1))) => fst (fst u)) (snd (Bf F2Hom))).
    refine (_ @ (ap_compose (fun u : utype (BG (Ker (compG f2 f1))) => fst u)
                   (fun w : fiber (fun x => k2 (k1 x)) (sh G2) => fst w) (snd (Bf F2Hom)))^).
    exact (ap (ap fst) (ap_fst_path_sigma_prop (fun _ => ptrunc_isProp)
                          (u := sh (Ker (compG f2 f1))) (v := F2k (sh (Ker f1))) refl))^.
  Defined.

  Definition isF2_ismono (F : Hom (Ker f1) (Ker (compG f2 f1))) (e : isF2 F) : ismono F.
  Proof.
    apply ismonoC_ismono. apply (ismonoC_first F (kermap (compG f2 f1))).
    exact (trp ismonoC e (ismono_ismonoC _ (kermap_ismono f1))).
  Defined.

  Definition cor_cokermaps_F2_mono : cor_cokermaps_F2_mono_stmt.
  Proof.
    refine (isProp_inhabited_isContr _ (F2Hom; F2Hom_isF2); isF2_ismono).
    intros [F e] [F' e'].
    apply (path_sigma_prop (fun _ => Hom_isSet _ _ _ _)).
    exact (Overture.fst (ismonoC_cancel _) (ismono_ismonoC _ (kermap_ismono (compG f2 f1)))
             _ F F' (e^ @ e')).
  Defined.

  (** Part [it:monof2->isoF2]: by [conn_isEquiv_iff_point] it suffices
      that [ap_{F₂}] is a bijection on the loops at the point.  It is
      injective since [F₂] keeps the first component; a loop [g] of
      [Ker(f₂f₁)] has [Uf₂(Uf₁ g) = 1], hence [Uf₁ g = 1] when [f₂] is
      a monomorphism, so [g] lifts to [Ker(f₁)]. *)
  Definition fib_nat {X Y : Type} {f : X -> Y} {y : Y} {u v : fiber f y} (l : u = v)
    : trans (snd u) (ap f (ap fst l)) = snd v.
  Proof. destruct l. exact refl. Defined.

  Definition conj_triv {X : Type} {a b : X} (p : a = b) (A : b = b)
    : trans (trans p A) p⁻¹ = refl -> trans p A = p.
  Proof. destruct p. exact idmap. Defined.

  Local Notation ptK1 := (sh (Ker f1)).

  Definition ffcancel {K : Group} {X : Type} {f : X -> utype (BG K)} {y : utype (BG K)}
    {x0 : fiber f y} {u v : component (fiber f y) x0} (h h' : u = v)
    (e : ap (fun w : component (fiber f y) x0 => fst (fst w)) h
         = ap (fun w : component (fiber f y) x0 => fst (fst w)) h')
    : h = h'.
  Proof.
    refine (ap_fst_cancel (fun _ => prop_is_set ptrunc_isProp) h h' _).
    refine (ap_fst_cancel (fun z => BG_isGrpd K y (f z)) _ _ _).
    exact ((ap_compose (fun w : component (fiber f y) x0 => fst w) (fun w : fiber f y => fst w) h)^
           @ e @ ap_compose (fun w : component (fiber f y) x0 => fst w) (fun w : fiber f y => fst w) h').
  Defined.

  Definition F2k_ff (mu : ptK1 = ptK1)
    : ap (fun w : utype (BG (Ker (compG f2 f1))) => fst (fst w)) (ap F2k mu)
      = ap (fun w : utype (BG (Ker f1)) => fst (fst w)) mu
    := (ap_compose F2k (fun w : utype (BG (Ker (compG f2 f1))) => fst (fst w)) mu)^.

  Definition F2k_ap_isInj : isInj (@ap _ _ F2k ptK1 ptK1).
  Proof.
    apply (cancel_isInj (BG_isGrpd (Ker (compG f2 f1)) _ _)). intros mu mu' e.
    apply ffcancel. exact ((F2k_ff mu)^ @ ap (ap _) e @ F2k_ff mu').
  Defined.

  Definition F2k_ap_isSurj (m2 : ismono f2) : isSurj (@ap _ _ F2k ptK1 ptK1).
  Proof.
    intro l. apply trunc.
    pose (l0 := ap fst l).
    pose (g := ap fst l0 : sh G0 = sh G0).
    pose (c12 := snd (Bf (compG f2 f1))).
    assert (E1 : USymf f1 g = refl).
    { apply (isInj_cancel m2).
      exact ((loops_fun_pcomp (Bf f2) (Bf f1) g)^
             @ ap (fun r => trans r c12⁻¹) (fib_nat l0) @ trans_pV c12 @ (trans_pV kp2)^). }
    pose (mu0 := pathpair (Y := fun z => sh G1 = k1 z) g
                  (trp_fiber k1 (sh G1) g kp1 @ conj_triv kp1 (ap k1 g) E1)
                : shKer f1 = shKer f1).
    exists (path_sigma_prop (fun _ => ptrunc_isProp) (u := ptK1) (v := ptK1) mu0).
    apply ffcancel. refine (_ @ (F2k_ff _)^).
    refine (ap_compose (fun w : utype (BG (Ker (compG f2 f1))) => fst w)
              (fun w : fiber (fun x => k2 (k1 x)) (sh G2) => fst w) l @ _).
    refine (_ @ (ap_compose (fun w : utype (BG (Ker f1)) => fst w)
                   (fun w : fiber k1 (sh G1) => fst w) _)^).
    refine (_ @ ap (ap fst) (ap_fst_path_sigma_prop (fun _ => ptrunc_isProp)
                                (u := ptK1) (v := ptK1) mu0)^).
    exact (ap_fst_pathpair (Y := fun z => sh G1 = k1 z) g _)^.
  Defined.

  Definition F2Hom_isIso (m2 : ismono f2) : isIso F2Hom
    := snd (conn_isEquiv_iff_point F2k (BG_isConn _) (BG_isConn _) ptK1)
         (inj_surj_isEquiv F2k_ap_isInj (F2k_ap_isSurj m2)).

  Definition cor_cokermaps_monof2_isoF2 : cor_cokermaps_monof2_isoF2_stmt
    := fun m2 F e => trp isIso (ap fst (isContr_isProp' (fst cor_cokermaps_F2_mono)
                                          (F2Hom; F2Hom_isF2) (F; e)))
                       (F2Hom_isIso m2).

End CokerMaps.

(** Example [exa:fibersofcomposites] ([B mod_4] followed by [B sgn ∘ prj])
    illustrates [lem:fibersofcomposites] on connected fibers, identifying
    the stabilizer subgroups of [ℤ], [C_4] and [ℤ] (informal; not
    formalized). *)

(** Exercise [xca:fibersofcomposites]: the same for [R_4] followed by
    [B sgn] (informal; not formalized). *)

(** Exercise [xca:abstract-kernel] (statement only): the transitive
    [G]-set [X(f)], pointed at [Bf_pt], gives the kernel as a subgroup,
    and for an epimorphism [X(f)(z)] is [sh_H = Bf(z)]. *)
Section AbstractKernel.

  Context `{ua : Univalence} {G H : Group} (f : Hom G H).

  Local Notation k0 := (fst (Bf f)).
  Local Notation kp := (snd (Bf f)).

  Definition Xker : GSet G
    := fun z => ({p : sh H = k0 z & Ex (fun g : sh G = z => p = ap k0 g ⋅ kp)};
                 Sigma_isSet (BG_isGrpd H _ _) (fun _ => prop_is_set ptrunc_isProp)).

  Definition Xker_pt : el Xker (sh G) := (kp; trunc (refl; refl)).

  Definition xca_abstract_kernel_stmt : Type
    := forall t : istrans Xker,
         (subgrp_to_mono ((Xker; (Xker_pt; t)) : SubGrp G) = ker f)
         × (isepi f -> forall z, el Xker z ≃ (sh H = k0 z)).

End AbstractKernel.

(** *** The image of a homomorphism of groups *)

(** Definition [def:Im(grphom)]: [Im(f)] is the group of the subgroup
    [imsub f] of remark [rem:imageandcokernel]; its classifying type is
    the set image [∑_{w:BH} ‖(Bf)⁻¹(w)‖₀], pointed at
    [(sh_H, |(sh_G, Bf_pt)|₀)]. *)
Section Image.

  Context `{fe : Funext} {G H : Group} (f : Hom G H).

  Local Notation k0 := (fst (Bf f)).
  Local Notation kp := (snd (Bf f)).

  Definition Img : Group := subgrp_group (imsub f).

  Definition Img_BG : utype (BG Img) = im_n 0 k0 := refl.

  (** [Bi(f) :≡ fst], pointed by [refl]. *)
  Definition imincl : Hom Img H := subgrp_incl (imsub f).

  Definition imincl_ismono : ismono imincl := subgrp_incl_ismono (imsub f).

  (** [Bp(f)(z) :≡ (Bf(z), |(z, refl)|₀)], which is [im_p] of Section 3.9;
      the pointing path of exercise [xca:p-epi-i-mono]. *)
  Definition Bp (z : utype (BG G)) : utype (BG Img) := (k0 z; settrunc (z; refl)).

  Definition Bp_is_im_p : Bp = im_p 0 k0 := refl.

  Definition Bp_pt_trunc : act (coker f) kp (settrunc (shKer f)) = settrunc ((sh G; refl) : fiber k0 (k0 (sh G)))
    := act_coker f kp (sh G) kp @ ap (fun r => settrunc ((sh G; r) : fiber k0 (k0 (sh G)))) (concat_Vp kp).

  Definition Bp_pt : sh Img = Bp (sh G)
    := tot_path_act (coker f) kp (settrunc (shKer f))
       @ ap (fun c => (k0 (sh G); c) : utype (BG Img)) Bp_pt_trunc.

  Definition improj : Hom G Img := @mkhom G Img (Bp; Bp_pt).

  (** Exercise [xca:p-epi-i-mono]: [Bf = Bi(f) ∘ Bp(f)] as pointed maps,
      [p(f)] is an epimorphism and [i(f)] a monomorphism. *)
  Definition ap_fst_Bp_pt : ap fst Bp_pt = kp.
  Proof.
    refine (ap_pp fst _ _ @ _).
    refine (ap011 concat (ap_fst_tot_path_act (imsub f) kp (settrunc (shKer f))) _ @ concat_p1 _).
    exact ((ap_compose (fun c => (k0 (sh G); c) : utype (BG Img)) fst Bp_pt_trunc)^
           @ ap_const Bp_pt_trunc (k0 (sh G))).
  Defined.

  Definition imfact_comp : compG imincl improj = f.
  Proof.
    refine (_ @ inc_out f).
    apply (ap mkhom).
    refine (eqinv (snd (ptw_star (pcomp (Bf imincl) (Bf improj)) (Bf f))) ((fun x => refl); _)).
    refine (_ @ ap_fst_Bp_pt). cbn. exact (trans_1p _).
  Defined.

End Image.

Section ImageEpi.

  Context `{ua : Univalence} {G H : Group} (f : Hom G H).

  Definition imincl_ismonoC : ismonoC (imincl f) := ismono_ismonoC (imincl f) (imincl_ismono f).

  Definition improj_isepi : isepi (improj f).
  Proof.
    apply surj_isepi. apply connfib_surjection. intro y.
    exact (strunc_isContr_isConn (im_p_isnConnMap 0 (fst (Bf f)) y)).
  Defined.

End ImageEpi.

(** Definition [def:Im-fact]: the type [Epi(G) ×_Group Mono(H)] of
    epi-mono factorizations, and the map [Im-fact]; we use [MonoC], the
    categorical monomorphisms, which is equivalent to [Mono] by
    [Mono_MonoC_eqv]. *)
Definition EpiMono `{fe : Funext} (G H : Group) : Type
  := {e : Epi G & {m : MonoC H & fst e = fst m}}.

Definition Imfact `{ua : Univalence} {G H : Group} (f : Hom G H) : EpiMono G H
  := ((Img f; (improj f; improj_isepi f)); ((Img f; (imincl f; imincl_ismonoC f)); refl)).

(** The composition map [∘((Z, p, !), (Z', j, !), α) :≡ j ptoe(α) p] of the
    proof below, with [ptoe(α)] by transport of [j] along [α⁻¹]. *)
Definition EpiMono_comp `{fe : Funext} {G H : Group} (w : EpiMono G H) : Hom G H
  := compG (trp (fun Z => Hom Z H) (snd (snd w))⁻¹ (fst (snd (fst (snd w)))))
           (fst (snd (fst w))).

(** Lemma [lem:Im-fact-unique] (statement only). *)
Definition lem_Im_fact_unique_stmt `{ua : Univalence} : Type
  := forall G H : Group, isEquiv (@Imfact _ G H).

(** Remark [rem:n-im-ptd-map] (statement only): factorizations of a
    pointed map through its [n]-image form a contractible type. *)
Definition Factp {X Z : Ustar} (f : X →* Z) : Type
  := {Y : Ustar & {p : X →* Y & {i : Y →* Z & f = pcomp i p}}}.

Definition FactpN (n : trunc_index) {X Z : Ustar} (f : X →* Z) : Type
  := {w : Factp f & isnConnMap n (fst (fst (snd w))) × isnTruncMap n (fst (fst (snd (snd w))))}.

Definition rem_n_im_ptd_map_stmt `{ua : Univalence} : Type
  := forall (n : trunc_index) (X Z : Ustar) (f : X →* Z), isContr (FactpN n f).

(** Footnote [ft:(i,p)-equiv]: the equivalence [(i,p)^h_z :
    ‖f⁻¹(z)‖_n ≃ i⁻¹(z)] (informal; part of the remark). *)

(** Definition [def:image]: the image factorization, with the image
    [img] and the projection to the image [prjim]; this is [Imfact]
    above. *)
Definition img `{ua : Univalence} {G H : Group} (f : Hom G H) : Mono H
  := (Img f; (imincl f; imincl_ismono f)).

Definition prjim `{ua : Univalence} {G H : Group} (f : Hom G H) : Epi G
  := (Img f; (improj f; improj_isepi f)).

(** Exercise [ex:charsurinj].  Proved: (1)(a)⇐(b) [surj_isepi], (b)⇔(c')
    for the connected fibers ([surjection_connfib], [connfib_surjection]),
    (2)(a)⇔(b)⇔(d) ([ismono_iff_ismonoC], [ismono_isCovering],
    [isCovering_ismono]).  The remaining parts are stated. *)
Definition ex_charsurinj_stmt `{ua : Univalence} : Type
  := forall (G H : Group) (f : Hom G H),
       ((isepi f -> isSurj (USymf f))
        × (isepi f <-> isContr (el (coker f) (sh H)))
        × (isepi f <-> isIso (imincl f)))
       × ((ismono f <-> Mono_trivial (ker f))
          × (ismono f <-> isIso (improj f))).

(** The lemma after [ex:charsurinj] on images of composites (statement
    only). *)
Definition img_comp_stmt `{ua : Univalence} : Type
  := forall (G0 G1 G2 : Group) (f1 : Hom G0 G1) (f2 : Hom G1 G2),
       let u := compG (improj f2) (imincl f1) in
       (img (compG f2 f1)
        = (Img u; (compG (imincl f2) (imincl u);
                   ismonoC_ismono _ (ismonoC_comp _ _ (imincl_ismonoC u) (imincl_ismonoC f2)))))
       × (prjim (compG f2 f1)
          = (Img u; (compG (improj u) (improj f1);
                     isepi_comp _ _ (improj_isepi f1) (improj_isepi u)))).

(** Lemma [lem:kerandcoker] (proved below). *)
Definition lem_kerandcoker_stmt `{ua : Univalence} : Type
  := forall (G H : Group) (f : Hom G H), ker (improj f) = ker f.

(** Proof of [lem:kerandcoker]: [(Bp)⁻¹(sh_{Im f}) → (Bf)⁻¹(sh_H)],
    [(z, r) ↦ (z, ap_fst(r))] ([kc_Phi]) restricts to an equivalence of
    the components ([kc_eqv]); the inverse reconstructs [r] from its
    first component, using the membership in the component of
    [(sh_G, Bf_pt)] for the second ([kc_snd]), which lives in a set. *)
Section KerAndCoker.

  Context `{ua : Univalence} {G H : Group} (f : Hom G H).

  Local Notation k0 := (fst (Bf f)).
  Local Notation kp := (snd (Bf f)).
  Local Notation FP := (fiber (Bp f) (sh (Img f))).
  Local Notation FF := (fiber k0 (sh H)).

  Definition kc_Phi (u : FP) : FF := (fst u; ap fst (snd u)).

  Definition kc_P0 : shKer f = kc_Phi (shKer (improj f))
    := ap (fun t => (sh G; t) : FF) (ap_fst_Bp_pt f)^.

  Definition kc_PhiC (y : component FP (shKer (improj f))) : component FF (shKer f)
    := (kc_Phi (fst y); ptrunc_rec ptrunc_isProp (fun r => trunc (kc_P0 @ ap kc_Phi r)) (snd y)).

  Definition kc_shift {w : utype (BG H)} {u v : fiber k0 w} (r0 : u = v)
    : ((fst u; (snd v)^ @ snd u) : fiber k0 (k0 (fst v))) = (fst v; refl).
  Proof. destruct r0. destruct u as [a p]. exact (ap (fun t => (a; t) : fiber k0 (k0 a)) (concat_Vp p)). Defined.

  Definition kc_snd (z : utype (BG G)) (q : sh H = k0 z) (c : ptrunc (shKer f = (z; q)))
    : trp (el (coker f)) q (settrunc (shKer f)) = settrunc ((z; refl) : fiber k0 (k0 z)).
  Proof.
    refine (act_coker f q (sh G) kp @ _).
    refine (ptrunc_rec (strunc_isSet _ _) _ c). intro r0.
    exact (ap settrunc (kc_shift r0)).
  Defined.

  Definition kc_r (z : utype (BG G)) (q : sh H = k0 z) (c : ptrunc (shKer f = (z; q)))
    : sh (Img f) = Bp f z
    := pathpair (Y := el (coker f)) q (kc_snd z q c).

  Definition kc_mem (v : FF) (c : ptrunc (shKer f = v))
    : ptrunc (shKer (improj f) = ((fst v; kc_r (fst v) (snd v) c) : FP)).
  Proof.
    refine (ptrunc_rec ptrunc_isProp _ c). intro r0. destruct r0. apply trunc.
    apply (ap (fun r => (sh G; r) : FP)).
    apply (ap_fst_cancel (fun w => strunc_isSet (T := fiber k0 w))).
    exact (ap_fst_Bp_pt f @ (ap_fst_pathpair _ _)^).
  Defined.

  Definition kc_PsiC (w : component FF (shKer f)) : component FP (shKer (improj f))
    := ((fst (fst w); kc_r (fst (fst w)) (snd (fst w)) (snd w)); kc_mem (fst w) (snd w)).

  Definition kc_eqv : component FP (shKer (improj f)) ≃ component FF (shKer f).
  Proof.
    refine (mkEqv kc_PhiC kc_PsiC _ _).
    - intros [[z r] c].
      apply (path_sigma_prop (fun _ => ptrunc_isProp)). cbn.
      apply (ap (fun t => (z; t) : FP)).
      apply (ap_fst_cancel (fun w => strunc_isSet (T := fiber k0 w))).
      exact (ap_fst_pathpair _ _).
    - intros [[z q] c].
      apply (path_sigma_prop (fun _ => ptrunc_isProp)). cbn.
      exact (ap (fun t => (z; t) : FF) (ap_fst_pathpair (Y := el (coker f)) q (kc_snd z q c))
             : kc_Phi (z; kc_r z q c) = (z; q)).
  Defined.

  Definition kc_pt : sh (Ker f) = kc_PhiC (sh (Ker (improj f)))
    := path_sigma_prop (fun _ => ptrunc_isProp)
         (u := sh (Ker f)) (v := kc_PhiC (sh (Ker (improj f)))) kc_P0.

  Definition kc_pmap : BG (Ker (improj f)) →* BG (Ker f) := (kc_PhiC; kc_pt).

  Definition lem_kerandcoker_pf : ker (improj f) = ker f.
  Proof.
    refine (Mono_path (ker (improj f)) (ker f) (kc_pmap; snd kc_eqv) _).
    refine (eqinv (snd (ptw_star (pcomp (Bf (kermap f)) kc_pmap)
                                 (Bf (kermap (improj f)))))
              ((fun y => refl); _)).
    cbn. refine (trans_1p _ @ _).
    refine (ap_compose (@fst FF (fun v => ptrunc (shKer f = v))) (@fst _ _) kc_pt @ _).
    refine (ap (ap (@fst _ _)) (ap_fst_path_sigma_prop (fun _ => ptrunc_isProp)
              (u := sh (Ker f)) (v := kc_PhiC (sh (Ker (improj f)))) kc_P0) @ _).
    refine ((ap_compose (fun t => (sh G; t) : FF) (@fst _ _) _)^ @ _).
    exact (ap_const _ _).
  Defined.

End KerAndCoker.

Definition lem_kerandcoker `{ua : Univalence} : lem_kerandcoker_stmt
  := fun G H f => lem_kerandcoker_pf f.

(** The exercise after [lem:kerandcoker] (statement only): a
    monomorphism is identified with the inclusion of its image, and an
    epimorphism with the projection to its image. *)
Definition xca_mono_epi_img_stmt `{ua : Univalence} : Type
  := (forall (G H : Group) (m : Mono H), m = img (fst (snd m)))
     × (forall (G H : Group) (e : Epi G), e = prjim (fst (snd e))).

(** The first part: for a monomorphism the fibers of [Bi] are sets
    ([ismono_isCovering]), so [Bp(i)] is an equivalence onto the set
    image, compatible with the inclusions ([Mono_path]).  The second part
    needs that epimorphisms are surjective ([epi_surjection_stmt]). *)
Definition mono_img `{ua : Univalence} {H : Group} (m : Mono H) : m = img (fst (snd m)).
Proof.
  destruct m as [G [i mi]].
  pose (c := ismono_isCovering i mi).
  pose (g := fun w : utype (BG (Img i)) => fst (strunc_rec (c (fst w)) idmap (snd w))).
  assert (fg : forall w, Bp i (g w) = w).
  { intros [y t]. revert t.
    refine (strunc_ind _ (fun _ => BG_isGrpd (Img i) _ _) _). intros [z p].
    exact (paths_ind_r (fst (Bf i) z)
             (fun y0 p0 => Bp i (g (y0; settrunc ((z; p0) : fiber (fst (Bf i)) y0)))
                           = (y0; settrunc ((z; p0) : fiber (fst (Bf i)) y0))) refl y p). }
  pose (e := ((Bp i; Bp_pt i); iso_to_isEquiv (Bp i) g (fun _ => refl) fg) : BG G ≃* BG (Img i)).
  refine (Mono_path ((G; (i; mi)) : Mono H) (img i) e _).
  exact (ap (fun r => (fst (Bf i); r) : BG G →* BG H) (trans_1p _ @ ap_fst_Bp_pt i)).
Defined.

(** The example from linear algebra after this exercise (informal). *)
