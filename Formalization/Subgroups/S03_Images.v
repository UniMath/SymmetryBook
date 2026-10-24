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

    Left out (statements only; time limit per result)
    - The exercise after [rem:imageandcokernel] ([xca_ker_coker_stmt],
      with [trivhom]); corollary [cor:cokermaps], all parts
      ([cor_cokermaps_..._stmt], with [isF1], [isF2], [F1coker]); exercise
      [xca:abstract-kernel] ([xca_abstract_kernel_stmt], with [Xker]);
      lemma [lem:Im-fact-unique] ([lem_Im_fact_unique_stmt]); remark
      [rem:n-im-ptd-map] ([rem_n_im_ptd_map_stmt], with [Factp], [FactpN]);
      the parts of exercise [ex:charsurinj] not proved in 9.2/9.3
      ([ex_charsurinj_stmt]); the lemma on images of composites
      ([img_comp_stmt]); lemma [lem:kerandcoker]
      ([lem_kerandcoker_stmt]); the exercise after it
      ([xca_mono_epi_img_stmt]).
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

(** Corollary [cor:cokermaps] (statements only).  The homomorphisms
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

(** Lemma [lem:kerandcoker] (statement only). *)
Definition lem_kerandcoker_stmt `{ua : Univalence} : Type
  := forall (G H : Group) (f : Hom G H), ker (improj f) = ker f.

(** The exercise after [lem:kerandcoker] (statement only): a
    monomorphism is identified with the inclusion of its image, and an
    epimorphism with the projection to its image. *)
Definition xca_mono_epi_img_stmt `{ua : Univalence} : Type
  := (forall (G H : Group) (m : Mono H), m = img (fst (snd m)))
     × (forall (G H : Group) (e : Epi G), e = prjim (fst (snd e))).

(** The example from linear algebra after this exercise (informal). *)
