(** * Section 9.2 Epimorphisms, and an equivalent take on monomorphisms

    Part of Chapter 9 ([subgroups.tex]); see [Subgroups.v] for an
    overview of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Lemma [lem:injmonosurjepiSet]: parts [it:injmono] ([injmono]) and
      [it:surjepi] ([surjepi_to], [surjepi_from], [surjepi]); the converse
      of [it:surjepi] tests against [D :≡ Prop_U], in a larger universe,
      which is allowed since [D] ranges over all sets.
    - Definitions [def:monomorphism] and [def:epimorphism]: [ismonoC]
      (the name [ismono] is taken by [def:typeofmono], Section 5.3),
      [isepi], [MonoC], [Epi], [MonoC_proper], [Epi_proper], as
      [isMono]/[isEpi] in [GroupCat] (Section 6.3), with cancellation forms
      [ismonoC_cancel], [isepi_cancel].
    - [USymf_cancel]: [USym] acts injectively on homomorphisms, by
      [abstr_hom_eqv] (Section 7.5).
    - Example [exa:projections-epi] ([prG1_isepi], [prG2_isepi]), via
      [surj_isepi].
    - Exercise [xca:mono1st-epi2nd] ([ismonoC_comp], [isepi_comp],
      [ismonoC_first], [isepi_second]).
    - Lemma [lem:eq-mono-cover]: [it:mono] ⇔ [it:injection]
      ([ismonoC_ismono], [ismono_ismonoC], [ismono_iff_ismonoC]) and
      [it:injection] ⇔ [it:cover] ([ismono_isCovering],
      [isCovering_ismono]), via [cor:fib-vs-path] with [Q :≡ isProp] and
      the comparison of [Ωk] with [ap_k] ([loops_isInj_ap],
      [ap_isInj_loops]).  [Mono_MonoC_eqv]: the two types of
      monomorphisms agree.
    - Lemma [lem:epi-surj]: [it:surjection] ⇒ [it:epi]
      ([surjection_isepi]) and [it:surjection] ⇔ [it:connfib]
      ([surjection_connfib], [connfib_surjection]), via
      [cor:fib-vs-path] with [Q :≡ ‖_‖].
    - From Section 5.3, placed here since the inverse uses
      [ismono_isCovering]: lemma [lem:SubG=MonoG] with exercise
      [xca:SubG=MonoG] ([lem_SubG_MonoG]; the inverse [mono_to_subgrp]
      takes the [G]-set of fibers of [Bi], [fibX]), and corollary
      [lem:setofsubgroups] ([lem_setofsubgroups], from [SubGrp_isSet] of
      Section 5.3).

    Left out (statements only)
    - [it:epi] ⇒ [it:surjection] ([epi_surjection_stmt]): the book's proof
      goes through construction [con:monos-are-equalizers]
      ([con_monos_are_equalizers_stmt], with [isEqualizer]), whose
      implementation is still a draft, and the image factorization of
      Section 9.3.
    - Lemma [lem:epimonoiso] is hidden (\wip) and not formalized.
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core.
From SymmetryBook Require Export ConGroups.ConGroups.

Local Open Scope uf_scope.

(** ** 9.2 Epimorphisms, and an equivalent take on monomorphisms *)

(** Lemma [lem:injmonosurjepiSet]. *)
Section InjMonoSurjEpiSet.

  Context `{fe : Funext} {B C : Type} (sC : isSet C) (f : B -> C).

  (** Part [it:injmono]. *)
  Definition injmono
    : isInj f <-> (forall (A : Type) (sA : isSet A) (g h : A -> B), f ∘ g = f ∘ h -> g = h).
  Proof.
    split.
    - intros j A sA g h e.
      apply ptw_inv. intro a. exact (isInj_cancel j _ _ (ap (fun k => k a) e)).
    - intro c. apply (cancel_isInj sC). intros b b' e.
      refine (ap (fun k => k triv) (c True (prop_is_set True_isProp)
                                      (fun _ => b) (fun _ => b') _)).
      exact (ptw_inv (fun _ => e)).
  Defined.

  (** Part [it:surjepi].  The converse tests against [D :≡ Prop_U],
      which lives in a larger universe than [B] and [C]; this is allowed
      since [D] ranges over all sets. *)
  Definition surjepi_to
    : isSurj f -> forall (D : Type) (sD : isSet D) (g h : C -> D), g ∘ f = h ∘ f -> g = h.
  Proof.
    intros s D sD g h e. apply ptw_inv. intro c.
    refine (ptrunc_rec (sD _ _) _ (s c)). intros [b p].
    exact (ap g p @ ap (fun u => u b) e @ (ap h p)^).
  Defined.

  Definition surjepi_from `{ua : Univalence}
    : (forall (D : Type) (sD : isSet D) (g h : C -> D), g ∘ f = h ∘ f -> g = h) -> isSurj f.
  Proof.
    intros c y.
    pose (g := fun y' : C => ((ptrunc (fiber f y'); ptrunc_isProp) : PropU)).
    pose (h := fun _ : C => ((True; True_isProp) : PropU)).
    refine (trp fst (ap (fun k => k y) (c PropU PropU_isSet g h _))^ triv).
    apply ptw_inv. intro b.
    exact (path_PropU (P := g (f b)) (Q := h (f b)) (fun _ => triv) (fun _ => trunc (b; refl))).
  Defined.

  Definition surjepi `{ua : Univalence}
    : isSurj f <-> (forall (D : Type) (sD : isSet D) (g h : C -> D), g ∘ f = h ∘ f -> g = h)
    := (surjepi_to, surjepi_from).

End InjMonoSurjEpiSet.

(** The reformulation after [lem:injmonosurjepiSet]: injections are the
    maps for which postcomposition, surjections those for which
    precomposition, gives injections of sets of functions (informal; it
    is [injmono] and [surjepi] together with [cancel_isInj]). *)

(** Definitions [def:monomorphism] and [def:epimorphism]: the categorical
    notions in [GroupCat] (Section 6.3).  The name [ismono] is taken by
    definition [def:typeofmono] of Section 5.3; we write [ismonoC] for
    the categorical notion and show in [lem:eq-mono-cover] below that the
    two are equivalent. *)
Section MonoEpi.

  Context `{fe : Funext}.

  Definition ismonoC {G H : Group} (f : Hom G H) : Type := isMono (C := GroupCat) f.

  Definition isepi {G H : Group} (f : Hom G H) : Type := isEpi (C := GroupCat) f.

  Definition ismonoC_isProp {G H : Group} (f : Hom G H) : isProp (ismonoC f)
    := Pi_isProp (fun F => isInj_isProp _ _).

  Definition isepi_isProp {G H : Group} (f : Hom G H) : isProp (isepi f)
    := Pi_isProp (fun I => isInj_isProp _ _).

  Definition MonoC (H : Group) : Type := {G : Group & {i : Hom G H & ismonoC i}}.

  Definition Epi (G : Group) : Type := {H : Group & {f : Hom G H & isepi f}}.

  Definition MonoC_proper {H : Group} (m : MonoC H) : Type := ¬ isIso (fst (snd m)).

  Definition Epi_proper {G : Group} (e : Epi G) : Type := ¬ isIso (fst (snd e)).

  (** The cancellation forms. *)
  Definition ismonoC_cancel {G H : Group} (f : Hom G H)
    : ismonoC f <-> (forall (F : Group) (g h : Hom F G), compG f g = compG f h -> g = h)
    := isMono_cancel GroupCat_isPreCat f.

  Definition isepi_cancel {G H : Group} (f : Hom G H)
    : isepi f <-> (forall (I : Group) (g h : Hom H I), compG g f = compG h f -> g = h)
    := isEpi_cancel GroupCat_isPreCat f.

End MonoEpi.

(** [USym] acts injectively on homomorphisms, by [abstr_hom_eqv]
    (Section 7.5). *)
Definition USymf_cancel `{fe : Funext} {G H : Group} (g h : Hom G H)
  (e : USymf g = USymf h) : g = h
  := isInj_cancel (isEquiv_isInj (abstr_hom_isEquiv G H)) g h
       (path_absHom (abstr_hom g) (abstr_hom h) (fun s => ap (fun u => u s) e)).

(** If [USymf f] is surjective, [f] is an epimorphism (part of
    [lem:epi-surj] below, used for the next example). *)
Definition surj_isepi `{fe : Funext} {G H : Group} (f : Hom G H)
  (s : isSurj (USymf f)) : isepi f.
Proof.
  apply (Overture.snd (isepi_cancel f)). intros I g h e.
  apply USymf_cancel.
  refine (surjepi_to (USymf f) s _ (USym_isSet I) _ _ _).
  exact ((USym_compose f g)^ @ ap USymf e @ USym_compose f h).
Defined.

(** Example [exa:projections-epi]: the projections from [G₁ × G₂] are
    epimorphisms; [USymf prG1] and [USymf prG2] are split surjections. *)
Section ProjectionsEpi.

  Context `{fe : Funext} (G1 G2 : Group).

  Definition USymf_prG1 (s : USym G1)
    : USymf (prG1 G1 G2) (ap (fun z => (z; sh G2) : utype (BG (prodG G1 G2))) s) = s
    := loops_fun_refl (X := BG (prodG G1 G2)) (Y := BG G1) (fun z => fst z) _
       @ (ap_compose (fun z => (z; sh G2) : utype (BG (prodG G1 G2))) (fun z => fst z) s)^
       @ ap_idmap s.

  Definition USymf_prG2 (s : USym G2)
    : USymf (prG2 G1 G2) (ap (fun z => (sh G1; z) : utype (BG (prodG G1 G2))) s) = s
    := loops_fun_refl (X := BG (prodG G1 G2)) (Y := BG G2) (fun z => snd z) _
       @ (ap_compose (fun z => (sh G1; z) : utype (BG (prodG G1 G2))) (fun z => snd z) s)^
       @ ap_idmap s.

  Definition prG1_isepi : isepi (prG1 G1 G2)
    := surj_isepi _ (fun s => trunc (_; (USymf_prG1 s)^)).

  Definition prG2_isepi : isepi (prG2 G1 G2)
    := surj_isepi _ (fun s => trunc (_; (USymf_prG2 s)^)).

End ProjectionsEpi.

(** Exercise [xca:mono1st-epi2nd]. *)
Section MonoFirstEpiSecond.

  Context `{fe : Funext} {G1 G2 G3 : Group} (f1 : Hom G1 G2) (f2 : Hom G2 G3).

  Definition ismonoC_comp (m1 : ismonoC f1) (m2 : ismonoC f2) : ismonoC (compG f2 f1).
  Proof.
    apply (Overture.snd (ismonoC_cancel _)). intros F g h e.
    apply (Overture.fst (ismonoC_cancel f1) m1).
    apply (Overture.fst (ismonoC_cancel f2) m2).
    exact (compG_assoc f2 f1 g @ e @ (compG_assoc f2 f1 h)^).
  Defined.

  Definition isepi_comp (e1 : isepi f1) (e2 : isepi f2) : isepi (compG f2 f1).
  Proof.
    apply (Overture.snd (isepi_cancel _)). intros I g h e.
    apply (Overture.fst (isepi_cancel f2) e2).
    apply (Overture.fst (isepi_cancel f1) e1).
    exact ((compG_assoc g f2 f1)^ @ e @ compG_assoc h f2 f1).
  Defined.

  Definition ismonoC_first (m : ismonoC (compG f2 f1)) : ismonoC f1.
  Proof.
    apply (Overture.snd (ismonoC_cancel _)). intros F g h e.
    apply (Overture.fst (ismonoC_cancel _) m).
    exact ((compG_assoc f2 f1 g)^ @ ap (compG f2) e @ compG_assoc f2 f1 h).
  Defined.

  Definition isepi_second (e : isepi (compG f2 f1)) : isepi f2.
  Proof.
    apply (Overture.snd (isepi_cancel _)). intros I g h p.
    apply (Overture.fst (isepi_cancel _) e).
    exact (compG_assoc g f2 f1 @ ap (fun u => compG u f1) p @ (compG_assoc h f2 f1)^).
  Defined.

End MonoFirstEpiSecond.

(** Figure [fig:Znatural] is [Znatural] of Section 4.4. *)

(** For a pointed map [k] into a groupoid, [Ωk] is [ap_k] at the base
    point followed by conjugation with the pointing path, an equivalence;
    so [Ωk] is injective (surjective) iff [ap_k] is. *)
Section LoopsVsAp.

  Definition conj_path {Y : Type} {y b : Y} (e : y = b) (q : b = b) : y = y
    := e⁻¹ ⋅ (q ⋅ e).

  Definition conj_path_isEquiv {Y : Type} {y b : Y} (e : y = b) : isEquiv (conj_path e).
  Proof.
    destruct e.
    exact (isEquiv_homotopic (id _) _ (fun q => (trans_1p q)⁻¹) (id_isEquiv _)).
  Defined.

  Context {X Y : Ustar} (k : X →* Y) (sY : isSet (pt Y = pt Y))
    (sY' : isSet (fst k (pt X) = fst k (pt X))).

  Definition loops_fun_is_conj (p : pt X = pt X)
    : loops_fun k p = conj_path (snd k) (ap (fst k) p)
    := refl.

  Definition loops_isInj_ap : isInj (loops_fun k) -> isInj (@ap _ _ (fst k) (pt X) (pt X)).
  Proof.
    intro j. apply (cancel_isInj sY'). intros p p' e.
    exact (isInj_cancel j p p' (ap (conj_path (snd k)) e)).
  Defined.

  Definition ap_isInj_loops : isInj (@ap _ _ (fst k) (pt X) (pt X)) -> isInj (loops_fun k).
  Proof.
    intro j. apply (cancel_isInj sY). intros p p' e.
    exact (isInj_cancel j p p'
             (isInj_cancel (isEquiv_isInj (conj_path_isEquiv (snd k))) _ _ e)).
  Defined.

  Definition loops_isSurj_ap : isSurj (loops_fun k) -> isSurj (@ap _ _ (fst k) (pt X) (pt X)).
  Proof.
    intros s r.
    refine (ptrunc_rec ptrunc_isProp _ (s (conj_path (snd k) r))). intros [p e].
    exact (trunc (p; isInj_cancel (isEquiv_isInj (conj_path_isEquiv (snd k))) _ _ e)).
  Defined.

  Definition ap_isSurj_loops : isSurj (@ap _ _ (fst k) (pt X) (pt X)) -> isSurj (loops_fun k).
  Proof.
    intros s q.
    pose (c := conj_path_isEquiv (snd k)).
    refine (ptrunc_rec ptrunc_isProp _ (s (eqinv c q))). intros [p e].
    exact (trunc (p; (eqinv_r c q)^ @ ap (conj_path (snd k)) e)).
  Defined.

End LoopsVsAp.

(** Lemma [lem:eq-mono-cover] (also labelled [lem:eq-epi-conn]). *)
Section EqMonoCover.

  Context `{ua : Univalence} {G H : Group} (f : Hom G H).

  (** Part [it:mono] implies part [it:injection], taking [F :≡ ℤ]. *)
  Definition ismonoC_ismono (m : ismonoC f) : ismono f.
  Proof.
    apply (cancel_isInj (USym_isSet H)). intros a a' e.
    pose (eG := Hom_ZZ_eqv G). pose (eH := Hom_ZZ_eqv H).
    refine ((eqinv_r (snd eG) a)^ @ ap (fst eG) _ @ eqinv_r (snd eG) a').
    apply (Overture.fst (ismonoC_cancel f) m).
    apply (isInj_cancel (isEquiv_isInj (snd eH))).
    exact (Znatural G H f _ @ ap (USymf f) (eqinv_r (snd eG) a) @ e
           @ (ap (USymf f) (eqinv_r (snd eG) a'))^ @ (Znatural G H f _)^).
  Defined.

  (** Part [it:injection] implies part [it:mono], as in the footnote. *)
  Definition ismono_ismonoC (j : ismono f) : ismonoC f.
  Proof.
    apply (Overture.snd (ismonoC_cancel f)). intros F g h e.
    apply USymf_cancel. apply ptw_inv. intro s.
    apply (isInj_cancel j).
    exact (ap (fun u => u s) ((USym_compose g f)^ @ ap USymf e @ USym_compose h f)).
  Defined.

  Definition ismono_iff_ismonoC : ismono f <-> ismonoC f
    := (ismono_ismonoC, ismonoC_ismono).

  Local Notation k0 := (fst (Bf f)).

  Definition sH' : isSet (k0 (sh G) = k0 (sh G)) := BG_isGrpd H _ _.

  (** Part [it:injection] iff part [it:cover]: by [cor:fib-vs-path]
      ([Q_paths_fibers_point], [fibers_paths_Q]) with [Q :≡ isProp],
      using that [BG] is connected and [f] is pointed. *)
  Definition ismono_isCovering (j : ismono f) : isCovering k0.
  Proof.
    intros y z z'. revert y z z'.
    refine (Q_paths_fibers_point k0 isProp isProp_Qinv isProp_isProp (BG_isConn G) (sh G) _).
    exact (loops_isInj_ap (Bf f) sH' j).
  Defined.

  Definition isCovering_ismono (c : isCovering k0) : ismono f.
  Proof.
    apply (ap_isInj_loops (Bf f) (USym_isSet H)).
    exact (fibers_paths_Q k0 isProp isProp_Qinv (fun b => c b) (sh G) (sh G)).
  Defined.

End EqMonoCover.

(** The type [Mono(H)] of definition [def:monomorphism] is that of
    definition [def:typeofmono] (Section 5.3). *)
Definition Mono_MonoC_eqv `{ua : Univalence} (H : Group) : Mono H ≃ MonoC H.
Proof.
  refine (tot (fun G => tot (fun i => ismono_ismonoC i)); _).
  apply tot_isEquiv. intro G. apply tot_isEquiv. intro i.
  exact (snd (Eqv_of_props (isInj_isProp _ _) (ismonoC_isProp i)
                (ismono_ismonoC i) (ismonoC_ismono i))).
Defined.

(** Lemma [lem:epi-surj]. *)
Section EpiSurj.

  Context `{ua : Univalence} {G H : Group} (f : Hom G H).

  Local Notation k0 := (fst (Bf f)).

  (** Part [it:surjection] implies part [it:epi] ([surj_isepi] above). *)
  Definition surjection_isepi : isSurj (USymf f) -> isepi f := surj_isepi f.

  (** Part [it:surjection] iff part [it:connfib]: [cor:fib-vs-path] with
      [Q :≡ ‖_‖]; the fibers are inhabited since [BH] is connected. *)
  Definition surjection_connfib (s : isSurj (USymf f)) : forall y, isConn (fiber k0 y).
  Proof.
    intro y. split.
    - refine (ptrunc_rec ptrunc_isProp (fun p => trunc (sh G; p)) (snd (BG_isConn H) y _)).
    - revert y.
      refine (Q_paths_fibers_point k0 ptrunc (fun X Y e => ptrunc_rec ptrunc_isProp (fun x => trunc (fst e x)))
                (fun _ => ptrunc_isProp) (BG_isConn G) (sh G) _).
      exact (loops_isSurj_ap (Bf f) s).
  Defined.

  Definition connfib_surjection (c : forall y, isConn (fiber k0 y)) : isSurj (USymf f).
  Proof.
    apply (ap_isSurj_loops (Bf f)).
    exact (fibers_paths_Q k0 ptrunc (fun X Y e => ptrunc_rec ptrunc_isProp (fun x => trunc (fst e x)))
             (fun b => snd (c b)) (sh G) (sh G)).
  Defined.

  (** Part [it:epi] implies part [it:surjection] (statement only): the
      book derives it from construction [con:monos-are-equalizers]
      below, whose implementation is still a draft, via the image
      factorization of Section 9.3. *)
  Definition epi_surjection_stmt : Type := isepi f -> isSurj (USymf f).

End EpiSurj.

(** Construction [con:monos-are-equalizers] (statement only; the
    implementation in the book is a draft): every monomorphism is an
    equalizer. *)
Definition isEqualizer `{fe : Funext} {H G W : Group} (i : Hom H G) (φ ψ : Hom G W) : Type
  := (compG φ i = compG ψ i)
     × forall (F : Group) (k : Hom F G), compG φ k = compG ψ k ->
         isContr {l : Hom F H & k = compG i l}.

Definition con_monos_are_equalizers_stmt `{fe : Funext} : Type
  := forall (G H : Group) (i : Hom H G), ismonoC i ->
       {W : Group & {φ : Hom G W & {ψ : Hom G W & isEqualizer i φ ψ}}}.

(** Lemma [lem:SubG=MonoG] with exercise [xca:SubG=MonoG] (from 5.3;
    placed here since the inverse uses [ismono_isCovering]): the map
    [F : Sub(G) → Mono(G)] is an equivalence.  The inverse sends
    [i : H → G] to the [G]-set of fibers of [Bi], pointed at
    [(sh_H, Bi_pt)]. *)
Section SubGMonoG.

  Context `{ua : Univalence} {G : Group}.

  Definition fib_path {A B : Type} (f : A -> B) {a : B} {b : A} (p : a = f b)
    : ((a; (b; p)) : {z : B & fiber f z}) = (f b; (b; refl))
    := paths_ind_r (f b) (fun a0 p0 => ((a0; (b; p0)) : {z : B & fiber f z}) = (f b; (b; refl)))
         refl a p.

  Definition ap_fst_fib_path {A B : Type} (f : A -> B) {a : B} {b : A} (p : a = f b)
    : ap fst (fib_path f p) = p
    := paths_ind_r (f b) (fun a0 p0 => ap fst (fib_path f p0) = p0) refl a p.

  Definition trp_path_GSet {X Y : GSet G} (e : forall z, el X z ≃ el Y z) (z : utype (BG G))
    (x : el X z) : trp (fun Y0 : GSet G => el Y0 z) (path_GSet e) x = fst (e z) x.
  Proof.
    refine ((ptoe_ap (fun Y0 : GSet G => el Y0 z) (path_GSet e) x)^ @ _).
    refine (ap (fun q => ptoe q x)
              (ap_compose (fun Y0 : GSet G => Y0 z) (fun T : SetU => fst T) (path_GSet e)) @ _).
    refine (ap (fun q => ptoe (ap (fun T : SetU => fst T) q) x)
              (ptw (eqinv_r (funext X Y) (fun z0 => path_SetU (e z0))) z) @ _).
    refine (ap (fun q => ptoe q x) (ap_fst_sigma_prop _ _) @ _).
    exact (ap (fun e' => fst e' x) (ptoe_etop (e z))).
  Defined.

  Definition SubGrp_path {X Y : GSet G} {x : el X (sh G)} {y : el Y (sh G)}
    {t : istrans X} {t' : istrans Y} (α : X = Y)
    (h : trp (fun Y0 : GSet G => el Y0 (sh G)) α x = y)
    : ((X; (x; t)) : SubGrp G) = (Y; (y; t')).
  Proof.
    destruct α. destruct h.
    exact (ap (fun t0 => (X; (x; t0)) : SubGrp G) (istrans_isProp X t t')).
  Defined.

  Section FibGSet.

    Context {H : Group} (i : Hom H G) (mi : ismono i).

    Local Notation k0 := (fst (Bf i)).
    Local Notation kp := (snd (Bf i)).

    Definition fibX : GSet G := fun z => (fiber k0 z; ismono_isCovering i mi z).

    Definition fibX_conn : isConn (TotG fibX).
    Proof.
      refine (trunc ((k0 (sh H); (sh H; refl)) : TotG fibX); _).
      intros [z [x p]] [z' [x' p']].
      refine (ptrunc_rec ptrunc_isProp _ (snd (BG_isConn H) x x')). intro q.
      destruct q. exact (trunc (fib_path k0 p @ (fib_path k0 p')^)).
    Defined.

    Definition mono_to_subgrp : SubGrp G
      := (fibX; ((sh H; kp); trans_of_conn fibX fibX_conn)).

    Definition mono_subgrp_mono : ((H; (i; mi)) : Mono G) = subgrp_to_mono mono_to_subgrp.
    Proof.
      pose (f := fun x : utype (BG H) => (k0 x; (x; refl)) : TotG fibX).
      assert (fg : forall w : TotG fibX, f (fst (snd w)) = w).
      { intros [z [x p]]. exact (fib_path k0 p)^. }
      refine (Mono_path ((H; (i; mi)) : Mono G) (subgrp_to_mono mono_to_subgrp)
                (((f; fib_path k0 kp);
                  iso_to_isEquiv f (fun w : TotG fibX => fst (snd w)) (fun _ => refl) fg)
                 : BG H ≃* BG (subgrp_group mono_to_subgrp)) _).
      exact (ap (fun r => (k0; r) : BG H →* BG G) (trans_1p _ @ ap_fst_fib_path k0 kp)).
    Defined.

  End FibGSet.

  Definition subgrp_mono_subgrp (S : SubGrp G)
    : mono_to_subgrp (subgrp_incl S) (subgrp_incl_ismono S) = S.
  Proof.
    destruct S as [X [x t]]. unfold mono_to_subgrp.
    exact (SubGrp_path (path_GSet (X := fibX (subgrp_incl (X; (x; t))) (subgrp_incl_ismono (X; (x; t))))
                                  (Y := X) (fun z => Eqv_inv (fst_fiber_eqv (el X) z)))
                       (trp_path_GSet _ (sh G) _)).
  Defined.

  Definition lem_SubG_MonoG_eqv : isEquiv (fun S : SubGrp G => subgrp_to_mono S).
  Proof.
    refine (iso_to_isEquiv (fun S : SubGrp G => subgrp_to_mono S)
              (fun m : Mono G => mono_to_subgrp (fst (snd m)) (snd (snd m)))
              subgrp_mono_subgrp _).
    intros [H [i mi]]. exact (mono_subgrp_mono i mi)^.
  Defined.

End SubGMonoG.

Definition lem_SubG_MonoG `{ua : Univalence} : lem_SubG_MonoG_stmt
  := fun G => @lem_SubG_MonoG_eqv ua G.

Definition lem_setofsubgroups `{ua : Univalence} : lem_setofsubgroups_stmt
  := fun G => is_ntype_Eqv 0 (_; lem_SubG_MonoG G) (SubGrp_isSet G).
