(** * Section 9.6 Intersecting with normal subgroups

    Part of Chapter 9 ([subgroups.tex]); see [Subgroups.v] for an
    overview of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Lemma [lem:whatSylow2needs]: the second part is [imincl_ismono]
      ([whatSylow2needs_mono]), with [H/(N ∩ H)] the image of [f i] as in
      the proof; the first part ([lem_whatSylow2needs], with [N ∩ H] the
      pullback [pullbackG] of Section 8.4) is pasting of pullbacks,
      [((z, q, !), h, p) ↦ (h, q · f(p))] ([PhiS], [PhiC_eqv]), and
      needs neither that [f] is an epimorphism nor that [i] is a
      monomorphism.
    - [H]-fixed points ([isHfix]) and lemma [lem:thereisaconjugate]
      ([thereisaconjugate]).  NOTE for the book text: the conjugate
      subgroup [g H] should be pointed by [Bf_pt g] (first [g], then
      [Bf_pt]), not [g⁻¹ Bf_pt], which does not typecheck; same in the
      proof.
    - Informal: the two exercises (abstract intersection; the section in
      terms of [Sub(G)]).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core.
From SymmetryBook Require Export Subgroups.S05_Normal.

Local Open Scope uf_scope.

(** ** 9.6 Intersecting with normal subgroups *)

(** The first exercise of this section, to define the intersection of
    abstract subgroups (informal; the concrete intersection is
    [intersectionG], Section 8.4). *)

(** Lemma [lem:whatSylow2needs].  The first part: [N ∩ H] is (isomorphic
    to) the kernel of [f i] (proved below).  For the second part the
    proof identifies [H/(N ∩ H)] with [Im(f i)], and the induced
    homomorphism with [i(f i)], which is a monomorphism
    ([imincl_ismono], Section 9.3). *)
Definition lem_whatSylow2needs_stmt `{ua : Univalence} : Type
  := forall (G G' H : Group) (f : Hom G G') (e : isepi f) (i : Hom H G) (m : ismono i),
       {k : Iso (pullbackG (kermap f) i) (Ker (compG f i)) &
         compG (kermap (compG f i)) (fst k) = pullbackG_pr2 (kermap f) i}.

(** Proof of the first part, which needs neither [e] nor [m]: pasting
    pullbacks, [((z, q, !), h, p) ↦ (h, q · f(p))] ([PhiS]) is an
    equivalence of the components ([PhiC], [PsiC]). *)
Section WhatSylow2Needs.

  Context `{ua : Univalence} {G G' H : Group} (f : Hom G G') (i : Hom H G).

  Local Notation k0 := (fst (Bf f)).
  Local Notation kp := (snd (Bf f)).
  Local Notation Bi := (fst (Bf i)).
  Local Notation ip := (snd (Bf i)).
  Local Notation PB := (pullbackB (kermap f) i).
  Local Notation pbpt := (pullbackB_pt (kermap f) i).
  Local Notation KF := (fiber (fst (Bf (compG f i))) (sh G')).
  Local Notation kfpt := (shKer (compG f i)).

  Definition PhiS (x : PB) : KF := (snd (fst x); snd (fst (fst (fst x))) @ ap k0 (snd x)).

  Definition PhiS_pt : kfpt = PhiS pbpt
    := ap (fun r => (sh H; r) : KF)
          (trans_is_concat kp (ap k0 ip) @ ap (fun t => kp @ ap k0 t) (trans_1p ip)^).

  Definition PhiC (y : component PB pbpt) : component KF kfpt
    := (PhiS (fst y); ptrunc_rec ptrunc_isProp (fun r => trunc (PhiS_pt @ ap PhiS r)) (snd y)).

  Definition fib_move {z z' : utype (BG G)} (g : z = z') (q : sh G' = k0 z)
    : ((z; q) : fiber k0 (sh G')) = (z'; q @ ap k0 g).
  Proof. destruct g. exact (ap (fun t => (z; t) : fiber k0 (sh G')) (concat_p1 q)^). Defined.

  Definition pb_qpath {h0 : utype (BG H)} {q1 q2 : sh G' = k0 (Bi h0)} (e : q1 = q2)
    (c1 : ptrunc (shKer f = (Bi h0; q1))) (c2 : ptrunc (shKer f = (Bi h0; q2)))
    : ((((((Bi h0; q1) : fiber k0 (sh G')); c1); h0); refl) : PB)
      = (((((Bi h0; q2) : fiber k0 (sh G')); c2); h0); refl).
  Proof.
    destruct e.
    exact (ap (fun c => ((((((Bi h0; q1) : fiber k0 (sh G')); c); h0); refl) : PB))
              (ptrunc_isProp c1 c2)).
  Defined.

  Definition pb_move {z : utype (BG G)} {h0 : utype (BG H)} (p : z = Bi h0) (q : sh G' = k0 z)
    (c : ptrunc (shKer f = (z; q))) (c' : ptrunc (shKer f = (Bi h0; q @ ap k0 p)))
    : ((((((z; q) : fiber k0 (sh G')); c); h0); p) : PB)
      = (((((Bi h0; q @ ap k0 p) : fiber k0 (sh G')); c'); h0); refl).
  Proof.
    revert z p q c c'.
    refine (paths_ind_r (Bi h0)
              (fun z0 p0 => forall (q : sh G' = k0 z0) (c : ptrunc (shKer f = (z0; q)))
                              (c' : ptrunc (shKer f = (Bi h0; q @ ap k0 p0))),
                 ((((((z0; q) : fiber k0 (sh G')); c); h0); p0) : PB)
                 = (((((Bi h0; q @ ap k0 p0) : fiber k0 (sh G')); c'); h0); refl)) _).
    intros q c c'. exact (pb_qpath (concat_p1 q)^ c c').
  Defined.

  Definition mem1 {w0 : KF} (r : kfpt = w0) : shKer f = ((Bi (fst w0); snd w0) : fiber k0 (sh G')).
  Proof.
    destruct r.
    exact (fib_move ip kp @ ap (fun t => (Bi (sh H); t) : fiber k0 (sh G')) (trans_is_concat _ _)^).
  Defined.

  Definition mem2 {w0 : KF} (r : kfpt = w0) (c : ptrunc (shKer f = (Bi (fst w0); snd w0)))
    : pbpt = (((((Bi (fst w0); snd w0) : fiber k0 (sh G')); c); fst w0); refl).
  Proof.
    destruct r.
    refine (pb_move (trans refl ip) kp (trunc refl) (trunc (fib_move _ kp)) @ _).
    apply pb_qpath. exact (ap (fun t => kp @ ap k0 t) (trans_1p ip) @ (trans_is_concat _ _)^).
  Defined.

  Definition PsiC (w : component KF kfpt) : component PB pbpt.
  Proof.
    pose (c1 := ptrunc_rec ptrunc_isProp (fun r => trunc (mem1 r)) (snd w)).
    exact (((((((Bi (fst (fst w)); snd (fst w)) : fiber k0 (sh G')); c1); fst (fst w)); refl);
           ptrunc_rec ptrunc_isProp (fun r => trunc (mem2 r c1)) (snd w))).
  Defined.

  Definition PhiC_eqv : component PB pbpt ≃ component KF kfpt.
  Proof.
    refine (mkEqv PhiC PsiC _ _).
    - intros [[[[[z q] c] h0] p] cp].
      apply (path_sigma_prop (fun _ => ptrunc_isProp)). cbn.
      exact (pb_move p q c _)^.
    - intros [[h0 q] c].
      apply (path_sigma_prop (fun _ => ptrunc_isProp)). cbn.
      exact (ap (fun r => (h0; r) : KF) (concat_p1 q)).
  Defined.

  Definition PhiC_pt : sh (Ker (compG f i)) = PhiC (sh (pullbackG (kermap f) i))
    := path_sigma_prop (fun _ => ptrunc_isProp)
         (u := sh (Ker (compG f i))) (v := PhiC (sh (pullbackG (kermap f) i))) PhiS_pt.

  Definition PhiHom : Hom (pullbackG (kermap f) i) (Ker (compG f i))
    := @mkhom (pullbackG (kermap f) i) (Ker (compG f i)) (PhiC; PhiC_pt).

  Definition PhiHom_comp : compG (kermap (compG f i)) PhiHom = pullbackG_pr2 (kermap f) i.
  Proof.
    apply (ap mkhom).
    refine (eqinv (snd (ptw_star (pcomp (Bf (kermap (compG f i))) (Bf PhiHom))
                                 (Bf (pullbackG_pr2 (kermap f) i))))
              ((fun y => refl); _)).
    cbn. refine (trans_1p _ @ _).
    refine (ap_compose (@fst KF (fun v => ptrunc (kfpt = v))) (@fst _ _) PhiC_pt @ _).
    refine (ap (ap (@fst _ _)) (ap_fst_path_sigma_prop (fun _ => ptrunc_isProp)
              (u := sh (Ker (compG f i))) (v := PhiC (sh (pullbackG (kermap f) i))) PhiS_pt) @ _).
    refine ((ap_compose (fun r => (sh H; r) : KF) (@fst _ _) _)^ @ _).
    exact (ap_const _ _).
  Defined.

End WhatSylow2Needs.

Definition lem_whatSylow2needs `{ua : Univalence} : lem_whatSylow2needs_stmt
  := fun G G' H f e i m => ((PhiHom f i; snd (PhiC_eqv f i)); PhiHom_comp f i).

Definition whatSylow2needs_mono `{fe : Funext} {G G' H : Group} (f : Hom G G') (i : Hom H G)
  : ismono (imincl (compG f i))
  := imincl_ismono (compG f i).

(** The second exercise: the above in terms of [Sub(G)] (informal). *)

(** [H]-fixed points: for a homomorphism given by [F : BH_÷ → BG_÷] and
    [p : sh_G = F(sh_H)], [x : X(sh_G)] is an [H]-fixed point if
    [x = X(p⁻¹)(f(sh_H))] for some fixed point [f : ∏_v X(F(v))] of [F^*X]. *)
Definition isHfix {G H : Group} (X : GSet G) (F : utype (BG H) -> utype (BG G))
  (p : sh G = F (sh H)) (x : el X (sh G)) : Type
  := Ex (fun f : forall v, el X (F v) => x = act X p^ (f (sh H))).

(** Lemma [lem:thereisaconjugate].  The conjugate subgroup [g H] is
    pointed by [g] followed by [p] ([g @ p] in the library's diagrammatic
    order, the book's [Bf_pt g]).  NOTE for the book text: the book
    writes [g⁻¹ Bf_pt], which does not typecheck; the computation in the
    proof needs [Bf_pt g]. *)
Definition thereisaconjugate {G H : Group} (X : GSet G) (F : utype (BG H) -> utype (BG G))
  (p : sh G = F (sh H)) (x : el X (sh G)) (g : USym G)
  : isHfix X F p (act X g x) <-> isHfix X F (g @ p) x.
Proof.
  split; refine (ptrunc_rec ptrunc_isProp _); intros [f e]; apply trunc; exists f.
  - refine ((transport_Vp (el X) g x)^ @ ap (act X g^) e @ _).
    exact ((transport_pp (el X) _ _ _)^ @ ap (fun r => act X r (f (sh H))) (inv_pp g p)^).
  - refine (ap (act X g) e @ _).
    refine ((transport_pp (el X) _ _ _)^ @ _).
    exact (ap (fun r => act X r (f (sh H)))
              (ap (fun r => r @ g) (inv_pp g p) @ concat_pp_p _ _ _
               @ ap (fun r => p^ @ r) (concat_Vp g) @ concat_p1 _)).
Defined.
