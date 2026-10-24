(** * Section 9.6 Intersecting with normal subgroups

    Part of Chapter 9 ([subgroups.tex]); see [Subgroups.v] for an
    overview of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Lemma [lem:whatSylow2needs]: the second part is [imincl_ismono]
      ([whatSylow2needs_mono]), with [H/(N ∩ H)] the image of [f i] as in
      the proof; the first part is stated ([lem_whatSylow2needs_stmt]),
      with [N ∩ H] the pullback [pullbackG] of Section 8.4.
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

(** Lemma [lem:whatSylow2needs].  The first part is stated only: [N ∩ H]
    is (isomorphic to) the kernel of [f i].  For the second part the
    proof identifies [H/(N ∩ H)] with [Im(f i)], and the induced
    homomorphism with [i(f i)], which is a monomorphism
    ([imincl_ismono], Section 9.3). *)
Definition lem_whatSylow2needs_stmt `{ua : Univalence} : Type
  := forall (G G' H : Group) (f : Hom G G') (e : isepi f) (i : Hom H G) (m : ismono i),
       {k : Iso (pullbackG (kermap f) i) (Ker (compG f i)) &
         compG (kermap (compG f i)) (fst k) = pullbackG_pr2 (kermap f) i}.

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
