(** * Section 8.4 The pullback

    Part of Chapter 8 ([congp.tex]); see [ConGroups.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - The pullback ([def:pullback]) and its universal property
      ([xca:univpropofpullback]) are formalized in Section 6.8
      ([Cats/S08_Limits.v]), where [cats.tex] defines them.
    - Definition [def:intersectionand unionofsets] ([sub_inter],
      [sub_union]); the book's union [A(s) + B(s)] is not a family of
      propositions, so we truncate it.  NOTE for the book text.
      Exercise [xca:intersectionpullbackofsets](1)
      ([pullback_inter_eqv]) and (2), part
      [xca:cardinalityintersectionunion] ([xca_card_union_inter], via
      [A ⨿ B ≃ (A ∪ B) ⨿ (A ∩ B)], [union_inter_eqv]).
    - Definition [def:intersectionofgroups]: [pullbackG f f'] (the
      component at [(sh_H, sh_{H'}, p_{f'} p_f⁻¹)]), with its projections,
      and [intersectionG] of two monomorphisms.
    - The exercise on [Hom(K, H ×_G H')] and [U(H ×_G H')]
      ([pullbackG_univ]; the last part, about abstract groups, is not
      stated separately).  Identifications in the pullback are pairs of
      identifications with a commuting square ([pb_path], [pb_nat],
      [pb_path_eta]), which is a proposition since [BG] is a groupoid;
      [U(H ×_G H')] is the pullback of [USymf f] and [USymf f']
      ([pbU_eqv]), and [Hom(K, H ×_G H')] is the type of pairs of pointed
      maps with a pointed homotopy ([PBdata], [pbPhi_eqv], [pbHom_eqv]).

    Left out (statements only, no proofs yet; time limit per result)
    - Example [ex:pullbackandgcd] ([ex_pullbackandgcd_stmt]) and the
      example [L ℤ = a ℤ ∩ b ℤ] ([lcm_intersection_stmt], with [dgHom]).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Spaces.Nat.Core Spaces.Nat.Division
  Spaces.Circle Spaces.Finite.Finite.
From SymmetryBook Require Export ConGroups.S03_Wreath.

Local Open Scope uf_scope.

(** ** 8.4 The pullback *)

(** Example [ex:pullbackandgcd] (statement only): the pullback of the
    [a]-fold and the [b]-fold coverings of the circle is
    [S1 × BC_{gcd(a,b)}]. *)
Definition ex_pullbackandgcd_stmt `{Univalence} : Type
  := forall i j : ℕ,
       pullback (dg (S i)) (dg (S j))
       ≃ (S1 × utype (BG (CG (pred (nat_gcd (S i) (S j)))))).

(** Definition [def:intersectionand unionofsets]: intersection and union
    of subsets (the union is the propositional truncation of the sum, so
    that it is again a subset). *)
Definition sub_inter {S : Type} (P Q : Sub S) : Sub S
  := fun s => ((fst (P s) × fst (Q s)); prod_isProp (snd (P s)) (snd (Q s))).

Definition sub_union {S : Type} (P Q : Sub S) : Sub S
  := fun s => ptrunc_PropU (fst (P s) ⨿ fst (Q s)).

(** Exercise [xca:intersectionpullbackofsets](1). *)
Definition pullback_inter_eqv {S : Type} (P Q : Sub S)
  : pullback (fun x : carrier P => fst x) (fun y : carrier Q => fst y)
    ≃ carrier (sub_inter P Q).
Proof.
  refine (mkEqv
    (fun w : pullback (fun x : carrier P => fst x) (fun y : carrier Q => fst y) =>
       exist (fun s => fst (sub_inter P Q s)) (fst (prB w))
         ((snd (prB w); trp (fun s => fst (Q s)) (snd w)⁻¹ (snd (prC w)))
          : fst (P (fst (prB w))) × fst (Q (fst (prB w)))))
    (fun v : carrier (sub_inter P Q) =>
       (((((fst v; fst (snd v)) : carrier P); ((fst v; snd (snd v)) : carrier Q))
         : carrier P × carrier Q); refl))
    _ _).
  - intros [[[s x] [s' y]] p]. cbn in p. destruct p. exact refl.
  - intros [s [x y]]. exact refl.
Defined.

(** Exercise [xca:intersectionpullbackofsets](2), part
    [xca:cardinalityintersectionunion]:
    for subsets of a finite set (with finite carriers),
    [|A| + |B| = |A ∪ B| + |A ∩ B|]. *)
Definition xca_card_union_inter_stmt `{Univalence} : Type
  := forall (S : Type) (P Q : Sub S)
            (hP : isFinSet (carrier P)) (hQ : isFinSet (carrier Q))
            (hU : isFinSet (carrier (sub_union P Q))) (hI : isFinSet (carrier (sub_inter P Q))),
       add (cardF hP) (cardF hQ) = add (cardF hU) (cardF hI).

(** The proof: [A ⨿ B ≃ (A ∪ B) ⨿ (A ∩ B)], sending an element of [A]
    to [A ∩ B] if it is in [B]; membership in [B] is decidable on [A]
    and hence on [A ∪ B], since [A ∩ B] and [A] are finite. *)
Section CardUnionInter.

  Context `{Univalence} {S : Type} (P Q : Sub S)
    (FP : Finite (carrier P)) (FI : Finite (carrier (sub_inter P Q))).

  Definition carrier_path {R : Sub S} {s s' : S} (r : fst (R s)) (r' : fst (R s')) (e : s = s')
    : ((s; r) : carrier R) = (s'; r')
    := path_sigma_prop (fun t => snd (R t)) (u := (s; r)) (v := (s'; r')) e.

  Definition decQ_P (s : S) (p : fst (P s)) : isDecidable (fst (Q s)).
  Proof.
    pose (T := {i : carrier (sub_inter P Q) & ((fst i; fst (snd i)) : carrier P) = (s; p)}).
    refine (ptrunc_rec (lem_isProp (snd (Q s))) _ (merely_decidable_finite T)).
    intros [[i e]|n].
    - exact (inl (trp (fun t => fst (Q t)) (ap fst e) (snd (snd i)))).
    - exact (inr (fun q => n ((s; (p; q)); refl))).
  Defined.

  Definition decQ_U (s : S) (u : fst (sub_union P Q s)) : isDecidable (fst (Q s))
    := ptrunc_rec (lem_isProp (snd (Q s)))
         (fun w => match w with inl p => decQ_P s p | inr q => inl q end) u.

  Definition P_of_U (s : S) (n : ¬ fst (Q s)) (u : fst (sub_union P Q s)) : fst (P s)
    := ptrunc_rec (snd (P s)) (fun w => match w with inl p => p | inr q => match n q with end end) u.

  Definition union_inter_fwd (x : carrier P ⨿ carrier Q)
    : carrier (sub_union P Q) ⨿ carrier (sub_inter P Q)
    := match x with
       | inl (s; p) => match decQ_P s p with
                       | inl q => inr (s; (p; q))
                       | inr _ => inl (s; trunc (inl p))
                       end
       | inr (s; q) => inl (s; trunc (inr q))
       end.

  Definition union_inter_bwd (y : carrier (sub_union P Q) ⨿ carrier (sub_inter P Q))
    : carrier P ⨿ carrier Q
    := match y with
       | inl (s; u) => match decQ_U s u with
                       | inl q => inr (s; q)
                       | inr n => inl (s; P_of_U s n u)
                       end
       | inr (s; (p; q)) => inl (s; p)
       end.

  Definition union_inter_eqv
    : (carrier P ⨿ carrier Q) ≃ (carrier (sub_union P Q) ⨿ carrier (sub_inter P Q)).
  Proof.
    refine (mkEqv union_inter_fwd union_inter_bwd _ _).
    - intros [[s p]|[s q]]; cbn.
      + unfold union_inter_fwd, union_inter_bwd, decQ_U; cbn.
        destruct (decQ_P s p) as [q|n]; cbn.
        * exact refl.
        * destruct (decQ_P s p) as [q|n']; [destruct (n q)|].
          exact (ap inl (carrier_path _ _ refl)).
      + exact refl.
    - intros [[s u]|[s [p q]]]; cbn.
      + destruct (decQ_U s u) as [q|n]; cbn.
        * exact (ap inl (carrier_path _ _ refl)).
        * destruct (decQ_P s (P_of_U s n u)) as [q|n']; cbn.
          -- destruct (n q).
          -- exact (ap inl (carrier_path _ _ refl)).
      + destruct (decQ_P s p) as [q'|n]; cbn.
        * exact (ap inr (carrier_path (R := sub_inter P Q) _ _ refl)).
        * destruct (n q).
  Defined.

End CardUnionInter.

Definition xca_card_union_inter `{Univalence} : xca_card_union_inter_stmt.
Proof.
  intros S P Q hP hQ hU hI.
  pose (FP := isFinSet_Finite hP). pose (FQ := isFinSet_Finite hQ).
  pose (FU := isFinSet_Finite hU). pose (FI := isFinSet_Finite hI).
  refine (ap011 add (cardF_fcard hP) (cardF_fcard hQ) @ _
          @ (ap011 add (cardF_fcard hU) (cardF_fcard hI))^).
  refine (nat_add_comm _ _ @ (fcard_sum _ _)^ @ _ @ fcard_sum _ _ @ nat_add_comm _ _).
  exact (fcard_equiv' (Equiv_of_Eqv (union_inter_eqv P Q FP FI))).
Defined.

(** Definition [def:intersectionofgroups]: the pullback of groups, the
    component of [BH ×_{BG} BH'] at [(sh_H, sh_{H'}, p_{f'} p_f⁻¹)]. *)
Section PullbackGroups.

  Context `{fe : Funext} {H H' G : Group} (f : Hom H G) (f' : Hom H' G).

  Definition pullbackB : Type := pullback (fst (Bf f)) (fst (Bf f')).

  Definition pullbackB_isGrpd : isGrpd pullbackB
    := Sigma_isGrpd (Sigma_isGrpd (BG_isGrpd H) (fun _ => BG_isGrpd H'))
         (fun _ => set_isGrpd (BG_isGrpd G _ _)).

  Definition pullbackB_pt : pullbackB
    := (((sh H; sh H') : utype (BG H) × utype (BG H')); snd (Bf f') ⋅ (snd (Bf f))⁻¹).

  Definition pullbackG : Group := AutG pullbackB_isGrpd pullbackB_pt.

  (** The projections are homomorphisms. *)
  Definition pullbackG_pr1 : Hom pullbackG H
    := mkhom (((fun w : component pullbackB pullbackB_pt => prB (fst w)); refl)
                : BG pullbackG →* BG H).

  Definition pullbackG_pr2 : Hom pullbackG H'
    := mkhom (((fun w : component pullbackB pullbackB_pt => prC (fst w)); refl)
                : BG pullbackG →* BG H').

End PullbackGroups.

(** The intersection of two monomorphisms is their pullback. *)
Definition intersectionG `{Funext} {G : Group} (m m' : Mono G) : Group
  := pullbackG (fst (snd m)) (fst (snd m')).

(** The example [Lℤ = aℤ ∩ bℤ] (statement only): with [a ↦ (dg_a, refl)]
    the subgroup [aℤ], the pullback of [aℤ] and [bℤ] is [ℤ], included
    by [dg_L] for [L] the least common multiple. *)
Definition dgHom `{Univalence} (n : ℕ) : Hom ZZ ZZ := mkhom ((dg n; refl) : BG ZZ →* BG ZZ).

Definition lcm_intersection_stmt `{Univalence} : Type
  := forall i j : ℕ,
       {k : Hom ZZ (pullbackG (dgHom (S i)) (dgHom (S j))) &
         isIso k
         × (compG (dgHom (S i)) (compG (pullbackG_pr1 (dgHom (S i)) (dgHom (S j))) k)
            = dgHom (nat_lcm (S i) (S j)))}.

(** The exercise on [Hom(K, H ×_G H')] and [U(H ×_G H')] (proved below,
    [pullbackG_univ]). *)
Definition pullbackG_univ_stmt `{Funext} : Type
  := forall (H H' G K : Group) (f : Hom H G) (f' : Hom H' G),
       (pullback (fun k : Hom K H => compG f k) (fun k : Hom K H' => compG f' k)
        ≃ Hom K (pullbackG f f'))
       × (pullback (USymf f) (USymf f') ≃ USym (pullbackG f f')).

(** Proof of the exercise.  Identifications in [pullbackB] are given by
    identifications [p], [q] of the components with a commuting square
    ([pb_path], [pb_nat], [pb_path_eta]); the square is a proposition,
    since [BG] is a groupoid. *)
Definition conj_sq_fw {A : Type} {x y z : A} (a : x = y) (b : x = z) (t : y = y) (t' : z = z)
  : trans a⁻¹ b @ t' = t @ trans a⁻¹ b -> trans (trans a t) a⁻¹ = trans (trans b t') b⁻¹.
Proof.
  destruct b, a. intro e.
  exact (trans_1p t @ (concat_p1 t)^ @ e^ @ concat_1p t' @ (trans_1p t')^).
Defined.

Definition conj_sq_bw {A : Type} {x y z : A} (a : x = y) (b : x = z) (t : y = y) (t' : z = z)
  : trans (trans a t) a⁻¹ = trans (trans b t') b⁻¹ -> trans a⁻¹ b @ t' = t @ trans a⁻¹ b.
Proof.
  destruct b, a. intro e.
  exact (concat_1p t' @ (trans_1p t')^ @ e^ @ trans_1p t @ (concat_p1 t)^).
Defined.

Definition pb_pt_sq {A : Type} {x y z y2 z2 : A} (a : x = y) (b : x = z) (P : y = y2) (Q : z = z2)
  (h : y2 = z2) : trans a⁻¹ b @ Q = P @ h -> h ⋅ trans a P = trans b Q.
Proof.
  destruct b, Q, h, a. intro e.
  exact (trans_1p P @ ((concat_p1 P)^ @ e^ @ concat_p1 _)).
Defined.

Definition pb_pt_sq_bw {A : Type} {x y z y2 z2 : A} (a : x = y) (b : x = z) (P : y = y2) (Q : z = z2)
  (h : y2 = z2) : h ⋅ trans a P = trans b Q -> trans a⁻¹ b @ Q = P @ h.
Proof.
  destruct b, Q, h, a. intro e.
  exact (concat_p1 _ @ ((trans_1p P)^ @ e)^ @ (concat_p1 P)^).
Defined.

Definition cancel_2path {A : Type} {x y z : A} (α : x = y) (β : z = y) : (α^ @ (α @ β^)) @ β = refl.
Proof. destruct β, α. exact refl. Defined.

Section PullbackUniv.

  Context `{fe : Funext} {H H' G : Group} (f : Hom H G) (f' : Hom H' G).

  Local Notation k := (fst (Bf f)).
  Local Notation k' := (fst (Bf f')).
  Local Notation PB := (pullbackB f f').

  Definition pb_path {u v : PB} (p : prB u = prB v) (q : prC u = prC v)
    (s : snd u @ ap k' q = ap k p @ snd v) : u = v.
  Proof.
    destruct u as [[b c] r], v as [[b' c'] r']. cbn in *. destruct p, q.
    exact (ap (fun t => ((((b; c) : utype (BG H) × utype (BG H')); t) : PB))
              ((concat_p1 r)^ @ s @ concat_1p r')).
  Defined.

  Definition ap_prB_pb_path {u v : PB} (p : prB u = prB v) (q : prC u = prC v)
    (s : snd u @ ap k' q = ap k p @ snd v) : ap prB (pb_path p q s) = p.
  Proof.
    destruct u as [[b c] r], v as [[b' c'] r']. cbn in *. destruct p, q.
    exact ((ap_compose (fun t => ((((b; c) : utype (BG H) × utype (BG H')); t) : PB)) prB
              ((concat_p1 r)^ @ s @ concat_1p r'))^
           @ ap_const ((concat_p1 r)^ @ s @ concat_1p r') _).
  Defined.

  Definition ap_prC_pb_path {u v : PB} (p : prB u = prB v) (q : prC u = prC v)
    (s : snd u @ ap k' q = ap k p @ snd v) : ap prC (pb_path p q s) = q.
  Proof.
    destruct u as [[b c] r], v as [[b' c'] r']. cbn in *. destruct p, q.
    exact ((ap_compose (fun t => ((((b; c) : utype (BG H) × utype (BG H')); t) : PB)) prC
              ((concat_p1 r)^ @ s @ concat_1p r'))^
           @ ap_const ((concat_p1 r)^ @ s @ concat_1p r') _).
  Defined.

  Definition pb_nat {u v : PB} (l : u = v) : snd u @ ap k' (ap prC l) = ap k (ap prB l) @ snd v.
  Proof. destruct l. exact (concat_p1 _ @ (concat_1p _)^). Defined.

  Definition pb_path_eta {u v : PB} (l : u = v) : pb_path (ap prB l) (ap prC l) (pb_nat l) = l.
  Proof.
    destruct l. destruct u as [[b c] r]. cbn.
    exact (ap (ap (fun t => ((((b; c) : utype (BG H) × utype (BG H')); t) : PB)))
              (cancel_2path (concat_p1 r) (concat_1p r))).
  Defined.

  Definition pb_path_congr {u v : PB} {p p' : prB u = prB v} {q q' : prC u = prC v}
    (s : snd u @ ap k' q = ap k p @ snd v) (s' : snd u @ ap k' q' = ap k p' @ snd v)
    (ep : p = p') (eq : q = q') : pb_path p q s = pb_path p' q' s'.
  Proof.
    destruct ep, eq. exact (ap (pb_path p q) (BG_isGrpd G _ _ _ _ s s')).
  Defined.

  Local Notation pbpt := (pullbackB_pt f f').
  Local Notation lp := (USym_AutG_eqv (pullbackB_isGrpd f f') pbpt).

  (** The symmetries of [H ×_G H'] map to the pullback of [USymf f] and
      [USymf f'], by [l ↦ (ap prB l, ap prC l)]. *)
  Definition pbU (l : USym (pullbackG f f')) : pullback (USymf f) (USymf f')
    := (((ap prB (fst lp l); ap prC (fst lp l)) : USym H × USym H');
        conj_sq_fw (snd (Bf f)) (snd (Bf f')) _ _ (pb_nat (fst lp l))).

  Definition pbU_isInj : isInj pbU.
  Proof.
    apply (cancel_isInj (Sigma_isSet (Sigma_isSet (USym_isSet H) (fun _ => USym_isSet H'))
                           (fun _ => prop_is_set (USym_isSet G _ _)))).
    intros l1 l2 e.
    apply (isInj_cancel (isEquiv_isInj (snd lp))).
    pose (e12 := eqinv (snd (path_prod_eqv _ _ _ _)) (ap fst e)).
    exact ((pb_path_eta (fst lp l1))^
           @ pb_path_congr (u := pbpt) (v := pbpt) (pb_nat (fst lp l1)) (pb_nat (fst lp l2))
               (fst e12) (snd e12)
           @ pb_path_eta (fst lp l2)).
  Defined.

  Definition pbU_isSurj : isSurj pbU.
  Proof.
    intros [[a a'] e]. apply trunc.
    pose (s0 := conj_sq_bw (snd (Bf f)) (snd (Bf f')) _ _ e).
    pose (l := pb_path (u := pbpt) (v := pbpt) a a' s0).
    exists (eqinv (snd lp) l).
    apply (path_sigma_prop (fun _ => USym_isSet G _ _)). cbn.
    refine (_ @ ap (fun l0 : pbpt = pbpt => ((ap prB l0; ap prC l0) : USym H × USym H')) (eqinv_r (snd lp) l)^).
    exact (fst (path_prod_eqv _ _ _ _) ((ap_prB_pb_path (u := pbpt) (v := pbpt) a a' s0)^;
                                        (ap_prC_pb_path (u := pbpt) (v := pbpt) a a' s0)^)).
  Defined.

  Definition pbU_eqv : USym (pullbackG f f') ≃ pullback (USymf f) (USymf f')
    := (pbU; inj_surj_isEquiv pbU_isInj pbU_isSurj).

  (** [Hom(K, H ×_G H')]: a pointed map [BK →* B(H ×_G H')] amounts to
      pointed maps [k₁ : BK →* BH], [k₂ : BK →* BH'] with a pointed
      homotopy [Bf k₁ ~ Bf' k₂] ([PBdata], [pbPhi0], [pbPsi0]). *)
  Context {K : Group}.

  Local Notation BP := (BG (pullbackG f f')).

  Definition PBdata : Type
    := {kk : (BG K →* BG H) × (BG K →* BG H') &
         {h : forall x, k (fst (fst kk) x) = k' (fst (snd kk) x) &
           h (sh K) ⋅ snd (pcomp (Bf f) (fst kk)) = snd (pcomp (Bf f') (snd kk))}}.

  Definition pbg0 (d : PBdata) (x : utype (BG K)) : PB
    := (((fst (fst (fst d)) x; fst (snd (fst d)) x) : utype (BG H) × utype (BG H')); fst (snd d) x).

  Definition pbL (d : PBdata) : pbpt = pbg0 d (sh K)
    := pb_path (u := pbpt) (v := pbg0 d (sh K)) (snd (fst (fst d))) (snd (snd (fst d)))
         (pb_pt_sq_bw (snd (Bf f)) (snd (Bf f')) _ _ _ (snd (snd d))).

  Definition pbmem (d : PBdata) (x : utype (BG K)) : ptrunc (pbpt = pbg0 d x)
    := ptrunc_rec ptrunc_isProp (fun p : sh K = x => trunc (pbL d @ ap (pbg0 d) p))
         (snd (BG_isConn K) (sh K) x).

  Definition pbPhi0 (d : PBdata) : BG K →* BP
    := ((fun x => (pbg0 d x; pbmem d x));
        path_sigma_prop (fun _ => ptrunc_isProp) (u := pt BP) (v := (pbg0 d (sh K); pbmem d (sh K)))
          (pbL d)).

  Definition pbPhi0_L (d : PBdata) : ap fst (snd (pbPhi0 d)) = pbL d
    := ap_fst_path_sigma_prop (fun _ => ptrunc_isProp)
         (u := pt BP) (v := (pbg0 d (sh K); pbmem d (sh K))) (pbL d).

  Definition pbPsi0 (g : BG K →* BP) : PBdata.
  Proof.
    pose (L := ap fst (snd g) : pbpt = fst (fst g (sh K))).
    pose (K1 := ((fun x => prB (fst (fst g x))); ap prB L) : BG K →* BG H).
    pose (K2 := ((fun x => prC (fst (fst g x))); ap prC L) : BG K →* BG H').
    exact (((K1; K2) : (BG K →* BG H) × (BG K →* BG H'));
           ((fun x => snd (fst (fst g x)));
            pb_pt_sq (snd (Bf f)) (snd (Bf f')) _ _ _ (pb_nat L))).
  Defined.

  Definition PBdata_path {k1 : utype (BG K) -> utype (BG H)} {k2 : utype (BG K) -> utype (BG H')}
    {sk1 sk1' : sh H = k1 (sh K)} {sk2 sk2' : sh H' = k2 (sh K)}
    (h : forall x, k (k1 x) = k' (k2 x))
    (c : h (sh K) ⋅ snd (pcomp (Bf f) (k1; sk1)) = snd (pcomp (Bf f') (k2; sk2)))
    (c' : h (sh K) ⋅ snd (pcomp (Bf f) (k1; sk1')) = snd (pcomp (Bf f') (k2; sk2')))
    (e1 : sk1 = sk1') (e2 : sk2 = sk2')
    : ((((k1; sk1); (k2; sk2)) : (BG K →* BG H) × (BG K →* BG H')); (h; c)) = ((((k1; sk1'); (k2; sk2')) : (BG K →* BG H) × (BG K →* BG H')); (h; c')) :> PBdata.
  Proof.
    destruct e1, e2.
    exact (ap (fun c0 => ((((k1; sk1); (k2; sk2)) : (BG K →* BG H) × (BG K →* BG H')); (h; c0)) : PBdata)
              (BG_isGrpd G _ _ _ _ c c')).
  Defined.

  Definition pbPsiPhi (d : PBdata) : pbPsi0 (pbPhi0 d) = d.
  Proof.
    destruct d as [[[k1 sk1] [k2 sk2]] [h c]].
    refine (PBdata_path h _ c _ _).
    - refine (ap (ap prB) (pbPhi0_L ((((k1; sk1); (k2; sk2)) : (BG K →* BG H) × (BG K →* BG H')); (h; c))) @ _).
      exact (ap_prB_pb_path _ _ _).
    - refine (ap (ap prC) (pbPhi0_L ((((k1; sk1); (k2; sk2)) : (BG K →* BG H) × (BG K →* BG H')); (h; c))) @ _).
      exact (ap_prC_pb_path _ _ _).
  Defined.

  Definition pbPhiPsi (g : BG K →* BP) : pbPhi0 (pbPsi0 g) = g.
  Proof.
    destruct g as [gf gp].
    apply (eqinv (snd (ptw_star (pbPhi0 (pbPsi0 (gf; gp))) (gf; gp)))).
    exists (fun x => path_sigma_prop (fun _ => ptrunc_isProp)
                       (u := fst (pbPhi0 (pbPsi0 (gf; gp))) x) (v := gf x) refl).
    apply (isInj_cancel (isEquiv_isInj (snd (subtype_paths_eqv (fun _ => ptrunc_isProp) _ _)))).
    refine (ap_trans fst _ _ @ _).
    refine (ap011 trans (ap_fst_path_sigma_prop (fun _ => ptrunc_isProp) _)
              (ap_fst_path_sigma_prop (fun _ => ptrunc_isProp) _) @ _).
    exact (pb_path_congr (u := pbpt) _ (pb_nat (ap fst gp)) refl refl @ pb_path_eta (ap fst gp)).
  Defined.

  Definition pbPhi_eqv : PBdata ≃ (BG K →* BP) := mkEqv pbPhi0 pbPsi0 pbPsiPhi pbPhiPsi.

  (** The pullback of [compG f] and [compG f'] is [PBdata], by [ptw_star]. *)
  Definition pbHom_fw (w : pullback (fun k1 : Hom K H => compG f k1) (fun k2 : Hom K H' => compG f' k2))
    : PBdata
    := (((out (fst (fst w)); out (snd (fst w))) : (BG K →* BG H) × (BG K →* BG H'));
        fst (ptw_star _ _) (ap out (snd w))).

  Definition pbHom_bw (d : PBdata)
    : pullback (fun k1 : Hom K H => compG f k1) (fun k2 : Hom K H' => compG f' k2)
    := (((inc (fst (fst d)); inc (snd (fst d))) : Hom K H × Hom K H');
        ap inc (eqinv (snd (ptw_star (pcomp (Bf f) (fst (fst d))) (pcomp (Bf f') (snd (fst d)))))
                  (snd d))).

  Definition pbHom_eqv
    : pullback (fun k1 : Hom K H => compG f k1) (fun k2 : Hom K H' => compG f' k2) ≃ PBdata.
  Proof.
    refine (mkEqv pbHom_fw pbHom_bw _ _).
    - intros [[[k1] [k2]] e].
      exact (path_sigma_prop (fun _ => Hom_isSet K G _ _)
               (u := pbHom_bw (pbHom_fw (((inc k1; inc k2) : Hom K H × Hom K H'); e)))
               (v := ((inc k1; inc k2) : Hom K H × Hom K H'; e)) refl).
    - intros [kk w].
      refine (ap (fun w0 => (kk; w0) : PBdata) _).
      pose (P := ptw_star (pcomp (Bf f) (fst kk)) (pcomp (Bf f') (snd kk))).
      refine (ap (fst P) ((ap_compose inc out (eqinv (snd P) w))^ @ ap_idmap _) @ _).
      exact (eqinv_r (snd P) w).
  Defined.

End PullbackUniv.

Definition pullbackG_univ `{Funext} : pullbackG_univ_stmt
  := fun H H' G K f f' =>
       (Eqv_comp (pbHom_eqv f f' (K := K)) (Eqv_comp (pbPhi_eqv f f') (Eqv_inv (Copy_eqv _)));
        Eqv_inv (pbU_eqv f f')).
