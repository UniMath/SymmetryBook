(** * Section 3.3 Coverings

    Part of Chapter 3 ([circle.tex]); see [Circle.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - [def:covering]: coverings, connected, finite and decidable
      coverings, pointed coverings, and [SetBundle(B)].
    - The equivalence [SetBundle(B) ≃ (B → Set)] of
      [lem:Prop-Set-pointed-families], in the direction of [preim] so that
      it computes by definition ([coverPreim_Eqv]), and
      [lem:setbundle-is-groupoid].
    - Exercise [xca:covering-utils], all six parts.  For part 4 we do not
      follow the hint: [f⁻¹(b)] is the fiber over [(b, refl)] of a map
      between the sets [(gf)⁻¹(g(b))] and [g⁻¹(g(b))].
    - Exercise [xca:twoS1coverings], both parts.
    - [thm:coveringsofS1perms]: [SetBundle(S1) ≃ (S1 → Set) ≃
      ∑_{X:Set}(X ≃ X)], together with [g : (S1 → U) ≃ ∑_{X:U}(X ≃ X)]; the
      squares with the forgetful maps commute (the left one by
      definition, the right one by [ap_compose]).  Remark
      [rem:subtype-diagram] is only used for these particular diagrams.
    - Example [def:universalcover], [def:univ-cover], and
      [lem:univ-cover-of-groupoid] in both directions, with the book's
      argument for "universal implies contractible" (using associativity
      of pointed composition, [pcomp_assoc]).  The other direction does
      not need that [B] is a groupoid: pointed maps out of a contractible
      pointed type form a contractible type.
    - [def:RtoS1]: [R : S1 → U] with [R(base) :≡ ℤ], [R(loop) := etop(zs)],
      which is set-valued, and the exponential covering [exp].  The
      implicit arguments of [fst] in [exp] are given explicitly: otherwise
      unification unfolds [R] into a case analysis on the library's
      private inductive type underlying [S1]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Colimits.Coeq Colimits.Pushout
  Spaces.Nat.Core Spaces.Int Spaces.Circle.
From SymmetryBook Require Export Circle.S02_Integers.

Local Open Scope uf_scope.

(** ** 3.3 Coverings *)

(** Definition [def:covering]. *)
Definition isCovering {A B : Type} (f : A -> B) : Type
  := forall b : B, isSet (fiber f b).

Definition isConnCovering {A B : Type} (f : A -> B) : Type
  := isCovering f × isConn A.

Definition isFinCovering {A B : Type} (f : A -> B) : Type
  := forall b : B, isFinSet (fiber f b).

Definition isDecCovering {A B : Type} (f : A -> B) : Type
  := forall b : B, isDecSet (fiber f b).

(** Pointed coverings.  By the footnote ([xca:freemaps]), a map out of a
    pointed type is the same as a pointed map to its image of the point. *)
Definition isPtdCovering {A B : Ustar} (f : A →* B) : Type := isCovering (fst f).

(** [SetBundle(B) :≡ ∑_{A:U} ∑_{f:A→B} ∏_{b:B} isSet(f⁻¹(b))]. *)
Definition SetBundle (B : Type) : Type
  := {A : Type & {f : A -> B & forall b, isSet (fiber f b)}}.

(** The equivalence with [B → Set] from [lem:Prop-Set-pointed-families] of 2.25,
    in the direction [f(A,h) :≡ (b ↦ h⁻¹(b))] (the restriction of
    [preim]), so that it computes by definition. *)
Section SetBundleFamilies.

  Context `{Univalence} (B : Type).

  Definition coverPreim (w : SetBundle B) : B -> SetU
    := fun b => (fiber (fst (snd w)) b; snd (snd w) b).

  Definition coverPreim_Eqv : SetBundle B ≃ (B -> SetU).
  Proof.
    refine (Eqv_comp (sigma_assoc Type (fun A => A -> B)
                        (fun A f => forall b, isSet (fiber f b))) _).
    refine (Eqv_comp (Eqv_of_Equiv (equiv_functor_sigma_pb
                        (Q := fun F : B -> Type => forall b, isSet (F b))
                        (Equiv_of_Eqv (preim_eqv B)))) _).
    exact (mkEqv (fun (w : {F : B -> Type & forall b, isSet (F b)}) (b : B) =>
                    (fst w b; snd w b) : SetU)
                 (fun S : B -> SetU =>
                    ((fun b => fst (S b)); (fun b => snd (S b)))
                    : {F : B -> Type & forall b, isSet (F b)})
                 (fun w => refl) (fun S => refl)).
  Defined.

  Definition coverPreim_Eqv_fun (w : SetBundle B)
    : fst coverPreim_Eqv w = coverPreim w := refl.

  (** Lemma [lem:setbundle-is-groupoid]. *)
  Definition SetBundle_isGrpd : isGrpd (SetBundle B)
    := is_ntype_Eqv 1 (Eqv_inv coverPreim_Eqv) (Pi_ntype 1 (fun _ => SetU_isGrpd)).

End SetBundleFamilies.

(** Exercise [xca:covering-utils]. *)
Section CoveringUtils.

  (** 1. [A → 𝟙] is a covering iff [A] is a set. *)
  Definition fiber_toTrue_eqv {A : Type} (t : True)
    : fiber (fun _ : A => tt) t ≃ A
    := mkEqv fst (fun a => (a; True_isProp t tt))
         (fun w => path_sigma_prop (fun _ => prop_is_set True_isProp _ _)
                     (u := (fst w; True_isProp t tt)) (v := w) refl)
         (fun a => refl).

  Definition covering_toTrue (A : Type)
    : (isCovering (fun _ : A => tt) -> isSet A)
      × (isSet A -> isCovering (fun _ : A => tt))
    := (fun c => is_ntype_Eqv 0 (fiber_toTrue_eqv tt) (c tt);
        fun s t => is_ntype_Eqv 0 (Eqv_inv (fiber_toTrue_eqv t)) s).

  (** 2. [x ↦ b] from [𝟙] to [B] is a covering iff [b = b] is a set. *)
  Definition fiber_fromTrue_eqv {B : Type} (b b' : B)
    : fiber (fun _ : True => b) b' ≃ (b' = b).
  Proof.
    refine (mkEqv (fun w : fiber (fun _ : True => b) b' => snd w)
                  (fun p => (tt; p)) _ (fun p => refl)).
    intros [[] p]. exact refl.
  Defined.

  Definition isSet_from_inh {X : Type} (h : X -> isSet X) : isSet X
    := fun x y => h x x y.

  Definition covering_fromTrue {B : Type} (b : B)
    : (isCovering (fun _ : True => b) -> isSet (b = b))
      × (isSet (b = b) -> isCovering (fun _ : True => b))
    := (fun c => is_ntype_Eqv 0 (fiber_fromTrue_eqv b b) (c b);
        fun s b' => is_ntype_Eqv 0 (Eqv_inv (fiber_fromTrue_eqv b b'))
                      (isSet_from_inh (fun p : b' = b =>
                                         is_ntype_Eqv 0 (eq_l_eqv p⁻¹) s))).

  (** 3. Coverings compose; the fibers of [gf] are sums of fibers. *)
  Definition fiber_comp_eqv {A B C : Type} (f : A -> B) (g : B -> C) (c : C)
    : fiber (g ∘ f) c ≃ {w : fiber g c & fiber f (fst w)}.
  Proof.
    refine (mkEqv (fun v : fiber (g ∘ f) c =>
                     ((f (fst v); snd v) : fiber g c; (fst v; refl))
                     : {w : fiber g c & fiber f (fst w)})
                  (fun u : {w : fiber g c & fiber f (fst w)} =>
                     (fst (snd u); ap g (snd (snd u)) ⋅ snd (fst u)) : fiber (g ∘ f) c)
                  _ _).
    - intros [a p]. exact refl.
    - intros [[b p] [a q]]. cbn in p, q |- *.
      revert b q p. refine (paths_ind_r _ _ _). intro p. exact refl.
  Defined.

  Definition covering_comp {A B C : Type} {f : A -> B} {g : B -> C}
    (cf : isCovering f) (cg : isCovering g) : isCovering (g ∘ f)
    := fun c => is_ntype_Eqv 0 (Eqv_inv (fiber_comp_eqv f g c))
                  (Sigma_isSet (cg c) (fun w => cf (fst w))).

  (** 4 [it:left-cancel-cover]. If [g] and [gf] are coverings, then so is [f].  Instead of the
      book's hint we use that [f⁻¹(b)] is the fiber over [(b, refl)] of
      the projection [(gf)⁻¹(g(b)) ≃ ∑_{w : g⁻¹(g(b))} f⁻¹(fst w) → g⁻¹(g(b))],
      a map between sets. *)
  Definition fiber_sets_isSet {X Y : Type} (h : X -> Y) (sX : isSet X)
    (sY : isSet Y) (y : Y) : isSet (fiber h y)
    := Sigma_isSet sX (fun x => prop_is_set (sY _ _)).

  Definition covering_cancel {A B C : Type} {f : A -> B} {g : B -> C}
    (cg : isCovering g) (cgf : isCovering (g ∘ f)) : isCovering f
    := fun b => is_ntype_Eqv 0
         (Eqv_inv (fst_fiber_eqv (fun w : fiber g (g b) => fiber f (fst w)) (b; refl)))
         (fiber_sets_isSet fst (is_ntype_Eqv 0 (fiber_comp_eqv f g (g b)) (cgf (g b)))
            (cg (g b)) (b; refl)).

  (** 5. A covering of a groupoid by a connected type [A] with a
      connected loop type [a = a] has a contractible domain. *)
  Definition loops_conj {X : Type} {x y : X} (p : x = y) : (x = x) ≃ (y = y).
  Proof. destruct p. exact (idEqv _). Defined.

  Definition covering_conn_isContr `{Funext} {A B : Type} {f : A -> B} (a : A)
    (cA : isConn A) (ca : isConn (a = a)) (gB : isGrpd B) (cf : isCovering f)
    : isContr A.
  Proof.
    pose (inj := fun r => fibers_paths_Q f isProp (fun X Y e h => isProp_Eqv e h)
                            (fun b z z' => cf b z z') a a r : isProp (fiber (ap f) r)).
    pose (sa := inj_ntype 0 (f := @ap A B f a a) inj (gB (f a) (f a))).
    pose (cl := conn_set_isContr ca sa).
    apply (conn_loops_prop_isContr cA). intro x.
    exact (ptrunc_rec (isProp_isProp _)
             (fun p : a = x => isProp_Eqv (loops_conj p) (isContr_isProp' cl))
             (snd cA a x)).
  Defined.

  (** 6 [it:cover-n-type]. A covering of an [n]-type ([n ≥ 0]) has an [n]-type as domain. *)
  Fixpoint set_ntype (n : ℕ) {X : Type} (s : isSet X) : is_ntype n X
    := match n with
       | O => s
       | S n => fun x y => set_ntype n (prop_is_set (s x y))
       end.

  Definition covering_ntype `{Funext} (n : ℕ) {A B : Type} {f : A -> B}
    (cf : isCovering f) (hB : is_ntype n B) : is_ntype n A
    := is_ntype_Eqv n (sum_of_fibers f)
         (Sigma_ntype n hB (fun b => set_ntype n (cf b))).

End CoveringUtils.

(** Exercise [xca:twoS1coverings]. *)
Section TwoS1Coverings.

  Context `{Univalence}.

  Definition BoolSet : SetU := (Bool; isSet_bool).

  Definition c_Bool : S1 -> SetU := fun _ => BoolSet.

  Definition veSet (X : SetU) (l : X = X) : S1 -> SetU := ve SetU (X; l).

  (** 1. [∑_{z:S1} 𝟚] is not connected, and [c_𝟚 = ve_Set(𝟚, refl)]. *)
  Definition const_cover_not_conn : ¬ isConn {z : S1 & Bool}
    := fun c => ptrunc_rec False_isProp (fun e : ((base; yes) : {z : S1 & Bool}) = (base; no) =>
                                 yes_ne_no (ap (fun w : {z : S1 & Bool} => snd w) e))
                  (snd c (base; yes) (base; no)).

  Definition c_Bool_refl : c_Bool = veSet BoolSet refl
    := S1_fun_path (f := c_Bool) (g := veSet BoolSet refl) refl
         (ap_const loop BoolSet @ (trans_1p _ @ S1_rec_loop SetU BoolSet refl)^).

  (** 2. With [swap] lifted to [Set], [A :≡ ∑_{z:S1} ve_Set(𝟚, swap)(z)] is
      connected, and [c_𝟚 ≠ ve_Set(𝟚, swap)]. *)
  Definition swapSet : BoolSet = BoolSet
    := path_sigma_prop (u := BoolSet) (v := BoolSet) (fun X => isSet_isProp X) swap.

  Definition ap_fst_swapSet : ap (fun X : SetU => fst X) swapSet = swap
    := ap_fst_pathpair _ _.

  Definition A2 : Type := {z : S1 & fst (veSet BoolSet swapSet z)}.

  Definition trp_A2_loop
    : trp (fun z => fst (veSet BoolSet swapSet z)) loop yes = no.
  Proof.
    refine (transport_compose (fun X : SetU => fst X) (veSet BoolSet swapSet) loop yes @ _).
    refine (ap (fun r : BoolSet = BoolSet => trp (fun X : SetU => fst X) r yes)
              (S1_rec_loop SetU BoolSet swapSet) @ _).
    refine (transport_compose (fun T : Type => T) (fun X : SetU => fst X) swapSet yes @ _).
    refine (ap (fun r => transport idmap r yes) ap_fst_swapSet @ _).
    exact (ptw (ap fst (ptoe_etop swapEqv)) yes).
  Defined.

  Definition A2_paths (w : A2) : ptrunc (((base; yes) : A2) = w).
  Proof.
    destruct w as [z x]. revert z x.
    refine (S1_ind_prop (fun z => forall x, ptrunc (((base; yes) : A2) = (z; x)))
              (fun z => Pi_isProp (fun _ => ptrunc_isProp)) _).
    intros [|].
    - exact (trunc refl).
    - exact (trunc (pathpair (Y := fun z => fst (veSet BoolSet swapSet z)) loop trp_A2_loop)).
  Defined.

  Definition A2_isConn : isConn A2
    := (trunc (base; yes);
        fun w w' => ptrunc_rec ptrunc_isProp
                      (fun p => ptrunc_rec ptrunc_isProp (fun q => trunc (q ⋅ p⁻¹))
                                  (A2_paths w'))
                      (A2_paths w)).

  Definition trp_loops_refl {X : Type} {x y : X} (p : x = y)
    : trp (fun z => z = z) p refl = refl.
  Proof. destruct p. exact refl. Defined.

  Definition c_Bool_ne_swap : ¬ (c_Bool = veSet BoolSet swapSet).
  Proof.
    intro e.
    pose (e' := (ap (fun r => (BoolSet; r) : {X : SetU & X = X}) (ap_const loop BoolSet))^
                @ ap (ev SetU) e
                @ ap (fun r => (BoolSet; r) : {X : SetU & X = X})
                     (S1_rec_loop SetU BoolSet swapSet)).
    pose (s := pathsplit (Y := fun X : SetU => X = X) e').
    pose (r := (trp_loops_refl (fst s))^ @ snd s : refl = swapSet).
    exact (refl_ne_swap (ap (ap fst) r @ ap_fst_pathpair _ _)).
  Defined.

End TwoS1Coverings.

(** Theorem [thm:coveringsofS1perms], with remark [rem:subtype-diagram]
    for its squares.  The second row:
    [preim : ∑_{A:U}(A → S1) ≃ (S1 → U)] and
    [g(S) :≡ (S(base), trp^{id_U}_{S(loop)})], an equivalence by
    [lem:freeloopspace] and univalence; the third row: their restrictions
    [SetBundle(S1) ≃ (S1 → Set) ≃ ∑_{X:Set}(X ≃ X)].  The vertical maps
    forget the properties; the squares commute, the left one by
    definition. *)
Section CoveringsOfS1.

  Context `{Univalence}.

  Definition gU : (S1 -> Type) ≃ {X : Type & X ≃ X}
    := Eqv_comp (ev_Eqv (A := Type))
         (tot (fun X (p : X = X) => idtoeqv p); tot_isEquiv _ (fun X => ua X X)).

  Definition gU_fun (S : S1 -> Type) : fst gU S = exist (fun X : Type => X ≃ X) (S base) (idtoeqv (ap S loop))
    := refl.

  Definition gSet : (S1 -> SetU) ≃ {X : SetU & fst X ≃ fst X}
    := Eqv_comp (ev_Eqv (A := SetU))
         (tot (fun X (p : X = X) => idtoeqv (ap fst p));
          tot_isEquiv _ (fun X => snd (Eqv_comp (subtype_paths_eqv
                                                   (fun Y => isSet_isProp Y) X X)
                                                (idtoeqv; ua _ _)))).

  Definition coverings_S1 : SetBundle S1 ≃ {X : SetU & fst X ≃ fst X}
    := Eqv_comp (coverPreim_Eqv S1) gSet.

  Definition forget_left_square (w : SetBundle S1)
    : preim S1 (fst w; fst (snd w)) = (fun z => fst (fst (coverPreim_Eqv S1) w z))
    := refl.

  Definition forget_right_square (S : S1 -> SetU)
    : fst gU (fun z => fst (S z))
      = exist (fun X : Type => X ≃ X) (fst (fst (fst gSet S))) (snd (fst gSet S))
    := ap (fun r => exist (fun X : Type => X ≃ X) (fst (S base)) (idtoeqv r))
          (ap_compose S fst loop).

End CoveringsOfS1.

(** Example [def:universalcover]: [uc_{b₀}(b) :≡ (b₀ = b)] over a
    groupoid; the alternative forms [fst] and [cst_{b₀} : 𝟙 → B]. *)
Definition uc {B : Type} (b0 : B) : B -> Type := fun b => b0 = b.

Definition uc_covering {B : Type} (gB : isGrpd B) (b0 : B)
  : isCovering (@fst B (uc b0))
  := fun b => is_ntype_Eqv 0 (fst_fiber_eqv (uc b0) b) (gB b0 b).

Definition uc_Tot_isContr {B : Type} (b0 : B) : isContr (Tot (uc b0))
  := singleton_contr b0.

Definition cst_covering {B : Type} (gB : isGrpd B) (b0 : B)
  : isCovering (fun _ : True => b0)
  := snd (covering_fromTrue b0) (gB b0 b0).

(** Definition [def:univ-cover]. *)
Definition isUnivCovering {A B : Ustar} (f : A →* B) : Type
  := forall (C : Ustar) (g : C →* B), isPtdCovering g
       -> isContr {h : A →* C & f = pcomp g h}.

(** Lemma [lem:univ-cover-of-groupoid]. *)
Section UnivCoverOfGroupoid.

  Context `{Funext}.

  Definition isContr_paths {X : Type} (c : isContr X) (x y : X) : isContr (x = y)
    := isProp_inhabited_isContr (prop_is_set (isContr_isProp' c) x y)
         (isContr_isProp' c x y).

  (** Pointed maps out of a contractible pointed type form a contractible
      type. *)
  Definition pmap_dom_isContr (A Y : Ustar) (c : isContr (utype A))
    : isContr (A →* Y).
  Proof.
    refine (isContr_Eqv (Eqv_inv (mkEqv
              (fun g : A →* Y => (fst g (pt A); snd g) : {y : utype Y & pt Y = y})
              (fun w => ((fun _ => fst w); snd w) : A →* Y) _ (fun w => refl)))
              (singleton_contr (pt Y))).
    intros [g p]. change (utype A -> utype Y) in g. change (pt Y = g (pt A)) in p.
    pose (k := fun x => isContr_isProp' c (pt A) x).
    refine (eqinv (snd (ptw_star (((fun _ => g (pt A)); p) : A →* Y) ((g; p) : A →* Y))) _).
    refine (exist _ (fun x => ap g (k x)) _).
    exact (ap (fun r => ap g r ⋅ p) (prop_is_set (isContr_isProp' c) _ _ (k (pt A)) refl)).
  Defined.

  Definition contr_univCovering {A B : Ustar} (f : A →* B) (c : isContr (utype A))
    : isUnivCovering f
    := fun C g _ => Sigma_isContr (pmap_dom_isContr A C c)
                      (fun h => isContr_paths (pmap_dom_isContr A B c) _ _).

  Definition pcomp_assoc_lemma {X Y Z : Type} (F : Y -> Z) (G : X -> Y)
    {a b : X} (p : a = b) {y : Y} {z : Z} (q : y = G a) (r : z = F y)
    : ap (fun x => F (G x)) p ⋅ (ap F q ⋅ r) = ap F (ap G p ⋅ q) ⋅ r.
  Proof. destruct p. exact refl. Defined.

  Definition pcomp_assoc {W X Y Z : Ustar} (f : Y →* Z) (g : X →* Y) (h : W →* X)
    : pcomp (pcomp f g) h = pcomp f (pcomp g h)
    := ap (fun r => ((fun w => fst f (fst g (fst h w))); r) : W →* Z)
          (pcomp_assoc_lemma (fst f) (fst g) (snd h) (snd g) (snd f)).

  Definition unitStar : Ustar := (True; tt).

  Definition True_isContr : isContr True := (tt; fun t => match t with tt => refl end).

  Definition univCovering_contr {A B : Ustar} (f : A →* B)
    (gB : isGrpd (utype B)) (cf : isPtdCovering f) (u : isUnivCovering f)
    : isContr (utype A).
  Proof.
    pose (cstp := ((fun _ => pt B); refl) : unitStar →* B).
    pose (hc := fst (u unitStar cstp (cst_covering gB (pt B)))).
    pose (hc' := fst (contr_univCovering cstp True_isContr A f cf)).
    pose (h := fst hc). pose (h' := fst hc').
    pose (e := snd hc @ ap (fun k => pcomp k h) (snd hc') @ pcomp_assoc f h' h
               : f = pcomp f (pcomp h' h)).
    pose (cu := u A f cf).
    pose (r := ap fst ((snd cu ((pid A; refl) : {k : A →* A & f = pcomp f k}))^
                       @ snd cu (pcomp h' h; e))
               : pid A = pcomp h' h).
    refine (fst h' tt; fun a => _).
    exact (ap (fst h') (True_isProp tt (fst h a)) @ (ptw (ap fst r) a)^).
  Defined.

End UnivCoverOfGroupoid.

(** Definition [def:RtoS1]: [R(base) :≡ ℤ], [R(loop) := etop(zs)], and the
    exponential covering [exp :≡ fst : Tot(R) → S1], pointed at
    [(base, 0)] with pointing path [refl]. *)
Section ExpCovering.

  Context `{Univalence}.

  Definition R : S1 -> Type := S1_rec Type ℤ (etop zsEqv).

  Definition R_isSet (z : S1) : isSet (R z)
    := ptrunc_rec (isSet_isProp _)
         (fun p : base = z => trp (fun x => isSet (R x)) p ℤ_isSet)
         (S1_base_paths z).

  Definition RSet : S1 -> SetU := fun z => (R z; R_isSet z).

  Definition TotRstar : Ustar := (Tot R; (base; iplus 0)).

  (** The implicit arguments of [fst] are given explicitly: otherwise
      unification unfolds [R] into a case analysis on the library's private
      inductive type underlying [S1]. *)
  Definition exp : TotRstar →* S1star := (@fst S1 R; refl).

  Definition exp_covering : isPtdCovering exp
    := fun z => is_ntype_Eqv 0 (fst_fiber_eqv R z) (R_isSet z).

End ExpCovering.

(** Remark [rem:expforreal]: [exp] pictured as a helix over the circle,
    like the exponential map [ℝ → S¹] (informal). *)
