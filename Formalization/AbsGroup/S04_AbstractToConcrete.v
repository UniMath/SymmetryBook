(** * Section 7.4 Groups: from abstract to concrete and back

    Part of Chapter 7 ([absgroup.tex]); see [AbsGroup.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - The abstract permutation group [ag_Perm X] of a set [X], with
      elements [X ≃ X] under composition.  The book uses [abstr(Σ_X)],
      whose elements are identifications [X = X]; by univalence these
      correspond, and [SG_Perm_iso] (Section 7.6) gives the isomorphism.
    - Definition [def:abstrGtorsors]: [absGSet G :≡ ∑_{X:Set}
      absHom(G, Perm(X))], the action [gact], the principal torsor
      [absprtor], and [absGTor] (the component of [absprtor]).
    - Definition [def:Hom-absG] ([absHomG], [isGHom]), isomorphisms of
      [G]-sets ([gIso]), and the structure identity principle
      [(X = Y) ≃ gIso(X,Y)] ([gIso_eqv]), proved by contractibility of
      [∑_Y gIso(X,Y)] (with [Sigma_isContr_base], [SetU_total_contr]).
    - Definition [def:concr]: [concr G :≡ Aut_{absGSet}(absprtor)].
    - Exercise [xca:absprtorsor] ([absprtor_right_path]).
    - Example [ex:BqG], definition [def:qG-concr-abstr] and lemma
      [lem:Groupsareidentitytypes]: [Bq], pointed by an identification
      [Bq_pt_path] obtained from the identity isomorphism (the book's
      [refl] is not available since the proofs that left multiplication
      is an equivalence differ), [qG] and [qG_isIso]; the induced map on
      symmetries is [preinv] (precomposition with the inverse).
    - The isomorphism [r_G : G ≅ abstr(concr(G))] ([rG_iso]), via
      [rho(u) :≡ (- · u⁻¹)] (abstract Cayley, footnote
      [ft:abstract-Cayley]).
    - Theorem [thm:Groupsareidentitytypes] ([abstr_isEquiv]).  Since the
      type of torsors contains the type of sets, [concr(G)] lives in the
      next universe, and [q_G], [r_G] relate [G] to a group of the next
      universe.  To invert [abstr] within one universe we assume the
      replacement principle [Replacement] of Section 2.19: by exercise
      [xca:comp-loc-small-ess-small] the type of torsors is essentially
      small, since it is a component of the locally small type [absGSet]
      ([absGSet_locSmall], via [gIso_eqv]).  This gives [concr_small],
      and [abstr_isEquiv rep : isEquiv abstr].  NOTE for the book text:
      the size issue (and the need for replacement, or another way to get
      a small classifying type) is not mentioned.
    - Subsection 7.4.1: definition [def:phi^*] ([abs_restrict]),
      definition [def:phi_*] ([abs_coinduce], with [coind_set] and the
      action [h · b :≡ b(h⁻¹ ·)]), and exercise [xca:phi^*-|phi_*]
      ([abs_adj_restrict_coinduce]).

    Left out (statements only, no proofs yet; time limit per result)
    - Definition [def:phi_!] (via a set quotient; [def_phi_shriek_stmt],
      with the relation [phi_rel]), exercises [xca:phi_!-OK]
      ([xca_phi_OK_stmt]) and [xca:phi_!-|phi^*]
      ([xca_phi_shriek_adj_stmt]).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core.
From SymmetryBook Require Export AbsGroup.S03_AbstractHomomorphisms.

Local Open Scope uf_scope.
Local Open Scope ag_scope.
Local Notation "g · h" := (ag_mul _ g h) (at level 40, left associativity) : ag_scope.

(** ** 7.4 Groups: from abstract to concrete and back *)

(** The abstract permutation group of a set [X]: the self-equivalences
    of [X] under composition.  The book uses [abstr(Σ_X)], whose elements
    are identifications [X = X]; by univalence these are the
    self-equivalences, which we use for convenience. *)
Definition ag_Perm `{Funext} (X : SetU) : AbsGroup.
Proof.
  refine {| ag_S := fst X ≃ fst X; ag_isSet := Eqv_sets_isSet (snd X);
            ag_e := idEqv (fst X); ag_mul := fun f g => Eqv_comp g f;
            ag_inv := Eqv_inv |}.
  - intro f. apply path_Eqv. exact refl.
  - intro f. apply path_Eqv. exact refl.
  - intros f g h. apply path_Eqv. exact refl.
  - intro f. apply path_Eqv. apply ptw_inv. intro x. exact (eqinv_r (snd f) x).
Defined.

(** Composition of pointed equivalences. *)
Definition pEqv_comp {X Y Z : Ustar} (e : X ≃* Y) (e' : Y ≃* Z) : X ≃* Z
  := (pcomp (fst e') (fst e); comp_isEquiv (snd e) (snd e')).

(** A [Σ]-type over a contractible base is contractible as soon as one
    fiber is. *)
Definition Sigma_isContr_base {A : Type} {B : A -> Type} (cA : isContr A) (a0 : A)
  (c0 : isContr (B a0)) : isContr {a : A & B a}
  := Sigma_isContr cA (fun a => isContr_Eqv (trp B (isContr_isProp' cA a0 a);
                                             trp_isEquiv B _) c0).

Definition Type_total_contr `{Univalence} (X : Type) : isContr {T : Type & X ≃ T}
  := isContr_Eqv (tot (fun T (p : X = T) => idtoeqv p); tot_isEquiv _ (fun T => ua X T))
       (singleton_contr X).

Definition SetU_total_contr `{Univalence} (X : SetU) : isContr {T : SetU & fst X ≃ fst T}.
Proof.
  refine (isContr_Eqv (mkEqv
    (fun v : {w : {T : Type & fst X ≃ T} & isSet (fst w)} =>
       (((fst (fst v); snd v) : SetU); snd (fst v)) : {T : SetU & fst X ≃ fst T})
    (fun u : {T : SetU & fst X ≃ fst T} =>
       (((fst (fst u); snd u) : {T : Type & fst X ≃ T}); snd (fst u)))
    (fun _ => refl) (fun _ => refl)) _).
  exact (Sigma_isContr_base (Type_total_contr (fst X)) (fst X; idEqv _)
           (isProp_inhabited_isContr (isSet_isProp _) (snd X))).
Defined.

(** Footnote [ft:choicePshG]: [P_G] is defined with [sh_G = z] rather
    than [z = sh_G], so its abstract homomorphism is postcomposition
    [g ↦ (g · _)]; compare [Bq_G] in [ex:BqG] below (informal). *)

(** Definition [def:abstrGtorsors]: [G]-sets, the principal torsor and
    the type of torsors of an abstract group. *)
Section AbsGSets.

  Context `{Univalence} (G : AbsGroup).

  Definition absGSet : Type := {X : SetU & absHom G (ag_Perm X)}.

  Definition gset (X : absGSet) : Type := fst (fst X).

  Definition gset_isSet (X : absGSet) : isSet (gset X) := snd (fst X).

  (** The action [s ·_X x]. *)
  Definition gact (X : absGSet) (s : ag_S G) (x : gset X) : gset X
    := fst (fst (snd X) s) x.

  Definition absGSet_isGrpd : isGrpd absGSet
    := Sigma_isGrpd SetU_isGrpd (fun X => set_isGrpd (absHom_isSet _ _)).

  Definition lmul_eqv (g : ag_S G) : ag_S G ≃ ag_S G := (ag_mul G g; ag_lmul_isEquiv G g).

  Definition absprtor : absGSet
    := ((ag_S G; ag_isSet G);
        (lmul_eqv; fun g h => path_Eqv (lmul_eqv (g · h)) (Eqv_comp (lmul_eqv h) (lmul_eqv g))
                                (ptw_inv (fun s => (ag_assoc G g h s)^)))).

  Definition absGTor : Type := component absGSet absprtor.

  (** Definition [def:Hom-absG]: maps and isomorphisms of [G]-sets.
      (Placed here, before [def:concr], since the identifications of
      [G]-sets below are given by isomorphisms.) *)
  Definition isGHom (X Y : absGSet) (f : gset X -> gset Y) : Type
    := forall s x, f (gact X s x) = gact Y s (f x).

  Definition isGHom_isProp (X Y : absGSet) (f : gset X -> gset Y) : isProp (isGHom X Y f)
    := Pi_isProp (fun s => Pi_isProp (fun x => gset_isSet Y _ _)).

  Definition absHomG (X Y : absGSet) : Type := {f : gset X -> gset Y & isGHom X Y f}.

  Definition gIso (X Y : absGSet) : Type := {f : gset X ≃ gset Y & isGHom X Y (fst f)}.

  Definition gIso_id (X : absGSet) : gIso X X := (idEqv _; fun s x => refl).

  Definition path_gIso {X Y : absGSet} (f g : gIso X Y)
    (h : forall x, fst (fst f) x = fst (fst g) x) : f = g
    := path_sigma_prop (fun k => isGHom_isProp X Y (fst k))
         (path_Eqv _ _ (ptw_inv h)).

  Definition idtogIso {X Y : absGSet} (p : X = Y) : gIso X Y
    := match p with refl => gIso_id X end.

  Definition idtogIso_trans_pt {X Y Z : absGSet} (p : X = Y) (q : Y = Z) (x : gset X)
    : fst (fst (idtogIso (q ⋅ p))) x = fst (fst (idtogIso q)) (fst (fst (idtogIso p)) x).
  Proof. destruct q, p. exact refl. Defined.

  (** The structure identity principle for [G]-sets: [(X = Y) ≃ gIso(X,Y)]. *)
  Definition absHom_paths_eqv {X : SetU} (φ ψ : absHom G (ag_Perm X))
    : (φ = ψ) ≃ (forall s x, fst (fst φ s) x = fst (fst ψ s) x).
  Proof.
    refine (Eqv_comp (subtype_paths_eqv (fun k => isAbsHomFun_isProp G (ag_Perm X) k) φ ψ) _).
    refine (Eqv_comp (ptw; funext _ _) _).
    refine (Pi_eqv (fun s => Eqv_comp (subtype_paths_eqv (fun f => isEquiv_isProp f) _ _) _)).
    exact (ptw; funext _ _).
  Defined.

  Definition gIso_total_contr (X : absGSet) : isContr {Y : absGSet & gIso X Y}.
  Proof.
    refine (isContr_Eqv (mkEqv
      (fun v : {w : {T : SetU & gset X ≃ fst T} &
                 {ψ : absHom G (ag_Perm (fst w)) & isGHom X (fst w; ψ) (fst (snd w))}} =>
         let Y0 := ((fst (fst v); fst (snd v)) : absGSet) in
         exist (fun Y => gIso X Y) Y0
           (exist (fun f : gset X ≃ gset Y0 => isGHom X Y0 (fst f))
              (snd (fst v)) (snd (snd v))))
      (fun u : {Y : absGSet & gIso X Y} =>
         (((fst (fst u); fst (snd u)) : {T : SetU & gset X ≃ fst T});
          (snd (fst u); snd (snd u))))
      (fun _ => refl) (fun _ => refl)) _).
    refine (Sigma_isContr_base (SetU_total_contr (fst X)) (fst X; idEqv _) _).
    refine (isContr_Eqv (tot (fun ψ (p : snd X = ψ) => fst (absHom_paths_eqv (snd X) ψ) p);
                         tot_isEquiv _ (fun ψ => snd (absHom_paths_eqv (snd X) ψ)))
              (singleton_contr (snd X))).
  Defined.

  Definition idtogIso_isEquiv (X Y : absGSet) : isEquiv (@idtogIso X Y)
    := isEquiv_from_tot (fun Y => @idtogIso X Y)
         (contr_map_isEquiv (singleton_contr X) (gIso_total_contr X) _) Y.

  Definition gIso_eqv (X Y : absGSet) : (X = Y) ≃ gIso X Y
    := (idtogIso; idtogIso_isEquiv X Y).

  Definition path_absGSet {X Y : absGSet} (f : gIso X Y) : X = Y
    := eqinv (idtogIso_isEquiv X Y) f.

  (** The type of torsors is a connected groupoid, locally [U]-small. *)
  Definition absGTor_isGrpd : isGrpd absGTor := component_isGrpd absGSet_isGrpd absprtor.

End AbsGSets.

Arguments gset {_ G} X.
Arguments gact {_ G} X s x.
Arguments gIso {_ G} X Y.
Arguments isGHom {_ G} X Y f.
Arguments idtogIso {_ G X Y} p.
Arguments path_gIso {_ G X Y} f g h.
Arguments path_absGSet {_ G X Y} f.

(** Exercise [xca:absprtorsor]: the principal torsor is identified with
    [(S, g ↦ (s ↦ s · g⁻¹))], via the inverse. *)
Section RightTorsor.

  Context `{Univalence} (G : AbsGroup).

  Definition rmul_inv_eqv (g : ag_S G) : ag_S G ≃ ag_S G
    := ((fun s => s · ag_inv G g); ag_rmul_isEquiv G (ag_inv G g)).

  Definition absprtor_right : absGSet G.
  Proof.
    refine ((ag_S G; ag_isSet G); (rmul_inv_eqv; _)).
    intros g h. apply path_Eqv. apply ptw_inv. intro s. cbn.
    rewrite ag_inv_mul. exact (ag_assoc G _ _ _).
  Defined.

  Definition absprtor_right_path : absprtor G = absprtor_right.
  Proof.
    apply path_absGSet. refine ((ag_inv G; ag_inv_isEquiv G); _).
    intros g s. exact (ag_inv_mul G g s).
  Defined.

End RightTorsor.

(** Definition [def:concr]: the group classified by [(absGTor, absprtor)].
    Since [absGTor] contains the type of sets, [concr G] lives in the
    universe above the one of [G]. *)
Definition concr `{Univalence} (G : AbsGroup) : Group
  := AutG (absGSet_isGrpd G) (absprtor G).


(** Example [ex:BqG], definition [def:qG-concr-abstr] and lemma
    [lem:Groupsareidentitytypes].  Footnote [ft:shG=z]: [P_G(z)] with
    precomposition by inverses is also an [abstr(G)]-set (informal). *)
Section ConcrAbstr.

  Context `{Univalence} (G : Group).

  Local Notation A := (abstr G).

  Definition post_isEquiv {z : utype (BG G)} (g : USym G)
    : isEquiv (fun p : z = sh G => g ⋅ p).
  Proof.
    refine (iso_to_isEquiv _ (fun p => g⁻¹ ⋅ p) _ _); intro p.
    - exact (trans_assoc p g g⁻¹ @ ap (fun q => q ⋅ p) (trans_pV g)).
    - exact (trans_assoc p g⁻¹ g @ ap (fun q => q ⋅ p) (trans_Vp g)).
  Defined.

  (** [Bq_G(z) :≡ ((z = sh_G), post_z)]. *)
  Definition post_eqv (z : utype (BG G)) (g : USym G) : (z = sh G) ≃ (z = sh G)
    := ((fun p => g ⋅ p); post_isEquiv g).

  Definition Bq_set (z : utype (BG G)) : absGSet A
    := (((z = sh G); BG_isGrpd G z (sh G)) : SetU;
        (post_eqv z;
         fun g h => path_Eqv (post_eqv z (g ⋅ h)) (Eqv_comp (post_eqv z h) (post_eqv z g))
                      (ptw_inv (fun p => (trans_assoc p h g)^)))).

  Definition Bq_pt_iso : gIso (absprtor A) (Bq_set (sh G)).
  Proof. exists (idEqv (USym G)). intros s x. exact refl. Defined.

  Definition Bq_pt_path : absprtor A = Bq_set (sh G) := path_absGSet Bq_pt_iso.

  Definition Bq (z : utype (BG G)) : absGTor A
    := (Bq_set z; ptrunc_rec ptrunc_isProp (fun q => trunc (ap Bq_set q ⋅ Bq_pt_path))
                    (snd (BG_isConn G) (sh G) z)).

  Definition Bq_ptd : BG G →* BG (concr A)
    := (Bq; @path_sigma_prop _ (fun Y => ptrunc (absprtor A = Y)) (fun _ => ptrunc_isProp)
              (absprtor A; trunc refl) (Bq (sh G)) Bq_pt_path).

  (** The induced map on identity types is precomposition with the
      inverse. *)
  Definition preinv_pt {x y : utype (BG G)} (r : x = y) (p : x = sh G)
    : fst (fst (idtogIso (ap Bq_set r))) p = p ⋅ r⁻¹.
  Proof. destruct r. exact (trans_1p p)^. Defined.

  Definition preinv (r : sh G = sh G) : gIso (Bq_set (sh G)) (Bq_set (sh G))
    := idtogIso (ap Bq_set r).

  Definition preinv_isEquiv : isEquiv preinv.
  Proof.
    refine (iso_to_isEquiv _ (fun f => (fst (fst f) refl)⁻¹) _ _).
    - intro r. refine (ap symm (preinv_pt r refl) @ _). exact (symm_symm r).
    - intros [[f tf] c].
      refine (@path_gIso _ A (Bq_set (sh G)) (Bq_set (sh G)) _ ((f; tf); c) _).
      intro p. cbn in c |- *.
      refine (preinv_pt _ p @ _).
      refine (ap (fun q => p ⋅ q) (symm_symm _) @ _).
      refine ((c p refl)^ @ _). exact (ap f (trans_1p p)).
  Defined.

  Definition Bq_isEquiv : isEquiv Bq.
  Proof.
    apply (snd (conn_isEquiv_iff_point Bq (BG_isConn G) (component_isConn _) (sh G))).
    pose (s := subtype_paths_eqv (fun Y : absGSet A => @ptrunc_isProp (absprtor A = Y))
                 (Bq (sh G)) (Bq (sh G))).
    pose (Φ := gIso_eqv A (Bq_set (sh G)) (Bq_set (sh G))).
    refine (isEquiv_homotopic (eqinv (snd s) ∘ (eqinv (snd Φ) ∘ preinv)) _ _
              (comp_isEquiv (comp_isEquiv preinv_isEquiv (eqinv_isEquiv (snd Φ)))
                 (eqinv_isEquiv (snd s)))).
    intro r. apply (isInj_cancel (isEquiv_isInj (snd s))).
    refine (eqinv_r (snd s) _ @ _).
    refine (eqinv_l (snd Φ) _ @ _).
    exact (ap_compose Bq fst r).
  Defined.

  Definition Bq_pEqv : BG G ≃* BG (concr A) := (Bq_ptd; Bq_isEquiv).

  (** [q_G : Hom(G, concr(abstr(G)))] is an isomorphism. *)
  Definition qG : Hom G (concr A) := mkhom Bq_ptd.

  Definition qG_isIso : isIso qG := Bq_isEquiv.

End ConcrAbstr.

(** The isomorphism [r_G : G ≅ abstr(concr(G))] (abstract Cayley,
    footnote [ft:abstract-Cayley]) of the proof of theorem
    [thm:Groupsareidentitytypes].
    (Placed before the theorem, whose proof uses it.) *)
Section AbstrConcr.

  Context `{Univalence} (G : AbsGroup).

  Local Notation P := (absprtor G).

  Definition rho (u : ag_S G) : gIso P P
    := (rmul_inv_eqv G u; fun g s => (ag_assoc G g s (ag_inv G u))^).

  Definition rho_isEquiv : isEquiv rho.
  Proof.
    refine (iso_to_isEquiv _ (fun f => ag_inv G (fst (fst f) (ag_e G))) _ _).
    - intro u. cbn. refine (ap (ag_inv G) (ag_lunit G _) @ _). exact (ag_inv_inv G u).
    - intros [[f tf] c].
      refine (@path_gIso _ G P P _ ((f; tf); c) _).
      intro s. cbn in c |- *.
      refine (ap (ag_mul G s) (ag_inv_inv G _) @ _).
      refine ((c s (ag_e G))^ @ _). exact (ap f (ag_runit G s)).
  Defined.

  (** [J : USym(concr G) ≃ gIso(P, P)]. *)
  Definition Jeqv : USym (concr G) ≃ gIso P P
    := Eqv_comp (USym_AutG_eqv (absGSet_isGrpd G) P) (gIso_eqv G P P).

  Definition rG : ag_S G -> USym (concr G) := comp (eqinv (snd Jeqv)) rho.

  Definition rG_isEquiv : isEquiv rG
    := comp_isEquiv rho_isEquiv (eqinv_isEquiv (snd Jeqv)).

  Definition J_trans_pt (a b : USym (concr G)) (x : ag_S G)
    : fst (fst (fst Jeqv (a ⋅ b))) x = fst (fst (fst Jeqv a)) (fst (fst (fst Jeqv b)) x).
  Proof.
    refine (ap (fun q : P = P => fst (fst (@idtogIso _ G P P q)) x) (ap_trans fst b a) @ _).
    exact (@idtogIso_trans_pt _ G P P P _ _ x).
  Defined.

  Definition rG_mul : isAbsHomFun G (abstr (concr G)) rG.
  Proof.
    intros u v. apply (isInj_cancel (isEquiv_isInj (snd Jeqv))).
    apply path_gIso. intro x.
    refine (ap (fun f => fst (fst f) x) (eqinv_r (snd Jeqv) (rho (u · v))) @ _).
    refine (_ @ (J_trans_pt _ _ x)^).
    refine (_ @ ap (fun f => fst (fst f) _) (eqinv_r (snd Jeqv) (rho u))^).
    refine (_ @ ap (fun f => fst (fst f) x · ag_inv G u) (eqinv_r (snd Jeqv) (rho v))^).
    cbn. rewrite ag_inv_mul. exact (ag_assoc G _ _ _).
  Defined.

  Definition rG_iso : AbsIso G (abstr (concr G)) := ((rG; rG_isEquiv); rG_mul).

End AbstrConcr.

(** Theorem [thm:Groupsareidentitytypes].  [concr(G)] lives in the next
    universe, so to get an inverse of [abstr : Group → AbsGroup] within
    one universe we use the replacement principle (Section 2.19): the
    type of torsors is a component of a locally small type, hence
    essentially small (exercise [xca:comp-loc-small-ess-small]).  NOTE for
    the book text: the size issue is not mentioned there. *)
Definition absGSet_locSmall `{Univalence} (G : AbsGroup) : locSmall (absGSet G)
  := fun X Y => (gIso X Y; gIso_eqv G X Y).

Definition absGTor_small `{Univalence} (rep : Replacement) (G : AbsGroup)
  : essSmall (absGTor G)
  := replacement_component rep (absGSet_locSmall G) (absprtor G).

Definition concr_small `{Univalence} (rep : Replacement) (G : AbsGroup) : Group
  := let s := absGTor_small rep G in
     mkgroup (fst s; (fst (snd s) (absprtor G; trunc refl);
                      (isConn_Eqv (snd s) (component_isConn _);
                       is_ntype_Eqv 1 (snd s) (absGTor_isGrpd G)))).

Definition concr_small_pEqv `{Univalence} (rep : Replacement) (G : AbsGroup)
  : BG (concr G) ≃* BG (concr_small rep G)
  := ((fst (snd (absGTor_small rep G)); refl); snd (snd (absGTor_small rep G))).

Definition abstr_concr_small_iso `{Univalence} (rep : Replacement) (G : AbsGroup)
  : AbsIso G (abstr (concr_small rep G)).
Proof.
  pose (e := snd (absGTor_small rep G)).
  refine ((ap (fst e) ∘ rG G; comp_isEquiv (rG_isEquiv G) (ap_isEquiv_of (snd e) _ _)); _).
  intros u v. refine (ap (ap (fst e)) (rG_mul G u v) @ _).
  exact (ap_trans _ _ _).
Defined.

Definition concr_abstr_path `{Univalence} (rep : Replacement) (G : Group)
  : G = concr_small rep (abstr G)
  := path_Group (pEqv_comp (Bq_pEqv G) (concr_small_pEqv rep (abstr G))).

Definition abstr_isEquiv `{Univalence} (rep : Replacement) : isEquiv abstr
  := iso_to_isEquiv abstr (concr_small rep)
       (fun G => (concr_abstr_path rep G)^)
       (fun G => (path_AbsGroup (abstr_concr_small_iso rep G))^).

(** *** 7.4.1 The left and right adjoint of restriction, abstractly *)

Definition gact_mul `{Univalence} {G : AbsGroup} (X : absGSet G) (a b : ag_S G)
  (x : gset X) : gact X (a · b) x = gact X a (gact X b x)
  := ptw (ap fst (snd (snd X) a b)) x.
Section AbsRestrict.

  Context `{Uv : Univalence} {G H : AbsGroup} (φ : absHom G H).

  (** Definition [def:phi^*]. *)
  Definition abs_restrict (Y : absGSet H) : absGSet G.
  Proof.
    refine (fst Y; (fun s => fst (snd Y) (fst φ s); _)).
    intros s t. exact (ap (fst (snd Y)) (snd φ s t) @ snd (snd Y) _ _).
  Defined.

End AbsRestrict.


Section PhiShriek.

  Context `{Uv : Univalence} {G H : AbsGroup} (φ : absHom G H).

  (** Definition [def:phi_!] and exercises [xca:phi_!-OK],
      [xca:phi_!-|phi^*] (statements only).  The relation on [T × X]:
      [(t, x) ∼ (u, y) :≡ ∃_g (t φ(g) = u) × (x = g ·_X y)]; [φ_!X] is the
      quotient with [h · [(t, x)] :≡ [(h t, x)]]. *)
  Definition phi_rel (X : absGSet G) (w w' : ag_S H × gset X) : PropU
    := (Ex (fun g : ag_S G => (fst w · fst φ g = fst w') × (snd w = gact X g (snd w')));
        ptrunc_isProp).

  Definition xca_phi_OK_stmt : Type
    := forall X : absGSet G,
         (forall w, fst (phi_rel X w w))
         × (forall w w', fst (phi_rel X w w') -> fst (phi_rel X w' w))
         × (forall w w' w'', fst (phi_rel X w w') -> fst (phi_rel X w' w'') -> fst (phi_rel X w w''))
         × (forall (h : ag_S H) w w', fst (phi_rel X w w')
              -> fst (phi_rel X ((h · fst w; snd w) : ag_S H × gset X) (h · fst w'; snd w'))).

  Definition def_phi_shriek_stmt : Type
    := {F : absGSet G -> absGSet H &
         forall X, {e : gset (F X) ≃ quot (phi_rel X) &
                     forall h t x, fst e (gact (F X) h (eqinv (snd e) (S22_SetOperations.cls (phi_rel X) (t; x))))
                                   = S22_SetOperations.cls (phi_rel X) (h · t; x)}}.

  Definition xca_phi_shriek_adj_stmt : Type
    := forall F : absGSet G -> absGSet H,
       forall X : absGSet G, forall Y : absGSet H,
       (forall X', gset (F X') ≃ quot (phi_rel X')) ->
       absHomG H (F X) Y ≃ absHomG G X (abs_restrict φ Y).
End PhiShriek.

Section AbsCoinduce.

  Context `{Uv : Univalence} {G H : AbsGroup} (φ : absHom G H).

  (** Definition [def:phi_*]: [φ_*(X) :≡ {b : T → X | b(t φ(s⁻¹)) = s b(t)}],
      with action [h · b :≡ b(h⁻¹ ·)]. *)
  Definition coind_pred (X : absGSet G) (b : ag_S H -> gset X) : Type
    := forall s t, b (t · fst φ (ag_inv G s)) = gact X s (b t).

  Definition coind_pred_isProp (X : absGSet G) (b : ag_S H -> gset X)
    : isProp (coind_pred X b)
    := Pi_isProp (fun _ => Pi_isProp (fun _ => gset_isSet G X _ _)).

  Definition coind_set (X : absGSet G) : Type := {b : ag_S H -> gset X & coind_pred X b}.

  Definition coind_set_isSet (X : absGSet G) : isSet (coind_set X)
    := Sigma_isSet (Pi_isSet (fun _ => gset_isSet G X))
         (fun b => prop_is_set (coind_pred_isProp X b)).

  Definition coind_act0 (X : absGSet G) (h : ag_S H) (b : coind_set X) : coind_set X.
  Proof.
    refine ((fun t => fst b (ag_inv H h · t)); _).
    intros s t. refine (_ @ snd b s _). exact (ap (fst b) (ag_assoc H _ _ _)).
  Defined.

  Definition path_coind {X : absGSet G} (b b' : coind_set X)
    (e : forall t, fst b t = fst b' t) : b = b'
    := path_sigma_prop (coind_pred_isProp X) (ptw_inv e).

  Definition coind_act_comp (X : absGSet G) (g h : ag_S H) (b : coind_set X)
    : coind_act0 X (g · h) b = coind_act0 X g (coind_act0 X h b).
  Proof.
    apply path_coind. intro t. cbn. apply (ap (fst b)).
    rewrite ag_inv_mul. exact (ag_assoc H _ _ _)^.
  Defined.

  Definition coind_act_e (X : absGSet G) (b : coind_set X) : coind_act0 X (ag_e H) b = b.
  Proof.
    apply path_coind. intro t. cbn. apply (ap (fst b)).
    rewrite ag_inv_e. exact (ag_lunit H t).
  Defined.

  Definition coind_act_eqv (X : absGSet G) (h : ag_S H) : coind_set X ≃ coind_set X.
  Proof.
    refine (coind_act0 X h; iso_to_isEquiv _ (coind_act0 X (ag_inv H h)) _ _); intro b.
    - refine ((coind_act_comp X _ _ b)^ @ _).
      refine (ap (fun k => coind_act0 X k b) (ag_linv H h) @ _). exact (coind_act_e X b).
    - refine ((coind_act_comp X _ _ b)^ @ _).
      refine (ap (fun k => coind_act0 X k b) (ag_rinv H h) @ _). exact (coind_act_e X b).
  Defined.

  Definition abs_coinduce (X : absGSet G) : absGSet H.
  Proof.
    refine ((coind_set X; coind_set_isSet X); (coind_act_eqv X; _)).
    intros g h. apply path_Eqv. apply ptw_inv. intro b. exact (coind_act_comp X g h b).
  Defined.

  (** Exercise [xca:phi^*-|phi_*]:
      [Hom_G(φ^* Y, X) ≃ Hom_H(Y, φ_* X)]. *)
  Context (Y : absGSet H) (X : absGSet G).

  Definition adj_fw_elt (F : absHomG G (abs_restrict φ Y) X) (y : gset Y) : coind_set X.
  Proof.
    refine ((fun t => fst F (gact Y (ag_inv H t) y)); _).
    intros s t. refine (_ @ snd F s _). apply (ap (fst F)).
    change (gact (abs_restrict φ Y) s ?z) with (gact Y (fst φ s) z).
    rewrite <- !gact_mul. apply (ap (fun g => gact Y g y)).
    rewrite ag_inv_mul, (absHom_inv (fst φ) (snd φ)), ag_inv_inv. exact refl.
  Defined.

  Definition adj_fw (F : absHomG G (abs_restrict φ Y) X) : absHomG H Y (abs_coinduce X).
  Proof.
    refine (adj_fw_elt F; _).
    intros h y. apply path_coind. intro t. cbn. apply (ap (fst F)).
    rewrite <- !gact_mul. apply (ap (fun g => gact Y g y)).
    rewrite ?ag_inv_mul, ?ag_inv_inv. exact refl.
  Defined.

  Definition adj_bw (k : absHomG H Y (abs_coinduce X)) : absHomG G (abs_restrict φ Y) X.
  Proof.
    refine ((fun y => fst (fst k y) (ag_e H)); _).
    intros s y. cbn.
    refine (ap (fun b => fst b (ag_e H)) (snd k (fst φ s) y) @ _). cbn.
    refine (_ @ snd (fst k y) s (ag_e H)). apply (ap (fst (fst k y))).
    rewrite (absHom_inv (fst φ) (snd φ)), ag_runit, ag_lunit. exact refl.
  Defined.

  Definition abs_adj_restrict_coinduce
    : absHomG G (abs_restrict φ Y) X ≃ absHomG H Y (abs_coinduce X).
  Proof.
    refine (mkEqv adj_fw adj_bw _ _).
    - intro F. refine (path_sigma_prop (fun f => isGHom_isProp G _ _ f) _).
      apply ptw_inv. intro y. cbn. apply (ap (fst F)).
      rewrite ag_inv_e. exact (ptw (ap fst (absHom_unit _ (snd (snd Y)))) y).
    - intro k. refine (path_sigma_prop (fun f => isGHom_isProp H _ _ f) _).
      apply ptw_inv. intro y. apply path_coind. intro t. cbn.
      refine (ap (fun b => fst b (ag_e H)) (snd k (ag_inv H t) y) @ _). cbn.
      apply (ap (fst (fst k y))).
      rewrite ag_inv_inv. exact (ag_runit H t).
  Defined.

End AbsCoinduce.

