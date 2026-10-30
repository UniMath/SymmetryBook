(** * Section 7.2 Monoids and abstract groups

    Part of Chapter 7 ([absgroup.tex]); see [AbsGroup.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:monoid]: the record [Monoid]; example
      [exa:monoid]: lists under concatenation ([list_monoid]); the
      underlying monoid of an abstract group ([ag_monoid]).
    - The propositions [UnitLaws], [AssocLaw], [MonoidLaws], [InverseLaw],
      [GroupLaws] and definition [def:type-abstrgp] ([AbsGroupSig]).  We
      keep the record [AbsGroup] of Section 4.3, which is the book's
      [Σ]-type up to the position of [isSet(S)] and the bracketing of the
      laws; [issig_AbsGroup] is the library's equivalence of the record
      with its [Σ]-type.
    - Lemma [lem:group-inv-operation]: under the mere existence of right
      inverses the fibers [μ(g)⁻¹(e)] are contractible
      ([inv_fiber_isContr]), hence the type of inverse operations is
      contractible ([inverse_operation_isContr]).
    - Exercise [xca:left-inv-involution]: [ag_linv] (Section 4.3) and
      [ag_inv_inv]; further [ag_inv_mul], [ag_inv_e], cancellation, and
      left/right multiplication as equivalences.
    - Remark [rem:abs-iso]: isomorphisms of abstract groups ([AbsIso]),
      and from an isomorphism an identification ([path_AbsGroup]), by
      equivalence induction ([Eqv_ind]) and the fact that unit and inverse
      are determined by the multiplication ([path_AbsGroup_mul]).
      Conversely, [path_AbsGroup] is an equivalence
      ([path_AbsGroup_isEquiv], the full analysis of [rem:abs-iso]): it
      is a section of [idtoAbsIso] ([idtoAbsIso_path], using the
      computation rule [Eqv_ind_beta]), so the isomorphisms out of [G]
      form a contractible type.
    - Exercise [xca:typemonoidisgroupoid] ([Monoid_isGrpd],
      [AbsGroup_isGrpd]).
    - Exercise [xca:op-abs-group]: [ag_op] and the isomorphism [op_iso]
      given by the inverse.
    - Exercise [xca:conj]: conjugation [conj] is an isomorphism
      ([conj_iso], [conj_path]), with [conj_comp] and [conj_e].
    - Exercise [xca:cheapgroup]: sheargroups ([Sheargroup]) and the
      equivalence [group_shear_eqv], with [ā̄ = a] ([sg_bar_bar]) as in
      the hint.

    Left out (statements only, no proofs yet; time limit per result)
    - Exercise on Furstenberg groups ([Furstenberg],
      [xca_furstenberg_stmt]).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Spaces.List.Core.
From SymmetryBook Require Export Cats.Cats.

Local Open Scope uf_scope.

(** ** 7.2 Monoids and abstract groups *)

(** Definition [def:monoid]. *)
Record Monoid : Type := {
  (** [struc:monoid-set] *)
  mo_S : Type;
  mo_isSet : isSet mo_S;
  (** [struc:monoid-unit] *)
  mo_e : mo_S;
  (** [struc:monoid-mult] *)
  mo_mul : mo_S -> mo_S -> mo_S;
  (** [monoid:unit-laws] *)
  mo_runit : forall g, mo_mul g mo_e = g;
  mo_lunit : forall g, mo_mul mo_e g = g;
  (** [monoid:ass-law] *)
  mo_assoc : forall g1 g2 g3, mo_mul g1 (mo_mul g2 g3) = mo_mul (mo_mul g1 g2) g3
}.

(** Example [exa:monoid]: lists under concatenation. *)
Definition app_nil_right {X : Type} (l : X^*) : app l ε = l.
Proof.
  induction l as [|x l IH].
  - exact refl.
  - exact (ap (cons x) IH).
Defined.

Definition list_monoid (X : SetU) : Monoid
  := {| mo_S := (fst X)^*;
        mo_isSet := list_isSet (snd X);
        mo_e := ε;
        mo_mul := app;
        mo_runit := app_nil_right;
        mo_lunit := fun l => refl;
        mo_assoc := app_assoc |}.

(** The underlying monoid of an abstract group. *)
Definition ag_monoid (G : AbsGroup) : Monoid
  := {| mo_S := ag_S G; mo_isSet := ag_isSet G; mo_e := ag_e G; mo_mul := ag_mul G;
        mo_runit := ag_runit G; mo_lunit := ag_lunit G; mo_assoc := ag_assoc G |}.

(** Notation [not:GroupLaws]: the propositions [UnitLaws], [AssocLaw],
    [MonoidLaws], [InverseLaw] and [GroupLaws]. *)
Section Laws.

  Context (S : Type) (e : S) (μ : S -> S -> S) (ι : S -> S).

  Definition UnitLaws : Type := forall g : S, (μ g e = g) × (μ e g = g).

  Definition AssocLaw : Type
    := forall g1 g2 g3 : S, μ g1 (μ g2 g3) = μ (μ g1 g2) g3.

  Definition MonoidLaws : Type := isSet S × (UnitLaws × AssocLaw).

  Definition InverseLaw : Type := forall g : S, μ g (ι g) = e.

  Definition GroupLaws : Type := MonoidLaws × InverseLaw.

End Laws.

(** Definition [def:type-abstrgp]: the book's type of abstract groups as an
    iterated [Σ]-type.  The record [AbsGroup] of Section 4.3 is this type
    up to the position of [isSet(S)] and the bracketing of the laws; the
    library's [issig] gives the equivalence with the record. *)
Definition AbsGroupSig : Type
  := {S : Type & {e : S & {μ : S -> S -> S & {ι : S -> S & GroupLaws S e μ ι}}}}.

Definition issig_AbsGroup : _ <~> AbsGroup := ltac:(issig).

Definition issig_Monoid : _ <~> Monoid := ltac:(issig).

(** Remark [rem:inverses-as-property]: instead of the inverse operation
    [monoid:inv-op] ([ι] above, or [ag_inv]) with the law of inverses
    [monoid:inv-law] ([InverseLaw]), one may posit [axiom:mere-inverse]
    (the hypothesis [minv] below); [lem:group-inv-operation] shows that
    this gives a unique inverse operation. *)
Section Inverses.

  Context `{Funext} (S : Type) (sS : isSet S) (e : S) (μ : S -> S -> S)
    (ru : forall g, μ g e = g) (lu : forall g, μ e g = g)
    (asc : forall g1 g2 g3, μ g1 (μ g2 g3) = μ (μ g1 g2) g3)
    (minv : forall g, ptrunc {h : S & e = μ g h}).

  (** Lemma [lem:group-inv-operation]: the fiber [μ(g)⁻¹(e)] is
      contractible, hence there is a unique inverse operation. *)
  Definition left_of_right (g h : S) (r : e = μ g h) : μ h g = e.
  Proof.
    refine (ptrunc_rec (sS _ _) _ (minv h)). intros [k s].
    assert (kg : k = g).
    { refine ((lu k)^ @ _). refine (ap (fun x => μ x k) r @ _).
      refine ((asc g h k)^ @ _). refine (ap (μ g) s^ @ _). exact (ru g). }
    destruct kg. exact s^.
  Defined.

  Definition inv_fiber_isContr (g : S) : isContr {h : S & e = μ g h}.
  Proof.
    refine (ptrunc_rec (isContr_isProp _) _ (minv g)). intros [h r].
    refine ((h; r); _). intros [h' r'].
    refine (@path_sigma_prop S (fun h => e = μ g h) (fun _ => sS _ _) (h; r) (h'; r') _). cbn.
    refine ((ru h)^ @ _). refine (ap (μ h) r' @ _). refine (asc h g h' @ _).
    refine (ap (fun x => μ x h') (left_of_right g h r) @ _). exact (lu h').
  Defined.

  Definition inverse_operation_isContr
    : isContr {ι : S -> S & forall g, e = μ g (ι g)}.
  Proof.
    refine (isContr_Eqv (type_theoretic_AC S S (fun g h => e = μ g h)) _).
    exact (@isContr_of_Contr _ (@contr_forall _ S _
             (fun g => Contr_of_isContr (inv_fiber_isContr g)))).
  Defined.

End Inverses.

(** Notation for abstract groups. *)
Declare Scope ag_scope.
Local Notation "g · h" := (ag_mul _ g h) (at level 40, left associativity) : ag_scope.
Local Notation "g ⁻" := (ag_inv _ g) (at level 3, format "g ⁻") : ag_scope.
Local Open Scope ag_scope.

Section GroupFacts.

  Context (G : AbsGroup).

  Local Notation S := (ag_S G).
  Local Notation e := (ag_e G).

  (** Uniqueness of inverses. *)
  Definition ag_inv_unique (g h : S) (r : g · h = e) : h = ag_inv G g.
  Proof.
    refine ((ag_lunit G h)^ @ _). refine (ap (fun x => x · h) (ag_linv G g)^ @ _).
    refine ((ag_assoc G _ _ _)^ @ _). refine (ap (ag_mul G _) r @ _).
    exact (ag_runit G _).
  Defined.

  (** Exercise [xca:left-inv-involution]: [e = g⁻¹ · g] is [ag_linv]
      (Section 4.3), and [g = (g⁻¹)⁻¹].
    (Placed with the other facts on inverses, before [rem:abs-iso], which uses them.) *)
  Definition ag_inv_inv (g : S) : ag_inv G (ag_inv G g) = g
    := (ag_inv_unique (ag_inv G g) g (ag_linv G g))^.

  Definition ag_inv_mul (a b : S) : ag_inv G (a · b) = ag_inv G b · ag_inv G a.
  Proof.
    refine (ag_inv_unique (a · b) _ _)^.
    refine (ag_assoc G _ _ _ @ _).
    refine (ap (fun x => x · _) (ag_assoc G _ _ _)^ @ _).
    refine (ap (fun x => a · x · _) (ag_rinv G b) @ _).
    refine (ap (fun x => x · _) (ag_runit G a) @ _).
    exact (ag_rinv G a).
  Defined.

  Definition ag_inv_e : ag_inv G e = e
    := (ag_inv_unique e e (ag_runit G e))^.

  Definition ag_cancel_l (a b c : S) (r : a · b = a · c) : b = c.
  Proof.
    refine ((ag_lunit G b)^ @ _). refine (ap (fun x => x · b) (ag_linv G a)^ @ _).
    refine ((ag_assoc G _ _ _)^ @ _). refine (ap (ag_mul G _) r @ _).
    refine (ag_assoc G _ _ _ @ _). refine (ap (fun x => x · c) (ag_linv G a) @ _).
    exact (ag_lunit G c).
  Defined.

  Definition ag_cancel_r (a b c : S) (r : b · a = c · a) : b = c.
  Proof.
    refine ((ag_runit G b)^ @ _). refine (ap (ag_mul G b) (ag_rinv G a)^ @ _).
    refine (ag_assoc G _ _ _ @ _). refine (ap (fun x => x · _) r @ _).
    refine ((ag_assoc G _ _ _)^ @ _). refine (ap (ag_mul G c) (ag_rinv G a) @ _).
    exact (ag_runit G c).
  Defined.

  (** Left multiplication is an equivalence. *)
  Definition ag_lmul_isEquiv (g : S) : isEquiv (ag_mul G g).
  Proof.
    refine (iso_to_isEquiv _ (ag_mul G (ag_inv G g)) _ _); intro s.
    - refine (ag_assoc G _ _ _ @ _). refine (ap (fun x => x · s) (ag_linv G g) @ _).
      exact (ag_lunit G s).
    - refine (ag_assoc G _ _ _ @ _). refine (ap (fun x => x · s) (ag_rinv G g) @ _).
      exact (ag_lunit G s).
  Defined.

  Definition ag_rmul_isEquiv (g : S) : isEquiv (fun s => s · g).
  Proof.
    refine (iso_to_isEquiv _ (fun s => s · ag_inv G g) _ _); intro s.
    - refine ((ag_assoc G _ _ _)^ @ _). refine (ap (ag_mul G s) (ag_rinv G g) @ _).
      exact (ag_runit G s).
    - refine ((ag_assoc G _ _ _)^ @ _). refine (ap (ag_mul G s) (ag_linv G g) @ _).
      exact (ag_runit G s).
  Defined.

End GroupFacts.

(** Remark [rem:abs-iso]: isomorphisms of abstract groups. *)
Definition isAbsHomFun (G H : AbsGroup) (f : ag_S G -> ag_S H) : Type
  := forall s t : ag_S G, f (s · t) = f s · f t.

Definition AbsIso (G H : AbsGroup) : Type
  := {f : ag_S G ≃ ag_S H & isAbsHomFun G H (fst f)}.

Definition AbsIso_id (G : AbsGroup) : AbsIso G G := (idEqv _; fun s t => refl).

(** Footnote [ft:no-abs-inftygp]: we do not know how to define a type of
    "abstract [∞]-groups" in a similar way (informal). *)

(** Two abstract groups with the same underlying set and the same
    multiplication are equal: the unit and the inverse are determined by
    the multiplication, and the rest are propositions. *)
Definition path_AbsGroup_mul `{Funext}
  (S : Type) (sS sS' : isSet S) (e e' : S) (μ : S -> S -> S) (ι ι' : S -> S)
  ru lu asc ri ru' lu' asc' ri'
  : {| ag_S := S; ag_isSet := sS; ag_e := e; ag_mul := μ; ag_inv := ι;
       ag_runit := ru; ag_lunit := lu; ag_assoc := asc; ag_rinv := ri |}
    = {| ag_S := S; ag_isSet := sS'; ag_e := e'; ag_mul := μ; ag_inv := ι';
         ag_runit := ru'; ag_lunit := lu'; ag_assoc := asc'; ag_rinv := ri' |}.
Proof.
  pose (G := {| ag_S := S; ag_isSet := sS; ag_e := e; ag_mul := μ; ag_inv := ι;
                ag_runit := ru; ag_lunit := lu; ag_assoc := asc; ag_rinv := ri |}).
  pose (G' := {| ag_S := S; ag_isSet := sS'; ag_e := e'; ag_mul := μ; ag_inv := ι';
                 ag_runit := ru'; ag_lunit := lu'; ag_assoc := asc'; ag_rinv := ri' |}).
  assert (pe : e = e') by exact ((ru' e)^ @ lu e').
  destruct pe.
  assert (pι : ι = ι').
  { apply ptw_inv. intro g. exact (ag_inv_unique G' g (ι g) (ri g)). }
  destruct pι.
  assert (ps : sS = sS') by apply isSet_isProp.
  destruct ps.
  assert (pru : ru = ru') by (apply ptw_inv; intro; apply sS).
  assert (plu : lu = lu') by (apply ptw_inv; intro; apply sS).
  assert (pasc : asc = asc')
    by (apply ptw_inv; intro; apply ptw_inv; intro; apply ptw_inv; intro; apply sS).
  assert (pri : ri = ri') by (apply ptw_inv; intro; apply sS).
  destruct pru, plu, pasc, pri. exact refl.
Defined.

(** Equivalence induction (from univalence). *)
Definition Eqv_ind `{Univalence} {X : Type} (P : forall Y : Type, X ≃ Y -> Type)
  (d : P X (idEqv X)) (Y : Type) (f : X ≃ Y) : P Y f.
Proof.
  refine (trp (P Y) (eqinv_r (ua X Y) f) _).
  generalize (eqinv (ua X Y) f). intro p. destruct p. exact d.
Defined.

(** From an isomorphism of abstract groups we get an identification. *)
Definition path_AbsGroup `{Univalence} {G K : AbsGroup} (f : AbsIso G K) : G = K.
Proof.
  destruct G as [S sS e μ ι ru lu asc ri].
  destruct K as [T sT e' μ' ι' ru' lu' asc' ri'].
  destruct f as [f hf]. cbn in f, hf.
  revert T f sT e' μ' ι' ru' lu' asc' ri' hf.
  refine (Eqv_ind _ _).
  intros sT e' μ' ι' ru' lu' asc' ri' hf. cbn in hf.
  assert (pμ : μ = μ').
  { apply ptw_inv; intro s; apply ptw_inv; intro t. exact (hf s t). }
  destruct pμ. apply path_AbsGroup_mul.
Defined.

(** The converse of [path_AbsGroup]: it is an equivalence
    [AbsIso(G,H) ≃ (G = H)], the full analysis of remark [rem:abs-iso]. *)
Definition path_AbsGroup_isEquiv_stmt `{Univalence} : Type
  := forall G K : AbsGroup, isEquiv (@path_AbsGroup _ G K).

(** The computation rule of equivalence induction, from the
    contractibility of the fiber of [idtoeqv] over [idEqv]. *)
Definition Eqv_J {X : Type} (P : forall Y : Type, X ≃ Y -> Type) (d : P X (idEqv X))
  {Y : Type} (p : X = Y) : X ≃ Y -> P Y (idtoeqv p)
  := match p with refl => fun _ => d end.

Definition Eqv_ind_beta `{Univalence} {X : Type} (P : forall Y : Type, X ≃ Y -> Type)
  (d : P X (idEqv X)) : Eqv_ind P d X (idEqv X) = d.
Proof.
  change (trp (P X) (eqinv_r (ua X X) (idEqv X))
            (Eqv_J P d (eqinv (ua X X) (idEqv X)) (idEqv X)) = d).
  pose (F := fun w : fiber (@idtoeqv X X) (idEqv X) =>
               trp (P X) (snd w)^ (Eqv_J P d (fst w) (idEqv X))).
  refine (ap (fun r => trp (P X) r _) (inv_V _)^ @ _).
  exact (ap F (isContr_isProp' (ua X X (idEqv X))
                 (eqinv (ua X X) (idEqv X); (eqinv_r (ua X X) (idEqv X))^) (refl; refl))).
Defined.

Definition ap_ag_S_path_AbsGroup_mul `{Funext}
  (S : Type) (sS sS' : isSet S) (e e' : S) (μ : S -> S -> S) (ι ι' : S -> S)
  ru lu asc ri ru' lu' asc' ri'
  : ap ag_S (path_AbsGroup_mul S sS sS' e e' μ ι ι' ru lu asc ri ru' lu' asc' ri') = refl.
Proof.
  unfold path_AbsGroup_mul. cbn.
  repeat match goal with |- context [match ?X with refl => _ end] => destruct X end.
  exact refl.
Defined.

(** The underlying map of the set is that of the isomorphism. *)
Definition path_AbsGroup_S `{Univalence} {G K : AbsGroup} (f : AbsIso G K)
  : ptoe (ap ag_S (path_AbsGroup f)) = fst (fst f).
Proof.
  destruct G as [S sS e μ ι ru lu asc ri].
  destruct K as [T sT e' μ' ι' ru' lu' asc' ri'].
  destruct f as [f hf]. cbn in f, hf.
  revert T f sT e' μ' ι' ru' lu' asc' ri' hf.
  refine (Eqv_ind _ _).
  intros sT e' μ' ι' ru' lu' asc' ri' hf.
  unfold path_AbsGroup. cbn. rewrite Eqv_ind_beta. cbn.
  match goal with |- context [match ?X with refl => _ end] => destruct X end.
  exact (ap ptoe (ap_ag_S_path_AbsGroup_mul S sS sT e e' μ ι ι' ru lu asc ri ru' lu' asc' ri')).
Defined.

Definition idtoAbsIso {G K : AbsGroup} (p : G = K) : AbsIso G K
  := match p with refl => AbsIso_id G end.

Definition idtoAbsIso_S {G K : AbsGroup} (p : G = K)
  : fst (fst (idtoAbsIso p)) = ptoe (ap ag_S p).
Proof. destruct p. exact refl. Defined.

Definition idtoAbsIso_path `{Univalence} {G K : AbsGroup} (f : AbsIso G K)
  : idtoAbsIso (path_AbsGroup f) = f.
Proof.
  apply (path_sigma_prop (fun g => Pi_isProp (fun _ => Pi_isProp (fun _ => ag_isSet K _ _)))).
  apply path_Eqv. exact (idtoAbsIso_S _ @ path_AbsGroup_S f).
Defined.

Definition path_AbsGroup_isEquiv `{Univalence} : path_AbsGroup_isEquiv_stmt.
Proof.
  intros G K.
  assert (c : isContr {K' : AbsGroup & AbsIso G K'}).
  { refine ((G; AbsIso_id G); _). intros [K' f].
    refine (ap (tot (fun K'' (p : G = K'') => idtoAbsIso p))
              (isContr_isProp' (singleton_contr G) (G; refl) (K'; path_AbsGroup f)) @ _).
    exact (ap (fun g => (K'; g) : {K'' : AbsGroup & AbsIso G K''}) (idtoAbsIso_path f)). }
  pose (t := isEquiv_from_tot (fun K' (p : G = K') => idtoAbsIso p)
               (contr_map_isEquiv (singleton_contr G) c _) K).
  refine (isEquiv_homotopic (eqinv t) _ _ (eqinv_isEquiv t)).
  intro f. exact (ap (eqinv t) (idtoAbsIso_path f)^ @ eqinv_l t _).
Defined.

(** Exercise [xca:op-abs-group]: the opposite group, and the inverse as an
    isomorphism [G ≅ G^op]. *)
Definition ag_op (G : AbsGroup) : AbsGroup
  := {| ag_S := ag_S G; ag_isSet := ag_isSet G; ag_e := ag_e G;
        ag_mul := fun a b => b · a; ag_inv := ag_inv G;
        ag_runit := ag_lunit G; ag_lunit := ag_runit G;
        ag_assoc := fun g1 g2 g3 => (ag_assoc G g3 g2 g1)^;
        ag_rinv := ag_linv G |}.

Definition ag_inv_isEquiv (G : AbsGroup) : isEquiv (ag_inv G)
  := iso_to_isEquiv _ (ag_inv G) (ag_inv_inv G) (ag_inv_inv G).

Definition op_iso (G : AbsGroup) : AbsIso G (ag_op G)
  := ((ag_inv G; ag_inv_isEquiv G); ag_inv_mul G).

Definition path_op `{Univalence} (G : AbsGroup) : G = ag_op G := path_AbsGroup (op_iso G).

(** Exercise [xca:conj]: conjugation [conj^g(s) :≡ g · s · g⁻¹]. *)
Definition conj (G : AbsGroup) (g s : ag_S G) : ag_S G := g · s · ag_inv G g.

Definition conj_mul (G : AbsGroup) (g : ag_S G) : isAbsHomFun G G (conj G g).
Proof.
  intros s t. unfold conj. symmetry.
  refine (ag_assoc G _ _ _ @ _). apply (ap (fun x => x · _)).
  refine ((ag_assoc G _ _ _)^ @ _). refine (_ @ (ag_assoc G g s t)^).
  apply (ap (ag_mul G (g · s))).
  refine (ag_assoc G _ _ _ @ _). refine (ap (fun x => x · t) (ag_linv G g) @ _).
  exact (ag_lunit G t).
Defined.

Definition conj_comp (G : AbsGroup) (a b s : ag_S G)
  : conj G a (conj G b s) = conj G (a · b) s.
Proof.
  unfold conj. rewrite ag_inv_mul. rewrite !ag_assoc. exact refl.
Defined.

Definition conj_e (G : AbsGroup) (s : ag_S G) : conj G (ag_e G) s = s.
Proof.
  unfold conj. rewrite ag_inv_e, ag_runit, ag_lunit. exact refl.
Defined.

Definition conj_isEquiv (G : AbsGroup) (g : ag_S G) : isEquiv (conj G g).
Proof.
  refine (iso_to_isEquiv _ (conj G (ag_inv G g)) _ _); intro s.
  - exact (conj_comp G _ _ s @ ap (fun x => conj G x s) (ag_linv G g) @ conj_e G s).
  - exact (conj_comp G _ _ s @ ap (fun x => conj G x s) (ag_rinv G g) @ conj_e G s).
Defined.

Definition conj_iso (G : AbsGroup) (g : ag_S G) : AbsIso G G
  := ((conj G g; conj_isEquiv G g); conj_mul G g).

Definition conj_path `{Univalence} (G : AbsGroup) (g : ag_S G) : G = G
  := path_AbsGroup (conj_iso G g).

(** Remark [rem:ee=e_coherence]: since the underlying type is a set, the
    two identifications [e · e = e] given by the unit laws agree, and no
    coherence is needed (informal). *)

(** Exercise [xca:typemonoidisgroupoid]: the types of monoids and of
    abstract groups are groupoids, as [Σ]-types over [Set] of sets. *)
Definition Sigma_isGrpd {A : Type} {B : A -> Type} (gA : isGrpd A)
  (gB : forall a, isGrpd (B a)) : isGrpd {a : A & B a}
  := @IsTrunc_isGrpd _ (@istrunc_sigma _ _ _ (isGrpd_IsTrunc gA)
                               (fun a => isGrpd_IsTrunc (gB a))).

Definition set_isGrpd {A : Type} (sA : isSet A) : isGrpd A := set_ntype 1 sA.

Definition prop_isGrpd {A : Type} (pA : isProp A) : isGrpd A
  := set_isGrpd (prop_is_set pA).

Definition AbsGroup_isGrpd `{Univalence} : isGrpd AbsGroup.
Proof.
  refine (is_ntype_Eqv 1 (Eqv_comp (Eqv_inv (sigma_assoc _ _ _))
                            (Eqv_of_Equiv issig_AbsGroup)) _).
  refine (Sigma_isGrpd SetU_isGrpd _). intros [S sS]. cbn.
  apply set_isGrpd.
  refine (Sigma_isSet sS _). intro e.
  refine (Sigma_isSet (Pi_isSet (fun _ => Pi_isSet (fun _ => sS))) _). intro μ.
  refine (Sigma_isSet (Pi_isSet (fun _ => sS)) _). intro ι.
  apply prop_is_set.
  repeat refine (prod_isProp _ _);
    repeat (apply Pi_isProp; intro); apply sS.
Defined.

Definition Monoid_isGrpd `{Univalence} : isGrpd Monoid.
Proof.
  refine (is_ntype_Eqv 1 (Eqv_comp (Eqv_inv (sigma_assoc _ _ _))
                            (Eqv_of_Equiv issig_Monoid)) _).
  refine (Sigma_isGrpd SetU_isGrpd _). intros [S sS]. cbn.
  apply set_isGrpd.
  refine (Sigma_isSet sS _). intro e.
  refine (Sigma_isSet (Pi_isSet (fun _ => Pi_isSet (fun _ => sS))) _). intro μ.
  apply prop_is_set.
  repeat refine (prod_isProp _ _);
    repeat (apply Pi_isProp; intro); apply sS.
Defined.

(** Exercise [xca:cheapgroup]: sheargroups, with [ā :≡ a * e]. *)
Record Sheargroup : Type := {
  sg_S : Type;
  sg_isSet : isSet sg_S;
  sg_e : sg_S;
  sg_op : sg_S -> sg_S -> sg_S;
  sg_lunit : forall a, sg_op sg_e a = a;
  sg_self : forall a, sg_op a a = sg_e;
  sg_shear : forall a b c, sg_op c (sg_op b a)
                           = sg_op (sg_op (sg_op c (sg_op b sg_e)) sg_e) a
}.

Section Shear.

  Context (K : Sheargroup).

  Local Notation "a * b" := (sg_op K a b).
  Local Notation e := (sg_e K).
  Local Notation "a ‾" := (sg_op K a (sg_e K)) (at level 3, format "a ‾").

  Definition sg_bar_e : e‾ = e := sg_self K e.

  Definition sg_bar_bar (a : sg_S K) : a‾‾ = a.
  Proof.
    pose (r := sg_shear K a a (a‾)).
    rewrite (sg_self K a) in r. rewrite (sg_self K (a‾)) in r.
    refine (r @ _). refine (ap (fun x => x * a) sg_bar_e @ _). exact (sg_lunit K a).
  Defined.

  Definition shear_to_group : AbsGroup.
  Proof.
    refine {| ag_S := sg_S K; ag_isSet := sg_isSet K; ag_e := e;
              ag_mul := fun a b => b‾ * a; ag_inv := fun a => a‾ |}.
    - intro a. refine (ap (fun x => x * a) sg_bar_e @ _). exact (sg_lunit K a).
    - intro a. exact (sg_bar_bar a).
    - intros a b c. cbn. refine (_ @ (sg_shear K a (b‾) (c‾))^).
      exact (ap (fun x => (c‾ * x)‾ * a) (sg_bar_bar b))^.
    - intro a. refine (ap (fun x => x * a) (sg_bar_bar a) @ _). exact (sg_self K a).
  Defined.

End Shear.

Definition group_to_shear (G : AbsGroup) : Sheargroup.
Proof.
  refine {| sg_S := ag_S G; sg_isSet := ag_isSet G; sg_e := ag_e G;
            sg_op := fun a b => b · ag_inv G a |}.
  - intro a. rewrite ag_inv_e. exact (ag_runit G a).
  - intro a. exact (ag_rinv G a).
  - intros a b c. cbn. rewrite ?ag_inv_e, ?ag_lunit.
    rewrite ?ag_inv_mul, ?ag_inv_inv, ?ag_inv_mul, ?ag_inv_inv, ?ag_assoc. exact refl.
Defined.

Definition path_Sheargroup_op `{Funext}
  (S : Type) (sS sS' : isSet S) (e e' : S) (op op' : S -> S -> S)
  lu sf sh lu' sf' sh' (hop : forall a b, op a b = op' a b)
  : {| sg_S := S; sg_isSet := sS; sg_e := e; sg_op := op;
       sg_lunit := lu; sg_self := sf; sg_shear := sh |}
    = {| sg_S := S; sg_isSet := sS'; sg_e := e'; sg_op := op';
         sg_lunit := lu'; sg_self := sf'; sg_shear := sh' |}.
Proof.
  assert (po : op = op') by (apply ptw_inv; intro; apply ptw_inv; intro; apply hop).
  destruct po.
  assert (pe : e = e') by exact ((sf e)^ @ sf' e).
  destruct pe.
  assert (ps : sS = sS') by apply isSet_isProp.
  destruct ps.
  assert (plu : lu = lu') by (apply ptw_inv; intro; apply sS).
  assert (psf : sf = sf') by (apply ptw_inv; intro; apply sS).
  assert (psh : sh = sh')
    by (apply ptw_inv; intro; apply ptw_inv; intro; apply ptw_inv; intro; apply sS).
  destruct plu, psf, psh. exact refl.
Defined.

Definition group_shear_eqv `{Univalence} : AbsGroup ≃ Sheargroup.
Proof.
  refine (mkEqv group_to_shear shear_to_group _ _).
  - intro G. symmetry. refine (@path_AbsGroup _ G (shear_to_group (group_to_shear G)) (idEqv _; _)).
    intros s t. cbn. unfold id.
    rewrite ?ag_lunit, ?ag_inv_inv. exact refl.
  - intros [S sS e op lu sf sh].
    apply path_Sheargroup_op. intros a b.
    exact (ap (fun x => op x b)
              (sg_bar_bar {| sg_S := S; sg_isSet := sS; sg_e := e; sg_op := op;
                             sg_lunit := lu; sg_self := sf; sg_shear := sh |} a)).
Defined.
(** Exercise on Furstenberg groups (statement only): a nonempty set with
    [∘] such that [(a ∘ c) ∘ (b ∘ c) = a ∘ b] and every [a ∘ - ] hits
    every [c]. *)
Definition Furstenberg : Type
  := {S : SetU & {op : fst S -> fst S -> fst S &
       ptrunc (fst S)
       × (forall a b c, op (op a c) (op b c) = op a b)
       × (forall a c, Ex (fun b => op a b = c))}}.

Definition xca_furstenberg_stmt `{Univalence} : Type := Furstenberg ≃ AbsGroup.

