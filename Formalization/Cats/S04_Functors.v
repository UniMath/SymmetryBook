(** * Section 6.4 Functors and natural transformations

    Part of Chapter 6 ([cats.tex]); see [Cats.v] for an overview of the
    chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:functor]: the record [Functor] ([fob], [fmap],
      [fid], [fcomp]); into a precategory a functor is determined by its
      actions on objects and arrows ([path_Functor]).
    - Exercise [xca:wild-functor-isos] ([fmap_isIso]).
    - Examples: [ex:functor-preorders] ([Functor_preorder_eqv]),
      [ex:USym-functor] ([USymFun]), [ex:action-functors] (restriction
      [RestrictFun], induction [InduceFun] and coinduction [CoinduceFun]),
      [def:n-trunc-functor] ([TruncFun]), [ex:add-remove-basepoint]
      ([PlusFun], [ForgetFun]), [ex:loop-functor] ([LoopFun], with
      [loops_map_pid] and [loops_map_pcomp]), [ex:slice-projection]
      ([SliceProj]) and [ex:arrow-cat] ([ArrowCat], a precategory, with
      [DomFun] and [CodFun]).
    - Exercise [xca:wildprecat-of-wildprecats]: [idF], [compF], and [λ],
      [ρ], [α] for functors into precategories ([compF_idF_l],
      [compF_idF_r], [compF_assoc]); hence the wild precategory of
      precategories [PreCatCat].
    - Definition [def:full-faithful] ([isFaithful], [isFull],
      [isFullyFaithful]).
    - Definition [def:nat-trans] ([NatTrans]); examples [ex:pt-unpt-unit]
      ([PlusUnit]) and [ex:path-gpd-nat] ([PathFun], [PathNat]).
    - Definition [def:functor-cat] ([FunctorCat], a precategory) and
      exercise [xca:funext-nat-trans] ([natiso_components],
      [components_natiso]); exercise [xca:path-core-adj]
      ([xca_path_core_adj], with inverse [path_functor]:
      [p ↦ idtoiso(ap f p)]).
    - Example [ex:repr-functors] ([RepCo], [RepContra]).

    Left out (statements only, no proofs yet)
    - That [C^→] is a category if [C] is ([ArrowCat_isUnivalent_stmt]).
    - Exercise [xca:wildprecat-of-wildprecats] for wild functors into
      wild precategories ([wild_functor_laws_stmt]); the pentagon fillers
      are left out.
    - Exercises [xca:wildcat-of-precats] ([xca_wildcat_of_precats_stmt],
      for precategories) and [xca:functor-cat-univalent]
      ([FunctorCat_isUnivalent_stmt]).

    Left out (not formalized)
    - The hidden example after [def:full-faithful] (a work-in-progress
      item in the book). *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Types.Unit Truncations.Core Spaces.Nat.Core.
From SymmetryBook Require Export Cats.S03_Duality.

Local Open Scope uf_scope.

(** ** 6.4 Functors and natural transformations *)

(** Definition [def:functor]: a wild functor, with [F_id] and [F_∘]. *)
Record Functor (C D : WildPreCat) : Type := {
  fob : Ob C -> Ob D;
  fmap : forall A B, homC A B -> homC (fob A) (fob B);
  fid : forall A, fmap A A (idC A) = idC (fob A);
  fcomp : forall A B E (f : homC A B) (g : homC B E),
      fmap A E (g ∘c f) = fmap B E g ∘c fmap A B f
}.

Arguments fob {C D} _ _.
Arguments fmap {C D} _ {A B} _.
Arguments fid {C D} _ _.
Arguments fcomp {C D} _ {A B E} _ _.

(** A wild functor into a precategory is determined by its actions on
    objects and arrows. *)
Definition path_Functor `{Funext} {C D : WildPreCat} (pd : isPreCat D) (F G : Functor C D)
  (p : fob F = fob G)
  (q : trp (fun (ob : Ob C -> Ob D) => forall A B, homC A B -> homC (ob A) (ob B)) p (@fmap C D F)
       = @fmap C D G)
  : F = G.
Proof.
  destruct F as [ob m i c], G as [ob' m' i' c']. cbn in p, q. destruct p, q.
  assert (ei : i = i') by (apply ptw_inv; intro; apply pd).
  assert (ec : c = c').
  { apply ptw_inv; intro; apply ptw_inv; intro; apply ptw_inv; intro;
      apply ptw_inv; intro; apply ptw_inv; intro; apply pd. }
  destruct ei, ec. exact refl.
Defined.

(** Exercise [xca:wild-functor-isos]: wild functors preserve
    isomorphisms. *)
Definition fmap_isIso {C D : WildPreCat} (F : Functor C D) {A B : Ob C} {f : homC A B}
  (i : isIsoC f) : isIsoC (fmap F f).
Proof.
  destruct i as [[g s] [h r]].
  refine ((fmap F g; _); (fmap F h; _)).
  - exact ((fcomp F g f)^ @ ap (fmap F) s @ fid F B).
  - exact ((fcomp F f h)^ @ ap (fmap F) r @ fid F A).
Defined.

(** Example [ex:functor-preorders]: a functor between preorders amounts
    to a monotone map. *)
Definition Monotone (P Q : WildPreCat) : Type
  := {F : Ob P -> Ob Q & forall p p', homC p p' -> homC (F p) (F p')}.

Definition Functor_preorder_eqv `{Funext} (P Q : WildPreCat) (hQ : isPreorder Q)
  : Functor P Q ≃ Monotone P Q.
Proof.
  refine (mkEqv (fun F => (fob F; fun p p' => @fmap P Q F p p'))
                (fun m : Monotone P Q => {| fob := fst m; fmap := snd m;
                             fid := fun A => hQ _ _ _ _;
                             fcomp := fun A B E f g => hQ _ _ _ _ |}) _ _).
  - intro F. match goal with |- ?L = ?R =>
      exact (path_Functor (preorder_isPreCat Q hQ) L R refl refl) end.
  - intros [F m]. exact refl.
Defined.

(** Example [ex:USym-functor]: [USym : Group → Set]. *)
Definition USymf_idG `{Funext} (G : Group) : USymf (idG G) = id (USym G)
  := ptw_inv (fun p => trans_1p _ @ ap_idmap p).

Definition USymFun `{Funext} : Functor GroupCat SetCat
  := {| fob := fun G : Ob GroupCat => ((USym G; USym_isSet G) : Ob SetCat);
        fmap := fun (G H : Ob GroupCat) (f : Hom G H) => USymf f;
        fid := USymf_idG;
        fcomp := fun G H K f g => USym_compose f g |}.

(** Example [ex:action-functors]: restriction [f^*] and coinduction
    [f_*] along a homomorphism, with their actions on arrows. *)
Section ActionFunctors.

  Context `{Funext} {G K : Group} (f : Hom G K).

  Definition RestrictFun : Functor (GSetCat K) (GSetCat G)
    := Build_Functor (GSetCat K) (GSetCat G)
       (restrict f)
       (fun X Y g z => g (fst (Bf f) z))
       (fun X => refl)
       (fun X Y Z g h => refl).

  Definition CoinduceFun : Functor (GSetCat G) (GSetCat K)
    := Build_Functor (GSetCat G) (GSetCat K)
       (coinduce f)
       (fun X Y g w u z p => g z (u z p))
       (fun X => refl)
       (fun X Y Z g h => refl).

  (** Induction [f_!], acting on arrows by the functoriality of set
      truncation. *)
  Definition induce_map {X Y : GSet G} (g : HomGs X Y) : HomGs (induce f X) (induce f Y)
    := fun w => strunc_rec strunc_isSet
                  (fun t => settrunc ((fst t; (fst (snd t); g (fst t) (snd (snd t))))
                                      : induce_type f Y w)).

  Definition InduceFun : Functor (GSetCat G) (GSetCat K).
  Proof.
    refine (Build_Functor (GSetCat G) (GSetCat K) (induce f) (fun X Y g => induce_map g) _ _).
    - intro X. apply ptw_inv. intro w. apply ptw_inv.
      refine (strunc_ind_prop _ (fun _ => strunc_isSet _ _) _). intros [z [p x]]. exact refl.
    - intros X Y Z g h. apply ptw_inv. intro w. apply ptw_inv.
      refine (strunc_ind_prop _ (fun _ => strunc_isSet _ _) _). intros [z [p x]]. exact refl.
  Defined.

End ActionFunctors.

(** The identity functor and composition of functors. *)
Definition idF (C : WildPreCat) : Functor C C
  := Build_Functor C C
       (fun A => A)
       (fun A B f => f)
       (fun A => refl)
       (fun A B E f g => refl).

Definition compF {C D E : WildPreCat} (G : Functor D E) (F : Functor C D) : Functor C E
  := Build_Functor C E
       (fun A => fob G (fob F A))
       (fun A B f => fmap G (fmap F f))
       (fun A => ap (fmap G) (fid F A) @ fid G (fob F A))
       (fun A B E' f g => ap (fmap G) (fcomp F f g) @ fcomp G (fmap F f) (fmap F g)).

(** Example [def:n-trunc-functor]: [‖-‖_n : U → U^{≤n}], into the full
    subcategory on the [n]-types. *)
Definition isTruncU `{Funext} (n : trunc_index) (A : Ob TypeCat) : PropU
  := (IsTrunc n A; IsHProp_isProp).

Definition TruncFun `{Funext} (n : trunc_index) : Functor TypeCat (FullSub TypeCat (isTruncU n)).
Proof.
  refine (Build_Functor TypeCat (FullSub TypeCat (isTruncU n))
            (fun A => ((Trunc n A; istrunc_truncation n A) : Ob (FullSub TypeCat (isTruncU n))))
            (fun A B f => Trunc_functor n f) _ _).
  - intro A. apply ptw_inv. refine (Trunc_ind _ _). intro a. exact refl.
  - intros A B E f g. apply ptw_inv. refine (Trunc_ind _ _). intro a. exact refl.
Defined.

(** Example [ex:add-remove-basepoint]: [(-)_+ : U → U_*] and
    [(-)_÷ : U_* → U]. *)
Definition plusPtd (A : Type) : Ustar := (A ⨿ True; inr triv).

Definition plus_fun {A B : Type} (f : A -> B) (x : A ⨿ True) : B ⨿ True
  := match x with inl a => inl (f a) | inr t => inr t end.

Definition path_pmap_refl `{Funext} {X Y : Ustar} (f g : utype X -> utype Y)
  (fp : pt Y = f (pt X)) (gp : pt Y = g (pt X))
  (h : forall x, f x = g x) (e : h (pt X) ⋅ fp = gp) : ((f; fp) : X →* Y) = (g; gp)
  := eqinv (snd (ptw_star (f; fp) (g; gp))) (h; e).

Definition PlusFun `{Funext} : Functor TypeCat PtdCat.
Proof.
  refine (Build_Functor TypeCat PtdCat plusPtd
            (fun A B f => ((plus_fun f; refl) : plusPtd A →* plusPtd B)) _ _).
  - intro A. refine (path_pmap_refl (X := plusPtd A) (Y := plusPtd A) (plus_fun (fun a : A => a)) idmap refl refl
                       (fun x : A ⨿ True => match x with inl a => refl | inr t => match t with triv => refl end end) _).
    exact refl.
  - intros A B E f g. refine (path_pmap_refl (X := plusPtd A) (Y := plusPtd E)
                       (plus_fun (g ∘ f)) (plus_fun g ∘ plus_fun f) refl _
                       (fun x : A ⨿ True => match x with inl a => refl | inr t => match t with triv => refl end end) _).
    exact refl.
Defined.

Definition ForgetFun `{Funext} : Functor PtdCat TypeCat
  := Build_Functor PtdCat TypeCat
       (utype)
       (fun X Y f => fst f)
       (fun X => refl)
       (fun X Y Z f g => refl).

(** Example [ex:loop-functor]: [Ω : U_* → U_*], with the pointing path
    of [Ωk] from [loops_map] (Section 4.4). *)
Definition loops_map_pid `{Funext} (X : Ustar) : loops_map (pid X) = pid (loops X)
  := path_pmap_refl (X := loops X) (Y := loops X) (loops_fun (pid X)) idmap
       (snd (loops_map (pid X))) refl (fun p : pt X = pt X => trans_1p _ @ ap_idmap p) refl.

Definition loops_map_pcomp `{Funext} {X Y Z : Ustar} (g : Y →* Z) (f : X →* Y)
  : loops_map (pcomp g f) = pcomp (loops_map g) (loops_map f).
Proof.
  destruct X as [A x], Y as [B y], Z as [C z], f as [f0 fp], g as [g0 gp].
  cbn in *. revert z gp. refine (paths_ind_r _ _ _).
  revert y fp g0. refine (paths_ind_r _ _ _). intro g0.
  exact (path_pmap_refl _ _ (snd (loops_map (pcomp ((g0; refl) : (B; f0 x) →* (C; g0 (f0 x)))
                                                   ((f0; refl) : (A; x) →* (B; f0 x)))))
           (snd (pcomp (loops_map ((g0; refl) : (B; f0 x) →* (C; g0 (f0 x))))
                       (loops_map ((f0; refl) : (A; x) →* (B; f0 x)))))
           (loops_fun_pcomp ((g0; refl) : (B; f0 x) →* (C; g0 (f0 x)))
                            ((f0; refl) : (A; x) →* (B; f0 x))) refl).
Defined.

Definition LoopFun `{Funext} : Functor PtdCat PtdCat
  := Build_Functor PtdCat PtdCat
       (loops)
       (fun X Y k => loops_map k)
       (loops_map_pid)
       (fun X Y Z f g => loops_map_pcomp g f).

(** Example [ex:slice-projection]. *)
Definition SliceProj `{Funext} (C : WildPreCat) (pc : isPreCat C) (C0 : Ob C)
  : Functor (SliceCat C pc C0) C
  := Build_Functor (SliceCat C pc C0) C
       (fun A => fst A)
       (fun A B g => fst g)
       (fun A => refl)
       (fun A B E f g => refl).

(** Example [ex:arrow-cat]: the arrow precategory, with [dom] and
    [cod]. *)
Section ArrowCat.

  Context `{Funext} (C : WildPreCat) (pc : isPreCat C).

  Definition ArrOb : Type := {A : Ob C & {B : Ob C & homC A B}}.

  Definition ArrHom (X Y : ArrOb) : Type
    := {g : homC (fst X) (fst Y) & {h : homC (fst (snd X)) (fst (snd Y)) &
         snd (snd Y) ∘c g = h ∘c snd (snd X)}}.

  Definition path_ArrHom {X Y : ArrOb} (u v : ArrHom X Y)
    (p : fst u = fst v) (q : fst (snd u) = fst (snd v)) : u = v.
  Proof.
    destruct u as [g [h e]], v as [g' [h' e']]. cbn in p, q. destruct p, q.
    exact (ap (fun e0 => (g; (h; e0)) : ArrHom X Y) (pc _ _ _ _ e e')).
  Defined.

  Definition arr_id (X : ArrOb) : ArrHom X X
    := (idC (fst X); (idC (fst (snd X)); rhoC _ @ (lamC _)^)).

  Definition arr_comp {X Y Z : ArrOb} (v : ArrHom Y Z) (u : ArrHom X Y) : ArrHom X Z.
  Proof.
    refine (fst v ∘c fst u; (fst (snd v) ∘c fst (snd u); _)).
    refine (alphaC _ _ _ @ ap (fun k => k ∘c fst u) (snd (snd v)) @ _).
    refine ((alphaC _ _ _)^ @ ap (fun k => fst (snd v) ∘c k) (snd (snd u)) @ alphaC _ _ _).
  Defined.

  Definition ArrowCat : WildPreCat
    := {| Ob := ArrOb;
          homC := ArrHom;
          idC := arr_id;
          compC := @arr_comp;
          lamC := fun X Y u => path_ArrHom (arr_comp (arr_id Y) u) u (lamC _) (lamC _);
          rhoC := fun X Y u => path_ArrHom (arr_comp u (arr_id X)) u (rhoC _) (rhoC _);
          alphaC := fun X Y Z W u v w =>
                      path_ArrHom (arr_comp w (arr_comp v u)) (arr_comp (arr_comp w v) u)
                        (alphaC _ _ _) (alphaC _ _ _) |}.

  Definition ArrowCat_isPreCat : isPreCat ArrowCat
    := fun X Y => Sigma_isSet (pc _ _) (fun _ => Sigma_isSet (pc _ _)
                                          (fun _ => prop_is_set (pc _ _ _ _))).

  Definition DomFun : Functor ArrowCat C
    := Build_Functor ArrowCat C (fun X => fst X) (fun X Y u => fst u)
         (fun X => refl) (fun X Y Z u v => refl).

  Definition CodFun : Functor ArrowCat C
    := Build_Functor ArrowCat C (fun X => fst (snd X)) (fun X Y u => fst (snd u))
         (fun X => refl) (fun X Y Z u v => refl).

  (** If [C] is a category, then so is [C^→] (statement only). *)
  Definition ArrowCat_isUnivalent_stmt : Type := isUnivalent C -> isUnivalent ArrowCat.

End ArrowCat.

(** Exercise [xca:wildprecat-of-wildprecats]: identity and composition
    of wild functors with [λ], [ρ] and [α], into a precategory (where the
    laws for [F_id] and [F_∘] hold automatically). *)
Definition compF_idF_l `{Funext} {C D : WildPreCat} (pd : isPreCat D) (F : Functor C D)
  : compF (idF D) F = F
  := path_Functor pd (compF (idF D) F) F refl refl.

Definition compF_idF_r `{Funext} {C D : WildPreCat} (pd : isPreCat D) (F : Functor C D)
  : compF F (idF C) = F
  := path_Functor pd (compF F (idF C)) F refl refl.

Definition compF_assoc `{Funext} {C D E W : WildPreCat} (pw : isPreCat W)
  (F : Functor C D) (G : Functor D E) (K : Functor E W)
  : compF K (compF G F) = compF (compF K G) F
  := path_Functor pw (compF K (compF G F)) (compF (compF K G) F) refl refl.

(** For wild functors in general, [λ], [ρ], [α] and the pentagon
    fillers (statements only). *)
Definition wild_functor_laws_stmt : Type
  := forall (C D E W : WildPreCat) (F : Functor C D) (G : Functor D E) (K : Functor E W),
       (compF (idF D) F = F) × (compF F (idF C) = F) × (compF K (compF G F) = compF (compF K G) F).

(** Exercise [xca:wildcat-of-precats] (statement only): the precategories,
    with functors as arrows, form a univalent wild category; likewise the
    categories. *)
Definition PreCatCat `{Funext} : WildPreCat
  := {| Ob := PreCat;
        homC := fun C D => Functor (fst C) (fst D);
        idC := fun C => idF (fst C);
        compC := fun C D E G F => compF G F;
        lamC := fun C D F => compF_idF_l (snd D) F;
        rhoC := fun C D F => compF_idF_r (snd D) F;
        alphaC := fun C D E W F G K => compF_assoc (snd W) F G K |}.

Definition xca_wildcat_of_precats_stmt `{Funext} : Type := isUnivalent PreCatCat.

(** Definition [def:full-faithful]. *)
Definition isFaithful {C D : WildPreCat} (F : Functor C D) : Type
  := forall A B : Ob C, isInj (@fmap C D F A B).

Definition isFull {C D : WildPreCat} (F : Functor C D) : Type
  := forall A B : Ob C, isSurj (@fmap C D F A B).

Definition isFullyFaithful {C D : WildPreCat} (F : Functor C D) : Type
  := forall A B : Ob C, isEquiv (@fmap C D F A B).

Definition full_faithful_isFullyFaithful `{Funext} {C D : WildPreCat} (F : Functor C D)
  (fa : isFaithful F) (fu : isFull F) : isFullyFaithful F
  := fun A B => inj_surj_isEquiv (fa A B) (fu A B).

(** Definition [def:nat-trans]. *)
Definition NatTrans {C D : WildPreCat} (F G : Functor C D) : Type
  := {a : forall A, homC (fob F A) (fob G A) &
      forall A B (f : homC A B), fmap G f ∘c a A = a B ∘c fmap F f}.

Definition NatTrans_isSet `{Funext} {C D : WildPreCat} (pd : isPreCat D) (F G : Functor C D)
  : isSet (NatTrans F G)
  := Sigma_isSet (Pi_isSet (fun A => pd _ _))
       (fun a => prop_is_set (Pi_isProp (fun A => Pi_isProp (fun B => Pi_isProp (fun f => pd _ _ _ _))))).

Definition path_NatTrans `{Funext} {C D : WildPreCat} (pd : isPreCat D) {F G : Functor C D}
  (a b : NatTrans F G) (p : forall A, fst a A = fst b A) : a = b
  := path_sigma_prop (fun a => Pi_isProp (fun A => Pi_isProp (fun B => Pi_isProp (fun f => pd _ _ _ _))))
       (u := a) (v := b) (ptw_inv p).

(** Example [ex:pt-unpt-unit]: [η : id_U → ((-)_+)_÷], with component
    [inl], natural by [refl]. *)
Definition PlusUnit `{Funext} : NatTrans (idF TypeCat) (compF ForgetFun PlusFun)
  := ((fun A => @inl A True); fun A B f => refl).

(** Example [ex:path-gpd-nat]: a function gives a wild functor between
    path groupoids, and a homotopy a natural transformation (by the
    naturality squares [ns]). *)
Definition PathFun {A B : Type} (f : A -> B) : Functor (PathGrpd A) (PathGrpd B)
  := Build_Functor (PathGrpd A) (PathGrpd B) f (fun x y p => ap f p) (fun x => refl)
       (fun x y z p q => ap_trans f p q).

Definition PathNat {A B : Type} {f g : A -> B} (h : forall x, f x = g x)
  : NatTrans (PathFun f) (PathFun g)
  := (h; fun x y p => (ns h p)^).

(** Definition [def:functor-cat]: the functor precategory [C → D] for a
    precategory [D]. *)
Section FunctorCat.

  Context `{Funext} (C D : WildPreCat) (pd : isPreCat D).

  Definition nat_id (F : Functor C D) : NatTrans F F
    := ((fun A => idC (fob F A)); fun A B f => rhoC _ @ (lamC _)^).

  Definition nat_comp {F G K : Functor C D} (b : NatTrans G K) (a : NatTrans F G) : NatTrans F K.
  Proof.
    refine ((fun A => fst b A ∘c fst a A); fun A B f => _).
    refine (alphaC _ _ _ @ ap (fun k => k ∘c fst a A) (snd b A B f) @ _).
    exact ((alphaC _ _ _)^ @ ap (fun k => fst b B ∘c k) (snd a A B f) @ alphaC _ _ _).
  Defined.

  Definition FunctorCat : WildPreCat
    := {| Ob := Functor C D;
          homC := NatTrans;
          idC := nat_id;
          compC := @nat_comp;
          lamC := fun F G a => path_NatTrans pd (nat_comp (nat_id G) a) a (fun A => lamC _);
          rhoC := fun F G a => path_NatTrans pd (nat_comp a (nat_id F)) a (fun A => rhoC _);
          alphaC := fun F G K L a b c =>
                      path_NatTrans pd (nat_comp c (nat_comp b a)) (nat_comp (nat_comp c b) a)
                        (fun A => alphaC _ _ _) |}.

  Definition FunctorCat_isPreCat : isPreCat FunctorCat := fun F G => NatTrans_isSet pd F G.

  (** Exercise [xca:funext-nat-trans]: a natural transformation is an
      isomorphism iff each component is. *)
  Definition natiso_components {F G : Functor C D} (a : NatTrans F G)
    (i : isIsoC (C := FunctorCat) a) : forall A, isIsoC (fst a A)
    := fun A => ((fst (fst (fst i)) A; ap (fun u : NatTrans G G => fst u A) (snd (fst i)));
                 (fst (fst (snd i)) A; ap (fun u : NatTrans F F => fst u A) (snd (snd i)))).

  Definition components_natiso {F G : Functor C D} (a : NatTrans F G)
    (i : forall A, isIsoC (fst a A)) : isIsoC (C := FunctorCat) a.
  Proof.
    pose (g := fun A => fst (fst (i A))).
    assert (gn : forall A B (f : homC A B), fmap F f ∘c g A = g B ∘c fmap G f).
    { intros A B f.
      pose (gl := fun X => isIsoC_inv_eq (i X)).
      refine ((lamC _)^ @ ap (fun k => k ∘c (fmap F f ∘c g A)) (snd (snd (i B)))^ @ _).
      refine (ap (fun k => (k ∘c fst a B) ∘c (fmap F f ∘c g A)) (gl B) @ _).
      refine ((alphaC _ _ _)^ @ ap (fun k => g B ∘c k) (alphaC _ _ _) @ _).
      refine (ap (fun k => g B ∘c (k ∘c g A)) (snd a A B f)^ @ _).
      refine (ap (fun k => g B ∘c k) (alphaC _ _ _)^ @ _).
      refine (ap (fun k => g B ∘c (fmap G f ∘c k)) (snd (fst (i A))) @ _).
      exact (ap (fun k => g B ∘c k) (rhoC _)). }
    refine (((g; gn); _); ((g; gn); _)).
    - apply path_NatTrans; [exact pd|]. intro A. exact (snd (fst (i A))).
    - apply path_NatTrans; [exact pd|]. intro A.
      exact (ap (fun k => k ∘c fst a A) (isIsoC_inv_eq (i A))^ @ snd (snd (i A))).
  Defined.

  (** Exercise [xca:functor-cat-univalent] (statement only). *)
  Definition FunctorCat_isUnivalent_stmt : Type := isUnivalent D -> isUnivalent FunctorCat.

End FunctorCat.

(** Exercise [xca:path-core-adj]: for a type [A] and a
    category [C], restricting to objects is an equivalence
    [[A, C] ≃ (A → Ob(C))]. *)
Definition xca_path_core_adj_stmt `{Funext} : Type
  := forall (A : Type) (C : Cat),
       isEquiv (fun F : Functor (PathGrpd A) (fst C) => fob F).

(** The inverse sends [f : A → Ob(C)] to the functor [p ↦ idtoiso(ap f p)]. *)
Definition path_functor {A : Type} {C : WildPreCat} (f : A -> Ob C) : Functor (PathGrpd A) C.
Proof.
  refine (Build_Functor (PathGrpd A) C f (fun a b p => fst (idtoiso (ap f p))) (fun a => refl) _).
  intros a b e p q. destruct q, p. exact (lamC _)^.
Defined.

Definition xca_path_core_adj `{Funext} : xca_path_core_adj_stmt.
Proof.
  intros A C. refine (iso_to_isEquiv _ path_functor _ (fun f => refl)).
  intro F. refine (path_Functor (fst (snd C)) (path_functor (fob F)) F refl _). cbn.
  apply path_forall. intro a. apply path_forall. intro b. apply path_forall. intro p.
  destruct p. exact (fid F a)^.
Defined.

(** Example [ex:repr-functors]: the representable wild functors
    [Hom(C₀, -) : C → U] and [Hom(-, C₀) : C^op → U]. *)
Definition RepCo `{Funext} (C : WildPreCat) (C0 : Ob C) : Functor C TypeCat
  := Build_Functor C TypeCat (fun A => homC C0 A) (fun A B f k => f ∘c k)
       (fun A => ptw_inv (fun k => lamC k)) (fun A B E f g => ptw_inv (fun k => (alphaC k f g)^)).

Definition RepContra `{Funext} (C : WildPreCat) (C0 : Ob C) : Functor (Op C) TypeCat
  := Build_Functor (Op C) TypeCat (fun A : Ob C => homC (w := C) A C0)
       (fun A B (f : homC (w := C) B A) (k : homC (w := C) A C0) => @compC C B A C0 k f)
       (fun A => ptw_inv (fun k : homC (w := C) A C0 => rhoC k))
       (fun A B E (f : homC (w := C) B A) (g : homC (w := C) E B) =>
          ptw_inv (fun k : homC (w := C) A C0 => alphaC g f k)).
