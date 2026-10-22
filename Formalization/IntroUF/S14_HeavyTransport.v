(** * Section 2.14 Heavy transport

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Transport in function-type families, and its univalence special
      case: transport along [etop g] gives [g ∘ f ∘ g⁻¹].
    - Transport in [f x = g x] ([lem:trp-in-fx=Ygx]) and its four special
      cases (the last is conjugation), plus the dependent version stated
      with [po_e(apd …)].
    - [trptw] (pointwise transport).
    - Dan's lemma, formalized literally as written:
      [(f(x) =^Y_p f(x')) ≃ (f(x) = f(x))].  The right-hand side and the
      [e]/[p] mix-up in the statement look like typos in the source. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S13_Univalence.

Local Open Scope uf_scope.

(** ** 2.14 Heavy transport *)

(** Definition [def:function-type-families]. *)
Definition fun_family {X : Type} (Y Z : X -> Type) : X -> Type
  := fun x => Y x -> Z x.

(** Construction [lem:trp-in-function-type]. *)
Definition trp_fun {X : Type} {Y Z : X -> Type} {x x' : X} (e : x = x')
  (f : Y x -> Z x) (y' : Y x')
  : trp (fun_family Y Z) e f y' = trp Z e (f (trp Y e⁻¹ y')).
Proof. destruct e. exact refl. Defined.

(** The special case [Y :≡ Z :≡ id_U] with a path coming from univalence:
    [trp^{X ↦ (X → X)}_{etop g}(f) = g ∘ f ∘ g⁻¹]. *)
Definition trp_trp_inv {A B : Type} (p : A = B) (b : B)
  : ptoe p (trp (fun T : Type => T) p⁻¹ b) = b.
Proof. destruct p. exact refl. Defined.

Definition trp_endo_gen `{Funext} {A B : Type} (p : A = B) (g : A ≃ B)
  (h : ptoe p = fst g) (f : A -> A)
  : trp (fun X : Type => X -> X) p f = comp (fst g) (comp f (eqinv (snd g))).
Proof.
  apply ptw_inv. intro b.
  refine (trp_fun (Y := fun T : Type => T) (Z := fun T : Type => T) p f b @ _).
  unfold comp.
  refine (ptw h _ @ ap (fun a => fst g (f a)) _).
  refine ((eqinv_l (snd g) _)^ @ ap (eqinv (snd g)) _).
  exact ((ptw h _)^ @ trp_trp_inv p b).
Defined.

Definition trp_endo_ua `{UnivalenceUF} `{Funext} {A B : Type} (g : A ≃ B)
  (f : A -> A)
  : trp (fun X : Type => X -> X) (etop g) f
    = comp (fst g) (comp f (eqinv (snd g)))
  := trp_endo_gen (etop g) g (ap fst (ptoe_etop g)) f.

(** Construction [lem:trp-in-fx=Ygx]:
    [trp^Z_e(i) = ap_g(e) · i · ap_f(e)⁻¹], where [Z(x) :≡ (f(x) = g(x))]. *)
Definition trp_paths_fg {X Y : Type} (f g : X -> Y) {x x' : X} (e : x = x')
  (i : f x = g x)
  : trp (fun x => f x = g x) e i = (ap g e ⋅ i) ⋅ (ap f e)⁻¹.
Proof. destruct e. exact (trans_1p i)^. Defined.

(** Exercise [xca:trp-in-a/x=b/x]. *)
Section TrpInPaths.

  Context {X : Type} (a b : X) {x x' : X} (e : x = x').

  Definition trp_paths_const (i : a = b) : trp (fun _ => a = b) e i = i.
  Proof. destruct e. exact refl. Defined.

  (** Part [trp-in-a=x]. *)
  Definition trp_paths_l (i : a = x) : trp (fun x => a = x) e i = e ⋅ i.
  Proof. destruct e. exact refl. Defined.

  (** Part [trp-in-x=a]. *)
  Definition trp_paths_r (i : x = b) : trp (fun x => x = b) e i = i ⋅ e⁻¹.
  Proof. destruct e. exact (trans_1p i)^. Defined.

  (** Part [trp-in-x=x], conjugation; see also [trp_symmetry_conj] in 2.5. *)
  Definition trp_paths_conj (i : x = x)
    : trp (fun x => x = x) e i = (e ⋅ i) ⋅ e⁻¹.
  Proof. destruct e. exact (trans_1p i)^. Defined.

End TrpInPaths.

(** Converting a path over [p] into a path using transport, via [po_p]. *)
Definition po_to_trp {X : Type} {Y : X -> Type} {x x' : X} {p : x = x'}
  {y : Y x} {y' : Y x'} (q : PathOver Y p y y') : trp Y p y = y'
  := trp (fun T : Type => T) (po p y y') q.

(** Construction [lem:trp-in-fx=Yxgx]: the dependent version. *)
Definition trp_paths_dep {X : Type} {Y : X -> Type} (f g : forall x, Y x)
  {x x' : X} (e : x = x') (i : f x = g x)
  : trp (fun x => f x = g x) e i
    = (po_to_trp (apd g e) ⋅ ap (trp Y e) i) ⋅ (po_to_trp (apd f e))⁻¹.
Proof.
  destruct e. cbn.
  exact ((ap_id i)^ @ (trans_1p (ap (id (Y x)) i))^).
Defined.

(** Definition [def:Dan's-lemma], stated literally as in the text:
    [(f(x) =^Y_p f(x')) ≃ (f(x) = f(x))], by induction on [p]. *)
Definition dans_lemma {X : Type} {Y : X -> Type} (f : forall x, Y x)
  {x x' : X} (p : x = x')
  : PathOver Y p (f x) (f x') ≃ (f x = f x).
Proof. destruct p. exact (idEqv _). Defined.

(** Exercise [xca:trp-in-y=_(x)]: pointwise transport. *)
Definition trptw {X Y : Type} {x : X} {y : Y} {f g : X -> Y} (e : f = g)
  (p : y = f x)
  : trp (fun h : X -> Y => y = h x) e p = ptw e x ⋅ p.
Proof. destruct e. exact refl. Defined.
