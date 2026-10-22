(** * Section 2.6 Product types

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - [ap]; all three parts of [lem:apcomp]; exercise [xca:trp-ap].
    - [ptw := apD10] (the book's [happly], for dependent functions), and
      its identification with the footnote's [ap (ev x)].
    - The funext remark, via the library's [path_forall]; this is the
      only use of Coq-HoTT's [Funext] in 2.2 - 2.6.
    - The naturality square [ns(h,p)].
    - Bridge: [ptw] is [apD10]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S05_IdentityTypes.

Local Open Scope uf_scope.

(** ** 2.6 Product types

    If [X : U] and [Y : X -> U] then [forall x, Y x : U]. *)

Definition pi_in_U@{u} (X : Type@{u}) (Y : X -> Type@{u}) : Type@{u}
  := forall x : X, Y x.

(** Definition [def:ap]: [ap_{f,x,x}(refl x) :≡ refl_{f(x)}].  This is
    the library's [ap], which has the same name. *)
Definition ap_refl {X Y : Type} (f : X -> Y) (x : X)
  : ap f (refl x) = refl (f x) := refl.

(** Construction [lem:apcomp]. *)
Section ApComp.

  Context {X Y : Type} (f : X -> Y) {x x' x'' : X}.

  Definition ap_trans (p : x = x') (p' : x' = x'')
    : ap f (p' ⋅ p) = ap f p' ⋅ ap f p.
  Proof. destruct p', p. exact refl. Defined.

  Definition ap_symm (p : x = x') : ap f (p⁻¹) = (ap f p)⁻¹
    := match p with refl => refl end.

  Definition ap_id (p : x = x') : ap (id X) p = p
    := match p with refl => refl end.

End ApComp.

(** Exercise [xca:trp-ap]: [trp^{T ∘ f}_p = trp^T_{ap_f(p)}], both of type
    [T(f(a)) -> T(f(a'))]. *)
Definition trp_ap {X A : Type} (T : X -> Type) (f : A -> X)
  {a a' : A} (p : a = a')
  : trp (T ∘ f) p = trp T (ap f p)
  := match p with refl => refl end.

(** Definition [def:ptw]: from an identification of (dependent) functions
    to pointwise identifications, [ptw_{f,f}(refl f) :≡ x ↦ refl_{f(x)}].
    This is the library's [apD10] (Book HoTT's [happly]). *)
Definition ptw {X : Type} {Y : X -> Type} {f g : forall x, Y x}
  (p : f = g) : forall x : X, f x = g x
  := apD10 p.

Definition ptw_refl {X : Type} {Y : X -> Type} (f : forall x, Y x)
  : ptw (refl f) = (fun x => refl (f x)) := refl.

(** Footnote to [def:ptw]: the alternative via evaluation
    [ev_x(f) :≡ f(x)].  Not equal by definition, but identified. *)
Definition ev {X : Type} {Y : X -> Type} (x : X) : (forall x, Y x) -> Y x
  := fun f => f x.

Definition ptw_ev {X : Type} {Y : X -> Type} {f g : forall x, Y x}
  (p : f = g) (x : X) : ptw p x = ap (ev x) p
  := match p with refl => refl end.

(** Function extensionality ([def:funext], postulated later in the book)
    provides the converse; in Coq-HoTT it is the class [Funext], with
    [path_forall : (forall x, f x = g x) -> f = g]. *)
Definition funext_converse `{Funext} {X : Type} {Y : X -> Type}
  {f g : forall x, Y x} : (forall x, f x = g x) -> f = g
  := path_forall f g.

(** Definition [def:naturality-square]: for [h : ∏_x f(x) = g(x)] and
    [p : x = x'], an identification
    [ns(h,p) : h(x') · ap_f(p) = ap_g(p) · h(x)].
    For [p :≡ refl_x] the goal is [h(x) · refl_{f(x)} = h(x)], which is
    constructed by induction on [h(x)] (exercise part 2). *)
Definition ns {X Y : Type} {f g : X -> Y} (h : forall x, f x = g x)
  {x x' : X} (p : x = x')
  : h x' ⋅ ap f p = ap g p ⋅ h x
  := match p with refl => trans_1p (h x) end.

(** *** Bridges to Coq-HoTT *)

Definition ptw_is_apD10 {X : Type} {Y : X -> Type} {f g : forall x, Y x}
  (p : f = g) : ptw p = apD10 p := refl.
