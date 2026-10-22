(** * Section 2.12 More inductive types

    Part of Chapter 2 ([intro-uf.tex]); see [IntroUF.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - [False] and [True] with their universal properties
      ([xca:True-univ-prop]); [yes ≠ no] and [0 ≠ succ n].
    - Binary sums: [xca:binary-sum-equiv], [xca:bin-sum-univ-prop], and
      [xca:binary-sum-id], by the encode-decode method rather than the
      route the book suggests.
    - Unary sums [Copy] and the negated naturals [NNN] ([exa:nnn]); the
      constructor [-] is called [negN], since [neg] is negation (2.15).
    - Lists [X^*] ([def:lists]) with [list_ind], [len := length] and
      concatenation [app]; [hd], [tl] with values in [X ⨿ True] (the
      library's [head] uses [option]); [rev] from concatenation (the
      library's [reverse] uses an accumulator); exercises
      [xca:list-contr], [xca:concat-assoc] and [xca:reverse]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core.
From SymmetryBook Require Export IntroUF.S11_BinaryProducts.

Local Open Scope uf_scope.

(** ** 2.12 More inductive types *)

(** *** Finite types: [False] ([𝟘]), [True] ([𝟙] with [triv :≡ triv]) and
    [Bool] ([𝟚]), all in [Type0]. *)

Check (False : Type0).
Check (True : Type0).
Check (Bool : Type0).

Definition False_paths (x y : False) : x = y := match x with end.

Definition False_absurd_nat : False -> (0%nat = 1%nat :> ℕ)
  := fun x => match x with end.

Definition True_center (u : True) : u = triv
  := match u with triv => refl end.

Definition True_paths (x y : True) : x = y
  := match x, y with triv, triv => refl end.

Definition to_Unit (X : Type) : X -> True := fun _ => triv.

(** Exercise [xca:True-univ-prop]. *)
Definition True_univ_prop `{Funext} (X : Type)
  : isEquiv (fun f : True -> X => f triv)
  := snd (True_to_X_eqv X).

(** [(yes = no) -> 𝟘], by substitution in [P(yes) :≡ 𝟙], [P(no) :≡ 𝟘]. *)
Definition yes_ne_no : (yes = no) -> False
  := fun e => trp (fun b : Bool => if b then True else False) e triv.

(** [(0 = S(n)) -> 𝟘], by substitution in [P(0) :≡ 𝟙], [P(S(m)) :≡ 𝟘]. *)
Definition zero_ne_succ (n : ℕ) : (0%nat = succ n) -> False
  := fun e => trp (fun i : ℕ => match i with O => True | S _ => False end)
                e triv.

(** *** Binary sums: [X ⨿ Y] is Coq-HoTT's [X + Y]. *)

Notation "X ⨿ Y" := (sum X Y) (at level 50, left associativity) : uf_scope.

(** Exercise [xca:binary-sum-equiv]. *)
Definition binary_sum_equiv (X Y : Type)
  : isEquiv (fun z : X ⨿ Y =>
            match z return {b : Bool & bool_family X Y b} with
            | inl x => (no; x)
            | inr y => (yes; y)
            end).
Proof.
  refine (iso_to_isEquiv _
            (fun w => match w with
                      | (yes; y) => inr y
                      | (no; x) => inl x
                      end) _ _).
  - intros [x|y]; exact refl.
  - intros [[] t]; exact refl.
Defined.

(** Exercise [xca:binary-sum-id].  We use the encode-decode method instead
    of the suggested route via [xca:binary-sum-equiv]. *)
Section BinarySumPaths.

  Context {X Y : Type}.

  Definition code_inl (x : X) : X ⨿ Y -> Type
    := fun w => match w with inl x' => x = x' | inr _ => False end.

  Definition code_inr (y : Y) : X ⨿ Y -> Type
    := fun w => match w with inl _ => False | inr y' => y = y' end.

  Definition encode_inl {x : X} {w : X ⨿ Y} (r : inl x = w) : code_inl x w
    := trp (code_inl x) r refl.

  Definition encode_inr {y : Y} {w : X ⨿ Y} (r : inr y = w) : code_inr y w
    := trp (code_inr y) r refl.

  Definition inl_ne_inr (x : X) (y : Y) : (inl x = inr y) -> False
    := encode_inl.

  Definition path_inl_eqv (x x' : X) : (inl x = inl x' :> X ⨿ Y) ≃ (x = x').
  Proof.
    refine (mkEqv (@encode_inl x (inl x')) (ap inl) _ _).
    - intro r.
      enough (G : forall w (r : inl x = w),
                 match w return inl x = w -> Type with
                 | inl x' => fun r => ap inl (encode_inl r) = r
                 | inr _ => fun _ => True
                 end r) by exact (G _ r).
      intros w r'. destruct r'. exact refl.
    - intro p. destruct p. exact refl.
  Defined.

  Definition path_inr_eqv (y y' : Y) : (inr y = inr y' :> X ⨿ Y) ≃ (y = y').
  Proof.
    refine (mkEqv (@encode_inr y (inr y')) (ap inr) _ _).
    - intro r.
      enough (G : forall w (r : inr y = w),
                 match w return inr y = w -> Type with
                 | inl _ => fun _ => True
                 | inr y' => fun r => ap inr (encode_inr r) = r
                 end r) by exact (G _ r).
      intros w r'. destruct r'. exact refl.
    - intro p. destruct p. exact refl.
  Defined.

End BinarySumPaths.

(** Exercise [xca:bin-sum-univ-prop]. *)
Definition bin_sum_univ_prop `{Funext} (X Y Z : Type)
  : isEquiv (fun h : X ⨿ Y -> Z => (comp h inl; comp h inr) : (X -> Z) × (Y -> Z)).
Proof.
  refine (iso_to_isEquiv _
            (fun (w : (X -> Z) × (Y -> Z)) z =>
               match z with inl x => fst w x | inr y => snd w y end)
            _ (fun _ => refl)).
  intro h. apply ptw_inv. intros [x|y]; exact refl.
Defined.

(** Exercise: [(X ⨿ 𝟘) ≃ X]. *)
Definition sum_False_eqv (X : Type) : (X ⨿ False) ≃ X.
Proof.
  refine (mkEqv (fun z : X ⨿ False =>
                   match z with inl x => x | inr e => match e with end end)
                inl _ (fun _ => refl)).
  intros [x|[]]. exact refl.
Defined.

(** *** Unary sums *)

Inductive Copy (X : Type) : Type := inc : X -> Copy X.
Arguments inc {X} x.

(** The destructor [out(inc(x)) :≡ x]. *)
Definition out {X : Type} (z : Copy X) : X := match z with inc x => x end.

Definition inc_out {X : Type} (z : Copy X) : inc (out z) = z
  := match z with inc x => refl end.

Definition Copy_eqv (X : Type) : Copy X ≃ X
  := mkEqv out inc inc_out (fun _ => refl).

Definition path_inc_eqv {X : Type} (x x' : X) : (inc x = inc x') ≃ (x = x').
Proof.
  refine (mkEqv (@ap _ _ out (inc x) (inc x')) (@ap _ _ inc x x') _ _).
  - intro r.
    enough (G : forall w (r : inc x = w),
               match w return inc x = w -> Type with
               | inc x' => fun r => ap inc (ap out r) = r
               end r) by exact (G _ r).
    intros w r'. destruct r'. exact refl.
  - intro p. change (x = x') in p. destruct p. exact refl.
Defined.

Definition path_out_eqv {X : Type} (z z' : Copy X) : (out z = out z') ≃ (z = z').
Proof. destruct z as [x], z' as [x']. exact (Eqv_inv (path_inc_eqv x x')). Defined.

(** Example [exa:nnn]: the negated natural numbers [ℕ⁻ :≡ Copy_{-}(ℕ)]; the constructor
    [-] is called [negN], since [neg] is negation (2.15). *)
Inductive NNN : Type0 := negN : ℕ -> NNN.

(** The destructor [-(-n) :≡ n]. *)
Definition unneg (m : NNN) : ℕ := match m with negN n => n end.

Definition neg_unneg_neg (n : ℕ) : negN (unneg (negN n)) = negN n := refl.

Definition NNN_eqv : NNN ≃ ℕ
  := mkEqv unneg negN (fun m => match m with negN n => refl end)
           (fun _ => refl).

(** *** Lists *)

(** Definition [def:lists]: [X^*] is the library's [list X], with the
    empty list [ε :≡ nil] and the constructor [cons]. *)

Notation "X ^*" := (list X) (at level 1, format "X ^*") : uf_scope.
Notation ε := nil.

(** The induction principle is the library's [list_ind], with its
    computation rules holding by definition. *)
Definition list_ind_nil {X : Type} (T : X^* -> Type) (t : T ε)
  (g : forall x l, T l -> T (cons x l))
  : list_ind X T t g ε = t := refl.
Definition list_ind_cons {X : Type} (T : X^* -> Type) (t : T ε)
  (g : forall x l, T l -> T (cons x l)) (x : X) (l : X^*)
  : list_ind X T t g (cons x l) = g x l (list_ind X T t g l) := refl.

(** The length, [len(ε) :≡ 0] and [len(x l) :≡ succ(len(l))]: the
    library's [length]. *)
Definition len {X : Type} : X^* -> ℕ := @length X.

Definition len_nil {X : Type} : len (ε : X^*) = 0%nat := refl.
Definition len_cons {X : Type} (x : X) (l : X^*)
  : len (cons x l) = succ (len l) := refl.

(** Exercise [xca:list-contr], using the library's [repeat]. *)
Definition len_isEquiv {X : Type} (H : isContr X) : isEquiv (@len X).
Proof.
  refine (iso_to_isEquiv len (repeat (fst H)) _ _).
  - intro l. induction l as [|x l IH].
    + exact refl.
    + exact (ap011 cons (snd H x) IH).
  - intro n. induction n as [|n IH].
    + exact refl.
    + exact (ap succ IH).
Defined.

(** Head and tail, with values in [X ⨿ True] as in the book.  (The
    library's [head] uses [option], and its [tail] maps [ε] to [ε].) *)
Definition hd {X : Type} (l : X^*) : X ⨿ True
  := match l with ε => inr triv | cons x _ => inl x end.

Definition tl {X : Type} (l : X^*) : X^* ⨿ True
  := match l with ε => inr triv | cons _ l' => inl l' end.

(** Exercise [xca:reverse]: concatenation, by induction on the first
    argument, is the library's [app]; reversal is defined from it.  (The
    library's [reverse] uses an accumulator instead.) *)
Definition app_nil {X : Type} (l : X^*) : app ε l = l := refl.
Definition app_cons {X : Type} (x : X) (l1 l2 : X^*)
  : app (cons x l1) l2 = cons x (app l1 l2) := refl.

Definition rev {X : Type} : X^* -> X^*
  := list_ind X (fun _ => X^*) ε (fun x _ r => app r (cons x ε)).

(** Exercise [xca:concat-assoc]. *)
Definition app_assoc {X : Type} (l1 l2 l3 : X^*)
  : app l1 (app l2 l3) = app (app l1 l2) l3.
Proof.
  induction l1 as [|x l1 IH].
  - exact refl.
  - exact (ap (cons x) IH).
Defined.
