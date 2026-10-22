(** * Section 7.5 Homomorphisms, from abstract to concrete and back

    Part of Chapter 7 ([absgroup.tex]); see [AbsGroup.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Lemma [lem:homomabstrconcr]: [abstr : Hom(G,H) ≃ absHom(abstr G,
      abstr H)] ([abstr_hom_eqv]).  The inverse [deloop] follows the
      book's delooping: the family [Cfam f x] is contractible at [sh_G]
      ([C_sh_contr], a retract of [∑_y (sh_H = y)]) and hence everywhere
      ([C_contr]); its centers give [Bg] and [pg], with the naturality
      [pg_nat] by induction.  [abstr ∘ deloop = id] ([abstr_deloop]) as in
      the book; for [deloop ∘ abstr = id] (left to the reader in the
      book) we use that a pointed map [k] gives another section of [C]
      ([ck_prop]), so it agrees with the centers, and [ptw_star].

    - The category of abstract groups ([AbsGroupCat]) and the functor
      [abstr] ([AbstrFun]), fully faithful by [abstr_hom_eqv]
      ([AbstrFun_ff]).

    Left out (statements only, no proofs yet; time limit per result)
    - The functor [concr] on morphisms (it uses [φ_!]) and exercise
      [xca:Bconcr-OK] ([xca_Bconcr_OK_stmt]); theorem
      [thm:concr-equiv-cats], stated for [abstr]
      ([thm_concr_equiv_cats_stmt]).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core.
From SymmetryBook Require Export AbsGroup.S04_AbstractToConcrete.

Local Open Scope uf_scope.

(** ** 7.5 Homomorphisms, from abstract to concrete and back *)

(** Lemma [lem:homomabstrconcr]: "delooping" an abstract homomorphism,
    following the book's family [C(x)]. *)
Section Deloop.

  Context `{fe : Funext} {G H : Group} (f : absHom (abstr G) (abstr H)).

  Local Notation fh := (fst f).

  Definition Cfam (x : utype (BG G)) : Type
    := {y : utype (BG H) & {p : (sh G = x) -> (sh H = y) &
          forall (ω : sh G = sh G) (α : sh G = x), p (α ⋅ ω) = p α ⋅ fh ω}}.

  Definition Cprop_isProp (x : utype (BG G)) (y : utype (BG H))
    (p : (sh G = x) -> (sh H = y))
    : isProp (forall (ω : sh G = sh G) (α : sh G = x), p (α ⋅ ω) = p α ⋅ fh ω)
    := Pi_isProp (fun _ => Pi_isProp (fun _ => BG_isGrpd H _ _ _ _)).

  (** [C(sh_G)] is a retract of [∑_y (sh_H = y)], hence contractible. *)
  Definition C_fw (w : {y : utype (BG H) & sh H = y}) : Cfam (sh G).
  Proof.
    refine (fst w; ((fun α => snd w ⋅ fh α); _)).
    intros ω α. refine (ap (fun q => snd w ⋅ q) (snd f α ω) @ _).
    exact (trans_assoc _ _ _).
  Defined.

  Definition C_sh_contr : isContr (Cfam (sh G)).
  Proof.
    refine (isContr_retract C_fw (fun c => (fst c; fst (snd c) refl)) _
              (singleton_contr (sh H))).
    intros [y [p c]]. unfold C_fw. cbn.
    apply (ap (fun w => (y; w))).
    refine (path_sigma_prop (Cprop_isProp (sh G) y) _). cbn.
    apply ptw_inv. intro α. exact (c α refl)^.
  Defined.

  Definition C_contr (x : utype (BG G)) : isContr (Cfam x).
  Proof.
    refine (ptrunc_rec (isContr_isProp _) _ (snd (BG_isConn G) (sh G) x)).
    intro q. destruct q. exact C_sh_contr.
  Defined.

  Definition Bg (x : utype (BG G)) : utype (BG H) := fst (fst (C_contr x)).

  Definition pg (x : utype (BG G)) : (sh G = x) -> (sh H = Bg x)
    := fst (snd (fst (C_contr x))).

  Definition pg_prop (x : utype (BG G)) (ω : sh G = sh G) (α : sh G = x)
    : pg x (α ⋅ ω) = pg x α ⋅ fh ω
    := snd (snd (fst (C_contr x))) ω α.

  Definition deloop : Hom G H := mkhom ((Bg; pg (sh G) refl) : BG G →* BG H).

  (** [p(λα) = Bg(λ) p(α)], by induction on [λ]. *)
  Definition pg_nat {x x' : utype (BG G)} (l : x = x') (α : sh G = x)
    : pg x' (l ⋅ α) = ap Bg l ⋅ pg x α.
  Proof. destruct l. exact refl. Defined.

  Definition abstr_deloop_pt (ω : USym G) : USymf deloop ω = fh ω.
  Proof.
    pose (pt := pg (sh G) refl).
    assert (e : ap Bg ω ⋅ pt = pt ⋅ fh ω).
    { refine ((pg_nat ω refl)^ @ _). refine (ap (pg (sh G)) (trans_1p ω) @ _).
      exact (pg_prop (sh G) ω refl). }
    unfold USymf, loops_fun, deloop, Bf, mkhom. cbn. fold pt.
    refine (ap (fun q => pt⁻¹ ⋅ q) e @ _).
    refine (trans_assoc _ _ _ @ _).
    exact (ap (fun q => q ⋅ fh ω) (trans_pV pt)).
  Defined.

  Definition abstr_deloop : abstr_hom deloop = f
    := path_absHom (abstr_hom deloop) f abstr_deloop_pt.

End Deloop.

(** The pointed map [k] gives a section of [C] for [f :≡ abstr(k)]. *)
Definition ck_prop {A B : Type} (x0 : A) (k0 : A -> B) (y : B) (kp : y = k0 x0)
  {x : A} (α : x0 = x) (ω : x0 = x0)
  : ap k0 (α ⋅ ω) ⋅ kp
    = (ap k0 α ⋅ kp) ⋅ loops_fun ((k0; kp) : (A; x0) →* (B; y)) ω.
Proof.
  revert y kp. refine (paths_ind_r _ _ _).
  destruct α. exact refl.
Defined.

Definition C_path_fst {G H : Group} {f : absHom (abstr G) (abstr H)}
  {x : utype (BG G)} {c c' : Cfam f x} (P : c = c') (α : sh G = x)
  : ap fst P ⋅ fst (snd c) α = fst (snd c') α.
Proof. destruct P. exact refl. Defined.

Definition deloop_abstr `{fe : Funext} {G H : Group} (k : Hom G H)
  : deloop (abstr_hom k) = k.
Proof.
  destruct k as [[k0 kp]].
  pose (f := abstr_hom (mkhom ((k0; kp) : BG G →* BG H))).
  pose (ck := fun x : utype (BG G) =>
          ((k0 x; ((fun α => ap k0 α ⋅ kp);
                   fun ω α => ck_prop (sh G) k0 (sh H) kp α ω)) : Cfam f x)).
  pose (P := fun x => isContr_isProp' (C_contr f x) (fst (C_contr f x)) (ck x)).
  apply (ap mkhom).
  refine (eqinv (snd (ptw_star ((Bg f; pg f (sh G) refl) : BG G →* BG H) (k0; kp))) _).
  refine (exist _ (fun x => ap fst (P x)) _). cbn.
  exact (C_path_fst (P (sh G)) refl).
Defined.

Definition abstr_hom_isEquiv `{fe : Funext} (G H : Group) : isEquiv (@abstr_hom G H)
  := iso_to_isEquiv _ deloop deloop_abstr abstr_deloop.

Definition abstr_hom_eqv `{fe : Funext} (G H : Group) : Hom G H ≃ absHom (abstr G) (abstr H)
  := (abstr_hom; abstr_hom_isEquiv G H).

(** The category of abstract groups and the functor [abstr] (now that
    categories are available, Chapter 6).  By [abstr_hom_eqv], [abstr] is
    fully faithful. *)
Definition AbsGroupCat `{Funext} : WildPreCat
  := Build_WildPreCat AbsGroup absHom absHom_id (fun G H K g f => absHom_comp g f)
       (fun G H f => path_absHom (absHom_comp (absHom_id H) f) f (fun s => refl))
       (fun G H f => path_absHom (absHom_comp f (absHom_id G)) f (fun s => refl))
       (fun G H K L f g h => path_absHom (absHom_comp h (absHom_comp g f))
                               (absHom_comp (absHom_comp h g) f) (fun s => refl)).

Definition AbstrFun `{Funext} : Functor GroupCat AbsGroupCat
  := Build_Functor GroupCat AbsGroupCat abstr (fun G H f => abstr_hom f)
       abstr_id (fun G0 G1 G2 f0 f1 => abstr_comp f0 f1).

Definition AbstrFun_ff `{Funext} : isFullyFaithful AbstrFun
  := fun G H => abstr_hom_isEquiv G H.

(** Exercise [xca:Bconcr-OK] and theorem [thm:concr-equiv-cats]
    (statements only).  [concr] on morphisms uses [φ_!] (Section 7.4,
    stated only), so we state the theorem for [abstr], whose inverse
    [concr] is.  The first component is part [it:Bconcr_pt]. *)
Definition xca_Bconcr_OK_stmt `{Univalence} : Type
  := (forall (G H : AbsGroup) (φ : absHom G H) (F : absGSet G -> absGSet H),
        (forall X, gset (F X) ≃ quot (phi_rel φ X)) -> F (absprtor G) = absprtor H)
     × {C : Functor AbsGroupCat GroupCat & forall G, fob C G = concr G}.

Definition thm_concr_equiv_cats_stmt `{Funext} : Type := isCatEquiv AbstrFun.
