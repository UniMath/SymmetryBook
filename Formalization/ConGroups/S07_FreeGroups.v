(** * Section 8.7 Free groups

    Part of Chapter 8 ([congp.tex]); see [ConGroups.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:bfree]: [BFGT S] as the library's coequalizer of
      the two maps [S → 1], with [fbase], [floop], and the induction
      principle [BFG_ind] (computing on [fbase] by [refl]); it is
      connected ([BFGT_isConn]).
    - Evaluation at the loops is an equivalence
      [(BF_S →* (B, b)) ≃ (S → (b = b))] for any pointed type
      ([free_ev_eqv]).
    - The free group [FG S], with generators [fgen], and its universal
      property [Hom(F_S, G) ≃ (S → UG)] ([FG_univ]).  Deviation: as for
      sums, [FG S] is classified by the [1]-truncation of [BF_S], since
      the book shows that [BF_S] is a groupoid only for decidable [S].

    - Signed letters [Stilde] with complementation [compl], the
      reduction [reduce] (the exercise: by nested induction on words,
      using decidable equality), reduced words [Reduced], Dyck words
      [Dyck], and the interpretation [interp : S̃^* → UF_S].
    - The exercise [R_1 ≃ ℤ] ([R1_Z], with the value [wval] of a word
      and [reduce_rep]: a reduced word is [aⁿ] or [(a⁻¹)⁻ⁿ]).

    Left out (statements only, no proofs yet; time limit per result)
    - The remark [S̃^*/∼ ≃ R_S] ([reduce_quot_stmt]), theorem
      [thm:free-group-elements] ([thm_free_group_elements_stmt]), and the
      exercise [F_{n+1} = F_n ∨ ℤ]
      ([FG_succ_stmt], with [iterWedgeZ]).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Colimits.Coeq Spaces.List.Core Spaces.Finite.Fin Spaces.Int.
From SymmetryBook Require Export ConGroups.S06_Sums.

Local Open Scope uf_scope.

(** ** 8.7 Free groups *)

(** Definition [def:bfree]: the higher inductive type [BF_S] with a point
    [base] and loops [loop_s : base = base] for [s : S], implemented as
    the library's coequalizer of the two maps [S → 1]. *)
Section FreeGroup.

  Context (S : Type).

  Definition BFGT : Type := Coeq (fun _ : S => triv) (fun _ : S => triv).

  Definition fbase : BFGT := coeq triv.

  Definition floop (s : S) : fbase = fbase := cglue s.

  Definition BFG : Ustar := (BFGT; fbase).

  (** The induction principle, with its computation rules. *)
  Definition BFG_ind (A : BFGT -> Type) (a : A fbase)
    (l : forall s, PathOver A (floop s) a a) : forall x, A x
    := Coeq_ind A (fun t => match t with tt => a end) l.

  Definition BFG_ind_base (A : BFGT -> Type) (a : A fbase) l
    : BFG_ind A a l fbase = a := refl.

  Definition BFGT_isConn : isConn BFGT.
  Proof.
    refine (isConn_from_pt fbase _).
    exact (Coeq_ind (fun x => ptrunc (fbase = x)) (fun t => match t with tt => trunc refl end)
             (fun s => ptrunc_isProp _ _)).
  Defined.

  (** Evaluation [ev(k)(s) :≡ Ωk(loop_s)] is an equivalence
      [(BF_S →* (B, b)) ≃ (S → (b = b))], for any pointed type [(B, b)]. *)
  Definition free_ev {B : Type} {b : B} (k : BFG →* (B; b)) : S -> b = b
    := fun s => loops_fun k (floop s).

  Definition free_ve {B : Type} {b : B} (u : S -> b = b) : BFG →* (B; b)
    := (Coeq_rec B (fun _ => b) u; refl).

  Definition free_ev_ve `{Funext} {B : Type} {b : B} (u : S -> b = b)
    : free_ev (free_ve u) = u.
  Proof.
    apply ptw_inv. intro s. unfold free_ev, free_ve.
    refine (@loops_fun_refl BFG (B; b) (Coeq_rec B (fun _ => b) u) (floop s) @ _).
    exact (Coeq_rec_beta_cglue B _ u s).
  Defined.

  Definition free_ve_ev `{Funext} {B : Type} {b : B} (k : BFG →* (B; b))
    : free_ve (free_ev k) = k.
  Proof.
    destruct k as [k kp]. change (BFGT -> B) in k. revert b kp. refine (paths_ind_r _ _ _).
    refine (eqinv (snd (ptw_star (free_ve (free_ev ((k; refl) : BFG →* (B; k fbase))))
                                 ((k; refl) : BFG →* (B; k fbase)))) _).
    pose (u := free_ev ((k; refl) : BFG →* (B; k fbase))).
    simple refine (_; _).
    - refine (Coeq_ind (fun x => Coeq_rec B (fun _ => k fbase) u x = k x)
                (fun t => match t with tt => refl end) _).
      intro s. refine (transport_paths_FlFr (f := Coeq_rec B (fun _ => k fbase) u) (g := k) (cglue s) refl @ _).
      refine (ap (fun r => (r^ @ refl) @ ap k (cglue s)) (Coeq_rec_beta_cglue B _ u s) @ _).
      unfold u, free_ev. rewrite (@loops_fun_refl BFG (B; k fbase) k (floop s)).
      refine (ap (fun r => r @ _) (concat_p1 _) @ _). exact (concat_Vp _).
    - exact refl.
  Defined.

  Definition free_ev_eqv `{Funext} (B : Type) (b : B) : (BFG →* (B; b)) ≃ (S -> b = b)
    := mkEqv free_ev free_ve free_ve_ev free_ev_ve.

  (** The free group [F_S :≡ mkgroup(BF_S, base)].  The book proves that
      [BF_S] is a groupoid for decidable [S] (theorem
      [thm:free-group-elements]); as for sums, we take the
      [1]-truncation, which is a groupoid by construction. *)
  Definition FG : Group
    := mkgroup (Trunc 1 BFGT;
                (tr fbase;
                 (surj_isConn (f := tr)
                    (fun y => Trunc_ind (fun y => Ex (fun a => y = tr a))
                                (fun a => trunc (a; refl)) y)
                    BFGT_isConn;
                  IsTrunc_isGrpd (istrunc_truncation 1 _)))).

  (** The generators [ι_s : U F_S]. *)
  Definition fgen (s : S) : USym FG := ap tr (floop s).

  (** The universal property: [Hom(F_S, G) ≃ (S → UG)]. *)
  Definition FG_univ `{Funext} (G : Group) : Hom FG G ≃ (S -> USym G).
  Proof.
    refine (Eqv_comp (Copy_eqv _) _).
    refine (Eqv_comp (Eqv_of_Equiv (equiv_functor_sigma_pb
               (Q := fun k : BFGT -> utype (BG G) => sh G = k fbase)
               (Equiv_of_Eqv (@trunc_univ_prop _ 1 BFGT (utype (BG G))
                                (isGrpd_IsTrunc (BG_isGrpd G)))))) _).
    exact (free_ev_eqv (utype (BG G)) (sh G)).
  Defined.

End FreeGroup.

(** ** Words in signed letters *)
Section Words.

  Context {S : Type} (dS : isDecSet S).

  (** Signed letters [S̃ :≡ S ⨿ S] with complementation. *)
  Definition Stilde : Type := S ⨿ S.

  Definition compl (x : Stilde) : Stilde
    := match x with inl a => inr a | inr a => inl a end.

  Definition Stilde_dec (x y : Stilde) : isDecidable (x = y).
  Proof.
    destruct x as [a|a], y as [b|b].
    - destruct (snd (dS a b)) as [e|n]; [left; exact (ap inl e) | right].
      intro p. exact (n (ap (fun w => match w with inl c => c | inr _ => a end) p)).
    - right. intro p.
      exact (false_ne_true (ap (fun w : Stilde => match w with inl _ => false | inr _ => true end) p)).
    - right. intro p.
      exact (false_ne_true (ap (fun w : Stilde => match w with inl _ => true | inr _ => false end) p)).
    - destruct (snd (dS a b)) as [e|n]; [left; exact (ap inr e) | right].
      intro p. exact (n (ap (fun w => match w with inr c => c | inl _ => a end) p)).
  Defined.

  (** The reduction [ρ_S], by nested induction on words (the exercise
      after the definition of reduced words). *)
  Fixpoint reduce (w : list Stilde) : list Stilde
    := match w with
       | nil => nil
       | cons x w' =>
           match reduce w' with
           | nil => cons x nil
           | cons y r => match Stilde_dec y (compl x) with
                         | inl _ => r
                         | inr _ => cons x (cons y r)
                         end
           end
       end.

  (** Reduced words [R_S] (the image of [ρ_S]) and Dyck words [D_S]. *)
  Definition Reduced : Type := im reduce.

  Definition Dyck : Type := fiber reduce nil.

  (** The remark that [ρ_S] induces [S̃^*/∼ ≃ R_S] (statement only). *)
  Definition reduce_rel (u v : list Stilde) : PropU
    := ((reduce u = reduce v);
        list_isSet (sum_isSet (fun x y => fst (dS x y)) (fun x y => fst (dS x y))) _ _).

  Definition reduce_quot_stmt `{Univalence} : Type
    := {e : quot reduce_rel ≃ Reduced &
         forall w, fst (fst e (S22_SetOperations.cls reduce_rel w)) = reduce w}.

  (** The interpretation [⟦_⟧ : S̃^* → UF_S]. *)
  Fixpoint interp (w : list Stilde) : USym (FG S)
    := match w with
       | nil => refl
       | cons (inl a) w' => fgen S a ⋅ interp w'
       | cons (inr a) w' => (fgen S a)⁻¹ ⋅ interp w'
       end.

  (** Theorem [thm:free-group-elements] (statement only). *)
  Definition thm_free_group_elements_stmt : Type
    := isEquiv (fun w : Reduced => interp (fst w)).

End Words.

(** The exercise [R_1 ≃ ℤ] (statement only), with [ε ↦ 0] and [ζ_*]
    corresponding to [zs]. *)
Definition True_isDecSet : isDecSet True
  := hedberg (fun x y => match x, y with tt, tt => inl refl end).

Definition zeta_star (w : Reduced True_isDecSet) : Reduced True_isDecSet
  := (reduce True_isDecSet (cons (inl triv) (fst w)); trunc (cons (inl triv) (fst w); refl)).

Definition R1_Z_stmt : Type
  := {e : Reduced True_isDecSet ≃ ℤ &
       (fst e (nil; trunc (nil; refl)) = iplus 0)
       × (forall w, fst e (zeta_star w) = zs (fst e w))}.

(** The proof: the value [wval w : Int] of a word (the number of [a]s
    minus the number of [a⁻¹]s) is invariant under [reduce], and a reduced
    word is determined by its value: [reduce w = repI (wval w)], with
    [repI n] the word [aⁿ] or [(a⁻¹)⁻ⁿ].  We transfer from the library's
    [Int] to [ℤ] along [fromInt]. *)
Fixpoint wval (w : list (@Stilde True)) : Int
  := match w with
     | nil => zero
     | cons (inl _) w' => int_succ (wval w')
     | cons (inr _) w' => int_pred (wval w')
     end.

Fixpoint repP (n : ℕ) : list (@Stilde True)
  := match n with O => cons (inl triv) nil | S n' => cons (inl triv) (repP n') end.

Fixpoint repN (n : ℕ) : list (@Stilde True)
  := match n with O => cons (inr triv) nil | S n' => cons (inr triv) (repN n') end.

Definition repI (x : Int) : list (@Stilde True)
  := match x with negS n => repN n | zero => nil | posS n => repP n end.

Definition wval_rep (x : Int) : wval (repI x) = x.
Proof.
  destruct x as [n| |n]; [|exact refl|].
  - induction n as [|n IH]; [exact refl|]. exact (ap int_pred IH).
  - induction n as [|n IH]; [exact refl|]. exact (ap int_succ IH).
Defined.

Definition inl_ne_inr_T (e : (inl triv : @Stilde True) = inr triv) : Empty
  := false_ne_true (ap (fun w : @Stilde True => match w with inl _ => false | inr _ => true end) e).

Definition reduce_rep (w : list (@Stilde True)) : reduce True_isDecSet w = repI (wval w).
Proof.
  induction w as [|c w IH]; [exact refl|].
  destruct c as [[]|[]]; cbn [reduce wval]; rewrite IH; destruct (wval w) as [[|n]| |[|n]];
    cbn [repI repN repP int_succ int_pred compl];
    try exact refl;
    destruct (Stilde_dec True_isDecSet _ _) as [e|ne];
    solve [ exact refl | destruct (inl_ne_inr_T e) | destruct (inl_ne_inr_T e^)
          | destruct (ne refl) ].
Defined.

Definition R1_Z : R1_Z_stmt.
Proof.
  pose (sL := list_isSet (sum_isSet (fun x y => fst (True_isDecSet x y))
                                    (fun x y => fst (True_isDecSet x y)))).
  assert (rr : forall x, reduce True_isDecSet (repI x) = repI x)
    by (intro x; exact (reduce_rep _ @ ap repI (wval_rep x))).
  simple refine (mkEqv (fun w => fromInt (wval (fst w)))
                   (fun z => (repI (toInt z); trunc (repI (toInt z); (rr _)^))) _ _; (refl; _)).
  - intros [u s]. apply (path_sigma_prop (fun _ => ptrunc_isProp)). cbn.
    refine (ap repI (toInt_fromInt _) @ _).
    refine (ptrunc_rec (sL _ _) _ s). intros [x p]. destruct p^.
    exact (ap repI (ap wval (reduce_rep x) @ wval_rep _) @ (reduce_rep x)^).
  - intro z. exact (ap fromInt (wval_rep _) @ fromInt_toInt z).
  - intro w.
    exact (ap fromInt (ap wval (reduce_rep (cons (inl triv) (fst w))) @ wval_rep _)
           @ fromInt_succ _).
Defined.

(** The exercise [F_{n+1} ≃ F_n ∨ ℤ] (statement only), hence
    [F_n = ((ℤ ∨ ℤ) ∨ ⋯) ∨ ℤ] with [n] copies of [ℤ]. *)
Fixpoint iterWedgeZ `{Univalence} (n : ℕ) : Group
  := match n with O => TG | S n' => sumG (iterWedgeZ n') ZZ end.

Definition FG_succ_stmt `{Univalence} : Type
  := (forall n : ℕ, Iso (FG (Fin (S n))) (sumG (FG (Fin n)) ZZ))
     × (forall n : ℕ, FG (Fin n) = iterWedgeZ n).
