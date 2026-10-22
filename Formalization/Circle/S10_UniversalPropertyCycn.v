(** * Section 3.10 Universal property of Cyc_n

    Part of Chapter 3 ([circle.tex]); see [Circle.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - For [n = k+1]: the base point [pt_n :≡ (Fin n, zs)] of [Cyc_n] and
      its symmetry [σ_n :≡ (zs⁻¹, !)] ([pt_n], [sigma_n]); powers of a
      symmetry ([ppow]).

    Left out (statements only, no proofs yet; the section was not
    formalized in the run on Chapter 3, and was added later with
    statements only)
    - Theorem [prop:ump-cycn-into-groupoids] ([ump_cycn_stmt]): for a
      groupoid [A], [f ↦ (f(pt_n), ap_f(σ_n), !)] is an equivalence
      [(Cyc_n → A) ≃ ∑_{a:A} ∑_{σ : a = a} (refl_a = σ^n)].  The map needs
      [σ_n^n = refl], which is not formalized yet, so the statement asks
      for an equivalence whose first two components are [f(pt_n)] and
      [ap_f(σ_n)].
    - The corollary after the theorem ([cycn_coverings_stmt]): connected
      coverings over [Cyc_n] are the cycles [(X,t)] with [t^n = id]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Spaces.Nat.Core Spaces.Finite.Fin.
From SymmetryBook Require Export Circle.S09_HigherImages.

Local Open Scope uf_scope.

(** ** 3.10 Universal property of [Cyc_n] *)

Section UniversalPropertyCycn.

  Context `{Univalence} (k : ℕ).

  (** The base point [pt_n :≡ (Fin n, zs)] of [Cyc_n], for [n = k+1]. *)
  Definition pt_n : Cycm k := (Fincyc k; trunc refl).

  (** The symmetry [σ_n :≡ (zs⁻¹, !)] of [pt_n]: [zs⁻¹] commutes with
      [zs]. *)
  Definition zs_inv_comm
    : fst (Eqv_inv (finsuccEqv k)) ∘ fst (finsuccEqv k)
      = fst (finsuccEqv k) ∘ fst (Eqv_inv (finsuccEqv k))
    := ptw_inv (fun x => eqinv_l (snd (finsuccEqv k)) x @ (eqinv_r (snd (finsuccEqv k)) x)^).

  Definition sigma_n : pt_n = pt_n
    := path_sigma_prop (fun _ => ptrunc_isProp) (u := pt_n) (v := pt_n)
         (cyc_path (Fincyc k) (Fincyc k) (endo_path (Eqv_inv (finsuccEqv k)) zs_inv_comm)).

  (** Powers [σ^i] of a symmetry. *)
  Fixpoint ppow {A : Type} {a : A} (s : a = a) (i : ℕ) : a = a
    := match i with O => refl | S i' => s ⋅ ppow s i' end.

  (** Theorem [prop:ump-cycn-into-groupoids] (statement only). *)
  Definition ump_cycn_stmt : Type
    := forall (A : Type) (gA : isGrpd A),
         {e : (Cycm k -> A) ≃ {a : A & {s : a = a & refl = ppow s (S k)}} &
           forall f : Cycm k -> A,
             ((f pt_n; ap f sigma_n) : {a : A & a = a})
             = (fst (fst e f); fst (snd (fst e f)))}.

  (** The corollary after the theorem (statement only): the connected
      coverings over [Cyc_n] are the cycles whose order divides [n], i.e.
      with [t^n = id]. *)
  Definition cycn_coverings_stmt : Type
    := {Fam : Cycm k -> SetU & isConn {c : Cycm k & fst (Fam c)}}
       ≃ {c : Cyc & tpow (fst (snd c)) (iplus (S k)) = idmap}.

End UniversalPropertyCycn.
