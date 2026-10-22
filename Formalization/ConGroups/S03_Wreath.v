(** * Section 8.3 Wreath products

    Part of Chapter 8 ([congp.tex]); see [ConGroups.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - The action [H^X(z) :≡ Aut_{X(z) → BH}(_ ↦ sh_H)] ([powerAction]) and
      the wreath product [H ≀_X G :≡ G ⋉ H^X] ([wreath]).
    - For [X(sh_G)] finite: [B(H ≀_X G) ≃ ∑_{z:BG} (X(z) → BH)]
      ([B_wreath_eqv]), using that finite powers of connected types are
      connected ([PiG_isConn] of Section 4.2, via finite choice).

    The examples (hypercubes, Sudoku, trees) are empty in the book.
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core.
From SymmetryBook Require Export ConGroups.S02_Semidirect.

Local Open Scope uf_scope.

(** ** 8.3 Wreath products *)

Section Wreath.

  Context `{Uv : Univalence} (G H : Group) (X : GSet G).

  (** The action [H^X : BG → Group],
      [H^X(z) :≡ Aut_{X(z) → BH}(_ ↦ sh_H)]. *)
  Definition powerAction (z : utype (BG G)) : Group
    := AutG (Pi_ntype 1 (fun _ : el X z => BG_isGrpd H)) (fun _ => sh H).

  (** The wreath product [H ≀_X G :≡ G ⋉ H^X]. *)
  Definition wreath : Group := semidirect G powerAction.

  (** If the underlying set of [X] is finite, the classifying type of
      [H ≀_X G] is [∑_{z:BG} (X(z) → BH)]. *)
  Context (hX : isFinSet (el X (sh G))).

  Definition el_isFinSet (z : utype (BG G)) : isFinSet (el X z)
    := ptrunc_rec ptrunc_isProp (fun p => trp (fun w => isFinSet (el X w)) p hX)
         (snd (BG_isConn G) (sh G) z).

  Definition power_isConn (z : utype (BG G)) : isConn (el X z -> utype (BG H))
    := PiG_isConn (el_isFinSet z) (fun _ => H).

  Definition B_wreath_eqv
    : utype (BG wreath) ≃ {z : utype (BG G) & el X z -> utype (BG H)}
    := (tot (fun z => @fst _ (fun f => ptrunc ((fun _ => sh H) = f)));
        tot_isEquiv _ (fun z => component_fst_isEquiv (power_isConn z) _)).

End Wreath.
