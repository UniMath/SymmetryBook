(** * Chapter 10 of [fingp.tex]: Finite groups

    ** Summary of this formalization

    Section 10.1 is an overview without results.  Sections 10.2 - 10.4:
    Lagrange's theorem, counting version ([S02_Lagrange.v]), Cauchy's
    theorem ([S03_Cauchy.v]) and Sylow's theorems ([S04_Sylow.v]), one
    file per section, each starting with its own summary.  They build on
    Chapters 2 - 9 ([Subgroups.Subgroups]).  Everything compiles with
    nothing admitted.

    Proved: the counting version of Lagrange's theorem (from Section
    5.3) and the order of a product.  Cauchy's and Sylow's theorems and
    the lemmas leading to them are stated only. *)

From SymmetryBook Require Export
  FinGroups.S02_Lagrange
  FinGroups.S03_Cauchy
  FinGroups.S04_Sylow.
