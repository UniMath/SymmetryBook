(** * Chapter 4 of [group.tex]: Groups, concretely

    ** Summary of this formalization

    Section 4.1 is an overview without results.  Sections 4.2 - 4.7: the
    type of groups ([S02_TypeOfGroups.v]), abstract groups
    ([S03_AbstractGroups.v]), homomorphisms ([S04_Homomorphisms.v]),
    the sign homomorphism ([S05_Sign.v]), bicycles
    ([S06_Bicycles.v]) and ∞-groups ([S07_InfinityGroups.v]), one file per section, each starting
    with its own summary.  They build on Chapters 2 and 3
    ([Circle.Circle]).  Everything compiles with nothing admitted.

    [Group] and [Hom G H] are wrapped copies ([Copy], Section 2.12) of
    [UUscone] and of pointed maps, as in the book.  Since [Copy] has no
    definitional eta rule, [mkgroup (B G)] is only propositionally equal
    to [G] ([inc_out]).  [UUscone] and [Group] are universe
    polymorphic; groups such as [Aut(G)] for [G : Group] live in a larger
    universe (cf. the book's footnote on size issues), and with
    replacement have a copy in the universe of [G] ([AutGrp_small],
    Section 9.7). *)

From SymmetryBook Require Export
  Group.S02_TypeOfGroups
  Group.S03_AbstractGroups
  Group.S04_Homomorphisms
  Group.S05_Sign
  Group.S06_Bicycles
  Group.S07_InfinityGroups.
