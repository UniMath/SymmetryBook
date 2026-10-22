(** * Chapter 7 of [absgroup.tex]: Groups, abstractly

    ** Summary of this formalization

    Section 7.1 is an overview without results.  Sections 7.2 - 7.7:
    monoids and abstract groups ([S02_Monoids.v]), abstract homomorphisms
    ([S03_AbstractHomomorphisms.v]), groups from abstract to concrete and
    back ([S04_AbstractToConcrete.v]), homomorphisms
    ([S05_Homomorphisms.v]), actions ([S06_Actions.v]) and heaps
    ([S07_Heaps.v]), one file per section, each starting with its own
    summary.  The sections hidden in the published book ("Benefits from
    having the categorical equivalence", "Delooping groups and
    homomorphisms via the Rezk completion") are not formalized.  They
    build on Chapters 2 - 6 ([Cats.Cats]).  Everything compiles with
    nothing admitted.

    Main results: [abstr : Group → AbsGroup] is an equivalence
    ([abstr_isEquiv]), assuming the replacement principle to keep the
    inverse in the same universe (NOTE for the book text); [Hom(G,H) ≃
    absHom(abstr G, abstr H)] ([abstr_hom_eqv]); [G-Set ≃ abstr(G)-Set]
    ([actions_eqv]). *)

From SymmetryBook Require Export
  AbsGroup.S02_Monoids
  AbsGroup.S03_AbstractHomomorphisms
  AbsGroup.S04_AbstractToConcrete
  AbsGroup.S05_Homomorphisms
  AbsGroup.S06_Actions
  AbsGroup.S07_Heaps.
