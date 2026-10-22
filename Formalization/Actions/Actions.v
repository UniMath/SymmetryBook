(** * Chapter 5 of [actions.tex]: Actions

    ** Summary of this formalization

    Section 5.1 is an overview without results.  Sections 5.2 - 5.7:
    group actions ([S02_GSets.v]), subgroups ([S03_Subgroups.v]),
    invariant maps and orbits ([S04_Orbits.v]), the classifying type as
    the type of torsors ([S05_Torsors.v]), Cayley's theorem
    ([S06_Cayley.v]) and the lemma that is not Burnside's
    ([S07_Burnside.v]), one file per section, each starting with its own
    summary.  They build on Chapters 2 - 4 ([Group.Group]).  Everything
    compiles with nothing admitted.

    [G]-sets are maps [BG → Set], with [Set] the book's [∑_X isSet(X)];
    finiteness and cardinalities are mostly expressed with the library's
    [Finite] and [fcard]. *)

From SymmetryBook Require Export
  Actions.S02_GSets
  Actions.S03_Subgroups
  Actions.S04_Orbits
  Actions.S05_Torsors
  Actions.S06_Cayley
  Actions.S07_Burnside.
