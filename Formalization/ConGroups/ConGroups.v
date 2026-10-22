(** * Chapter 8 of [congp.tex]: Constructing groups

    ** Summary of this formalization

    Section 8.1 is an overview without results, and Section 8.5 (pushouts
    of types) is still to be written in the book.  Sections 8.2 - 8.4,
    8.6 and 8.7: semidirect products ([S02_Semidirect.v]), wreath products
    ([S03_Wreath.v]), the pullback ([S04_Pullback.v]), sums of groups
    ([S06_Sums.v]) and free groups ([S07_FreeGroups.v]), one file per
    section, each starting with its own summary.  They build on Chapters
    2 - 7 ([AbsGroup.AbsGroup]).  Everything compiles with nothing
    admitted.

    Wedges and the classifying types of free groups are the library's
    pushouts and coequalizers; sums of groups and free groups are
    classified by their [1]-truncations, since the book proves these
    types to be groupoids only in the decidable case. *)

From SymmetryBook Require Export
  ConGroups.S02_Semidirect
  ConGroups.S03_Wreath
  ConGroups.S04_Pullback
  ConGroups.S06_Sums
  ConGroups.S07_FreeGroups.
