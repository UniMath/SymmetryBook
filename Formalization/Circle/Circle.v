(** * Chapter 3 of [circle.tex]: The universal symmetry: the circle

    ** Summary of this formalization

    Sections 3.1 - 3.10 of Chapter 3 of the book "Symmetry", one file per
    section, each starting with its own summary: the circle and its
    universal property ([S01_Circle.v]), the integers as a higher
    inductive type ([S02_Integers.v]), coverings ([S03_Coverings.v]), the
    symmetries in the circle ([S04_SymmetriesCircle.v]), the circle as the
    type of infinite cycles ([S05_Reinterpretation.v]) and connected
    coverings over the circle ([S06_ConnCoverings.v]), permutations
    ([S07_Permutations.v]), the [m]-th root ([S08_MthRoot.v]) and higher
    images ([S09_HigherImages.v]), and the universal property of [Cyc_n]
    ([S10_UniversalPropertyCycn.v], statements only); 3.6 partly.  The
    hidden Section 3.11 is not formalized.
    They build on Chapter 2 ([IntroUF.IntroUF]).  Everything compiles with
    nothing admitted.

    The circle is the library's [Circle] and the integers are the
    library's [Pushout] of [-0] and [0] over [𝟙]; both are higher inductive
    types of Coq-HoTT (graph quotients).  [Funext] and [Univalence] are
    used only where needed. *)

From SymmetryBook Require Export
  Circle.S01_Circle
  Circle.S02_Integers
  Circle.S03_Coverings
  Circle.S04_SymmetriesCircle
  Circle.S05_Reinterpretation
  Circle.S06_ConnCoverings
  Circle.S07_Permutations
  Circle.S08_MthRoot
  Circle.S09_HigherImages
  Circle.S10_UniversalPropertyCycn.
