(** * Chapter 2 of [intro-uf.tex]: An introduction to univalent mathematics

    ** Summary of this formalization

    This file collects the sections 2.2 - 2.27 of Chapter 2 of the book
    "Symmetry", one file [S<nn>_<Name>.v] per section, each starting with
    its own summary.  Each section builds on the previous one by
    [Require Export], so importing this file gives the whole chapter.
    Everything compiles with nothing admitted.

    The chapter introduces the book's basic notions.  Those that occur
    definitionally in Coq-HoTT are defined from the library notion
    ([cst], [comp], [id], [ℕ], [ind_ℕ], [add], [mul], [path_ind], [symm],
    [trp], [ptw], [PathOver], [apd], [apap], [fst], [snd], [tot], [neg],
    [ptrunc], [strunc], [Fin], ...).  The others are the book's own
    ([trans], [isContr], [fiber], [isEquiv], [≃], [×], [isProp], [isSet],
    [is_ntype], [UnivalenceUF], [isSurj], [isInj], pointed types, the
    quotient [quot], [le], [isFinSet], ...), and each section shows them
    equivalent to the library's notions where needed ("Bridges to
    Coq-HoTT").

    Axioms ([Print Assumptions]): function extensionality and univalence
    come from Coq-HoTT's [Funext] and [Univalence] and are used only by
    the results that need them; the book's principles [funext] and
    [UnivalenceUF] are derived from them (2.9, 2.15).  Truncations and
    quotients use the library's higher inductive types.  The replacement
    principle (2.19) is a hypothesis where it is used.

    Placement differing from the book: exercise [xca:ints-as-quotient]
    (2.22) is in 2.23, and the remark that [FinSet] is essentially small
    (2.24) is in 2.27, because their proofs use later results (for the
    latter, the lemma [sigma_contr_fibers] of 2.27).

    NOTEs for the book text (hints by the author that simplified proofs)
    are in the summaries of 2.17 ([xca:unique-fact-image]), 2.23
    ([xca:ints-as-quotient]), 2.24 ([xca:2-element-sets]) and 2.27
    ([FinSet] essentially small). *)

From SymmetryBook Require Export
  IntroUF.S02_Types
  IntroUF.S03_Universes
  IntroUF.S04_NaturalNumbers
  IntroUF.S05_IdentityTypes
  IntroUF.S06_ProductTypes
  IntroUF.S07_IdentifyingInFamilies
  IntroUF.S08_SumTypes
  IntroUF.S09_Equivalences
  IntroUF.S10_IdentifyingPairs
  IntroUF.S11_BinaryProducts
  IntroUF.S12_InductiveTypes
  IntroUF.S13_Univalence
  IntroUF.S14_HeavyTransport
  IntroUF.S15_PropsSetsGroupoids
  IntroUF.S16_PropTruncation
  IntroUF.S17_SurjInj
  IntroUF.S18_Decidability
  IntroUF.S19_Replacement
  IntroUF.S20_Subtypes
  IntroUF.S21_PointedTypes
  IntroUF.S22_SetOperations
  IntroUF.S23_MoreNaturalNumbers
  IntroUF.S24_FiniteSets
  IntroUF.S25_FamiliesMaps
  IntroUF.S26_HigherTruncations
  IntroUF.S27_StuffStructure.
