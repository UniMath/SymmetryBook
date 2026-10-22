(** * Chapter 6 of [cats.tex]: A categorical interlude

    ** Summary of this formalization

    Section 6.1 is an overview without results, and Section 6.9
    (monoidal categories) is empty in the book.  Sections 6.2 - 6.8:
    categories ([S02_Categories.v]), abstract notions and duality
    ([S03_Duality.v]), functors and natural transformations
    ([S04_Functors.v]), adjunctions ([S05_Adjunctions.v]), the Yoneda
    lemma ([S06_Yoneda.v]), equivalences of categories
    ([S07_Equivalences.v]) and limits and colimits ([S08_Limits.v]), one
    file per section, each starting with its own summary.  They build on
    Chapters 2 - 5 ([Actions.Actions]).  Everything compiles with nothing
    admitted; results left out are stated (as definitions of their
    statements, named [..._stmt]) at their place, and listed in the
    summaries.

    Main design choices: a wild precategory is a record [WildPreCat] with
    the laws as identifications; isomorphisms are [IsoC] (to avoid a
    clash with the group isomorphisms of Section 4.4); functors
    ([Functor]) and adjunctions ([Adjunction]) are records.  The
    categories of types, pointed types, families, sets, groups and
    [G]-sets are shown univalent.  The pullback of types is formalized
    here and used in Section 8.4.

    Main results: [isIsoC f] is a proposition; the Yoneda lemma
    ([yoneda_eqv]) and full faithfulness of the Yoneda embedding
    ([yo_ff]); the triangle laws of an adjunction; equivalences are fully
    faithful ([cat_equiv_ff]); the Rezk completion is a weak equivalence
    ([RezkEta_isWeakEquiv]). *)

From SymmetryBook Require Export
  Cats.S02_Categories
  Cats.S03_Duality
  Cats.S04_Functors
  Cats.S05_Adjunctions
  Cats.S06_Yoneda
  Cats.S07_Equivalences
  Cats.S08_Limits.
