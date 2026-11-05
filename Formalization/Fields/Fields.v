(** * Chapter 13 of [fields.tex]: Rings, fields and vector spaces

    ** Summary of this formalization

    Only Section 13.1 ([S01_Rings.v]) has been started, with the
    questions [TBD1] and [TBD2] of Example [exa:allS1*-swap]: the 2-loop
    of a square of loops is bilinear, and swapping the arguments of a
    function of two variables inverts it, so [swap(m_k) = m_{-k}]; the
    equivalence [M ≃ ℤ] of that example sends [m_k] to [k], and the
    w-outer reading of [m_k] is [γ^k] with [γ] that of [m_1], also as
    [m_1] precomposed with the degree [k] map, for all [k : ℤ].  The
    chapter is still in flux; the other results are not formalized
    yet.  It builds on Chapters 2 - 10
    ([FinGroups.FinGroups]).  Everything compiles with nothing
    admitted. *)

From SymmetryBook Require Export
  Fields.S01_Rings.
