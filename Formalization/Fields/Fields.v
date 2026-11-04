(** * Chapter 13 of [fields.tex]: Rings, fields and vector spaces

    ** Summary of this formalization

    Only Section 13.1 ([S01_Rings.v]) has been started, with the sign
    question [TBD2] of Example [exa:allS1*-swap]: swapping the arguments
    of a function of two variables inverts the 2-loop of a square of
    loops, so [swap(m_k) = m_{-k}].  The chapter is still in flux; the
    other results are not formalized yet.  It builds on Chapters 2 - 10
    ([FinGroups.FinGroups]).  Everything compiles with nothing
    admitted. *)

From SymmetryBook Require Export
  Fields.S01_Rings.
