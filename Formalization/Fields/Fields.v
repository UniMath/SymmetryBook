(** * Chapter 13 of [fields.tex]: Rings, fields and vector spaces

    ** Summary of this formalization

    Only Section 13.1 ([S01_Rings.v]) has been started: abstract and
    mixed rings (13.1.1, 13.1.2: [AbsRing], [MixRing], the integers as a
    mixed ring, and [USym R] of a mixed ring as an abstract ring), pointed
    homotopies, the functor [O] with [O = e ∘ Ω], the pointed equivalence
    [swap] ([con:swap-ptd-doms]), fields over abstract rings, and the
    questions [TBD1] and [TBD2] of Example [exa:allS1*-swap]: the 2-loop
    of a square of loops is bilinear, and swapping the arguments of a
    function of two variables inverts it, so [swap(m_k) = m_{-k}], also
    as an identification in [M] ([swap_m_k], with [swap] on [M] defined
    directly, [swapM]); the
    equivalence [M ≃ ℤ] of that example sends [m_k] to [k], and the
    w-outer reading of [m_k] is [γ^k] with [γ] that of [m_1], also as
    [m_1] precomposed with the degree [k] map, for all [k : ℤ]; and
    [M ≃ Σ_{h : S¹ × S¹ → S¹} (id = h(base,-))], sending [m_1] to the
    multiplication of [S¹] (with both components, [M_eqv_mult_m_sigma]), with [h_k(w,u) = h_1(w^k,u)] there
    ([h_k_sigma]).  The
    chapter is still in flux; the other results are not formalized
    yet.  It builds on Chapters 2 - 10
    ([FinGroups.FinGroups]).  Everything compiles with nothing
    admitted. *)

From SymmetryBook Require Export
  Fields.S01_Rings.
