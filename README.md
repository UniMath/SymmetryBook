# SymmetryBook
This book will be a textbook written in the univalent style, taking advantage of the presence of symmetry in the logic at an early stage.

## Style guide

- Try to be informal.  Use as few formulas as possible, especially for the parts about type theory and logic, to ease the entry into group theory.
- We call objects in a type *elements* of that type even if the type is not a set.
- An element of a proposition can be called a *proof*.
- Identity types are denoted in general using the macro \eqto, which produces ⥱ (that is an arrow with an = on top). An element of an identity type is called an *identification*, and otherwise a *path*. We may say that it shows how to *identify* two elements.
  If the type is a set, we may denote its identity types by a = b and call them *equations*. When a = b has an element we say that a and b are *equal*.
- Types similar to identity types, like the type of eqivalences from A to B, are also denoted with a macro ending in "to", like \equivto, producing ⥲ (that is an arrow with an equivalence sign on top).
- The type containing the variable in a family is called the "parameter type", not the "index type", nor the "base type".
- Being equal by definiton is denoted with three lines and is called just that, and not *definitionally equal* or *judgmentally equal*.
- A synonym of "function" is "map".  We don't use "mapping" or "application" as synonyms.
- In the preliminary chapters (up to subgroups), the underlying set map U from groups to sets has to be applied explicitly. Thereafter, it can be a coercion.
- Composition of p: a⥱b and q: b⥱c is denoted by either p∗q (p\ct q), or by q·p (q\cdot p), qp or q∘p (q\circ p). The latter is preferred when p and q come from equivalences.
- In dependent pairs, components having propositional type may be omitted.
- If x is a bound variable and c is less bound, then we prefer c ⥱ x to x ⥱ c. Typically, if c is the center of contraction.
- If k and n are number variables that can be renamed, then we prefer k < n to k > n or n < k.
- *up to* versus *modulo* regarding a group action: *Up to* is the stacky version, the orbit type (typically for us, a groupoid), whereas *modulo* refers to the set of connected components/the set of orbits. For example, given a group G, we have the groupoid of elements up to conjugation versus the set of elements modulo conjugation.
- Globally defined constants are typeset roman, while variables are italic. One exception is the *B* construction: The B matches whatever it operates on and joins to it without any space.
- When a structure is introduced and unpacked at the same time, use ≡ to connect the new variable with the unpacked parts. For example: “Let M ≡ (S,ι,μ) be a monoid”.
- Hints to exercises go in footnotes in the margin, with the footnote marker at the end of the exercise.
- Margin notes should usually to be made as footnotes (i.e., with a footnote marker).
- For a G-set X, we also write X for the underlying set, and we may write X^z to mean X twisted by a G-shape z : BG.
- Whenever possible, do not use a letter for a variable when the same letter is being used as an operator. E.g., try to avoid a variable B when the classifying type/map operator B is used in the same paragraph.
- Use macros with mathematical meaning, such as \conncomp, whenever possible, for uniformity of notation.
- Avoid the use of acronyms, such as LEM and LPO.
- Construct sort-order keys for glossary entries this way:
  + for unary operators, use 1 followed by something (e.g., for $-y$ use (1-);
  + for binary operators, use 2 followed by something (e.g., for $x+y$ use (2+);
  + for numbers, use 8 followed by the number (e.g., for $0$ use (80).
  + for identifiers in the Greek alphabet use 9 followed by the 2-digit ordinal number of the first letter (for proper alphabetization) and then something (e.g., for $\loops$ use (924Omega):
    ```
    01 Α α, 02 Β β, 03 Γ γ, 04 Δ δ, 05 Ε ε, 06 Ζ ζ, 07 Η η, 08 Θ θ, 09 Ι ι,
    10 Κ κ, 11 Λ λ, 12 Μ μ, 13 Ν ν, 14 Ξ ξ, 15 Ο ο, 16 Π π, 17 Ρ ρ, 18 Σ σ, 19 Τ τ,
    20 Υ υ, 21 Φ φ, 22 Χ χ, 23 Ψ ψ, and 24 Ω ω;
    ```
  + for identifiers in the Roman alphabet use the name (e.g., for $\Ker$ use (Ker) or (ker);
- Given a: A, we refer to elements of a ⥱ a as either symmetries *of* a, or symmetries *in* A.

## Current draft of the book (outdated since CI stopped)

Go [here for the current draft of the book](https://unimath.github.io/SymmetryBook/book.pdf).

## Compiling the book

To speed up compilation while writing the book, we cache the macros as a TeX format, and we externalize most of the figures,
so that they're only compiled once (or when necessary after changes to them).
This is managed with the Makefile, so just run `make`. The first run takes about 5–10 minutes, but subsequent compilations should finish in seconds.

## An icosahedron for your viewing pleasure

Go [here for an interactive icosahedron](https://unimath.github.io/SymmetryBook/icosahedron.html)
and [here for a Cayley diagram of the icosahedral group](https://unimath.github.io/SymmetryBook/icocayley.html).

Shield: [![CC BY-SA 4.0][cc-by-sa-shield]][cc-by-sa]

This work is licensed under a
[Creative Commons Attribution-ShareAlike 4.0 International License][cc-by-sa].

[![CC BY-SA 4.0][cc-by-sa-image]][cc-by-sa]

[cc-by-sa]: http://creativecommons.org/licenses/by-sa/4.0/
[cc-by-sa-image]: https://licensebuttons.net/l/by-sa/4.0/88x31.png
[cc-by-sa-shield]: https://img.shields.io/badge/License-CC%20BY--SA%204.0-lightgrey.svg
