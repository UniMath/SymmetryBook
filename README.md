# SymmetryBook
This book will be an undergraduate textbook written in the univalent style, taking advantage of the presence of symmetry in the logic at an early stage.

## Style guide

- Try to be informal.  Use as few formulas as possible, especially for the parts about type theory and logic, to ease the entry into group theory.
- We call objects in a type *elements* of that type even if the type is not a set.
- An element of a proposition can be called a *proof*.
- An element of an identity type is called an *identification*, and otherwise a *path*.
- Composition of p: a=b and q: b=c is denoted by either p\ct q, or by q\cdot p, qp or q\circ p. The latter is preferred when p and q come from equivalences. The macro \ct currently produces a star.
- In dependent pairs, components having propositional type may be omitted.
- If x is a bound variable and c is less bound, then we prefer c = x to x = c. Typically, if c is the center of contraction.
- If k and n are number variables that can be renamed, then we prefer k < n to k > n or n < k.
- *up to* versus *modulo* regarding a group action: *Up to* is the stacky version, the orbit type (typically for us, a groupoid), whereas *modulo* refers to the set of connected components/the set of orbits. For example, given a group G, we have the groupoid of elements up to conjugation versus the set of elements modulo conjugation.
- globally defined constants are typeset roman, while variables are italic. One exception is the *B* construction: The B matches whatever it operates on and joins to it without any space.
- Whenever possible, do not use a letter for a variable when the same letter is being used as an operator. E.g., try to avoid a variable B when the classifying type/map operator B is used in the same paragraph.
- Use macros with mathematical meaning, such as \conncomp, whenever possible, for uniformity of notation.
