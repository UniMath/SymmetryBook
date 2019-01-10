# SymmetryBook
This book will be an undergraduate textbook written in the univalent style, taking advantage of the presence of symmetry in the logic at an early stage.

## Style guide

- Try to be informal.  Use as few formulas as possible, especially for the parts about type theory and logic, to ease the entry into group theory.
- We call objects in a type *elements* of that type even if the type is not a set.
- An element of a proposition can be called a *proof*.
- An element of an identity type is called an *identification*, not a *path*.
- Composition of p: a=b and q: b=c is denoted by either p\ct q, or by q\cdot q, qp or q\circ p. The latter is preferred when p and q come from equivalences. The macro \ct currently produces a star.
- In dependent pairs, components having propositional type may be omitted.
- If x is a bound variable and c is less bound, then we prefer c = x to x = c. Typically, if c is the center of contraction.
- If f: A -> B, then we prefer f(a)=b to b=f(a), even if a is a bound variable.
- If k and n are number variables that can be renamed, then we prefer k < n to k > n.

