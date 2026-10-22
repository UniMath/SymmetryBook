(** * Formalization of the book "Symmetry"

    Rocq with the Coq-HoTT library; the LaTeX sources are the files
    [*.tex] in the parent directory.  Build with [coqc -noinit
    -indices-matter] (see [_CoqProject]).

    ** Structure

    - [Symmetry.v] (this file) exports all chapters.
    - One directory per chapter, with a chapter file that exports its
      sections: [IntroUF/IntroUF.v] (Chapter 2, [intro-uf.tex]),
      [Circle/Circle.v] (Chapter 3, [circle.tex], Sections 3.1 - 3.10),
      [Group/Group.v] (Chapter 4, [group.tex], Sections 4.2 - 4.7) and
      [Actions/Actions.v] (Chapter 5, [actions.tex], Sections 5.2 - 5.7),
      [Cats/Cats.v] (Chapter 6, [cats.tex], Sections 6.2 - 6.8),
      [AbsGroup/AbsGroup.v] (Chapter 7, [absgroup.tex], Sections
      7.2 - 7.7) and [ConGroups/ConGroups.v] (Chapter 8, [congp.tex],
      Sections 8.2 - 8.4, 8.6, 8.7).
    - Results that are left out are stated without proof, as definitions
      of their statements (named [..._stmt]) at their proper place, and
      listed in the summary of their file.
    - One file per section, [S<nn>_<Name>.v], each starting with a summary
      of what is formalized, what differs from the text, and NOTEs for the
      book text.  Each section exports the previous one, and the first
      section of a chapter exports the previous chapter.

    ** Conventions

    The book deviates from Book HoTT and the Coq-HoTT library:
    1. Path composition is written in the order of function composition:
       for [p : a = b] and [q : b = c] we write [q ⋅ p :≡ trans p q], with
       [trans] defined by induction on [q] as in the book.
    2. Pointing paths and fibers use [y = f(x)]:
       [f⁻¹(y) :≡ ∑_x (y = f(x))].
    3. The book's [happly] is called [ptw], for dependent functions.

    When a notion occurs definitionally in Coq-HoTT, i.e. the library's
    definition satisfies the book's defining equations by definition, we
    define the book's notion from it ([Definition book_name :=
    library_name]) and use the book's name henceforth.  Constructors
    ([refl], [yes], [no], [triv]) are renamed by notations, so that they
    can still be used in patterns.  Where the book uses judgmental
    equality [≡], we check it by [refl]. *)

From SymmetryBook Require Export
  IntroUF.IntroUF
  Circle.Circle
  Group.Group
  Actions.Actions
  Cats.Cats
  AbsGroup.AbsGroup
  ConGroups.ConGroups.
