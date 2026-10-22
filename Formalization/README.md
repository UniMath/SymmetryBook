This directory contains (experiments with) autoformalization.

Here are the instructions for Claude:

The LaTeX sources are at github.com/marcbezem/SymmetryBook/*-tex.
Use rocq with the Coq-HoTT library.
All formalization results should be uploaded to 
github.com/marcbezem/SymmetryBook/Formalization, where you are allowed to commit and push.
You are NOT allowed to commit and push to github.com/marcbezem/SymmetryBook/ 
any LaTeX sources, but you are allowed to propose changes to the local copy of these,
changes which I may or may not make myself, commit and push.
Always build on earlier results in github.com/marcbezem/SymmetryBook/Formalization.
Deviations from Book HoTT and the Coq-HoTT library include:
- path composition uses the same order as function composition
- pointing paths and fibers use y = f(x)

If a notion occurs definitionally in the Coq-Hott library, use it to define our notion,
such as: Definition book_name := library_name. Use book_name henceforth.
Include the summary that you write after each formalization run as a comment 
at the beginning of the .v file that you propose to commit and push.

File structure:
- Symmetry.v at the top documents the structure and exports all chapters;
  _CoqProject lists all files in dependency (= book) order.
- One directory per chapter (e.g. Circle/ for circle.tex), with a chapter
  file of the same name (Circle/Circle.v) that only re-exports its sections
  and starts with a summary of the whole chapter.
- One file per section, S<nn>_<Name>.v, with nn the book's section number.
  No file for overview sections, sections hidden in the book (\wip), or
  sections that are empty or still to be written.
- Each section file does Require Export of the previous section; the first
  section of a chapter exports the previous chapter file.
- Material the book repeats is formalized once, at its first occurrence;
  later sections refer to it.

Anchoring in the LaTeX source:
- The labels of the LaTeX source (\label{...}) are the anchor points of the
  formalization; see "Labels" below.
- The formalization of a labelled item (definition, lemma, exercise,
  example, remark, ...) is preceded by a comment naming the item and its
  label, e.g. (** Lemma [lem:ff-eso] ... *), and may consist of several
  Rocq items (auxiliary definitions and lemmas, variants).
- Items without a label are anchored by a comment that names them by the
  nearest label (e.g. "the exercise after [def:mu_E]") or by their content.
- Items follow the order of the LaTeX source.

Labels:
- Cite a label verbatim between square brackets, exactly as in
  \label{...} (without extra braces), so that one search finds both the
  .tex and the .v file. Never correct or normalize a label in a .v file,
  not even an odd one such as [lem:[]0-maps-to-X/G] or
  [exer:first examples].
- Every label gets an anchor in the .v files, for navigation, also
  labels of enumerate items, equations, footnotes and informal remarks.
  Exceptions are structural labels (of chapters, sections, figures,
  including section labels without a prefix) and labels in commented-out
  text or in hidden (\wip) parts.
- Put the anchor where the item is formalized: an item label of a lemma
  goes on the Rocq lemma for that part ((** Part [prop-utils-pi]. *)),
  a label of a component of a structure goes on the record field, and
  an equation label goes on the definition or lemma that realizes it.
- If nothing is formalized (footnote, informal remark, displayed
  diagram), the anchor is a short comment at the right place saying what
  the item is, marked "(informal)"; the summary need not list these.
- If a label in the book is wrong (e.g. swapped labels), propose the fix
  of the .tex file and show the diff first. After approval, fix the .tex
  file, check the \cref's to the label, update the anchors in the .v
  files, and commit both together. Until then, cite the label verbatim
  with a note at the anchor and a NOTE in the summary.
- The same holds for small errors in the book text (typos, stray
  punctuation): show the fix first, then fix the .tex file. 
- Before committing, check both directions: every cited [label] exists
  in the .tex sources, and every label of the formalized sections that
  is not exempt (see above) is cited in some .v file.

Contents of a section file:
- A header comment with the summary of the run: what is formalized (book
  labels and Rocq names), deviations from the text, NOTEs for the book
  text, and what is left out and why.
- A result that is left out is stated without proof at its anchor point,
  as Definition name_stmt : Type := ...; nothing is admitted. Results that
  cannot be stated formally (informal remarks, alternative proofs) are only
  listed in the summary.

Naming: use the book's names (from macros.tex). If a name clashes with an
earlier notion, add a suffix (e.g. isIsoC/IsoC for categories, since
isIso/Iso are the group isomorphisms).
