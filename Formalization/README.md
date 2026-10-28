This directory contains (experiments with) autoformalization.

Here are the instructions for Claude:

The LaTeX sources are at github.com/UniMath/SymmetryBook/*.tex.
Use rocq with the Coq-HoTT library (Rocq 9.1.0 with Coq-HoTT 9.1;
see "Building" below).
All formalization results should be uploaded to 
github.com/UniMath/SymmetryBook/Formalization, where you are allowed to commit and 
push, directly to the master branch.
You are NOT allowed to commit or push to github.com/UniMath/SymmetryBook/ 
any LaTeX sources, but you are allowed to propose changes to the local copy of these,
changes which I may or may not make myself, commit and push.
Always build on earlier results in github.com/UniMath/SymmetryBook/Formalization.
Deviations from Book HoTT and the Coq-HoTT library include:
- path composition uses the same order as function composition
- pointing paths and fibers use y = f(x), e.g. f : (X,x) →* (Y,y) has
  pointing path y = f(x)

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
  later sections refer to it.  Chapters 1-7 are almost done; the later
  chapters are still in flux and may still duplicate material from the
  earlier ones (e.g. the pullback, now in cats.tex, of which an old copy
  is commented out in subgroups.tex).  Such duplication will be removed
  from the book: formalize at the first occurrence and ignore the copy.
  If a duplicate is not commented out, report it as a NOTE.

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
  of the .tex file, including the \cref's to the label(s).
  After I have committed and pushed the fix (or a variant thereof),
  update the anchors in the .v files. Until then, cite the label verbatim
  with a note at the anchor and a NOTE in the summary.
- The same holds for small errors in the book text (typos, stray
  punctuation): propose a fix of the .tex file. 
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

Working copies:
- Claude works in its own clone of UniMath/SymmetryBook (on a Mac:
  ~/git/SymmetryBook-Formalization); my own working copy (on a Mac:
  ~/git/SymmetryBook) is read-only for Claude. I work on several
  machines: pull before starting, push when done.

Proposals for the LaTeX sources:
- Write proposed .tex fixes to the directory proposals/ at the top of
  Claude's clone, which is NOT under git control (it is listed in
  .git/info/exclude; never git add it): a patch chN-chM.patch with the
  mechanical fixes, checked with git apply --check against my working
  copy, and a note chN-chM.md explaining each fix and listing the points
  that need a decision by the authors. N-M are the chapters the patch
  touches, e.g. ch3-ch3 for circle.tex only.
- After I have pushed a fix (or a variant of it), Claude updates the
  anchors and NOTEs in the .v files and deletes the proposal files
  that are settled.
- Claude may commit and push changes to Formalization/README.md, and
  leaves a note on each change in proposals/README-README.md.

Review before I commit:
- When I ask, review my uncommitted changes (git diff in my working
  copy) before I commit and push, plus pushed commits that Claude's clone
  lacks (I also edit on other machines and on GitHub). Check mathematical
  correctness, notation consistent with the surrounding text and
  macros.tex, typos in nearby lines, and labels that are anchored in the
  .v files. Report only; do not commit .tex changes. The aim is one
  reviewed push instead of many small ones, each of which runs CI.

Naming: use the book's names (from macros.tex). If a name clashes with an
earlier notion, add a suffix (e.g. isIsoC/IsoC for categories, since
isIso/Iso are the group isomorphisms).

Building:
- Requirements: Rocq 9.1.0 and Coq-HoTT 9.1 (opam packages
  rocq-core.9.1.0 and coq-hott.9.1, from the repository
  https://rocq-prover.org/opam/released).
- Build everything, in Formalization/, with rocq on the PATH:
    rocq makefile -f _CoqProject -o Makefile.rocq
    make -f Makefile.rocq -j
  The generated Makefile.rocq* files are not under git control.
- Build before committing; a commit must build without errors.
- Linux: opam 2.6.1 in ~/.local/bin (installed without sudo), switch
  rocq-9.1 with ocaml-base-compiler.4.14.2, rocq-core.9.1.0 and
  coq-hott.9.1; activate it with
    eval $(opam env --switch=rocq-9.1)
  The full build takes about 3 minutes.
- Mac (macOS 15, x86_64): opam 2.4.1 from Homebrew, switch default
  with ocaml-base-compiler.5.4.0 and rocq-core.9.1.0 (active by
  default); coq-hott is pinned to dev from a local clone
    opam pin coq-hott git+file:///Users/marc/git/Coq-HoTT#master
  (commit 5c938e4) rather than coq-hott.9.1. The full build (-j8)
  takes about 3.5 minutes, without errors or warnings.
