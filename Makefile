MK = latexmk

all: book.pdf TAGS
book.pdf: always figures version.tex macros.fmt
	$(MK) -quiet book
see-errors: figures version.tex macros.fmt
	$(MK) book
one-by-one: figures version.tex macros.fmt
	pdflatex -halt-on-error --shell-escape -fmt macros book.tex
	makeindex book.idx
	biber book
	pdflatex -halt-on-error --shell-escape -fmt macros book.tex
	makeindex book.idx
	pdflatex -halt-on-error --shell-escape -fmt macros book.tex
figures:
	mkdir $@
macros.fmt: macros.tex tikzsetup.tex
	pdflatex -ini -jobname="macros" "&pdflatex macros.tex\dump"
version.tex: .git/refs/heads/$(shell git branch --show-current)
	git log -1 --date=short \
    --pretty=format:'\newcommand{\OPTcommit}{%h}%n\newcommand{\OPTdate}{%ad}%n' \
    > version.tex
clean:
	rm -rf *.aux *.fdb_latexmk *.fls *.log *.out *.toc *.brf *.blg *.bbl *.bcf	\
		*.run.xml *.glo *.gls *.idx *.ilg *.ind					\
		*.auxlock *.synctex.gz TAGS version.tex macros.fmt
cleanall:
	rm -rf *.aux *.fdb_latexmk *.fls *.log *.out *.toc *.brf *.blg *.bbl *.bcf	\
		*.run.xml *.glo *.gls *.idx *.ilg *.ind					\
		book.pdf *.auxlock *.synctex.gz figures TAGS version.tex macros.fmt
always:

# This list should include all the tex files that go into the book, in the order they go.
# Compare with the \include commands in book.tex
BOOKFILES :=				\
	macros.tex				\
	tikzsetup.tex			\
	book.tex					\
	intro.tex					\
	intro-uf.tex			\
	circle.tex				\
	group.tex					\
	actions.tex				\
	absgroup.tex			\
	congp.tex					\
	subgroups.tex			\
	symmetry.tex			\
	fingp.tex					\
	fggroups.tex			\
	abelian.tex				\
	fields.tex				\
	geometry.tex			\
	galois.tex				\
	history.tex				\
	metamath.tex			\
	choicefin.tex

TAGS : Makefile $(BOOKFILES)
	etags $(BOOKFILES)
