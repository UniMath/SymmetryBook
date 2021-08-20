MK = latexmk -halt-on-error -pdf -pdflatex="pdflatex -halt-on-error --shell-escape %O %S"

all: book.pdf TAGS
book.pdf: always figures version.tex
	$(MK) -quiet book
see-errors: figures version.tex
	$(MK) book
one-by-one: figures version.tex
	pdflatex -halt-on-error --shell-escape book.tex
	makeindex book.idx
	biber book
	pdflatex -halt-on-error --shell-escape book.tex
	makeindex book.idx
	pdflatex -halt-on-error --shell-escape book.tex
figures:
	mkdir $@
version.tex: .git/refs/heads/master
	printf '\\newcommand{\\OPTversion}{%s}\n' \
		"`git log -1 --pretty=format:'\texttt{%h} (%as)'`" > version.tex
clean:
	rm -rf *.aux *.fdb_latexmk *.fls *.log *.out *.toc *.brf *.blg *.bbl *.bcf	\
		*.run.xml *.glo *.gls *.idx *.ilg *.ind					\
		*.auxlock *.synctex.gz TAGS version.tex
cleanall:
	rm -rf *.aux *.fdb_latexmk *.fls *.log *.out *.toc *.brf *.blg *.bbl *.bcf	\
		*.run.xml *.glo *.gls *.idx *.ilg *.ind					\
		*.pdf *.auxlock *.synctex.gz figures TAGS version.tex
always:

# This list should include all the tex files that go into the book, in the order they go.
# Compare with the \include commands in book.tex
BOOKFILES :=						\
	macros.tex					\
	tikzsetup.tex					\
	book.tex					\
	intro.tex					\
	intro-uf.tex					\
	circle.tex					\
	group.tex					\
	subgroups.tex					\
	symmetry.tex					\
	fggroups.tex					\
	fingp.tex					\
	metamath.tex					\
	history.tex					\
	EuclideanGeometry.tex

TAGS : Makefile $(BOOKFILES)
	etags $(BOOKFILES)
