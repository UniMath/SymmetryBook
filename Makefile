MK = latexmk -halt-on-error -pdf -pdflatex="pdflatex -halt-on-error --shell-escape %O %S"

all: book.pdf TAGS
book.pdf: always figures
	$(MK) -quiet book
see-errors: figures
	$(MK) book
one-by-one: figures
	pdflatex -halt-on-error --shell-escape book.tex
	makeindex book.idx
	biber book
	pdflatex -halt-on-error --shell-escape book.tex
	makeindex book.idx
	pdflatex -halt-on-error --shell-escape book.tex
figures:
	mkdir $@
clean:
	rm -rf *.aux *.fdb_latexmk *.fls *.log *.out *.toc *.brf *.blg *.bbl *.bcf	\
		*.run.xml *.glo *.gls *.idx *.ilg *.ind					\
		*.auxlock *.synctex.gz TAGS
cleanall:
	rm -rf *.aux *.fdb_latexmk *.fls *.log *.out *.toc *.brf *.blg *.bbl *.bcf	\
		*.run.xml *.glo *.gls *.idx *.ilg *.ind					\
		*.pdf *.auxlock *.synctex.gz figures TAGS
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
	EuclideanGeometry.tex

TAGS : Makefile $(BOOKFILES)
	etags $(BOOKFILES)
