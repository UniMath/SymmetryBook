TEXOPTIONS = -halt-on-error -pdf -pdflatex="pdflatex --shell-escape %O %S"
MK = latexmk $(TEXOPTIONS)

all: book.pdf TAGS
book.pdf: always figures
	$(MK) -quiet book
see-errors: figures
	$(MK) book
one-by-one: figures
	pdflatex --shell-escape book.tex
	biber book
	pdflatex --shell-escape book.tex
	pdflatex --shell-escape book.tex
figures:
	mkdir $@
clean:
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
	gerbes.tex					\
	fingp.tex					\
	EuclideanGeometry.tex			

TAGS : Makefile $(BOOKFILES)
	etags $(BOOKFILES)
