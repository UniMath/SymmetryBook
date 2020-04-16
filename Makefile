all: book.pdf TAGS
book.pdf: always figures
	latexmk -halt-on-error -quiet -pdf -pdflatex="pdflatex --shell-escape %O %S" book
see-errors: figures
	latexmk -halt-on-error -pdf -pdflatex="pdflatex --shell-escape %O %S" book
one-by-one: figures
	pdflatex --shell-escape book.tex
	biber book
	pdflatex --shell-escape book.tex
	pdflatex --shell-escape book.tex
figures:
	mkdir $@
clean:
	rm -f *.aux *.fdb_latexmk *.fls *.log *.out *.toc *.brf *.blg *.bbl *.bcf *.run.xml
veryclean:clean
	rm -rf *.pdf *.auxlock *.synctex.gz figures
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
