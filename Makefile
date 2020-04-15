all: book.pdf TAGS
book.pdf:always; latexmk -pdf -quiet -halt-on-error book
see-errors:; latexmk -pdf -halt-on-error book
one-by-one:
	pdflatex book.tex
	biber book
	pdflatex book.tex
	pdflatex book.tex
always:
clean:; rm -f *.aux *.fdb_latexmk *.fls *.log *.out *.toc *.brf *.blg *.bbl *.bcf *.run.xml 
veryclean:clean; rm -f *.pdf

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
