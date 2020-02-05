all: book.pdf TAGS
book.pdf:always; latexmk -pdf book
always:
clean:; rm -f *.aux *.fdb_latexmk *.fls *.log *.out *.toc *.brf *.blg *.bbl
veryclean:clean; rm -f *.pdf
ZTors.pdf:always; latexmk -pdf ZTors

BOOKFILES :=						\
	book.tex					\
	top.tex						\
	macros.tex					\
	intro.tex					\
	intro-uf.tex					\
	circle.tex					\
	group.tex					\
	gerbes.tex					\
	symmetry.tex					\
	EuclideanGeometry.tex			

TAGS : Makefile *.tex
	etags $(BOOKFILES)
