all: book.pdf TAGS
book.pdf:always; latexmk -pdf -quiet book
always:
clean:; rm -f *.aux *.fdb_latexmk *.fls *.log *.out *.toc *.brf *.blg *.bbl *.bcf
veryclean:clean; rm -f *.pdf

BOOKFILES :=						\
	book.tex					\
	top.tex						\
	macros.tex					\
	intro.tex					\
	intro-uf.tex					\
	circle.tex					\
	group.tex					\
	subgroups.tex					\
	gerbes.tex					\
	symmetry.tex					\
	EuclideanGeometry.tex			

TAGS : Makefile *.tex
	etags $(BOOKFILES)
