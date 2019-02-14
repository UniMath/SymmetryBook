all: book.pdf
book.pdf:always; latexmk -pdf book
always:
clean:; rm -f *.aux *.fdb_latexmk *.fls *.log *.out *.toc
veryclean:clean; rm -f *.pdf
ZTors.pdf:always; latexmk -pdf ZTors
