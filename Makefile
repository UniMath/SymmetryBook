book.pdf:*.tex; latexmk -pdf book
clean:; rm -f *.aux *.fdb_latexmk *.fls *.log *.out *.toc
veryclean:clean; rm -f *.pdf
