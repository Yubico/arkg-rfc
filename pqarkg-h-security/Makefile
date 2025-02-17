all: pqarkg-h.pdf

auto:
	ls -1 | entr make pqarkg-h.pdf

force: clean all

clean:
	rm -f *.aux *.bbl *.bcf *.blg *.fdb_latexmk *.fls *.log *.out *.pdf *.run.xml

%.pdf: %.tex %.bib
	latexmk -pdf pqarkg-h
