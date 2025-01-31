all: pqarkg-h.pdf

auto:
	ls -1 | entr make pqarkg-h.pdf

force: clean all

clean:
	rm -f *.aux *.log *.out *.pdf

%.pdf: %.tex %.bib
	latexmk -pdf pqarkg-h
