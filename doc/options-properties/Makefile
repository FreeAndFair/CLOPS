F:= optionsproperties

.PHONY:	build clean pdflatex

all:	build

build:	${F}.pdf

${F}.pdf ${F}.bbl: ${F}.tex ${F}.bib
	rubber -W all --pdf ${F}.tex

clean:
	rubber --clean --pdf ${F} && rm -rf ${F}

pdflatex: 
	pdflatex ${F}
bibtex: 
	bibtex ${F}
