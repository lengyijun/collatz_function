all:
	pdflatex table.tex
	pdflatex table.tex

clean:
	rm -f table.aux  table.log  table.pdf

