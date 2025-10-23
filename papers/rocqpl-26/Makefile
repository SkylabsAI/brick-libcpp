mutexes.pdf: mutexes.tex bibfile.bib
	pdflatex mutexes.tex
	bibtex mutexes
	pdflatex mutexes.tex
	pdflatex mutexes.tex

clean:
	rm mutexes.pdf
