all: talk.pdf


%.pdf: %.tex
	pdflatex $<
	pdflatex $<


clean:
	rm -f *~ *.aux *.log *.nav *.out *.snm *.toc
