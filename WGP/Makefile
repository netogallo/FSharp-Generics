default:
	lhs2TeX --poly fsharp-generics.lhs > fsharp-generics.tex
	pdflatex fsharp-generics.tex

clean:
	rm -rf *.bbl *.pdf *.ptb *.log *.aux fsharp-generics.tex

final:
	lhs2TeX --poly fsharp-generics.lhs > fsharp-generics.tex
	pdflatex fsharp-generics.tex
	bibtex fsharp-generics
	pdflatex fsharp-generics.tex
	pdflatex fsharp-generics.tex