main.pdf: main.tex extract.tex
	latexmk -pdf -interaction=nonstopmode $<

extract.tex: extract.py ../jml2why3.ml
	python3 $< > $@
