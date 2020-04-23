
slides.pdf: slides.tex imap.pdf imap_partial.pdf
	latexmk -pdf slides

%.svg: %.plantuml
	plantuml -tsvg $<

%.pdf: %.svg
	inkscape -A $@ $<

