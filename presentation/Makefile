
slides.pdf: slides.tex imap.pdf imap_partial.pdf heap/overlay.tex
	latexmk -pdf slides

%.svg: %.plantuml
	plantuml -tsvg $<

%.pdf: %.svg
	inkscape -A $@ $<

heap/overlay.tex: heap.svg
	./export_overlays $<
