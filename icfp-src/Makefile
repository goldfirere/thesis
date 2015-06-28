
all: src.pdf

%.pdf: %.tex
	latexmk -pdf $*

%.tex: %.lhs rae.fmt
	lhs2TeX --poly -o $@ $<
