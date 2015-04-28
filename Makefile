OTT_FILES_BASE =
PAPER_BASE = thesis
OTT_PICKY = false
BIB_FILES_BASE = thesis
FMT_FILES_BASE = rae

OTT_FILES_FULL = $(OTT_FILES_BASE:%=ott/%.ott)
OTT_OUTPUT_BASE = tycls-ott
OTT_OUTPUT_FULL = # tex/$(OTT_OUTPUT_BASE).tex
BIB_FILES_FULL = $(BIB_FILES_BASE:%=tex/%.bib)
FMT_FILES_FULL = $(FMT_FILES_BASE:%=tex/%.fmt)
MNG_FILES_BASE = 
OTT_DUMP_BASE = ott
OTT_OPTS = -tex_show_meta false -tex_wrap false -picky_multiple_parses $(OTT_PICKY)
ALL_TEX_FILES = $(wildcard tex/*.tex) $(patsubst %.lhs,%.tex,$(wildcard tex/*.lhs)) $(patsubst %.tex.mng,%.tex,$(wildcard tex/*.tex.mng)) $(patsubst %.lhs.mng,%.tex,$(wildcard tex/*.lhs.mng))


PDF_DIR_MARKER = pdf/.dir_exists

default: thesis
all: default

thesis: pdf/$(PAPER_BASE).pdf
ott: pdf/$(OTT_DUMP_BASE).pdf

$(PDF_DIR_MARKER):
	mkdir pdf
	touch $(PDF_DIR_MARKER)

$(OTT_OUTPUT_FULL): $(OTT_FILES_FULL)
	ott $(OTT_OPTS) -o $@ $^

tex/$(PAPER_BASE).pdf: $(ALL_TEX_FILES)

tex/%.pdf: tex/%.tex $(OTT_OUTPUT_FULL) $(PDF_DIR_MARKER) $(BIB_FILES_FULL)
	latexmk -pdf -cd $<

pdf/%.pdf: tex/%.pdf
	cp tex/$*.pdf pdf/$*.pdf

tex/%: tex/%.mng $(OTT_FILES_FULL)
	ott $(OTT_OPTS) -tex_filter $< $@ $(OTT_FILES_FULL)

tex/%.tex: tex/%.lhs $(FMT_FILES_FULL)
	cd $(TEX_DIR); lhs2TeX --poly -o $*.tex $*.lhs

clean:
	rm -rf tex/*.{fdb_latexmk,fls,log,aux,bbl,blg,pdf,ptb}
	rm -rf $(OTT_OUTPUT_FULL)
	rm -rf $(patsubst %.lhs,%.tex,$(wildcard tex/*.lhs))
	rm -rf $(patsubst %.mng,%,$(wildcard tex/*.mng))
	rm -rf pdf

.PHONY: clean all ott default thesis
.SECONDARY: tex/$(PAPER_BASE).tex
