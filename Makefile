OTT_FILES_BASE =
PAPER_BASE = thesis
OTT_PICKY = false
BIB_FILES_BASE = thesis
FMT_FILES_BASE = rae
HS_FILES_BASE = ThesisPreamble

OTT_FILES_FULL = $(OTT_FILES_BASE:%=ott/%.ott)
OTT_OUTPUT_BASE = tycls-ott
OTT_OUTPUT_FULL = # aux/$(OTT_OUTPUT_BASE).tex
BIB_FILES_FULL = $(BIB_FILES_BASE:%=tex/%.bib)
FMT_FILES_FULL = $(FMT_FILES_BASE:%=tex/%.fmt)
MNG_FILES_BASE =
OTT_DUMP_BASE = ott
OTT_OPTS = -tex_show_meta false -tex_wrap false -picky_multiple_parses $(OTT_PICKY)
ALL_TEX_FILES = $(wildcard tex/*.tex) $(patsubst %.tex.mng,%.tex,$(wildcard tex/*.tex.mng))
ALL_LHS_FILES = $(filter-out tex/thesis.lhs,$(wildcard tex/*.lhs) $(patsubst %.lhs.mng,%.lhs,$(wildcard tex/*.lhs.mng)))

PDF_DIR_MARKER = pdf/.dir_exists
AUX_DIR_MARKER = aux/.dir_exists

default: thesis compile
all: default

compile: $(ALL_LHS_FILES:tex/%.lhs=aux/%.o)

thesis: pdf/$(PAPER_BASE).pdf
ott: pdf/$(OTT_DUMP_BASE).pdf

$(PDF_DIR_MARKER):
	mkdir pdf
	touch $@
$(AUX_DIR_MARKER):
	mkdir aux
	touch $@

$(OTT_OUTPUT_FULL): $(OTT_FILES_FULL)
	ott $(OTT_OPTS) -o $@ $^

aux/$(PAPER_BASE).tex: $(ALL_LHS_FILES:tex/%=aux/%)

aux/%.pdf: aux/%.tex $(OTT_OUTPUT_FULL) $(BIB_FILES_FULL:tex/%=aux/%) $(AUX_DIR_MARKER) $(ALL_TEX_FILES:tex/%=aux/%)
	latexmk -pdf -cd $<

aux/%: tex/% $(AUX_DIR_MARKER)
	cp $< $@

pdf/%.pdf: aux/%.pdf $(PDF_DIR_MARKER)
	cp aux/$*.pdf pdf/$*.pdf

tex/%: tex/%.mng $(OTT_FILES_FULL)
	ott $(OTT_OPTS) -tex_filter $< $@ $(OTT_FILES_FULL)

aux/%.tex: aux/%.lhs $(FMT_FILES_FULL:tex/%=aux/%)
	cd aux && lhs2TeX --poly -o $*.tex $*.lhs

aux/%.o: aux/%.hs $(HS_FILES_BASE:%=o/%.o)
	ghc -io -o $@ -c $<

o/%.o: hs/%.hs
	ghc -c $< -odir o -hidir o

aux/%.hs: aux/%.lhs $(FMT_FILES_FULL:tex/%=aux/%)
	cd aux && lhs2TeX --newcode -o $*.hs $*.lhs

clean:
	rm -rf $(OTT_OUTPUT_FULL)
	rm -rf $(patsubst %.lhs,%.tex,$(wildcard tex/*.lhs))
	rm -rf $(patsubst %.mng,%,$(wildcard tex/*.mng))
	rm -rf pdf
	rm -rf aux

.PHONY: clean all ott default thesis compile
.SECONDARY:
.SUFFIXES:
