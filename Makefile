C = motivation
C_EXT = $(if $(wildcard tex/$(C).lhs*),$(C).lhs,$(C).tex)

OTT_FILES_BASE = syn syn_hask syn_inf syn_oi syn_sb syn_suffix rules rules_inf
PAPER_BASE = thesis
OTT_PICKY = false
BIB_FILES_FULL = bib/rae.bib
FMT_FILES_BASE = rae
HS_FILES_BASE = ThesisPreamble DB # Pico/Ott Pico/Syn Pico/Util Pico/Rules
GHC_OPTS = -Werror -Wall -fprint-explicit-kinds -ieffects -dynamic-too
GHC = ghc-8

OTT_FILES_FULL = $(OTT_FILES_BASE:%=ott/%.ott)
OTT_OUTPUT_BASE = ottdefns
OTT_OUTPUT_FULL = aux/$(OTT_OUTPUT_BASE).tex
FMT_FILES_FULL = $(FMT_FILES_BASE:%=tex/%.fmt)
MNG_FILES_BASE =
OTT_DUMP_BASE = ottdump
OTT_OPTS = -tex_show_meta false -tex_wrap false -picky_multiple_parses $(OTT_PICKY)
COQ_OTT_OPTS = -coq_expand_list_types false
ALL_TEX_FILES = $(wildcard tex/*.tex) $(patsubst %.tex.mng,%.tex,$(wildcard tex/*.tex.mng))
ALL_LHS_FILES = $(filter-out tex/thesis.lhs tex/chapter.lhs,$(wildcard tex/*.lhs) $(patsubst %.lhs.mng,%.lhs,$(wildcard tex/*.lhs.mng)))

PDF_DIR_MARKER = pdf/.dir_exists
AUX_DIR_MARKER = aux/.dir_exists
O_DIR_MARKER = o/.dir_exists

BUILD_WITH_LHS = thesis chapter

default: thesis compile
all: default

compile: $(ALL_LHS_FILES:tex/%.lhs=aux/%.o)

thesis: pdf/$(PAPER_BASE).pdf
	@echo '**** THESIS BUILT ****'

chapter: pdf/chapter.pdf

ott: pdf/$(OTT_DUMP_BASE).pdf

$(PDF_DIR_MARKER):
	mkdir pdf
	touch $@
$(AUX_DIR_MARKER):
	mkdir aux
	touch $@
$(O_DIR_MARKER):
	mkdir o
	touch $@

$(OTT_OUTPUT_FULL): $(OTT_FILES_FULL)
	ott $(OTT_OPTS) -o $@ $^

aux/$(PAPER_BASE).tex: $(ALL_LHS_FILES:tex/%=aux/%)
aux/chapter.tex: aux/thechapter.lhs

aux/chapter.pdf: $(OTT_OUTPUT_FULL) aux/texpreamble.tex aux/thesispreamble.tex $(BIB_FILES_FULL)
aux/ottdump.pdf: $(OTT_OUTPUT_FULL) aux/texpreamble.tex
aux/thesis.pdf: $(OTT_OUTPUT_FULL) $(BIB_FILES_FULL) $(ALL_TEX_FILES:tex/%=aux/%)

ifneq ($(wildcard tex/$(C).lhs*),)
aux/thechapter.lhs: aux/$(C).lhs
	cp $< $@
else
aux/thechapter.lhs: aux/$(C).tex
	echo "\input{$(C)}" > $@
endif

aux/%.pdf: aux/%.tex $(AUX_DIR_MARKER)
	latexmk -pdf -cd $<

aux/%: tex/% $(AUX_DIR_MARKER)
	cp $< $@

pdf/%.pdf: aux/%.pdf $(PDF_DIR_MARKER)
	cp aux/$*.pdf pdf/$*.pdf

aux/%: aux/%.mng $(OTT_FILES_FULL)
	ott $(OTT_OPTS) -tex_filter $< $@ $(OTT_FILES_FULL)

aux/%.hs: aux/%.lhs.mng $(OTT_FILES_FULL) $(FMT_FILES_FULL:tex/%=aux/%)
	ott $(COQ_OTT_OPTS) -coq_filter aux/$*.lhs.mng aux/$*.temp.lhs $(OTT_FILES_FULL)
	cd aux && lhs2TeX --newcode -o $*.hs $*.temp.lhs
	perl -pi -e "s/TICK/\'/g" $@
	perl -pi -e "s/\'\\[\\]/[]/g" $@

# extra custom dependency
aux/motivation.lhs: aux/effects.lhs

$(BUILD_WITH_LHS:%=aux/%.tex): aux/%.tex: aux/%.lhs $(FMT_FILES_FULL:tex/%=aux/%)
	cd aux && lhs2TeX --poly -o $*.tex $*.lhs

# This builds the effects files
o/All.o: effects/*.hs effects/*/*.hs
	$(GHC) --make $(GHC_OPTS) -odir o -hidir o effects/All.hs

aux/%.o: aux/%.hs $(HS_FILES_BASE:%=o/%.o) o/All.o
	$(GHC) $(GHC_OPTS) -io -o $@ -c $<

o/%.o: hs/%.hs $(O_DIR_MARKER)
	$(GHC) $(GHC_OPTS) -c $< -odir o -hidir o

aux/%.hs: aux/%.lhs $(FMT_FILES_FULL:tex/%=aux/%)
	cd aux && lhs2TeX --newcode -o $*.hs $*.lhs
	perl -pi -e "s/TICK/\'/g" $@

clean:
	rm -rf $(OTT_OUTPUT_FULL)
	rm -rf $(patsubst tex/%.lhs,aux/%.tex,$(wildcard tex/*.lhs))
	rm -rf $(patsubst tex/%.mng,aux/%,$(wildcard tex/*.mng))
	rm -rf pdf
	rm -rf aux
	rm -rf o

.PHONY: clean all ott default thesis compile
.SECONDARY:
.SUFFIXES:
