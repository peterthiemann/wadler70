.PHONY: all snippets

AGDA_SOURCES = \
	LambdaSigmaExamples.agda \
	WeakeningExamples.agda \
	WeakeningComparison.agda \
	WeakeningEta.agda \
	STLC70.agda \
	STLC70Notation.agda \
	WeakeningToSTLC70.agda

all: wadler70.pdf

snippets: agda-generated.tex

agda-generated.tex: $(AGDA_SOURCES) runagdatex
	bash ./runagdatex

wadler70.pdf: wadler70.tex macros.tex agda-generated.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error wadler70.tex
