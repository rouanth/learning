CHAPTERS=Preliminaries Integers
BNAME=Book

REFDIR=.tmp/
CHREFS=$(addsuffix .tex, $(addprefix $(REFDIR), $(CHAPTERS)))

TEMPLDIR=templates/
HEADTEMPL=$(TEMPLDIR)head.tex
TAILTEMPL=$(TEMPLDIR)tail.tex

TMPDIR=.tmp/
TMPTEX=$(TMPDIR)$(BNAME).tex

RESPDF=$(BNAME).pdf
TMPPDF=$(TMPDIR)$(RESPDF)
TMPLOG=$(TMPDIR)$(BNAME).log
TMPAUX=$(TMPDIR)$(BNAME).aux

all: $(RESPDF)

$(REFDIR)%.tex: data/%/title data/%/*.tex
	printf '%s' '\section{'           > $@
	cat    '$<'                      >> $@
	printf '%s' '}\begin{enumerate}' >> $@
	for f in `ls data/$*/*.tex`; \
		do printf '%s' "\item \input{$$f}" >> $@; done
	printf '%s' '\end{enumerate}'    >> $@

$(TMPTEX): $(HEADTEMPL) $(CHREFS) $(TAILTEMPL)
	cat $^ > $@

$(TMPPDF): $(TMPTEX)
	pdflatex -output-directory $(TMPDIR) $<

$(RESPDF): $(TMPPDF)
	cp $< $@

clean:
	rm -f $(CHREFS) $(TMPAUX) $(TMPLOG) $(TMPPDF) $(RESPDF) $(TMPTEX)

.PHONY: all clean

