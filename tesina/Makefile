MAIN = main

TEX_SRC = $(wildcard *.tex)
BIB_SRC = tesina.bib
IMG_SRC = $(wildcard img/*)

LATEXMK = latexmk -pdf -halt-on-error -interaction=nonstopmode

.PHONY: all clean distclean watch

all: $(MAIN).pdf

$(MAIN).pdf: $(TEX_SRC) $(BIB_SRC) $(IMG_SRC)
	$(LATEXMK) $(MAIN).tex

# inotifywait does not exist on macOS, use fswatch there.
ifeq ($(shell uname),Darwin)
WAIT = fswatch -1 $(TEX_SRC) $(BIB_SRC) img >/dev/null
else
WAIT = inotifywait -qre close_write .
endif

watch:
	while true; do		\
		clear;		\
		$(MAKE);	\
		$(WAIT) || exit 1; \
	done

clean:
	latexmk -c $(MAIN).tex

distclean:
	latexmk -C $(MAIN).tex
	rm -f $(MAIN).bbl $(MAIN).synctex.gz
