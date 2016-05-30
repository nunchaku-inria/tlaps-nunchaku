
SRC=$(wildcard doc/*.adoc)
HTML=$(subst .adoc,.html,$(SRC))

all: $(HTML)

%.html: %.adoc
	asciidoc $<
