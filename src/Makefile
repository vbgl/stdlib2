.SUFFIXES: .v .vo

all: lock.vo

dep:
	coqdep *.v > dep

%.vo: %.v
	coqc -nois $*

clean:
	$(RM) dep *.vo *.glob

-include dep
