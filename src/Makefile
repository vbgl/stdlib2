.SUFFIXES: .v .vo

all: lock.vo

dep:
	coqdep *.v > dep

%.vo: %.v
	coqtop -noinit -R . Stdlib -compile $<

clean:
	$(RM) dep *.vo *.glob

-include dep
