COQC := coqc `cat _CoqProject`

all: RunLength.vo

clean:
	fd --no-ignore-vcs -e vo -e glob -x rm {}

RunLength.vo: VST/fcf/EqDec.vo

%.vo: %.v
	$(COQC) $<
