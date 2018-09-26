COQC := coqc `cat _CoqProject`

all: RunLength.vo

RunLength.vo: VST/fcf/EqDec.vo

%.vo: %.v
	$(COQC) $<
