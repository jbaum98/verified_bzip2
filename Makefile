COQFLAGS := `cat _CoqProject`
COQC := coqc $(COQFLAGS)

all: RunLength.vo

clean:
	fd --no-ignore-vcs -e vo -e glob -x rm {}

RunLength.vo: Instances.vo NatEncode.vo VST/fcf/EqDec.vo
Instances.vo: VST/fcf/EqDec.vo VST/compcert/lib/Integers.vo
NatEncode.vo: VST/compcert/lib/Integers.vo


VST/%.vo: VST/%.v
	$(MAKE) -C VST COQFLAGS="$(COQFLAGS)" $(patsubst VST/%,%,$@)

%.vo: %.v
	$(COQC) $<
