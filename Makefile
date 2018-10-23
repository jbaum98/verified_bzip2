COQFLAGS := `cat _CoqProject`
COQC := coqc $(COQFLAGS)

all: $(patsubst %.v,%.vo,$(wildcard *.v))

clean:
	fd --no-ignore-vcs -e vo -e glob -x rm {}

RunLength.vo: Instances.vo NatEncode.vo SumboolIf.vo \
							VST/compcert/lib/Integers.vo \
							VST/compcert/lib/Coqlib.vo
Instances.vo: VST/msl/eq_dec.vo VST/compcert/lib/Integers.vo
NatEncode.vo: VST/compcert/lib/Integers.vo

VST/%.vo: VST/%.v
	$(MAKE) -C VST $(patsubst VST/%,%,$@)

%.vo: %.v
	$(COQC) $<
