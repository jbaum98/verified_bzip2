COQFLAGS := `cat _CoqProject`
COQC := coqc $(COQFLAGS)

VFILES := RunLength Instances NatEncode Ord MergesortClass Prefix BurrowsWheeler

all: $(addsuffix .vo, $(VFILES))

clean:
	fd --no-ignore-vcs -e vo -e glob -x rm {}

RunLength.vo: Instances.vo NatEncode.vo SumboolIf.vo \
							VST/compcert/lib/Integers.vo \
							VST/compcert/lib/Coqlib.vo
Instances.vo: VST/msl/eq_dec.vo VST/compcert/lib/Integers.vo
NatEncode.vo: VST/compcert/lib/Integers.vo
Ord.vo: VST/compcert/lib/Integers.vo
MergesortClass.vo: Ord.vo
Prefix.vo: Ord.vo MergesortClass.vo
BurrowsWheeler.vo: Ord.vo Rot.vo Prefix.vo

VST/%.vo: VST/%.v
	$(MAKE) -C VST $(patsubst VST/%,%,$@)

%.vo: %.v
	$(COQC) $<
