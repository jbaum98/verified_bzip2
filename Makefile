COQFLAGS := `cat _CoqProject`
COQC := coqc $(COQFLAGS)

VFILES := RunLength Instances NatEncode Ord MergesortClass Prefix BurrowsWheeler

all: $(addsuffix .vo, $(VFILES))

clean-local:
	fd -E VST --no-ignore-vcs -e vo -e glob -x rm {}

clean:
	fd --no-ignore-vcs -e vo -e glob -x rm {}

RunLength.vo: Instances.vo NatEncode.vo SumboolIf.vo \
							VST/compcert/lib/Integers.vo \
							VST/compcert/lib/Coqlib.vo
Instances.vo: VST/msl/eq_dec.vo VST/compcert/lib/Integers.vo
NatEncode.vo: VST/compcert/lib/Integers.vo
Ord.vo: VST/compcert/lib/Integers.vo Instances.vo
MergesortClass.vo: Ord.vo
Prefix.vo: Ord.vo MergesortClass.vo
BurrowsWheeler.vo: Ord.vo Rotation.vo Prefix.vo Rots.vo
Rotation.vo: Repeat.vo BWTactics.vo
Iterate.vo: Repeat.vo
Rots.vo: Iterate.vo Rotation.vo Repeat.vo
Repeat.vo: BWTactics.vo

VST/%.vo: VST/%.v
	$(MAKE) -C VST $(patsubst VST/%,%,$@)

%.vo: %.v
	$(COQC) $<
