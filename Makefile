COQFLAGS := `cat _CoqProject`
COQC := coqc $(COQFLAGS)

VFILES := RunLength Instances NatEncode Ord Mergesort Prefix BurrowsWheeler Sorted \
					Rotation Iterate

all: $(addsuffix .vo, $(VFILES))

clean-local:
	fd -E VST --no-ignore-vcs -e vo -e glob -x rm {}

clean:
	fd --no-ignore-vcs -e vo -e glob -x rm {}

RunLength.vo: Instances.vo NatEncode.vo SumboolIf.vo \
							VST/compcert/lib/Integers.vo \
							VST/compcert/lib/Coqlib.vo
Instances.vo: VST/msl/eq_dec.vo VST/compcert/lib/Integers.vo Ord.vo
NatEncode.vo: VST/compcert/lib/Integers.vo
Ord.vo: VST/compcert/lib/Integers.vo
Mergesort.vo: Ord.vo Sorted.vo
Prefix.vo: Ord.vo Mergesort.vo
BurrowsWheeler.vo: Ord.vo Rotation.vo Prefix.vo Rots.vo
Rotation.vo: Repeat.vo BWTactics.vo Pointfree.vo
Iterate.vo: Repeat.vo Pointfree.vo
Rots.vo: Iterate.vo Rotation.vo Repeat.vo
Repeat.vo: BWTactics.vo Pointfree.vo
Sorted.vo: Ord.vo
Pointfree.vo: BWTactics.vo Lib.vo

VST/%.vo: VST/%.v
	$(MAKE) -C VST $(patsubst VST/%,%,$@)

%.vo: %.v
	$(COQC) $<
