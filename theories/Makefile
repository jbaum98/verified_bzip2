COQFLAGS := `cat _CoqProject`
COQC := coqc $(COQFLAGS)
COQDEP := coqdep $(COQFLAGS)

SRC := $(shell find BWT -iname "*.v")
OBJ := $(SRC:%.v=%.vo)
DEPS := $(SRC:%.v=%.d)

all: BWT/BurrowsWheeler.vo BWT/Sorting/RadixSort.v BWT/Sorting/StablePerm.v

BWT/%.vo: BWT/%.v
	$(COQC) $<

BWT/%.d: BWT/%.v
	$(COQDEP) $< > $@

-include $(DEPS)
