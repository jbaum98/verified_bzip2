COQFLAGS := `cat _CoqProject`
COQC := coqc $(COQFLAGS)
COQDEP := coqdep $(COQFLAGS)

SRC := $(shell fd . -e v 'BWT')
OBJ := $(SRC:%.v=%.vo)
DEPS := $(SRC:%.v=%.d)

all: $(OBJ)

clean-local:
	fd -E VST --no-ignore-vcs -e vo -e glob -e d -x rm {}

clean:
	fd --no-ignore-vcs -e vo -e glob -e d -x rm {}

BWT/%.vo: BWT/%.v
	$(COQC) $<

BWT/%.d: BWT/%.v
	$(COQDEP) $< > $@

-include $(DEPS)
