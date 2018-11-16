COQFLAGS := `cat _CoqProject`
COQC := coqc $(COQFLAGS)
COQDEP := coqdep $(COQFLAGS)

SRC := $(shell fd . -e v 'theories/BWT')
OBJ := $(SRC:%.v=%.vo)
DEPS := $(SRC:%.v=%.d)

all: $(OBJ)

clean-local:
	fd -E theories/VST --no-ignore-vcs -e vo -e glob -e d -x rm {}

clean:
	fd --no-ignore-vcs -e vo -e glob -e d -x rm {}

theories/VST/%.vo: theories/VST/%.v
	$(MAKE) -C theories/VST $(patsubst theories/VST/%,%,$@)

theories/BWT/%.vo: theories/BWT/%.v
	$(COQC) $<

theories/BWT/%.d: theories/BWT/%.v
	$(COQDEP) $< > $@

-include $(DEPS)
