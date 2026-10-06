# Rocq build: sources in theories/, artifacts in build/theories/.
#
# Rocq 9+: default `rocq c`. Coq 8.x: `make COQC=coqc COQCOMPILE='$(COQC)'`

COQC ?= rocq
COQCOMPILE ?= $(COQC) c

SRC := theories
BUILD := build/theories
COQFLAGS := -Q $(BUILD) Classifier

VFILES := \
  $(SRC)/Predicate.v \
  $(SRC)/Raw.v \
  $(SRC)/prefixgen/Extract.v \
  $(SRC)/prefixgen/Base.v \
  $(SRC)/prefixgen/Prefixgen.v \
  $(SRC)/pathgen/Base.v \
  $(SRC)/pathgen/Pathgen.v \
  $(SRC)/Theorems.v

VOFILES := $(patsubst $(SRC)/%.v,$(BUILD)/%.vo,$(VFILES))

.PHONY: all clean

all: $(VOFILES)

$(BUILD)/%.vo: $(SRC)/%.v
	@mkdir -p $(dir $@)
	$(COQCOMPILE) $(COQFLAGS) -o $@ $<

$(BUILD)/Raw.vo: $(BUILD)/Predicate.vo
$(BUILD)/prefixgen/Extract.vo: $(BUILD)/Predicate.vo $(BUILD)/Raw.vo
$(BUILD)/prefixgen/Base.vo: $(BUILD)/Predicate.vo $(BUILD)/Raw.vo
$(BUILD)/prefixgen/Prefixgen.vo: \
  $(BUILD)/Predicate.vo $(BUILD)/Raw.vo \
  $(BUILD)/prefixgen/Extract.vo $(BUILD)/prefixgen/Base.vo
$(BUILD)/pathgen/Base.vo: $(BUILD)/Predicate.vo
$(BUILD)/pathgen/Pathgen.vo: $(BUILD)/Predicate.vo $(BUILD)/pathgen/Base.vo
$(BUILD)/Theorems.vo: \
  $(BUILD)/Predicate.vo $(BUILD)/Raw.vo \
  $(BUILD)/prefixgen/Base.vo $(BUILD)/prefixgen/Prefixgen.vo \
  $(BUILD)/pathgen/Base.vo

clean:
	rm -rf build
	rm -f $(SRC)/*.vo $(SRC)/*.glob $(SRC)/*.vok $(SRC)/*.vos $(SRC)/.*.aux
	rm -f $(SRC)/prefixgen/*.vo $(SRC)/prefixgen/*.glob $(SRC)/prefixgen/*.vok \
	      $(SRC)/prefixgen/*.vos $(SRC)/prefixgen/.*.aux
	rm -f $(SRC)/pathgen/*.vo $(SRC)/pathgen/*.glob $(SRC)/pathgen/*.vok \
	      $(SRC)/pathgen/*.vos $(SRC)/pathgen/.*.aux
