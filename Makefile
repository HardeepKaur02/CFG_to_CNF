FSTAR_HOME ?= /Users/hardeepkaur/COD492/FStar
DY_HOME ?= /Users/hardeepkaur/COL831

CACHE_DIR     ?= $(DY_HOME)/.cache/symbolic
HINT_DIR      ?= $(DY_HOME)/.hints/symbolic

.PHONY: all verify clean

all:
	rm -f .depend.symbolic && $(MAKE) .depend.symbolic

FSTAR_INCLUDE_DIRS = $(DY_HOME) $(DY_HOME)/symbolic

FSTAR_FLAGS = --cmi \
  --warn_error -331 \
  --cache_checked_modules --cache_dir $(CACHE_DIR) \
  --already_cached "+Prims+FStar+LowStar+C+Spec.Loops+TestLib" \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS) $(OTHERFLAGS)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints # --query_stats

ALL_SOURCES = $(wildcard *.fst) $(wildcard *.fsti)

ROOTS = $(filter-out $(FIXME),$(ALL_SOURCES))

.depend.symbolic: $(HINT_DIR) $(CACHE_DIR)
	$(info $(ROOTS))
	$(FSTAR) --cmi --dep full $(ROOTS) --extract '* -Prims -LowStar -FStar' > $@

include .depend.symbolic

$(HINT_DIR):
	mkdir -p $@

$(CACHE_DIR):
	mkdir -p $@

$(CACHE_DIR)/%.checked: | .depend.symbolic $(HINT_DIR) $(CACHE_DIR)
	$(FSTAR) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $*).hints

verify: $(addsuffix .checked, $(addprefix $(CACHE_DIR)/,$(ROOTS)))
