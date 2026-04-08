ROOTS := $(wildcard *.fst)

FSTAR = fstar.exe $(SIL) $(FSTAR_FLAGS)
FSTAR_FLAGS += --cache_dir obj
FSTAR_FLAGS += --odir obj
FSTAR_FLAGS += --warn_error -274

KRML = krml -skip-compilation -skip-makefiles $(KSIL)

all: verify

obj/%.fst.checked: %.fst
	$(call msg,"CHECK",$<)
	$(FSTAR) -c $< -o $@

obj/%.krml: obj/%.fst.checked
	$(call msg,"EXTRACT",$<)
	$(FSTAR) --codegen krml --extract '*,-FStar.Reflection,-FStar.Tactics,-FStar.List' $< -o $@

%.c %.h &: MOD=$(subst _,.,$(basename $(notdir $<)))
%.c %.h &: obj/%.krml
	$(call msg,"KRML",$<)
	$(KRML) $< -bundle '$(MOD)=*'

.PHONY: clean
clean:
	rm -rf obj/
	rm -f .dep .dep.touch

.PHONY: .force
.dep.touch: .force
	mkdir -p $(dir $@)
	[ -e $@ ] || touch $@
	find . \( -name '*.fst' -o -name '*.fsti' \) -newer $@ -exec touch $@ \; -quit

.dep: .dep.touch
	$(call msg, "DEPEND", $(SRC))
	$(Q)$(FSTAR) --dep full $(ROOTS) --already_cached Prims,FStar,Pulse,PulseCore -o $@

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),echo-fstar)
include .dep
endif
endif

verify: $(ALL_CHECKED_FILES)

.PHONY: echo-fstar
echo-fstar:
	@echo $(FSTAR)

.DELETE_ON_ERROR:
.SECONDARY:
MAKEFLAGS += --no-builtin-rules
Q?=@
SIL?=--silent
KSIL?=-silent
RAMON=
ifneq ($(V),)
	Q=
	SIL=
	KSIL=
else
	MAKEFLAGS += -s
endif
define msg =
@printf "   %-14s  %s\n" $(1) $(2)
endef
