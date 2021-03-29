MAKE_COQ = Makefile.coq
# KNOWNTARGETS will not be passed along to $(MAKE_COQ)
KNOWNTARGETS := $(MAKE_COQ) clean
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
COQ_PROJECT = _CoqProject
KNOWNFILES := Makefile $(COQ_PROJECT)

.DEFAULT_GOAL := invoke-coqmakefile

$(MAKE_COQ): Makefile $(COQ_PROJECT)
	"$(COQBIN)"coq_makefile -f "$(COQ_PROJECT)" -o "$@"

clean:
	if test -e "$(MAKE_COQ)"; then "$(MAKE)" -f "$(MAKE_COQ)" cleanall; fi
	$(RM) "$(MAKE_COQ)" "$(MAKE_COQ)".conf

invoke-coqmakefile: $(MAKE_COQ)
	"$(MAKE)" --no-print-directory -f "$(MAKE_COQ)" $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile clean $(KNOWNFILES)

####################################################################
##                      Your targets here                         ##
####################################################################

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
