
.PHONY: all deep-clean clean lines profile

LEAN_OPT =
SRC = $(shell git ls-files | grep "\\.lean")
PROF = $(SRC:.lean=.lean.test_suite.out)

profile: $(PROF)

# %.prof.txt: %.lean
%.lean.test_suite.out: %.lean
	lean $^ --profile --test-suite

all:
	leanpkg build

clean:
	/usr/bin/find src test -name "*.olean" -delete
	/usr/bin/find src test -name "*.lean.test_suite.out" -delete
	/usr/bin/find src test -name "*.lean.status" -delete

deep-clean:
	/usr/bin/find . -name "*.olean" -delete
	/usr/bin/find . -name "*.lean.test_suite.out" -delete
	/usr/bin/find . -name "*.lean.status" -delete

lines:
	wc `git ls-files -x .lean`
