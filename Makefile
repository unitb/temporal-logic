
.PHONY: all clean lines profile

LEAN_OPT =
SRC = $(shell git ls-files | grep "\\.lean")
PROF = $(SRC:.lean=.lean.test_suite.out)

profile:
	leanpkg build -- --profile --test-suite

# %.prof.txt: %.lean
# %.lean.test_suite.out: %.lean
# 	lean $^ --profile --test-suite

all:
	leanpkg build

clean:
	/usr/bin/find . -name "*.olean" -delete
	/usr/bin/find . -name "*.lean.test_suite.out" -delete
	/usr/bin/find . -name "*.lean.status" -delete

lines:
	wc `git ls-files | grep .lean`
