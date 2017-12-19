
.PHONY: all clean lines

LEAN_OPT =

all:
	leanpkg build

clean:
	/usr/bin/find . -name "*.olean" -delete

lines:
	wc `git ls-files | grep .lean`
