# test/perf/graphics_2d/c_reference/Makefile
# Build C reference benchmark. -O2 scalar, no auto-vectorize for fair comparison.

CC     ?= cc
CFLAGS  = -std=c11 -O2 -Wall -Wextra -o bench_2d bench_2d.c

.PHONY: all run clean
all: bench_2d
bench_2d: bench_2d.c
	$(CC) $(CFLAGS)
run: bench_2d
	./bench_2d
clean:
	rm -f bench_2d
