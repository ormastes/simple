# test/perf/graphics_2d/c_reference/Makefile
CC     ?= cc
CFLAGS  = -std=c11 -O2 -Wall -Wextra

# Metal target uses clang directly (ObjC ARC; not compatible with -std=c11)
METAL_FLAGS = -O2 -fobjc-arc -Wall -Wextra

.PHONY: all run clean
all: bench_2d bench_2d_cuda bench_2d_memset bench_2d_metal

bench_2d: bench_2d.c
	$(CC) $(CFLAGS) -o bench_2d bench_2d.c

bench_2d_cuda: bench_2d_cuda.c
	$(CC) $(CFLAGS) -o bench_2d_cuda bench_2d_cuda.c -ldl -lrt

bench_2d_memset: bench_2d_memset.c
	$(CC) $(CFLAGS) -o bench_2d_memset bench_2d_memset.c -ldl -lrt

bench_2d_metal: bench_2d_metal.m
	clang $(METAL_FLAGS) -o bench_2d_metal bench_2d_metal.m \
		-framework Metal -framework Foundation

run: all
	./bench_2d
	./bench_2d_cuda
	./bench_2d_memset

run_metal: bench_2d_metal
	./bench_2d_metal

clean:
	rm -f bench_2d bench_2d_cuda bench_2d_memset bench_2d_metal
