# test/perf/graphics_2d/c_reference/Makefile
CC     ?= cc
CFLAGS  = -std=c11 -O2 -Wall -Wextra

.PHONY: all run clean
all: bench_2d bench_2d_cuda bench_2d_memset

bench_2d: bench_2d.c
	$(CC) $(CFLAGS) -o bench_2d bench_2d.c

bench_2d_cuda: bench_2d_cuda.c
	$(CC) $(CFLAGS) -o bench_2d_cuda bench_2d_cuda.c -ldl -lrt

bench_2d_memset: bench_2d_memset.c
	$(CC) $(CFLAGS) -o bench_2d_memset bench_2d_memset.c -ldl -lrt

bench_2d_metal: bench_2d_metal.m
	clang -O2 -fobjc-arc bench_2d_metal.m -framework Metal -framework Foundation -o bench_2d_metal

run: all
	./bench_2d
	./bench_2d_cuda
	./bench_2d_memset

clean:
	rm -f bench_2d bench_2d_cuda bench_2d_memset bench_2d_metal
