# Makefile for Simple scilib native backends
#
# Three shared libraries, all exporting the symbols declared in scilib_shim.h:
#   libspl_scilib_mock.so     — CPU-correct; no CUDA dependency (default backend)
#   libspl_scilib_cublas.so   — Real cuBLAS_64 BLAS on GPU
#   libspl_scilib_cusolver.so — Real cuSOLVER LAPACK on GPU
#
# Runtime selection: set SIMPLE_BLAS_BACKEND=mock|cublas|cusolver (default: mock)
#
# Usage:
#   make all        # build mock + cublas + cusolver (skips GPU targets if nvcc absent)
#   make mock       # build mock only (no CUDA required)
#   make cublas     # build cuBLAS backend (requires CUDA)
#   make cusolver   # build cuSOLVER backend (requires CUDA)
#   make clean      # remove build artifacts
#   make install    # copy *.so to $(DESTDIR)/lib/

CUDA_HOME ?= /usr/local/cuda-13.0
CUDA_INCLUDE = $(CUDA_HOME)/targets/x86_64-linux/include
CUDA_LIB     = $(CUDA_HOME)/targets/x86_64-linux/lib

CC      = gcc
CFLAGS  = -shared -fPIC -O2 -Wall -Wextra -I.
LDFLAGS =

DESTDIR ?= ../../../release/$(shell uname -m)-$(shell uname -s | tr A-Z a-z)

NVCC_BIN := $(shell command -v nvcc 2>/dev/null || echo "")

# -----------------------------------------------------------------------
.PHONY: all mock cublas cusolver clean install

all: mock
	@if [ -n "$(NVCC_BIN)" ]; then \
		$(MAKE) cublas cusolver; \
	else \
		echo "WARNING: nvcc not found — skipping cublas and cusolver targets"; \
	fi

# -----------------------------------------------------------------------
# mock — CPU-correct; requires no CUDA
mock: libspl_scilib_mock.so

libspl_scilib_mock.so: mock_shim.c scilib_shim.h
	$(CC) $(CFLAGS) -o $@ mock_shim.c $(LDFLAGS)

# -----------------------------------------------------------------------
# cublas — real cuBLAS_64 backend
cublas: _check_nvcc libspl_scilib_cublas.so

libspl_scilib_cublas.so: cublas_shim.c scilib_shim.h
	$(CC) $(CFLAGS) -I$(CUDA_INCLUDE) -o $@ cublas_shim.c \
	    -L$(CUDA_LIB) -lcublas -lcudart $(LDFLAGS)

# -----------------------------------------------------------------------
# cusolver — real cuSOLVER LAPACK backend
cusolver: _check_nvcc libspl_scilib_cusolver.so

libspl_scilib_cusolver.so: cusolver_shim.c scilib_shim.h
	$(CC) $(CFLAGS) -I$(CUDA_INCLUDE) -o $@ cusolver_shim.c \
	    -L$(CUDA_LIB) -lcusolver -lcublas -lcudart $(LDFLAGS)

# -----------------------------------------------------------------------
# pre-flight: abort if nvcc is not available
_check_nvcc:
	@if [ -z "$(NVCC_BIN)" ]; then \
		echo "ERROR: nvcc not found. Install CUDA toolkit or set CUDA_HOME."; \
		exit 1; \
	fi

# -----------------------------------------------------------------------
clean:
	rm -f *.so *.o

# -----------------------------------------------------------------------
install: all
	mkdir -p $(DESTDIR)/lib
	cp *.so $(DESTDIR)/lib/
