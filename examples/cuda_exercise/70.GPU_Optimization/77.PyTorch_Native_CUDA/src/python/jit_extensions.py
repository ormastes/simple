"""
JIT compilation of native CUDA extensions using torch.utils.cpp_extension.load().

This module provides an alternative to ``pip install -e .`` by compiling the
CUDA kernels on-the-fly. The first call incurs a compilation delay; subsequent
calls reuse the cached binary.  This is convenient during development because
it avoids the setup.py build step.

Usage:
    from jit_extensions import get_ops
    ops = get_ops()
    C = ops.matmul(A, B)
"""

import os
from torch.utils.cpp_extension import load

# Paths relative to this file
_MODULE_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))

_SOURCES = [
    os.path.join(_MODULE_DIR, "cpp", "bindings.cpp"),
    os.path.join(_MODULE_DIR, "cuda", "matmul_cuda.cu"),
    os.path.join(_MODULE_DIR, "cuda", "backprop_cuda.cu"),
    os.path.join(_MODULE_DIR, "cuda", "attention_cuda.cu"),
]

_INCLUDE_DIRS = [
    os.path.join(_MODULE_DIR, "cuda"),
]

_cached_module = None


def get_ops():
    """Load (and cache) the JIT-compiled CUDA extension module.

    Returns:
        The compiled Python module with .matmul(), .linear_forward(),
        .linear_backward(), and .attention() functions.
    """
    global _cached_module
    if _cached_module is None:
        _cached_module = load(
            name="cuda_native_ops_jit",
            sources=_SOURCES,
            extra_include_paths=_INCLUDE_DIRS,
            extra_cuda_cflags=["-O3", "--use_fast_math"],
            extra_cflags=["-O3"],
            verbose=True,
        )
    return _cached_module
