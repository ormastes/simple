"""
setup.py for building the cuda_native_ops PyTorch extension.

This uses torch.utils.cpp_extension.CUDAExtension to compile the CUDA kernels
and pybind11 bindings into a single Python extension module that can be imported
directly (import cuda_native_ops).

Usage:
    pip install -e .           # editable install
    python setup.py build_ext  # build without installing
"""

from setuptools import setup
from torch.utils.cpp_extension import BuildExtension, CUDAExtension

setup(
    name='cuda_native_ops',
    version='0.1.0',
    description='Native CUDA operations for PyTorch (matmul, linear backward, attention)',
    ext_modules=[
        CUDAExtension(
            name='cuda_native_ops',
            sources=[
                'src/cpp/bindings.cpp',
                'src/cuda/matmul_cuda.cu',
                'src/cuda/backprop_cuda.cu',
                'src/cuda/attention_cuda.cu',
            ],
            include_dirs=['src/cuda'],
            extra_compile_args={
                'cxx': ['-O3'],
                'nvcc': ['-O3', '--use_fast_math'],
            },
        )
    ],
    cmdclass={'build_ext': BuildExtension},
    python_requires='>=3.8',
)
