"""
Setup script for attention_expert PyTorch extension

Builds and installs the C++/CUDA extension for attention with dynamic expert loading.
"""

from setuptools import setup, find_packages
from torch.utils.cpp_extension import BuildExtension, CUDAExtension
import os

# Get the directory containing this setup.py
root_dir = os.path.dirname(os.path.abspath(__file__))
src_dir = os.path.join(os.path.dirname(root_dir), 'src')

# Source files for main extension
attention_sources = [
    os.path.join(src_dir, 'pytorch', 'attention_pytorch.cpp'),
    os.path.join(src_dir, 'kernels', 'attention_fwd.cu'),
    os.path.join(src_dir, 'kernels', 'expert_fwd.cu'),
]

# Source files for NVMe loader extension
nvme_sources = [
    os.path.join(src_dir, 'pytorch', 'nvme_tensor_loader.cpp'),
]

# Include directories
include_dirs = [
    os.path.join(src_dir, 'common'),
    os.path.join(root_dir, '..', '..', '..', '00.cuda_custom_lib'),  # cuda_utils.h
]

# Compiler flags
extra_compile_args = {
    'cxx': ['-O3', '-std=c++20'],
    'nvcc': [
        '-O3',
        '--use_fast_math',
        '-std=c++20',
        '-gencode=arch=compute_75,code=sm_75',  # Turing
        '-gencode=arch=compute_80,code=sm_80',  # Ampere
        '-gencode=arch=compute_86,code=sm_86',  # Ampere (RTX 30xx)
        '-gencode=arch=compute_89,code=sm_89',  # Ada Lovelace (RTX 40xx)
        '-gencode=arch=compute_90,code=sm_90',  # Hopper
    ]
}

setup(
    name='attention_expert',
    version='0.1.0',
    author='CUDA Exercise Project',
    description='PyTorch extension for attention with dynamic expert loading from NVMe',
    long_description=open(os.path.join(root_dir, '..', 'README.md')).read(),
    long_description_content_type='text/markdown',
    packages=find_packages(),
    ext_modules=[
        # Main attention/expert extension
        CUDAExtension(
            name='attention_expert._C',
            sources=attention_sources,
            include_dirs=include_dirs,
            extra_compile_args=extra_compile_args,
        ),
        # NVMe tensor loader extension (C++ only, no CUDA)
        CUDAExtension(
            name='attention_expert._nvme_loader',
            sources=nvme_sources,
            include_dirs=include_dirs,
            extra_compile_args={'cxx': ['-O3', '-std=c++20']},
        ),
    ],
    cmdclass={
        'build_ext': BuildExtension
    },
    install_requires=[
        'torch>=2.0.0',
    ],
    python_requires='>=3.8',
    classifiers=[
        'Development Status :: 3 - Alpha',
        'Intended Audience :: Developers',
        'Intended Audience :: Science/Research',
        'License :: OSI Approved :: MIT License',
        'Programming Language :: Python :: 3',
        'Programming Language :: Python :: 3.8',
        'Programming Language :: Python :: 3.9',
        'Programming Language :: Python :: 3.10',
        'Programming Language :: Python :: 3.11',
        'Topic :: Scientific/Engineering :: Artificial Intelligence',
    ],
)
