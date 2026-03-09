/**
 * @file pycuda_wrapper.py
 * @brief Python bindings for CPU Mixture of Experts
 *
 * @author Yoon, Jonghyun
 * @date 2025-10-25
 */

"""
PyCUDA wrapper for CPU Mixture of Experts (MoE)

This module provides Python bindings for CPU-based MoE
implementations, enabling easy integration with NumPy and ML workflows.
All expert weights use flat buffer layout for efficient ctypes interop.
"""

import ctypes
import numpy as np
from typing import Tuple, Optional
import os
import sys

# Load the compiled shared library
_lib_path = os.path.join(os.path.dirname(__file__), '..', '..', 'libcpu_experts.so')
if not os.path.exists(_lib_path):
    _lib_path = 'libcpu_experts.so'  # Try in current directory

try:
    _lib = ctypes.CDLL(_lib_path)
except OSError as e:
    print(f"Error loading library: {e}", file=sys.stderr)
    print(f"Searched path: {_lib_path}", file=sys.stderr)
    _lib = None

if _lib:
    # Define function signatures

    # cpu_topk_gating
    _lib.cpu_topk_gating.argtypes = [
        ctypes.POINTER(ctypes.c_int),    # expert_indices
        ctypes.POINTER(ctypes.c_float),  # expert_weights
        ctypes.POINTER(ctypes.c_float),  # gate_logits
        ctypes.c_int,                     # batch_size
        ctypes.c_int,                     # num_experts
        ctypes.c_int                      # top_k
    ]
    _lib.cpu_topk_gating.restype = None

    # cpu_expert_ffn
    _lib.cpu_expert_ffn.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # output
        ctypes.POINTER(ctypes.c_float),  # input
        ctypes.POINTER(ctypes.c_float),  # weights_1
        ctypes.POINTER(ctypes.c_float),  # bias_1
        ctypes.POINTER(ctypes.c_float),  # weights_2
        ctypes.POINTER(ctypes.c_float),  # bias_2
        ctypes.c_int,                     # batch_size
        ctypes.c_int,                     # d_model
        ctypes.c_int,                     # d_ff
        ctypes.c_int,                     # expert_idx
        ctypes.c_int                      # num_experts
    ]
    _lib.cpu_expert_ffn.restype = None

    # cpu_moe_forward
    _lib.cpu_moe_forward.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # output
        ctypes.POINTER(ctypes.c_float),  # input
        ctypes.POINTER(ctypes.c_float),  # gate_weights
        ctypes.POINTER(ctypes.c_float),  # expert_weights_1
        ctypes.POINTER(ctypes.c_float),  # expert_bias_1
        ctypes.POINTER(ctypes.c_float),  # expert_weights_2
        ctypes.POINTER(ctypes.c_float),  # expert_bias_2
        ctypes.c_int,                     # batch_size
        ctypes.c_int,                     # d_model
        ctypes.c_int,                     # d_ff
        ctypes.c_int,                     # num_experts
        ctypes.c_int                      # top_k
    ]
    _lib.cpu_moe_forward.restype = None

    # cpu_gelu
    _lib.cpu_gelu.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # output
        ctypes.POINTER(ctypes.c_float),  # input
        ctypes.c_int                      # n
    ]
    _lib.cpu_gelu.restype = None

    # cpu_moe_forward_parallel
    _lib.cpu_moe_forward_parallel.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # output
        ctypes.POINTER(ctypes.c_float),  # input
        ctypes.POINTER(ctypes.c_float),  # gate_weights
        ctypes.POINTER(ctypes.c_float),  # expert_weights_1
        ctypes.POINTER(ctypes.c_float),  # expert_bias_1
        ctypes.POINTER(ctypes.c_float),  # expert_weights_2
        ctypes.POINTER(ctypes.c_float),  # expert_bias_2
        ctypes.c_int,                     # batch_size
        ctypes.c_int,                     # d_model
        ctypes.c_int,                     # d_ff
        ctypes.c_int,                     # num_experts
        ctypes.c_int,                     # top_k
        ctypes.c_int                      # num_threads
    ]
    _lib.cpu_moe_forward_parallel.restype = None

    # cpu_moe_timed
    _lib.cpu_moe_timed.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # output
        ctypes.POINTER(ctypes.c_float),  # input
        ctypes.POINTER(ctypes.c_float),  # gate_weights
        ctypes.POINTER(ctypes.c_float),  # expert_weights_1
        ctypes.POINTER(ctypes.c_float),  # expert_bias_1
        ctypes.POINTER(ctypes.c_float),  # expert_weights_2
        ctypes.POINTER(ctypes.c_float),  # expert_bias_2
        ctypes.c_int,                     # batch_size
        ctypes.c_int,                     # d_model
        ctypes.c_int,                     # d_ff
        ctypes.c_int,                     # num_experts
        ctypes.c_int,                     # top_k
        ctypes.c_char_p                   # method
    ]
    _lib.cpu_moe_timed.restype = ctypes.c_float


def _float_ptr(arr):
    """Helper to get ctypes float pointer from numpy array"""
    return arr.ctypes.data_as(ctypes.POINTER(ctypes.c_float))


def _int_ptr(arr):
    """Helper to get ctypes int pointer from numpy array"""
    return arr.ctypes.data_as(ctypes.POINTER(ctypes.c_int))


class CPUMoE:
    """CPU Mixture of Experts with PyCUDA-compatible interface"""

    @staticmethod
    def topk_gating(gate_logits: np.ndarray, top_k: int) -> Tuple[np.ndarray, np.ndarray]:
        """
        Select top-k experts for each token via softmax + top-k selection.

        Args:
            gate_logits: [batch_size, num_experts], dtype=float32
            top_k: Number of experts to select per token

        Returns:
            expert_indices: [batch_size, top_k], dtype=int32
            expert_weights: [batch_size, top_k], dtype=float32 (normalized)

        Raises:
            RuntimeError: If library not loaded
            ValueError: If dtype is not float32 or dimensions are wrong
        """
        if _lib is None:
            raise RuntimeError("CPU Experts library not loaded")

        if gate_logits.dtype != np.float32:
            raise ValueError("gate_logits must be float32")

        if gate_logits.ndim != 2:
            raise ValueError("gate_logits must be 2D [batch_size, num_experts]")

        batch_size, num_experts = gate_logits.shape

        if top_k > num_experts:
            raise ValueError(f"top_k ({top_k}) > num_experts ({num_experts})")

        expert_indices = np.zeros((batch_size, top_k), dtype=np.int32)
        expert_weights = np.zeros((batch_size, top_k), dtype=np.float32)

        gate_logits_c = np.ascontiguousarray(gate_logits)

        _lib.cpu_topk_gating(
            _int_ptr(expert_indices),
            _float_ptr(expert_weights),
            _float_ptr(gate_logits_c),
            batch_size, num_experts, top_k
        )

        return expert_indices, expert_weights

    @staticmethod
    def expert_ffn(input: np.ndarray, W1: np.ndarray, b1: np.ndarray,
                   W2: np.ndarray, b2: np.ndarray,
                   expert_idx: int, num_experts: int) -> np.ndarray:
        """
        Single expert feed-forward network.

        Uses flat buffer layout: W1[num_experts, d_ff, d_model].
        The expert_idx selects the slice to use.

        Args:
            input: [batch_size, d_model], dtype=float32
            W1: [num_experts, d_ff, d_model] or [num_experts * d_ff * d_model], dtype=float32
            b1: [num_experts, d_ff] or [num_experts * d_ff], dtype=float32
            W2: [num_experts, d_model, d_ff] or [num_experts * d_model * d_ff], dtype=float32
            b2: [num_experts, d_model] or [num_experts * d_model], dtype=float32
            expert_idx: Which expert to use (0-indexed)
            num_experts: Total number of experts

        Returns:
            output: [batch_size, d_model], dtype=float32
        """
        if _lib is None:
            raise RuntimeError("CPU Experts library not loaded")

        if input.dtype != np.float32:
            raise ValueError("Input must be float32")

        if input.ndim != 2:
            raise ValueError("Input must be 2D [batch_size, d_model]")

        batch_size, d_model = input.shape

        # Flatten weight arrays for C function
        W1_flat = np.ascontiguousarray(W1.ravel())
        b1_flat = np.ascontiguousarray(b1.ravel())
        W2_flat = np.ascontiguousarray(W2.ravel())
        b2_flat = np.ascontiguousarray(b2.ravel())

        # Infer d_ff from W1 shape
        total_w1 = W1_flat.size
        d_ff = total_w1 // (num_experts * d_model)

        output = np.zeros((batch_size, d_model), dtype=np.float32)
        input_c = np.ascontiguousarray(input)

        _lib.cpu_expert_ffn(
            _float_ptr(output),
            _float_ptr(input_c),
            _float_ptr(W1_flat),
            _float_ptr(b1_flat),
            _float_ptr(W2_flat),
            _float_ptr(b2_flat),
            batch_size, d_model, d_ff, expert_idx, num_experts
        )

        return output

    @staticmethod
    def moe_forward(input: np.ndarray, gate_weights: np.ndarray,
                    W1: np.ndarray, b1: np.ndarray,
                    W2: np.ndarray, b2: np.ndarray,
                    top_k: int) -> np.ndarray:
        """
        Complete MoE forward pass: gate, route, compute, combine.

        Args:
            input: [batch_size, d_model], dtype=float32
            gate_weights: [num_experts, d_model], dtype=float32
            W1: [num_experts, d_ff, d_model], dtype=float32
            b1: [num_experts, d_ff], dtype=float32
            W2: [num_experts, d_model, d_ff], dtype=float32
            b2: [num_experts, d_model], dtype=float32
            top_k: Number of experts to activate per token

        Returns:
            output: [batch_size, d_model], dtype=float32
        """
        if _lib is None:
            raise RuntimeError("CPU Experts library not loaded")

        if input.dtype != np.float32:
            raise ValueError("Input must be float32")

        batch_size, d_model = input.shape
        num_experts = gate_weights.shape[0]

        # Flatten all weight arrays
        input_c = np.ascontiguousarray(input)
        gate_c = np.ascontiguousarray(gate_weights.ravel())
        W1_flat = np.ascontiguousarray(W1.ravel())
        b1_flat = np.ascontiguousarray(b1.ravel())
        W2_flat = np.ascontiguousarray(W2.ravel())
        b2_flat = np.ascontiguousarray(b2.ravel())

        # Infer d_ff
        d_ff = W1.size // (num_experts * d_model)

        output = np.zeros((batch_size, d_model), dtype=np.float32)

        _lib.cpu_moe_forward(
            _float_ptr(output),
            _float_ptr(input_c),
            _float_ptr(gate_c),
            _float_ptr(W1_flat),
            _float_ptr(b1_flat),
            _float_ptr(W2_flat),
            _float_ptr(b2_flat),
            batch_size, d_model, d_ff, num_experts, top_k
        )

        return output

    @staticmethod
    def gelu(input: np.ndarray) -> np.ndarray:
        """
        GELU activation function.

        Args:
            input: Input array, dtype=float32 (any shape)

        Returns:
            output: Same shape as input, dtype=float32
        """
        if _lib is None:
            raise RuntimeError("CPU Experts library not loaded")

        if input.dtype != np.float32:
            raise ValueError("Input must be float32")

        input_flat = np.ascontiguousarray(input.ravel())
        output_flat = np.zeros_like(input_flat)

        _lib.cpu_gelu(
            _float_ptr(output_flat),
            _float_ptr(input_flat),
            input_flat.size
        )

        return output_flat.reshape(input.shape)


def validate_against_numpy(input: np.ndarray, gate_weights: np.ndarray,
                           W1: np.ndarray, b1: np.ndarray,
                           W2: np.ndarray, b2: np.ndarray,
                           top_k: int) -> Tuple[bool, float]:
    """
    Validate CPU MoE output against a pure-NumPy reference implementation.

    Args:
        input: [batch_size, d_model]
        gate_weights: [num_experts, d_model]
        W1, b1, W2, b2: Expert weights (flat buffer layout)
        top_k: Number of experts per token

    Returns:
        (is_correct, max_error): Validation result and maximum absolute error
    """
    output_cpu = CPUMoE.moe_forward(input, gate_weights, W1, b1, W2, b2, top_k)

    # NumPy reference: compute gate logits
    batch_size, d_model = input.shape
    num_experts = gate_weights.shape[0]
    d_ff = W1.shape[1] if W1.ndim == 3 else W1.size // (num_experts * d_model)

    gate_logits = input @ gate_weights.T  # [batch_size, num_experts]

    # Softmax
    gate_logits_shifted = gate_logits - gate_logits.max(axis=1, keepdims=True)
    exp_logits = np.exp(gate_logits_shifted)
    probs = exp_logits / exp_logits.sum(axis=1, keepdims=True)

    # Top-k
    topk_indices = np.argsort(-probs, axis=1)[:, :top_k]

    output_ref = np.zeros_like(input)

    for b_idx in range(batch_size):
        topk_probs = probs[b_idx, topk_indices[b_idx]]
        topk_probs = topk_probs / topk_probs.sum()

        for k in range(top_k):
            eidx = topk_indices[b_idx, k]
            w = topk_probs[k]

            # Reshape weights for this expert
            w1_e = W1.reshape(num_experts, d_ff, d_model)[eidx]
            b1_e = b1.reshape(num_experts, d_ff)[eidx]
            w2_e = W2.reshape(num_experts, d_model, d_ff)[eidx]
            b2_e = b2.reshape(num_experts, d_model)[eidx]

            # FFN: GELU(x @ W1^T + b1) @ W2^T + b2
            hidden = input[b_idx] @ w1_e.T + b1_e
            # GELU
            hidden = 0.5 * hidden * (1.0 + np.tanh(
                0.7978845608 * (hidden + 0.044715 * hidden ** 3)))
            expert_out = hidden @ w2_e.T + b2_e

            output_ref[b_idx] += w * expert_out

    max_error = np.max(np.abs(output_cpu - output_ref))
    is_correct = max_error < 1e-3

    return is_correct, float(max_error)


def benchmark(batch_size: int, d_model: int, d_ff: int,
              num_experts: int, top_k: int,
              warmup: int = 3, runs: int = 10) -> Tuple[float, float]:
    """
    Benchmark MoE performance.

    Args:
        batch_size, d_model, d_ff: Model dimensions
        num_experts: Total number of experts
        top_k: Experts activated per token
        warmup, runs: Benchmark parameters

    Returns:
        (gflops, time_ms): Performance in GFLOPS and average time in ms
    """
    import time

    np.random.seed(42)
    input_data = np.random.randn(batch_size, d_model).astype(np.float32) * 0.01
    gate_weights = np.random.randn(num_experts, d_model).astype(np.float32) * 0.01
    W1 = np.random.randn(num_experts, d_ff, d_model).astype(np.float32) * 0.01
    b1 = np.random.randn(num_experts, d_ff).astype(np.float32) * 0.01
    W2 = np.random.randn(num_experts, d_model, d_ff).astype(np.float32) * 0.01
    b2 = np.random.randn(num_experts, d_model).astype(np.float32) * 0.01

    # Warmup
    for _ in range(warmup):
        _ = CPUMoE.moe_forward(input_data, gate_weights, W1, b1, W2, b2, top_k)

    # Benchmark
    times = []
    for _ in range(runs):
        start = time.perf_counter()
        _ = CPUMoE.moe_forward(input_data, gate_weights, W1, b1, W2, b2, top_k)
        end = time.perf_counter()
        times.append(end - start)

    avg_time = np.mean(times)

    # FLOPS calculation:
    # Gate: batch_size * num_experts * d_model (matmul)
    # Per expert FFN: 2 * (d_model * d_ff) per token (two linear layers)
    # Total per token: top_k * 2 * (d_model * d_ff + d_ff * d_model) = top_k * 4 * d_model * d_ff
    gate_flops = batch_size * num_experts * d_model * 2
    expert_flops = batch_size * top_k * 4 * d_model * d_ff
    total_flops = gate_flops + expert_flops
    gflops = (total_flops / avg_time) / 1e9

    return gflops, avg_time * 1000


if __name__ == "__main__":
    print("CPU MoE PyCUDA Wrapper")
    print("=" * 50)

    # Test correctness
    np.random.seed(42)
    batch_size = 16
    d_model = 64
    d_ff = 256
    num_experts = 4
    top_k = 2

    input_data = np.random.randn(batch_size, d_model).astype(np.float32) * 0.1
    gate_weights = np.random.randn(num_experts, d_model).astype(np.float32) * 0.1
    W1 = np.random.randn(num_experts, d_ff, d_model).astype(np.float32) * 0.1
    b1 = np.random.randn(num_experts, d_ff).astype(np.float32) * 0.1
    W2 = np.random.randn(num_experts, d_model, d_ff).astype(np.float32) * 0.1
    b2 = np.random.randn(num_experts, d_model).astype(np.float32) * 0.1

    is_correct, max_err = validate_against_numpy(
        input_data, gate_weights, W1, b1, W2, b2, top_k)
    status = "PASSED" if is_correct else "FAILED"
    print(f"MoE Validation: {status} (max_error={max_err:.2e})")

    # Test GELU
    x = np.array([-2.0, -1.0, 0.0, 1.0, 2.0], dtype=np.float32)
    gelu_out = CPUMoE.gelu(x)
    print(f"\nGELU test: {x} -> {gelu_out}")

    print()

    # Benchmark
    print("Performance Benchmark:")
    configs = [
        (32, 128, 512, 4, 1),
        (32, 128, 512, 4, 2),
        (32, 128, 512, 8, 2),
        (32, 256, 1024, 8, 2),
    ]

    for bs, dm, dff, ne, tk in configs:
        gflops, time_ms = benchmark(bs, dm, dff, ne, tk)
        print(f"  B={bs:3d}, D={dm:4d}, FF={dff:4d}, E={ne:2d}, K={tk}: "
              f"{gflops:6.2f} GFLOPS ({time_ms:7.2f} ms)")
