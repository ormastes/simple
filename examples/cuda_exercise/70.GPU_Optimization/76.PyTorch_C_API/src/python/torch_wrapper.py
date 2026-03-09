"""
PyTorch wrapper for custom CUDA operations via ctypes C API.

This module loads the shared library (libtorch_cuda_ops.so) built from the
C API sources and exposes the CUDA kernels as torch.autograd.Function classes.
Each Function handles:
  - Converting torch.Tensor to raw device pointers via .data_ptr()
  - Building TorchTensorDesc structs for the C boundary
  - Calling the C API function and checking the return status
  - Saving tensors for the backward pass where needed
"""

import ctypes
import os
import torch
import torch.autograd

# ---- ctypes struct definitions matching torch_api.h ----

class TorchTensorDesc(ctypes.Structure):
    """Mirror of the C TorchTensorDesc struct."""
    _fields_ = [
        ("data", ctypes.c_void_p),
        ("shape", ctypes.POINTER(ctypes.c_int64)),
        ("ndim", ctypes.c_int),
        ("numel", ctypes.c_int64),
    ]


def _make_desc(tensor: torch.Tensor) -> TorchTensorDesc:
    """Build a TorchTensorDesc from a contiguous CUDA tensor."""
    assert tensor.is_cuda, "Tensor must be on CUDA device"
    assert tensor.is_contiguous(), "Tensor must be contiguous"

    desc = TorchTensorDesc()
    desc.data = ctypes.c_void_p(tensor.data_ptr())
    shape_arr = (ctypes.c_int64 * tensor.ndim)(*tensor.shape)
    desc.shape = ctypes.cast(shape_arr, ctypes.POINTER(ctypes.c_int64))
    desc.ndim = tensor.ndim
    desc.numel = tensor.numel()
    # Keep shape array alive
    desc._shape_arr = shape_arr
    return desc


def _check_status(status: int, func_name: str) -> None:
    """Raise RuntimeError if a C API call returned a non-zero status."""
    messages = {
        0: "success",
        1: "invalid argument",
        2: "CUDA error",
        3: "out of memory",
    }
    if status != 0:
        msg = messages.get(status, f"unknown error {status}")
        raise RuntimeError(f"{func_name} failed: {msg}")


def _load_library() -> ctypes.CDLL:
    """Load the shared library, searching common build paths."""
    candidates = [
        os.path.join(os.path.dirname(__file__), "..", "..", "build", "libtorch_cuda_ops.so"),
        os.path.join(os.path.dirname(__file__), "libtorch_cuda_ops.so"),
        "libtorch_cuda_ops.so",
    ]
    for path in candidates:
        full = os.path.abspath(path)
        if os.path.isfile(full):
            return ctypes.CDLL(full)
    raise FileNotFoundError(
        "Cannot find libtorch_cuda_ops.so. Build the project first."
    )


# Global library handle (lazy-loaded)
_lib = None


def _get_lib() -> ctypes.CDLL:
    global _lib
    if _lib is None:
        _lib = _load_library()
    return _lib


# ---- torch.autograd.Function wrappers ----

class CUDAMatMul(torch.autograd.Function):
    """Custom matmul backed by the tiled CUDA kernel via C API."""

    @staticmethod
    def forward(ctx, A: torch.Tensor, B: torch.Tensor) -> torch.Tensor:
        """Compute C = A @ B using the custom CUDA kernel.

        Args:
            A: Left matrix [M x K], float32, CUDA
            B: Right matrix [K x N], float32, CUDA
        Returns:
            C: Result matrix [M x N]
        """
        ctx.save_for_backward(A, B)
        M, K = A.shape
        N = B.shape[1]
        C = torch.empty(M, N, device=A.device, dtype=torch.float32)

        a_desc = _make_desc(A)
        b_desc = _make_desc(B)
        c_desc = _make_desc(C)

        lib = _get_lib()
        status = lib.torch_matmul(
            ctypes.byref(c_desc), ctypes.byref(a_desc), ctypes.byref(b_desc)
        )
        _check_status(status, "torch_matmul")
        return C

    @staticmethod
    def backward(ctx, grad_output: torch.Tensor):
        """Compute gradients for A and B using standard matmul rules."""
        A, B = ctx.saved_tensors
        grad_A = grad_output @ B.T
        grad_B = A.T @ grad_output
        return grad_A, grad_B


class CUDALinear(torch.autograd.Function):
    """Custom linear layer forward/backward via C API."""

    @staticmethod
    def forward(ctx, input: torch.Tensor, weight: torch.Tensor,
                bias: torch.Tensor = None) -> torch.Tensor:
        """Forward: output = input @ weight^T + bias."""
        ctx.save_for_backward(input, weight, bias)
        batch, in_f = input.shape
        out_f = weight.shape[0]
        output = torch.empty(batch, out_f, device=input.device, dtype=torch.float32)

        in_desc = _make_desc(input)
        w_desc = _make_desc(weight)
        out_desc = _make_desc(output)

        lib = _get_lib()
        if bias is not None:
            b_desc = _make_desc(bias.contiguous())
            status = lib.torch_linear_forward(
                ctypes.byref(out_desc), ctypes.byref(in_desc),
                ctypes.byref(w_desc), ctypes.byref(b_desc)
            )
        else:
            status = lib.torch_linear_forward(
                ctypes.byref(out_desc), ctypes.byref(in_desc),
                ctypes.byref(w_desc), None
            )
        _check_status(status, "torch_linear_forward")
        return output

    @staticmethod
    def backward(ctx, grad_output: torch.Tensor):
        """Backward: compute grad_input, grad_weight, grad_bias."""
        input, weight, bias = ctx.saved_tensors
        batch, in_f = input.shape
        out_f = weight.shape[0]

        grad_input = torch.empty_like(input)
        grad_weight = torch.empty_like(weight)

        gi_desc = _make_desc(grad_input)
        gw_desc = _make_desc(grad_weight)
        go_desc = _make_desc(grad_output.contiguous())
        in_desc = _make_desc(input)
        w_desc = _make_desc(weight)

        lib = _get_lib()
        if bias is not None:
            grad_bias = torch.empty_like(bias)
            gb_desc = _make_desc(grad_bias)
            status = lib.torch_linear_backward(
                ctypes.byref(gi_desc), ctypes.byref(gw_desc), ctypes.byref(gb_desc),
                ctypes.byref(go_desc), ctypes.byref(in_desc), ctypes.byref(w_desc)
            )
            _check_status(status, "torch_linear_backward")
            return grad_input, grad_weight, grad_bias
        else:
            status = lib.torch_linear_backward(
                ctypes.byref(gi_desc), ctypes.byref(gw_desc), None,
                ctypes.byref(go_desc), ctypes.byref(in_desc), ctypes.byref(w_desc)
            )
            _check_status(status, "torch_linear_backward")
            return grad_input, grad_weight, None


class CUDAScaledDotProductAttention(torch.autograd.Function):
    """Custom scaled dot-product attention via C API."""

    @staticmethod
    def forward(ctx, Q: torch.Tensor, K: torch.Tensor, V: torch.Tensor,
                causal: bool = False) -> torch.Tensor:
        """Forward: output = softmax(Q @ K^T / sqrt(d_k)) @ V."""
        ctx.save_for_backward(Q, K, V)
        ctx.causal = causal

        seq_len, head_dim = Q.shape[-2], Q.shape[-1]
        output = torch.empty_like(Q)

        q_desc = _make_desc(Q.contiguous())
        k_desc = _make_desc(K.contiguous())
        v_desc = _make_desc(V.contiguous())
        o_desc = _make_desc(output)

        lib = _get_lib()
        status = lib.torch_scaled_dot_product_attention(
            ctypes.byref(o_desc), ctypes.byref(q_desc),
            ctypes.byref(k_desc), ctypes.byref(v_desc),
            ctypes.c_int(1 if causal else 0)
        )
        _check_status(status, "torch_scaled_dot_product_attention")
        return output

    @staticmethod
    def backward(ctx, grad_output: torch.Tensor):
        """Backward pass (falls back to PyTorch autograd for simplicity)."""
        Q, K, V = ctx.saved_tensors
        # Recompute attention weights for backward
        d_k = Q.shape[-1]
        scores = torch.matmul(Q, K.transpose(-2, -1)) / (d_k ** 0.5)
        if ctx.causal:
            mask = torch.triu(torch.ones_like(scores), diagonal=1).bool()
            scores.masked_fill_(mask, float('-inf'))
        attn = torch.softmax(scores, dim=-1)

        grad_V = attn.transpose(-2, -1) @ grad_output
        grad_attn = grad_output @ V.transpose(-2, -1)

        # Softmax backward
        grad_scores = attn * (grad_attn - (grad_attn * attn).sum(dim=-1, keepdim=True))
        grad_scores /= (d_k ** 0.5)

        grad_Q = grad_scores @ K
        grad_K = grad_scores.transpose(-2, -1) @ Q

        return grad_Q, grad_K, grad_V, None


# ---- Convenience functions ----

def cuda_matmul(A: torch.Tensor, B: torch.Tensor) -> torch.Tensor:
    """Compute A @ B using the custom CUDA kernel."""
    return CUDAMatMul.apply(A, B)


def cuda_linear(input: torch.Tensor, weight: torch.Tensor,
                bias: torch.Tensor = None) -> torch.Tensor:
    """Linear layer: output = input @ weight^T + bias."""
    return CUDALinear.apply(input, weight, bias)


def cuda_sdpa(Q: torch.Tensor, K: torch.Tensor, V: torch.Tensor,
              causal: bool = False) -> torch.Tensor:
    """Scaled dot-product attention."""
    return CUDAScaledDotProductAttention.apply(Q, K, V, causal)
