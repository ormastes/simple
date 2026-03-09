"""
PyTorch operator wrappers using the native CUDA extension (cuda_native_ops).

Each class inherits from torch.autograd.Function and delegates forward/backward
to the compiled C++/CUDA extension loaded via ``import cuda_native_ops``.  These
wrappers are the user-facing API and can be used as drop-in replacements for the
equivalent PyTorch built-in operations.
"""

import torch
import torch.autograd


def _get_ops():
    """Lazy import of the compiled extension module."""
    import cuda_native_ops
    return cuda_native_ops


class NativeMatMul(torch.autograd.Function):
    """Matrix multiplication backed by the native CUDA kernel."""

    @staticmethod
    def forward(ctx, A: torch.Tensor, B: torch.Tensor) -> torch.Tensor:
        """Compute C = A @ B using the native tiled CUDA kernel.

        Args:
            A: Left matrix [M x K], float32, CUDA.
            B: Right matrix [K x N], float32, CUDA.
        Returns:
            C: Result [M x N].
        """
        ctx.save_for_backward(A, B)
        ops = _get_ops()
        return ops.matmul(A.contiguous(), B.contiguous())

    @staticmethod
    def backward(ctx, grad_output: torch.Tensor):
        """Standard matmul backward: dA = dC @ B^T, dB = A^T @ dC."""
        A, B = ctx.saved_tensors
        ops = _get_ops()
        grad_A = ops.matmul(grad_output.contiguous(), B.t().contiguous())
        grad_B = ops.matmul(A.t().contiguous(), grad_output.contiguous())
        return grad_A, grad_B


class NativeLinear(torch.autograd.Function):
    """Linear layer (y = xW^T + b) with native CUDA forward and backward."""

    @staticmethod
    def forward(ctx, input: torch.Tensor, weight: torch.Tensor,
                bias: torch.Tensor = None) -> torch.Tensor:
        """Forward pass.

        Args:
            input:  [batch x in_features]
            weight: [out_features x in_features]
            bias:   [out_features] or None
        """
        ctx.save_for_backward(input, weight, bias)
        ctx.has_bias = bias is not None
        ops = _get_ops()
        bias_arg = bias.contiguous() if bias is not None else torch.empty(0, device=input.device)
        return ops.linear_forward(input.contiguous(), weight.contiguous(), bias_arg)

    @staticmethod
    def backward(ctx, grad_output: torch.Tensor):
        """Backward pass computing grad_input, grad_weight, and optionally grad_bias."""
        input, weight, bias = ctx.saved_tensors
        ops = _get_ops()
        results = ops.linear_backward(
            grad_output.contiguous(), input.contiguous(),
            weight.contiguous(), ctx.has_bias
        )
        grad_input = results[0]
        grad_weight = results[1]
        grad_bias = results[2] if ctx.has_bias else None
        return grad_input, grad_weight, grad_bias


class NativeAttention(torch.autograd.Function):
    """Scaled dot-product attention with native CUDA kernel."""

    @staticmethod
    def forward(ctx, Q: torch.Tensor, K: torch.Tensor, V: torch.Tensor,
                causal: bool = False) -> torch.Tensor:
        """Forward: output = softmax(Q @ K^T / sqrt(d_k)) @ V.

        Args:
            Q: Query  [seq_len x head_dim]
            K: Key    [seq_len x head_dim]
            V: Value  [seq_len x head_dim]
            causal: Apply lower-triangular causal mask
        """
        ctx.save_for_backward(Q, K, V)
        ctx.causal = causal
        ops = _get_ops()
        return ops.attention(Q.contiguous(), K.contiguous(), V.contiguous(), causal)

    @staticmethod
    def backward(ctx, grad_output: torch.Tensor):
        """Backward pass using PyTorch autograd for the softmax/matmul chain."""
        Q, K, V = ctx.saved_tensors
        d_k = Q.shape[-1]
        scores = torch.matmul(Q, K.t()) / (d_k ** 0.5)
        if ctx.causal:
            mask = torch.triu(torch.ones_like(scores), diagonal=1).bool()
            scores.masked_fill_(mask, float('-inf'))
        attn = torch.softmax(scores, dim=-1)

        grad_V = attn.t() @ grad_output
        grad_attn = grad_output @ V.t()
        grad_scores = attn * (grad_attn - (grad_attn * attn).sum(dim=-1, keepdim=True))
        grad_scores /= (d_k ** 0.5)
        grad_Q = grad_scores @ K
        grad_K = grad_scores.t() @ Q
        return grad_Q, grad_K, grad_V, None


# ---- Convenience functions ----

def native_matmul(A: torch.Tensor, B: torch.Tensor) -> torch.Tensor:
    """Matrix multiplication using the native CUDA kernel."""
    return NativeMatMul.apply(A, B)


def native_linear(input: torch.Tensor, weight: torch.Tensor,
                  bias: torch.Tensor = None) -> torch.Tensor:
    """Linear layer: output = input @ weight^T + bias."""
    return NativeLinear.apply(input, weight, bias)


def native_attention(Q: torch.Tensor, K: torch.Tensor, V: torch.Tensor,
                     causal: bool = False) -> torch.Tensor:
    """Scaled dot-product attention."""
    return NativeAttention.apply(Q, K, V, causal)
