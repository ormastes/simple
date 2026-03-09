"""
Python unit tests for the native CUDA extension (cuda_native_ops).

These tests verify correctness of the pybind11-bound CUDA operations by
comparing results against PyTorch's built-in implementations.  They require
a CUDA-capable GPU and a working PyTorch installation.

Run with:
    python -m pytest test/unit/test_native_ops.py -v
"""

import unittest
import torch

# Skip the entire module if CUDA is unavailable
if not torch.cuda.is_available():
    raise unittest.SkipTest("CUDA not available")

try:
    import cuda_native_ops
    HAS_OPS = True
except ImportError:
    HAS_OPS = False


@unittest.skipUnless(HAS_OPS, "cuda_native_ops not compiled; run setup.py first")
class TestMatmul(unittest.TestCase):
    """Tests for cuda_native_ops.matmul()."""

    def test_small_square(self):
        """Small square matrices should match torch.matmul within tolerance."""
        A = torch.randn(32, 32, device="cuda")
        B = torch.randn(32, 32, device="cuda")
        C = cuda_native_ops.matmul(A, B)
        ref = torch.matmul(A, B)
        self.assertTrue(torch.allclose(C, ref, atol=1e-3),
                        f"Max diff: {(C - ref).abs().max().item()}")

    def test_non_square(self):
        """Non-square matrices with dimensions not aligned to tile size."""
        A = torch.randn(37, 19, device="cuda")
        B = torch.randn(19, 43, device="cuda")
        C = cuda_native_ops.matmul(A, B)
        ref = torch.matmul(A, B)
        self.assertTrue(torch.allclose(C, ref, atol=1e-2),
                        f"Max diff: {(C - ref).abs().max().item()}")

    def test_identity(self):
        """Multiplying by identity should return the original matrix."""
        A = torch.randn(16, 16, device="cuda")
        I = torch.eye(16, device="cuda")
        C = cuda_native_ops.matmul(A, I)
        self.assertTrue(torch.allclose(C, A, atol=1e-5))


@unittest.skipUnless(HAS_OPS, "cuda_native_ops not compiled")
class TestLinear(unittest.TestCase):
    """Tests for linear forward and backward."""

    def test_forward_no_bias(self):
        """Linear forward without bias should match F.linear."""
        x = torch.randn(8, 16, device="cuda")
        w = torch.randn(10, 16, device="cuda")
        bias = torch.empty(0, device="cuda")
        out = cuda_native_ops.linear_forward(x, w, bias)
        ref = torch.nn.functional.linear(x, w, None)
        self.assertTrue(torch.allclose(out, ref, atol=1e-2),
                        f"Max diff: {(out - ref).abs().max().item()}")

    def test_forward_with_bias(self):
        """Linear forward with bias."""
        x = torch.randn(8, 16, device="cuda")
        w = torch.randn(10, 16, device="cuda")
        b = torch.randn(10, device="cuda")
        out = cuda_native_ops.linear_forward(x, w, b)
        ref = torch.nn.functional.linear(x, w, b)
        self.assertTrue(torch.allclose(out, ref, atol=1e-2),
                        f"Max diff: {(out - ref).abs().max().item()}")

    def test_backward_grad_bias(self):
        """Backward should produce correct grad_bias (column sums of grad_output)."""
        batch, in_f, out_f = 4, 8, 6
        go = torch.randn(batch, out_f, device="cuda")
        x = torch.randn(batch, in_f, device="cuda")
        w = torch.randn(out_f, in_f, device="cuda")
        results = cuda_native_ops.linear_backward(go, x, w, True)
        grad_bias = results[2]
        ref_bias = go.sum(dim=0)
        self.assertTrue(torch.allclose(grad_bias, ref_bias, atol=1e-3),
                        f"Max diff: {(grad_bias - ref_bias).abs().max().item()}")


@unittest.skipUnless(HAS_OPS, "cuda_native_ops not compiled")
class TestAttention(unittest.TestCase):
    """Tests for scaled dot-product attention."""

    def test_no_causal(self):
        """Non-causal attention should produce non-zero output."""
        Q = torch.randn(8, 16, device="cuda")
        K = torch.randn(8, 16, device="cuda")
        V = torch.randn(8, 16, device="cuda")
        out = cuda_native_ops.attention(Q, K, V, False)
        self.assertFalse(torch.all(out == 0))

    def test_causal(self):
        """Causal attention output should differ from non-causal."""
        Q = torch.randn(8, 16, device="cuda")
        K = torch.randn(8, 16, device="cuda")
        V = torch.randn(8, 16, device="cuda")
        out_nc = cuda_native_ops.attention(Q, K, V, False)
        out_c = cuda_native_ops.attention(Q, K, V, True)
        # First row should be the same (no future tokens to mask)
        self.assertTrue(torch.allclose(out_nc[0], out_c[0], atol=1e-3))
        # Later rows should generally differ
        self.assertFalse(torch.allclose(out_nc, out_c, atol=1e-4))

    def test_uniform_attention(self):
        """With Q=K=0, attention weights are uniform, output = mean(V, dim=0)."""
        seq, dim = 4, 4
        Q = torch.zeros(seq, dim, device="cuda")
        K = torch.zeros(seq, dim, device="cuda")
        V = torch.eye(seq, dim, device="cuda")
        out = cuda_native_ops.attention(Q, K, V, False)
        expected = V.mean(dim=0).unsqueeze(0).expand(seq, dim)
        self.assertTrue(torch.allclose(out, expected, atol=1e-3),
                        f"Max diff: {(out - expected).abs().max().item()}")


if __name__ == "__main__":
    unittest.main()
