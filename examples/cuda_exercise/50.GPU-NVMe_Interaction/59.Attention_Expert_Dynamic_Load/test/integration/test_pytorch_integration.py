"""
Integration tests for PyTorch attention_expert extension

Tests the full pipeline including:
- Basic forward pass
- Autograd (backward pass)
- AMP (automatic mixed precision)
- torch.compile
"""

import torch
import torch.nn as nn
import pytest
import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'python'))

try:
    from attention_expert import MultiHeadAttention, MixtureOfExperts
    EXTENSION_AVAILABLE = True
except ImportError:
    EXTENSION_AVAILABLE = False
    print("Warning: attention_expert extension not available. Skipping tests.")


@pytest.mark.skipif(not EXTENSION_AVAILABLE, reason="Extension not built")
@pytest.mark.skipif(not torch.cuda.is_available(), reason="CUDA not available")
class TestMultiHeadAttention:
    """Test cases for MultiHeadAttention"""

    def test_basic_forward(self):
        """Test basic forward pass"""
        batch_size = 2
        seq_len = 10
        hidden_dim = 512
        num_heads = 8

        attn = MultiHeadAttention(
            hidden_dim=hidden_dim,
            num_heads=num_heads,
            causal=False
        ).cuda()

        x = torch.randn(batch_size, seq_len, hidden_dim, device='cuda')
        out = attn(x)

        assert out.shape == (batch_size, seq_len, hidden_dim)
        assert out.device == x.device
        assert not torch.isnan(out).any()
        assert not torch.isinf(out).any()

    def test_causal_attention(self):
        """Test causal (autoregressive) attention"""
        batch_size = 2
        seq_len = 10
        hidden_dim = 256
        num_heads = 4

        attn = MultiHeadAttention(
            hidden_dim=hidden_dim,
            num_heads=num_heads,
            causal=True
        ).cuda()

        x = torch.randn(batch_size, seq_len, hidden_dim, device='cuda')
        out = attn(x)

        assert out.shape == x.shape

    def test_autograd(self):
        """Test backward pass (autograd)"""
        batch_size = 2
        seq_len = 10
        hidden_dim = 128
        num_heads = 4

        attn = MultiHeadAttention(
            hidden_dim=hidden_dim,
            num_heads=num_heads
        ).cuda()

        x = torch.randn(batch_size, seq_len, hidden_dim,
                       device='cuda', requires_grad=True)

        out = attn(x)
        loss = out.sum()
        loss.backward()

        # Check gradients exist
        assert x.grad is not None
        assert attn.q_weight.grad is not None
        assert not torch.isnan(x.grad).any()

    def test_amp(self):
        """Test automatic mixed precision (AMP)"""
        batch_size = 2
        seq_len = 10
        hidden_dim = 256
        num_heads = 8

        attn = MultiHeadAttention(
            hidden_dim=hidden_dim,
            num_heads=num_heads
        ).cuda()

        x = torch.randn(batch_size, seq_len, hidden_dim, device='cuda')

        # Run with AMP
        with torch.cuda.amp.autocast():
            out = attn(x)

        # Output should be in lower precision (FP16 or BF16)
        assert out.dtype in [torch.float16, torch.bfloat16]
        assert out.shape == x.shape

    @pytest.mark.skipif(not hasattr(torch, 'compile'), reason="torch.compile not available")
    def test_torch_compile(self):
        """Test torch.compile integration"""
        batch_size = 2
        seq_len = 10
        hidden_dim = 128
        num_heads = 4

        attn = MultiHeadAttention(
            hidden_dim=hidden_dim,
            num_heads=num_heads
        ).cuda()

        # Compile the module
        attn_compiled = torch.compile(attn)

        x = torch.randn(batch_size, seq_len, hidden_dim, device='cuda')

        # Run compiled version
        out = attn_compiled(x)

        assert out.shape == x.shape
        assert not torch.isnan(out).any()

    def test_different_batch_sizes(self):
        """Test with varying batch sizes"""
        hidden_dim = 256
        num_heads = 8

        attn = MultiHeadAttention(
            hidden_dim=hidden_dim,
            num_heads=num_heads
        ).cuda()

        for batch_size in [1, 2, 4, 8]:
            for seq_len in [5, 10, 20]:
                x = torch.randn(batch_size, seq_len, hidden_dim, device='cuda')
                out = attn(x)
                assert out.shape == (batch_size, seq_len, hidden_dim)


@pytest.mark.skipif(not EXTENSION_AVAILABLE, reason="Extension not built")
@pytest.mark.skipif(not torch.cuda.is_available(), reason="CUDA not available")
class TestMixtureOfExperts:
    """Test cases for MixtureOfExperts"""

    def test_basic_forward(self):
        """Test basic MoE forward pass"""
        batch_size = 2
        seq_len = 10
        hidden_dim = 256
        num_experts = 8
        experts_per_token = 2

        moe = MixtureOfExperts(
            hidden_dim=hidden_dim,
            num_experts=num_experts,
            experts_per_token=experts_per_token,
            ffn_dim=1024
        ).cuda()

        x = torch.randn(batch_size, seq_len, hidden_dim, device='cuda')
        out = moe(x)

        assert out.shape == (batch_size, seq_len, hidden_dim)
        assert not torch.isnan(out).any()

    def test_moe_autograd(self):
        """Test MoE backward pass"""
        batch_size = 2
        seq_len = 10
        hidden_dim = 128

        moe = MixtureOfExperts(
            hidden_dim=hidden_dim,
            num_experts=4,
            experts_per_token=2,
            ffn_dim=512
        ).cuda()

        x = torch.randn(batch_size, seq_len, hidden_dim,
                       device='cuda', requires_grad=True)

        out = moe(x)
        loss = out.sum()
        loss.backward()

        assert x.grad is not None


@pytest.mark.skipif(not EXTENSION_AVAILABLE, reason="Extension not built")
@pytest.mark.skipif(not torch.cuda.is_available(), reason="CUDA not available")
class TestEndToEnd:
    """End-to-end integration tests"""

    def test_transformer_block(self):
        """Test combining attention + MoE in a transformer block"""
        batch_size = 2
        seq_len = 20
        hidden_dim = 256

        class TransformerBlock(nn.Module):
            def __init__(self, hidden_dim, num_heads, num_experts):
                super().__init__()
                self.attn = MultiHeadAttention(hidden_dim, num_heads)
                self.moe = MixtureOfExperts(
                    hidden_dim, num_experts, experts_per_token=2, ffn_dim=1024
                )
                self.norm1 = nn.LayerNorm(hidden_dim)
                self.norm2 = nn.LayerNorm(hidden_dim)

            def forward(self, x):
                # Attention with residual
                x = x + self.attn(self.norm1(x))
                # MoE with residual
                x = x + self.moe(self.norm2(x))
                return x

        block = TransformerBlock(
            hidden_dim=hidden_dim,
            num_heads=8,
            num_experts=8
        ).cuda()

        x = torch.randn(batch_size, seq_len, hidden_dim,
                       device='cuda', requires_grad=True)

        # Forward pass
        out = block(x)
        assert out.shape == x.shape

        # Backward pass
        loss = out.sum()
        loss.backward()

        assert x.grad is not None

    def test_cuda_graph_compatibility(self):
        """Test CUDA graph capture"""
        batch_size = 2
        seq_len = 10
        hidden_dim = 128

        attn = MultiHeadAttention(hidden_dim, num_heads=4).cuda()
        x = torch.randn(batch_size, seq_len, hidden_dim, device='cuda')

        # Warmup
        out_warmup = attn(x)

        # Capture graph
        g = torch.cuda.CUDAGraph()
        with torch.cuda.graph(g):
            out_graph = attn(x)

        # Replay graph
        g.replay()

        # Results should match warmup
        assert torch.allclose(out_graph, out_warmup, rtol=1e-3)


if __name__ == '__main__':
    if EXTENSION_AVAILABLE and torch.cuda.is_available():
        print("Running integration tests...")

        # Run basic tests
        test_attn = TestMultiHeadAttention()
        print("✓ Testing basic forward pass...")
        test_attn.test_basic_forward()

        print("✓ Testing autograd...")
        test_attn.test_autograd()

        print("✓ Testing AMP...")
        test_attn.test_amp()

        print("✓ Testing different batch sizes...")
        test_attn.test_different_batch_sizes()

        print("\n✓ All tests passed!")
    else:
        print("Skipping tests: extension not available or CUDA not available")
