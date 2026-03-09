"""
Complete training example with NVMe-backed dynamic loading

Demonstrates:
1. Loading training data from NVMe using DataLoader
2. Dynamic expert weight loading during forward pass
3. Attention weight caching and prefetching
4. Complete training loop with gradient accumulation
"""

import torch
import torch.nn as nn
import torch.optim as optim
from torch.utils.data import DataLoader
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from attention_expert import MultiHeadAttention, MixtureOfExperts
from attention_expert.nvme_loader import (
    NVMeDataset,
    NVMeExpertLoader,
    NVMeAttentionWeightLoader,
    create_nvme_dataloader
)


class TransformerWithDynamicLoading(nn.Module):
    """
    Transformer block with optional NVMe-backed dynamic weight loading

    Args:
        hidden_dim: Hidden dimension
        num_heads: Number of attention heads
        num_experts: Number of MoE experts
        load_from_nvme: Whether to load weights from NVMe
        nvme_path: Path to NVMe device
    """

    def __init__(
        self,
        hidden_dim=512,
        num_heads=8,
        num_experts=64,
        load_from_nvme=False,
        nvme_path='/dev/nvme0n1'
    ):
        super().__init__()

        self.hidden_dim = hidden_dim
        self.load_from_nvme = load_from_nvme

        # Attention (can load from NVMe)
        self.norm1 = nn.LayerNorm(hidden_dim)
        self.attn = MultiHeadAttention(
            hidden_dim=hidden_dim,
            num_heads=num_heads,
            load_from_nvme=load_from_nvme,
            nvme_path=nvme_path if load_from_nvme else None
        )

        # MoE (dynamic expert loading)
        self.norm2 = nn.LayerNorm(hidden_dim)
        self.moe = MixtureOfExperts(
            hidden_dim=hidden_dim,
            num_experts=num_experts,
            experts_per_token=2,
            ffn_dim=hidden_dim * 4,
            load_from_nvme=load_from_nvme,
            nvme_path=nvme_path if load_from_nvme else None
        )

        # Expert loader (if using NVMe)
        if load_from_nvme:
            expert_size_bytes = 4 * 1024 * 1024  # 4MB per expert
            self.expert_loader = NVMeExpertLoader(
                nvme_path=nvme_path,
                num_experts=num_experts,
                expert_size_bytes=expert_size_bytes,
                cache_size=8  # Cache 8 experts
            )

    def forward(self, x, expert_ids=None):
        """
        Forward pass with optional dynamic loading

        Args:
            x: Input [batch, seq_len, hidden_dim]
            expert_ids: Optional list of expert IDs to prefetch

        Returns:
            Output tensor
        """
        # Prefetch experts if needed
        if self.load_from_nvme and expert_ids is not None:
            self.expert_loader.prefetch_experts(expert_ids)

        # Attention
        x = x + self.attn(self.norm1(x))

        # MoE
        x = x + self.moe(self.norm2(x))

        return x


def train_with_nvme_data(
    nvme_data_path='/dev/nvme0n1',
    nvme_weights_path='/dev/nvme0n2',
    epochs=10,
    batch_size=32,
    learning_rate=1e-4
):
    """
    Complete training loop with NVMe-backed data and weights

    Args:
        nvme_data_path: NVMe device for training data
        nvme_weights_path: NVMe device for model weights
        epochs: Number of training epochs
        batch_size: Batch size
        learning_rate: Learning rate
    """

    print("=" * 60)
    print("Training with NVMe Dynamic Loading")
    print("=" * 60)

    # ========================================
    # 1. Create NVMe-backed DataLoader
    # ========================================

    print("\n[1/5] Creating NVMe DataLoader...")

    # Check if NVMe devices exist (use dummy data if not)
    use_nvme_data = os.path.exists(nvme_data_path)
    use_nvme_weights = os.path.exists(nvme_weights_path)

    if use_nvme_data:
        dataloader = create_nvme_dataloader(
            nvme_path=nvme_data_path,
            kind_id=0,
            start_lba=0,
            length=10000,  # 10K training samples
            item_shape=[512],  # 512-dim input
            batch_size=batch_size,
            shuffle=True
        )
        print(f"✓ Created NVMe DataLoader: {nvme_data_path}")
    else:
        print(f"⚠ NVMe device not found: {nvme_data_path}")
        print("  Using dummy data for demo...")

        # Dummy data for demonstration
        class DummyDataset(torch.utils.data.Dataset):
            def __len__(self):
                return 1000

            def __getitem__(self, idx):
                return torch.randn(512, device='cuda')

        dataloader = DataLoader(DummyDataset(), batch_size=batch_size, shuffle=True)

    # ========================================
    # 2. Create Model with Dynamic Loading
    # ========================================

    print("\n[2/5] Creating model...")

    model = TransformerWithDynamicLoading(
        hidden_dim=512,
        num_heads=8,
        num_experts=64,
        load_from_nvme=use_nvme_weights,
        nvme_path=nvme_weights_path
    ).cuda()

    if use_nvme_weights:
        print(f"✓ Model with NVMe loading: {nvme_weights_path}")
        print(f"  - 64 experts, only ~8 cached in GPU")
        print(f"  - Dynamic loading during forward pass")
    else:
        print("✓ Model created (all-in-memory mode)")

    # ========================================
    # 3. Setup Optimizer and Loss
    # ========================================

    print("\n[3/5] Setting up optimizer...")

    optimizer = optim.Adam(model.parameters(), lr=learning_rate)
    scaler = torch.cuda.amp.GradScaler()  # For AMP

    print(f"✓ Optimizer: Adam (lr={learning_rate})")
    print(f"✓ Using Automatic Mixed Precision (AMP)")

    # ========================================
    # 4. Training Loop
    # ========================================

    print(f"\n[4/5] Starting training ({epochs} epochs)...")

    for epoch in range(epochs):
        model.train()
        total_loss = 0
        num_batches = 0

        for batch_idx, batch in enumerate(dataloader):
            # Ensure batch is on GPU
            if not batch.is_cuda:
                batch = batch.cuda()

            # Add sequence dimension if needed
            if batch.dim() == 2:  # [batch, features]
                batch = batch.unsqueeze(1)  # [batch, 1, features]

            optimizer.zero_grad()

            # Forward pass with AMP
            with torch.cuda.amp.autocast():
                # Forward
                output = model(batch)

                # Dummy loss (replace with actual task loss)
                loss = output.pow(2).mean()

            # Backward with gradient scaling
            scaler.scale(loss).backward()
            scaler.step(optimizer)
            scaler.update()

            total_loss += loss.item()
            num_batches += 1

            # Print progress
            if (batch_idx + 1) % 10 == 0:
                avg_loss = total_loss / num_batches
                print(f"  Epoch [{epoch+1}/{epochs}] "
                      f"Batch [{batch_idx+1}/{len(dataloader)}] "
                      f"Loss: {avg_loss:.6f}")

        avg_epoch_loss = total_loss / num_batches
        print(f"\n  Epoch {epoch+1} Summary: Avg Loss = {avg_epoch_loss:.6f}")

    # ========================================
    # 5. Save Model
    # ========================================

    print("\n[5/5] Saving model...")

    # Save model weights
    save_path = "transformer_nvme_model.pt"
    torch.save(model.state_dict(), save_path)
    print(f"✓ Model saved to {save_path}")

    print("\n" + "=" * 60)
    print("Training Complete!")
    print("=" * 60)


def benchmark_nvme_loading():
    """Benchmark NVMe loading performance"""

    print("\n" + "=" * 60)
    print("NVMe Loading Performance Benchmark")
    print("=" * 60)

    nvme_path = '/dev/nvme0n1'
    if not os.path.exists(nvme_path):
        print(f"⚠ NVMe device not found: {nvme_path}")
        print("  Skipping benchmark...")
        return

    # Test expert loading
    print("\n[1/2] Benchmarking expert loading...")

    expert_loader = NVMeExpertLoader(
        nvme_path=nvme_path,
        num_experts=64,
        expert_size_bytes=4 * 1024 * 1024,  # 4MB
        cache_size=8
    )

    import time

    # Cold load (no cache)
    start = time.time()
    for i in range(8):
        expert_loader.load_expert(i)
    cold_time = time.time() - start
    print(f"  Cold load (8 experts): {cold_time*1000:.2f} ms")

    # Warm load (from cache)
    start = time.time()
    for i in range(8):
        expert_loader.load_expert(i)
    warm_time = time.time() - start
    print(f"  Warm load (8 experts): {warm_time*1000:.2f} ms")
    print(f"  Speedup: {cold_time/warm_time:.1f}x")

    # Test data loading
    print("\n[2/2] Benchmarking data loading...")

    dataloader = create_nvme_dataloader(
        nvme_path=nvme_path,
        kind_id=0,
        start_lba=0,
        length=1000,
        item_shape=[3, 224, 224],  # ImageNet-size
        batch_size=64,
        shuffle=False
    )

    start = time.time()
    for i, batch in enumerate(dataloader):
        if i >= 10:  # Test 10 batches
            break
    data_time = time.time() - start

    print(f"  10 batches (64 samples each): {data_time*1000:.2f} ms")
    print(f"  Throughput: {640/data_time:.1f} samples/sec")

    print("\n" + "=" * 60)


def main():
    """Main entry point"""

    print("\nAttention Expert Dynamic Loading - Training Example\n")

    # Check CUDA availability
    if not torch.cuda.is_available():
        print("ERROR: CUDA not available. This example requires a CUDA GPU.")
        return

    print(f"Using GPU: {torch.cuda.get_device_name(0)}")

    # Run training demo
    try:
        train_with_nvme_data(
            epochs=3,
            batch_size=16,
            learning_rate=1e-4
        )
    except Exception as e:
        print(f"\nTraining failed: {e}")
        import traceback
        traceback.print_exc()

    # Run benchmark
    try:
        benchmark_nvme_loading()
    except Exception as e:
        print(f"\nBenchmark failed: {e}")


if __name__ == '__main__':
    main()
