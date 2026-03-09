"""
Integration tests for NVMe loading functionality

Tests the complete pipeline including:
- NVMe tensor loading (read/write)
- TensorNVMeReader for dictionary-based access
- NVMeDataset and DataLoader integration
- Dynamic expert/attention weight loading
"""

import torch
import pytest
import sys
import os
import tempfile

# Add parent directory to path for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'python'))

try:
    from attention_expert.nvme_loader import (
        NVMeDataset,
        NVMeExpertLoader,
        NVMeAttentionWeightLoader,
        create_nvme_dataloader,
        NVME_AVAILABLE
    )
    import attention_expert._nvme_loader as _nvme
    EXTENSION_AVAILABLE = NVME_AVAILABLE
except ImportError:
    EXTENSION_AVAILABLE = False
    print("Warning: NVMe extension not available. Skipping NVMe tests.")


@pytest.mark.skipif(not EXTENSION_AVAILABLE, reason="NVMe extension not built")
@pytest.mark.skipif(not torch.cuda.is_available(), reason="CUDA not available")
class TestNVMeTensorIO:
    """Test basic NVMe tensor I/O operations"""

    def test_read_write_tensor(self):
        """Test writing and reading tensor from file"""

        # Create temporary file for testing
        with tempfile.NamedTemporaryFile(delete=False, suffix='.bin') as f:
            temp_path = f.name

        try:
            # Create test tensor
            original = torch.randn(100, 512, device='cuda')

            # Write to file
            bytes_written = _nvme.write_tensor(original, temp_path, 0)
            assert bytes_written == original.numel() * original.element_size()

            # Read back
            loaded = _nvme.read_tensor(temp_path, 0, [100, 512], torch.float32)

            # Verify
            assert loaded.shape == original.shape
            assert loaded.device == original.device
            assert torch.allclose(loaded, original, rtol=1e-5)

        finally:
            if os.path.exists(temp_path):
                os.unlink(temp_path)

    def test_read_into_existing_tensor(self):
        """Test reading into pre-allocated tensor"""

        with tempfile.NamedTemporaryFile(delete=False, suffix='.bin') as f:
            temp_path = f.name

        try:
            # Create and write test data
            original = torch.randn(50, 256, device='cuda')
            _nvme.write_tensor(original, temp_path, 0)

            # Pre-allocate tensor
            preallocated = torch.empty_like(original)

            # Read into it
            result = _nvme.read_into_tensor(
                preallocated, temp_path, 0,
                original.numel() * original.element_size()
            )

            # Verify
            assert result is preallocated  # Same tensor returned
            assert torch.allclose(result, original, rtol=1e-5)

        finally:
            if os.path.exists(temp_path):
                os.unlink(temp_path)


@pytest.mark.skipif(not EXTENSION_AVAILABLE, reason="NVMe extension not built")
@pytest.mark.skipif(not torch.cuda.is_available(), reason="CUDA not available")
class TestTensorNVMeReader:
    """Test dictionary-based tensor reader"""

    def test_add_kind_and_read(self):
        """Test adding kinds and reading data"""

        with tempfile.NamedTemporaryFile(delete=False, suffix='.bin') as f:
            temp_path = f.name

        try:
            # Write test data (100 items, each 512 floats)
            test_data = torch.randn(100, 512, device='cuda')
            _nvme.write_tensor(test_data, temp_path, 0)

            # Create reader
            reader = _nvme.TensorNVMeReader(temp_path)

            # Add kind
            reader.add_kind(
                kind_id=0,
                start_lba=0,
                length=100,
                sector_size=4096,
                item_shape=[512],
                dtype=torch.float32
            )

            # Read first 10 items
            batch = reader.read_kind(kind_id=0, idx=0, count=10)

            assert batch.shape == (10, 512)
            assert batch.device.type == 'cuda'
            assert torch.allclose(batch, test_data[:10], rtol=1e-5)

        finally:
            if os.path.exists(temp_path):
                os.unlink(temp_path)

    def test_multiple_kinds(self):
        """Test managing multiple data kinds"""

        with tempfile.NamedTemporaryFile(delete=False, suffix='.bin') as f:
            temp_path = f.name

        try:
            # Write two kinds of data
            kind0_data = torch.randn(50, 256, device='cuda')
            kind1_data = torch.randn(50, 128, device='cuda')

            offset0 = 0
            _nvme.write_tensor(kind0_data, temp_path, offset0)

            offset1 = kind0_data.numel() * kind0_data.element_size()
            _nvme.write_tensor(kind1_data, temp_path, offset1)

            # Create reader with two kinds
            reader = _nvme.TensorNVMeReader(temp_path)

            reader.add_kind(
                kind_id=0, start_lba=offset0 // 4096, length=50,
                sector_size=4096, item_shape=[256], dtype=torch.float32
            )
            reader.add_kind(
                kind_id=1, start_lba=offset1 // 4096, length=50,
                sector_size=4096, item_shape=[128], dtype=torch.float32
            )

            # Read from both kinds
            batch0 = reader.read_kind(0, 0, 5)
            batch1 = reader.read_kind(1, 0, 5)

            assert batch0.shape == (5, 256)
            assert batch1.shape == (5, 128)

            assert torch.allclose(batch0, kind0_data[:5], rtol=1e-5)
            assert torch.allclose(batch1, kind1_data[:5], rtol=1e-5)

        finally:
            if os.path.exists(temp_path):
                os.unlink(temp_path)


@pytest.mark.skipif(not EXTENSION_AVAILABLE, reason="NVMe extension not built")
@pytest.mark.skipif(not torch.cuda.is_available(), reason="CUDA not available")
class TestNVMeDataset:
    """Test PyTorch Dataset integration"""

    def test_dataset_creation(self):
        """Test creating NVMe-backed dataset"""

        with tempfile.NamedTemporaryFile(delete=False, suffix='.bin') as f:
            temp_path = f.name

        try:
            # Write test data
            test_data = torch.randn(100, 3, 32, 32, device='cuda')
            _nvme.write_tensor(test_data, temp_path, 0)

            # Create dataset
            dataset = NVMeDataset(
                nvme_path=temp_path,
                kind_id=0,
                start_lba=0,
                length=100,
                item_shape=[3, 32, 32],
                dtype=torch.float32
            )

            assert len(dataset) == 100

            # Test indexing
            item = dataset[0]
            assert item.shape == (3, 32, 32)
            assert torch.allclose(item, test_data[0], rtol=1e-5)

        finally:
            if os.path.exists(temp_path):
                os.unlink(temp_path)

    def test_dataloader_integration(self):
        """Test with PyTorch DataLoader"""

        with tempfile.NamedTemporaryFile(delete=False, suffix='.bin') as f:
            temp_path = f.name

        try:
            # Write test data
            test_data = torch.randn(50, 256, device='cuda')
            _nvme.write_tensor(test_data, temp_path, 0)

            # Create DataLoader
            dataloader = create_nvme_dataloader(
                nvme_path=temp_path,
                kind_id=0,
                start_lba=0,
                length=50,
                item_shape=[256],
                batch_size=10,
                shuffle=False,
                num_workers=0
            )

            # Test iteration
            batches = list(dataloader)
            assert len(batches) == 5  # 50 items / batch_size 10

            # First batch should match test data
            first_batch = batches[0]
            assert first_batch.shape == (10, 256)
            assert torch.allclose(first_batch, test_data[:10], rtol=1e-5)

        finally:
            if os.path.exists(temp_path):
                os.unlink(temp_path)


@pytest.mark.skipif(not EXTENSION_AVAILABLE, reason="NVMe extension not built")
@pytest.mark.skipif(not torch.cuda.is_available(), reason="CUDA not available")
class TestExpertAndAttentionLoading:
    """Test expert and attention weight loading"""

    def test_expert_loader(self):
        """Test NVMeExpertLoader"""

        with tempfile.NamedTemporaryFile(delete=False, suffix='.bin') as f:
            temp_path = f.name

        try:
            # Create 8 experts, each 1MB (256K floats)
            num_experts = 8
            expert_size_bytes = 256 * 1024 * 4  # 256K floats * 4 bytes

            # Write experts
            for i in range(num_experts):
                expert_weights = torch.full([256 * 1024], float(i), device='cuda')
                offset = i * expert_size_bytes
                _nvme.write_tensor(expert_weights, temp_path, offset)

            # Create loader
            loader = NVMeExpertLoader(
                nvme_path=temp_path,
                num_experts=num_experts,
                expert_size_bytes=expert_size_bytes,
                cache_size=3
            )

            # Load expert 5
            expert5 = loader.load_expert(5)
            assert expert5.shape[0] == 256 * 1024
            assert torch.allclose(expert5, torch.tensor(5.0))

            # Load from cache (should be fast)
            expert5_cached = loader.load_expert(5)
            assert expert5_cached is expert5  # Same tensor

        finally:
            if os.path.exists(temp_path):
                os.unlink(temp_path)

    def test_attention_weight_loader(self):
        """Test NVMeAttentionWeightLoader"""

        with tempfile.NamedTemporaryFile(delete=False, suffix='.bin') as f:
            temp_path = f.name

        try:
            # Create 3 layers, hidden_dim=128
            num_layers = 3
            hidden_dim = 128

            # Write Q, K, V, O for each layer
            for layer in range(num_layers):
                for weight_idx, value in enumerate([1.0, 2.0, 3.0, 4.0]):  # Q, K, V, O
                    weight = torch.full([hidden_dim, hidden_dim], value, device='cuda')
                    offset = (layer * 4 + weight_idx) * hidden_dim * hidden_dim * 4
                    _nvme.write_tensor(weight, temp_path, offset)

            # Create loader
            loader = NVMeAttentionWeightLoader(
                nvme_path=temp_path,
                num_layers=num_layers,
                hidden_dim=hidden_dim
            )

            # Load layer 1
            q, k, v, o = loader.load_layer(1)

            assert q.shape == (hidden_dim, hidden_dim)
            assert torch.allclose(q, torch.tensor(1.0))
            assert torch.allclose(k, torch.tensor(2.0))
            assert torch.allclose(v, torch.tensor(3.0))
            assert torch.allclose(o, torch.tensor(4.0))

        finally:
            if os.path.exists(temp_path):
                os.unlink(temp_path)


if __name__ == '__main__':
    if EXTENSION_AVAILABLE and torch.cuda.is_available():
        print("Running NVMe loading integration tests...")

        # Run basic I/O tests
        test_io = TestNVMeTensorIO()
        print("✓ Testing tensor I/O...")
        test_io.test_read_write_tensor()
        test_io.test_read_into_existing_tensor()

        # Run reader tests
        test_reader = TestTensorNVMeReader()
        print("✓ Testing TensorNVMeReader...")
        test_reader.test_add_kind_and_read()
        test_reader.test_multiple_kinds()

        # Run dataset tests
        test_dataset = TestNVMeDataset()
        print("✓ Testing NVMeDataset...")
        test_dataset.test_dataset_creation()
        test_dataset.test_dataloader_integration()

        # Run expert/attention tests
        test_loading = TestExpertAndAttentionLoading()
        print("✓ Testing expert/attention loading...")
        test_loading.test_expert_loader()
        test_loading.test_attention_weight_loader()

        print("\n✓ All NVMe tests passed!")
    else:
        print("Skipping tests: extension not available or CUDA not available")
