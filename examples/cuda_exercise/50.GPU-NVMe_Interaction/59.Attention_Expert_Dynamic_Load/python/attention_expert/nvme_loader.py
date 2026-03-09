"""
NVMe-backed PyTorch Dataset and DataLoader integration

Provides utilities for loading data directly from NVMe storage into GPU tensors,
bypassing host memory for maximum efficiency.
"""

import torch
from torch.utils.data import Dataset, DataLoader
from typing import Optional, Tuple, List
import os

# Import C++ extension
try:
    import attention_expert._nvme_loader as _nvme
    NVME_AVAILABLE = True
except ImportError:
    NVME_AVAILABLE = False
    print("Warning: NVMe loader extension not available. "
          "Build with nvme support to enable NVMe loading.")


class NVMeDataset(Dataset):
    """
    PyTorch Dataset backed by NVMe storage

    Loads data directly from NVMe into GPU tensors, bypassing host memory.
    Compatible with torch.utils.data.DataLoader for training pipelines.

    Args:
        nvme_path: Path to NVMe device (e.g., '/dev/nvme0n1' or file path)
        kind_id: Data kind identifier
        start_lba: Starting LBA for this dataset
        length: Number of items in dataset
        sector_size: Bytes per sector (usually 4096)
        item_shape: Shape of each item (without batch dimension)
        dtype: Data type (torch.float32, torch.float16, etc.)

    Example:
        >>> dataset = NVMeDataset(
        ...     nvme_path='/dev/nvme0n1',
        ...     kind_id=0,
        ...     start_lba=0,
        ...     length=50000,
        ...     sector_size=4096,
        ...     item_shape=[3, 224, 224],  # ImageNet images
        ...     dtype=torch.float32
        ... )
        >>> dataloader = DataLoader(dataset, batch_size=64, shuffle=True)
        >>> for batch in dataloader:
        ...     # batch is already on GPU!
        ...     pass
    """

    def __init__(
        self,
        nvme_path: str,
        kind_id: int,
        start_lba: int,
        length: int,
        sector_size: int = 4096,
        item_shape: Tuple[int, ...] = (1,),
        dtype: torch.dtype = torch.float32
    ):
        if not NVME_AVAILABLE:
            raise RuntimeError("NVMe loader extension not available")

        if not os.path.exists(nvme_path):
            raise FileNotFoundError(f"NVMe device not found: {nvme_path}")

        self.nvme_path = nvme_path
        self.kind_id = kind_id
        self.length = length
        self.item_shape = item_shape
        self.dtype = dtype

        # Create reader and add kind
        self.reader = _nvme.TensorNVMeReader(nvme_path)
        self.reader.add_kind(
            kind_id, start_lba, length, sector_size, item_shape, dtype
        )

    def __len__(self) -> int:
        return self.length

    def __getitem__(self, idx: int) -> torch.Tensor:
        """Load single item from NVMe"""
        if idx < 0 or idx >= self.length:
            raise IndexError(f"Index {idx} out of range [0, {self.length})")

        # Read single item (count=1), then remove batch dimension
        tensor = self.reader.read_kind(self.kind_id, idx, 1)
        return tensor.squeeze(0)


class NVMeExpertLoader:
    """
    Loader for MoE expert weights stored on NVMe

    Manages dynamic loading of expert weights from NVMe storage.
    Useful for large-scale MoE models where all experts don't fit in GPU memory.

    Args:
        nvme_path: Path to NVMe device containing expert weights
        num_experts: Total number of experts
        expert_size_bytes: Size of each expert in bytes
        base_offset: Base byte offset in NVMe device
        cache_size: Maximum number of experts to cache in GPU (0 = no cache)

    Example:
        >>> loader = NVMeExpertLoader(
        ...     nvme_path='/dev/nvme0n1',
        ...     num_experts=64,
        ...     expert_size_bytes=4 * 1024 * 1024,  # 4MB per expert
        ...     base_offset=0
        ... )
        >>> # Load expert 5
        >>> expert_weights = loader.load_expert(5)
        >>> print(expert_weights.shape)
    """

    def __init__(
        self,
        nvme_path: str,
        num_experts: int,
        expert_size_bytes: int,
        base_offset: int = 0,
        cache_size: int = 8,
        dtype: torch.dtype = torch.float32
    ):
        if not NVME_AVAILABLE:
            raise RuntimeError("NVMe loader extension not available")

        self.nvme_path = nvme_path
        self.num_experts = num_experts
        self.expert_size_bytes = expert_size_bytes
        self.base_offset = base_offset
        self.dtype = dtype

        # Simple LRU cache for experts
        self.cache_size = cache_size
        self.cache = {}  # expert_id -> tensor
        self.cache_order = []  # LRU order

    def load_expert(self, expert_id: int) -> torch.Tensor:
        """
        Load expert weights from NVMe

        Args:
            expert_id: Expert index (0-based)

        Returns:
            Expert weights as CUDA tensor
        """
        if expert_id < 0 or expert_id >= self.num_experts:
            raise ValueError(f"Expert ID {expert_id} out of range")

        # Check cache
        if expert_id in self.cache:
            # Move to front of LRU
            self.cache_order.remove(expert_id)
            self.cache_order.append(expert_id)
            return self.cache[expert_id]

        # Calculate offset for this expert
        offset = self.base_offset + expert_id * self.expert_size_bytes

        # Determine shape (flatten expert weights)
        num_elements = self.expert_size_bytes // self.dtype.itemsize
        shape = [num_elements]

        # Load from NVMe
        expert_tensor = _nvme.read_tensor(
            self.nvme_path, offset, shape, self.dtype
        )

        # Update cache
        if self.cache_size > 0:
            if len(self.cache) >= self.cache_size:
                # Evict oldest
                evict_id = self.cache_order.pop(0)
                del self.cache[evict_id]

            self.cache[expert_id] = expert_tensor
            self.cache_order.append(expert_id)

        return expert_tensor

    def load_experts(self, expert_ids: List[int]) -> List[torch.Tensor]:
        """Load multiple experts"""
        return [self.load_expert(eid) for eid in expert_ids]

    def prefetch_experts(self, expert_ids: List[int]):
        """Prefetch experts into cache (async)"""
        for eid in expert_ids:
            if eid not in self.cache:
                self.load_expert(eid)


class NVMeAttentionWeightLoader:
    """
    Loader for attention layer weights stored on NVMe

    Enables loading attention weights (Q, K, V, O) on-demand from NVMe.
    Useful for very large models or multi-task models with many attention heads.

    Args:
        nvme_path: Path to NVMe device
        num_layers: Number of transformer layers
        hidden_dim: Hidden dimension
        base_offset: Base offset in NVMe
        dtype: Weight data type

    Example:
        >>> loader = NVMeAttentionWeightLoader(
        ...     nvme_path='/dev/nvme0n1',
        ...     num_layers=24,
        ...     hidden_dim=1024
        ... )
        >>> # Load weights for layer 10
        >>> q, k, v, o = loader.load_layer(10)
    """

    def __init__(
        self,
        nvme_path: str,
        num_layers: int,
        hidden_dim: int,
        base_offset: int = 0,
        dtype: torch.dtype = torch.float32
    ):
        if not NVME_AVAILABLE:
            raise RuntimeError("NVMe loader extension not available")

        self.nvme_path = nvme_path
        self.num_layers = num_layers
        self.hidden_dim = hidden_dim
        self.base_offset = base_offset
        self.dtype = dtype

        # Each layer has 4 weight matrices: Q, K, V, O
        # Each matrix is [hidden_dim, hidden_dim]
        self.weight_size_bytes = hidden_dim * hidden_dim * dtype.itemsize
        self.layer_size_bytes = 4 * self.weight_size_bytes

    def load_layer(
        self, layer_id: int
    ) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor]:
        """
        Load attention weights for a specific layer

        Args:
            layer_id: Layer index (0-based)

        Returns:
            Tuple of (Q_weight, K_weight, V_weight, O_weight)
        """
        if layer_id < 0 or layer_id >= self.num_layers:
            raise ValueError(f"Layer ID {layer_id} out of range")

        layer_offset = self.base_offset + layer_id * self.layer_size_bytes
        shape = [self.hidden_dim, self.hidden_dim]

        # Load Q, K, V, O weights
        q_weight = _nvme.read_tensor(
            self.nvme_path, layer_offset + 0 * self.weight_size_bytes, shape, self.dtype
        )
        k_weight = _nvme.read_tensor(
            self.nvme_path, layer_offset + 1 * self.weight_size_bytes, shape, self.dtype
        )
        v_weight = _nvme.read_tensor(
            self.nvme_path, layer_offset + 2 * self.weight_size_bytes, shape, self.dtype
        )
        o_weight = _nvme.read_tensor(
            self.nvme_path, layer_offset + 3 * self.weight_size_bytes, shape, self.dtype
        )

        return q_weight, k_weight, v_weight, o_weight


def create_nvme_dataloader(
    nvme_path: str,
    kind_id: int,
    start_lba: int,
    length: int,
    item_shape: Tuple[int, ...],
    batch_size: int = 32,
    shuffle: bool = True,
    num_workers: int = 0,
    **kwargs
) -> DataLoader:
    """
    Create PyTorch DataLoader with NVMe backend

    Args:
        nvme_path: Path to NVMe device
        kind_id: Data kind identifier
        start_lba: Starting LBA
        length: Number of items
        item_shape: Shape of each item
        batch_size: Batch size
        shuffle: Whether to shuffle data
        num_workers: Number of worker processes (0 = main process only)
        **kwargs: Additional arguments to DataLoader

    Returns:
        DataLoader instance

    Example:
        >>> dataloader = create_nvme_dataloader(
        ...     nvme_path='/dev/nvme0n1',
        ...     kind_id=0,
        ...     start_lba=0,
        ...     length=50000,
        ...     item_shape=[3, 224, 224],
        ...     batch_size=64,
        ...     shuffle=True
        ... )
        >>> for batch in dataloader:
        ...     # Process batch (already on GPU)
        ...     pass
    """
    dataset = NVMeDataset(
        nvme_path=nvme_path,
        kind_id=kind_id,
        start_lba=start_lba,
        length=length,
        item_shape=item_shape
    )

    return DataLoader(
        dataset,
        batch_size=batch_size,
        shuffle=shuffle,
        num_workers=num_workers,
        pin_memory=False,  # Data already on GPU
        **kwargs
    )


# Convenience function for expert loading
def load_expert_weights(nvme_path: str, expert_id: int, expert_size_bytes: int) -> torch.Tensor:
    """Quick helper to load a single expert's weights"""
    if not NVME_AVAILABLE:
        raise RuntimeError("NVMe loader extension not available")

    offset = expert_id * expert_size_bytes
    num_elements = expert_size_bytes // 4  # Assuming float32
    return _nvme.read_tensor(nvme_path, offset, [num_elements], torch.float32)
