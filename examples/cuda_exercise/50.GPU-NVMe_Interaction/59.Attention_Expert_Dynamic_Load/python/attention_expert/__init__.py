"""
attention_expert - PyTorch extension for attention with dynamic expert loading

This package provides native PyTorch integration for:
- Multi-head attention with optional NVMe weight loading
- Mixture of Experts (MoE) with dynamic expert loading
- Full autograd, AMP, and torch.compile support
- NVMe-backed PyTorch Dataset and DataLoader
- Dynamic weight loading utilities
"""

from .ops import MultiHeadAttention, MixtureOfExperts

# NVMe loader (optional, requires NVMe extension)
try:
    from .nvme_loader import (
        NVMeDataset,
        NVMeExpertLoader,
        NVMeAttentionWeightLoader,
        create_nvme_dataloader,
        load_expert_weights
    )
    NVME_AVAILABLE = True
except ImportError:
    NVME_AVAILABLE = False
    NVMeDataset = None
    NVMeExpertLoader = None
    NVMeAttentionWeightLoader = None
    create_nvme_dataloader = None
    load_expert_weights = None

__version__ = '0.1.0'
__all__ = [
    'MultiHeadAttention',
    'MixtureOfExperts',
    'NVMeDataset',
    'NVMeExpertLoader',
    'NVMeAttentionWeightLoader',
    'create_nvme_dataloader',
    'load_expert_weights',
    'NVME_AVAILABLE'
]
