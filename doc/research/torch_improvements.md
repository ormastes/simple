# Torch Module Improvements - Research & Implementation Plan

**Date:** 2026-01-10
**Status:** Research Phase
**Related Specs:** `doc/spec/tooling/{config_system,experiment_tracking,training_engine}.md`

---

## Executive Summary

This document proposes comprehensive improvements to the Simple ML/Torch infrastructure, drawing inspiration from PyTorch Ignite, OmegaConf, and W&B while harmonizing with existing Simple infrastructure. Key enhancements include:

1. **Smart Caching System** - Mmap-based data caching with memory-aware management
2. **Runtime Validation Modes** - `check_only`, `train_only`, `check_and_train` for comprehensive testing
3. **Enhanced Config System** - SDN-based hierarchical configuration with CLI overrides
4. **Experiment Tracking** - Local-first tracking with artifact lineage
5. **Training Engine** - Event-driven, composable training loops

---

## 1. Smart Caching System

### 1.1 Architecture Overview

Build upon existing mmap infrastructure (`src/runtime/src/value/file_io/mmap.rs`) to create intelligent data caching:

```
┌─────────────────────────────────────────────────────────────┐
│                     CacheManager                            │
├─────────────────────────────────────────────────────────────┤
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │
│  │ File Scanner │→ │ Memory Check │→ │ Cache Policy │     │
│  └──────────────┘  └──────────────┘  └──────────────┘     │
│         ↓                  ↓                  ↓             │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │
│  │ Mmap Regions │  │ Normal I/O   │  │ Cache Status │     │
│  └──────────────┘  └──────────────┘  └──────────────┘     │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 File Size Analysis & Smart Caching

**Strategy:** Mimic Ignite's data loading but enhance with memory-aware caching:

```simple
# simple/std_lib/src/ml/torch/cache.spl

class FileCacheEntry:
    path: Str
    size: Int
    priority: Int           # 0=low, 1=normal, 2=high
    cache_mode: CacheMode   # Mmap, Normal, None
    last_accessed: F64
    mtime: F64              # Modification time

enum CacheMode:
    Mmap      # Memory-mapped (zero-copy)
    Normal    # Standard buffered I/O
    None      # No caching (direct load)
    Disabled  # Explicitly disabled for this file

class CacheManager:
    entries: [FileCacheEntry]
    total_size: Int
    memory_limit: Int
    mmap_regions: {str: MmapRegion}

    fn __init__(self, memory_limit: Int = null):
        # Auto-detect memory limit (80% of available RAM)
        if memory_limit is null:
            total_mem = sys.memory_total()
            self.memory_limit = (total_mem * 0.8).to_int()
        else:
            self.memory_limit = memory_limit

        self.entries = []
        self.total_size = 0
        self.mmap_regions = {}

    fn scan_files(self, paths: [Str], priorities: {str: Int} = {}):
        """Scan files and determine caching strategy"""

        # Collect file info
        files = []
        for path in paths:
            if not fs.exists(path):
                continue

            stat = fs.stat(path)
            files.append({
                "path": path,
                "size": stat.size,
                "priority": priorities.get(path, 1),
                "mtime": stat.mtime
            })

        # Sort by priority (high to low), then size (small to large)
        files = sorted(files, key=lambda f: (-f["priority"], f["size"]))

        # Determine cache strategy
        cumulative_size = 0
        for file in files:
            # Check if adding this file exceeds memory
            if cumulative_size + file["size"] > self.memory_limit:
                # Switch to normal I/O for remaining files
                cache_mode = CacheMode.Normal
            else:
                cache_mode = CacheMode.Mmap
                cumulative_size += file["size"]

            entry = FileCacheEntry(
                path=file["path"],
                size=file["size"],
                priority=file["priority"],
                cache_mode=cache_mode,
                last_accessed=time.now(),
                mtime=file["mtime"]
            )
            self.entries.append(entry)

        self.total_size = cumulative_size

        return {
            "total_files": len(files),
            "total_size": sum(f["size"] for f in files),
            "cached_size": cumulative_size,
            "cached_files": sum(1 for e in self.entries if e.cache_mode == CacheMode.Mmap),
            "memory_limit": self.memory_limit
        }

    fn get(self, path: Str) -> CachedData:
        """Get file data (from cache or load)"""

        entry = self._find_entry(path)
        if entry is null:
            # Not tracked, load directly
            return self._load_normal(path)

        # Check if file changed
        current_mtime = fs.stat(path).mtime
        if current_mtime > entry.mtime:
            # File changed, invalidate cache
            self._invalidate(path)
            entry.mtime = current_mtime

        # Update access time
        entry.last_accessed = time.now()

        # Return based on cache mode
        match entry.cache_mode:
            CacheMode.Mmap:
                return self._load_mmap(entry)
            CacheMode.Normal:
                return self._load_normal(path)
            CacheMode.None:
                return self._load_direct(path)
            CacheMode.Disabled:
                return self._load_direct(path)

    fn _load_mmap(self, entry: FileCacheEntry) -> CachedData:
        """Load via mmap (zero-copy)"""

        # Check if already mapped
        if entry.path in self.mmap_regions:
            region = self.mmap_regions[entry.path]
            return CachedData(region.data, cached=true)

        # Create mmap region
        region_handle = native_mmap_create(entry.path)
        data = native_mmap_read(region_handle, offset=0, size=entry.size)

        self.mmap_regions[entry.path] = MmapRegion(
            handle=region_handle,
            data=data,
            size=entry.size
        )

        return CachedData(data, cached=true)

    fn _load_normal(self, path: Str) -> CachedData:
        """Load via standard I/O (buffered)"""
        data = fs.read_bytes(path)
        return CachedData(data, cached=false)

    fn _load_direct(self, path: Str) -> CachedData:
        """Direct load (no caching)"""
        data = fs.read_bytes(path)
        return CachedData(data, cached=false)

    fn _invalidate(self, path: Str):
        """Invalidate cache for file"""
        if path in self.mmap_regions:
            region = self.mmap_regions[path]
            native_mmap_unmap(region.handle)
            del self.mmap_regions[path]

    fn set_cache_mode(self, path: Str, mode: CacheMode):
        """Override cache mode for specific file"""
        entry = self._find_entry(path)
        if entry is not null:
            if entry.cache_mode == CacheMode.Mmap and mode != CacheMode.Mmap:
                self._invalidate(path)
            entry.cache_mode = mode

    fn cleanup(self):
        """Cleanup all mmap regions"""
        for path, region in self.mmap_regions.items():
            native_mmap_unmap(region.handle)
        self.mmap_regions.clear()

    fn stats(self) -> {str: any}:
        """Get cache statistics"""
        return {
            "total_entries": len(self.entries),
            "mmap_count": sum(1 for e in self.entries if e.cache_mode == CacheMode.Mmap),
            "total_size": self.total_size,
            "memory_limit": self.memory_limit,
            "memory_usage_pct": (self.total_size / self.memory_limit * 100).to_int(),
            "active_mmaps": len(self.mmap_regions)
        }
```

### 1.3 Background Tokenizer Loading

Leverage existing async file infrastructure (`src/runtime/src/value/file_io/async_file.rs`):

```simple
# simple/std_lib/src/ml/torch/tokenizer_cache.spl

class TokenizerCache:
    vocab_handle: AsyncFileHandle
    merges_handle: AsyncFileHandle
    cache_dir: Str
    ready: Bool

    fn __init__(self, vocab_path: Str, merges_path: Str = null):
        self.cache_dir = fs.cache_dir("tokenizers")
        self.ready = false

        # Start background loading
        self.vocab_handle = self._start_async_load(vocab_path, prefault=true)

        if merges_path is not null:
            self.merges_handle = self._start_async_load(merges_path, prefault=true)

    fn _start_async_load(self, path: Str, prefault: Bool) -> AsyncFileHandle:
        """Start async file loading with mmap"""

        # Create async file handle
        handle = native_async_file_create(path, mode=0, prefault=prefault)

        # Start loading in background
        native_async_file_start_loading(handle)

        return handle

    fn wait_ready(self):
        """Block until tokenizer is loaded"""
        vocab_ready = native_async_file_wait(self.vocab_handle)

        if self.merges_handle is not null:
            merges_ready = native_async_file_wait(self.merges_handle)

        self.ready = true

    fn is_ready(self) -> Bool:
        """Non-blocking check if tokenizer is ready"""
        vocab_ready = native_async_file_is_ready(self.vocab_handle)

        if self.merges_handle is not null:
            merges_ready = native_async_file_is_ready(self.merges_handle)
            return vocab_ready and merges_ready

        return vocab_ready

    fn get_vocab(self) -> Tensor:
        """Get vocab (blocks if not ready)"""
        if not self.ready:
            self.wait_ready()

        return self._decode_vocab(self.vocab_handle)

# Usage in training
tokenizer_cache = TokenizerCache("vocab.txt", "merges.txt")

# Training starts immediately, tokenizer loads in background
model = create_model()
optimizer = create_optimizer()

# ... setup code ...

# Wait for tokenizer before first use
tokenizer_cache.wait_ready()
vocab = tokenizer_cache.get_vocab()
```

### 1.4 Change Detection & Cache Invalidation

```simple
class CacheValidator:
    fn check_source_changes(self, entries: [FileCacheEntry]) -> [Str]:
        """Check which files have changed since caching"""

        changed_files = []

        for entry in entries:
            if not fs.exists(entry.path):
                changed_files.append(entry.path)
                continue

            current_mtime = fs.stat(entry.path).mtime
            if current_mtime > entry.mtime:
                changed_files.append(entry.path)

        return changed_files

    fn auto_invalidate(self, cache_mgr: CacheManager):
        """Auto-invalidate changed files"""

        changed = self.check_source_changes(cache_mgr.entries)

        for path in changed:
            cache_mgr._invalidate(path)
            print(f"Cache invalidated: {path}")

        return len(changed)
```

---

## 2. Runtime Validation System

### 2.1 Overview

Add comprehensive runtime validation with three modes:

- **check_only** - Validate all logic paths without training
- **train_only** - Standard training (existing behavior)
- **check_and_train** - Validate then train

### 2.2 Validation Architecture

```simple
# simple/std_lib/src/ml/torch/validation.spl

enum ValidationMode:
    CheckOnly        # Run checks, no training
    TrainOnly        # Skip checks, train normally
    CheckAndTrain    # Run checks then train

class RuntimeValidator:
    mode: ValidationMode
    checks_passed: Bool
    errors: [ValidationError]

    fn __init__(self, mode: ValidationMode = ValidationMode.TrainOnly):
        self.mode = mode
        self.checks_passed = false
        self.errors = []

    fn should_check(self) -> Bool:
        return self.mode in [ValidationMode.CheckOnly, ValidationMode.CheckAndTrain]

    fn should_train(self) -> Bool:
        return self.mode in [ValidationMode.TrainOnly, ValidationMode.CheckAndTrain]

    fn validate_all(
        self,
        model: torch.nn.Module,
        dataloader: DataLoader,
        optimizer: Optimizer,
        loss_fn: Fn
    ) -> ValidationReport:
        """Run all validation checks"""

        if not self.should_check():
            return ValidationReport(skipped=true)

        report = ValidationReport()

        # 1. Memory validation
        report.add_section(self._check_memory(model, dataloader))

        # 2. Shape validation
        report.add_section(self._check_shapes(model, dataloader))

        # 3. Gradient flow
        report.add_section(self._check_gradients(model, dataloader, loss_fn))

        # 4. NaN/Inf detection
        report.add_section(self._check_numeric_stability(model, dataloader, loss_fn))

        # 5. Device placement
        report.add_section(self._check_devices(model, dataloader))

        # 6. Data pipeline
        report.add_section(self._check_dataloader(dataloader))

        # 7. Optimizer state
        report.add_section(self._check_optimizer(optimizer, model))

        # 8. Loop validation
        report.add_section(self._check_training_loop(model, dataloader, optimizer, loss_fn))

        self.checks_passed = not report.has_errors()
        self.errors = report.errors

        return report

    fn _check_memory(self, model: torch.nn.Module, dataloader: DataLoader) -> ValidationSection:
        """Validate memory usage"""

        section = ValidationSection("Memory Validation")

        # Get model memory
        model_params = sum(p.numel() * p.element_size() for p in model.parameters())
        section.add_info(f"Model parameters: {model_params / 1e6:.2f} MB")

        # Estimate activation memory (single batch)
        sample_batch = next(iter(dataloader))
        batch_size = sample_batch[0].shape[0]

        # Forward pass to measure activation memory
        torch.cuda.reset_peak_memory_stats() if torch.cuda.is_available() else null
        with torch.no_grad():
            _ = model(sample_batch[0])

        if torch.cuda.is_available():
            peak_mem = torch.cuda.max_memory_allocated() / 1e6
            section.add_info(f"Peak activation memory: {peak_mem:.2f} MB")

            # Check if it fits in GPU
            total_gpu_mem = torch.cuda.get_device_properties(0).total_memory / 1e6
            if peak_mem > total_gpu_mem * 0.9:
                section.add_error(f"Memory usage ({peak_mem:.0f}MB) exceeds 90% of GPU memory ({total_gpu_mem:.0f}MB)")
        else:
            section.add_info("Running on CPU, memory check skipped")

        return section

    fn _check_shapes(self, model: torch.nn.Module, dataloader: DataLoader) -> ValidationSection:
        """Validate tensor shapes through the model"""

        section = ValidationSection("Shape Validation")

        sample_batch = next(iter(dataloader))
        images, labels = sample_batch

        section.add_info(f"Input shape: {images.shape}")
        section.add_info(f"Label shape: {labels.shape}")

        try:
            with torch.no_grad():
                output = model(images)

            section.add_info(f"Output shape: {output.shape}")

            # Check output matches labels
            if output.shape[0] != labels.shape[0]:
                section.add_error(f"Batch size mismatch: output[0]={output.shape[0]}, labels[0]={labels.shape[0]}")

            section.add_pass("Shape validation passed")

        except Exception as e:
            section.add_error(f"Shape mismatch error: {e}")

        return section

    fn _check_gradients(
        self,
        model: torch.nn.Module,
        dataloader: DataLoader,
        loss_fn: Fn
    ) -> ValidationSection:
        """Validate gradient flow"""

        section = ValidationSection("Gradient Flow Validation")

        sample_batch = next(iter(dataloader))
        images, labels = sample_batch

        model.train()
        model.zero_grad()

        # Forward pass
        output = model(images)
        loss = loss_fn(output, labels)

        # Backward pass
        loss.backward()

        # Check gradients
        no_grad_params = []
        nan_grad_params = []
        zero_grad_params = []

        for name, param in model.named_parameters():
            if param.grad is null:
                no_grad_params.append(name)
            elif torch.isnan(param.grad).any():
                nan_grad_params.append(name)
            elif torch.abs(param.grad).max() < 1e-10:
                zero_grad_params.append(name)

        if len(no_grad_params) > 0:
            section.add_warning(f"Parameters with no gradients: {no_grad_params}")

        if len(nan_grad_params) > 0:
            section.add_error(f"Parameters with NaN gradients: {nan_grad_params}")

        if len(zero_grad_params) > 0:
            section.add_warning(f"Parameters with near-zero gradients: {zero_grad_params}")

        if len(no_grad_params) == 0 and len(nan_grad_params) == 0:
            section.add_pass("Gradient flow validation passed")

        return section

    fn _check_numeric_stability(
        self,
        model: torch.nn.Module,
        dataloader: DataLoader,
        loss_fn: Fn
    ) -> ValidationSection:
        """Check for NaN/Inf in outputs"""

        section = ValidationSection("Numeric Stability Validation")

        sample_batch = next(iter(dataloader))
        images, labels = sample_batch

        model.eval()
        with torch.no_grad():
            output = model(images)
            loss = loss_fn(output, labels)

        # Check for NaN/Inf
        if torch.isnan(output).any():
            section.add_error("NaN detected in model output")

        if torch.isinf(output).any():
            section.add_error("Inf detected in model output")

        if torch.isnan(loss):
            section.add_error("NaN detected in loss")

        if torch.isinf(loss):
            section.add_error("Inf detected in loss")

        if not (torch.isnan(output).any() or torch.isinf(output).any() or torch.isnan(loss) or torch.isinf(loss)):
            section.add_pass("Numeric stability validation passed")

        return section

    fn _check_devices(self, model: torch.nn.Module, dataloader: DataLoader) -> ValidationSection:
        """Validate device placement"""

        section = ValidationSection("Device Validation")

        sample_batch = next(iter(dataloader))
        images, labels = sample_batch

        # Check model device
        model_device = next(model.parameters()).device
        section.add_info(f"Model device: {model_device}")

        # Check data device
        data_device = images.device
        section.add_info(f"Data device: {data_device}")

        # Check consistency
        if model_device != data_device:
            section.add_error(f"Device mismatch: model on {model_device}, data on {data_device}")
        else:
            section.add_pass("Device validation passed")

        return section

    fn _check_dataloader(self, dataloader: DataLoader) -> ValidationSection:
        """Validate data pipeline"""

        section = ValidationSection("DataLoader Validation")

        # Test iteration
        try:
            batch_count = 0
            for batch in dataloader:
                batch_count += 1
                if batch_count >= 3:  # Test first 3 batches
                    break

            section.add_info(f"Successfully loaded {batch_count} batches")
            section.add_pass("DataLoader validation passed")

        except Exception as e:
            section.add_error(f"DataLoader error: {e}")

        return section

    fn _check_optimizer(self, optimizer: Optimizer, model: torch.nn.Module) -> ValidationSection:
        """Validate optimizer configuration"""

        section = ValidationSection("Optimizer Validation")

        # Check optimizer has parameters
        param_groups = optimizer.param_groups
        section.add_info(f"Optimizer param groups: {len(param_groups)}")

        total_params = sum(len(group["params"]) for group in param_groups)
        model_params = sum(1 for _ in model.parameters())

        section.add_info(f"Parameters in optimizer: {total_params}")
        section.add_info(f"Parameters in model: {model_params}")

        if total_params != model_params:
            section.add_warning(f"Parameter count mismatch: optimizer={total_params}, model={model_params}")

        section.add_pass("Optimizer validation passed")

        return section

    fn _check_training_loop(
        self,
        model: torch.nn.Module,
        dataloader: DataLoader,
        optimizer: Optimizer,
        loss_fn: Fn
    ) -> ValidationSection:
        """Run a mini training loop to validate all logic paths"""

        section = ValidationSection("Training Loop Validation")

        try:
            model.train()

            # Run 3 mini-epochs
            for mini_epoch in 0..3:
                epoch_loss = 0.0
                batch_count = 0

                for batch in dataloader:
                    images, labels = batch

                    # Forward
                    optimizer.zero_grad()
                    output = model(images)
                    loss = loss_fn(output, labels)

                    # Backward
                    loss.backward()
                    optimizer.step()

                    epoch_loss += loss.item()
                    batch_count += 1

                    if batch_count >= 2:  # Just 2 batches per mini-epoch
                        break

                avg_loss = epoch_loss / batch_count
                section.add_info(f"Mini-epoch {mini_epoch}: loss={avg_loss:.4f}")

            section.add_pass("Training loop validation passed")

        except Exception as e:
            section.add_error(f"Training loop error: {e}")

        return section

class ValidationSection:
    name: Str
    infos: [Str]
    warnings: [Str]
    errors: [Str]
    passed: Bool

    fn __init__(self, name: Str):
        self.name = name
        self.infos = []
        self.warnings = []
        self.errors = []
        self.passed = false

    fn add_info(self, msg: Str):
        self.infos.append(msg)

    fn add_warning(self, msg: Str):
        self.warnings.append(msg)

    fn add_error(self, msg: Str):
        self.errors.append(msg)

    fn add_pass(self, msg: Str):
        self.passed = true
        self.infos.append(f"✓ {msg}")

    fn has_errors(self) -> Bool:
        return len(self.errors) > 0

class ValidationReport:
    sections: [ValidationSection]
    skipped: Bool

    fn __init__(self, skipped: Bool = false):
        self.sections = []
        self.skipped = skipped

    fn add_section(self, section: ValidationSection):
        self.sections.append(section)

    fn has_errors(self) -> Bool:
        return any(s.has_errors() for s in self.sections)

    fn print(self):
        if self.skipped:
            print("Validation skipped (train_only mode)")
            return

        print("=" * 70)
        print("RUNTIME VALIDATION REPORT")
        print("=" * 70)

        for section in self.sections:
            print(f"\n{section.name}")
            print("-" * 70)

            for info in section.infos:
                print(f"  [INFO] {info}")

            for warning in section.warnings:
                print(f"  [WARN] {warning}")

            for error in section.errors:
                print(f"  [ERROR] {error}")

        print("\n" + "=" * 70)
        if self.has_errors():
            print("VALIDATION FAILED ❌")
        else:
            print("VALIDATION PASSED ✓")
        print("=" * 70)
```

### 2.3 Integration with Training

```simple
# Example training script with validation

import Conf from config
import Track from ml.tracking
import RuntimeValidator, ValidationMode from ml.torch.validation
import torch from ml.torch

# Load config
cfg = Conf.load_sdn("config/train.sdn")

# Parse validation mode from CLI or config
mode_str = cfg.get("validation_mode", "train_only")
validation_mode = match mode_str:
    "check_only" => ValidationMode.CheckOnly
    "train_only" => ValidationMode.TrainOnly
    "check_and_train" => ValidationMode.CheckAndTrain

# Create validator
validator = RuntimeValidator(validation_mode)

# Setup training components
model = create_model(cfg)
train_loader = create_dataloader(cfg, split="train")
val_loader = create_dataloader(cfg, split="val")
optimizer = torch.optim.Adam(model.parameters(), lr=cfg.lr)
loss_fn = torch.nn.CrossEntropyLoss()

# Run validation
report = validator.validate_all(model, train_loader, optimizer, loss_fn)
report.print()

# Exit if check_only or validation failed
if validation_mode == ValidationMode.CheckOnly:
    print("Check-only mode: exiting without training")
    sys.exit(0 if report.has_errors() else 1)

if validation_mode == ValidationMode.CheckAndTrain and report.has_errors():
    print("Validation failed: aborting training")
    sys.exit(1)

# Proceed with training
if validator.should_train():
    with Track.run(project=cfg.project, config=Conf.to_dict(cfg)) as run:
        # ... training loop ...
        pass
```

### 2.4 CLI Integration

```bash
# Check only (validate without training)
simple train.spl --mode=check_only

# Train only (skip validation)
simple train.spl --mode=train_only

# Check and train (validate then train if passed)
simple train.spl --mode=check_and_train
```

---

## 3. Enhanced Configuration System

### 3.1 SDN-Based Config

Use SDN as the primary configuration format (see `doc/spec/tooling/config_system.md`):

```sdn
# config/train.sdn

# Project metadata
project = cifar10-resnet50
seed = 42
validation_mode = check_and_train

# Training hyperparameters
train:
    epochs = 100
    batch_size = 128
    lr = 1e-3
    weight_decay = 1e-4
    checkpoint_every = 1000

# Model architecture
model:
    type = resnet50
    pretrained = false
    num_classes = 10
    dropout = 0.1

# Dataset
dataset:
    name = cifar10
    root = ./data
    augmentation = true
    num_workers = 4

# Cache configuration
cache:
    enabled = true
    memory_limit = null  # Auto-detect
    priorities:
        model_weights = 2
        vocab = 2
        train_data = 1
        val_data = 0

# Tracking
tracking:
    enabled = true
    mode = offline
    log_every = 10
```

### 3.2 CLI Overrides

```bash
# Override specific values
simple train.spl train.lr=5e-4 train.batch_size=256 model.dropout=0.2

# Use different config file
simple train.spl --config=config/ablation.sdn train.epochs=50
```

---

## 4. Integration with Existing Infrastructure

### 4.1 Harmonization Strategy

**Leverage existing Simple infrastructure:**

1. **File I/O** - Use `src/runtime/src/value/file_io/`
   - `mmap.rs` for zero-copy file access
   - `async_file.rs` for background loading
   - `fadvise.rs` for kernel hints

2. **Concurrency** - Use `src/runtime/src/concurrent/`
   - `ConcurrentMap` for cache registries
   - `ConcurrentQueue` for async task queues

3. **Memory** - Use `src/runtime/src/memory/gc.rs`
   - `GcRuntime` for heap management
   - Write barriers for cache updates

4. **SDN** - Use `src/sdn/` for config parsing
   - `SdnDocument` for config loading
   - Path queries for nested access

5. **Module Cache** - Extend `src/compiler/src/module_cache.rs` pattern
   - Thread-local caches
   - Circular dependency detection

### 4.2 FFI Additions

New FFI functions needed in `simple/std_lib/src/ml/torch/`:

```simple
# Additional FFI for validation
@rt_torch_memory_stats() -> {total: i64, used: i64, peak: i64}
@rt_torch_has_nan(tensor_handle: u64) -> i32
@rt_torch_has_inf(tensor_handle: u64) -> i32
@rt_torch_gradient_norm(tensor_handle: u64) -> f64

# Cache management FFI
@rt_cache_create(memory_limit: i64) -> u64
@rt_cache_scan_files(cache_handle: u64, paths_ptr: *u8, paths_len: i32) -> i32
@rt_cache_get(cache_handle: u64, path_ptr: *u8, path_len: i32, &data_handle: u64) -> i32
@rt_cache_invalidate(cache_handle: u64, path_ptr: *u8, path_len: i32) -> i32
@rt_cache_stats(cache_handle: u64) -> {str: any}
```

---

## 5. Implementation Roadmap

### Phase 1: Core Caching (Week 1-2)
- [ ] Implement `CacheManager` with file scanning
- [ ] Memory-aware mmap allocation
- [ ] File size sorting and prioritization
- [ ] Basic cache invalidation

### Phase 2: Async Loading (Week 3)
- [ ] Background tokenizer loading
- [ ] Async file handle integration
- [ ] Progress tracking

### Phase 3: Validation System (Week 4-5)
- [ ] `RuntimeValidator` class
- [ ] Memory validation
- [ ] Shape validation
- [ ] Gradient flow checks
- [ ] Numeric stability checks
- [ ] Training loop validation

### Phase 4: Config Integration (Week 6)
- [ ] SDN config loading
- [ ] CLI dotlist parser
- [ ] Config merging
- [ ] Interpolation support

### Phase 5: Tracking & Engine (Week 7-8)
- [ ] Experiment tracking system (see `experiment_tracking.md`)
- [ ] Training engine (see `training_engine.md`)
- [ ] Handler library

### Phase 6: Testing & Docs (Week 9-10)
- [ ] Unit tests (SSpec format)
- [ ] Integration tests
- [ ] User guide
- [ ] API documentation

---

## 6. Testing Strategy

### 6.1 Cache System Tests

```simple
# test/unit/ml/torch/cache_spec.spl

feature "Cache System":
    scenario "File size analysis":
        files = [
            "small.bin",   # 1 MB
            "medium.bin",  # 100 MB
            "large.bin"    # 5 GB
        ]

        cache = CacheManager(memory_limit=200_000_000)  # 200 MB
        stats = cache.scan_files(files)

        assert stats["cached_files"] == 2  # small + medium
        assert stats["cached_size"] < 200_000_000

    scenario "Memory limit enforcement":
        cache = CacheManager(memory_limit=50_000_000)  # 50 MB

        # Should fit in cache
        data1 = cache.get("small.bin")  # 10 MB
        assert data1.cached == true

        # Should exceed limit, use normal I/O
        data2 = cache.get("large.bin")  # 100 MB
        assert data2.cached == false

    scenario "Change detection":
        cache = CacheManager()
        cache.scan_files(["data.bin"])

        # Modify file
        fs.write_bytes("data.bin", new_data)

        # Should detect change
        data = cache.get("data.bin")
        # Cache should be invalidated and reloaded
```

### 6.2 Validation System Tests

```simple
# test/unit/ml/torch/validation_spec.spl

feature "Runtime Validation":
    scenario "Shape validation":
        model = SimpleModel(input_size=784, output_size=10)
        dataloader = create_test_dataloader(batch_size=32)

        validator = RuntimeValidator(ValidationMode.CheckOnly)
        report = validator.validate_all(model, dataloader, optimizer, loss_fn)

        assert not report.has_errors()

    scenario "Gradient flow detection":
        model = ModelWithDeadLayer()  # Has layer with no gradients
        dataloader = create_test_dataloader()

        validator = RuntimeValidator(ValidationMode.CheckOnly)
        report = validator.validate_all(model, dataloader, optimizer, loss_fn)

        # Should detect no gradients in dead layer
        assert report.has_errors()

    scenario "Memory check":
        huge_model = HugeModel(size=10_000_000)  # 10M parameters
        tiny_gpu_mem = 100_000_000  # 100 MB (simulated)

        validator = RuntimeValidator(ValidationMode.CheckOnly)
        report = validator._check_memory(huge_model, dataloader)

        # Should warn about memory usage
        assert len(report.warnings) > 0
```

---

## 7. Performance Considerations

### 7.1 Mmap vs Normal I/O

**Mmap Advantages:**
- Zero-copy data access
- OS-level caching
- Shared memory across processes
- Lazy loading (pages loaded on demand)

**Mmap Disadvantages:**
- Page fault overhead on first access
- Limited by virtual address space
- Not suitable for very large files on 32-bit systems

**Decision Rule:**
- Files < memory_limit: Use mmap
- Files > memory_limit: Use normal I/O
- Files > 2GB on 32-bit: Force normal I/O

### 7.2 Background Loading

**Tokenizer Loading:**
- Start async load at initialization
- Continue training setup
- Wait before first use
- ~30-50% speedup on large vocab files

**Dataset Prefetching:**
- Load next batch in background
- Hide I/O latency during compute
- Use thread pool for parallel loading

---

## 8. Example End-to-End Usage

```simple
#!/usr/bin/env simple

import Conf from config
import Track from ml.tracking
import Engine, Events from ml.engine
import Checkpoint, EarlyStopping from ml.engine.handlers
import RuntimeValidator, ValidationMode from ml.torch.validation
import CacheManager from ml.torch.cache
import torch from ml.torch

# 1. Load configuration (SDN format)
cfg = Conf.load_sdn("config/train.sdn")
cli_overrides = Conf.from_cli_dotlist(sys.args[1..])
cfg = Conf.merge(cfg, cli_overrides)
cfg = Conf.resolve(cfg)

# 2. Setup cache system
cache = CacheManager(memory_limit=cfg.cache.memory_limit)
dataset_files = glob("data/train/*.bin") + glob("data/val/*.bin")
cache.scan_files(dataset_files, priorities=cfg.cache.priorities)

print("Cache stats:", cache.stats())

# 3. Setup validation
validation_mode = match cfg.validation_mode:
    "check_only" => ValidationMode.CheckOnly
    "train_only" => ValidationMode.TrainOnly
    "check_and_train" => ValidationMode.CheckAndTrain

validator = RuntimeValidator(validation_mode)

# 4. Create model, dataloader, optimizer
model = create_model(cfg.model)
train_loader = create_dataloader(cfg.dataset, cache=cache, split="train")
val_loader = create_dataloader(cfg.dataset, cache=cache, split="val")
optimizer = torch.optim.Adam(model.parameters(), lr=cfg.train.lr)
loss_fn = torch.nn.CrossEntropyLoss()

# 5. Run validation
report = validator.validate_all(model, train_loader, optimizer, loss_fn)
report.print()

if validation_mode == ValidationMode.CheckOnly:
    sys.exit(0)

if validation_mode == ValidationMode.CheckAndTrain and report.has_errors():
    print("Validation failed, aborting training")
    sys.exit(1)

# 6. Setup training engine
fn train_step(engine: Engine, batch: any):
    model.train()
    optimizer.zero_grad()

    x, y = batch
    pred = model(x)
    loss = loss_fn(pred, y)

    loss.backward()
    optimizer.step()

    return {"loss": loss.item(), "pred": pred.detach(), "labels": y}

fn val_step(engine: Engine, batch: any):
    model.eval()
    with torch.no_grad():
        x, y = batch
        pred = model(x)
        loss = loss_fn(pred, y)
    return {"loss": loss.item(), "pred": pred, "labels": y}

trainer = Engine(train_step)
evaluator = Engine(val_step)

# 7. Setup tracking
with Track.run(project=cfg.project, config=Conf.to_dict(cfg)) as run:
    # Validation every epoch
    @trainer.on(Events.EPOCH_COMPLETED)
    fn validate(engine: Engine):
        evaluator.run(val_loader)
        metrics = evaluator.state.metrics

        run.log({
            "train/loss": engine.state.output["loss"],
            "val/loss": metrics["loss"],
            "val/acc": metrics["acc"]
        }, step=engine.state.epoch)

    # Checkpointing
    checkpoint = Checkpoint(
        to_save={"model": model, "optimizer": optimizer},
        save_dir=cfg.train.checkpoint_dir,
        score_function=lambda e: evaluator.state.metrics["acc"],
        n_saved=3
    )
    trainer.on(Events.EPOCH_COMPLETED, checkpoint)

    # Early stopping
    early_stop = EarlyStopping(
        patience=10,
        score_function=lambda e: evaluator.state.metrics["acc"],
        trainer=trainer
    )
    evaluator.on(Events.EPOCH_COMPLETED, early_stop)

    # Run training
    trainer.run(train_loader, max_epochs=cfg.train.epochs)

    # Save final model
    model_artifact = Track.Artifact(f"{cfg.project}-final", type="model")
    torch.save(model.state_dict(), "final_model.pt")
    model_artifact.add_file("final_model.pt")
    run.log_artifact(model_artifact)

print("Training completed!")
cache.cleanup()
```

---

## 9. References & Inspirations

**OmegaConf:**
- Hierarchical configs: https://omegaconf.readthedocs.io/
- CLI overrides via dotlist
- Interpolation and resolvers

**W&B (wandb):**
- Local-first logging: https://docs.wandb.ai/
- Artifact lineage tracking
- Hyperparameter sweeps

**PyTorch Ignite:**
- Event-driven training: https://pytorch-ignite.ai/
- Reusable handlers
- Composable engines

**Existing Simple Infrastructure:**
- SDN format: `src/sdn/`
- Mmap: `src/runtime/src/value/file_io/mmap.rs`
- Async loading: `src/runtime/src/value/file_io/async_file.rs`
- Concurrent structures: `src/runtime/src/concurrent/`

---

## 10. Next Steps

1. **Review & Feedback** - Gather team input on design
2. **Prototype Cache System** - Implement basic `CacheManager`
3. **Validation POC** - Build proof-of-concept validator
4. **Integration Tests** - Test with real training workflows
5. **Documentation** - User guide and API docs
6. **Benchmark** - Compare performance vs baseline

---

**Author:** Claude Code
**Last Updated:** 2026-01-10
**Status:** Awaiting Review
