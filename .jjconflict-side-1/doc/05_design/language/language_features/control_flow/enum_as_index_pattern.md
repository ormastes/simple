# Enum as Index Pattern - Design and Examples

**Feature ID**: #194
**Pattern**: Using enums as compile-time indices for type parameters
**Date**: 2026-01-10

---

## Pattern Overview

Using enums as **const type parameters** to select specific variants at compile time.

```simple
# Define enum with variants
enum GpuIndex:
    Gpu0 | Gpu1 | Gpu2 | Gpu3

# Use enum as const type parameter
struct Gpu[T, const idx: GpuIndex]:
    value: T
    device: GpuIndex  # Runtime storage

# Each instantiation is a distinct type
Gpu[Int, GpuIndex::Gpu0]  # Type 1
Gpu[Int, GpuIndex::Gpu1]  # Type 2 (different from Type 1!)
```

**Key Insight**: The enum value becomes part of the **type**, not just runtime data.

---

## Example 1: Basic Enum Definition and Usage

```simple
"""
Demonstrates enum definition and using enum as index.
"""

# ============================================================================
# Step 1: Define Enum for Device Selection
# ============================================================================

enum GpuIndex:
    """Enum representing GPU device indices."""
    Gpu0
    Gpu1
    Gpu2
    Gpu3

    # Helper methods
    fn to_int(self) -> Int:
        """Convert enum to integer."""
        match self:
            case GpuIndex::Gpu0: 0
            case GpuIndex::Gpu1: 1
            case GpuIndex::Gpu2: 2
            case GpuIndex::Gpu3: 3

    fn name(self) -> String:
        """Get device name."""
        match self:
            case GpuIndex::Gpu0: "GPU 0"
            case GpuIndex::Gpu1: "GPU 1"
            case GpuIndex::Gpu2: "GPU 2"
            case GpuIndex::Gpu3: "GPU 3"

# ============================================================================
# Step 2: Use Enum as Const Type Parameter
# ============================================================================

struct Gpu[T, const idx: GpuIndex]:
    """
    Generic GPU computation wrapper.

    Type parameters:
    - T: The value type (e.g., DeviceInt, Tensor)
    - idx: CONST enum selecting which GPU (compile-time)
    """
    value: T
    device: GpuIndex  # Runtime storage of the same index

    fn new(val: T) -> Gpu[T, idx]:
        Gpu(
            value: val,
            device: idx  # idx is available as const value
        )

    fn get(self) -> T:
        self.value

    fn device_id(self) -> Int:
        self.device.to_int()

    fn device_name(self) -> String:
        self.device.name()

# ============================================================================
# Step 3: Using Enum-Indexed Types
# ============================================================================

fn example_basic_usage():
    print("=== Example 1: Basic Enum Index Usage ===\n")

    # Create value on GPU 0
    # Type: Gpu[Int, GpuIndex::Gpu0]
    let gpu0_val: Gpu[Int, GpuIndex::Gpu0] = Gpu.new(42)

    print(f"Created on {gpu0_val.device_name()}")
    print(f"Device ID: {gpu0_val.device_id()}")
    print(f"Value: {gpu0_val.get()}\n")

    # Create value on GPU 1
    # Type: Gpu[Int, GpuIndex::Gpu1] - DIFFERENT TYPE!
    let gpu1_val: Gpu[Int, GpuIndex::Gpu1] = Gpu.new(100)

    print(f"Created on {gpu1_val.device_name()}")
    print(f"Device ID: {gpu1_val.device_id()}")
    print(f"Value: {gpu1_val.get()}\n")

    # ❌ Type error: cannot assign different GPU types
    # let x: Gpu[Int, GpuIndex::Gpu0] = gpu1_val  # ERROR!
    print("✅ Type system prevents mixing GPU 0 and GPU 1 values")
```

**Output:**
```
=== Example 1: Basic Enum Index Usage ===

Created on GPU 0
Device ID: 0
Value: 42

Created on GPU 1
Device ID: 1
Value: 100

✅ Type system prevents mixing GPU 0 and GPU 1 values
```

---

## Example 2: Enum Index for Type Safety

```simple
"""
Demonstrates how enum indices provide compile-time type safety.
"""

# Custom type
struct DeviceInt:
    value: Int
    fn new(v: Int) -> DeviceInt:
        DeviceInt(value: v)
    fn get(self) -> Int:
        self.value

# ============================================================================
# Device-Specific Operations (Compile-Time Dispatch)
# ============================================================================

fn compute_on_gpu0(val: Gpu[DeviceInt, GpuIndex::Gpu0]) -> Gpu[DeviceInt, GpuIndex::Gpu0]:
    """
    Function ONLY accepts GPU 0 values.
    Type signature enforces this at compile time.
    """
    print("Computing on GPU 0 (using GPU 0 kernels)")
    Gpu.new(DeviceInt.new(val.get().get() + 10))

fn compute_on_gpu1(val: Gpu[DeviceInt, GpuIndex::Gpu1]) -> Gpu[DeviceInt, GpuIndex::Gpu1]:
    """
    Function ONLY accepts GPU 1 values.
    Different implementation for GPU 1.
    """
    print("Computing on GPU 1 (using GPU 1 kernels)")
    Gpu.new(DeviceInt.new(val.get().get() * 2))

fn example_type_safety():
    print("\n=== Example 2: Type Safety with Enum Index ===\n")

    let data: DeviceInt = DeviceInt.new(50)

    # Place on GPU 0
    let gpu0_val: Gpu[DeviceInt, GpuIndex::Gpu0] = Gpu.new(data)
    let result0 = compute_on_gpu0(gpu0_val)
    print(f"GPU 0 result: {result0.get().get()}\n")

    # Place on GPU 1
    let gpu1_val: Gpu[DeviceInt, GpuIndex::Gpu1] = Gpu.new(data)
    let result1 = compute_on_gpu1(gpu1_val)
    print(f"GPU 1 result: {result1.get().get()}\n")

    # ❌ Type error: wrong GPU index
    # compute_on_gpu0(gpu1_val)  # ERROR: Expected Gpu0, found Gpu1
    print("❌ ERROR: compute_on_gpu0(gpu1_val)")
    print("   Expected: Gpu[DeviceInt, GpuIndex::Gpu0]")
    print("   Found:    Gpu[DeviceInt, GpuIndex::Gpu1]")
```

**Output:**
```
=== Example 2: Type Safety with Enum Index ===

Computing on GPU 0 (using GPU 0 kernels)
GPU 0 result: 60

Computing on GPU 1 (using GPU 1 kernels)
GPU 1 result: 100

❌ ERROR: compute_on_gpu0(gpu1_val)
   Expected: Gpu[DeviceInt, GpuIndex::Gpu0]
   Found:    Gpu[DeviceInt, GpuIndex::Gpu1]
```

---

## Example 3: Generic Functions with Enum Bounds

```simple
"""
Demonstrates generic functions that work across different enum indices.
"""

# ============================================================================
# Generic over Enum Index
# ============================================================================

fn transfer_to_gpu0[T, const src_idx: GpuIndex](
    src: Gpu[T, src_idx]
) -> Gpu[T, GpuIndex::Gpu0]:
    """
    Transfer from ANY GPU to GPU 0.
    Generic over source index, concrete output index.
    """
    print(f"Transfer: {src.device_name()} → GPU 0")
    Gpu.new(src.get())

fn transfer_to_gpu1[T, const src_idx: GpuIndex](
    src: Gpu[T, src_idx]
) -> Gpu[T, GpuIndex::Gpu1]:
    """
    Transfer from ANY GPU to GPU 1.
    """
    print(f"Transfer: {src.device_name()} → GPU 1")
    Gpu.new(src.get())

fn transfer_between[T, const src: GpuIndex, const dst: GpuIndex](
    src_val: Gpu[T, src]
) -> Gpu[T, dst]:
    """
    Transfer between ANY two GPUs.
    Generic over both source and destination.
    """
    print(f"Transfer: GPU {src.to_int()} → GPU {dst.to_int()}")
    Gpu.new(src_val.get())

fn example_generic_transfer():
    print("\n=== Example 3: Generic Transfer Functions ===\n")

    let data: DeviceInt = DeviceInt.new(42)

    # Create on GPU 2
    let gpu2_val: Gpu[DeviceInt, GpuIndex::Gpu2] = Gpu.new(data)
    print(f"Created on {gpu2_val.device_name()}\n")

    # Transfer GPU 2 → GPU 0 (using generic function)
    let gpu0_val: Gpu[DeviceInt, GpuIndex::Gpu0] = transfer_to_gpu0(gpu2_val)
    print(f"Now on {gpu0_val.device_name()}\n")

    # Transfer GPU 0 → GPU 1
    let gpu1_val: Gpu[DeviceInt, GpuIndex::Gpu1] = transfer_to_gpu1(gpu0_val)
    print(f"Now on {gpu1_val.device_name()}\n")

    # Transfer GPU 1 → GPU 3 (fully generic)
    let gpu3_val: Gpu[DeviceInt, GpuIndex::Gpu3] =
        transfer_between[DeviceInt, GpuIndex::Gpu1, GpuIndex::Gpu3](gpu1_val)
    print(f"Now on {gpu3_val.device_name()}")
```

**Output:**
```
=== Example 3: Generic Transfer Functions ===

Created on GPU 2

Transfer: GPU 2 → GPU 0
Now on GPU 0

Transfer: GPU 0 → GPU 1
Now on GPU 1

Transfer: GPU 1 → GPU 3
Now on GPU 3
```

---

## Example 4: Pattern Matching on Enum Runtime Values

```simple
"""
Demonstrates pattern matching on enum values (runtime dispatch).
"""

# ============================================================================
# Runtime Device Selection
# ============================================================================

fn get_device_strategy(idx: GpuIndex) -> String:
    """
    Runtime pattern matching on enum value.
    """
    match idx:
        case GpuIndex::Gpu0:
            "High-performance compute GPU"
        case GpuIndex::Gpu1:
            "Memory-optimized GPU"
        case GpuIndex::Gpu2:
            "Inference-specialized GPU"
        case GpuIndex::Gpu3:
            "General-purpose GPU"

fn select_optimal_gpu(workload_size: Int) -> GpuIndex:
    """
    Runtime logic to select GPU based on workload.
    Returns enum value.
    """
    if workload_size < 1000:
        GpuIndex::Gpu3  # Small workload → general GPU
    else if workload_size < 10000:
        GpuIndex::Gpu1  # Medium workload → memory GPU
    else:
        GpuIndex::Gpu0  # Large workload → high-performance GPU

fn example_runtime_dispatch():
    print("\n=== Example 4: Runtime Enum Dispatch ===\n")

    let workloads = [500, 5000, 50000]

    for size in workloads:
        let selected: GpuIndex = select_optimal_gpu(size)
        let strategy = get_device_strategy(selected)

        print(f"Workload size: {size}")
        print(f"  Selected: {selected.name()}")
        print(f"  Strategy: {strategy}\n")
```

**Output:**
```
=== Example 4: Runtime Enum Dispatch ===

Workload size: 500
  Selected: GPU 3
  Strategy: General-purpose GPU

Workload size: 5000
  Selected: GPU 1
  Strategy: Memory-optimized GPU

Workload size: 50000
  Selected: GPU 0
  Strategy: High-performance compute GPU
```

---

## Example 5: Multi-GPU Array with Enum Indexing

```simple
"""
Demonstrates array of values on different GPUs, indexed by enum.
"""

# ============================================================================
# Multi-GPU Storage
# ============================================================================

struct MultiGpuArray[T]:
    """
    Array distributed across 4 GPUs.
    Each element knows its GPU via enum index.
    """
    gpu0: Gpu[T, GpuIndex::Gpu0]
    gpu1: Gpu[T, GpuIndex::Gpu1]
    gpu2: Gpu[T, GpuIndex::Gpu2]
    gpu3: Gpu[T, GpuIndex::Gpu3]

    fn new(v0: T, v1: T, v2: T, v3: T) -> MultiGpuArray[T]:
        MultiGpuArray(
            gpu0: Gpu.new(v0),
            gpu1: Gpu.new(v1),
            gpu2: Gpu.new(v2),
            gpu3: Gpu.new(v3)
        )

    fn get(self, idx: GpuIndex) -> Int:
        """
        Runtime indexing using enum value.
        Pattern match to select the right GPU.
        """
        match idx:
            case GpuIndex::Gpu0:
                self.gpu0.get().get()
            case GpuIndex::Gpu1:
                self.gpu1.get().get()
            case GpuIndex::Gpu2:
                self.gpu2.get().get()
            case GpuIndex::Gpu3:
                self.gpu3.get().get()

    fn sum(self) -> Int:
        """Sum values across all GPUs."""
        self.gpu0.get().get() +
        self.gpu1.get().get() +
        self.gpu2.get().get() +
        self.gpu3.get().get()

fn example_multi_gpu_array():
    print("\n=== Example 5: Multi-GPU Array ===\n")

    # Create distributed array
    let arr: MultiGpuArray[DeviceInt] = MultiGpuArray.new(
        DeviceInt.new(10),  # GPU 0
        DeviceInt.new(20),  # GPU 1
        DeviceInt.new(30),  # GPU 2
        DeviceInt.new(40)   # GPU 3
    )

    # Access by enum index (runtime)
    print("Array contents:")
    for i in [0, 1, 2, 3]:
        let idx = match i:
            case 0: GpuIndex::Gpu0
            case 1: GpuIndex::Gpu1
            case 2: GpuIndex::Gpu2
            case 3: GpuIndex::Gpu3
            case _: GpuIndex::Gpu0

        let val = arr.get(idx)
        print(f"  {idx.name()}: {val}")

    # Compute across all GPUs
    let total = arr.sum()
    print(f"\nTotal sum: {total}")
```

**Output:**
```
=== Example 5: Multi-GPU Array ===

Array contents:
  GPU 0: 10
  GPU 1: 20
  GPU 2: 30
  GPU 3: 40

Total sum: 100
```

---

## Example 6: Compile-Time vs Runtime Enum Usage

```simple
"""
Demonstrates the difference between compile-time and runtime enum usage.
"""

fn example_compile_vs_runtime():
    print("\n=== Example 6: Compile-Time vs Runtime ===\n")

    # ────────────────────────────────────────────────────────────
    # COMPILE-TIME: Enum in type parameter (const idx)
    # ────────────────────────────────────────────────────────────
    print("Compile-time enum usage:")

    # These are DIFFERENT TYPES determined at compile time
    let gpu0: Gpu[Int, GpuIndex::Gpu0] = Gpu.new(42)
    let gpu1: Gpu[Int, GpuIndex::Gpu1] = Gpu.new(100)

    print(f"  gpu0 type: Gpu[Int, GpuIndex::Gpu0]")
    print(f"  gpu1 type: Gpu[Int, GpuIndex::Gpu1]")
    print(f"  → Different types at compile time!\n")

    # ────────────────────────────────────────────────────────────
    # RUNTIME: Enum as regular value
    # ────────────────────────────────────────────────────────────
    print("Runtime enum usage:")

    # Select device at runtime
    let runtime_choice: GpuIndex = if some_condition():
        GpuIndex::Gpu0
    else:
        GpuIndex::Gpu1

    print(f"  runtime_choice = {runtime_choice.name()}")
    print(f"  → Value determined at runtime\n")

    # ────────────────────────────────────────────────────────────
    # BOTH: Compile-time type + Runtime value
    # ────────────────────────────────────────────────────────────
    print("Both compile-time and runtime:")

    # Compile-time: Type Gpu[Int, GpuIndex::Gpu0]
    # Runtime: device field stores GpuIndex::Gpu0
    let val: Gpu[Int, GpuIndex::Gpu0] = Gpu.new(42)

    print(f"  Compile-time type: Gpu[Int, GpuIndex::Gpu0]")
    print(f"  Runtime device value: {val.device.name()}")
    print(f"  → Both levels working together!")

fn some_condition() -> Bool:
    true
```

**Output:**
```
=== Example 6: Compile-Time vs Runtime ===

Compile-time enum usage:
  gpu0 type: Gpu[Int, GpuIndex::Gpu0]
  gpu1 type: Gpu[Int, GpuIndex::Gpu1]
  → Different types at compile time!

Runtime enum usage:
  runtime_choice = GPU 0
  → Value determined at runtime

Both compile-time and runtime:
  Compile-time type: Gpu[Int, GpuIndex::Gpu0]
  Runtime device value: GPU 0
  → Both levels working together!
```

---

## Example 7: Advanced - Enum as Lookup Key

```simple
"""
Advanced pattern: Using enum to build type-safe lookup tables.
"""

# ============================================================================
# GPU Configuration Table
# ============================================================================

struct GpuConfig:
    memory_gb: Int
    cores: Int
    bandwidth_gbps: Int

fn get_gpu_config(idx: GpuIndex) -> GpuConfig:
    """
    Lookup table using enum as key.
    Each GPU has different specs.
    """
    match idx:
        case GpuIndex::Gpu0:
            GpuConfig(memory_gb: 80, cores: 10752, bandwidth_gbps: 2000)
        case GpuIndex::Gpu1:
            GpuConfig(memory_gb: 48, cores: 6912, bandwidth_gbps: 1200)
        case GpuIndex::Gpu2:
            GpuConfig(memory_gb: 24, cores: 3584, bandwidth_gbps: 600)
        case GpuIndex::Gpu3:
            GpuConfig(memory_gb: 12, cores: 1920, bandwidth_gbps: 300)

fn example_enum_lookup():
    print("\n=== Example 7: Enum as Lookup Key ===\n")

    print("GPU Specifications:")
    for i in [0, 1, 2, 3]:
        let idx = match i:
            case 0: GpuIndex::Gpu0
            case 1: GpuIndex::Gpu1
            case 2: GpuIndex::Gpu2
            case 3: GpuIndex::Gpu3
            case _: GpuIndex::Gpu0

        let config = get_gpu_config(idx)
        print(f"  {idx.name()}:")
        print(f"    Memory: {config.memory_gb} GB")
        print(f"    Cores: {config.cores}")
        print(f"    Bandwidth: {config.bandwidth_gbps} GB/s")
```

**Output:**
```
=== Example 7: Enum as Lookup Key ===

GPU Specifications:
  GPU 0:
    Memory: 80 GB
    Cores: 10752
    Bandwidth: 2000 GB/s
  GPU 1:
    Memory: 48 GB
    Cores: 6912
    Bandwidth: 1200 GB/s
  GPU 2:
    Memory: 24 GB
    Cores: 3584
    Bandwidth: 600 GB/s
  GPU 3:
    Memory: 12 GB
    Cores: 1920
    Bandwidth: 300 GB/s
```

---

## Summary: Enum as Index Pattern

### Key Concepts

1. **Compile-Time Index**
   ```simple
   struct Gpu[T, const idx: GpuIndex]
   #              ^^^^^ const = compile-time
   ```

2. **Type-Level Distinction**
   ```simple
   Gpu[Int, GpuIndex::Gpu0]  # Type A
   Gpu[Int, GpuIndex::Gpu1]  # Type B (different!)
   ```

3. **Runtime Value Storage**
   ```simple
   struct Gpu[T, const idx: GpuIndex]:
       device: GpuIndex  # Runtime storage
   ```

4. **Pattern Matching**
   ```simple
   match device:
       case GpuIndex::Gpu0: ...
       case GpuIndex::Gpu1: ...
   ```

### Usage Patterns

| Pattern | Example | Purpose |
|---------|---------|---------|
| **Type parameter** | `Gpu[T, const idx]` | Compile-time type safety |
| **Runtime value** | `let x: GpuIndex = Gpu0` | Runtime dispatch |
| **Function param** | `fn f(idx: GpuIndex)` | Dynamic selection |
| **Pattern match** | `match idx: case Gpu0:` | Branching logic |
| **Generic bound** | `fn f[const idx: GpuIndex]()` | Generic over index |

### Benefits

✅ **Type Safety** - Compiler catches wrong GPU usage
✅ **Clear Intent** - Type shows which GPU explicitly
✅ **Zero Runtime Cost** - Compile-time only
✅ **Flexible** - Works compile-time AND runtime
✅ **Exhaustive** - Pattern matching ensures all cases handled

---

**Prepared by**: Claude Code Assistant
**Date**: 2026-01-10
**Pattern**: Enum as Compile-Time Index for Type Parameters
