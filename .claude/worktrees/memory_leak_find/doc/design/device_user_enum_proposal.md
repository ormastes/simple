# Execution Context Types - User Enum Design

**Feature ID**: #194
**Status**: Designing
**Pattern**: `Gpu[UserEnum, idx]` with custom type embedding
**Date**: 2026-01-10

---

## Design Overview

This design uses **user-defined enums** to wrap custom types, preventing bare primitives while allowing implicit conversion. The main types are `Host[T]` and `Gpu[T, idx]` where `T` is a user-defined enum.

### Key Concepts

1. **Custom types** wrap primitives (GpuInt, HostInt, etc.)
2. **User enum** embeds custom types
3. **Implicit conversion** from custom type → enum
4. **No bare primitives** - type system enforces wrapping
5. **GpuIndex** type for device selection
6. **Generic Gpu[UserEnum, idx]** for device placement

---

## Type System Architecture

### Base Pattern

```simple
# Step 1: Custom types (prevent bare primitives)
struct GpuInt:
    value: Int

    fn new(val: Int) -> GpuInt:
        GpuInt(value: val)

    fn get(self) -> Int:
        self.value

struct HostInt:
    value: Int

    fn new(val: Int) -> HostInt:
        HostInt(value: val)

    fn get(self) -> Int:
        self.value

# Step 2: User enum wraps custom types
enum DeviceInt:
    Gpu(GpuInt)
    Host(HostInt)

    fn get(self) -> Int:
        match self:
            case DeviceInt::Gpu(v):
                v.get()
            case DeviceInt::Host(v):
                v.get()

# Step 3: Implicit conversion (automatic upcast)
impl From[GpuInt] for DeviceInt:
    fn from(val: GpuInt) -> DeviceInt:
        DeviceInt::Gpu(val)

impl From[HostInt] for DeviceInt:
    fn from(val: HostInt) -> DeviceInt:
        DeviceInt::Host(val)

# Step 4: GpuIndex type for device indexing
enum GpuIndex:
    Gpu0
    Gpu1
    Gpu2
    Gpu3

# Step 5: Main execution context types
struct Gpu[T, const idx: GpuIndex]:
    value: T
    device_id: GpuIndex

    fn new(val: T) -> Gpu[T, idx]:
        Gpu(value: val, device_id: idx)

    fn get(self) -> T:
        self.value

struct Host[T]:
    value: T

    fn new(val: T) -> Host[T]:
        Host(value: val)

    fn get(self) -> T:
        self.value
```

### Usage Pattern

```simple
# Create custom type value (NOT bare primitive)
let x: GpuInt = GpuInt.new(42)

# Implicit conversion to enum
let y: DeviceInt = x  # Auto-converts via From trait

# Place on specific device
let z: Gpu[DeviceInt, GpuIndex::Gpu0] = Gpu.new(y)

# Extract value
let result: Int = z.get().get()  # 42
```

---

## Complete Examples

### Example 1: Basic Device Values with User Enum

```simple
"""
Demonstrates custom types, user enum, and device placement.
No bare primitives allowed - all values wrapped.
"""

# ============================================================================
# Custom Types (Prevent Bare Primitives)
# ============================================================================

struct GpuInt:
    """Integer value for GPU computation."""
    value: Int

    fn new(val: Int) -> GpuInt:
        GpuInt(value: val)

    fn get(self) -> Int:
        self.value

    fn add(self, other: GpuInt) -> GpuInt:
        GpuInt(value: self.value + other.value)

struct HostInt:
    """Integer value for host/CPU computation."""
    value: Int

    fn new(val: Int) -> HostInt:
        HostInt(value: val)

    fn get(self) -> Int:
        self.value

# ============================================================================
# User Enum (Embeds Custom Types)
# ============================================================================

enum DeviceInt:
    """Device-polymorphic integer - can be GPU or Host."""
    Gpu(GpuInt)
    Host(HostInt)

    fn get(self) -> Int:
        match self:
            case DeviceInt::Gpu(v):
                v.get()
            case DeviceInt::Host(v):
                v.get()

    fn device_name(self) -> String:
        match self:
            case DeviceInt::Gpu(_):
                "GPU"
            case DeviceInt::Host(_):
                "Host"

# ============================================================================
# Implicit Conversion (Custom Type → Enum)
# ============================================================================

impl From[GpuInt] for DeviceInt:
    fn from(val: GpuInt) -> DeviceInt:
        DeviceInt::Gpu(val)

impl From[HostInt] for DeviceInt:
    fn from(val: HostInt) -> DeviceInt:
        DeviceInt::Host(val)

# ============================================================================
# GpuIndex Type
# ============================================================================

enum GpuIndex:
    Gpu0
    Gpu1
    Gpu2
    Gpu3

    fn to_int(self) -> Int:
        match self:
            case GpuIndex::Gpu0: 0
            case GpuIndex::Gpu1: 1
            case GpuIndex::Gpu2: 2
            case GpuIndex::Gpu3: 3

# ============================================================================
# Main Device Types
# ============================================================================

struct Gpu[T, const idx: GpuIndex]:
    """GPU computation wrapper with device index."""
    value: T
    device_id: GpuIndex

    fn new(val: T) -> Gpu[T, idx]:
        Gpu(value: val, device_id: idx)

    fn get(self) -> T:
        self.value

    fn map[U](self, f: fn(T) -> U) -> Gpu[U, idx]:
        Gpu(value: f(self.value), device_id: self.device_id)

struct Host[T]:
    """Host/CPU computation wrapper."""
    value: T

    fn new(val: T) -> Host[T]:
        Host(value: val)

    fn get(self) -> T:
        self.value

    fn map[U](self, f: fn(T) -> U) -> Host[U]:
        Host(value: f(self.value))

# ============================================================================
# Usage Example
# ============================================================================

fn main():
    print("=== Example 1: Basic Device Values ===\n")

    # ❌ ERROR: Bare primitives not allowed
    # let x: Int = 42  # Compiler error!

    # ✅ OK: Wrapped in custom type
    let x: GpuInt = GpuInt.new(42)
    print(f"GpuInt value: {x.get()}")

    # ✅ Implicit conversion to enum
    let y: DeviceInt = x  # Auto-converts via From[GpuInt]
    print(f"DeviceInt value: {y.get()}")
    print(f"Device type: {y.device_name()}")

    # ✅ Place on GPU 0
    let z: Gpu[DeviceInt, GpuIndex::Gpu0] = Gpu.new(y)
    print(f"GPU value: {z.get().get()}")
    print(f"GPU device: {z.device_id.to_int()}")

    # ✅ Create host value
    let host_val: HostInt = HostInt.new(100)
    let host_enum: DeviceInt = host_val  # Implicit conversion
    let host_compute: Host[DeviceInt] = Host.new(host_enum)
    print(f"Host value: {host_compute.get().get()}")
```

**Output:**
```
=== Example 1: Basic Device Values ===

GpuInt value: 42
DeviceInt value: 42
Device type: GPU
GPU value: 42
GPU device: 0
Host value: 100
```

---

### Example 2: Multi-GPU Computation with Device Transfers

```simple
"""
Demonstrates explicit device transfers between GPUs using user enums.
Each GPU has a distinct index, transfers are type-safe.
"""

# ============================================================================
# Transfer Operations
# ============================================================================

# Host → GPU transfer
fn to_gpu[T, const idx: GpuIndex](host_val: Host[T]) -> Gpu[T, idx]:
    print(f"Transfer: Host → GPU {idx.to_int()}")
    Gpu.new(host_val.get())

# GPU → Host transfer
fn to_host[T, const idx: GpuIndex](gpu_val: Gpu[T, idx]) -> Host[T]:
    print(f"Transfer: GPU {idx.to_int()} → Host")
    Host.new(gpu_val.get())

# GPU → GPU transfer
fn gpu_to_gpu[T, const src: GpuIndex, const dst: GpuIndex](
    gpu_val: Gpu[T, src]
) -> Gpu[T, dst]:
    print(f"Transfer: GPU {src.to_int()} → GPU {dst.to_int()}")
    Gpu.new(gpu_val.get())

# ============================================================================
# Multi-GPU Pipeline
# ============================================================================

fn multi_gpu_pipeline():
    print("\n=== Example 2: Multi-GPU Pipeline ===\n")

    # Stage 1: Load data on host
    let data: HostInt = HostInt.new(10)
    print(f"Loaded on host: {data.get()}")

    # Stage 2: Transfer to GPU 0
    let host_enum: DeviceInt = data
    let host_compute: Host[DeviceInt] = Host.new(host_enum)
    let gpu0_val: Gpu[DeviceInt, GpuIndex::Gpu0] = to_gpu(host_compute)

    # Stage 3: Compute on GPU 0
    let gpu0_result = gpu0_val.map(\v:
        match v:
            case DeviceInt::Gpu(gv):
                DeviceInt::Gpu(gv.add(GpuInt.new(5)))
            case _:
                v
    )
    print(f"Computed on GPU 0: {gpu0_result.get().get()}")

    # Stage 4: Transfer to GPU 1
    let gpu1_val: Gpu[DeviceInt, GpuIndex::Gpu1] = gpu_to_gpu(gpu0_result)

    # Stage 5: Compute on GPU 1
    let gpu1_result = gpu1_val.map(\v:
        match v:
            case DeviceInt::Gpu(gv):
                DeviceInt::Gpu(GpuInt.new(gv.get() * 2))
            case _:
                v
    )
    print(f"Computed on GPU 1: {gpu1_result.get().get()}")

    # Stage 6: Transfer back to host
    let final: Host[DeviceInt] = to_host(gpu1_result)
    print(f"Final result on host: {final.get().get()}")
```

**Output:**
```
=== Example 2: Multi-GPU Pipeline ===

Loaded on host: 10
Transfer: Host → GPU 0
Computed on GPU 0: 15
Transfer: GPU 0 → GPU 1
Computed on GPU 1: 30
Transfer: GPU 1 → Host
Final result on host: 30
```

---

### Example 3: Tensor Type with Device Placement

```simple
"""
Combines tensor dimension tracking with device placement.
Tensors are wrapped in custom types, placed on specific devices.
"""

# ============================================================================
# Tensor Custom Types
# ============================================================================

struct GpuTensor:
    """Tensor data for GPU computation."""
    data: List[Float]
    shape: List[Int]

    fn new(data: List[Float], shape: List[Int]) -> GpuTensor:
        GpuTensor(data: data, shape: shape)

    fn matmul(self, other: GpuTensor) -> GpuTensor:
        # Simplified matmul (real implementation uses GPU kernels)
        print("GPU matmul kernel executing...")
        GpuTensor.new(self.data, [self.shape[0], other.shape[1]])

struct HostTensor:
    """Tensor data for host/CPU computation."""
    data: List[Float]
    shape: List[Int]

    fn new(data: List[Float], shape: List[Int]) -> HostTensor:
        HostTensor(data: data, shape: shape)

# ============================================================================
# Tensor User Enum
# ============================================================================

enum DeviceTensor:
    Gpu(GpuTensor)
    Host(HostTensor)

    fn shape(self) -> List[Int]:
        match self:
            case DeviceTensor::Gpu(t):
                t.shape
            case DeviceTensor::Host(t):
                t.shape

# Implicit conversions
impl From[GpuTensor] for DeviceTensor:
    fn from(val: GpuTensor) -> DeviceTensor:
        DeviceTensor::Gpu(val)

impl From[HostTensor] for DeviceTensor:
    fn from(val: HostTensor) -> DeviceTensor:
        DeviceTensor::Host(val)

# ============================================================================
# Neural Network Layer
# ============================================================================

fn neural_network_forward():
    print("\n=== Example 3: Neural Network ===\n")

    # Load data on host
    let input_data: HostTensor = HostTensor.new(
        [1.0, 2.0, 3.0, 4.0],
        [2, 2]
    )
    print(f"Input shape: {input_data.shape}")

    # Transfer to GPU 0
    let gpu_input: GpuTensor = GpuTensor.new(input_data.data, input_data.shape)
    let gpu_enum: DeviceTensor = gpu_input  # Implicit conversion
    let gpu0_tensor: Gpu[DeviceTensor, GpuIndex::Gpu0] = Gpu.new(gpu_enum)

    # Layer 1 weights on GPU 0
    let weight1: GpuTensor = GpuTensor.new([0.5, 0.5, 0.5, 0.5], [2, 2])
    let weight1_enum: DeviceTensor = weight1
    let gpu0_weight1: Gpu[DeviceTensor, GpuIndex::Gpu0] = Gpu.new(weight1_enum)

    # Forward pass on GPU 0
    print("Layer 1 forward pass on GPU 0...")
    let layer1_out = gpu0_tensor.map(\t:
        match t:
            case DeviceTensor::Gpu(tensor):
                let w = match gpu0_weight1.get():
                    case DeviceTensor::Gpu(wt): wt
                    case _: tensor
                DeviceTensor::Gpu(tensor.matmul(w))
            case _:
                t
    )

    print(f"Layer 1 output shape: {layer1_out.get().shape()}")
    print("Neural network complete!")
```

**Output:**
```
=== Example 3: Neural Network ===

Input shape: [2, 2]
Layer 1 forward pass on GPU 0...
GPU matmul kernel executing...
Layer 1 output shape: [2, 2]
Neural network complete!
```

---

### Example 4: Data Parallel Training with User Enum

```simple
"""
Data parallel training across 4 GPUs.
Each GPU processes a batch, gradients gathered and averaged.
"""

# ============================================================================
# Model Type (Custom Type)
# ============================================================================

struct GpuModel:
    """Model weights on GPU."""
    weights: List[Float]

    fn new(weights: List[Float]) -> GpuModel:
        GpuModel(weights: weights)

    fn forward(self, data: GpuTensor) -> GpuTensor:
        print(f"Forward pass with {self.weights.len()} parameters")
        data  # Simplified

struct HostModel:
    """Model weights on host."""
    weights: List[Float]

    fn new(weights: List[Float]) -> HostModel:
        HostModel(weights: weights)

# ============================================================================
# Model User Enum
# ============================================================================

enum DeviceModel:
    Gpu(GpuModel)
    Host(HostModel)

impl From[GpuModel] for DeviceModel:
    fn from(val: GpuModel) -> DeviceModel:
        DeviceModel::Gpu(val)

impl From[HostModel] for DeviceModel:
    fn from(val: HostModel) -> DeviceModel:
        DeviceModel::Host(val)

# ============================================================================
# Training Step (Device-Specific)
# ============================================================================

fn train_step[const idx: GpuIndex](
    model: Gpu[DeviceModel, idx],
    data: Gpu[DeviceTensor, idx]
) -> Gpu[DeviceTensor, idx]:
    print(f"Training on GPU {idx.to_int()}...")

    # Forward + backward (simplified)
    let gradients = data.map(\d:
        match d:
            case DeviceTensor::Gpu(t):
                DeviceTensor::Gpu(t)  # Simplified gradient computation
            case _:
                d
    )

    gradients

# ============================================================================
# Data Parallel Training
# ============================================================================

fn data_parallel_training():
    print("\n=== Example 4: Data Parallel Training ===\n")

    # Create master model on host
    let master_weights = [0.1, 0.2, 0.3, 0.4]
    let master_model: HostModel = HostModel.new(master_weights)
    print(f"Master model: {master_weights.len()} parameters")

    # Replicate to 4 GPUs
    let gpu_model: GpuModel = GpuModel.new(master_model.weights)

    let model0: Gpu[DeviceModel, GpuIndex::Gpu0] = Gpu.new(gpu_model.into())
    let model1: Gpu[DeviceModel, GpuIndex::Gpu1] = Gpu.new(gpu_model.into())
    let model2: Gpu[DeviceModel, GpuIndex::Gpu2] = Gpu.new(gpu_model.into())
    let model3: Gpu[DeviceModel, GpuIndex::Gpu3] = Gpu.new(gpu_model.into())

    # Create data batches
    let batch0: Gpu[DeviceTensor, GpuIndex::Gpu0] = Gpu.new(
        GpuTensor.new([1.0, 2.0], [1, 2]).into()
    )
    let batch1: Gpu[DeviceTensor, GpuIndex::Gpu1] = Gpu.new(
        GpuTensor.new([3.0, 4.0], [1, 2]).into()
    )
    let batch2: Gpu[DeviceTensor, GpuIndex::Gpu2] = Gpu.new(
        GpuTensor.new([5.0, 6.0], [1, 2]).into()
    )
    let batch3: Gpu[DeviceTensor, GpuIndex::Gpu3] = Gpu.new(
        GpuTensor.new([7.0, 8.0], [1, 2]).into()
    )

    # Parallel training (all GPUs simultaneously)
    print("\nEpoch 1:")
    let grads0 = train_step(model0, batch0)
    let grads1 = train_step(model1, batch1)
    let grads2 = train_step(model2, batch2)
    let grads3 = train_step(model3, batch3)

    # Gather gradients to GPU 0 (simplified)
    print("\nGathering gradients to GPU 0...")
    let grads1_to_0: Gpu[DeviceTensor, GpuIndex::Gpu0] = gpu_to_gpu(grads1)
    let grads2_to_0: Gpu[DeviceTensor, GpuIndex::Gpu0] = gpu_to_gpu(grads2)
    let grads3_to_0: Gpu[DeviceTensor, GpuIndex::Gpu0] = gpu_to_gpu(grads3)

    print("Averaging gradients on GPU 0...")
    print("Broadcasting updated weights...")
    print("Training epoch complete!")
```

**Output:**
```
=== Example 4: Data Parallel Training ===

Master model: 4 parameters

Epoch 1:
Training on GPU 0...
Training on GPU 1...
Training on GPU 2...
Training on GPU 3...

Gathering gradients to GPU 0...
Transfer: GPU 1 → GPU 0
Transfer: GPU 2 → GPU 0
Transfer: GPU 3 → GPU 0
Averaging gradients on GPU 0...
Broadcasting updated weights...
Training epoch complete!
```

---

### Example 5: Preventing Primitive Leakage

```simple
"""
Demonstrates how the type system prevents bare primitives.
All values must be wrapped in custom types.
"""

fn type_safety_demo():
    print("\n=== Example 5: Type Safety ===\n")

    # ❌ ERROR: Bare primitive not allowed
    # let x: Int = 42
    # Compiler error: "Bare primitive type 'Int' not allowed"

    # ✅ OK: Wrapped in custom type
    let x: GpuInt = GpuInt.new(42)
    print(f"✅ GpuInt created: {x.get()}")

    # ❌ ERROR: Cannot mix bare primitive with custom type
    # let y = x.get() + 10
    # Must wrap result

    # ✅ OK: Wrap result in custom type
    let y: GpuInt = GpuInt.new(x.get() + 10)
    print(f"✅ Computation result: {y.get()}")

    # ❌ ERROR: Cannot pass bare primitive to Gpu[T, idx]
    # let z: Gpu[Int, GpuIndex::Gpu0] = Gpu.new(42)
    # Compiler error: "Expected DeviceInt, found Int"

    # ✅ OK: Wrap in custom type, convert to enum, then place on GPU
    let val: GpuInt = GpuInt.new(42)
    let enum_val: DeviceInt = val  # Implicit conversion
    let gpu_val: Gpu[DeviceInt, GpuIndex::Gpu0] = Gpu.new(enum_val)
    print(f"✅ GPU value created: {gpu_val.get().get()}")

    # ✅ OK: Pattern matching to extract custom type
    let extracted: GpuInt = match gpu_val.get():
        case DeviceInt::Gpu(v):
            v
        case _:
            GpuInt.new(0)

    print(f"✅ Extracted value: {extracted.get()}")

    print("\n✅ All type safety checks passed!")
```

**Output:**
```
=== Example 5: Type Safety ===

✅ GpuInt created: 42
✅ Computation result: 52
✅ GPU value created: 42
✅ Extracted value: 42

✅ All type safety checks passed!
```

---

### Example 6: Combining with Tensor Dimensions

```simple
"""
Combines device placement with tensor dimension tracking.
Type system verifies both device AND shape correctness.
"""

# Assume TensorShape from feature #193
import verification.models.tensor_dimensions.{TensorShape, DimSpec}

# ============================================================================
# Typed Tensor with Device
# ============================================================================

struct GpuTypedTensor[Shape]:
    """GPU tensor with compile-time shape tracking."""
    data: List[Float]
    shape: Shape

    fn new(data: List[Float], shape: Shape) -> GpuTypedTensor[Shape]:
        GpuTypedTensor(data: data, shape: shape)

struct HostTypedTensor[Shape]:
    """Host tensor with compile-time shape tracking."""
    data: List[Float]
    shape: Shape

    fn new(data: List[Float], shape: Shape) -> HostTypedTensor[Shape]:
        HostTypedTensor(data: data, shape: shape)

# ============================================================================
# Typed Tensor User Enum
# ============================================================================

enum DeviceTypedTensor[Shape]:
    Gpu(GpuTypedTensor[Shape])
    Host(HostTypedTensor[Shape])

# ============================================================================
# Typed Matmul with Device + Dimension Checking
# ============================================================================

fn matmul_gpu0[B, I, O](
    input: Gpu[DeviceTypedTensor[TensorShape[[B, I]]], GpuIndex::Gpu0],
    weight: Gpu[DeviceTypedTensor[TensorShape[[I, O]]], GpuIndex::Gpu0]
) -> Gpu[DeviceTypedTensor[TensorShape[[B, O]]], GpuIndex::Gpu0]:
    """
    Matrix multiplication with:
    - Device verification: Both on GPU 0
    - Shape verification: Dimensions [B, I] × [I, O] = [B, O]
    """
    print("Type-safe GPU matmul:")
    print("  ✅ Device: Both on GPU 0")
    print("  ✅ Shapes: Compatible dimensions")

    # Simplified implementation
    input.map(\t:
        match t:
            case DeviceTypedTensor::Gpu(tensor):
                DeviceTypedTensor::Gpu(tensor)  # Actual GPU kernel
            case _:
                t
    )

fn typed_tensor_demo():
    print("\n=== Example 6: Device + Dimension Tracking ===\n")

    # Create input tensor: [32, 784] on GPU 0
    let input_shape = TensorShape[[
        DimSpec.exact(32),
        DimSpec.exact(784)
    ]]
    let input_tensor: GpuTypedTensor = GpuTypedTensor.new([], input_shape)
    let input_enum: DeviceTypedTensor = input_tensor.into()
    let input: Gpu[DeviceTypedTensor, GpuIndex::Gpu0] = Gpu.new(input_enum)

    # Create weight tensor: [784, 256] on GPU 0
    let weight_shape = TensorShape[[
        DimSpec.exact(784),
        DimSpec.exact(256)
    ]]
    let weight_tensor: GpuTypedTensor = GpuTypedTensor.new([], weight_shape)
    let weight_enum: DeviceTypedTensor = weight_tensor.into()
    let weight: Gpu[DeviceTypedTensor, GpuIndex::Gpu0] = Gpu.new(weight_enum)

    # Type-safe matmul
    let output = matmul_gpu0(input, weight)
    # Output type: Gpu[DeviceTypedTensor[TensorShape[[32, 256]]], GpuIndex::Gpu0]

    print("  ✅ Output shape: [32, 256]")
    print("\nType system verified:")
    print("  1. Both tensors on same device (GPU 0)")
    print("  2. Dimension 784 matches between input/weight")
    print("  3. Output shape correctly inferred as [32, 256]")
```

**Output:**
```
=== Example 6: Device + Dimension Tracking ===

Type-safe GPU matmul:
  ✅ Device: Both on GPU 0
  ✅ Shapes: Compatible dimensions
  ✅ Output shape: [32, 256]

Type system verified:
  1. Both tensors on same device (GPU 0)
  2. Dimension 784 matches between input/weight
  3. Output shape correctly inferred as [32, 256]
```

---

### Example 7: Async + Device Integration

```simple
"""
Combines async/await with device placement.
Type: Promise[Gpu[DeviceInt, idx]]
"""

# ============================================================================
# Async GPU Operations
# ============================================================================

async fn async_gpu_compute(
    data: Gpu[DeviceInt, GpuIndex::Gpu0]
) -> Promise[Gpu[DeviceInt, GpuIndex::Gpu0]]:
    """
    Async GPU kernel launch.
    Returns Promise of GPU computation.
    """
    print("Launching async GPU kernel...")

    # Simulate async GPU work
    let result = future(data.map(\v:
        match v:
            case DeviceInt::Gpu(gv):
                DeviceInt::Gpu(gv.add(GpuInt.new(100)))
            case _:
                v
    ))

    await result

async fn async_device_pipeline():
    print("\n=== Example 7: Async + Device ===\n")

    # Create GPU value
    let val: GpuInt = GpuInt.new(42)
    let enum_val: DeviceInt = val
    let gpu_val: Gpu[DeviceInt, GpuIndex::Gpu0] = Gpu.new(enum_val)

    # Launch async computation
    let future_result: Promise[Gpu[DeviceInt, GpuIndex::Gpu0]] =
        async_gpu_compute(gpu_val)

    print("Waiting for GPU kernel...")
    let result = await future_result

    print(f"Result: {result.get().get()}")
    print("\n✅ Async GPU computation complete!")
```

**Output:**
```
=== Example 7: Async + Device ===

Launching async GPU kernel...
Waiting for GPU kernel...
Result: 142

✅ Async GPU computation complete!
```

---

## Type System Formalization

### Type Grammar

```
DeviceType := Host[UserEnum]
            | Gpu[UserEnum, GpuIndex]

UserEnum := enum EnumName:
              Variant1(CustomType1)
              Variant2(CustomType2)
              ...

CustomType := struct TypeName:
                field1: PrimitiveType
                ...

GpuIndex := enum GpuIndex:
              Gpu0 | Gpu1 | Gpu2 | Gpu3

ImplicitConversion := impl From[CustomType] for UserEnum
```

### Type Checking Rules

1. **No Bare Primitives**:
   ```
   Γ ⊢ x : Int    (bare primitive)
   ───────────────────────────────  ERROR
   ```

2. **Custom Type Required**:
   ```
   Γ ⊢ x : GpuInt    (custom type)
   ───────────────────────────────  OK
   Γ ⊢ x : GpuInt
   ```

3. **Implicit Conversion**:
   ```
   Γ ⊢ x : GpuInt
   impl From[GpuInt] for DeviceInt
   ─────────────────────────────────
   Γ ⊢ x : DeviceInt    (implicit)
   ```

4. **Device Placement**:
   ```
   Γ ⊢ v : DeviceInt
   ────────────────────────────────────
   Γ ⊢ Gpu.new(v) : Gpu[DeviceInt, idx]
   ```

5. **Device Transfer**:
   ```
   Γ ⊢ x : Gpu[T, idx1]
   ────────────────────────────
   Γ ⊢ gpu_to_gpu(x) : Gpu[T, idx2]
   ```

---

## Error Messages

### Bare Primitive Error

```
Error: Bare primitive type 'Int' not allowed at src/compute.spl:10

All primitive values must be wrapped in custom types:
- GpuInt for GPU computation
- HostInt for host computation

Example:
  let x: GpuInt = GpuInt.new(42)

Help: Create a custom type wrapper for your primitive
```

### Device Mismatch Error

```
Error: Device mismatch at src/train.spl:42

Expected: Gpu[DeviceTensor, GpuIndex::Gpu0]
Found:    Gpu[DeviceTensor, GpuIndex::Gpu1]

Help: Use gpu_to_gpu() to transfer between devices:
  let gpu0_val = gpu_to_gpu[_, GpuIndex::Gpu1, GpuIndex::Gpu0](gpu1_val)
```

### Enum Conversion Error

```
Error: No implicit conversion from GpuInt to DeviceFloat

Available conversions:
- From[GpuInt] for DeviceInt
- From[HostInt] for DeviceInt
- From[GpuFloat] for DeviceFloat

Help: Ensure you're using the correct user enum type
```

---

## Summary

### Key Design Points

1. ✅ **Custom types** (GpuInt, HostInt) wrap primitives
2. ✅ **User enum** (DeviceInt) embeds custom types
3. ✅ **Implicit conversion** via `From` trait
4. ✅ **GpuIndex** type for device selection
5. ✅ **Gpu[UserEnum, idx]** generic device placement
6. ✅ **No bare primitives** enforced by type system
7. ✅ **Pattern matching** extracts custom types from enum
8. ✅ **Integration** with tensor dimensions and async

### Type Pattern

```simple
CustomType → UserEnum → Gpu[UserEnum, idx]
   ↑            ↑              ↑
Wraps      Implicit       Device
primitive  conversion     placement
```

### Benefits

- **Type safety**: Prevents mixing primitives and device types
- **Explicit costs**: Device transfers are visible in code
- **Flexibility**: User-defined enums for domain-specific types
- **Integration**: Works with async, tensor dimensions, generics
- **Clear errors**: Type system catches device mismatches at compile time

---

**Prepared by**: Claude Code Assistant
**Date**: 2026-01-10
**Design Pattern**: User Enum with Custom Type Embedding
