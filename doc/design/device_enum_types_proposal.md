# Device Enum Types - Enhanced Design Proposal

**Concept**: Use enum-wrapped custom types where device contexts are first-class types, not generic parameters. Primitives cannot exist bare - they must be wrapped in device-specific types.

**Date**: 2026-01-10

---

## Core Concept: No Bare Primitives

### Problem with Primitives

```simple
# BAD: Where does this Int live?
let x: Int = 42  # CPU? GPU? Which GPU?

# WORSE: Can't track device
fn add(a: Int, b: Int) -> Int:
    a + b  # Where does addition happen?
```

### Solution: Device-Wrapped Types

```simple
# GOOD: Device is part of the type
let x: Gpu0Int = 42  # Lives on GPU 0
let y: Gpu1Int = 42  # Lives on GPU 1
let z: HostInt = 42  # Lives on CPU

# Type system prevents mixing
fn add_gpu0(a: Gpu0Int, b: Gpu0Int) -> Gpu0Int:
    a + b  # Addition on GPU 0
```

---

## Type System Design

### Custom Device Types

Each device has its own type namespace:

```simple
# GPU 0 types
type Gpu0Int = Int @ Gpu0
type Gpu0Float = Float @ Gpu0
type Gpu0Tensor = Tensor @ Gpu0
type Gpu0Array<T> = Array<T> @ Gpu0

# GPU 1 types
type Gpu1Int = Int @ Gpu1
type Gpu1Float = Float @ Gpu1
type Gpu1Tensor = Tensor @ Gpu1

# Host types
type HostInt = Int @ Host
type HostFloat = Float @ Host
type HostTensor = Tensor @ Host

# The `@ Device` syntax means "wrapped with device context"
```

### Device Enum Wrapper

```simple
# Enum that can hold values from any device
enum DeviceValue<T>:
    OnGpu0(Gpu0<T>)
    OnGpu1(Gpu1<T>)
    OnGpu2(Gpu2<T>)
    OnHost(Host<T>)

# Examples
let val1: DeviceValue<Int> = DeviceValue::OnGpu0(Gpu0Int(42))
let val2: DeviceValue<Int> = DeviceValue::OnHost(HostInt(42))

# Can pattern match to extract
match val1:
    case DeviceValue::OnGpu0(x):
        # x: Gpu0Int
        compute_on_gpu0(x)
    case DeviceValue::OnHost(x):
        # x: HostInt
        compute_on_host(x)
```

### Implicit Conversions

```simple
# Define implicit conversions
impl From<Gpu0Int> for DeviceValue<Int>:
    fn from(val: Gpu0Int) -> DeviceValue<Int>:
        DeviceValue::OnGpu0(val)

impl From<HostInt> for DeviceValue<Int>:
    fn from(val: HostInt) -> DeviceValue<Int>:
        DeviceValue::OnHost(val)

# Usage - automatic upcast
fn process(val: DeviceValue<Int>) -> Int:
    match val:
        case DeviceValue::OnGpu0(x): x.to_host().unwrap()
        case DeviceValue::OnHost(x): x.unwrap()

let x: Gpu0Int = 42
process(x)  # Implicitly converts to DeviceValue::OnGpu0(x)
```

---

## Example 1: Basic Device Types

```simple
# Define device type wrappers
struct Gpu0<T>:
    value: T
    _marker: PhantomData<Gpu0Device>

struct Gpu1<T>:
    value: T
    _marker: PhantomData<Gpu1Device>

struct Host<T>:
    value: T
    _marker: PhantomData<HostDevice>

# Type aliases for convenience
type Gpu0Int = Gpu0<Int>
type Gpu0Float = Gpu0<Float>
type Gpu1Int = Gpu1<Int>
type HostInt = Host<Int>

# Operations are device-specific
impl Gpu0<Int>:
    fn add(self, other: Gpu0<Int>) -> Gpu0<Int>:
        # Addition happens on GPU 0
        Gpu0(value: self.value + other.value)

    fn mul(self, other: Gpu0<Int>) -> Gpu0<Int>:
        Gpu0(value: self.value * other.value)

    # Transfer to other devices
    fn to_gpu1(self) -> Gpu1<Int>:
        # GPU 0 → GPU 1 transfer
        Gpu1(value: self.value)

    fn to_host(self) -> Host<Int>:
        # GPU 0 → Host transfer
        Host(value: self.value)

# Usage
let a: Gpu0Int = Gpu0(value: 10)
let b: Gpu0Int = Gpu0(value: 20)
let c: Gpu0Int = a.add(b)  # Result: Gpu0(30), stays on GPU 0

# Type error if mixing devices
let d: Gpu1Int = Gpu1(value: 5)
let e = a.add(d)  # ERROR: Cannot mix Gpu0<Int> and Gpu1<Int>

# Must transfer explicitly
let d_on_gpu0: Gpu0Int = d.to_gpu0()
let e: Gpu0Int = a.add(d_on_gpu0)  # OK
```

---

## Example 2: Device Enum with Pattern Matching

```simple
# Generic device value enum
enum DeviceInt:
    Gpu0(Gpu0Int)
    Gpu1(Gpu1Int)
    Gpu2(Gpu2Int)
    Gpu3(Gpu3Int)
    Host(HostInt)

enum DeviceTensor:
    Gpu0(Gpu0Tensor)
    Gpu1(Gpu1Tensor)
    Host(HostTensor)

# Functions that work on any device
fn compute_anywhere(val: DeviceInt) -> DeviceInt:
    match val:
        case DeviceInt::Gpu0(x):
            # Compute on GPU 0
            DeviceInt::Gpu0(x.mul(Gpu0(2)))
        case DeviceInt::Gpu1(x):
            # Compute on GPU 1
            DeviceInt::Gpu1(x.mul(Gpu1(2)))
        case DeviceInt::Host(x):
            # Compute on host
            DeviceInt::Host(x.mul(Host(2)))

# Smart constructor that picks best device
fn auto_device(value: Int) -> DeviceInt:
    if cuda_available():
        DeviceInt::Gpu0(Gpu0(value))
    else:
        DeviceInt::Host(Host(value))

# Usage
let x = auto_device(42)
let result = compute_anywhere(x)  # Runs on whichever device x is on
```

---

## Example 3: Tensor Operations with Device Types

```simple
# Device-specific tensor types
struct Gpu0Tensor:
    data: TensorData
    shape: TensorShape
    _device: PhantomData<Gpu0>

struct Gpu1Tensor:
    data: TensorData
    shape: TensorShape
    _device: PhantomData<Gpu1>

struct HostTensor:
    data: TensorData
    shape: TensorShape
    _device: PhantomData<Host>

# Operations stay on device
impl Gpu0Tensor:
    fn matmul(self, other: Gpu0Tensor) -> Gpu0Tensor:
        # Matrix multiply on GPU 0
        Gpu0Tensor(
            data: gpu0_matmul(self.data, other.data),
            shape: infer_matmul_shape(self.shape, other.shape)
        )

    fn relu(self) -> Gpu0Tensor:
        # ReLU on GPU 0
        Gpu0Tensor(
            data: gpu0_relu(self.data),
            shape: self.shape
        )

    # Transfer operators
    fn to_gpu1(self) -> Gpu1Tensor:
        Gpu1Tensor(
            data: transfer_gpu0_to_gpu1(self.data),
            shape: self.shape
        )

    fn to_host(self) -> HostTensor:
        HostTensor(
            data: transfer_gpu0_to_host(self.data),
            shape: self.shape
        )

# Enum wrapper
enum DeviceTensor:
    Gpu0(Gpu0Tensor)
    Gpu1(Gpu1Tensor)
    Host(HostTensor)

# Generic operations
impl DeviceTensor:
    fn matmul(self, other: DeviceTensor) -> DeviceTensor:
        match (self, other):
            case (DeviceTensor::Gpu0(a), DeviceTensor::Gpu0(b)):
                DeviceTensor::Gpu0(a.matmul(b))
            case (DeviceTensor::Gpu1(a), DeviceTensor::Gpu1(b)):
                DeviceTensor::Gpu1(a.matmul(b))
            case (DeviceTensor::Host(a), DeviceTensor::Host(b)):
                DeviceTensor::Host(a.matmul(b))
            case _:
                panic("Device mismatch - use .to_device() to transfer")

    fn to_device(self, target: Device) -> DeviceTensor:
        match (self, target):
            case (DeviceTensor::Gpu0(t), Device::Gpu1):
                DeviceTensor::Gpu1(t.to_gpu1())
            case (DeviceTensor::Gpu1(t), Device::Gpu0):
                DeviceTensor::Gpu0(t.to_gpu0())
            # ... all combinations
```

---

## Example 4: Neural Network with Device Types

```simple
# Model with device-specific parameters
struct Gpu0Model:
    layer1: Gpu0Tensor  # Weights on GPU 0
    layer2: Gpu0Tensor
    layer3: Gpu0Tensor

struct Gpu1Model:
    layer1: Gpu1Tensor  # Weights on GPU 1
    layer2: Gpu1Tensor
    layer3: Gpu1Tensor

# Device-specific forward pass
impl Gpu0Model:
    fn forward(self, input: Gpu0Tensor) -> Gpu0Tensor:
        # All operations stay on GPU 0
        let h1 = input.matmul(self.layer1).relu()
        let h2 = h1.matmul(self.layer2).relu()
        let output = h2.matmul(self.layer3)
        output

impl Gpu1Model:
    fn forward(self, input: Gpu1Tensor) -> Gpu1Tensor:
        # All operations stay on GPU 1
        let h1 = input.matmul(self.layer1).relu()
        let h2 = h1.matmul(self.layer2).relu()
        let output = h2.matmul(self.layer3)
        output

# Enum wrapper for multi-device models
enum DeviceModel:
    Gpu0(Gpu0Model)
    Gpu1(Gpu1Model)
    Host(HostModel)

impl DeviceModel:
    fn forward(self, input: DeviceTensor) -> DeviceTensor:
        match (self, input):
            case (DeviceModel::Gpu0(m), DeviceTensor::Gpu0(x)):
                DeviceTensor::Gpu0(m.forward(x))
            case (DeviceModel::Gpu1(m), DeviceTensor::Gpu1(x)):
                DeviceTensor::Gpu1(m.forward(x))
            case _:
                panic("Model and input on different devices")

    # Replicate model to another device
    fn replicate_to_gpu1(self) -> DeviceModel:
        match self:
            case DeviceModel::Gpu0(model):
                DeviceModel::Gpu1(Gpu1Model(
                    layer1: model.layer1.to_gpu1(),
                    layer2: model.layer2.to_gpu1(),
                    layer3: model.layer3.to_gpu1()
                ))
            case _:
                panic("Can only replicate from GPU0")
```

---

## Example 5: Data Parallel Training

```simple
# Training step - device-specific
fn train_step_gpu0(
    model: Gpu0Model,
    data: Gpu0Tensor,
    labels: Gpu0Tensor
) -> Gpu0Tensor:
    # All on GPU 0
    let output = model.forward(data)
    let loss = cross_entropy(output, labels)
    let grads = backward(loss)
    grads

fn train_step_gpu1(
    model: Gpu1Model,
    data: Gpu1Tensor,
    labels: Gpu1Tensor
) -> Gpu1Tensor:
    # All on GPU 1
    let output = model.forward(data)
    let loss = cross_entropy(output, labels)
    let grads = backward(loss)
    grads

# Data parallel training across 4 GPUs
fn train_data_parallel(
    data: List[HostTensor],
    labels: List[HostTensor]
):
    # Create model on GPU 0
    let master_model: Gpu0Model = create_model_gpu0()

    # Replicate to other GPUs
    let model0: Gpu0Model = master_model
    let model1: Gpu1Model = master_model.to_gpu1()
    let model2: Gpu2Model = master_model.to_gpu2()
    let model3: Gpu3Model = master_model.to_gpu3()

    # Split data
    let batches = data.chunk(4)
    let label_batches = labels.chunk(4)

    for epoch in range(100):
        # Transfer data to respective GPUs (once per epoch)
        let data0: Gpu0Tensor = batches[0].to_gpu0()
        let data1: Gpu1Tensor = batches[1].to_gpu1()
        let data2: Gpu2Tensor = batches[2].to_gpu2()
        let data3: Gpu3Tensor = batches[3].to_gpu3()

        let labels0: Gpu0Tensor = label_batches[0].to_gpu0()
        let labels1: Gpu1Tensor = label_batches[1].to_gpu1()
        let labels2: Gpu2Tensor = label_batches[2].to_gpu2()
        let labels3: Gpu3Tensor = label_batches[3].to_gpu3()

        # Parallel training (each GPU works independently)
        let grads0: Gpu0Tensor = train_step_gpu0(model0, data0, labels0)
        let grads1: Gpu1Tensor = train_step_gpu1(model1, data1, labels1)
        let grads2: Gpu2Tensor = train_step_gpu2(model2, data2, labels2)
        let grads3: Gpu3Tensor = train_step_gpu3(model3, data3, labels3)

        # Gather gradients to GPU 0 for averaging
        let grads0_copy: Gpu0Tensor = grads0
        let grads1_on_0: Gpu0Tensor = grads1.to_gpu0()
        let grads2_on_0: Gpu0Tensor = grads2.to_gpu0()
        let grads3_on_0: Gpu0Tensor = grads3.to_gpu0()

        # Average gradients on GPU 0
        let avg_grads: Gpu0Tensor = average([
            grads0_copy,
            grads1_on_0,
            grads2_on_0,
            grads3_on_0
        ])

        # Update master model on GPU 0
        model0 = update_weights(model0, avg_grads)

        # Broadcast updated weights to other GPUs
        let updated_weights0: Gpu0Tensor = model0.layer1
        model1.layer1 = updated_weights0.to_gpu1()
        model2.layer1 = updated_weights0.to_gpu2()
        model3.layer1 = updated_weights0.to_gpu3()
```

---

## Example 6: Heterogeneous Pipeline with Enum

```simple
# Pipeline stages with different devices
enum PipelineStage<T>:
    LoadOnHost(Host<T>)
    PreprocessOnGpu0(Gpu0<T>)
    InferenceOnGpu1(Gpu1<T>)
    PostprocessOnHost(Host<T>)

# Pipeline state machine
fn pipeline_next(stage: PipelineStage<Image>) -> PipelineStage<Tensor>:
    match stage:
        case PipelineStage::LoadOnHost(img):
            # Host → GPU 0
            let gpu0_img: Gpu0Image = img.to_gpu0()
            let preprocessed: Gpu0Tensor = preprocess_gpu0(gpu0_img)
            PipelineStage::PreprocessOnGpu0(preprocessed)

        case PipelineStage::PreprocessOnGpu0(tensor):
            # GPU 0 → GPU 1
            let gpu1_tensor: Gpu1Tensor = tensor.to_gpu1()
            let inference_result: Gpu1Tensor = model_gpu1.forward(gpu1_tensor)
            PipelineStage::InferenceOnGpu1(inference_result)

        case PipelineStage::InferenceOnGpu1(result):
            # GPU 1 → Host
            let host_result: HostTensor = result.to_host()
            let postprocessed: HostTensor = postprocess_host(host_result)
            PipelineStage::PostprocessOnHost(postprocessed)

        case PipelineStage::PostprocessOnHost(final):
            # Pipeline complete
            final

# Run full pipeline
fn run_pipeline(image_path: String) -> HostTensor:
    # Start with loading on host
    let image: HostImage = load_image(image_path)
    let stage1: PipelineStage<Image> = PipelineStage::LoadOnHost(image)

    # Progress through pipeline
    let stage2 = pipeline_next(stage1)  # → GPU 0
    let stage3 = pipeline_next(stage2)  # → GPU 1
    let final = pipeline_next(stage3)   # → Host

    final
```

---

## Example 7: Generic Device Functions

```simple
# Trait for device types
trait DeviceType:
    type DeviceMarker

    fn add(self, other: Self) -> Self
    fn mul(self, other: Self) -> Self
    fn to_host(self) -> Host<T>

# Implement for each device
impl DeviceType for Gpu0<T>:
    type DeviceMarker = Gpu0Device

    fn add(self, other: Gpu0<T>) -> Gpu0<T>:
        # GPU 0 addition
        ...

impl DeviceType for Gpu1<T>:
    type DeviceMarker = Gpu1Device

    fn add(self, other: Gpu1<T>) -> Gpu1<T>:
        # GPU 1 addition
        ...

# Generic function over any device
fn compute_generic<D: DeviceType>(a: D, b: D) -> D:
    let c = a.add(b)
    let d = c.mul(a)
    d

# Usage
let x_gpu0: Gpu0Int = Gpu0(10)
let y_gpu0: Gpu0Int = Gpu0(20)
let result_gpu0: Gpu0Int = compute_generic(x_gpu0, y_gpu0)

let x_gpu1: Gpu1Int = Gpu1(10)
let y_gpu1: Gpu1Int = Gpu1(20)
let result_gpu1: Gpu1Int = compute_generic(x_gpu1, y_gpu1)
```

---

## Example 8: Preventing Primitive Leakage

```simple
# NO bare primitives allowed
let x: Int = 42  # ERROR: Primitive types not allowed
                 # Use: HostInt, Gpu0Int, etc.

# Must wrap in device type
let x: HostInt = Host(42)  # OK
let y: Gpu0Int = Gpu0(42)  # OK

# Literals are ambiguous - must specify device
let z = 42  # ERROR: Cannot infer device for literal
let z: Gpu0Int = 42  # OK: type annotation provides device

# Function signatures must be explicit
fn bad_add(a: Int, b: Int) -> Int:  # ERROR: No bare Int
    a + b

fn good_add(a: Gpu0Int, b: Gpu0Int) -> Gpu0Int:  # OK
    a.add(b)

# Generic over device is OK
fn generic_add<D: DeviceType>(a: D, b: D) -> D:  # OK
    a.add(b)

# Enum provides escape hatch when device is dynamic
fn dynamic_add(a: DeviceInt, b: DeviceInt) -> DeviceInt:
    match (a, b):
        case (DeviceInt::Gpu0(x), DeviceInt::Gpu0(y)):
            DeviceInt::Gpu0(x.add(y))
        case (DeviceInt::Host(x), DeviceInt::Host(y)):
            DeviceInt::Host(x.add(y))
        case _:
            panic("Device mismatch")
```

---

## Example 9: Combining with Tensor Dimensions

```simple
# Device + Shape tracking
struct Gpu0Tensor<Shape>:
    data: TensorData
    shape: Shape
    _device: PhantomData<Gpu0>

# Type aliases for common cases
type Gpu0Tensor2D = Gpu0Tensor<TensorShape<[Dim.Var(0), Dim.Var(1)]>>
type Gpu1Tensor2D = Gpu1Tensor<TensorShape<[Dim.Var(0), Dim.Var(1)]>>

# Operations preserve both device AND shape
fn matmul_gpu0(
    a: Gpu0Tensor<TensorShape<[batch, in_dim]>>,
    b: Gpu0Tensor<TensorShape<[in_dim, out_dim]>>
) -> Gpu0Tensor<TensorShape<[batch, out_dim]>>:
    # Type system verifies:
    # 1. Both tensors on GPU 0
    # 2. Shapes compatible (in_dim matches)
    # 3. Output shape correct
    Gpu0Tensor(
        data: gpu0_matmul(a.data, b.data),
        shape: infer_matmul_shape(a.shape, b.shape)
    )

# Example usage
let input: Gpu0Tensor<TensorShape<[batch:32, 784]>> =
    load_batch().to_gpu0()

let weight: Gpu0Tensor<TensorShape<[784, 256]>> =
    model.layer1

# Compiler verifies:
# ✅ Both on GPU 0
# ✅ Shapes compatible (784 matches)
# ✅ Result shape [32, 256]
let output: Gpu0Tensor<TensorShape<[batch:32, 256]>> =
    matmul_gpu0(input, weight)

# Type error if wrong device
let gpu1_weight: Gpu1Tensor<TensorShape<[784, 256]>> = ...
let bad = matmul_gpu0(input, gpu1_weight)  # ERROR: Device mismatch
```

---

## Example 10: Async + Device

```simple
# Combine async Future with device types
enum DeviceFuture<T>:
    Gpu0(Promise<Gpu0<T>>)
    Gpu1(Promise<Gpu1<T>>)
    Host(Promise<Host<T>>)

# Async computation on specific device
async fn async_compute_gpu0(x: Gpu0Int) -> Gpu0Int:
    # Async operations on GPU 0
    let y = await gpu0_async_kernel(x)
    let z = y.mul(Gpu0(2))
    z

# Returns Promise<Gpu0Int>
let future: Promise<Gpu0Int> = async_compute_gpu0(Gpu0(42))

# Can wrap in enum for dynamic dispatch
let wrapped: DeviceFuture<Int> = DeviceFuture::Gpu0(future)

# Pattern match to extract
match wrapped:
    case DeviceFuture::Gpu0(fut):
        let result: Gpu0Int = await fut
        process_gpu0(result)
    case DeviceFuture::Host(fut):
        let result: HostInt = await fut
        process_host(result)
```

---

## Type System Formalization

### Type Syntax

```
τ ::= Int | Float | Bool | String          (Base types - NOT directly usable)
    | Device<D, τ>                          (Device-wrapped type)
    | DeviceEnum<τ>                         (Enum of all devices)
    | Promise<τ>                            (Async computation)
    | Device<D, Promise<τ>>                 (Async on specific device)

D ::= Gpu0 | Gpu1 | Gpu2 | ... | Host       (Device identifiers)
```

### Typing Rules

```
─────────────────────────────
Γ ⊢ v : Device<D, τ>  (value on device D)


Γ ⊢ e1 : Device<D, τ1>    Γ ⊢ e2 : Device<D, τ2>    op : τ1 × τ2 → τ3
─────────────────────────────────────────────────────────────────────
Γ ⊢ e1 op e2 : Device<D, τ3>  (operation stays on device)


Γ ⊢ e : Device<D1, τ>
─────────────────────────────────────────
Γ ⊢ e.to_device<D2>() : Device<D2, τ>  (explicit transfer)


Γ ⊢ e : Device<D, τ>
─────────────────────────────────────────
Γ ⊢ DeviceEnum::D(e) : DeviceEnum<τ>  (upcast to enum)
```

### Constraint: No Bare Primitives

```
─────────────────
⊢ v : Int    (ILLEGAL - primitives cannot be used directly)


────────────────────────────
⊢ Device<D, Int>(v) : Device<D, Int>  (LEGAL - must wrap in device)
```

---

## Implementation Notes

### Custom Type Wrapper Syntax

```rust
// In src/type/src/lib.rs
pub enum Type {
    // Existing...

    // New: Device-wrapped type
    DeviceWrapped {
        device: DeviceId,
        inner: Box<Type>,
    },

    // New: Device enum
    DeviceEnum {
        inner: Box<Type>,
    },
}

pub enum DeviceId {
    Gpu(u32),     // GPU 0, 1, 2, ...
    Host,         // CPU
    Custom(String), // Custom device types
}
```

### Preventing Bare Primitives

```rust
// Type checker validates no bare primitives
fn check_type(ty: &Type) -> Result<(), TypeError> {
    match ty {
        Type::Int | Type::Float | Type::Bool | Type::String => {
            Err(TypeError::BarePromitive {
                ty: ty.clone(),
                help: "Wrap in device type: Host<Int>, Gpu0<Int>, etc."
            })
        }
        Type::DeviceWrapped { .. } => Ok(()),
        // ... other cases
    }
}
```

### Implicit Conversion

```rust
// Generate From trait implementations
impl From<Gpu0<T>> for DeviceEnum<T> {
    fn from(val: Gpu0<T>) -> DeviceEnum<T> {
        DeviceEnum::Gpu0(val)
    }
}

// Compiler inserts conversion automatically
let x: Gpu0Int = Gpu0(42);
let y: DeviceEnum<Int> = x;  // Implicit: DeviceEnum::from(x)
```

---

## Summary

**Key Design Points**:

1. ✅ **No Bare Primitives**: All values must be wrapped in device types
2. ✅ **Custom Device Types**: `Gpu0<T>`, `Gpu1<T>`, `Host<T>` are distinct types
3. ✅ **Enum Wrapper**: `DeviceEnum<T>` for dynamic device selection
4. ✅ **Implicit Upcast**: Device types auto-convert to enum
5. ✅ **Explicit Downcast**: Pattern matching to extract device type
6. ✅ **Transfer Operators**: `.to_gpu0()`, `.to_host()` etc.
7. ✅ **Type Safety**: Cannot mix devices without explicit transfer
8. ✅ **Generic Functions**: Can be generic over device type
9. ✅ **Async Integration**: `Promise<Gpu0<T>>` for async GPU ops
10. ✅ **Shape Integration**: Combine with tensor dimensions

**Advantages over Generic Approach**:
- Stronger type safety (can't accidentally use bare Int)
- More explicit device placement
- Better error messages
- Prevents device leakage
- Natural enum pattern matching

**Next Steps**:
- Prototype custom type wrappers
- Implement enum auto-conversion
- Add syntax for `@ Device` annotation
- Test with real examples

---

**Prepared by**: Claude Code Assistant
**Date**: 2026-01-10
**Status**: Enhanced Design Proposal
