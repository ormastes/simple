# Execution Context Types - Implementation Roadmap

**Feature ID**: #194
**Status**: Designing → Implementing
**Dependencies**: Type system (#32), Async/Await (#41), Tensor Dimensions (#193)
**Date**: 2026-01-10

---

## Overview

This roadmap outlines the implementation strategy for execution context types, which enable compile-time device tracking similar to how `Promise<T>` tracks async computations. The design uses enum-wrapped custom types to prevent bare primitives and ensure type safety across CPU/GPU boundaries.

**Key Innovation**: Unlike generic `Host<id, T>` approach, we use custom device types (`Gpu0<T>`, `Gpu1<T>`, `Host<T>`) wrapped in enums, preventing bare primitives at the type level.

---

## Architecture Overview

### Type System Extension

```rust
// New type variants in src/type/src/types.rs
pub enum Type {
    // Existing...
    Int,
    Float,
    // ...

    // NEW: Device computation types
    DeviceComputation {
        device: DeviceType,
        inner: Box<Type>,
    },
}

pub enum DeviceType {
    Host { cpu_id: Option<u32> },
    Gpu { device_id: u32, backend: GpuBackend },
    Auto,  // Scheduler chooses
}

pub enum GpuBackend {
    Cuda,
    Metal,
    Vulkan,
    Software,
}
```

### Runtime Representation

```rust
// New runtime object in src/runtime/src/value/mod.rs
#[repr(C)]
pub struct RuntimeDeviceComputation {
    pub header: HeapHeader,
    pub device_type: u8,      // Host=0, Gpu=1
    pub device_id: u32,       // CPU/GPU number
    pub backend: u32,         // CUDA/Metal/etc.
    pub value: RuntimeValue,  // Wrapped value
    pub metadata: u64,        // Device-specific metadata
}

impl RuntimeDeviceComputation {
    pub fn new_host(cpu_id: u32, value: RuntimeValue) -> Self { ... }
    pub fn new_gpu(device_id: u32, backend: GpuBackend, value: RuntimeValue) -> Self { ... }
    pub fn transfer_to_host(&self) -> RuntimeDeviceComputation { ... }
    pub fn transfer_to_gpu(&self, device_id: u32) -> RuntimeDeviceComputation { ... }
}
```

---

## Implementation Phases

### Phase 1: Type System Foundation (Week 1-2)

**Files to modify:**
- `src/type/src/types.rs` - Add `Type::DeviceComputation`
- `src/type/src/unification.rs` - Device type unification
- `src/type/src/inference.rs` - Device type inference

**Tasks:**

1. **Add Device Type Variants**
   ```rust
   // In types.rs
   impl Type {
       pub fn host(inner: Type) -> Type {
           Type::DeviceComputation {
               device: DeviceType::Host { cpu_id: None },
               inner: Box::new(inner),
           }
       }

       pub fn gpu(device_id: u32, inner: Type) -> Type {
           Type::DeviceComputation {
               device: DeviceType::Gpu {
                   device_id,
                   backend: GpuBackend::Cuda,
               },
               inner: Box::new(inner),
           }
       }
   }
   ```

2. **Unification Rules**
   ```rust
   // In unification.rs
   fn unify_device_computations(
       d1: &DeviceType,
       d2: &DeviceType,
       t1: &Type,
       t2: &Type,
   ) -> Result<Type, TypeError> {
       match (d1, d2) {
           // Same device → unify inner types
           (DeviceType::Host { cpu_id: c1 }, DeviceType::Host { cpu_id: c2 })
               if c1 == c2 => unify(t1, t2),

           (DeviceType::Gpu { device_id: d1, .. }, DeviceType::Gpu { device_id: d2, .. })
               if d1 == d2 => unify(t1, t2),

           // Different devices → error
           _ => Err(TypeError::DeviceMismatch {
               expected: d2.clone(),
               found: d1.clone(),
           }),
       }
   }
   ```

3. **Prevent Bare Primitives**
   ```rust
   // In inference.rs
   fn check_no_bare_primitives(ty: &Type) -> Result<(), TypeError> {
       match ty {
           Type::Int | Type::Float | Type::Bool | Type::String
               if !is_wrapped_in_device(ty) =>
           {
               Err(TypeError::BarePrimitiveNotAllowed {
                   primitive: ty.clone(),
                   hint: "Wrap in Host<T>, Gpu<device, T>, or device-specific type".into(),
               })
           }
           _ => Ok(()),
       }
   }
   ```

**Tests:**
- `src/type/tests/device_types.rs` - Device type unification tests
- `src/type/tests/bare_primitive_prevention.rs` - Error on bare primitives

---

### Phase 2: Parser Support (Week 2)

**Files to modify:**
- `src/parser/src/types_def/mod.rs` - Parse device type syntax
- `src/parser/src/ast/nodes/core.rs` - AST nodes for device types

**Syntax to support:**

```simple
# Type annotations
let x: Host<Int> = Host(42)
let y: Gpu0<Float> = Gpu0(3.14)

# Device enum
enum DeviceInt:
    Gpu0(Gpu0<Int>)
    Gpu1(Gpu1<Int>)
    Host(Host<Int>)

# Generic device types
struct Gpu0[T]:
    value: T
```

**Implementation:**

```rust
// In types_def/mod.rs
fn parse_device_type(&mut self) -> Result<TypeAnnotation, ParseError> {
    match self.current_token {
        Token::Identifier("Host" | "Gpu0" | "Gpu1" | ...) => {
            let device_name = self.consume_identifier()?;
            self.expect(Token::LBracket)?;  // [
            let inner_type = self.parse_type()?;
            self.expect(Token::RBracket)?;  // ]

            Ok(TypeAnnotation::DeviceComputation {
                device: device_name,
                inner: Box::new(inner_type),
            })
        }
        _ => self.parse_base_type(),
    }
}
```

**Tests:**
- Parse `Host<Int>`, `Gpu0<Float>` correctly
- Parse device enum definitions
- Parse generic device structs

---

### Phase 3: HIR Lowering (Week 3)

**Files to modify:**
- `src/compiler/src/hir/lower/mod.rs` - Lower device types to HIR
- `src/compiler/src/hir/mod.rs` - HIR representation

**Tasks:**

1. **Device Type Checking**
   ```rust
   // Check device compatibility in function calls
   fn check_device_call(
       fn_device: &DeviceType,
       arg_device: &DeviceType,
   ) -> Result<(), TypeError> {
       if fn_device != arg_device {
           return Err(TypeError::DeviceMismatch {
               expected: fn_device.clone(),
               found: arg_device.clone(),
               help: format!(
                   "Use .to_{}() to transfer value",
                   fn_device.name()
               ),
           });
       }
       Ok(())
   }
   ```

2. **Implicit Device Transfer Insertion**
   ```rust
   // When crossing device boundaries, insert transfer calls
   fn insert_device_transfer(
       value: HirExpr,
       from: DeviceType,
       to: DeviceType,
   ) -> HirExpr {
       HirExpr::MethodCall {
           receiver: Box::new(value),
           method: format!("to_{}", to.name()),
           args: vec![],
       }
   }
   ```

**Tests:**
- Device mismatch errors
- Implicit transfer insertion
- Function device annotation checking

---

### Phase 4: MIR Codegen (Week 3-4)

**Files to modify:**
- `src/compiler/src/codegen/mir_gen.rs` - Generate MIR for device ops
- `src/compiler/src/mir/instructions.rs` - New MIR instructions

**New MIR instructions:**

```rust
pub enum MirInstruction {
    // Existing...

    // NEW: Device operations
    CreateHostComputation {
        dest: Register,
        cpu_id: Option<u32>,
        value: Register,
    },
    CreateGpuComputation {
        dest: Register,
        device_id: u32,
        backend: GpuBackend,
        value: Register,
    },
    DeviceTransfer {
        dest: Register,
        source: Register,
        from_device: DeviceType,
        to_device: DeviceType,
    },
    DeviceExecute {
        dest: Register,
        computation: Register,
        operation: Box<MirBlock>,
    },
}
```

**Codegen:**

```rust
fn gen_device_computation(&mut self, expr: &HirExpr) -> Register {
    match expr {
        HirExpr::DeviceConstruction { device, value } => {
            let val_reg = self.gen_expr(value);
            let dest = self.alloc_register();

            match device {
                DeviceType::Host { cpu_id } => {
                    self.emit(MirInstruction::CreateHostComputation {
                        dest,
                        cpu_id: *cpu_id,
                        value: val_reg,
                    });
                }
                DeviceType::Gpu { device_id, backend } => {
                    self.emit(MirInstruction::CreateGpuComputation {
                        dest,
                        device_id: *device_id,
                        backend: *backend,
                        value: val_reg,
                    });
                }
            }

            dest
        }
        _ => self.gen_expr(expr),
    }
}
```

---

### Phase 5: Runtime Implementation (Week 4-5)

**Files to create/modify:**
- `src/runtime/src/value/device_computation.rs` (NEW)
- `src/runtime/src/device_transfer.rs` (NEW)
- `src/runtime/src/value/mod.rs` - Export device types

**Implementation:**

```rust
// device_computation.rs
#[repr(C)]
pub struct RuntimeDeviceComputation {
    pub header: HeapHeader,
    pub device_type: DeviceTypeTag,
    pub device_id: u32,
    pub value: RuntimeValue,
}

#[repr(u8)]
pub enum DeviceTypeTag {
    Host = 0,
    Gpu = 1,
}

impl RuntimeDeviceComputation {
    pub fn new_host(cpu_id: u32, value: RuntimeValue) -> RuntimeValue {
        let comp = Box::new(RuntimeDeviceComputation {
            header: HeapHeader::new(HeapObjectType::DeviceComputation),
            device_type: DeviceTypeTag::Host,
            device_id: cpu_id,
            value,
        });
        RuntimeValue::from_heap_ptr(Box::into_raw(comp) as u64)
    }

    pub fn transfer_to_gpu(&self, device_id: u32) -> RuntimeValue {
        // For prototype: just wrap value
        // In production: actual GPU transfer
        RuntimeDeviceComputation::new_gpu(device_id, self.value)
    }
}

// FFI exports
#[no_mangle]
pub extern "C" fn simple_device_computation_new_host(
    cpu_id: u32,
    value: RuntimeValue,
) -> RuntimeValue {
    RuntimeDeviceComputation::new_host(cpu_id, value)
}

#[no_mangle]
pub extern "C" fn simple_device_computation_transfer(
    comp: RuntimeValue,
    target_device_type: u8,
    target_device_id: u32,
) -> RuntimeValue {
    let comp_ptr = comp.as_heap_ptr() as *const RuntimeDeviceComputation;
    unsafe {
        match target_device_type {
            0 => (*comp_ptr).transfer_to_host(target_device_id),
            1 => (*comp_ptr).transfer_to_gpu(target_device_id),
            _ => panic!("Invalid device type"),
        }
    }
}
```

**Tests:**
- `src/runtime/src/value/device_tests.rs` - Device computation creation
- `src/runtime/src/device_transfer_tests.rs` - Transfer operations

---

### Phase 6: Standard Library (Week 5-6)

**Files to create:**
- `simple/std_lib/src/execution/__init__.spl` (NEW)
- `simple/std_lib/src/execution/device_types.spl` (NEW)
- `simple/std_lib/src/execution/transfers.spl` (NEW)

**Implementation:**

```simple
# device_types.spl
"""
Device-aware type system for execution context tracking.

Provides custom device types that prevent bare primitives and
ensure type-safe device transfers.
"""

# Base device marker structs
struct Gpu0Device
struct Gpu1Device
struct Gpu2Device
struct Gpu3Device
struct HostDevice

# Generic device computation wrappers
struct Gpu0[T]:
    """GPU 0 computation wrapper."""
    value: T

    fn new(val: T) -> Gpu0[T]:
        Gpu0(value: val)

    fn get(self) -> T:
        self.value

    fn to_gpu1(self) -> Gpu1[T]:
        Gpu1(value: self.value)  # Runtime handles actual transfer

    fn to_host(self) -> Host[T]:
        Host(value: self.value)

struct Gpu1[T]:
    """GPU 1 computation wrapper."""
    value: T

    fn new(val: T) -> Gpu1[T]:
        Gpu1(value: val)

    fn to_gpu0(self) -> Gpu0[T]:
        Gpu0(value: self.value)

    fn to_host(self) -> Host[T]:
        Host(value: self.value)

struct Host[T]:
    """Host (CPU) computation wrapper."""
    value: T

    fn new(val: T) -> Host[T]:
        Host(value: val)

    fn to_gpu0(self) -> Gpu0[T]:
        Gpu0(value: self.value)

    fn to_gpu1(self) -> Gpu1[T]:
        Gpu1(value: self.value)

# Type aliases for common types
type Gpu0Int = Gpu0[Int]
type Gpu1Int = Gpu1[Int]
type HostInt = Host[Int]

type Gpu0Float = Gpu0[Float]
type Gpu1Float = Gpu1[Float]
type HostFloat = Host[Float]

# Device enum for dynamic device selection
enum DeviceInt:
    Gpu0(Gpu0Int)
    Gpu1(Gpu1Int)
    Host(HostInt)

    fn get(self) -> Int:
        match self:
            case DeviceInt::Gpu0(val):
                val.get()
            case DeviceInt::Gpu1(val):
                val.get()
            case DeviceInt::Host(val):
                val.get()
```

**Tests:**
- `simple/std_lib/test/unit/execution/device_types_spec.spl`
- `simple/std_lib/test/integration/execution/multi_device_spec.spl`

---

### Phase 7: Integration with Tensor Dimensions (Week 6)

**Goal**: Combine device types with tensor dimension tracking

**Files to modify:**
- `simple/std_lib/src/ml/torch/typed_tensor.spl`

**Implementation:**

```simple
# typed_tensor.spl enhancement

# Tensor with both device and dimension tracking
type Gpu0Tensor[Shape] = Gpu0[TypedTensor[Shape]]
type Gpu1Tensor[Shape] = Gpu1[TypedTensor[Shape]]
type HostTensor[Shape] = Host[TypedTensor[Shape]]

# Example usage
fn matmul_gpu0[B, I, O](
    input: Gpu0Tensor[TensorShape[[B, I]]],
    weight: Gpu0Tensor[TensorShape[[I, O]]]
) -> Gpu0Tensor[TensorShape[[B, O]]]:
    # Type system verifies:
    # ✅ Both tensors on GPU 0
    # ✅ Dimension I matches
    # ✅ Output shape correct

    let result_shape = infer_matmul_shape(input.shape, weight.shape)?
    let result_data = gpu0_matmul(input.data, weight.data)

    Gpu0(value: TypedTensor(
        data: result_data,
        shape: result_shape
    ))
```

**Tests:**
- Device + dimension type checking
- Transfer preservation of dimensions
- Error messages for device + dimension mismatches

---

### Phase 8: Integration with Async (Week 7)

**Goal**: Support `Promise<Gpu0<T>>` for async GPU operations

**Files to modify:**
- `src/compiler/src/async_analysis.rs`

**Implementation:**

```simple
# Async GPU computation
async fn train_batch_gpu0(
    data: Gpu0Tensor[TensorShape[[32, 784]]],
    labels: Gpu0Tensor[TensorShape[[32, 10]]]
) -> Promise<Gpu0Tensor[TensorShape[[32, 10]]]>:
    # Launch async GPU kernel
    let output = ~model.forward_async(data)
    let loss = ~compute_loss_async(output, labels)
    ~backward_async(loss)

# Type: Promise<Gpu0<Tensor>>
let result = train_batch_gpu0(data, labels)
```

**Runtime support:**
- GPU kernel launches return promises
- Synchronization on `.await`
- Concurrent GPU streams

---

### Phase 9: Error Messages (Week 7)

**Goal**: Clear, actionable error messages

**Implementation:**

```rust
// Enhanced error messages
match error {
    TypeError::DeviceMismatch { expected, found, location } => {
        format!(
            "Device mismatch at {location}\n\
             Expected: {}\n\
             Found: {}\n\n\
             Help: Use .to_{}() to transfer the value to the expected device\n\
             Example: value.to_{}()",
            expected.display(),
            found.display(),
            expected.transfer_method(),
            expected.transfer_method(),
        )
    }

    TypeError::BarePrimitiveNotAllowed { primitive, location } => {
        format!(
            "Bare primitive type `{}` not allowed at {location}\n\n\
             All primitive values must be wrapped in device types:\n\
             - Host<{0}> for CPU computation\n\
             - Gpu0<{0}> for GPU 0\n\
             - Gpu1<{0}> for GPU 1\n\n\
             Example: let x: Host<{0}> = Host({example_value})",
            primitive.display(),
            example_value = primitive.example_value(),
        )
    }
}
```

**Examples:**

```
Error: Device mismatch at src/train.spl:42
Expected: Gpu0<Tensor>
Found: Gpu1<Tensor>

Help: Use .to_gpu0() to transfer the value to the expected device
Example: value.to_gpu0()
```

```
Error: Bare primitive type `Int` not allowed at src/compute.spl:10

All primitive values must be wrapped in device types:
- Host<Int> for CPU computation
- Gpu0<Int> for GPU 0
- Gpu1<Int> for GPU 1

Example: let x: Host<Int> = Host(42)
```

---

### Phase 10: Documentation & Examples (Week 8)

**Files to create:**
- `doc/guide/execution_context_guide.md` - User guide
- `doc/spec/generated/execution_context.md` - Spec (auto-generated)
- `examples/gpu_computation.spl` - Multi-GPU example
- `examples/heterogeneous_pipeline.spl` - CPU/GPU pipeline

**Topics to cover:**
1. Introduction to device types
2. Creating device-wrapped values
3. Device transfers
4. Device enums for dynamic dispatch
5. Pattern matching on devices
6. Integration with tensor dimensions
7. Async GPU operations
8. Multi-GPU data parallelism
9. Error handling
10. Performance best practices

---

## Testing Strategy

### Unit Tests
- Type unification for device types
- Bare primitive prevention
- Device transfer semantics
- Runtime device computation creation

### Integration Tests
- Multi-device pipelines
- Tensor + device integration
- Async + device integration
- Error message clarity

### System Tests
- `tests/system/execution_context_tests.spl` - End-to-end workflows
- `tests/system/multi_gpu_tests.spl` - Multi-GPU scenarios

### Examples as Tests
- All examples in `examples/` should compile and run
- Verify output matches expected behavior

---

## Success Criteria

- [ ] Type system enforces device tracking
- [ ] Bare primitives rejected at compile time
- [ ] Device transfers explicit and type-safe
- [ ] Device enums support dynamic dispatch
- [ ] Integration with tensor dimensions works
- [ ] Integration with async/await works
- [ ] Error messages clear and actionable
- [ ] All tests passing (unit, integration, system)
- [ ] Documentation complete and accurate
- [ ] Examples demonstrate all features
- [ ] Performance acceptable (minimal overhead)

---

## Risks and Mitigation

### Risk 1: Type System Complexity
**Impact**: High
**Likelihood**: Medium

**Mitigation**:
- Start with simple cases (Host<Int>, Gpu0<Int>)
- Incrementally add complexity (enums, generics)
- Extensive testing at each phase

### Risk 2: Runtime Overhead
**Impact**: Medium
**Likelihood**: Low

**Mitigation**:
- Device wrappers compile to zero-cost abstractions
- Transfers only occur when explicitly requested
- Benchmark critical paths

### Risk 3: Parser Limitations
**Impact**: High
**Likelihood**: Medium

**Mitigation**:
- Discovered during tensor dimensions work
- May need workarounds for angle bracket generics in class fields
- Use standalone implementations if needed

---

## Timeline

| Phase | Duration | Dependencies | Status |
|-------|----------|--------------|--------|
| 1. Type System | 2 weeks | None | Not started |
| 2. Parser | 1 week | Phase 1 | Not started |
| 3. HIR | 1 week | Phase 2 | Not started |
| 4. MIR | 1 week | Phase 3 | Not started |
| 5. Runtime | 2 weeks | Phase 4 | Not started |
| 6. Stdlib | 1 week | Phase 5 | Not started |
| 7. Tensor Integration | 1 week | Phase 6, #193 | Not started |
| 8. Async Integration | 1 week | Phase 6, #41 | Not started |
| 9. Error Messages | 1 week | Phases 1-8 | Not started |
| 10. Documentation | 1 week | Phases 1-9 | Not started |

**Total**: ~12 weeks (3 months)

---

## Next Steps

1. **Immediate**: Review this roadmap with stakeholders
2. **Week 1**: Begin Phase 1 (Type System Foundation)
3. **Week 2**: Complete Phase 1, start Phase 2 (Parser)
4. **Month 1 Review**: Assess progress, adjust timeline
5. **Month 2**: Complete runtime and stdlib
6. **Month 3**: Integration, polish, documentation

---

## References

- **Design Document**: `doc/design/device_enum_types_proposal.md`
- **Quick Reference**: `doc/design/device_types_quick_reference.md`
- **Prototype Demo**: `examples/execution_context_demo.spl`
- **Related Features**:
  - #193 - Tensor Dimension Inference
  - #41 - Async/Await
  - #32 - Generics
  - #18 - Memory Types

---

**Prepared by**: Claude Code Assistant
**Date**: 2026-01-10
**Status**: Ready for implementation
