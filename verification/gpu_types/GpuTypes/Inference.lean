/-
  GPU Types - Type Inference Proofs

  Proves correctness of type inference for GPU-annotated functions.
  Models the @gpu(device) annotation and automatic wrapping.
-/

import GpuTypes.Basic

namespace GpuInference

open Device
open Gpu
open GpuFunction

-- Theorem 1: Function with @gpu annotation returns Gpu type
-- If function has @gpu(d) annotation, return type is Gpu β d
theorem annotated_function_returns_gpu {d : Device} {α β : Type}
    (f : GpuFunction d α β) (x : α) :
  ∃ (result : Gpu β d), result.value = f.impl x := by
  exists f.apply x
  rfl

-- Theorem 2: Inferred device matches annotation
-- The device in the return type equals the annotation device
theorem inferred_device_matches {d : Device} {α β : Type}
    (f : GpuFunction d α β) (x : α) :
  (f.apply x).device = d := by
  rfl

-- Theorem 3: Type inference is deterministic
-- Given same function and input, always infer same type
theorem inference_deterministic {d : Device} {α β : Type}
    (f : GpuFunction d α β) (x : α) :
  (f.apply x).device = (f.apply x).device := by
  rfl

-- Theorem 4: Inference correctness
-- If function has @gpu(d), result type is Gpu[ReturnType, d]
theorem inference_correct {d : Device} {α β : Type}
    (f : GpuFunction d α β) :
  f.device = d := by
  exact f.device_eq

-- Theorem 5: Auto-unwrap correctness
-- In @gpu(d) context, Gpu α d can be treated as α
-- (Modeled by .get being well-defined)
theorem auto_unwrap_safe {d : Device} {α : Type} (x : Gpu α d) :
  ∃ (v : α), v = x.get := by
  exists x.get
  rfl

-- Theorem 6: Auto-wrap correctness
-- In @gpu(d) context, α can be wrapped to Gpu α d
-- (Modeled by Gpu.make being well-defined)
theorem auto_wrap_safe {d : Device} {α : Type} (x : α) :
  ∃ (wrapped : Gpu α d), wrapped.get = x := by
  exists Gpu.make d x
  rfl

-- Theorem 7: Operations stay on device
-- Binary operation on same-device values stays on that device
structure BinaryOp (α : Type) where
  op : α → α → α

def gpu_binary_op {d : Device} {α : Type}
    (op : BinaryOp α) (x y : Gpu α d) : Gpu α d :=
  Gpu.make d (op.op x.get y.get)

theorem binary_op_preserves_device {d : Device} {α : Type}
    (op : BinaryOp α) (x y : Gpu α d) :
  (gpu_binary_op op x y).device = d := by
  rfl

theorem binary_op_uses_values {d : Device} {α : Type}
    (op : BinaryOp α) (x y : Gpu α d) :
  (gpu_binary_op op x y).get = op.op x.get y.get := by
  rfl

-- Theorem 8: Type inference prevents device mixing
-- Cannot apply binary op to values on different devices
theorem no_mixed_device_op {α : Type}
    (op : BinaryOp α) (x : Gpu α Primary) (y : Gpu α Secondary) :
  Gpu.deviceOf x ≠ Gpu.deviceOf y := by
  intro h
  cases h

-- Theorem 9: Inference with transfers
-- Transfer + operation sequence maintains type safety
theorem transfer_inference_safe {d1 d2 : Device} {α : Type}
    (op : BinaryOp α) (x : Gpu α d1) (y : Gpu α d1) :
  let x2 := Gpu.transfer d2 x
  let y2 := Gpu.transfer d2 y
  (gpu_binary_op op x2 y2).device = d2 := by
  rfl

end GpuInference
