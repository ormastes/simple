/-
  GPU Types - Safety Proofs

  Proves that the GPU type system prevents device mixing and ensures
  type-safe device transfers.
-/

import GpuTypes.Basic

namespace GpuSafety

open Device
open Gpu

-- Theorem 1: Device tracking is correct
-- If a value has type Gpu α d, then its runtime device IS d
theorem device_tracking_correct {α : Type} {d : Device} (x : Gpu α d) :
  Gpu.deviceOf x = d := by
  rfl

-- Theorem 2: Cannot mix devices
-- Values from different devices have different types
theorem no_device_mixing {α : Type} (x : Gpu α Primary) (y : Gpu α Secondary) :
  Gpu.deviceOf x ≠ Gpu.deviceOf y := by
  intro h
  cases h

-- Theorem 3: Transfer is type-safe
-- Transferring to device d2 produces a value of type Gpu α d2
theorem transfer_type_safe {α : Type} {d1 d2 : Device} (x : Gpu α d1) :
  Gpu.deviceOf (Gpu.transfer d2 x) = d2 := by
  rfl

-- Theorem 4: Transfer preserves value
-- The value inside Gpu is unchanged by transfer
theorem transfer_value_preservation {α : Type} {d1 d2 : Device} (x : Gpu α d1) :
  (Gpu.transfer d2 x).get = x.get := by
  rfl

-- Theorem 5: Transfer is idempotent on same device
-- Transferring to the same device is a no-op (value-wise)
theorem transfer_same_device {α : Type} {d : Device} (x : Gpu α d) :
  (Gpu.transfer d x).get = x.get := by
  rfl

-- Theorem 6: Transfer composition
-- Sequential transfers compose correctly
theorem transfer_composition {α : Type} {d1 d2 d3 : Device} (x : Gpu α d1) :
  Gpu.transfer d3 (Gpu.transfer d2 x) = Gpu.transfer d3 x := by
  apply Gpu.mk.injEq.mpr
  constructor
  · rfl  -- Values equal
  constructor
  · rfl  -- Devices equal
  · rfl  -- Proofs equal

-- Theorem 7: Device distinction is decidable
-- Can always decide if two devices are equal
theorem device_eq_decidable (d1 d2 : Device) : Decidable (d1 = d2) := by
  cases d1 <;> cases d2 <;>
    (first | apply isTrue rfl | apply isFalse; intro h; cases h)

end GpuSafety
