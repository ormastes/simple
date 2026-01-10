/-
  GPU Types - Basic Definitions

  Defines the core GPU type system for Simple language.
  Models device-parameterized computations with type-level device tracking.
-/

-- Device enumeration (user-defined in Simple)
inductive Device where
  | Primary : Device
  | Secondary : Device
  | Inference : Device
  | Backup : Device
deriving Repr, DecidableEq

namespace Device

-- Device to natural number mapping
def toNat : Device → Nat
  | Primary => 0
  | Secondary => 1
  | Inference => 2
  | Backup => 3

-- Devices are distinct
theorem primary_ne_secondary : Primary ≠ Secondary := by
  intro h
  cases h

theorem primary_ne_inference : Primary ≠ Inference := by
  intro h
  cases h

theorem secondary_ne_inference : Secondary ≠ Inference := by
  intro h
  cases h

end Device

-- GPU-wrapped value with device type parameter
structure Gpu (α : Type) (d : Device) where
  value : α
  device : Device
  device_eq : device = d
deriving Repr

namespace Gpu

-- Get the device of a GPU value (type-level)
def deviceOf {α : Type} {d : Device} (_ : Gpu α d) : Device := d

-- Get the inner value
def get {α : Type} {d : Device} (x : Gpu α d) : α := x.value

-- Create GPU value
def make {α : Type} (d : Device) (x : α) : Gpu α d :=
  { value := x, device := d, device_eq := rfl }

-- Transfer to different device
def transfer {α : Type} {d1 : Device} (d2 : Device) (x : Gpu α d1) : Gpu α d2 :=
  { value := x.value, device := d2, device_eq := rfl }

-- Device equality
theorem device_type_correct {α : Type} {d : Device} (x : Gpu α d) :
  x.device = d := x.device_eq

-- Transfer preserves value
theorem transfer_preserves_value {α : Type} {d1 d2 : Device} (x : Gpu α d1) :
  (transfer d2 x).value = x.value := rfl

-- Transfer changes device
theorem transfer_changes_device {α : Type} {d1 d2 : Device} (x : Gpu α d1) :
  (transfer d2 x).device = d2 := rfl

end Gpu

-- Function with GPU annotation
structure GpuFunction (d : Device) (α β : Type) where
  impl : α → β
  device : Device
  device_eq : device = d

namespace GpuFunction

-- Execute function (wraps result in Gpu)
def apply {d : Device} {α β : Type} (f : GpuFunction d α β) (x : α) : Gpu β d :=
  Gpu.make d (f.impl x)

-- Function device is correct
theorem device_correct {d : Device} {α β : Type} (f : GpuFunction d α β) :
  f.device = d := f.device_eq

-- Application returns correct device
theorem apply_device {d : Device} {α β : Type} (f : GpuFunction d α β) (x : α) :
  (f.apply x).device = d := rfl

end GpuFunction
