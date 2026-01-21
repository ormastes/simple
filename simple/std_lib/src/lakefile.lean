import Lake
open Lake DSL

package SimpleVerification where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

/-!
# Simple Language Verification - Consolidated Lake Project

This Lake project manages all colocated Lean 4 verification files alongside
Simple (.spl) source files.

## Directory Structure

```
simple/std_lib/src/
├── memory/proofs/
│   └── capabilities.lean       -- Reference capability system verification
├── core/proofs/
│   ├── visibility.lean         -- Visibility and export model
│   └── module_resolution.lean  -- Module path resolution
├── macro/proofs/
│   └── auto_import.lean        -- Macro auto-import model
├── compiler/proofs/
│   └── pattern_exhaustiveness.lean  -- Pattern matching exhaustiveness
├── ml/proofs/
│   ├── TensorDimensions.lean   -- Tensor dimension inference
│   └── TensorMemory.lean       -- Tensor memory verification
└── gpu/proofs/
    └── (future: GPU type verification)
```

## Building

```bash
cd simple/std_lib/src && lake build
```

## Properties Verified

- **Memory Safety**: Reference capabilities prevent data races
- **Module System**: Visibility and resolution are deterministic
- **Pattern Matching**: Exhaustiveness checking is sound
- **Tensor Types**: Dimension inference and memory bounds
-/

-- Memory capability verification
@[default_target]
lean_lib MemoryCapabilities where
  roots := #[`capabilities]
  srcDir := "memory/proofs"

-- Core verification (visibility, module resolution)
lean_lib CoreVisibility where
  roots := #[`visibility]
  srcDir := "core/proofs"

lean_lib CoreModuleResolution where
  roots := #[`module_resolution]
  srcDir := "core/proofs"

-- Macro verification
lean_lib MacroAutoImport where
  roots := #[`auto_import]
  srcDir := "macro/proofs"

-- Compiler verification (pattern matching)
lean_lib CompilerPatternExhaustiveness where
  roots := #[`pattern_exhaustiveness]
  srcDir := "compiler/proofs"

-- ML/Tensor verification
lean_lib TensorDimensions where
  roots := #[`TensorDimensions]
  srcDir := "ml/proofs"

lean_lib TensorMemory where
  roots := #[`TensorMemory]
  srcDir := "ml/proofs"
