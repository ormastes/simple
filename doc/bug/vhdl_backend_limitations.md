# VHDL Backend Limitations

**Status:** Active
**Backend:** `--backend vhdl` / `SIMPLE_ENV=vhdl`
**Output:** Text source (`.vhd` files) — not executable

## Mode Restrictions

VHDL is a text-source backend (like the C backend). It generates `.vhd` source files only.

- **Interpreter mode:** Not applicable — VHDL is not executable
- **JIT mode:** Not applicable — VHDL is not executable
- **AOT mode:** Generates `.vhd` source files (the only valid mode)

## Unsynthesizable Types

These types cannot be mapped to synthesizable VHDL constructs:

| Type | VHDL Output | Reason |
|------|-------------|--------|
| `f16` | `-- ERROR: f16 not synthesizable` | No native float in VHDL synthesis |
| `f32` | `-- ERROR: f32 not synthesizable` | No native float in VHDL synthesis |
| `f64` | `-- ERROR: f64 not synthesizable` | No native float in VHDL synthesis |
| Pointers | `-- ERROR: pointers not synthesizable` | VHDL has no pointer concept |

## MIR Instruction Coverage

The following MIR instructions produce stub/warning comments instead of VHDL:

- **Function calls** (`Call`) — emits `-- Unsupported instruction: Call(...)`
- **Indirect calls** — not supported
- **Memory operations** (`Alloc`, `Load`, `Store`) — not synthesizable
- **Return statements** (`Return`) — entity outputs are mapped as ports instead
- **String operations** — not synthesizable
- **Dynamic dispatch** — not supported

## Supported MIR Instructions

- `Const` — signal assignment from literal
- `Copy` / `Move` — signal assignment
- `BinOp` — arithmetic, comparison, bitwise (add, sub, mul, div, and, or, xor, shifts)
- `UnaryOp` — negation, bitwise not
- `Nop` — ignored
- `VhdlProcess` — combinational, clocked, async-reset processes
- `VhdlSignalAssign` — signal assignment with optional delay
- `VhdlVarAssign` — variable assignment
- `VhdlPortMap` — component instantiation
- `VhdlResize` — resize operation
- `VhdlSlice` — signal slicing
- `VhdlConcat` — signal concatenation

## Known Issues

1. **`bin/simple build --backend vhdl` broken** — the `--backend` CLI flag causes
   "function expects 0 argument(s)" error for ALL text-source backends (C, VHDL).
   This is a pre-existing CLI build command bug, not VHDL-specific.
   Workaround: use `SIMPLE_EXECUTION_MODE=vhdl` (same bug currently).
2. **Comparison operators** produce VHDL conditional expressions that may not be
   synthesizable with all tools (uses `'if ... then ... else ...'` pattern)
3. **Integer constants** always use `to_signed(val, 64)` regardless of target width
4. **No testbench generation** — only synthesizable RTL is produced
