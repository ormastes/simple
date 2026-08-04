# Duplicate `backend_types` terminal declarations (third copy still open)

Status: PARTIALLY FIXED 2026-08-04. Two of three copies reconciled; the
`10.frontend/core` copy is still an independent divergent declaration.

## What was fixed

`src/compiler/70.backend/backend_types.spl` (call it A) ends with

    export use compiler.backend.backend.backend_types.*

so it already re-exported every name from
`src/compiler/70.backend/backend/backend_types.spl` (B) — and it ALSO declared
its own `BackendKind`, `CompiledSymbol` and `CompiledSymbolKind`. A single
`use compiler.backend.backend_types.*` therefore delivered each of those three
names from two terminal modules at once, which blocked Stage 3 self-host:

    error: in-process native-build: HIR lowering error in
    src/compiler/backend/backend/interpreter.spl: enum payload dependency
    `CompiledSymbolKind` conflicts:
      `compiler.backend.backend_types::CompiledSymbolKind::enum` vs
      `compiler.backend.backend.backend_types::CompiledSymbolKind::enum`

The `src/compiler/backend -> 70.backend` symlink is NOT involved. Both module
paths are derived from real, distinct files: A from `70.backend/backend_types
.spl` and B from `70.backend/backend/backend_types.spl`. Stripping the numeric
directory prefix yields `compiler.backend.backend_types` and
`compiler.backend.backend.backend_types` respectively, with or without the
symlink.

A no longer declares the three names; it imports them from B and lets the
pre-existing wildcard re-export carry them to every importer. One terminal
declaration per name.

## What is still open

`src/compiler/10.frontend/core/backend_types.spl` (C) declares a THIRD
`BackendKind` and a third `CompiledSymbolKind`. All three `BackendKind`
declarations had a DIFFERENT variant order, which matters because same-named
enums collapse in the global enum registry — whichever registers first fixes the
discriminants for every importer, so the other importers silently get the wrong
discriminant. Measured orders, by index of `Byl`:

| copy | file | `Byl` index | extra variants |
|------|------|-------------|----------------|
| A (removed) | `70.backend/backend_types.spl` | 13 | `Custom(name: text)`, zero uses in tree |
| B (kept)    | `70.backend/backend/backend_types.spl` | 6 | — |
| C (open)    | `10.frontend/core/backend_types.spl` | 9 | — |

`CompiledSymbolKind` is `Function, Data, Const` in all three, so that name is
structurally safe today; only its two-terminal visibility was the Stage 3
blocker. `CompiledSymbol` field order also differed between A
(name/address/size/kind) and B (name/kind/address/size).

C was left alone in the Stage 3 fix because no importer currently shares a
lowering scope with both C and B, so it does not reproduce the payload-conflict
error. It remains a latent miscompile via the global-registry collapse.

## Fix direction for C

Make C import `BackendKind` / `CompiledSymbolKind` from B the same way A now
does, or — if the frontend must not depend on the backend layer — give C's enums
distinct names. Do NOT "sync the orders by hand"; three hand-synced copies is
what produced this in the first place (the in-tree note that used to sit above
A's `CompiledSymbolKind` asked exactly that and still drifted).

## Reproduction

Replay the recorded Stage 3 command against the Stage 2 self-hosted binary
(bare positional `.spl` form, no `--entry` / `--source`, cranelift backend):

    build/bootstrap/stage3/<triple>/stage2-admitted/simple native-build \
      --target <triple> --backend cranelift --runtime-bundle core-c-bootstrap \
      --mode dynload -o <out> src/app/cli/bootstrap_main.spl
