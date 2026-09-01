# Compiler-owned source-to-LLVM IR architecture

<!-- codex-architecture -->

## Status

Accepted for this implementation lane.

## Decision

The compiler driver owns `compile_source_to_llvm_ir(source_path,
target_triple, bare_metal)`. It returns a typed bundle containing parallel
module-name and LLVM-text arrays plus a fail-closed error/exit status.

The driver executes the real frontend and middle-end phases, lowers every
loaded source with a `MirTargetContext` derived from the explicit triple, then
translates every MIR module independently. LLVM modules remain independent
because their headers, declarations, global namespaces, and metadata are
complete compilation units. The CLI compiles each unit to an object and links
the object set.

`LlvmIRBuilder` retains the scalar fields of the `LlvmTargetTriple` supplied at
construction. It no longer re-reads target environment while emitting a
header. `MirToLlvm` gains explicit target-config and entry-module paths while
the existing environment-compatible entrypoints remain available to legacy
driver flows.

`app.io._CliCompile.compile_llvm_ir_facade` is a one-call adapter imported by
the two compile implementations and the bootstrap diagnostic. It is not
re-exported from `app.io` or `app.cli`.

## Layering

```text
app compile command
  -> app.io._CliCompile.compile_llvm_ir_facade
    -> compiler.driver.driver_source_llvm_ir
      -> frontend/HIR/MIR driver phases
      -> explicit MirTargetContext
      -> explicit LlvmTargetConfig
      -> one MirToLlvm translation per MIR module
```

The compiler has no upward dependency on app code. The former Rust/raw-runtime
path disappears after the final Simple call site migrates.

## Failure policy

- Explicit `host`/`native` aliases are rejected; callers must supply a triple.
- `bare_metal=true` requires a `none`/`simpleos` OS component.
- `bare_metal=false` rejects `none`/`simpleos`.
- Unsupported architectures and malformed triples fail before source loading.
- Missing or empty MIR/IR units fail the whole operation.
- A single-output `llvm-ir` or `object` request refuses a multi-unit bundle.
- ELF routes require a source-defined `_start`; no wrapper is fabricated.
- The current bare-metal ELF linker facade admits only x86/x86_64, the two
  architectures for which it has a real linker-script/emulation policy.

## Startup and hot path

There is no request-loop cache: this is a compile operation. The facade is
selective and never exported broadly. Explicit target resolution avoids LLVM
capability probes and host/environment target discovery. Result arrays are
allocated once at module count and filled by index; no aggregate LLVM string is
built.

## MDSOC assessment

No virtual capsule or feature transform is warranted. This is a linear driver
product and an app adapter. Introducing runtime composition would enlarge the
bootstrap closure and weaken target authority.
