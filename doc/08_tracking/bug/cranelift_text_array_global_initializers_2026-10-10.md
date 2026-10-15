# Cranelift stored text and array module initialization

Status: focused fixes verified by native AArch64 execution; full compiler/MCP
admission remains pending. This is not a release or merge PASS.

## Defects and contracts

Mutable or exported plain text literals previously retained `MirConstValue.Str`
static payloads. Cranelift correctly rejected these: compiler-process text
pointers cannot be embedded in a target object. Route stored literals through
the existing guarded module initializer, create an empty `Opaque("str")` slot,
and construct/store the runtime text value. The provisional slot has this same
type before bootstrap function lowering. Private immutable literals stay inline;
interpolation keeps its existing runtime route.

The original MC/DC closure also contains array globals. MIR already creates
arrays in its guarded initializer, and Cranelift already represents array SSA
values and global loads/stores as pointer-width runtime handles. Its static
allowlist nevertheless rejected their empty slots. Admit only `Array` statics
with no static initializer payload. Nonempty static payloads, unsupported
aggregate kinds, and imported globals retain their explicit rejection.

Neither change writes host pointers into target data, omits initialization,
invents success, or weakens the no-stub gate.

## Focused evidence

Base revision: `fb05765b78b6f0792c0f1ba270470ecf9bdad23b`.
Isolated worktree: `/home/yoon/dev/simple-cranelift-text-globals-20261010`.
Evidence directory: `build/native_probe/text-globals/` in that worktree.

- `baseline-cold.log`: parent native compiler rejects the text fixture's
  `PUBLIC_TEXT` static.
- `compiler-build.log`: diagnostic compiler construction, 16 compiled,
  1201 reused, zero failed, 42.8 seconds. SHA-256:
  `19846071a0a9eb549b56723fdd4b0d389b6694dc255408fb2f191bb5ca8a20bd`.
- `arm.log`: `native_text_module_globals.spl` builds with Cranelift;
  its AArch64 executable exits zero after eight checks: private/exported/empty/
  inferred mutable text, dependent declaration-order initialization, replacement,
  and rereads. Executable SHA-256:
  `a4ffdde95e83a1841b1880b01b6264f7d9561516c7b4e8bb58c3aa154c07c7c5`.
- `aspect_readiness.log`, `facet_registry.log`: text-only repair exposes the
  independent array-slot rejection for `_r_boundary_slots` and `_cat_last_error`.
- `compiler-arrays-build.log`: second diagnostic compiler construction,
  3 compiled, 1214 reused, zero failed, 37.8 seconds. SHA-256:
  `1dc9c6cc582ff9f4f5b65cf5d8ba658f7f41a711537ff6167953d51201f34ead`.
- `array-arm.log`: `native_array_module_globals.spl` builds with Cranelift;
  its AArch64 executable exits zero after eight checks covering empty and
  nonempty arrays, integer and text elements, replacement, and rereads.
- `aspect_readiness-array.log`, `facet_registry-array.log`: both original
  failing modules now emit real AArch64 relocatable objects with Cranelift.
- `riscv-llvm18.log`: text fixture emits an ELF64 RISC-V relocatable object
  using the explicit entry/target route and `SIMPLE_LLVM_BIN=/usr/lib/llvm-18/bin`.
  LLVM 18.1.3 `llc` SHA-256:
  `682c25e9be136578115664d3f62e067ddd8f2f3f92830c6d42d8c9cee2d74884`.
- Working direct-env guard passes; `git diff --check` passes; the required
  `doc/06_spec` executable-spec count is zero.

Both compiler constructions use the expressly authorized Rust bootstrap seed
only to produce a native Simple compiler. All fixture builds use those native
Simple compilers with `SIMPLE_NO_STUB_FALLBACK=1`. The private compiler cache
was cloned from the parent lane; its own validator accepted reuse. Historical
cache provenance is not fully bound cryptographically, so these are diagnostic
artifacts, not admitted release producers.

## Remaining gates and limitations

The MIR regression spec `test/01_unit/compiler/mir/text_module_global_initialization_spec.spl`
asserts nil text slots, exact runtime initializer store counts, and private
literal inlining. It is authored but not executed. The apparent canonical
release executable identifies itself as a Rust seed and fails on existing
`windows_redirected_process.spl` syntax. It is unsuitable as the normal test
runner; no further test attempt uses it.

`dynamic_aspect-array.log` and `dynamic_probe-array.log` retain a separate
explicit failure: imported `READINESS_FULL` needs declaration-only data support
in Cranelift. The current data SFFI combines declaration and definition; using
it would create duplicate global owners. This boundary is deliberately not
relaxed by the text/array repair and needs a separate complete import contract.

The first explicit RISC-V object attempt reached LLVM but the default `llc`
lacks RISC-V support (`riscv.log`). The LLVM 18 retry passes. RISC-V execution
is not claimed without its runtime/toolchain environment.

Full compiler/library/MCP/LSP checks, core runtime and MCP native smoke, and
the executable MIR regression remain mandatory before merge admission.

## Reproduction

Use the lane's native `simple-arrays` compiler for Cranelift probes and set
`SIMPLE_NO_STUB_FALLBACK=1` plus `SIMPLE_RUNTIME_PATH` to the frozen bootstrap
runtime directory. The single-module diagnostic route is:

```text
simple-arrays native-build test/fixtures/compiler/native_array_module_globals.spl --backend cranelift --threads 1 --cache-dir <isolated-cache> -o <arm-executable>
```

For RISC-V, set `SIMPLE_LLVM_BIN=/usr/lib/llvm-18/bin` and use the explicit
entry route; a positional single-file route does not honor the requested target:

```text
simple native-build --source test/fixtures/compiler --entry-closure --entry test/fixtures/compiler/native_text_module_globals.spl --backend llvm --target riscv64-unknown-linux-gnu --threads 1 --cache-dir <isolated-cache> --emit-object -o <riscv-object>
```
