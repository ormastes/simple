# JIT emits calls to runtime symbols that were never registered (`rt_value_unbox_int` family)

Status: FIXED 2026-08-11
Severity: BLOCKER (origin/main tip produced a JIT-broken compiler)

## Symptom

A pristine build of `origin/main` at `b6d717e62e2` failed at run time with:

```
unresolved external symbol 'rt_value_unbox_int'
```

The JIT lane then silently fell back to the interpreter.
`scripts/check/check-numeric-builtin-result-type.shs` reported 23 wrong
(empty strings) and `check-native-unwrap-enum-receiver.shs` failed.

The DEPLOYED binary (built 04:14 the same day) passed everything — the
registration existed only inside that binary's build, never in source. This
is the *stranded-in-binary / missing-in-source* shape: a working artifact is
not evidence that the source can reproduce it.

## Root cause — the registration mechanism IS the list

`src/compiler_rust/runtime/build.rs:52` parses
`pub const RUNTIME_SYMBOL_NAMES` out of
`src/compiler_rust/common/src/runtime_symbols.rs:381` and generates
`RUNTIME_SYMBOL_ENTRIES` (build.rs:102-116), the table
`register_static_runtime_symbols()` (`runtime/src/lib.rs:316`) publishes and
`StaticSymbolProvider::get_symbol` (`native_loader/src/static_provider.rs:26`)
answers from. `codegen/jit.rs:391` registers a JIT symbol only when that
provider (or the ELF fallback) resolves the name.

So a symbol absent from `RUNTIME_SYMBOL_NAMES` is **never registered**, no
matter that it is defined in the runtime and declared in
`codegen/runtime_sffi.rs`.

`rt_value_unbox_int` was:
- emitted: `codegen/instr/mod.rs:1495`, `codegen/cranelift_emitter.rs:788`
- spec'd:  `codegen/runtime_sffi.rs:555`
- defined: `runtime/src/value/sffi/value_ops.rs:80`, `src/runtime/runtime_native.c:2179`
- **absent** from `common/src/runtime_symbols.rs` `RUNTIME_SYMBOL_NAMES`

Nothing in the build fails when an emitted symbol is unlisted — the gap is
only observable at run time.

## Family audit (do not fix one and leave brothers)

Diffed every name codegen emits (`call_runtime_*`, `runtime_funcs.get`,
`declare_function`, `get_function`) against `RUNTIME_SYMBOL_NAMES`: 109
emitted, 15 unlisted. Of those 15, three are actually defined in a runtime and
were therefore genuinely broken; the rest have no definition anywhere
(`rt_await`, `rt_contract_check`, `rt_unit_bound_check`, `rt_generator_yield`,
`rt_future_*`, `rt_par_for_each`) or are monoio symbols reached by another
path.

Fixed (added to the list):
- `rt_value_unbox_int`     — Rust + C runtime; the reported failure
- `rt_struct_receiver_valid` — C runtime; added by today's `a1bcda91f6`, same gap
- `rt_dict_insert`         — C runtime; pre-existing, same shape

Verified clean by family: `rt_math_*` (33/33 listed), `rt_unwrap_*` (2/2,
`rt_unwrap_or_trap` landed correctly), `rt_value_*` (14/14 after this fix).

## Fix

`src/compiler_rust/common/src/runtime_symbols.rs` — three names added to
`RUNTIME_SYMBOL_NAMES` with a comment stating that listing here *is* the
registration and that codegen must not emit a call to an unlisted symbol.

## Verification (candidate `/mnt/data/cargo-target-clean/release/simple`)

```
PASS — 9 probe(s) checked                                   # check-deployed-binary-capabilities
PASS — 48 assertions checked across 2 lanes, 0 failures     # check-numeric-builtin-result-type
PASS — 4 checked                                            # check-native-unwrap-enum-receiver
```

## Follow-up (not done here)

There is no gate that fails when codegen emits a runtime symbol missing from
`RUNTIME_SYMBOL_NAMES`. That check is mechanical (the diff above is ~20 lines
of script) and would have caught this at build time rather than at run time.

## Follow-up IMPLEMENTED 2026-08-11

Added `#[test] every_emitted_runtime_symbol_is_registered_or_allowlisted` in
`src/compiler_rust/compiler/tests/runtime_symbol_registration_gate.rs`. It
re-derives, from source text, both sides of the diff the incident audit did by
hand:

- **Listed set**: parses `RUNTIME_SYMBOL_NAMES` out of
  `common/src/runtime_symbols.rs` with the exact same line-scan
  `runtime/build.rs` itself uses (copied, not imported, so the test stays
  honest about what the build actually sees).
- **Emitted set**: regex-scans every `.rs` file under `compiler/src/codegen/`
  for `rt_*` literals passed to the four name-resolution call shapes:
  `call_runtime_*(ctx, builder, "rt_x", ...)`, `runtime_funcs.get("rt_x")`,
  `.declare_function("rt_x", ...)`, `get_function[_ptr]("rt_x")`.
- Fails, naming every offending symbol, if `emitted - listed` is non-empty and
  not in `ALLOWED_UNLISTED` — the 12-name audited allowlist (`rt_await`,
  `rt_contract_check`, `rt_unit_bound_check`, `rt_generator_yield`,
  `rt_par_for_each`, `rt_future_get_ctx/get_state/set_state` — all undefined
  anywhere in the runtime — and `rt_monoio_future_get_ctx/get_result/
  set_async_state`, `rt_monoio_poll` — defined but registered through the
  monoio executor's own linkage, not this list).
- Also fails if any `ALLOWED_UNLISTED` name becomes newly listed (stale
  allowlist entry), and both extraction passes assert non-vacuity (file count
  / symbol count floors) so a path or pattern drift can't silently pass green.

Runs under plain `cargo test -p simple-compiler
--test runtime_symbol_registration_gate`; no new crate, no build.rs change,
no proc macro — uses `regex`, already a normal dependency of the crate.

**Negative control** (pristine worktree at `origin/main` `ec88f23e190`,
`CARGO_TARGET_DIR=/mnt/data/cargo-target-symgate`): removed `"rt_dict_insert"`
from `RUNTIME_SYMBOL_NAMES` — test failed, naming exactly `["rt_dict_insert"]`
and pointing at this bug doc in the panic message. Restored the line — test
passed. `cargo build` is unaffected (the test file only exists under
`compiler/tests/`, not compiled into the library or binary).

**Scope: which of the three runtimes does this gate, and why no more was
added.** The 2026-08-11 incident actually hit two independently-gated
runtimes, not one:
1. Hosted (Rust `runtime/src/value/...` and C `src/runtime/runtime_native.c`)
   via the JIT's `RUNTIME_SYMBOL_NAMES` registration list — this gate, added
   here. `runtime/build.rs`'s `collect_defined_runtime_symbols` scans BOTH the
   Rust runtime source and the C runtime dir to populate
   `RUNTIME_SYMBOL_ENTRIES`, so one list gates both hosted implementations;
   no second hosted-C-specific check is needed.
2. Baremetal (`examples/09_embedded/simple_os/arch/x86_64/boot/
   baremetal_stubs.c`), which failed differently the same day
   (`rt_value_unbox_int`, `rt_collection_remove` reported `FABRICATED-NEW` by
   commit `bb02bc5bd7b`) — this is **already gated** by an existing,
   independent, stronger mechanism:
   `generate_stub_object_freestanding` in
   `src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs`, which
   runs *inside the real freestanding linker pipeline*
   (`clang --target=x86_64-unknown-elf`) and inspects the linker's own
   unresolved-symbol list — not a static text heuristic — then NEW-ONLY
   ratchets any newly-fabricated (`return 0` weak-stub) symbol against
   `config/freestanding_fabricated_stub_baseline.sdn`, invoked from
   `scripts/check/check-simpleos-x86-kernel-elf.shs` and
   `scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs` during
   SimpleOS kernel builds. Because it reads real link-time truth (what the
   linker actually could not resolve) rather than re-deriving emitted-symbol
   sets from source text, it is strictly more precise than anything this
   text-based Rust test could add for the baremetal path, so no second check
   was written here — doing so would duplicate, not strengthen, existing
   coverage. Net: all three runtime implementations now have a build/link-time
   gate for this exact defect shape; none did before today.
