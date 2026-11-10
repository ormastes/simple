# Phase3 strict-JIT `sffi_env_get_i64` blocker

Status: OPEN / release-blocking for the Phase3 core-C candidate.

## Observed fact

At commit `c74500a9cf58ba63ee5efd2a224cc3812d0536ba`, a fresh bootstrap
producer succeeded, then the single contained Stage4 candidate failed before
any cache object or output binary was produced:

```text
SIMPLE_JIT_STRICT: unresolved external symbol 'sffi_env_get_i64'
would NULL-jump in JIT; refusing to fall back to the interpreter
```

The candidate used `SIMPLE_EXECUTION_MODE=jit`,
`SIMPLE_NO_STUB_FALLBACK=1`, `SIMPLE_JIT_STRICT=1`, and
`SIMPLE_JIT_STRICT_ALL=1`. Its exact command, producer identity, containment,
and hashes are recorded in
`build/native_probe/corec-argv-provider/phase3-char-provider-c74500a9cf5/receipt.txt`:

- producer: PASS, 3m32s, bootstrap SHA-256
  `e98adb2c87e945328a197c4154cc4800e88765c22a6dcae76109d73183e692aa`;
- candidate: status 1; stderr SHA-256
  `07bb229c66ef9bd433f2d6a1d2647b84727fd5daf999ae56e5f2fd26396c5951`;
- candidate cache files: 0; binary: absent; no descendants after terminal.

An immediately preceding fresh producer/candidate at
`210e42caacd2a1c0d9e134e0d5a3f14f4b7769e7` fail-closed on the separate
legacy `text_dot_from_char_code` symbol. That defect was repaired in
`c74500a9cf5`; its focused static-JIT regression passed. The current failure
therefore is not evidence that the character-provider repair was ineffective.

## Established ownership facts

- `src/compiler/10.frontend/core/_Ast/decl_nodes.spl` declares the real
  provider `rt_env_get_i64` and defines private helper
  `_sffi_env_get_i64` that calls it.
- `src/compiler_rust/common/src/runtime_symbols.rs` registers
  `rt_env_get_i64`; no provider named `sffi_env_get_i64` exists or should be
  added.
- Commit `210e42caacd` added a narrow parser/flattened-HIR/MIR/static-JIT
  regression. It proves that the declaration owner retains the exact private
  helper spelling and that flattened `ast_decl_arena_default` calls
  `_sffi_env_get_i64`, not `sffi_env_get_i64`.

## Not established

The narrow regression does **not** yet capture the full
`native_build_worker.spl` flattened graph or the post-lowering declaration map
which yielded the bare import. It is therefore unproven whether the loss occurs
in an import-qualified call target, post-MIR transform/inlining, or runtime
declaration registration in that larger worker graph. Renaming the helper or
adding a fake `sffi_env_get_i64` runtime symbol would hide the ownership error
and is prohibited.

## Deterministic next proof and fix condition

Build a bounded worker-graph MIR/declaration-map probe (no full candidate)
that emits, for the first `sffi_env_get_i64` import:

1. its declaring MIR function and call target before/after inline expansion;
2. all function IDs/declaration linkage entries for `_sffi_env_get_i64`,
   `sffi_env_get_i64`, and `rt_env_get_i64`; and
3. the flattened source owner and module-qualified spelling where the target
   first changes, if it changes.

Accept a fix only when that probe proves one concrete loss boundary and an
exact strict-JIT regression confirms the graph declares/calls the local helper
or canonical `rt_env_get_i64`, never a synthetic bare provider. Then a new
candidate may be authorized.

## Gate impact

The Phase3 candidate is not admissible: it produced no executable, so
`--version`, `native-build --help`, and all downstream tests/tools are
not admissible. No interpreter fallback, stub, alias provider, or candidate
retry is acceptable as substitute evidence.


## Triage 2026-11-10 (p3-lib2 lane, work/p3-lib2-20261110)

**Verdict: SUPERSEDED — fixed on origin/release/1.0.0 base (PR #7597, 2026-11-07);
the doc's acceptance condition is met in-tree.**

- The flattened-alias loss boundary is proven and repaired by the SFFI alias
  table: `sffi_alias_target("sffi_env_get_i64") == Some("rt_env_get_i64")`
  (`compiler/src/codegen/instr/calls.rs:3856`, comment cites this exact import
  alias). The remap is wired into JIT import resolution at
  `codegen/jit.rs:492` (mirrored in `common_backend.rs:140`): a direct Call to
  `sffi_env_get_i64` also requires the canonical `rt_env_get_i64` to resolve,
  and `rt_env_get_i64` is registered (`common/src/runtime_symbols.rs:881`). A
  synthetic bare `sffi_env_get_i64` provider was NOT added, per the doc.
- Exact strict-JIT regression demanded by the doc exists and is asserted:
  `codegen/jit_tests.rs::test_jit_sffi_env_i64_alias_uses_registered_runtime_provider`
  (line 455) compiles the flattened `extern fn sffi_env_get_i64` module and runs
  it (asserts `provider.get_symbol("sffi_env_get_i64").is_none()`, provider has
  `rt_env_get_i64`, call returns the default 41). Complementary MIR-level
  guard: `compiler/src/pipeline/native_project/tests.rs:601` proves the
  flattened decl-arena graph calls `_sffi_env_get_i64` and never lists bare
  `sffi_env_get_i64` in `mir.extern_fn_names`.
- Host-limit note: cargo test execution of `compiler_rust` is outside this lane's
  scope (agent-10 owns compiler_rust); the fix + both regression tests are
  present and wired in the current tree.
