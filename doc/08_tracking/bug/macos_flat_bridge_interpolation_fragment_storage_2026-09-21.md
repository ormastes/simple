# Flat AST bridge retains one fragment array entry per interpolation character

- Status: source fix implemented; behavioral verification blocked.
- Scope: focused allocation owner found while auditing the P1
  `bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20` and
  `selfhosted_stage4_interpreter_string_interpolation_broken_2026-07-30`
  database entries on macOS. Neither parent issue is closed by this change.
- Base: `3b0328f41b2`; isolated branch `fix/astra-parser-todo3-20260921`.

## Defect and change

`flat_bridge_build_string_interps` in
`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` retained every
one-character text in `inner_parts` and joined that array at each closing
brace. A fragment of length N required N retained array entries in addition
to the final text. The core parser already records bounds and copies the
completed region once. The rich AST bridge now uses that same bounded slice.

The existing depth and escape rules, conversion ordering, span propagation,
and fail-closed behavior are preserved. Per-character scanning still exists;
this removes fragment storage, not all scan allocations. No RSS or runtime
speedup is claimed, and the historical whole-build memory failure has not
been reproduced or resolved by this focused change.

## Regression and evidence

`test/01_unit/compiler/parser/flat_bridge_interpolation_slice_spec.spl`
covers expression order and source spans, nested braces, escaped braces,
malformed/unmatched rejection and recovery, and absence of per-character
fragment storage in the production owner.

On 2026-09-21 this focused command was attempted from the isolated checkout:

```sh
/Users/ormastes/simple/.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple check src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl
```

The admitted pure-Simple Stage2 binary's SHA-256 is
`e1c0f79a7f0bc9b42df99b1219293e9c3852742a24843e07f96e81d5dcbcd81a`.
Its directory contains `stage2-provenance.receipt` and `stage2-sanity.receipt`.
It exited 1 with `error: unknown command 'check'`; log:
`/tmp/astra-parser-todo3-stage2-check.log`. The unsupported command fails closed.

Before that provenance was supplied, two checks were mistakenly attempted
with `/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple`
(SHA-256 `2a59a9cbc17e7e078b2b4dbb44bad7f865a0aa201cbd21405059b412c6c033ba`).
The coordinating audit identified that release-slot binary as a Rust seed.
Those diagnostics are explicitly excluded from verification evidence. Both
reported `ERROR: no admitted cached self-hosted check worker artifact is
available`; logs:
`/tmp/astra-parser-todo3-source-check.log` and
`/tmp/astra-parser-todo3-spec-check.log`. No behavioral PASS is claimed.

The focused SSpec, compiler/lib checks, and MCP/native smoke remain pending
an admitted runnable toolchain. No full bootstrap was run. The shared bug/TODO
databases and files owned by the preceding repair commits were not edited.

## Allocation regression follow-up

The regression now includes an 8,192-character suffix in a completed
interpolation identifier and checks the complete converted identifier value.
A second case calls the production bridge with 32-byte and 65,536-byte
unfinished regions, measuring each call with the production
`std.nogc_sync_mut.sffi.host.heap_array_capacity_bytes` facade. The input text
and span are constructed before either measurement. Because no closing brace
is present, neither call invokes the inner expression parser.

The test requires nonnegative capacity deltas and at most 4 KiB more array
storage for the large input. The old `inner_parts` algorithm retains at least
65,536 text slots (512 KiB on the native runtime), while the corrected scanner
retains only its constant-sized result array. This observable allocation
assertion complements the source-shape guard; it does not depend on searching
production text. A live 2,048-element integer array calibrates the counter and
requires at least 16 KiB of reported growth, so inert accounting cannot turn
the test green.

This allocation case requires the native runtime's array-capacity accounting
and no automatic collection during the measured call. A runtime without the
counter must report an unavailable-symbol/qualification failure; it must not
skip the assertion or substitute zero. The added cases have not been executed:
the admitted Stage2 `check` command remains unsupported and no admitted SSpec
runner was supplied. Before/after runtime failure/pass remains pending.
