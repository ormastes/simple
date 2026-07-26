# Interpreter Shared Text Compile WIP

## Status

Compile-green WIP retained by higher review. Do not fold or independently fix
the owned files listed in
`doc/03_plan/design/interpreter_shared_text_owned_files.txt`.

## Bounded Compile Evidence

- Cycle 1 after coherent `Value::Str(Arc<String>)` flip: 614 errors.
- Compiler-assisted/mechanical constructor conversion applied.
- First continuation cycle set: 217 errors; mandatory cap reached.
- Second continuation cycle set: 131 -> 46 -> 8 errors; mandatory cap reached.
- Final leaf pass: two shifted inference sites, then compiler check PASS.
- Authoritative command: `cargo check -p simple-compiler --message-format short`
  from `src/compiler_rust`.

## Focused Gates

PASS, each run once:

- shared clone preserves Arc/source-buffer identity;
- real executor field-map COW shares 8-byte and 1 MiB source buffers;
- explicit concat alias remains unchanged;
- Unicode index/slice semantics;
- RuntimeValue Unicode roundtrip;
- BridgeValue string behavior.
- immutability/deep-copy source audit (0 findings);
- content equality/key/display/ordering;
- case/replace/slice alias isolation;
- Unicode Value/Bridge and JSON/SDN byte roundtrips.

The single planned full `simple-compiler` test is not green: 2,895 passed, 239
failed, 1 ignored. The run exhausted the host to 2.2 GiB free, left an orphan
native-build child, and grew generated build data by about 19 GiB; failures span
unrelated loader, MIR, pipeline/native archive, runtime, and value areas. The
orphan was terminated and only safe Cargo incremental data was removed. Per the
one-run rule, the full suite is not repeated. Post-RSS remains unauthorized
pending higher disposition.

Targeted exact diagnostics classified the two apparent value/runtime failures:
the unchanged array bridge constructs a runtime array while its pre-existing
test incorrectly invokes tuple accessors, and the unchanged type matcher keeps
`Float` (`f64`) distinct from `Float32` while its pre-existing test expects an
`f64` value to match `f32`. Representative loader, MIR, and native-archive
tests also fail independently on an absent `env_get` export, an expected-error
mismatch, and a missing required core-C ABI symbol. These are workspace blockers,
not evidence of a SharedText semantic regression; no unrelated repairs were made.

Concat's remaining `Arc::make_mut` was found by the immutability audit and
replaced with a newly allocated `Value::text`, preserving explicit aliases.
Await higher review before post-RSS or parser scaling; no bootstrap is allowed.

Fixed post-migration RSS ceilings:

- Parser: 220,321 KiB.
- 10,000 distinct short texts: 494,199 KiB.

The post-migration release seed rebuild now passes at the documented
`src/compiler_rust/target/release/simple` path. It ran low-priority with one
Cargo job while foreign native builds were active, so its elapsed time is not
performance evidence. The two one-shot RSS/timing fixtures remain pending a
quiet host.

## 2026-07-26 bounded parser result

The current release seed completed the 11/22 KiB parser oracle after two
harness defects were removed: valid `self.field` no longer emits
`PythonSelf`, and the fixture uses the seed-exported microsecond clock instead
of an unavailable monotonic-millisecond symbol that forced JIT fallback.

- 11 KiB: 1,061 ms
- 22 KiB: 4,172 ms
- Wall time: 9.90 s
- Maximum RSS: 968,524 KiB

Absolute latency now passes the 15-second ceiling. The 3.93x scaling ratio and
RSS ceiling remain red, so the 493-source bootstrap is still unauthorized.
An equal-size, disjoint-identifier control measured 500ms/504ms, ruling out
growth of the global short-token cache. No production optimization is
authorized until a fresh bounded cycle separates lexer-only 440/880 timing
from parser/AST timing.

That fresh cycle measured lexer-only 440/880 at 539ms/5,272ms. Two
field-to-local array bindings in `scan_ident` and `scan_number` were cloning
the complete `source_chars` array for every identifier and number. Replacing
the aliases with direct indexed field reads made the unchanged parser oracle
pass at 33ms/75ms (2.27x), 4.62s wall time, and 205,192 KiB max RSS. The
small-fixture latency, ratio, and 220,321 KiB RSS gates are now green; the
493-source and pure-compiler acceptance gates remain pending.
