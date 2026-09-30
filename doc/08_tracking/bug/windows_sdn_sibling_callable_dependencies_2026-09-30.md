# SDN parser sibling triggers unresolved SdnSpan

Status: reduced to a four-module pure-Simple HIR reproducer; canonical class
reuse binding fix and prevention specs prepared by source review. The fix and
new specs are unexecuted. Stopped after the three authorized verification cycles.

## Authority and route

Isolated source: `D:/dev/simple-windows-local-selftype-20260930`, base commit
`5eb63efa451298e05201c06934f64b76ead7a8f8`, plus the three fixtures in this change.
Producer: immutable self-hosted Windows Phase 2 executable
`D:/dev/simple-windows-field-static-recovery-20260930/continuation/cbe4a8df41e14287005e258cf57f8e16bd096dee0c09954b39495446e5ab19cc/producer.exe`.
Its SHA-256 is the containing directory name. Producer source is separately
bound to `7c1f0a379c61ad60a5a396cdc68b290e34f0f0ba`; consumer-source changes do not
modify that executable.

Every invocation used `native-build` with a positional fixture, `--backend llvm`,
`--target x86_64-pc-windows-msvc`, `--runtime-bundle core-c-bootstrap`,
`--runtime-path` pointing at the reviewed retained `stage2-runtime-authority`,
`--entry-closure`, `--mode one-binary`, and a separate per-entry cache.
There were no explicit `--entry` or `--source` arguments. Logs show the
pure-Simple CompilerDriver phase trace. `SIMPLE_SCV_INVENTORY_COLD_INIT=1` was
set for the new cache roots; stub fallback and bootstrap delegation stayed
disabled. No Rust-backed invocation is counted in this investigation.

## Bounded results

| Cycle | Positional entry under `test/fixtures/native_local_class_selftype/` | Result |
| --- | --- | --- |
| 1 | `main.spl` | One module; native build PASS in 26.0874511 seconds; run exit 0 in 0.0342006 seconds, output `local class self type: 42` |
| 2 | `sdn_direct.spl` | Two modules; HIR PASS; MIR then fails on unrelated `SdnValue` operations including `contains_key`, `to_float`, and `get`; terminal exit 1 in 5.7964353 seconds |
| 3 | `sdn_parser_sibling.spl` | Four modules; reproduces exactly four `unresolved type: SdnSpan` HIR errors attributed to `src/lib/common/sdn/value.spl`; exit 1 in 1.6058819 seconds |

The successful binary is
`build/native_probe/phase2/cbe4a8df41e14287005e258cf57f8e16bd096dee0c09954b39495446e5ab19cc/local-class-entry/selftype_probe.exe`,
SHA-256 `71a564723f14ee2f95d8ba80d41bd87fa3cfd63c3d38fc7889b7a496b3e21b3d`.
Only this executable was run in this investigation. This is one additional
small component sanity result, not a full compiler/test-runner qualification.

The evidence root is the same `build/native_probe/phase2/<producer-sha>/`
directory, with subdirectories `local-class-entry`, `sdn-direct-entry`, and
`sdn-parser-sibling-entry`. Each contains exact arguments, consumer revision,
fixture and producer hashes in `build.started.json`, terminal status/timing in
`build.result.json`, and complete stdout/stderr. The successful first probe
also has `run.result.json` and run logs. The third probe recorded HIR cache
hits 0, misses 4, stores 3.

## What the reduction establishes

The four annotations in the original `SdnSpan` class (empty return at 12:26,
at return at 15:45, merge parameter at 18:27, merge return at 18:39) are not
sufficient to cause the failure: the real module passes HIR when imported
directly. The earlier general local-class/self-type hypothesis is therefore
not supported. The single-module control also executes both static methods
and the typed instance method correctly.

Adding `std.common.sdn.parser` is sufficient to reproduce the HIR failure,
without the original 75-module I/O facade closure. The four discovered modules
are the fixture, parser, structural scalar helper, and value module. The
parser's signatures include `Result<(SdnValue, Dict<text, SdnSpan>), text>`
and `Result<(SdnValue, Dict<text, SdnSpan>, [SdnIssue]), text>`.

## Source-only lead and next scoped work

`module_build.spl` resolves package sibling symbols before declaring local
symbols. `register_package_sibling_symbols` expands sibling composite and
callable surfaces through `register_imported_symbol`. Imported free functions
materialize their owner-scope type dependencies, then lower projected callable
types. Recursive tuple/generic dependencies that lead back to the module now
being lowered must bind its canonical class identity before signature
projection. That registration/re-entry boundary is the next inspection target;
the exact failing operation is not yet proven.

Both the producer's source revision and the fresh-main source already contain
the callable builtin-type guard in `materialize_imported_callable_dependency`.
The noisy builtin re-export diagnostics alone do not establish that this guard
is missing or identify the fatal bug. Do not repair the consumer by adding an
import of its own class, or suppress diagnostics as a substitute for binding.

An independently scoped follow-up can inspect the imported callable dependency
route with the four-module fixture and propose the smallest owner-binding fix.
Neither the successful one-module control nor the old 75-module facade should
be rerun without a concrete change. No broad source changes were made here.

## Source-only follow-up: canonical reuse skipped lexical publication

`SymbolTable.define_with_binding` in `src/compiler/20.hir/hir_types.spl` returned
an existing qualified class ID before inspecting `bind_lexical`. Imported
callable dependency registration allocates the defining module's class with
lexical publication disabled, then binds a qualified spelling. Later,
`declare_module_symbols` calls `define` with lexical publication enabled, but
the canonical-ID early return omitted both the current-scope name and the
`exact_symbols` index. This matches the sibling/direct differential; a direct
declaration without prior dependency allocation uses the ordinary path and
publishes both indexes.

The patch retains the canonical ID and, only when `bind_lexical` is true,
inserts an absent exact-name entry and calls `bind_local_type_if_free` for the
current scope. It mirrors the ordinary allocation path: a competing short name
in the same scope wins, while a child scope may bind the requested owner without
replacing its parent's binding. Requests with `bind_lexical=false` stay nonlocal.
Other type kinds retain their existing registration paths.

Prepared, **unexecuted** prevention coverage:

- `canonical_class_rebinding_spec.spl`: nonlexical-to-lexical publication,
  repeated nonlexical registration, same-scope competing owner, child-scope
  shadowing/restore, exact lookup, qualified lookup, and unchanged allocation ID.
- `sibling_callable_owner_selftype_spec.spl`: parser-shaped nested
  `Result<(i64, Dict<text, SpanProbe>), text>` sibling signature plus four local
  class self-type annotations, requiring zero HIR errors and canonical binding.
- The already recorded four-module fixture remains the native reproducer for
  qualification with a newly compiled producer. No fourth probe was run here.

## Interpreter analogue and numeric widths

The app interpreter uses a separate registration path:
`src/app/interpreter/module/evaluator.spl` handles `Node.Class` by writing
`state.classes` and calling `interp.env.define` for the constructor. It has no
matching canonical-ID early return at that site. The core interpreter's
`module_loader_core.spl` also binds exports for a caller when loading an already
loaded module, and its `env_define` updates or inserts the current-scope entry.
These source paths do not share HIR's `SymbolTable.define_with_binding` defect.
No interpreter execution or broader interpreter correctness is claimed, and no
interpreter patch is justified by this evidence.

Numeric width variants: **N/A**. The failure is publication of nominal owner/name
bindings; it does not inspect integer width, signedness, or numeric values.
