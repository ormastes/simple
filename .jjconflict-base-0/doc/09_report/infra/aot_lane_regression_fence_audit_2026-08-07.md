# AOT/native-build lane regression-fence audit — 2026-08-07

## Background

`bin/simple test` hard-defaults to the tree-walk interpreter. `TestExecutionMode`
(`src/lib/nogc_sync_mut/test_runner/execution_strategy.spl:14-19`) has exactly
five variants — `Native, Process, Safe, Container, ContainerSequential` — and
every one of them is a *process-isolation* mode ("Native" there means "run the
already-compiled test process directly, no ulimit/container wrapper"), **not**
a codegen backend. There is no AOT/LLVM variant. Confirmed by reading the enum
definition directly (not inferred from naming) — this is a genuine name
collision between "native process execution" and "native-build (LLVM AOT)
codegen", and it is exactly why specs cannot fence the AOT lane: no execution
mode in the runner ever routes through `native-build`/`simple compile --native`.

Consequence: any `*_spec.spl` claiming to cover AOT/native-build behaviour is
**structurally unable** to do so. The only real fence is a
`scripts/check/check-*.shs` script that invokes `native-build` or
`simple compile --native` directly and asserts on literal process output.
~30 such scripts already exist (`ls scripts/check | grep -i native`); this
audit looks for AOT-specific defects that still lack one.

## Method

Searched `doc/08_tracking/bug/` (272 filename hits for `native|aot|llvm`,
narrowed by reading titles/status lines) for defects specific to the
AOT/native-build/LLVM-backend code lane — excluding interpreter-only, JIT
(cranelift)-only, and generically-named "native" hits (e.g. "native array",
"native perf" where the defect turned out to be interpreter or JIT). Cross-
checked each candidate against `scripts/check/*.shs` (grep for related fixture
keywords) and `test/fixtures/` for an existing fixture.

## Ranked candidates

| # | Defect | Bug doc | `.shs` fence exists? | False-green spec risk? | Fence cost |
|---|--------|---------|----------------------|--------------------------|------------|
| 1 | Payload-bearing enum `match` refused (fail-closed) under `--native`; payload-free works | `match_on_enum_native_lowering_status_2026-08-07.md` | No | N/A (no spec claims to cover this — but future specs might and would be silently vacuous) | **Trivial** — 25-line fixture, one `compile --native` call. **FENCED THIS SESSION** (see below). |
| 2 | Native inlined `Option` return uses a bare text handle vs `rt_enum_new`-boxed value; `rt_native_eq` compares mismatched representations | `native_inlined_option_return_representation_mismatch_2026-08-02.md` | No (`check-native-option-try-target-fail.shs` covers a different scenario: `?`-operator on Option, not `SdnRow.get(...) == Some(x)`) | Yes — status doc says "TRACKED, NOT PARALLEL-CLAIMABLE"; any spec asserting this equality would be vacuous under the interpreter-only test runner | Low-medium — needs a minimal method that returns an inlined `Option` compared with `Some(...)`, isolated from the SdnRow/DB probe that first found it |
| 3 | `@extern fn` with no implementation: link-side guard now fails closed, but **codegen still fabricates a weak empty definition** at the object level (doc says "Codegen-side fabrication NOT fixed") | `native_link_fabricates_weak_empty_extern_definitions_2026-08-01.md` | No (`check-extern-registration.shs` etc. are unrelated hits from a generic grep) | Yes — link-side fix could make a spec appear to "cover" the whole family while the codegen half stays open | Low — a single unresolved `@extern fn` + object-level symbol inspection (`nm`/`objdump`) after native-build, no runtime execution needed |
| 4 | `rt_io_file_*`: interpreter fixed and verified; native/JIT still returns the `RT_KEEP` stub | `rt_io_file_family_interpreter_fixed_native_still_stubbed_2026-08-05.md` | No | Yes — "PARTIALLY FIXED" status is exactly the shape that regresses silently: someone fixes the interpreter, closes the tracker, and native stays broken forever unmonitored | Low — a native-build program calling one `rt_io_file_*` op and asserting it does NOT silently succeed (currently: stub, so assert the *known-broken* behaviour, flip on fix like row 1) |
| 5 | UTF-8 mid-codepoint slicing: three divergent policies across engines, one produces invalid UTF-8; native-lane state is OPEN (stage 1 landed, stage 2 pending) | `native_slice_splits_utf8_three_divergent_policies_2026-08-01.md` | Partial — `check-utf8-slice-audit-live.shs` exists but its scope needs confirming against the native lane specifically (title suggests live/interp probing, not necessarily `native-build`) | Possible | Medium — needs a native-build fixture exercising a mid-codepoint slice and asserting the currently-landed stage-1 (counting) behaviour, distinct from stage-2 (still open) |
| 6 | Weak/zero-size symbol fabrication family close cousin: native object cache invalidates whole build on scoped compiler changes (perf/correctness risk, not a wrong-output defect) | `native_object_cache_whole_build_fingerprint_granularity_2026-08-02.md` | **Yes (2026-08-08)** — `check-native-object-cache-granularity.shs` | Low direct false-green risk (perf issue, not correctness) | Medium — needs two builds + cache timestamp/rebuild-count assertions, not a simple stdout diff. **FENCED 2026-08-08**: re-confirmed via source read + a 3-module fixture (editing 1 of 3 modules → 0/3 reuse, `[NATIVE] cache: 0 hits, 3 misses`); the real fix needs per-module MIR/dependency-interface hashing that doesn't exist, so this session added a known-open canary rather than patching. |
| 7 | Pure-Simple LLVM shard emitted invalid `bitcast i1` to `ptr` — now FIXED, but only verified against one specific shard (`env/paths.spl`) compiled as a focused Stage 4 target | `llvm_bool_bitcast_to_ptr_invalid_ir_2026-08-03.md` | No dedicated minimal fixture (verification relied on a real source file + specific build mode) | Yes — FIXED-but-only-verified-once is a regression risk; no small standalone fixture exists to catch a recurrence cheaply | Medium — needs a minimal `.spl` snippet that produces a bool-to-pointer-typed bitcast in MIR, isolated from the large real shard |
| 8 | `--native` silent empty-binary emit — CLOSED as measurement artifact (not a real defect) | `native_emit_silent_empty_binary_2026-08-01.md` | N/A | No (closed, not a real defect) — included for completeness/ruled-out | None needed |

Rows 2–4 and 7 are the next-best candidates after row 1 if further fencing
work is scheduled: 2–4 are all confirmed-open-or-partially-fixed AOT-specific
defects with no fence and real regression risk; 7 is FIXED-but-unfenced with
a non-trivial (but not huge) repro cost.

## What was fenced this session

**Row 1** — payload-bearing enum `match` under `--native` — chosen because it
is confirmed open **as of today** (verified 2026-08-07, same day as this
audit), has an exact, stable expected diagnostic string
(`cannot compile to standalone native binary ... describe_shape: [PatternMatch]`),
and the fixture is self-contained (no DB/SdnRow/GPU dependencies unlike rows
2–6). See `scripts/check/check-native-enum-match-payload.shs` and
`test/fixtures/native_enum_match_payload/{main.spl,payload_free.spl}`.

The script asserts BOTH directions: the payload-free control must keep
compiling and printing the correct output (regression if it stops), and the
payload-bearing case must keep failing with the *specific* known diagnostic
(a `NOTE` fires, not silent pass, if the gap ever closes — mirroring the
pattern in `check-native-tuple-to-text.shs`).
