# Native `--entry` Build Correctness — Status & Remaining (2026-07-14)

Tracks the pure-Simple `native-build --entry` correctness campaign that feeds
self-hosting **#138** (single-file native-build route). Goal: every construct
the native backend emits must equal the seed interpreter oracle, **or** be
correct-by-construction where the oracle is provably broken. A loud build
failure is **never** silently converted to a wrong answer.

## Verification contract (unchanged, in force)

- **Oracle:** `env -u SIMPLE_BOOTSTRAP bin/simple run p.spl` (seed interpreter).
- **Native:** `env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry p.spl -o out --clean`.
- **Gate 1 — matrix:** `scripts/check/native-smoke-matrix.shs` must report
  `native_smoke_matrix=true`: at least one selected case ran and every selected
  case passed, with zero FAIL/XFAIL/XPASS/codegen-fallback results.
- **Gate 2 — parity:** `scripts/check/check-native-seed-parity.shs` (dual-backend
  regression harness) must report `native_seed_parity=true`. By default it
  defines **92 logical cases / 126 recorded checks** because strict-dual cases
  record LLVM and Cranelift separately. `NATIVE_OPEN_BUG_REPROS=1` expands this
  to **93 logical cases / 127 recorded checks**; execution is opt-in because
  the exact brace-literal reproduction remains known-red. Execution of the
  expanded matrix is pending.
  The full unfiltered gate is now scheduled on Linux x86_64 LLVM (STRICT-DUAL
  cases also build Cranelift); its first CI execution is pending. Five modes:
  PARITY (seed==native after newline-normalize, with an optional fixed expected
  value that both must match), NATIVE-AUTHORITATIVE
  (oracle provably broken → assert native==known-correct + document divergence),
  STRICT-DUAL (LLVM and Cranelift must match a fixed expected value), LOUD-FAIL
  (unsupported constructs and overflow must build-fail without leaving a
  binary), and RUNTIME-FAIL (build succeeds, then runtime exits nonzero with
  the required diagnostic).
- Land only via FF-replay onto the `git ls-remote` tip; verify every push with
  `ls-remote` + content-grep. **No branches.** Seed/compiler **redeploys need
  explicit user go-ahead** — this campaign edits `src/compiler/*.spl`, which
  `native-build` interprets live (no rebuild needed).

## Landed this campaign (origin/main, newest first)

| Commit | Fix |
|--------|-----|
| `13ef81cdde86` | `.map` probes reuse the lowered receiver so side-effecting array producers execute once |
| `7f28b8ebfd14` | FreeBSD QEMU workflow path filters now track strict native smoke matrix changes |
| `19ac0d5a4e6` | parity harness extended to 32 cases |
| `99c7f3516b0` | nested/destructuring match (tuple, nested enum+struct payload) |
| `3434196a876` | `text + number/bool/float` concat auto-stringifies (was SIGSEGV) |
| `eeba60ee024` | for-in over non-array iterables → loud-fail (was silent+panic) |
| `13e6f9d63ae` | float struct/tuple fields bit-preserved + typed (was fptosi trunc) |
| `3cbe3293561` | string methods with a variable argument (was llc crash / always-false) |
| `54eec04678d` | dual-backend parity harness (initial) |
| `761bbf4a637` | Option `.is_none/.unwrap/.unwrap_or/.map` wired |
| `e4dc1760ef4` | float `-0.0` sign, NaN casing, tiny-magnitude silent-zero |
| `3c87c535c76` | enum text-payload static type + payload-less enum equality |
| `249476fd257` | unimplemented-lowering stubs → loud build failures |
| `15ca6fe6190` | struct return-by-value + call-result/payload field access (+determinism) |
| `5fa6098d842` | match on text/or-patterns/ranges/bool (were silent garbage) |
| `9647fc190c3` | integer literal overflow loud-fails (was silent garbage) |
| `1df70c6b9ab` | dict `keys()`-iteration `d[k]` round-trips (was 0) |
| `ab957b1ae32` | tuple `.0/.1`, mixed-type destructure, `for (k,v)` loop |
| `33b56152412` | 2D arrays, slices, array-of-structs field access, `.contains` loud-fail |
| `e2c5d51014b` | sized unsigned/signed ints print + compare + divide correctly |
| `11f116448d3` | keep explicit test-runner sources |

~45 root causes fixed total (some pre-date this table). The original 15-case
matrix has grown to 21 registered cases; consumers trust its count-independent
strict success receipt instead of copying that evolving total.

## Correctness-by-construction divergences (native ≠ seed, native is right)

Oracle proven definitionally broken; native diverges intentionally, documented
in the parity harness NATIVE-AUTHORITATIVE cases:

- float `0.1` — seed prints non-round-tripping `0.09999999999999998`
  (`0.1 == 0.09999999999999998` returns FALSE → oracle violates round-trip).
- `Some(0)` / `rt_is_none` on i64-payload — seed prints `false`.
- compound-assign — seed gives `5/3/2/3`; native `1512246`.
- tuple pattern match — seed gives `0`; native `35`.
- `me` receiver, module globals, string ordering `"a"<"z"` — seed all wrong.

## Seven-lane sweep outcome (2026-07-14)

Landed results from the sweep:

- **entrypoint** — bare `fn main():` now emits explicit `ret i64 0`
  (`xor %eax,%eax`) instead of relying on register garbage (`7b92cf8a5459`).
- **exprdispatch2** — `a + [x]` array-concat SIGSEGV + bool/float in string
  interpolation fixed (`e9165c53a667`).
- **dictcallkeys** — fn-call-returned dict `d[k]` during `keys()` returns 0
  fixed by tagging call-result dict locals (`abde1838e3e4`).
- **closures2** — IIFE lowering landed (`bc33ade0120a`).
- **parity** — the sweep cases landed in the shared harness (`e7282ee52f42`).
- **errhandling/collections** — discovery produced the durable bug files listed
  below; the static constructor crash is resolved by the 2026-07-15 bottom-up
  fix and its parity cases.

**HARD RULE for every lane:** never run `bootstrap-from-scratch.sh`, `cargo`,
`bin/simple build bootstrap`, `--deploy`, or anything that writes `bin/release`
(a rogue redeploy was caught mid-run this session and killed before it clobbered
the shared binary — deploys require explicit user go-ahead).

## Remaining after the 7 lanes

- Parity-harness closure is source-complete for every landed sweep lane:
  `bare_main`, `iife`, `dict_from_call_keys`, `array_concat`,
  `interp_bool_float`, and `static_ctor_disambiguated` pin the entrypoint,
  closure, dict-call, collection, interpolation, and constructor fixes. The
  expanded dual-backend matrix still requires the executable gate above.
- The normal `brace_literal_scope` parity case retains the native-entry
  adaptation. `NATIVE_OPEN_BUG_REPROS=1` additionally selects the exact June
  cross-function source as `brace_literal_scope_exact`, including Unit `main`
  and the trailing top-level `main()` call that exercises `_expr_N` restoration
  plus `functions.contains("main")`. The active root fix stops the Rust seed's
  single-line f-string interpolation scan at its outer closing quote instead
  of consuming later functions while seeking a `}`; exact lexer and HIR
  regressions cover the source. The broad map-initialization workaround
  `f06e5829` remains reverted by `0f535b099788`. Exact Linux execution remains
  pending.
- Open filed bugs, in bottom-up order:
  - `native_try_op_on_option_silent_wrong_2026-07-14.md` source-implements `?`
    for authoritatively typed flat and boxed Option locals/direct-call returns;
    resolved and unresolved-method provenance paths are source-covered without
    guessing genuinely unknown late dispatch. Native-authoritative annotated,
    direct, and unresolved-method cases select flagless LLVM or explicit
    Cranelift on hosted Linux/macOS/Windows and FreeBSD x86_64. ARM32 default
    LLVM and Windows ARM64 LLVM/Cranelift require successful, nonempty target
    objects without the retired fail-closed diagnostic. Commit `cd68cb9af439`
    removes the flat payload-3 collision in source by using one enum-id-1
    handle (`Some=0`, `None=1`) at typed producers, returns, calls,
    lets/assignments, struct fields, and `if`/`match` merges. The follow-up
    closes the actual function-valued `f(3)` argument boundary and canonicalizes
    the early-`?` absent return that bypasses normal return promotion. Coverage
    reads that return's `rt_enum_id` directly so legacy raw nil cannot
    false-green through the migration-compatible `unwrap_or` consumer.
    Focused
    runnable tests cover the Rust MIR interpreter, raw-bool `Option.map`, the C
    runtime contract, and pure-runtime rejection of raw heap-tag collisions.
    The exact LLVM/Cranelift fixture is now a mandatory strict-dual gate;
    current-source execution remains pending because the available seed-hosted worker emitted a multi-million-token
    parser-hint flood and was terminated before native lowering rather than
    risking a runaway or crash.
  - The cross-module `Result<[u8], E>` control now routes both its Ok and Err
    paths through `?`. Flagless default-LLVM and explicit-Cranelift gates
    schedule it on FreeBSD x86_64 and AArch64/RISC-V QEMU. ARM32 default LLVM
    and RV32 bare-metal LLVM plus Windows ARM64 LLVM/Cranelift require nonempty
    target-correct relocatable objects from the same fixture. The ARM32 object
    check requires the target's hard-float ABI and rejects soft-float output;
    execution remains pending.
  - `native_text_option_unwrap_pointer_value_2026-07-15.md` is resolved at
    origin tip 8932fcb3a148: its exact flat-nullable text repro builds and
    prints `opt`. A dedicated strict-dual case schedules that exact repro on
    Linux plus selected macOS/Windows/FreeBSD hosts. The shared cross-target
    fixture repeats the rendered-value oracle for AArch64/RISC-V64 execution
    plus ARM32/RV32/Windows ARM64 target objects. Explicit enum Option remains
    the separate tagged-ABI item; first staged platform execution is pending.
  - `native_mixed_numeric_ordering_codegen_2026-07-16.md` is source-fixed for
    signed integers through shared MIR coercion before LLVM or Cranelift.
    Strict dual-backend execution is pending that staged CI. Unsigned
    high-bit casts and signed/unsigned ordering are source-fixed and covered by
    separate strict cases; the latter restores unsigned Cranelift predicates in
    both pure-Simple owners. Unsigned division, remainder, and right shift now
    select `udiv`/`urem`/logical shift in both LLVM routes and both active
    Cranelift owners; signed-left right shift remains arithmetic even when its
    count is unsigned. A strict dual-backend case covers all four operations;
    a separate LLVM parity case covers narrow signed-left widening without
    routing that backend-specific coercion probe through Cranelift.
  - `native_bool_array_element_interpolation_special_garbage_2026-07-17.md`
    is source-fixed in MIR: indexed reads retain the array element type before
    the bootstrap text fallback, and both Let-lowering paths preserve bool
    initializer types on fresh bound locals. A strict dual-backend case covers
    direct/bound interpolation, bare bound-value printing, and primitive array
    fields on structs/classes. Linux runs it in the full gate; macOS arm64/x64,
    Windows x64, and FreeBSD select it explicitly. First staged platform-matrix
    execution is pending. The shared cross-target fixture repeats direct and
    unannotated-bound interpolation through a plain bool array, a struct bool
    array field, and a class text array field for AArch64/RISC-V64 execution
    plus ARM32/RV32/Windows ARM64 target objects without changing its
    success-output protocol.
  - `native_class_array_field_mutation_segfault_2026-07-17.md` is source-fixed
    by registering declared class-field aggregate metadata and mirroring normal
    field projection provenance in mutating-receiver prelowering. A strict
    dual-backend case covers a non-first field's `.push`, field index assignment, and
    visibility of that array handle through an alias captured before mutation.
    The exact native-build shapes were re-verified locally; Linux runs the case
    in the full gate, while macOS arm64/x64, Windows x64, and FreeBSD select it
    explicitly. The shared cross-target fixture repeats the non-first-field
    push/index-write and pre-mutation alias oracle for AArch64/RISC-V64
    execution plus ARM32/RV32/Windows ARM64 objects. First staged
    platform-matrix execution is pending.
  - `native_nested_struct_value_copy_alias_2026-07-17.md` is source-fixed by
    routing local and plain-parameter value copies through one recursive MIR
    owner. Nested value structs are isolated, embedded classes stay shared,
    and nil nested fields are guarded. A strict LLVM/Cranelift case runs in
    Linux's full board and the hosted macOS/Windows plus FreeBSD selections;
    execution is pending. The shared cross-target fixture repeats the local and
    parameter isolation plus embedded-class sharing oracle for AArch64/RISC-V64
    execution and ARM32/RV32/Windows ARM64 target objects. Array-of-class boxing
    remains separate. Direct resolved non-generic
    by-value struct cycles, including cross-module cycles, are now rejected by
    one target-independent post-HIR validator before MIR; class/reference and
    wrapped Option/array shapes remain valid indirection boundaries. The
    in-process compiler integration spec covers direct, local-mutual, and
    cross-module value cycles plus allowed self-referential class and array
    indirection boundaries. First staged execution is pending.
  - Hosted `riscv32-unknown-linux-gnu` remains intentionally unsupported until
    a verified ILP32D linker/sysroot/CRT owner exists. The existing Linux
    architecture gate now exercises the original hosted target boundary with a
    flagless default-LLVM full build, requires loud failure and no output, then
    emits nonempty ELF32 RISC-V relocatable objects for both the minimal
    flagless default-LLVM `riscv32-unknown-none-elf` recovery probe and the
    shared cross-module Result/arithmetic correctness fixture. RV32 remains
    object-only; first staged execution is pending.
- Option `.map` now evaluates a side-effecting receiver exactly once and
  inlines its literal lambda with the decoded payload, preserving primitive
  text/float/bool/integer results through the tagged runtime-value merge.
  Array `map`/`filter`/`fold` retain their existing lifted i64 ABI. Linux runs
  the strict dual-backend typed-output/filter control in the full gate; that
  control now also observes the receiver's mutation count so duplicate
  evaluation cannot pass. macOS
  arm64/x64, Windows x64, and FreeBSD x86_64 select it explicitly. First staged
  platform-matrix execution is pending. The shared cross-target fixture now
  repeats that exact value-and-count oracle for default LLVM and explicit
  Cranelift on FreeBSD/AArch64/RISC-V64; ARM32/RV32 and Windows ARM64 require
  nonempty target objects from the same source.
- Option/Result method lowering now proves the receiver type before claiming
  `is_some`, `is_none`, `unwrap`, `unwrap_or`, `unwrap_err`, or lambda `map`.
  Unresolved custom owners with those names reuse one pre-lowered receiver and
  dispatch normally; Cranelift no longer treats `unwrap*` leaf names as
  identity calls. One strict LLVM/Cranelift fixture covers all six collisions,
  `Err(text).unwrap_err()`, and single receiver evaluation in Linux's full gate
  plus the selected macOS, Windows, and FreeBSD gates. First staged execution
  is pending.
- The Engine2D host-runtime queue symbol bug now has one incremental
  gate that builds the existing no-GPU probe with the host-GPU bundle under
  flagless LLVM or explicit Cranelift, compares native output byte-for-byte
  with the interpreter, and pins payload/overflow ABI values. The same probe
  traverses Draw IR SDN generation; its two dynamic text-array joins now use
  one pure-Simple newline loop instead of bootstrap's unsupported nonliteral
  array `.join()` lowering. Linux, macOS
  arm64/x64, Windows x64, and FreeBSD x86_64 schedule it; first staged
  execution remains pending. Cross-target objects are not counted as proof for
  this host link/runtime defect.
- The whole-compiler redeploy (#99 / Stage4) remains separate from this
  correctness campaign. Runtime-native's 18-symbol legacy dependency owner is
  now source-implemented as an exact localized compatibility provider. The
  exact archive projection and strict final-link routing are now
  source-implemented after inventory and transitive requested-owner resolution.
  SQLite now enters that path as a separate exact provider with conditional
  system-library input; its native result ABI was aligned with the public
  Simple/interpreter `1`/`0` contract. FreeBSD now reuses the existing `.a` /
  ELF compiler-backfill policy and GNU selected-archive projection instead of
  falling into Mach-O flags, and direct strict linking reuses the established
  base-system `/usr/lib` CRT directory. Its full Stage4 QEMU execution remains
  pending.
  The executed Stage4 unresolved preview's bare `path_parent`, `path_filename`,
  `path_extension`, `path_stem`, `path_components`, and `path_with_extension`
  are also removed in both filesystem profiles by reusing `std.path`; no new C
  provider was added. `file_metadata` now uses one opaque runtime stat handle,
  constructs the record in pure Simple, and releases the handle; no live
  unresolvable entry remains in that stub family.
  Windows COFF projection is now source-implemented for both linker families:
  MinGW keeps the exact static capsule, while MSVC links the selected owners
  once into an exact-export DLL/import library and hash-verifies the Stage4 and
  SQLite DLL neighbors beside the final executable. The Windows LLVM/Cranelift
  full-CLI matrix now schedules nonempty artifact receipts. The remaining
  Linux recovery profile now completes phase-one loading in 6.325 seconds for
  1,763 sources with the pure-Simple bucket hash; `std.alloc.sffi` is also owned
  in the pure library tree instead of the Rust-seed mirror. The next blocker is
  phase-two parse retention exceeding the 4 GiB safety cap, followed by first
  full execution evidence and any concrete missing owner reported by the
  complete compiler request closure, not the retired seed enum/mcall
  diagnoses. The first 160 phase-two parses covered 1,570,048 source bytes and
  contained no conditional directive or domain-block marker, yet retained
  about 3.65 GiB. Pure Simple now returns directive-free input directly from
  the conditional preprocessor and skips both domain-block line scans when no
  exact domain marker can occur. The focused specs pin byte-identical ordinary
  source plus both fast and existing slow branches. Three independent
  read-only audits agreed that the 484 logical aliases reuse 1,279 physical
  modules and are not duplicate ASTs; alias lookup remains unchanged.
  Higher-level review accepted the fast paths. Execution proof remains pending:
  the broad parser fixture stopped on existing phase-three lowering errors, a
  narrow current-source probe reached the known `HirExpr.is_some` bootstrap
  crash, and the cache-preserving Stage2-to-Stage3 rebuild was OOM-killed at
  the 4 GiB safety cap before producing a candidate. Per the bounded retry
  policy, those failing commands were not repeated. A later current-source
  incremental LLVM Stage2/Stage3 rebuild completed without Cargo or a full-CLI
  relink: Stage3 compiled 657 files with zero failures, linked in 618.2 seconds,
  and its one-file LLVM capability probe printed `windows native hello`. Its
  hash is `950f96418ae2f55d2eae1732a440e66509335c34526a603b92d31a060e16bdbc`.
  The first capped Stage4 follow-up lacked usable phase evidence because the
  canonical launcher set `SIMPLE_BOOTSTRAP_STAGE4=1`, while `log_phase` reads
  `SIMPLE_COMPILER_PHASE_PROFILE`; the six-minute run timed out with an empty
  profile log. The launcher now enables phase profiling by default while
  preserving an explicit `0` override. Source review also found that sync
  commit `0a749ba7f10c` had restored the allocation-heavy per-character
  `substring(scan_pos, scan_pos + 3)` triple-quote scan in phase-one entry
  closure loading. The retained-good `index_of` delimiter search is restored;
  the existing regression covers docstring correctness plus a 65,536-character
  line and rejects the slow loop. A focused LLVM execution probe then stopped
  on the separate undeclared `call_type_args` bug recorded in
  `doc/08_tracking/bug/native_entry_closure_call_type_args_undeclared_2026-07-19.md`.
  A later sync reintroduced that invalid optional conversion; current source
  again passes the Call arm's bound `[HirType]` values directly, and the
  entry-closure regression spec rejects the undeclared name. The earlier source
  fix was rebuilt incrementally into LLVM Stage3
  `745c134062c5d8624f0d6ed871b4a9c308a6e5bd55c4a0a39a32f1e62ac6504b`
  using 624 cached objects and 33 recompiles; its LLVM capability probe passed.
  A correctly instrumented six-minute Stage4 run then emitted `compile:start`
  and `phase1:load_sources:start` but never completed phase one, while RSS stayed
  near 28 MiB. The exact delimiter loop compiled and ran separately with
  `quote_count=2`, excluding that path and its Option/string lowering. History
  inspection found a second post-baseline overwrite: `fa1ee50c35c5` replaced
  the constant-allocation bucket membership test with `bucket.split("\n")` on
  every closure lookup and removed its source guards. The retained-good
  `starts_with`/`contains` check and both regression guards are restored. Its
  bounded six-minute follow-up still did not leave phase one and retained only
  about 28 MiB, excluding retention growth. History then exposed the remaining
  half of the same overwrite: `0a749ba7f10c` replaced the retained pure-Simple
  `hm_hash_text` with runtime `rt_hash_text`, whose registered-string validation
  linearly scans the global string registry on every hot-set hash. The proven
  pure-Simple hash is restored and source-pinned. Higher review then found that
  native `s[i].ord()` discarded the low three byte bits and allocated a
  one-character string per byte. The hash now reuses `text.bytes()` once and
  hashes the resulting integer bytes, preserving FNV entropy without that
  per-character registry path. A cache-preserving LLVM compile had emitted the
  loader object with a direct `hm_hash_text` relocation;
  the standalone bootstrap relink remained unavailable because that partial
  route omitted the existing runtime providers. Its bounded profile therefore
  remains pending. See
  `redeploy_stage4_plan_2026-07-09.md` and `stage4_stub_symbol_plan_2026-07-11.md`.
