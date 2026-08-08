# Native `--entry` Build Correctness — Status & Remaining (2026-07-14)

Tracks native-build correctness, including the pure-Simple single-file
positional route that feeds self-hosting **#138**. `--entry`/`--source` probes
remain Rust-worker/native-smoke evidence, not self-hosted MIR receipts. Goal: every construct
the native backend emits must equal the seed interpreter oracle, **or** be
correct-by-construction where the oracle is provably broken. A loud build
failure is **never** silently converted to a wrong answer.

## Current session remaining (2026-07-25)

- **MCP native receipt:** the fresh pure-Simple Stage4 compiler reached link,
  but its automatic `core-c-bootstrap` lane lacks the simple-core owners MCP
  needs. A complete simple-core archive was built successfully at
  `/tmp/root-mcp-current-llvm-20260724-1/simple-core/libsimple_runtime.a`.
  The pure CLI now captures `--runtime-path` in both spellings and exports
  `SIMPLE_RUNTIME_PATH` plus `SIMPLE_CORE_RUNTIME_PATH`; rebuild the MCP
  artifact with that explicit archive path before accepting it.
- **MCP helper closure:** the shared helper is now public and four explicit imports resolve
  `_mcp_find_simple_binary` calls from VCS, CLI, DAP, and play handlers. The
  first retry removed all five undefined helper symbols.
- **JSON Dict lowering:** `common/json/object_ops.spl` now gives the three
  `json_to_object` receivers an explicit `Dict<text, any>` type, with a source
  regression in `dict_typed_method_lowering_source_spec.spl`. A final native
  link receipt is still pending; do not claim MCP green until `Dict.has` and
  the simple-core process/string owners link cleanly.
- **MCP acceptance:** after the artifact links, run the strengthened
  `scripts/check/check-mcp-native-smoke.shs` once with LLVM and once with
  Cranelift as applicable. It now requires initialize/tools-list, correlated
  `simple_status`, and a real `simple_pipe` codebase query. Then retry the live
  Simple MCP handshake once; the old installed artifact was proven to SIGSEGV
  in `_process_run_inherit` on that query.
- **Other campaign receipts:** the exact brace-literal parity repro, staged
  platform matrix (macOS/Windows/FreeBSD/ARM/RISC-V), and full Stage4 QEMU
  execution remain pending as already recorded below.

## Verification contract (in force)

- **Oracle:** `env -u SIMPLE_BOOTSTRAP bin/simple run p.spl` (seed interpreter).
- **Native smoke / Rust-worker:** `env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry p.spl -o out --clean`.
  This validates the selected native/runtime lane, not the pure-Simple bootstrap MIR route.
- **Self-hosted single-file:** invoke the current Stage4 candidate with exactly
  one bare positional `.spl` input, no `--entry` and no `--source`, for example
  `SIMPLE_CORE_RUNTIME_PATH=/abs/libsimple_runtime.a STAGE4 native-build --backend cranelift --runtime-bundle simple-core --clean -o out p.spl`.
  C5 is not credited until this positional form builds and the binary exits `42`.
- **Gate 1 — matrix:** `scripts/check/native-smoke-matrix.shs` must report
  `native_smoke_matrix=true`: at least one selected case ran and every selected
  case passed, with zero FAIL/XFAIL/XPASS/codegen-fallback results.
- **Gate 2 — parity:** `scripts/check/check-native-seed-parity.shs` (dual-backend
  regression harness) must report `native_seed_parity=true`. By default it
  defines **97 logical cases / 137 recorded checks** because strict-dual cases
  record LLVM and Cranelift separately. `NATIVE_OPEN_BUG_REPROS=1` expands this
  to **98 logical cases / 138 recorded checks**; execution is opt-in because
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

**HARD RULE for every lane:** never run
`scripts/bootstrap/bootstrap-from-scratch.sh`, `cargo`,
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
  - `native_exists_check_struct_payload_becomes_bool_2026-07-25.md` is
    source-fixed: `ExistsCheck` preserves its payload merge rather than the
    `rt_is_some` condition and records the inner struct provenance. The exact
    imported getter fixture evaluates `evidence.?.marker` and expects output 42;
    it is mandatory strict LLVM/Cranelift parity and cross-target object input.
    Execution remains pending because no admitted pure-Simple candidate is
    available in this workspace.
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
    schedule it on hosted Linux/macOS/Windows, FreeBSD x86_64, and
    AArch64/RISC-V QEMU. ARM32 default LLVM and RV32 bare-metal LLVM plus
    Windows ARM64 LLVM/Cranelift require nonempty target-correct relocatable
    objects from the same fixture. The ARM32 object check requires the target's
    hard-float ABI and rejects soft-float output; first execution of the added
    hosted Cranelift gate remains pending.
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
  Array `filter`/`fold` retain their existing lifted i64 ABI. Array `map` is
  source-fixed: proven runtime arrays cannot be claimed by Option ownership,
  and the existing unresolved-array fallback now inlines its one-parameter
  callback while preserving input/result MIR types and returned-array element
  provenance. Resolved custom/static map owners remain untouched. The exact
  fixture and acceptance contract are tracked in
  `doc/08_tracking/bug/native_array_map_text_provenance_2026-07-19.md`. Linux runs
  the strict dual-backend typed-output control in the full gate; that
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
- Hosted canonical `i64?` `.?`/`if val` binding is source-fixed at the shared
  `ExistsCheck` payload boundary: the outer `Some` handle is unwrapped before
  generic runtime decoding. Hosted and cross-target fixtures pin `7`, not the
  former handle-derived `84`. The same raw merge now records f64/f32 inner
  provenance: `lower_if` performs the nil-sentinel test before remapping only
  the present branch through the existing bit-preserving payload decoder.
  The selected `option_is_none_map` strict dual-backend case covers both float
  widths on Linux, macOS, Windows, and FreeBSD; rebuilt executable proof
  remains pending. See
  `doc/08_tracking/bug/hosted_native_option_try_unwrap_payload_leak_2026-07-19.md`.
- LLVM enum f64 payloads now preserve the runtime payload-word ABI in both
  directions: `rt_enum_new` receives the f64 bits as i64, while MIR lowering
  bitcasts back only when the semantic payload type is f64; ordinary numeric
  i64-to-f64 casts remain `sitofp`. The former native XFAIL is now
  a source-fixed fixture. Its direct LLVM-IR regression is present; the bounded
  current-source mini build hit its 240-second cap, so native execution remains
  pending and was not retried. The shared native smoke matrix now schedules the
  fixture on Linux, macOS, Windows, and FreeBSD; Cranelift is the hosted control.
- LLVM aggregate reads now load uniform native-width field slots into a fresh
  SSA temporary and truncate to the declared narrow integer/bool width. The
  focused IR regression covers `i32` and `i1`, preventing the former
  load-i64-then-sext/zext type mismatch; full worker execution remains pending.
- `local_mir_type_of` now honors its nilable contract by returning a bare
  `MirType` or `nil`; its two wrapper-dependent consumers were converted in
  the same owner. The focused regression reproduces the former plain
  assignment plus `MirType.ptr` failure and a bounded direct pure-Simple run
  prints `local_mir_type_bare_ok`. Native matrix replay awaits the next
  incremental compiler rebuild.
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
  correctness campaign. Runtime-native's 19-symbol legacy dependency owner is
  now source-implemented as an exact localized compatibility provider. Its
  guarded process-spawn export owns the native-build timeout wrapper's process
  group and removes it when the Simple parent dies. Source/C evidence passes;
  fresh-runtime Linux parent-death evidence remains blocked by the bounded
  current-source diagnostic flood and exit-139 self-hosted checks. The
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
  narrow current-source probe reached the former `HirExpr.is_some` bootstrap
  crash. Current source binds the optional Return payload in both MIR prescan
  and lowering, and focused parse-to-HIR-to-MIR coverage now exercises both a
  value return and a bare return. The cache-preserving Stage2-to-Stage3 rebuild
  was OOM-killed at the 4 GiB safety cap before producing a candidate. Per the
  bounded retry policy, those failing commands were not repeated. A later
  current-source incremental LLVM Stage2/Stage3 rebuild completed without Cargo
  or a full-CLI relink: Stage3 compiled 657 files with zero failures, linked in
  618.2 seconds,
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
  remains pending. A final source audit then found that phase-one import
  discovery still called `content.split("\n")` and `trim()` for every source
  line. Under the bootstrap runtime that materialized and registered every
  ordinary line before the import walk, reintroducing quadratic registry work
  outside the already-fixed quote and hash loops. The shared scanner now walks
  `content.bytes()` once, recognizes declaration prefixes in place, and
  materializes only the ASCII module token. It never uses byte offsets to slice
  `text`, preserving interpreter/native behavior after preceding Unicode. The
  scanner also stops at `#` while outside a docstring so documentation comments
  containing `\"\"\"` cannot suppress later imports, while a quoted delimiter
  after `#` inside an active docstring still closes it. The focused regression
  covers both comment states, all declaration forms, long ordinary source,
  indentation, and Unicode before an import; fresh Stage4 execution evidence
  remains pending. A follow-up phase-one audit found that every `compiler.*`
  closure import still exhausted the generic `src/lib` plus ten-family search
  before trying its deterministic numbered compiler path, causing up to 33
  doomed filesystem probes per exact import (and again for terminal-symbol
  parents). Direct and relative candidates retain precedence, but numbered
  compiler mappings now run before generic library-family probing; focused
  resolver coverage pins both the paths and this ordering. Fresh bounded
  Stage4 timing remains pending. The canonical fixed-arity Stage4 API now also enables the
  low-memory mode its wrapper already requested; previously it reconstructed
  default `CompileOptions` and silently disabled every existing eviction point.
  Per-file AST resets now retain and clear declaration/expression/statement
  arena storage plus scalar lexer/module slots instead of registering fresh
  outer arrays for every parsed source. Omitted trait/mutability and GPU pools
  are reset with their siblings. Parser diagnostics, struct-name scratch, and
  token/cache singleton storage now reuse the same owners, and the lexer only
  replaces its source-specific payload instead of its outer active slot.
  Warning collection also retains every warning from the current parse instead
  of discarding the previous one. Pure runtime `source.chars()` now reuses each
  one-byte character handle within a conversion, retaining at most 256 distinct
  one-byte string objects plus unchanged multibyte objects. The O(N)
  `source_chars` reference array is now shallow-released after each active lexer
  replacement across pure-Simple, hosted-C, Rust native/JIT, and interpreter
  ownership models. Stage4 RSS evidence is pending. A
  bounded current-source refresh reached its 180-second cap without an
  artifact, while an isolated lexer probe compiled from cache but could not
  link through the preserved driver's incomplete pure/core-C runtime bundle
  projection. The aligned shallow-release ABI now enforces active-slot
  replacement before release; freeing the old array earlier remains an
  aliasing/UAF bug.
  The isolated rich-module bridge now resets the flat type/span/token/symbol/
  signature/composite pools before each file, while `reset_all_pools` clears
  their outer arrays in place instead of registering replacement arrays. A
  bounded direct pure-Simple two-module probe preserves the first rich module,
  drops the first file's named-type scratch entry, assigns the second file's
  first type ID at zero, and prints `type_pool_reset_ok`. Stage4 RSS impact is
  still pending; this is not claimed as the full 8 GiB fix.
  Composite flat-type registries now intern exact payloads before enforcing
  their fixed tag ranges. Union/intersection/refinement/tuple registrations can
  no longer spill into the next namespace, duplicate Dict/Result/array shapes
  no longer consume fresh IDs, tuple state participates in pool reset, and
  negative registry IDs are rejected. Parser exhaustion follows the existing
  diagnostic-plus-bare-type fallback instead of propagating `-1`. See
  `doc/08_tracking/bug/composite_type_registry_tag_overflow_2026-07-19.md`.
  Current-source object emission had reached a hosted `path_join` provider gap.
  The affected tools now call the existing public two-argument `std.path.join2`
  API instead of importing the private one-argument `join` compatibility alias;
  a focused native repro prints `left/right`. Bounded RSS and full executable
  proof remain pending. See
  `redeploy_stage4_plan_2026-07-09.md` and `stage4_stub_symbol_plan_2026-07-11.md`.
  The text predicate Part A lane now keeps `starts_with`, `ends_with`, and
  `contains` results typed as MIR Bool instead of i64, preventing native
  interpolation from rendering them as `1`/`0`; one focused source regression
  pins all three existing lowering paths. Primitive `.to_string()`/`.to_text()`
  recovery now runs after custom method dispatch, accepts only known text or
  supported bool/numeric MIR types, and reuses the existing renderer.
  Cranelift now gives `rt_raw_f64_to_string` its required f64 argument ABI
  instead of the generic all-i64 import signature. Focused MIR/source
  regressions pin both aliases and the typed import. Strict dual-backend
  scenarios also cover a side-effecting custom-owner `.to_string()` collision
  plus bool/f64/i64/u64/text primitive output. Unresolved custom owners named
  `starts_with`, `ends_with`, or `contains` now also win before the text
  fallback for both instance and static dispatch; focused MIR and strict-dual
  cases pin all three. The shared
  cross-target fixture covers positive/negative builtin predicates and both
  conversion aliases for bool/f64/i64/u64/text, so existing FreeBSD,
  AArch64/RV64 execution and ARM32/RV32/Windows-ARM64 object gates inherit the
  oracle. The
  available pure-Simple test artifacts either crash before scenario output or
  lack the `test` command, so native execution remains pending.
  The tracked release crash is the known stale two-argument `rt_env_set`
  runtime owner, not current caller lowering. Shared Stage4 candidate admission
  now runs a bounded, self-pinned `-c` environment-write probe before native-build checks,
  so the stale artifact fails identically on Linux/macOS/Windows/FreeBSD
  without a platform-specific disassembler; no redeploy is claimed.
  While exercising that cross-platform admission self-test, the host-GPU
  validator exposed older evidence bugs: same-ISA TCG was mislabeled native,
  report validation read QEMU argv before assignment, and `serial_has_pass`
  ignored its QEMU-argv parameter in favor of an unset global. Live QEMU runs
  now select `-accel tcg` explicitly, the shared validator requires that evidence,
  and report validation assigns and passes the encoded argv before consuming it.
  The portability contract passes; the full host-GPU self-test reached the
  session's three-cycle cap while exposing these validator defects, so a clean
  rerun remains pending.
  The later cross-module arithmetic exit-5 evidence is now isolated to
  `u64(0x8000000000000000) > 0.0`: generated code encodes the cast as signed
  f64 `0xc3e0000000000000`. A current-source Stage2/3 rebuild reproduced it.
  The remaining root was earlier unsigned-provenance copy propagation, not
  LLVM/Cranelift comparison dispatch. Copy propagation now preserves an
  authoritative registered destination and inherits a source flag only for an
  unregistered destination, using direct operand-to-ID calls so bootstrap
  cannot collapse the keys. The rejected destination-or-source rule remains
  absent. The unchanged cross-module fixture still needs rebuilt execution:
  current LLVM and Cranelift artifacts must both exit 0 while preserving the
  signed destination flag and inheriting unsigned provenance only for an
  unregistered destination.
  Pure-Simple text `.char_code_at(index)` now lowers after custom-owner
  dispatch through a reserved alias to the exact raw-i64 runtime ABI instead
  of boxing/decoding the codepoint or capturing a same-named source function.
  The shared runtime accepts raw literals and tagged dynamic text
  without allocation and decodes valid UTF-8 consistently; hosted x86_64,
  freestanding x86_64/AArch64/RV64, textual LLVM, LLVM-lib, and Cranelift owners
  are aligned. Existing Linux/macOS/Windows/FreeBSD smoke and AArch64/RV64
  execution fixtures are wired to pin raw/tagged/Unicode/bounds behavior.
  Focused C syntax and hosted runtime checks pass; native entry execution for
  those four cases under LLVM and Cranelift remains pending, as does the
  original x86_64-unknown-none pure-Simple redeploy/QEMU proof.
- Cranelift tuple returns no longer expose dead callee stack slots. Tuple
  aggregates now reuse LLVM's existing `rt_alloc` ownership while preserving
  the raw, untagged tuple pointer ABI. Multi-block native-smoke and cross-target
  producers keep a returned `(17, 37, true)` live across a same-sized
  tuple-producing call and reread it afterward; the hosted Cranelift case uses
  aggressive optimization. Linux/macOS/Windows/FreeBSD and AArch64/RV64
  execution are scheduled through existing gates; ARM32/RV32 and Windows ARM64
  remain compile-only. First staged platform execution is pending.
- Custom enum `==`/`!=` now uses declared-type provenance to route same-type
  handles through structural runtime equality instead of pointer comparison.
  Custom constructors now carry stable qualified-type runtime IDs (with
  Result/Option retaining reserved IDs 0/1), and Pure/C structural
  equality checks the ID before discriminants and recursively compares payloads.
  pointer registries reject false heap tags before dereference, and numeric
  arrays compare across generic, byte-packed, and u64-packed storage. A
  64-level guard bounds malformed nesting. The shared fixture covers a
  three-variant config field, separately allocated equal text payloads, raw
  heap-tag-collision integers, and generic-versus-packed array payloads so
  hosted interning cannot false-green. Hosted LLVM/Cranelift and AArch64/RV64
  execution are scheduled; ARM32/RV32 remain default-LLVM compile receipts.
  The shared fixture also rejects cross-type enums nested behind `Any` and now
  asserts that both custom runtime IDs are distinct and at least 2; see
  `native_enum_runtime_type_identity_2026-07-19.md`. Existing hosted
  Linux/macOS/Windows and canonical FreeBSD full-QEMU gates schedule the Rust
  seed against that fixture with both emitted backends after seed/native-all
  exists. Cross-compiled seed binaries remain build-only. The Rust
  native-project path now threads its configured backend through compilation,
  cache identity, and linking, so flagless enabled-seed builds actually use the
  documented LLVM default while explicit Cranelift remains supported; see
  `rust_seed_native_build_default_backend_config_ignored_2026-07-19.md`. The Rust
  MIR-to-bytecode path now lowers `EnumUnit`/`EnumWith` with the full `u32` enum
  ID and discriminant in `ENUM_NEW_TYPED`; variant tests use
  `ENUM_MATCH_TYPED`. Legacy opcode layouts remain compatible. Duplicated SMF
  writers emit version 2 while loaders accept versions `1..=2`. Focused Linux
  Rust execution passes and hosted Linux/macOS/Windows jobs schedule the same
  tests. The canonical FreeBSD full-QEMU wrapper is wired to run the two typed-enum
  bytecode compiler/VM regressions and requires an exact 2/2 summary; a live
  FreeBSD execution receipt remains pending. Native
  ARM32/AArch64/RV32/RV64 gates are not bytecode evidence. The original
  x86_64-unknown-none QEMU proof remains open.
- Module-init symbols now exclude punctuation inherited from absolute or
  hyphenated source paths in both the pure-Simple bootstrap MIR mirror and the
  Rust seed's owning module-prefix derivation. The existing hosted native smoke
  matrix adds a dynamic module-global case under its punctuated work directory.
  See
  `native_module_init_symbol_path_sanitization_2026-07-19.md`; focused LLVM and
  Cranelift execution pass.
- The Cranelift direct adapter now calls its shared function-definition wrapper
  with the wrapper's two-argument `(module, context)` contract. Fixing that
  exposed the shared MIR/startup gap: the focused function-initialized module
  global now gets zero-backed storage, a runtime init/store function, and a
  hosted startup call before `main`. Multiple runtime initializers fail loudly
  until HIR preserves declaration order. The hosted matrix now requires a real
  PASS, and FreeBSD schedules a scoped Cranelift execution after its default
  LLVM matrix. The shared cross-target `4 -> 5 -> 45` oracle exercises the same
  startup path on AArch64/RV64 LLVM+Cranelift and pins ARM32/RV32/Windows-ARM64
  objects. Cranelift now also accepts the already-supported F32/F64 storage
  types when a runtime initializer supplies their value, while literal float
  statics remain fail-closed; the shared fixture pins function-initialized F32
  and F64 globals. Fresh staged receipts remain pending. See
  `cranelift_module_global_initializer_arity_2026-07-19.md` and
  `cranelift_runtime_initialized_float_global_2026-07-19.md`.
- Multiple call-initialized module globals now reuse their preserved HIR source
  spans to order the existing sequential runtime stores. The shared fixture
  makes its second initializer depend on the first and expects `45`; it also
  checks that a call wrapped in arithmetic is runtime-initialized instead of
  being dropped by the former root-`Call` whitelist. Hosted and
  FreeBSD gates already own that fixture. The cross-target fixture repeats the
  dependent `4 -> 5 -> 45` oracle for AArch64/RV64 LLVM+Cranelift execution and
  ARM32/RV32/Windows-ARM64 object gates. Rebuilt execution remains pending.
  The same fixture now pins an interpolated `text` global as a runtime raw-text
  pointer, preserving `value=7` across LLVM and Cranelift without admitting
  tuple-backed or unrelated opaque statics.
  See `native_multiple_module_initializers_declaration_order_2026-07-19.md`.
- Cranelift text `.parse_f64()` now uses a Pure-runtime raw-f64 owner and an
  explicit i64-argument/f64-result import signature instead of the generic
  all-i64 fallback. Direct Cranelift signatures and runtime imports now select
  the native platform calling convention instead of hardcoding SystemV. The
  existing C9 fixture expects `42` and is scheduled on
  hosted LLVM/Cranelift, FreeBSD LLVM/Cranelift, and Cranelift AArch64/RISC-V64
  QEMU gates. Rebuilt current-source execution remains pending. See
  `native_string_methods_unresolved_in_mir_2026-07-17.md`.
- Integer `.chr()`/`.to_char()` now keeps primitive-builtin priority over an
  unrelated same-named UFCS free function while preserving custom struct
  method ownership. The pure-Simple runtime/interpreter and x86/ARM C hardware
  boundaries share the raw-codepoint UTF-8 behavior. The existing cross-target
  aggregate forces collisions plus two Unicode widths and is scheduled on
  hosted LLVM/Cranelift, FreeBSD LLVM/Cranelift, AArch64/RISC-V64 execution,
  and ARM32/RISC-V32/Windows-ARM64 object gates; the simple-core smoke runs C5
  against the pure runtime as Rust-worker/native-smoke evidence. The observed bare-metal text `.replace` sibling now
  uses replace-all semantics on x86_64, x86_32, ARM32, ARM64, and both RISC-V64
  runtime owners; focused C behavior and the six-owner SSpec contract prevent
  first-match-only, zero-stub, or wrap-prone match bounds. The 32-bit owners
  accept empty strings and reject allocations beyond their existing 1 MiB
  string limit; their bump allocators reject alignment overflow. ARM32, ARM64, and x86_32 text
  bracket indexing now shares the
  hosted/x86_64/RISC-V64 ABI: raw length/index results and tagged one-character
  text, with generic `rt_index_get` decoding its tagged index before forwarding.
  Typed-parameter literal and dynamic-text oracles run in hosted/FreeBSD parity
  and the shared cross-target fixture; 32-bit lanes remain object-only.
  Pure MIR `for ch in text` now lowers through Unicode-aware
  `rt_string_chars` and reuses the existing counted array loop, while dict and
  custom non-array iterables retain the #143 loud failure. Hosted, pure-core,
  x86/x86_32, ARM32/AArch64, and both RISC-V64 runtime owners split one text
  element per UTF-8 codepoint. A dynamic ASCII/BMP/astral strict-dual fixture
  is selected on hosted and FreeBSD matrices; the shared cross-target fixture
  inherits the same sum/join oracle for AArch64/RV64 execution and 32-bit
  object lanes. ARM32 now builds that shared fixture directly and validates a
  nonempty ELF32 hard-float relocatable object; RV32 remains soft-float
  object-only.
  Historical `--entry` Cranelift C5 receipts identified the first failed
  assertion as `65.chr() != "A"` (diagnostic exit `1`); after route correction
  these are Rust-worker evidence, not self-hosted receipts. The runtime returns the
  correct tagged text handle, but MIR recorded the call result as
  `MirType.i64()` and returned it without text conversion, so later equality
  and text methods took integer paths. Current source preserves that 64-bit
  call ABI, then converts the tagged result through the existing
  `decode_runtime_value` text path; this remains width-correct for ARM32/RV32.
  The focused contract pins the raw call and semantic conversion. Rebuilt
  execution remains pending a current-main Stage4: the available older Stage4
  ignored both live-worker selection knobs and reproduced the same byte-identical
  pre-fix C5 binary in all three bounded attempts. No active compiler build or
  reusable cache represented that source snapshot. A later isolated
  current-main compiler-only Stage4 built 675 files with zero failures, but
  its C5 receipt still exited `1` and called the colliding free functions. The
  remaining gate incorrectly required `Unresolved` resolution even when MIR
  proved the receiver integer. Current source gives primitive priority over
  `FreeFunction`/`Unresolved` only, preserves custom instance/trait/static
  dispatch, and reuses the prelowered receiver on free-function fallthrough.
  A fresh 675-file candidate containing that gate still emitted the colliding
  free call. Its exact lowering object matched the linked method, ruling out
  export-closure, backfill, and stale-cache selection. Current source therefore
  also recovers the explicit integer annotation from the function-local
  `local_hir_types` map when the prelowered MIR local has lost its type. The
  focused pure-Simple contract passes 4/4. A later 662-file rebuild contained
  five unresolved stubs and segfaulted on `--version`, so it is rejected rather
  than credited. A later no-stub 675-file candidate is valid and runnable, but
  the prior `--entry` C5 commands are now classified as Rust-worker receipts:
  the pure-Simple bootstrap route requires a positional `.spl` input. The
  malformed `CharOwner` layout presence/payload pair that first blocked that
  route is fixed in current source. The next positional C5 run exposed a
  Stage4 struct-pattern shadowing fault in the MIR prescan walker:
  `HirStmtKind.Expr` forwarded a nil payload and `HirExprKind.Block` could
  accept an `If` payload. Current source now derives runtime discriminants for
  `Expr`, `Let`, `Assign`, and statement `Block`, extracts each payload in an
  isolated qualified arm with an explicit HIR type, and likewise predispatches
  expression `Block`. The source contract pins all four statement payload
  bindings and the expression block binding.

  The classifier source contract was 5/5 before the later test additions.
  A v9 no-stub incremental rebuild completed with `7 compiled, 668 cached,
  0 failed`, but all three method diagnostics remained unresolved. Trace then
  proved primitive calls reach `runtime_int=true` and lower successfully; only
  `CharOwner` plus `char_code_at` still warned. A v11 no-stub rebuild completed
  with `5 compiled, 670 cached, 0 failed`; its declared-owner provenance bridge
  eliminated the `chr`/`to_char` warnings. The final positional C5 receipt now
  fails only at `char_code_at`. That v11 candidate already contains the
  discriminator-safe `mir_type_is_str` Opaque/Tuple hardening, so repeating
  that change is not the next fix.

  This C5 diagnosis has reached its three-cycle cap. The next exact diagnostic
  is to inspect the produced `chr` result/local MIR type and its `let`
  propagation into `nul` before adding any fallback. Do not infer a new
  fallback from the remaining `char_code_at` warning. C9 remains gated: only
  after a fresh positional C5 executable exits `42` should the next bottom-up
  item run, positional C9 `.parse_f64()` with exit `42`. See
  `native_chr_builtin_no_lowering_2026-07-18.md`.

  The 2026-07-25 bottom-up audit found that `bf7a6fc3d9c` had overwritten the
  proven tagged-text bridge from `5d2ef45f6a5c`: `.chr()` decoded its tagged
  result into a raw C pointer before the `let`, losing embedded-NUL length and
  runtime-value provenance. Current source restores the typed MIR copy plus
  `runtime_value_locals` and HIR `Str` registration. Higher-level review
  accepted the one-file root fix. The focused Simple test launcher reached the
  known stale argv0/delegation path and then failed before assertions while
  configuring its structured-result environment, so positional C5 exit `42`
  remains the next execution gate; C9 is still gated.

  Two bounded cache-preserving LLVM Stage4 attempts then stopped before object
  emission. The foreground attempt was terminated at phase-two parse +627s by
  the tool-session lifetime. A detached second attempt advanced to
  `var_reassign_ssa.spl` at +439s, then ended without an artifact while other
  long-lived native workers had created severe process pressure. Neither run
  emitted a compiler diagnostic or stub fallback, and neither changed the
  shared object cache. No third attempt is permitted in that environment:
  resume only after the unrelated workers drain, using the preserved cache and
  a separately bounded process. Positional C5 exit `42` remains unproven; C9
  must not run yet.

  After the runaway test process groups were removed, an isolated Cranelift
  compiler cache produced a valid 675-file no-stub candidate. Positional C5
  first exposed a Stage4 `SymbolId`/optional ABI fault in
  `canonical_mir_type_symbol`: the helper passed the struct through
  `get_symbol(SymbolId?)`, then dereferenced a present-but-nil payload. Current
  source uses the established `get_symbol_raw(symbol.id)` boundary and rejects
  a nil `Some(info)` payload before field access. The final incremental rebuild
  completed with `4 compiled, 671 cached, 0 failed`; candidate SHA-256 is
  `15e7712d3fc37d43c434b3538e9bf6ba201bcf0bb1dfb0b0dff2682a34e6582b`.
  Positional C5 no longer SIGILLs and now fails loudly on unresolved `chr` and
  `to_char` before output, with no stub fallback. This session reached its
  three-cycle cap. The next session must inspect why the existing integer
  builtin classifier is not selected in this exact current candidate; C5 exit
  `42` and C9 remain pending.

  The next bounded session restored the proven discriminator-based
  `MethodResolution` classifier and declared-owner bridge that a later
  overwrite had removed. Its first incremental candidate completed with
  `15 compiled, 664 cached, 0 failed`; primitive `chr`/`to_char` then built
  and ran through the embedded-NUL assertion, exiting `5` instead of failing
  unresolved. Binary inspection proved that `nul.len()` still called
  `rt_interp_cstr` plus `rt_strlen`, which necessarily truncates embedded NUL.
  A provenance-only retry (`4 compiled, 675 cached, 0 failed`) reproduced exit
  `5`, proving static MIR/HIR markers are not a sufficient Stage4 boundary.
  The final fix moves tagged-or-raw discrimination into the existing
  `rt_string_len` ABI: tagged strings use their stored byte length, while raw
  literals use `strlen`; known arrays retain `rt_len`. The final compiler
  candidate SHA-256 is
  `094e130efbc878d29e8cfecb6df6bda77167593705d123ccfe236b23b517ab5f`
  (`4 compiled, 675 cached, 0 failed`). A fresh 18-part pure-Simple Cranelift
  runtime archive built successfully. Positional C5 now passes primitive
  ASCII/BMP/astral conversion, embedded NUL length/codepoint, and all invalid
  scalar checks, then exits `10` at `owner.chr()`.

  This session has reached its three-cycle cap. The remaining C5 item is only
  declared custom-owner dispatch; diagnose why the restored
  `struct_value_syms` owner bridge is not selected before another fix. C9
  remains gated until positional C5 exits `42`.

  The following bounded session proved the owner bridge was selected and found
  the actual shared fault one layer later: Stage4 dropped struct-valued
  implicit method tails when extracting an optional MIR local with `if val`.
  Hoisting the established `result ?? LocalId(id: 0)` form into function
  lowering fixed both `CharOwner` methods. The incremental candidate completed
  with `4 compiled, 675 cached, 0 failed`; positional C5 built without warnings
  and the executable exited `42`. C5 is complete.

  Positional C9 then reached MIR lowering and failed loudly on both
  `.unwrap_or` calls. Parallel source/history traces confirmed the existing
  `parse_f64` nullable provenance source block is intact. Two current-source
  candidates then disproved the optional-control hypothesis: direct `.?` and
  explicit `if option.?: true else: false` normalization both rebuilt cleanly,
  but positional C9 still failed all four `.unwrap_or` calls as unresolved.
  Those ineffective compiler changes were reverted. The fixture now also
  requires default values for both invalid and trailing-junk parses.

  C9 has reached its three-cycle cap. The next session must trace the actual
  MIR local IDs and `local_hir_types` membership at two points only: immediately
  after `rt_string_to_float`, and after the `val` copy into `f`/`zero`/
  `invalid`/`trailing`. Do not change Result/Option routing again without that
  evidence. The safe bootstrap path is now proven: the Rust binary is used
  only to build a pure-Simple Stage4 candidate, with the preserved cache and a
  temporary output. The final candidate build was `5 compiled, 1388 cached,
  0 failed`, SHA-256
  `02b5a88088b77a5644b9c921963d63984bb5688d712463f9bf5bc732c06ff1e2`.
  Credit C9 only when its positional executable exits `42`.

  The next bounded session's trace output recorded that provenance evidence.
  Immediately
  after each `rt_string_to_float` call, the compiled Stage4 trace reported
  result locals `19`, `25`, `31`, and `37`, but both
  `runtime_value_locals.contains(id)` and `local_hir_types.contains(id)` were
  false. A second diagnostic showed direct Boolean Dict reads can return true
  while method-form `.contains` returns false, but direct HirType indexing then
  trapped on a nil receiver; this did not prove a valid metadata entry.
  Replacing the C9-critical metadata checks with explicit `rt_dict_contains`
  rebuilt successfully (`6 compiled, 1387 cached, 0 failed`, candidate
  SHA-256
  `2b4be288d623be41e18bff3d8a43260d0ac5d674191dfeb2cc19bd81ae1ea8f0`)
  but positional C9 still failed all four `.unwrap_or` calls unresolved. That
  ineffective source change and all temporary tracing were reverted.

  This session again reached C9's three-cycle cap; make no further C9 source
  change in this session. In a fresh bounded session, the next evidence
  boundary is the producer extraction itself: replace only
  `if val ts_local = ts_res` in the text-method call result with the established
  positive-presence plus coalesce form (`if ts_res.?` followed by
  `ts_res ?? fallback`), then trace the assigned metadata before changing any
  propagation or Option logic. This is the same struct-optional payload-loss
  class that blocked C5 implicit tails. Credit C9 only after the positional
  executable exits `42`.

  The next bounded session applied only that producer extraction correction
  first. Its clean incremental Stage4 candidate completed with `6 compiled,
  1387 cached, 0 failed`, but positional C9 still rejected all four
  `.unwrap_or` calls. A second candidate replaced the critical metadata
  membership reads with the existing raw-`i64` dictionary lookup ABI after
  direct bracket reads had shown a tagged-key mismatch. It also completed with
  `6 compiled, 1387 cached, 0 failed`, but produced the identical four
  unresolved calls. The raw lookup experiment was reverted; it was not the
  root fix. The independently established non-void call-result extraction
  correction remains, with a source contract.

  C9 has again reached the three-cycle cap. The next session must inspect the
  actual metadata write representation at the `parse_f64` producer and the
  copied receiver immediately before method dispatch. In particular, determine
  whether `local_hir_types` requires its documented parallel-array owner
  pattern rather than another dictionary membership variant. Do not change
  `unwrap_or` routing until that representation is proven. Credit C9 only when
  the positional executable exits `42`.

  The following bounded session proved that representation boundary. History
  identified the existing Stage4 precedent: `MirLowering` already keeps local
  symbol bindings in parallel arrays because mutation of a dictionary stored
  in that struct is not reliable. The same owner pattern now backs declared
  local HIR types and runtime-value membership, with shared set/find/remove
  helpers and every caller migrated. The C9 fixture adds a second-hop
  `zero_copy` binding so metadata-copy persistence is distinguished from direct
  `unwrap_or` routing. High-level review found no helper, constructor, reset,
  or caller-migration blocker, and pure-Simple checks reported both
  `src/compiler` and `src/lib` source parsing `OK`.

  C9 remains uncredited. Three cache-preserving Stage4 attempts were consumed
  before positional execution: the first two found committed parser errors in
  the Web-to-Engine2D lane (a split assignment and an unparenthesized split
  Boolean), both now repaired; the third reached link and failed on undefined
  `moduleloader_execute_smf` from CLI `run_file` under `core-c-bootstrap`.
  Do not retry C9 again in this session. The next bottom-up blocker is to restore
  the pure-Simple/core-C owner for that loader symbol, then resume C9 in a fresh
  bounded session and credit it only when the positional executable exits
  `42`.

  The loader blocker is now fixed without a hosted fallback. The first explicit
  facade import proved that the older loader reached six `rt_smf_reader_*`
  declarations that have no C or Rust implementation. CLI SMF execution now
  reuses the existing pure-Simple `SmfReaderMemory` compatibility loader
  instead. Its two real OS boundaries, `rt_mprotect` and `rt_munmap_raw`, are
  owned by the Stage4 legacy core C provider on Unix, macOS, FreeBSD, and
  Windows, with its audited ABI contract expanded from 19 to 21 symbols.
  The runtime-lane divergence baseline records these deliberate Stage4-only
  owners plus the matching `rt_getpid` compatibility owner; the combined
  runtime bundle does not contain either pair and its duplicate-symbol gate
  remains unchanged.

  The final cache-backed Stage4 CLI candidate completed with `5 compiled,
  1394 cached, 0 failed`; SHA-256
  `ceb22bdcc8072ff7ddfe612c1ffd858d35579ef82b1748df1b2ab0fccc0ee251`.
  Runtime sanity on a missing `.smf` exits `1` with exactly one controlled
  `SMF load failed` message. The CLI branch now returns that result instead of
  falling through to source interpretation. The candidate is ready for a
  fresh positional C9 run, but C9 remains uncredited in this session because
  its three-cycle cap was already reached.

  A fresh bounded C9 session then exercised that candidate on the five-case
  fixture (`f`, `zero`, `invalid`, `trailing`, and second-hop `zero_copy`).
  The first positional Cranelift run reached MIR lowering and rejected all five
  `.unwrap_or` calls as unresolved. A cache-preserving diagnostic candidate
  completed with `13 compiled, 1386 cached, 0 failed`, but the traced run
  exited `139` before any producer, copy, or method-dispatch marker. All
  temporary trace code was removed.

  History and source review identified the next candidate representation boundary:
  `find_local_hir_type` and its C9-critical consumers exchange `HirType?`.
  Rewriting only the lookup to the established optional-accumulator return
  pattern produced a candidate with `5 compiled, 1394 cached, 0 failed`, but
  the positional run still exited `139`. That change was reverted rather than
  preserving a crash.

  This session has reached C9's three-cycle cap. In the next fresh session,
  change only the C9-critical consumers—`option_inner_hir_type_for_local`, the
  primary `let` metadata copy, and reassignment if reached—from `if val`
  optional aggregate destructuring to the established `.?`/`??` extraction
  pattern. Then trace the option-resolution gate. Do not change `unwrap_or`
  routing, and defer LLVM execution until backend-neutral MIR lowering passes.
  Credit C9 only when the positional executable exits `42`.

  The next bounded session migrated those five C9-critical consumers to the
  established `.?`/`??` aggregate extraction pattern. The first pure-Simple
  self-rebuild attempt exited `139` before logging, so the Rust seed was used
  only for its bootstrap role. It produced a pure-Simple candidate with
  `1399 compiled, 0 cached, 0 failed`. That candidate resolved all five
  `.unwrap_or` calls, emitted and linked the Cranelift fixture, and exited
  `20`: uppercase passed, while the parse/Option block did not.

  One staged first-failure probe returned `5`, proving `f`, `zero`, invalid,
  and trailing presence checks passed before the nonzero `f.unwrap_or(0.0)`
  value comparison failed. Review found the same payload/handle mistake in
  `unwrap`, `unwrap_or`, and `map`: each extracted `some_val_*` and then passed
  the enclosing `receiver_local` to `decode_runtime_value`. All three sibling
  calls now decode the extracted payload, with focused source contracts.
  The cache-backed candidate completed with `5 compiled, 1394 cached,
  0 failed`, but the positional C9 fixture still exited `20`.

  C9 remains uncredited and this session has reached its three-cycle cap.
  The next fresh session should run the staged first-failure probe against the
  payload-fixed candidate to determine whether the first failing condition
  advanced beyond nonzero `f.unwrap_or`; do not repeat the already-recorded
  positional run first. LLVM and the downstream platform matrix remain
  deferred until the Cranelift executable exits `42`.

  The following bounded session first reran that staged probe against the
  payload-fixed candidate; it still returned `5`, so the first nonzero
  `unwrap_or` value remained corrupt. Six sibling `rt_is_some` call-result
  sites and both F64/F32 unbox call-result sites still used Stage4-unsafe
  `if val` extraction of `LocalId?`; all now use direct `?? LocalId(id: 0)`
  or guarded `.?`/`??` extraction. The canonical C9 fixture now reports each
  presence/value failure with a distinct exit while preserving success `42`.
  A cache-backed pure-Simple candidate completed with `15 compiled,
  1384 cached, 0 failed`, but the staged fixture exited `2`.

  A final value-class probe returned `14`: the present value was neither the
  default, zero, a sane 3.14-range scalar, nor negative. Cranelift's generic
  external-call path declared every result as i64, while
  `rt_value_as_float(i64)` returns f64. The backend now has a typed
  i64-to-f64 runtime-import helper and routes that exact symbol before the
  generic path, with source contracts for the parameter and return ABI.
  The resulting candidate completed with `6 compiled, 1393 cached, 0 failed`;
  the canonical Cranelift C9 fixture still exited `2`.

  C9 remains uncredited and this session has reached its three-cycle cap.
  The next fresh session should inspect the F64 `unwrap_or` some-branch merge:
  trace the typed `rt_value_as_float` SSA result through
  `emit_copy(result_local_uo, some_val_uo)` and Cranelift's destination
  stack/value-map handling. Do not repeat the already-recorded admission or
  import-signature experiments. LLVM and platform-matrix execution remain
  deferred until Cranelift exits `42`.

  A fresh session then isolated the merge hypothesis with a standalone typed
  F64 probe. Both the unannotated and explicit-`f64` forms exited `1` on the
  first check, `3.14 != 3.14`, before any Option or branch merge. This
  establishes an independent F64 literal/comparison failure before C9's
  shared-result-slot construction, so C9 cannot yet isolate that merge. The
  reproducer is retained as
  `test/03_system/native/f64_literal_compare.spl`, expected exit `42`.

  Six `MirOperand.Copy`/`Move` optional-local consumers in Cranelift value
  loading, indirect-call lowering, and operand-type classification now use
  direct `?? LocalId(id: -1)` extraction instead of Stage4-fragile `if val`.
  The resulting candidate completed with `7 compiled, 1392 cached, 0 failed`;
  the annotated F64 reproducer still exited `1`.

  The compiler-side SFFI wrapper also calls
  `rt_cranelift_fconst(i64, i64, f64) -> i64`. A typed
  `(I64, I64, F64) -> I64` runtime-import helper and exact symbol route now
  prevent that call from falling through the generic all-i64 extern ABI. The
  next candidate completed with `6 compiled, 1393 cached, 0 failed`, but the
  F64 reproducer still exited `1` and staged C9 still exited `2`.

  The remaining boundary was the adapter's call to the bare Simple wrapper
  `cranelift_fconst`, not the wrapper's inner `rt_cranelift_fconst` call.
  Cross-module wrapper calls use the same external-import lowering, so the
  bare name still received the generic all-i64 signature and passed its f64
  argument in the wrong ABI class. Both exact names now share the existing
  `(I64, I64, F64) -> I64` import helper; fcmp remains unchanged because its
  operands are intentionally i64 SSA-value handles. A source contract covers
  both names.

  Behavioral verification is blocked after the bounded three-cycle rebuild
  cap. Two seed-driven Cranelift rebuilds reached the linker but failed on the
  same unrelated missing entry-closure symbols (`Poll.unwrap`, `Path.join`,
  `FailSafeResult.is_err`, and siblings). A pure-Simple LLVM rebuild remained
  compute-bound without producing cache artifacts for 20 minutes and was
  stopped at the budget ceiling. The source-contract runner also reported
  `no examples executed`; none of these failures disproves the narrow ABI
  correction, but the plain F64 and C9 exits remain uncredited.

  C9 remains uncredited and this session has reached its three-cycle cap.
  The next fresh session must first restore a linkable cached compiler
  candidate, then run the plain F64 reproducer. If it remains red, inspect the
  actual F64 value at `rt_cranelift_fconst` entry and the two Cranelift
  operands passed to `cranelift_fcmp`; do not rewrite the shared-result merge
  until the plain reproducer is green.
  LLVM and platform-matrix execution remain deferred until the plain F64
  reproducer and C9 both exit `42`.

  The exact retained Stage4 seed command was recovered from the session log
  and replayed with its original full-CLI entry, tooling source, low-memory
  flag, and shared cache. It produced a corrected-source candidate with
  `5 compiled, 1394 cached, 0 failed`. That seed-built generation still exited
  `1` on the plain F64 fixture. Object disassembly proved the direct `3.14`
  comparison itself received pointer-like payloads such as `0x40c4efd0`
  instead of IEEE-754 `0x40091eb851eb851f`; fcmp was consuming an already-bad
  constant. The fixture now stages direct literal, local round-trip, and
  branch merge failures as exits 1, 2, and 3.

  This also establishes a generation boundary: the Rust seed does not execute
  the patched pure-Simple `cl_translate_call`, so its candidate cannot prove
  the bare-wrapper ABI correction. A fresh second-generation compiler must be
  built by that candidate through Cranelift. Both bounded closure builds
  crashed before object emission in
  `_native_build_entry_closure -> HashMap.contains_key`; a debugger backtrace
  captured that exact stack. Removing `--entry-closure` avoided the crash but
  spent the 10-minute cap in whole-source frontend work without emitting an
  object. The next fresh session should fix or bypass that closure HashMap
  crash with a focused regression, then produce the second-generation
  compiler from an isolated cache and rerun the staged F64 fixture once.

  The closure walker now uses built-in `Dict` tables instead of custom
  `HashSet.contains`/`HashMap.contains_key` probes. A seed-built generation-1
  CLI linked (`5 compiled, 1393 cached`) and, with a fresh generation-2 cache,
  traversed 908 closure sources and entered parsing rather than crashing.
  Generation-2 parsing remained too slow (roughly 10–50 seconds per early CLI
  file), so the bounded run was stopped; full generation-2 link, staged F64,
  and C9 remain uncredited. The generic non-`me` receiver ABI is source-fixed:
  both MIR method-call routes prepend the receiver and the existing cross-module
  `fn` source contract covers zero and explicit arguments. Native self-host
  execution remains pending an admitted pure-Simple executable; this change is
  only a bootstrap bridge. Next: fix the self-host parse
  performance blocker, resume the fresh generation-2 build, then run staged
  F64 once and C9 only after F64 exits 42.

  The next generation-1 rebuild exposed a seed-linker alias defect rather than
  a missing implementation: callers referenced `io__env_ops__env_get` while a
  linked object defined `nogc_sync_mut__io__env_ops__env_get`. The resolver
  compared only the final `env_get` leaf and rejected it as ambiguous. It now
  prefers a unique full qualified suffix, rejects qualified misses instead of
  guessing by leaf, and handles leading object-format underscores exact-first.
  Focused unit tests pass; rebuild the bootstrap seed before retrying the full
  CLI link and generation-2 performance receipt.

  That rebuilt seed then exposed a lost half of the refutable-let-else feature:
  current stdlib sources use `val Some(x) = e else:`, and the pure parser
  supports it, but the Rust parser change from historical commit
  `6d94927c0b96` was absent from current main. The seed parser support is
  restored with focused tests. Review also found and fixed a shared safety bug:
  shadowable `panic`/`fatal`/`abort` calls (and pure `pass/todo`) no longer count
  as guaranteed divergence; only syntactic `return`/`break`/`continue` do.
  Unsupported typed or mutable payload bindings fail closed. The positive
  Simple spec covers both the matched payload and fallback paths.

  A follow-up cache audit rejected the dormant
  `SIMPLE_NATIVE_BUILD_SKIP_PRE_PARSE` prototype: it set an unread config flag
  after checking record existence only, while compilation still performed the
  full parse/HIR/MIR pipeline. The prototype is removed and the cache policy
  test pins its absence. Whole-closure invalidation after a compiler or source
  change remains deliberate because native entries persist empty dependency
  lists and no final-link manifest. Do not weaken that scope; a future true
  warm-start bypass first needs a versioned final-link manifest with the exact
  compiler/backend/target/option/source fingerprint and deduplicated object
  set.

  Parser tracing then confirmed that token text already comes from the lexer's
  direct current-token slot. The old generation-keyed whole-source parser cache
  had no callers, so its slots, environment counter, and invalidation calls are
  removed with a source regression. This removes misleading dead work; it does
  not credit the outstanding 22 KiB parser-time gate or authorize another full
  generation build.

  The completed SharedText seed now reaches the bounded parser oracle. A false
  `PythonSelf` recovery hint had diagnosed valid—and sometimes required—
  `self.field` mutation hundreds of times; the scaling fixture also requested
  a clock symbol absent from the seed, forcing a second interpreter graph load
  after JIT failure. Both roots are fixed with focused regressions. The current
  oracle improved to 1.061s/4.172s, so the 22 KiB absolute gate passes, but its
  3.93x ratio and 968,524 KiB RSS remain uncredited. Do not launch the
  493-source generation until those measured owners are addressed.
  A 500ms/504ms equal-size disjoint-token control rejects the global token
  interner as the scaling owner. Native arena mutation, bootstrap env mirrors,
  and duplicate-declaration scans are also inactive on this JIT path. The
  three-cycle cap is reached; the next fresh session must run one lexer-only
  440/880 timing discriminator before changing production code.
  That discriminator measured 539ms/5,272ms and isolated two
  field-to-local array copies in `scan_ident` and `scan_number`; value-copy
  lowering cloned the whole source per identifier/number token. Direct
  indexed field reads remove the copies. The unchanged parser oracle now
  passes at 33ms/75ms (2.27x), 205,192 KiB max RSS, and exit 0. A source
  contract forbids restoring either hot whole-array alias. The 493-source
  phase-2 and imported-enum gates remain pending.

  The retained generation-1 pure-Simple candidate could not run the focused
  scaling fixture because HIR resolution rejected exported `parse_module` and
  `parser_has_errors`; both parser module spellings failed. The bounded
  three-cycle fixture lane is exhausted with no timing credit. Diagnose that
  candidate's source-closure/export resolution before the next measurement;
  do not substitute the Rust seed. Four consumers now use the canonical
  `compiler.core.parser` spelling, but that cleanup receives no performance or
  blocker credit.

  The unresolved-symbol root is now isolated before HIR: the CLI entry-closure
  walker only probed literal source-root paths, so `compiler.core.parser` never
  reached numbered `compiler/10.frontend/core/parser.spl`. It now reuses the
  driver's numbered compiler resolver, constrained to the caller's supplied
  source roots, with a source contract. This remains uncredited until a fresh
  pure-Simple candidate executes the focused fixture in a later bounded cycle.

  A bootstrap seed rebuilt with both the alias and grammar fixes passed the
  former 16-second discovery failure and emitted no parser/link diagnostics,
  but the final full-CLI attempt hit its 15-minute cap at sustained 100% CPU
  and about 515 MiB RSS without producing an artifact. The three-attempt cap is
  exhausted for this lane; do not retry unchanged. Generation-1,
  generation-2, staged F64, and C9 remain uncredited. The next session should
  inspect the warm native-cache miss/compile profile before another full build.

  Platform-gate hardening now routes every hosted native-smoke case through
  shared `platform_case`, `require_nonempty_target_object`, and
  `require_runtime_exit` checks. A focused pure-Simple generation-1 Cranelift
  arithmetic case passed with the strict receipt
  `total=1 pass=1 fail=0 ... native_smoke_matrix=true`. The canonical FreeBSD
  QEMU wrapper also fails before bootstrap unless `uname -s` is exactly
  `FreeBSD`. This strengthens Linux/macOS/Windows/FreeBSD consumers of the
  shared matrix but is not a substitute for their pending hosted CI receipts.
  The required pure-Simple SSpec docgen attempt timed out after 60 seconds
  without output; no generated-manual credit is claimed.

  The Linux pure-Simple architecture gate now schedules default-LLVM Windows
  ARM64 COFF scalar, cross-module `Result<u8>`, and Option objects and validates
  their format/machine through the shared target assertions. Its portability
  source gate passes. The retained old generation-1 candidate crashed
  `field access on nil receiver` followed by illegal instruction while trying
  the focused scalar object, before producing an artifact; this is blocker
  evidence only. A fresh candidate must run the wired gate before Windows
  ARM64 LLVM receives object credit.

  Two legacy CI definitions were retired instead of repaired:
  `windows-tests.yml` executed no Windows binary, while
  `test-isolation.yml` invoked five absent test roots and masked every failure.
  Their platform intent is superseded by the mandatory multiplatform, FreeBSD
  QEMU, and RISC-V hardware gates; they provided no valid coverage to preserve.
  The portability source contract rejects restoration of either false-green
  workflow, and both deleted paths still trigger that contract. External
  branch protection must not require their retired check names.

  The first exact brace-literal one-case attempt did not reach compilation:
  the parity harness defaulted to the untracked `bin/simple` convenience path,
  which is absent in a clean jj workspace. It now defaults to the tracked
  `bin/release/simple` self-hosted wrapper. The attempt is not a native receipt,
  and the case remains pending until a later bounded run. Both parity and
  native-matrix gates now reject a missing `SIMPLE_BINARY` once, before
  generating cases, instead of reporting misleading per-case compiler bugs.

  Entry-closure triage found a second CLI import parser still materializing
  every source line and admitting fake `use` declarations from docstrings.
  The CLI now delegates use/import/export-use discovery to the driver's shared
  byte scanner; only guarded `mod` and `export member.*` sibling syntax uses a
  compatibility line scan. Executable scanner assertions and a CLI source
  contract pin the behavior. The deployed pure-Simple tool segfaulted before
  the focused tests, optimizer, and source check could report results, so no
  performance or behavioral receipt is claimed this session.

  GDB then confirmed the deployed pure CLI's known stale `rt_env_set` ABI:
  `SIMPLE_BOOTSTRAP_EXPR_COUNT` reached libc with its 27-byte key length as the
  value pointer. Current Simple callers already stringify every environment
  value, and the existing full-candidate admission probes the four-argument
  ABI. A concurrent/manual Rust seed nevertheless occupied the release
  launcher's preferred path, bypassing admission. The tracked launcher now
  performs a bounded identity check and rejects seed/debug artifacts before
  normal dispatch; its integration test covers forwarding, seed rejection,
  and missing-runtime failure. A fresh admitted Stage4 redeploy remains open.

  Platform CI truthfulness was tightened again. The legacy
  `cross-platform.yml` and reusable `simple-llvm-cross.yml` workflows were
  retired: they used checked-in artifacts or handwritten LLVM IR and masked
  missing platform execution. Release no longer depends on that false gate,
  and the README badge points to the canonical strict bootstrap matrix.
  `baremetal-tests.yml` now preserves only its real Cortex-M33 C-shim QEMU
  smoke; it grants no Simple ARM32 compiler credit. The portability contract
  rejects restoration of the retired workflows or optional phantom jobs.
  Windows x86_64 hosted default-LLVM execution remains the genuine matrix gap.
  The stale release-only Chocolatey install and optional `llvm-lib` Stage 2
  were removed because the Rust seed requires `llvm-config` and link libraries
  that provider does not supply; the portability guard prevents that
  false-green path from returning. Real support needs a pinned compatible seed
  provider or a designed Cranelift-seed to pure-Simple Stage 2 bridge before
  the dynamic LLVM Stage 3 gate can become mandatory.

  Windows run `30178515336` reached Stage 2 in both MSVC and MinGW, then failed
  with `LNK1120`. The missing symbols were lost because the Rust bootstrap
  linker returned only stderr while `link.exe` writes unresolved-symbol
  diagnostics to stdout. Both linker failure paths now preserve both streams,
  with a focused regression test. The next strict Windows run must identify
  the actual missing provider before any link fix is selected.

  Windows run `30180656177` exposed both provider boundaries. MinGW rebuilt
  host-MSVC Rust archives because strict authority omitted Cargo's explicit
  target, then selected MSVC linker conventions from the host compiler. MSVC
  passed its aggregate Simple objects and `simple_native_all.lib` to
  `clang-cl` without per-archive `/WHOLEARCHIVE`, leaving 92 providers
  unresolved. Strict authority now binds all four Rust builds, cache paths,
  preserved compiler tools, manifest verification, and provenance
  fingerprints to the selected target. Rust and pure-Simple archive discovery
  use the same linker flavor (`.a` for MinGW, `.lib` for MSVC), including
  `SIMPLE_WINDOWS_ABI`, and strict `clang-cl` retains both required archives.
  The focused Rust/Simple checks and bootstrap portability contract pass. A
  fresh hosted Windows run remains required before either ABI receives
  execution credit. The admitted July 25 pure-Simple binary exits `139` during
  the broader `check src/compiler` gate, before diagnostics, so it provides no
  local core/MCP acceptance evidence and was not replaced with the Rust seed.
