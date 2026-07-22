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
  defines **95 logical cases / 133 recorded checks** because strict-dual cases
  record LLVM and Cranelift separately. `NATIVE_OPEN_BUG_REPROS=1` expands this
  to **96 logical cases / 134 recorded checks**; execution is opt-in because
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
  remains pending. The canonical fixed-arity Stage4 API now also enables the
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
  Pure-Simple text `.char_code_at(index)` now lowers after custom-owner
  dispatch through a reserved alias to the exact raw-i64 runtime ABI instead
  of boxing/decoding the codepoint or capturing a same-named source function.
  The shared runtime accepts raw literals and tagged dynamic text
  without allocation and decodes valid UTF-8 consistently; hosted x86_64,
  freestanding x86_64/AArch64/RV64, textual LLVM, LLVM-lib, and Cranelift owners
  are aligned. Existing Linux/macOS/Windows/FreeBSD smoke and AArch64/RV64
  execution fixtures now pin raw/tagged/Unicode/bounds behavior. Focused C
  syntax and hosted runtime behavior pass; the original x86_64-unknown-none
  pure-Simple redeploy/QEMU proof remains pending.
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
  tests. Canonical FreeBSD bytecode execution remains pending; native
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
  against the pure runtime. The observed bare-metal text `.replace` sibling now
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
  Rebuilt current-source execution remains pending. See
  `native_chr_builtin_no_lowering_2026-07-18.md`.
