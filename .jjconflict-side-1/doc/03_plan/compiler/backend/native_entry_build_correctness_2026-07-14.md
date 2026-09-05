# Native `--entry` Build Correctness — Status & Remaining (2026-07-14)

Tracks the pure-Simple `native-build --entry` correctness campaign that feeds
self-hosting **#138** (single-file native-build route). Goal: every construct
the native backend emits must equal the seed interpreter oracle, **or** be
correct-by-construction where the oracle is provably broken. A loud build
failure is **never** silently converted to a wrong answer.

## Current session remaining (2026-07-24)

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
- **Native:** `env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry p.spl -o out --clean`.
- **Gate 1 — matrix:** `scripts/check/native-smoke-matrix.shs` must report
  `total=15 pass=15 fail=0 codegen_fallback_hits=0`.
- **Gate 2 — parity:** `scripts/check/check-native-seed-parity.shs` (dual-backend
  regression harness) must report `native_seed_parity=true`. By default it
  defines **101 logical cases / 145 recorded checks** because strict-dual cases
  record LLVM and Cranelift separately. `NATIVE_OPEN_BUG_REPROS=1` expands this
  to **102 logical cases / 146 recorded checks**; execution is opt-in because
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

~45 root causes fixed total (some pre-date this table). Matrix has held 15/15
throughout.

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
  pending, so the opt-in case stays known-red until measured.
- Open filed bugs, in bottom-up order:
  - `native_try_op_on_option_silent_wrong_2026-07-14.md` source-implements `?`
    for authoritatively typed flat and boxed Option locals/direct-call returns;
    resolved and unresolved-method provenance paths are source-covered without
    guessing genuinely unknown late dispatch. Native-authoritative annotated,
    direct, and unresolved-method cases select flagless LLVM or explicit
    Cranelift on hosted Linux/macOS/Windows and FreeBSD x86_64. ARM32 default
    LLVM and Windows ARM64 LLVM/Cranelift require successful, nonempty target
    objects without the retired fail-closed diagnostic. Execution is pending.
    The flat payload-3 collision and uniform tagged Option ABI remain open.
  - The cross-module `Result<[u8], E>` control now routes both its Ok and Err
    paths through `?`. Existing LLVM and Cranelift gates schedule it on FreeBSD
    x86_64 and AArch64/RISC-V QEMU without adding another cross build; execution
    remains pending.
  - `native_text_option_unwrap_pointer_value_2026-07-15.md` is resolved at
    origin tip 8932fcb3a148: its exact flat-nullable text repro builds and
    prints `opt`. Explicit enum Option remains the separate tagged-ABI item.
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
    execution is pending.
  - `native_class_array_field_mutation_segfault_2026-07-17.md` is source-fixed
    by registering declared class-field aggregate metadata and mirroring normal
    field projection provenance in mutating-receiver prelowering. A strict
    dual-backend case covers a non-first field's `.push`, field index assignment, and
    visibility of that array handle through an alias captured before mutation.
    The exact native-build shapes were re-verified locally; Linux runs the case
    in the full gate, while macOS arm64/x64, Windows x64, and FreeBSD select it
    explicitly. First staged platform-matrix execution is pending.
  - `native_nested_struct_value_copy_alias_2026-07-17.md` is source-fixed by
    routing local and plain-parameter value copies through one recursive MIR
    owner. Nested value structs are isolated, embedded classes stay shared,
    and nil nested fields are guarded. A strict LLVM/Cranelift case runs in
    Linux's full board and the hosted macOS/Windows plus FreeBSD selections;
    execution is pending. Array-of-class boxing and cyclic value layouts remain
    separate.
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
  the strict dual-backend typed-output/filter control in the full gate; macOS
  arm64/x64, Windows x64, and FreeBSD x86_64 select it explicitly. First staged
  platform-matrix execution is pending.
- The whole-compiler redeploy (#99 / Stage4) remains separate from this
  correctness campaign. Its current source blocker is the fail-closed exact
  archive-projection/link step after runtime-native inventory and transitive
  requested-owner resolution, not the retired seed enum/mcall diagnoses. See
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
  absent. The unchanged cross-module fixture still needs rebuilt execution.
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
