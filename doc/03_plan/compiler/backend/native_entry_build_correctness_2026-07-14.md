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
  `total=15 pass=15 fail=0 codegen_fallback_hits=0`.
- **Gate 2 — parity:** `scripts/check/check-native-seed-parity.shs` (dual-backend
  regression harness) must report `native_seed_parity=true`. By default it
  defines **90 logical cases / 121 recorded checks** because strict-dual cases
  record LLVM and Cranelift separately. `NATIVE_OPEN_BUG_REPROS=1` expands this
  to **93 logical cases / 126 recorded checks**; execution is opt-in because
  those three reproductions remain known-red. Execution of the expanded matrix
  is pending.
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
  correctness campaign. Runtime-native's 18-symbol legacy dependency owner is
  now source-implemented as an exact localized compatibility provider. The
  current source blocker is the fail-closed exact archive-projection/link step
  after inventory and transitive requested-owner resolution, not the retired
  seed enum/mcall diagnoses. See
  `redeploy_stage4_plan_2026-07-09.md` and `stage4_stub_symbol_plan_2026-07-11.md`.
