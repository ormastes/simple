# Lane MATCHER — nil matcher / `is_nil` builtin gaps

**Date:** 2026-07-28
**Scope:** two blocking gaps reported by lanes DBDUR, NILQ, SPECFIX.

## (a) `assert_nil` rejected a typed `Option::None` — FIXED

- Reproduced on both engines with `build/matcher_repro/nil_repro_spec.spl`
  (`assert_nil failed: got Option::None`).
- Root cause: `src/compiler_rust/compiler/src/interpreter_call/bdd.rs:1513`
  compared `val != Value::Nil` instead of `val.is_nil_like()`. The mirror arm
  `assert_not_nil` had the same bug in reverse and **passed** a typed `None`.
- Fixed both arms to `Value::is_nil_like()` — the same predicate `== nil` and
  `expect(x).to_be_nil()` already use. Still strict (not a truthiness check).
- The pure-Simple `std.spec` definition (`src/lib/nogc_sync_mut/spec.spl:719`)
  and the test-runner's injected inline helper were already correct — they go
  through `==`. Only the Rust seed builtin was wrong.
- Bug doc: `doc/08_tracking/bug/assert_nil_rejects_typed_option_none_2026-07-28.md`

### File-abort claim: NOT a matcher/runner defect

DBDUR reported the runner aborted the file at the failing assertion. It does
not: in `build/matcher_repro/nil_repro_spec.spl` the failing example is followed
by four more that all run (`6 examples, 1 failure`). The whole-file loss in
`db_server_tier_spec.spl` was the **120s file timeout**
(`error: test-runner: file timed out`), which is a separate issue owned with
that spec, not by this lane.

## (b) `is_nil` as a language builtin — DECIDED: do NOT implement

Resolution (b): `is_nil` stays a user-type method name; spec call sites on
ordinary values use `== nil` or `expect(x).to_be_nil()` / `.to_not_be_nil()`.

Decisive reason: in `interpreter_helpers/method_dispatch.rs::call_method_on_value`
the built-in receiver-type arms match **before** user `impl` methods (builtins
~L45-618; `_impl_methods` only from L619). A universal `is_nil` builtin would
**shadow** the 26 existing correct `fn is_nil` methods on the compiler/interpreter
`Value` types, where `is_nil` means "is this `Value` the Nil **variant**" — a
different question. It would answer "is this runtime value absent" (always
`false` for a present struct), turning 26 correct call sites into silent wrong
answers. That is strictly worse than today's loud failure.

Full reasoning recorded in
`doc/08_tracking/bug/is_nil_is_not_a_language_builtin_2026-07-27.md`
(new "DECISION" section). Item 2 of that bug — the two engines disagree on the
**failure phase** (interpreter = compile-time, JIT = runtime) — is left OPEN;
that fix lives in `src/compiler/**`, outside this lane's owned paths.

### Call sites corrected (9, in both the `01_unit`/`03_system` and legacy
`unit`/`system` copies)

| file:line | was | now |
|---|---|---|
| `test/01_unit/os/kernel/loader/elf64_spec.spl:35,40` | `expect(h.is_nil()).to_equal(true)` | `expect(h).to_be_nil()` |
| `test/01_unit/os/kernel/loader/smf_spec.spl:162` | same | `expect(h).to_be_nil()` |
| `test/01_unit/os/kernel/logging/marker_wire_format_spec.spl:38,43` | same | `expect(spec).to_be_nil()` |
| `test/01_unit/os/kernel/logging/marker_wire_format_spec.spl:33,75` | `...to_equal(false)` | `expect(spec).to_not_be_nil()` |
| `test/01_unit/lib/gpu/engine3d/resource_pool_spec.spl:80` | same | `expect(found).to_be_nil()` |
| `test/01_unit/os/simpleos_board_hardening_spec.spl:40` | same | `expect(...).to_be_nil()` |

Deliberately **left alone** (legitimate user-type receivers, `is_nil` resolves
there correctly): `test/01_unit/runtime/runtime_value_test.spl:92,124`
(`TestRuntimeValue`) and `test/03_system/compiler/mir_types_spec.spl:202`
(MIR literal).

## Coordination

- `interpreter_call/bdd.rs` is inside lane GFIX's declared directory but was
  **clean** (GFIX's dirty files are `interpreter/{expr/calls.rs, expr/control.rs,
  mod.rs, node_exec.rs, place.rs}` and `interpreter_helpers/patterns.rs`). The
  edit is 2 arms in 1 otherwise-untouched file — no textual overlap with GFIX.
- Backups of every file this lane touched: `/tmp/matcher_lane_backup/`.

## Verification (fresh seed at `build/matcher_repro/bin/simple_matcherfix`)

`cargo build --profile bootstrap -p simple-driver` → 31 MB seed, `cargo check -p
simple-compiler` clean. `bin/simple` and `bin/release/**` were NOT overwritten.

| spec | pre-fix (`bin/simple`) | post-fix (scratch seed) |
|---|---|---|
| `build/matcher_repro/nil_repro_spec.spl` | 6 total, 5 pass, **1 fail** | 6 total, **6 pass** |
| `test/01_unit/lib/spec/nil_matcher_option_none_spec.spl` (new) | 14 total, 13 pass, **1 fail** | 14 total, **14 pass** |
| `test/01_unit/lib/spec/assert_functions_spec.spl` (existing, no-regress) | 7 pass | 7 pass |
| `db_server_tier_notransport_spec.spl` (payoff, see below) | 29 total, 23 pass, **6 fail** | 29 total, **28 pass, 1 fail** |
| `test/01_unit/os/kernel/loader/elf64_spec.spl` | blocked on `is_nil` | **4/4** |
| `test/01_unit/os/kernel/loader/smf_spec.spl` | blocked on `is_nil` | **18/18** |
| `test/01_unit/lib/gpu/engine3d/resource_pool_spec.spl` | blocked on `is_nil` | **17/17** |
| `test/01_unit/os/simpleos_board_hardening_spec.spl` | blocked on `is_nil` | 4 total, 2 pass, 2 fail (both **unrelated** content failures, no `is_nil`) |
| `test/01_unit/os/kernel/logging/marker_wire_format_spec.spl` | blocked on `is_nil` | 8 total, 3 pass, 5 fail — 2 are `src/os/kernel/log/markers.spl:245` (filed, out of lane scope), 3 pre-existing |

### Payoff headline

`test/system/database/server/db_server_tier_spec.spl` (30 examples) **hangs**
at example #5 ("answers every message on a connection driven by the transport
port") on lane DBDUR's in-flight `src/lib/nogc_sync_mut/database/server/transport.spl`
— that hang, not the matcher, is what loses the file. On the fixed seed the
`:114` example ("discards an abandoned transaction when the connection closes")
**passes** before the hang; pre-fix it was red.

To get a clean number, `build/matcher_repro/db_server_tier_notransport_spec.spl`
is the same file with only that one hanging example removed (29 examples):

- pre-fix: **23 passed / 6 failed** — **5 of the 6 were
  `assert_nil failed: got Option::None`**
- post-fix: **28 passed / 1 failed** — all five `assert_nil` reds gone; the one
  remaining failure is unrelated and pre-existing.

**5 previously-red examples flip green in that one spec.** The "26 hidden
examples" figure DBDUR expected does not apply — the runner does not abort the
file on a failed assertion (proven above); the loss was the timeout.

## Artifacts

- Fix: `src/compiler_rust/compiler/src/interpreter_call/bdd.rs` (assert_nil / assert_not_nil)
- Regression spec: `test/01_unit/lib/spec/nil_matcher_option_none_spec.spl`
- Repro: `build/matcher_repro/nil_repro_spec.spl`
- Bug docs: `doc/08_tracking/bug/assert_nil_rejects_typed_option_none_2026-07-28.md`,
  `doc/08_tracking/bug/is_nil_is_not_a_language_builtin_2026-07-27.md`
