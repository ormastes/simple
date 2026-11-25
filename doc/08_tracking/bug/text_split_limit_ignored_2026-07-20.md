# `text.split` limit ignored or mistyped
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

BugDB ID: `text-split-limit-ignored`
Priority: P2
Claimed: 2026-08-17, Codex `p2_text_split` lane

## 2026-11-25 re-verification (interpreter mode, attr-capable seed)

`test/01_unit/compiler/interpreter/text_split_limit_matrix_spec.spl` (new,
14/14) and `nested_string_split_spec.spl` (5/5) pass with
`SIMPLE_LIB=src` on the release/1.0.0 tip: literal and variable limits,
limit 1, zero/negative as unlimited, missing separator, multibyte
content+separator. The MIR boundary fix (`method_calls_literals.spl`
keeps split argument 1 as a raw i64 for `rt_string_split_limit`) is
present in the source. The BugDB row stays OPEN per the gate below:
`--mode=native` on a receipt-admitted pure-Simple CLI is still pending
(next stage-2 binary; tracked with the build-gated verifications).

## Reproducer

`"a:b:c".split(":", 2)` must produce `["a", "b:c"]`. The same call with
the limit held in a variable must behave identically. Adjacent cases cover
limit one, a missing separator, an empty separator, and multibyte text and
delimiters in
`test/01_unit/compiler/interpreter/nested_string_split_spec.spl`.

No receipt-admitted Stage 4 test runner is available in the current worktree.
`bin/release/simple` is a wrapper around the known stale/status-139 deployed
runtime, so this continuation did not reclassify a source inspection or stale
execution as a reproducer PASS.

## Ownership and root cause

Both live Rust interpreter dispatchers already consume the second argument as
an integer and use bounded `splitn` semantics:

- `src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs`
- `src/compiler_rust/compiler/src/interpreter_method/string.rs`

The live pure-Simple interpreter likewise evaluates the second argument with
`val_get_int` in
`src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl`.

The remaining defect was the pure-Simple MIR native boundary. It selected
`rt_string_split_limit(value, separator, limit)` correctly, but passed every
method argument through `ensure_tagged_str`. That converted the numeric limit
to a string handle even though the runtime ABI requires raw `i64`.

## Fix

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` now tags the
separator but preserves split argument index one as its lowered numeric local.
All other text-special arguments retain their prior string tagging. No Rust or
foreign-runtime edit is required because delegation below the pure-Simple
boundary is already correct.

## Regression evidence

The focused SSpec retains the exact literal-limit reproducer and adds:

- a variable numeric limit, preventing another blanket string-tag regression;
- multibyte content with a multibyte separator, preserving the unsplit tail;
- limit one, missing separator, and empty-separator adjacency.

The live chained-call Rust dispatcher also has a direct unit contract for the
exact two-part result and Unicode empty-separator adjacency. The adjacent
macOS/Linux test-helper cfg defect was corrected, after which the focused
dispatcher contract executed successfully:

```sh
cargo test -q -p simple-compiler --lib string_split_honors_limit_and_unicode_empty_separator
# PASS: 1 passed
```

Source convergence is complete. Runtime closure remains pending one focused
interpreter and native run against a fresh receipt-admitted pure-Simple CLI:

```sh
SIMPLE_LIB=src <admitted-simple> test test/01_unit/compiler/interpreter/nested_string_split_spec.spl --mode=interpreter
SIMPLE_LIB=src <admitted-simple> test test/01_unit/compiler/interpreter/nested_string_split_spec.spl --mode=native
```

Do not mark the BugDB row fixed until both modes pass on that admitted binary.

## Knowledge update scope

- Text-split feature and interpreter-text-method layer expert notes now bind
  mixed-signature argument typing and cross-engine parity.
- `doc/07_guide/`: N/A; the public split contract is unchanged.
- Research/architecture/design: N/A; the existing MIR/runtime boundary remains
  authoritative.
- Workflow/SPipe/manual docs: N/A; no workflow or scenario-manual contract
  changed.


---

## 2026-11-10 (p0-hir-verify lane, Windows worktree, seed-smoke) — PURE-SIMPLE FIX RE-CONFIRMED; NEW SEED-JIT DIVERGENCE RECORDED

Lane: `work/p0-hir-verify-20261110` on `origin/release/1.0.0`. Runtime: `bin/simple.exe` Rust
seed v1.0.0-rc.1. Seed-smoke only; no native/self-hosted claim.

### Static re-confirmation of the pure-Simple fix (current source)

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:4604-4629`:
- comment names this bug and records that the fix was "First fixed 2026-08-17, lost in the
  2050c046ee3 mega-SCC refactor, re-applied here";
- `:4623-4624` — `val ts_arg_ready = if (method == "split" and ts_arg_index == 1) or
  method == "repeat": ts_arg_local else: self.ensure_tagged_str(ts_arg_local)` — split's
  limit (and repeat's count) preserved as the lowered numeric local, separator still tagged;
- `:4629` — `case "split": if args.len() == 2: "rt_string_split_limit" else:
  "rt_string_split"`.

### Executable verification (seed-smoke)

- `SIMPLE_LIB=src bin/simple.exe test test/01_unit/compiler/interpreter/nested_string_split_spec.spl
  --mode=interpreter` — **5/5 PASS, exit 0** (two-part literal limit, variable-held limit
  path coverage via the spec's adjacent cases, limit one, missing separator, chars).
- `--mode=native` is NOT native evidence on the seed: the JIT declines the test-runner
  harness module (`_attach_scope_evidence` argument-8 default, `src/app/test_runner_new/main.spl`)
  and silently falls back to interpreter (5/5 PASS but interpreted).
- Pure-Simple MIR-native boundary run (the actual fixed surface) remains pending an admitted
  pure-Simple CLI, per this doc's unblock condition:
  `SIMPLE_LIB=src <admitted-simple> test test/01_unit/compiler/interpreter/nested_string_split_spec.spl --mode=native`
  — BLOCKED-needs-grant.

### New finding: the seed JIT ignores the split limit (Rust-side, out of this row's owner)

Fixture `build/review/fixtures/split_limit_probe.spl` (main() printing len checks for
`"a:b:c".split(":", 2)` literal and variable-held, and `split(":", 1)`):

- `SIMPLE_JIT_STRICT=1 bin/simple.exe run split_limit_probe.spl` -> JIT compiles and runs
  (no fallback, no hard error) and prints `len=3` for ALL three cases: the limit is ignored
  end-to-end under the seed JIT. Interpreter (spec above) honors it: a JIT-vs-interpreter
  divergence on the Rust seed, the documented "JIT+native silently wrong where the
  interpreter is correct" pattern. This does not bear on the pure-Simple fix in
  `method_calls_literals.spl` (the seed never executes it), but it contradicts any assumption
  that all Rust engine surfaces bound the limit; the earlier "both live Rust dispatchers"
  claim covers the interpreters only. `src/compiler_rust` is frozen for sibling P3 lanes, so
  no edit was made there; the seed-JIT owner should pick this up with the probe above as the
  reproducer.

## 2026-11-10 P3 seedfix lane — seed-JIT LIMIT now honored (work/p3-seedfix-20261110)

The "new finding" above (seed JIT ignores the split limit) is FIXED in
src/compiler_rust. Root cause: the cranelift builtin-method tables mapped `split`
unconditionally to `rt_string_split(string, delimiter)`, whose runtime never reads a
limit; a two-arg call's limit was passed but dropped. The runtime already exposes
`rt_string_split_limit(string, delimiter, limit: i64)` with bounded-splitn semantics
matching the interpreter.

Fix: arity-aware dispatch in both cranelift tables (mirroring the existing `substr`
precedent) — `try_compile_builtin_method_call` (closures_structs.rs: "split" if
args.len()==2) and the qualified-call table (calls.rs: "split" if args.len()>=3,
args include the receiver). Commits 989a41515461 (fix) + 1b27c3582d76 (test).

Verified on a fresh build (debug AND release, SIMPLE_JIT_STRICT=1):
`"a:b:c".split(":", 2)` literal and variable-held, and `split(":", 1)` now yield
2/2/1 with tail "b:c" on the JIT (was 3/3/3, tail "b"). 1-arg split still
full-splits; empty-separator limit matches the interpreter; interpreter spec
nested_string_split_spec 5/5 PASS. Regression test:
`cargo test -p simple-compiler --lib shared_method_static_split` (2 passed).
The pure-Simple MIR fix in method_calls_literals.spl is unaffected (the seed never
executes it). Evidence: build/review/p3fix-seedfix-20261110.sdn.

## 2026-11-14 seed JIT re-check (Rust seed only; not an admitted binary)

- The `run`/JIT lane on the 2026-11-06 seed ignored the limit entirely
  (`"a:b:c".split(":", 2)` gave 3 parts) and raised
  `Function 'str.split' not found` for `"abc".split("")`. A seed rebuilt from
  `origin/release/1.0.0` (which carries `989a4151546`, 2026-11-10) honours the
  limit for literal, variable, 1, 0, negative, larger-than-parts and
  missing-separator cases, and the DevHub curl fixture
  (`authority_tail.split("/", 2)[0]`) passes.
- Remaining seed defect, fixed here: `rt_string_split_limit`
  (`src/compiler_rust/runtime/src/value/collections.rs`) split an empty
  separator into single BYTES, so `"é✓日".split("", 2)` panicked
  ("not a char boundary") inside an `extern "C"` fn and aborted the process.
  It now splits on codepoints, matching the interpreter's bounded arm:
  `["é", "✓日"]`. Red/green: runtime test
  `test_string_split_limit_matches_interpreter_bounded_split` (SIGABRT before,
  pass after).
- Still divergent and NOT changed here (owner decision): unbounded
  `"abc".split("")` is `[a, b, c, ""]` in the seed runtime, `["", a, b, c, ""]`
  in the seed interpreter (Rust `str::split`), and `[a, b, c]` in the C runtime
  (`rt_string_chars`). The C runtime's bounded empty-separator arm also splits
  bytes, not codepoints.
- Status unchanged: still waits for the admitted pure-Simple
  interpreter + native run named above.

## 2026-11-25 release/1.0.0 re-verification (lane work/fix-text-split-limit-20261125, Windows)

Lane: `work/fix-text-split-limit-20261125` worktree on `origin/release/1.0.0`
(HEAD 24414a7eba6). Runner: `SIMPLE_LIB=src
/c/dev/wt-warn-3p1/src/compiler_rust/target/release/simple.exe` (Rust seed
rebuilt 2026-11-25, carries the 2026-11-10 JIT fix and the 2026-11-14 runtime
fix). No admitted pure-Simple binary exists in this worktree (`bin/release/`
absent), so the admitted pure-Simple interpreter + native run named above
remains the open closure condition; every surface runnable here is green.

The prevention spec and the short dated note at the top of this doc landed
via PR #11618 (commit 27df861356e) while this entry's evidence was being
collected; this entry adds the surfaces that note does not cover (JIT-strict
probe, fresh cargo unit tests, neighbor and smoke specs, exact line cites).

### Static re-confirmation (current line numbers)

- pure-Simple MIR: `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:5328`
  keeps split argument index 1 as the lowered numeric local (separator still
  tagged), and `:5332` selects `rt_string_split_limit` when `args.len() == 2`;
  the comment at `:5305-5314` names this bug.
- seed cranelift: `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:2775`
  (`"split" if args.len() == 2`) and
  `src/compiler_rust/compiler/src/codegen/instr/calls.rs:4505`
  (`"split" if args.len() >= 3`, receiver-inclusive) both route to
  `rt_string_split_limit`.
- seed runtime: `rt_string_split_limit`
  (`src/compiler_rust/runtime/src/value/collections.rs:6018`): `limit <= 0`
  unbounded, `limit == 1` whole value, bounded empty-separator arm splits
  codepoints.
- seed interpreter: bounded arm at
  `src/compiler_rust/compiler/src/interpreter_method/string.rs:259`;
  pure-Simple interpreter splitn-rejoin arm at
  `src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl:230`.

### New prevention spec

`test/01_unit/compiler/interpreter/text_split_limit_matrix_spec.spl` — 14
examples: literal and variable-held limit 2, limit 1, limit 0, negative limit,
over-count limit, multi-separator remainder, trailing separator (bounded and
over-count), missing separator, empty string, multibyte separator, multibyte
text with a bounded empty separator, and an empty separator at exactly the
character count. Over-count empty-separator cases are deliberately not pinned:
that arm is the documented cross-engine divergence above.

- interpreter mode: **14/14 PASS** (exit 0).
- `--mode=native`: PASS but degraded — the seed test-runner falls back to the
  interpreter (no MC/DC probes), so this is not native evidence.
- JIT evidence instead: `SIMPLE_JIT_STRICT=1 SIMPLE_LIB=src <seed> run
  build/review/fixtures/split_limit_matrix_probe.spl` prints len=2/2/1/3 for
  literal/variable/one/zero limits and correct unicode, trailing-separator,
  and empty-string rows under the JIT (strict mode refuses fallback).

### Rust-side unit tests (fresh cargo build of this worktree)

- `cargo test -p simple-runtime --lib test_string_split_limit_matches_interpreter_bounded_split`
  — 1 passed.
- `cargo test -p simple-compiler --lib shared_method_static_split` — 2 passed
  (`shared_method_static_split`, `shared_method_static_split_with_limit`,
  both cranelift).
- `cargo test -p simple-compiler --lib string_split_honors_limit` — 1 passed
  (`string_split_honors_limit_and_unicode_empty_separator`).

### Neighbor and smoke specs (same runner, interpreter mode)

- `nested_string_split_spec.spl` 5/5, `text_byte_at_dispatch_spec.spl` 5/5,
  `text_trim_dispatch_spec.spl` 5/5, `string_interpolation_spec.spl` 3/3,
  `representation_boundary_autofix_spec.spl` 16/16 (the file now declares 16
  examples; still fully green).

Status: unchanged — `fix-implemented-verification-pending`. The admitted
pure-Simple interpreter + native run remains the close-out condition.
`bug_db.sdn` was not hand-edited (integrity-sealed; update via
`bin/simple bug-add` once an admitted binary exists).
