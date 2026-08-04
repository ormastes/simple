# A `T?` value bound to a `bool` parameter is neither presence-coerced nor rejected — it arrives as the raw payload (2026-08-04)

**Status:** OPEN
**Found:** 2026-08-04
**Related — SAME root cause, found independently by parallel lanes the same day.
Fix once, close all four:**
- `bool_typed_parameter_accepts_non_bool_and_jit_corrupts_it_2026-08-04.md`
  (unit tier — 28 specs in `test/01_unit/std/`; also records the JIT re-tagging
  half and a prior session that papered over two specs by editing the test)
- `exists_check_contract_reddens_46_app_branch_coverage_specs_2026-08-04.md`
  (app tier — 46 specs / 138 examples)
- `exists_check_on_optional_i64_returns_payload_2026-08-01.md` (earlier lane)

**This file is the SYSTEM-tier census** (`test/03_system/**`, `test/system/**`):
the corpus-wide count and the exact per-directory attribution below are the part
the sibling reports do not have.
**Class:** silent wrong answer + missing type check. **The single largest
failure cluster in the whole system-test corpus.** `verify(<expr>.?)` appears
**2,174 times across 1,676 spec files** — 1,087 occurrences in 838 files of
`test/03_system/`, and the identical 1,087/838 in the duplicate legacy tree
`test/system/`:

| directory (per tree) | spec files carrying the idiom |
|----------------------|-------------------------------|
| `infrastructure/batch` (`test/system/batch`) | 500 |
| `core/error_path` | 100 |
| `stdlib` (`stdlib_comprehensive_*`) | 50 |
| `core/edge_case` | 50 |
| `compiler/runtime_comprehensive` | 50 |
| `compiler/comprehensive` | 50 |
| everything else | 38 |

Measured impact where the tier was actually run:
`test/03_system/core` — **249 of 249** failing examples are this defect (all 150
failing files carry the idiom; 100 files x 1 + 1 x 2 + 49 x 3 = 249, an exact
match). `test/03_system/stdlib` — 51 of 63. `test/03_system/compiler` — 50 of
the `comprehensive/*` failures.

> **RESOLVED 2026-08-04 by direct measurement. The count of 249 is CORRECT; the
> attribution "all 249 are this defect" is NOT.** An intermediate note withdrew
> the 249 as an artifact of the `code 127` failure mode (a bare worktree has no
> `bin/simple`, so directory runs fail per-file and the total equals the FILE
> count). That artifact is real and worth knowing, but it is **not** what
> produced this number. A controlled A/B over the whole tier found exactly 249
> failing examples in the OLD arm. See "MEASURED — `test/03_system/core`" below
> for the split: **149** are this defect, **100** are a different spec bug.
> The `stdlib` (51 of 63) and `compiler` (50) figures above remain unverified.

## MEASURED — `test/03_system/core` (2026-08-04, pin `851a0e8d82e`)

Whole tier, both arms, all 5,573 examples executed (`passed + failed` equalled
the static example count in every cell; `code 127` was 0 in all 16 runs).

| subdirectory | files | examples | fail OLD | fail NEW | delta |
|---|---|---|---|---|---|
| `edge_case` | 50 | 1,400 | **149** | **0** | **−149** |
| `error_path` | 100 | 3,000 | 100 | 100 | 0 |
| `compatibility` | 25 | 375 | 0 | 0 | 0 |
| `exploratory` | 25 | 375 | 0 | 0 | 0 |
| `regression` | 25 | 375 | 0 | 0 | 0 |
| `resilience` | 2 | 33 | 0 | 0 | 0 |
| top-level specs | 2 | 15 | 0 | 0 | 0 |
| **total** | **229** | **5,573** | **249** | **100** | **−149** |

The 149 decomposes exactly as `50 nested.? + 49 opt2.? + 50 d.get("a").?`,
matching the site counts. The prediction that the four subdirectories with no
`.?` sites would show no delta held.

**The 100 `error_path` failures are NOT this defect** — they are a genuine spec
bug, one per file: `verify(Some(nil).?)`. OLD reports `expected nil to equal
true`, NEW reports `expected false to equal true`. The fix changes the message,
not the verdict, and correctly so: `Some(nil)` is present-but-nil, and the spec
asserts it is `true`. **The spec is wrong, not the compiler.**

Arm identity established behaviorally, not by label: OLD = the same tree with
`return None;` as the first statement of `present_value_as_bool_arg`; md5 NEW
`bcbb7c53…` vs OLD `f0dfee65…`; isolated probes via `bin/simple run` gave
`verify(Some(Some(Some(10))).?)` → OLD `expected Option::Some(10) to equal true`,
NEW passes, and `verify(d.get("a").?)` → OLD `expected 1 to equal true`, NEW
passes.

### `1 == true` is runner-dependent

The masking effect documented below for `test/01_unit/std` — where `Some(1).?`
passes because payload `1` compares equal to `true` — **does not hold in this
tier**. Here `d.get("a").?` yields `1` and OLD fails it with `expected 1 to equal
true`. The difference is the runner: this measurement required
`SIMPLE_TEST_RUNNER_RUST=1`. So the loose comparison is a property of the
**pure-Simple** matcher, not of the language. Treat any `.?`-site census as
runner-specific.

### Deviation: the pure-Simple runner cannot run this tier at this pin

With the default runner, **both** arms died before executing any spec:

```
error: semantic: type MirToLlvm implements method translate_block_at from trait
MirTextCodegen with 7 parameter(s), but the trait declares 5
```

Zero examples, no `Results:` line. That — not host load — is the likeliest cause
of the earlier failed attempt to measure this tier. Filed separately as
`pure_simple_runner_blocked_by_trait_arity_mismatch_2026-08-04.md`. The Rust
runner is the correct instrument for a Rust-side change, but note that stdlib
`.spl` behavior is **not** exercised by it.

## MEASURED delta (2026-08-04, pinned worktrees at `b0f305f1ae6`)

The first properly-controlled A/B. Arms established **behaviorally**, not by
label: OLD has 0 occurrences of `present_value_as_bool_arg`, NEW has 3, the two
binaries differ by md5, and every reported run has `code 127 == 0`.

| cluster | files | examples | fail OLD | fail NEW | delta |
|---|---|---|---|---|---|
| `test/01_unit/std` `auto_comprehensive_*` (+3 `deep` samples) | 33 | 1029 | 28 | **0** | −28 |
| `test/01_unit/app/branch_coverage_*` | 25 | 1950 | 72 | **0** | −72 |

**100 examples closed, and every failure in both OLD arms was this defect** —
nothing else regressed or remained. Failure text, captured from a single-spec
run: `expected 42 to equal true` (`auto_comprehensive_10_spec.spl`).

### The idiom census overstates the blast radius by ~an order of magnitude

`check(<expr>.?)` against a `bool`-typed parameter appears in **660** files under
`test/01_unit/std` alone — yet the `deep/` (200) and `improved/` (432) families
are **green on OLD**. This is not vacuity: sabotaging one `check(true)` to
`check(false)` in `deep/array_deep_10_spec.spl` turned it red (`43 total, 42
passed, 1 failed`), so those specs do assert.

They pass because they use `check(Some(1).?)`. The unwrapped payload `1`
**compares equal to `true`**, so the assertion succeeds by accident. The red
specs are the ones whose payload is anything else — `Some(42)`, `Some(Some(10))`,
`d.get("key")`.

**Consequence: site counts must not be converted into failure counts.** Any
estimate of this defect's reach derived from grepping `.?` is wrong by the
fraction of sites whose payload happens to be `1`. The earlier corpus-wide
figure of ~1,200 was exactly such an extrapolation and is withdrawn.

(That `1 == true` succeeds at all is a separate latent defect — it silently
converts a real type error into a passing assertion. Filed separately as
`int_payload_compares_equal_to_bool_true_2026-08-04.md`.)

### The legacy `test/system/**` figure double-counts a mirror

At the pinned commit, blob-hash comparison (path-independent — path-relative
diffing misses the rename) shows:

- **all 838** idiom-carrying files in `test/system/` have byte-identical twins in
  `test/03_system/`. There is **zero unique legacy idiom source**;
- 3,221 of 3,424 `test/system/` files (94%) are byte-duplicates;
- `test/system/batch` (1,000 files) mirrors `test/03_system/infrastructure/batch`,
  not a same-named path;
- the 838 files collapse to **44 unique blobs** — `test/system/batch`'s 500 spec
  files are **2 distinct source texts**, 250 copies each, one `verify(opt.?)`
  site apiece. True occurrence count is **937**, not 1,087.

Measured there: batch blob A (covering 250 files) went `10 examples, 1 failure`
→ `10 examples, 0 failures`. So 500 failures close in that tree and 500 more in
its mirror — from fixing **two source lines once**. Six blob pairs remain
unmeasured and are not extrapolated.

Note also that the `edge_case` blobs use `verify(not d.get("c").?)`, which yields
a genuine bool and passes in **both** arms — a further reason occurrence counts
overstate failures.

### Measurement trap: `bin/simple` silently collapses the A/B

`simple test` **resolves through `bin/simple` when it exists**, even when a
different binary is invoked by absolute path. Planting an OLD copy at
`bin/simple` flipped a NEW-arm run from `0 failures` to `1 failure` with the OLD
defect text, with the NEW binary's md5 and mtime unchanged; removing it restored
`0`. **Absolute paths alone do not isolate the arms** — `bin/simple` must point
at the arm under test and be re-pointed when arms switch.

The `01_unit` numbers above were audited against this after the fact and are
sound: the symlink was re-pointed between arms and verified at each point
(`readlink` plus a symbol count), the two app arms ran in separate worktrees with
their own symlinks, and the single-spec probes ran with **no `bin/simple` on disk
at all** — immune to the mechanism — yet still diverged 1 → 0 on the same spec
whose family measured 28 → 0. A collapsed arm forces both sides to one binary,
which cannot produce 72-vs-0 and 28-vs-0.

### Not measured
- legacy duplicates `test/unit/std`, `test/unit/app` (byte-identical but for 4
  files; 69 + 29 idiom sites) — the reports' "138" adds these to the 72 above;
- `test/01_unit/app/interpreter/refc_binary_spec.spl` (4 sites),
  `mcp_unit/prompts_spec.spl` (16 sites);
- the remaining 629 `deep`/`improved` std files (3 sampled, all green on OLD).

Binary under test: `bin/release/x86_64-unknown-linux-gnu/simple` (on this tree
that is the **Rust seed** — `bin/simple --version` prints the seed banner).
`bin/simple test` executes specs on the interpreter.

## Symptom

Minimal repro — a `bool`-declared parameter receiving a `T?`:

```
fn takes_bool(b: bool) -> text:
    if b:
        return "TRUE"
    return "FALSE"

fn main():
    val o = Some(99)
    print "o.?          = {o.?}"           # 99      (correct: `.?` returns T?)
    print "takes_bool(o.?) = {takes_bool(o.?)}"
```

Actual (interpreter): `takes_bool` receives the **raw payload `99`**, not
`true`. No diagnostic is emitted at any stage — not at parse, not at
resolve/semantics, not at the call site.

Where this bites, verbatim from the failing specs (each declares its own
`fn verify(condition: bool): expect(condition).to_equal(true)`):

| spec | expression | reported failure |
|------|-----------|------------------|
| `core/edge_case/edge_case_11_system_spec.spl:41` | `verify(opt2.?)` where `opt2 = Some(42)` | `expected 42 to equal true` |
| `core/edge_case/edge_case_11_system_spec.spl:79` | `verify(nested.?)` where `nested = Some(Some(Some(10)))` | `expected Option::Some(10) to equal true` |
| `core/edge_case/edge_case_11_system_spec.spl:157` | `verify(d.get("a").?)` | `expected 1 to equal true` |
| `core/error_path/error_path_100_system_spec.spl:182` | `verify(opt.?)` where `opt = Some(nil)` | `expected nil to equal true` |
| `stdlib/stdlib_comprehensive_1_system_spec.spl:96` | `verify(result.?)` | `expected 99 to equal true` |

Note the control case in the same block passes:
`verify(not d.get("c").?)` is fine, because `not` forces a real `bool`.

## Root cause (what is PROVEN)

1. **`.?` is behaving to contract, and must not change.**
   `doc/07_guide/quick_reference/syntax_quick_reference.md:505` — "Existence
   Check (`.?`) — Returns `T?`". The pure-Simple lowering
   (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:2895-2902`) carries
   an explicit comment forbidding the collapse to a bare `rt_is_some` bool,
   citing the native-smoke-matrix "(14) Option/nil check (x.?)" regression where
   `if val v = x.?: return v` returned `1` instead of the payload. So the fix is
   NOT "make `.?` return bool".

2. **The gap is at argument binding.** The interpreter's parameter coercion hook
   is `coerce_param` in
   `src/compiler_rust/compiler/src/interpreter_call/core/arg_binding.rs:84`
   (a second copy at `:394`). It already performs two coercions:
   unsigned-width masking for `u8..u64` params (`:86-111`), and
   `Some(x) -> x` unwrapping when the target param is a concrete non-Optional
   type (`:112-131`). There is **no arm for a `bool`-declared parameter**, so a
   `T?` (or its already-unwrapped payload) falls through
   `copy_value_type_parameter` at `:132` untouched.

3. **The type checker does not reject it either.** No diagnostic is produced for
   `takes_bool(o.?)` at any stage, so the mismatch is invisible until an
   assertion downstream compares the payload against `true`. Silently accepting
   AND silently mis-binding is the actual defect: one of the two behaviours has
   to be chosen.

4. **The documented truthiness contract says the coercion should be
   presence-based.** `syntax_quick_reference.md:620` and `:626` define
   `opt.is_none()` as `not opt.?` and `list.is_empty()` as `not list.?`. Both
   identities only hold if a `T?` in a boolean position collapses to
   present/absent. Under that rule every failing example above is asserting
   something true.

## Blast radius beyond the spec tier

This is not test-only. Any product call `f(b: bool)` fed a `T?` — e.g. from a
`-> T?` helper or a `.?` — currently passes the payload. Under the interpreter
a nil payload happens to read falsy, so the wrong value is often masked; under
the JIT it does not (see the sibling bug
`jit_if_nil_takes_true_branch_2026-08-04.md`, where a nil bound to a `bool`
parameter takes the TRUE branch). The two bugs compound: the payload leaks in,
and then the branch test on it is also wrong.

## Why not fixed now

The fix site is inside the **Rust seed** (`arg_binding.rs`, two `coerce_param`
copies), which this repo's standing rule reserves for bootstrap and which needs
a `--full-bootstrap` cargo rebuild to take effect — a rebuild that would swap
the shared `bin/simple` out from under the parallel sessions live in this tree.

More importantly the change is a **language-semantics decision, not a local
patch**: adding "presence-coerce into a `bool` param" also has to answer what
happens for the other non-bool values at the same binding site (`0`, `""`, empty
collections, a plain `Int`), or it will silently accept `takes_bool(42)` as
`true` and convert today's loud wrong answer into a permanent quiet one. The
same table then has to be applied identically in the pure-Simple interpreter,
the Cranelift JIT and native codegen, or it just moves the divergence.

Recommended shape of the real fix, in order of preference:
1. Emit a semantic error when a non-`bool` static type is bound to a `bool`
   parameter, **except** for `T?`, which presence-coerces. This keeps
   `verify(x.?)` working (as the docs promise) and makes `takes_bool(42)` the
   compile error it should always have been.
2. Apply it in ONE shared place per engine, alongside the existing
   `Some(x) -> x` unwrap, so the three engines cannot drift.

---

# CORRECTION 2026-08-04 (later the same day) — coercion FIXED; the failure attribution above is WRONG

## The coercion half is fixed

`present_value_as_bool_arg()` in
`src/compiler_rust/compiler/src/interpreter_call/core/arg_binding.rs` now
coerces a non-`bool` argument landing on a `bool` parameter to a PRESENCE bool:
`Value::Nil -> false`, a real `Value::Bool` passes through untouched, any other
present value `-> true`. It is called from BOTH `coerce_param` closures
(`bind_args_with_injected` and `bind_args_with_values`) — there are two, and
fixing only one would have left the sibling broken.

**Correction to this report's own mechanism section.** The argument never
arrives as an `Option`. `Expr::ExistsCheck` (`interpreter/expr.rs:503`) unwraps
Some/Ok, decides presence (nil, and empty array/dict/str, are absent), then
returns the **bare payload** or `Value::Nil`. So the value hitting the binder is
e.g. `Value::Int(42)`, and a first fix that pattern-matched on
`Value::Enum{Option}` did nothing at all. `.?` returning the payload is CORRECT
per `doc/07_guide/quick_reference/syntax_quick_reference.md` ("Existence Check
(`.?`) — Returns `T?`"), which is why the coercion belongs at the parameter
boundary and not in `.?`.

Measured before/after on the same command, `SIMPLE_EXECUTION_MODE=interpret`:

| expression bound to `condition: bool` | before | after |
|---|---|---|
| `Some(0).?` | **false** | **true** |
| `Some(42).?`, `Some(Some(Some(10))).?`, `d.get("a").?` | true | true |
| `nil.?` | false | false |
| plain `true` / `false`, `1 == 1`, `1 == 2` | unchanged | unchanged |

Only the present-but-falsy-payload row moves. Presence is the correct answer:
`verify(d.get(k).?)` on a stored `0` asks whether the key is present.

## The failure attribution in this report does NOT reproduce

This report claims `test/03_system/core` — **249 of 249** failing examples are
this defect, and ~1,200 corpus-wide. That is not reproducible on this tree:

- The cited repro `core/edge_case/edge_case_11_system_spec.spl:41`
  (`verify(opt2.?)`, "expected 42 to equal true") **passes 28/28 run alone on
  the UNMODIFIED binary**.
- `test/03_system/core/edge_case`: **1400 total, 149 failed BEFORE the fix and
  149 failed AFTER** — bit-identical.
- `test/03_system/stdlib`: **1503 total, 63 failed before and 63 after.**
- The `edge_case` failures contain **zero `expected ... to equal ...` lines**.
  Every one is `Error: Process exited with code N`.

The attribution appears to have been derived by grepping failing files for the
`verify(x.?)` idiom, not by confirming the idiom caused the failure. The idiom
count (2,174 sites / 1,676 files) is real; the causal link to the failures is
not established.

## What those failures actually are — a DIFFERENT defect

`edge_case_11_system_spec.spl` reports **25 passed / 3 failed inside a directory
run** but **28 passed / 0 failed run alone**, same binary, same flags. The
failures are context-dependent across specs in one run and surface as
`Process exited with code N`, not as assertion mismatches. Filed separately as
`directory_run_context_makes_specs_fail_that_pass_alone_2026-08-04.md`. Anyone
attributing system-tier failure counts should measure per-spec first — this
artifact inflates directory-run counts by an unknown amount.

## Regression evidence

2,903 examples across the two directories above show zero drift beyond the
intended row. This is a correctness fix, not a failure-count fix.

**Deployment note:** Rust seed code. Built clean, but the deployed
`bin/release/<triple>/simple` keeps the old behaviour until the next redeploy.

---

# RETRACTION 2026-08-04 — the CORRECTION above was WRONG. The original report was RIGHT.

The section above claimed the failure attribution "does not reproduce" and that
the fix moved nothing. **That claim was itself measured wrong, and is retracted.**

## What actually happens, measured in a PINNED worktree

The repository working copy is mutated continuously by parallel sessions, and
`bin/simple test` **interprets `src/lib/**` and the spec library from source**.
So the same spec, same command, same binary returns different verdicts minutes
apart depending on which lineage the working copy happens to be on. Every
measurement in the retracted section was taken in that unstable tree.

Re-measured in a detached worktree pinned to a fixed commit (`14b0b036363`),
which no other session can move:

| binary | `edge_case_11_system_spec.spl` |
|---|---|
| deployed `bin/release/x86_64-unknown-linux-gnu/simple` (no fix) | 28 total, 25 passed, **3 failed** |
| rebuilt seed with `present_value_as_bool_arg` | 28 total, **28 passed, 0 failed** |

The three failures are exactly the ones this report named:

```
✗ null/nil propagation       expected 42 to equal true
✗ nested option unwrapping   expected Option::Some(10) to equal true
✗ dict with missing keys     expected 1 to equal true
```

i.e. `verify(opt2.?)`, `verify(nested.?)`, `verify(d.get("a").?)`. The fix closes
all three. Instrumenting the helper confirmed it fires with
`ty=Some(Simple("bool"))` on this path.

**So: the root cause in the original report is correct, the repro is correct,
and the fix resolves it.** Only the corpus-wide count (~1,200) remains
unverified — that is an extrapolation from the idiom census, not a measurement,
and it should be re-derived per-directory in a pinned tree before being quoted.

## Why the retracted section went wrong — three compounding errors

1. **Unstable tree.** Measurements were taken in a working copy that other
   sessions were rewriting mid-run; `src/lib` is interpreted, so this changes
   results without changing the binary or the spec.
2. **A binary that silently lost the fix.** A jj lineage move reverted
   `arg_binding.rs` in the working copy; a later rebuild produced a binary with
   NO fix that was still labelled "NEW (with fix)". The A/B was fix-vs-fix, then
   nofix-vs-nofix — never a true before/after.
3. **A vacuous control spec.** The synthetic spec used to "verify" the fix
   omitted `use std.spec`, so its `expect` never asserted and it reported 6/6
   green regardless. Any spec written to validate a matcher-level change MUST
   `use std.spec` and MUST be shown to fail before the fix.

## Mandatory procedure for anyone re-measuring this

```bash
git worktree add --detach /tmp/pinned $(git ls-remote origin main | cut -f1)
cd /tmp/pinned
SIMPLE_TIMEOUT_SECONDS=0 /abs/path/to/simple test --no-cache --no-cover-check <spec>
```

Pin the tree, use absolute binary paths, and verify the binary actually contains
the change (`grep` the symbol in the source it was built from) before labelling
either arm.
