# @noalloc annotation coverage — measured 2026-08-08

Status: **the WP-12a plan row is STALE.** The apparatus is NOT vacuous.

## Headline finding

`doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md` WP-12a records:

> "**zero functions in the tree carry `@noalloc`**, so there is nothing for it to
> check even if it worked"

That was false at the time of this measurement. **19 real function annotations
already existed**, and the audit driver already saw all 19 and ran a real check
over them. The `@noalloc` apparatus is live, not decorative. The plan row should
be corrected rather than used as justification for further work on the premise
that nothing is annotated.

Note the checker's own source already contradicted the plan row —
`src/compiler/35.semantics/noalloc_checker.spl:434` refers to "the 19 real
`@noalloc` functions landed in WP-12a".

## Measurement — exclusions stated

Tool: `/usr/bin/grep -rn` (NOT the shell's `grep`, which is a ugrep wrapper
honouring `.gitignore` and under-reports).

Roots scanned: `src doc test scripts`, filtered to
`--include=*.spl --include=*.md --include=*.rs --include=*.shs`.

Excluded: `src/compiler_rust/vendor/**`, `src/runtime/vendor/**`, `build/**`,
`.claude/worktrees/**` (the latter two are outside the scanned roots by
construction, so they cannot inflate the count).

### Total occurrences: 153 (BEFORE)

Breakdown of the 153 by kind:

| kind | count | where |
|---|---|---|
| **real function annotations** | **19** | `src/lib/nogc_async_mut_noalloc/{math,hash,string}/mod.spl` only |
| checker/driver source + prose | 39 | `noalloc_checker.spl` (21), `noalloc_manifest_scan.spl` (14), `gc_boundary_check.spl` (2), `allocator_symbol_scan.spl` (1), `effect_verifier.spl` (1) |
| test/spec files | 28 | `test/01_unit/...` (15), `test/03_system/...` (10), `test/unit/...` (6, one dir is a duplicate tree) |
| documentation / bug docs | 65 | `doc/08_tracking/bug/*` (37), `doc/03_plan/*` (10), reports/research/design (18) |
| build-script prose | 2 | `scripts/audit/noalloc_manifest_scan.spl` (print strings) |

Every hit outside `src/lib/nogc_async_mut_noalloc/**` was verified by reading the
matched line to be prose, a print string, or a test fixture — **not one real
annotation lives outside the noalloc tier**.

The 19 real annotations, per module:

- `src/lib/nogc_async_mut_noalloc/math/mod.spl` — 8
- `src/lib/nogc_async_mut_noalloc/string/mod.spl` — 7 (an 8th `@noalloc` hit in
  that file is the comment `# NOT @noalloc: string interpolation ...` at :132 —
  a deliberate negative marker, correctly not counted)
- `src/lib/nogc_async_mut_noalloc/hash/mod.spl` — 4

### AFTER this change: 162 occurrences / **28 real function annotations**

## Verbatim evidence

All runs: `SIMPLE_EXECUTION_MODE=interpret timeout 600 bin/simple run
src/compiler/90.tools/verify/noalloc_manifest_scan.spl`, output filtered to the
verdict and `error[noalloc]` lines. No bootstrap build was triggered.

### BEFORE

```
noalloc manifest scan: 19 @noalloc fn(s) checked, 0 violations
RC=0
```

### SABOTAGE of a PRE-EXISTING annotation (`bm_abs` in `math/mod.spl`)

Inserted `val leak = new Sabotage()` into the body of the already-`@noalloc`
`bm_abs`:

```
error[noalloc]: in @noalloc fn 'bm_abs': direct-alloc — heap allocation via 'new'
error[noalloc]: in @noalloc fn 'bm_abs': transitive-call — call to allocating function 'bm_abs'
error[noalloc]: in @noalloc fn 'bm_abs': transitive-call — call to allocating function 'bm_abs'
error[noalloc]: in @noalloc fn 'bm_abs': transitive-call — call to allocating function 'bm_abs'
error[noalloc]: in @noalloc fn 'bm_abs': transitive-call — call to allocating function 'bm_abs'
error[noalloc]: in @noalloc fn 'bm_gcd': transitive-call — call to allocating function 'bm_abs'
error[noalloc]: in @noalloc fn 'bm_gcd': transitive-call — call to allocating function 'bm_abs'
error[noalloc]: in @noalloc fn 'bm_lcm': transitive-call — call to allocating function 'bm_abs'
RC=1
```

This is the load-bearing result: the checker flags the direct allocation **and**
propagates it transitively to `bm_gcd`/`bm_lcm`, which really do call `bm_abs`.
Exit code flips to 1, so the driver is usable as a gate.

(The duplicated `bm_abs`→`bm_abs` rows are the text scanner's known
docstring/`Example:` false-positive behaviour, documented in the driver's own
header — they are noise on top of a correct verdict, not the verdict itself.)

### Reverted — clean again

```
noalloc manifest scan: 19 @noalloc fn(s) checked, 0 violations
RC=0
```

### AFTER adding the 9-function pilot set

```
noalloc manifest scan: 28 @noalloc fn(s) checked, 0 violations
RC=0
```

Count rose 19 → 28, i.e. the driver sees every newly annotated function, and all
nine pass clean.

### SABOTAGE of a NEWLY-added annotation (`pmp_napot_addr`)

Inserted `val leak = new PmpRegion()`:

```
error[noalloc]: in @noalloc fn 'pmp_napot_addr': direct-alloc — heap allocation via 'new'
RC=1
```

### Reverted — clean again

```
noalloc manifest scan: 28 @noalloc fn(s) checked, 0 violations
RC=0
```

## Pilot set — 9 functions, each read end-to-end before annotating

### `src/lib/nogc_async_mut_noalloc/baremetal/riscv_common/xlen.spl` (5)

| function | justification |
|---|---|
| `XlenConfig.is_rv32` | single field read `self.xlen` compared to an `i64` module constant; returns `bool`. No call, no literal, no interpolation. |
| `XlenConfig.is_rv64` | identical shape to `is_rv32`. |
| `XlenConfig.truncate` | one field read and a bitwise `&` against an integer literal; both branches return an `i64`. |
| `XlenConfig.sign_extend_32` | pure bitwise `&`/`|` on `i64` against integer literals, guarded by field-read comparisons. |
| `XlenConfig.sign_extend_imm` | shifts/or on `i64` locals, then calls **only** `self.truncate`, which is itself in this pilot set and proven alloc-free. This is the one pilot member with a callee, chosen deliberately so the transitive path is exercised positively — the driver registers it and reports clean. |

### `src/lib/nogc_async_mut_noalloc/baremetal/riscv_common/pmp.spl` (4)

| function | justification |
|---|---|
| `pmp_napot_addr` | single expression, shifts and an `or` on `u64` params. No call. |
| `pmp_addr_csr` | `CSR_PMPADDR0 + index` — one constant read plus integer add. |
| `pmp_cfg_csr` | `if`-expression yielding an int literal, then integer divide and add. No call. |
| `pmp_cfg_value` | `if`-expression yielding an int literal, `%`, and a shift on `u64`. No call. |

### Explicitly NOT annotated, after reading

- `pmp.spl::pmp_write_plan`, `pmp_regions_from_sandbox_lowering`,
  `pmp_write_plan_from_sandbox_lowering` — array literals and `.push()`; these
  allocate.
- `pmp.spl::pmp_config_byte`, `pmp_parse_u64` — call `text.contains` /
  `parse_int`; not proven allocation-free from source alone.
- `csr_defs.spl::csr_name` — returns `"csr_{addr}"`, a string interpolation.
  This is a genuine allocator and a good future negative test.
- `XlenConfig.rv32` / `rv64` — struct construction; `InitOnly` at best, not `None`.

## Preconditions verified before annotating

`@noalloc` was, until 2026-08-08, unregistered in any parser: the Rust seed
interpreter treated it as a Python-style runtime decorator and modules carrying
it failed to LOAD with `error: semantic: variable noalloc not found` (see
`src/lib/hash.spl:16-34` and
`doc/08_tracking/bug/noalloc_decorator_unbound_in_seed_interpreter_2026-08-08.md`).
Annotating a new module while that was live would have poisoned every consumer.

That was checked, not assumed. A probe importing both an already-annotated
module and a newly-annotated one loads clean under `SIMPLE_EXECUTION_MODE=interpret`:

```
xlen32=32 abs=5
```

so the seed in `bin/simple` already carries the decorator skip-list fix. Note
`SIMPLE_EXECUTION_MODE=interpreter` is **not** a valid mode string — only
`interpret` selects the interpreter; anything else silently runs JIT. Both were
run here and both load clean.

## Honest limits of the current gate

The apparatus works, but it is weaker than "verified allocation-free":

1. **It is a text scanner, not an AST/HIR pass.** Direct-alloc detection
   recognises exactly two forms from source text: ` new ` and a `{` inside a
   quoted literal. Array literals, dict literals and string concatenation are
   deliberately not detected, because `[` and `{` are too ambiguous in raw text.
   A pilot function that allocated via `[1,2,3]` would pass.
2. **Callee extraction cannot tell a call from prose.** `_extract_callees` pulls
   identifiers followed by `(` out of docstrings too, which is where the
   duplicated `bm_abs` rows above come from.
3. **The manifest is keyed by bare function name**, so two same-named functions
   in different modules collide.
4. **`Unknown` is not rejected by this gate.** A callee the manifest never saw
   passes. The honest reject-Unknown behaviour lives in the separate, opt-in
   `check_steady_state_gate`, which no driver currently runs.
5. **The compiler does not enforce `@noalloc` during a real build.** Only this
   standalone driver checks it. Annotations are documentation plus a lint, not a
   compile-time guarantee, despite the checker header's claim that it "emits hard
   errors ... so @noalloc is a compile-time guarantee".

## What full rollout would require

1. **Correct the WP-12a plan row** — it asserts zero annotations; there were 19.
2. **Wire the driver into CI as a gate.** It already exits 1 on violation. It is
   a `scripts/check/`-shaped fence, not a spec (a spec cannot import compiler
   modules).
3. **Replace text scanning with a real HIR pass** before annotating broadly.
   Limits 1–3 above all dissolve once `alloc_inference` runs over real HIR, and
   only then does an annotation mean what the checker header claims.
4. **Fix the docstring false-positive** in `_extract_callees` (skip lines inside
   `"""` blocks) — cheap, and removes the noise that currently makes real output
   hard to read.
5. **Qualify manifest keys by module path** to remove same-name collisions.
6. **Then** expand coverage tier-wide, module by module, each function read.
   Natural next targets by inspection: `collections/fixed_*.spl`,
   `baremetal/riscv_common/{alu,registers,decode}.spl`, `baremetal/x86/io.spl`.
7. **Land the `std.hash` / `std.string` re-export unblock** now that the
   decorator fix is deployed (`src/lib/hash.spl:27-33`).

## Files changed

- `src/lib/nogc_async_mut_noalloc/baremetal/riscv_common/xlen.spl` — 5 annotations
- `src/lib/nogc_async_mut_noalloc/baremetal/riscv_common/pmp.spl` — 4 annotations
- `doc/08_tracking/bug/noalloc_annotation_coverage_2026-08-08.md` — this file

`math/mod.spl` was sabotaged and reverted; it is byte-identical to its original
state, confirmed by the restored 19/28-clean runs above.
