# Stale deployed binaries reject current-language source — sspec-maintain scorer unrunnable on this Mac

Date: 2026-09-05. Found while trying to run `sspec-maintain scan` (modern sspec
documentization score) for the all-specs-to-80 goal.

## Symptom

Every binary available on this host failed before the scorer could run:

| Binary | Date | Failure |
|---|---|---|
| `bin/simple` → `bin/release/aarch64-apple-darwin-macho/simple` (bootstrap CLI, `simple-bootstrap 1.0.0-beta`) | stale | parse error: `val x = unsafe(...):` block-expr in `src/lib/nogc_sync_mut/io/file_ops.spl:134` — "unexpected token in expression: `:`" |
| `bin/release/aarch64-apple-darwin-macho/simple_seed` (Rust seed) | **Jul 25 13:12** | parse error: unparenthesized multi-line boolean chain — "Unexpected token: expected expression, found Indent" (first hit `src/lib/common/perf/execution_metrics.spl:365`, then `src/app/sspec_maintain/source_facts.spl`) |
| `bin/release/aarch64-apple-darwin/simple` (also a seed build) | Jul 25 14:15 | same class |
| `bin/local/phase2-aarch64-apple-darwin/simple` (`simple-bootstrap 1.0.0-rc.1`, built today by a parallel lane) | Sep 5 11:51 | parses current source, but AOT `compile error ... <invalid-heap>` on a hello world + HIR `unresolved type: Id` on generic struct params — WIP/broken lane binary, not usable |
| `.bak-2026-07-25-cli` backups | Jul 25 | also seed builds with the same parser staleness |

## Root cause

**Not a parser-logic defect.** Both toolchains' SOURCE already accept the
"offending" constructs:

- Unparenthesized multi-line boolean chains: fixed 2026-08-04/08-11 in the
  seed parser (guarded by `src/compiler_rust/parser/src/rejoined_continuation_test.rs`
  — `rejoined_nested_continuation_parses`, `observation_matches_shape_parses`).
  The pure-Simple compiler accepts them too (current `src/**` relies on them
  throughout, e.g. `execution_metrics.spl`).
- The deployed binaries simply predate the fixes: seed built **Jul 25**, six
  weeks of language evolution ago. `@always_inline` (landed Aug 26) and the
  `unsafe(...)` block expression likewise postdate them.

Secondary aggravator: this Mac's disk was 100% full (301 MiB free), which
surfaced as `ENOSPC` on tool outputs before anything else. Freed 60+ GiB by
removing 15 stale `/tmp` and `~/Library/Caches/simple/worktrees` git worktrees
(from Sep 3-4 lanes).

## Fix

Rebuild the seed from current source (running at time of writing):
`cd src/compiler_rust && cargo build --profile bootstrap -p simple-driver -p simple-native-all`.
Longer term: the sanctioned redeploy (`scripts/bootstrap/bootstrap-from-scratch.sh
--pure-simple --deploy`) so `bin/simple` is a current self-hosted binary — the
beta-era bootstrap binary currently pointed at `bin/simple` cannot parse the
current stdlib at all.

## Directive recorded on request (user, 2026-09-05)

**Do not add parentheses merely to make a multi-line boolean chain parse.**
Unparenthesized continuation after a trailing `and`/`or` is the intended,
readable form and is fully supported by current toolchain source. Adding `(...)`
wrappers around every continuation makes the code LESS readable and must not be
normalized into specs or product code; parentheses are for precedence grouping
only. (A temporary paren-rewrite of `source_facts.spl` made during diagnosis was
reverted — `git checkout` — for exactly this reason.) `.claude/rules/language.md`
updated accordingly.

## Second instance, same class: `unsafe(...)` capability blocks in `std.common.math.math` (2026-09-05)

Found while implementing the Excel-to-math-lib migration plans
(`doc/03_plan/app/office/excel_to_math_lib_migration.md`,
`doc/03_plan/app/office/excel_to_math_synthesis.md`).

**Symptom.** Both acceptance specs
(`test/03_system/plan_acceptance/excel_to_math_{lib_migration,synthesis}_spec.spl`)
are unrunnable on this Mac:

```
error: compile failed: parse: in "src/lib/common/math/math.spl":
Unexpected token: expected expression, found Colon
```

**Cause.** `1b4edca296c` ("SFFI v2 source-boundary hardening (#75)") added 24
`unsafe(...)` lines to `src/lib/common/math/math.spl` and removed none
(`git diff 1b4edca296c~1 1b4edca296c -- src/lib/common/math/math.spl | grep -c
'^+.*unsafe'` = 24, `'^-.*unsafe'` = 0). The deployed binaries predate the
construct. Anything importing `std.common.math.math` is therefore unloadable,
which includes `src/app/office/sheets/math_bridge.spl` and, through it,
`src/app/office/sheets/formula.spl` — the entire Excel formula engine.

**Reproduced on a two-line fixture**, both spellings:

- inline — `unsafe(capabilities: [ffi]): rt_math_sqrt(x)` →
  `parse: Unexpected token: expected expression, found Colon`
- block —
  ```
  unsafe(capabilities: [ffi]):
      rt_math_sqrt(x)
  ```
  → `HIR lowering error: Unknown variable: unsafe` /
  `error[E1002]: function 'unsafe' not found`

**Binaries probed, all failing.** `bin/release/aarch64-apple-darwin/simple`,
`.../simple_seed`, `bin/release/aarch64-apple-darwin-macho/simple_seed`,
`bin/release/macos-arm64/simple`. `bin/release/darwin-aarch64/simple` and
`bin/release/aarch64-apple-darwin-macho/simple` are bootstrap CLIs with no
`run`/`test` command.

`bin/local/phase2-aarch64-apple-darwin/simple` (built 2026-09-05 11:51) is the
closest: it **parses** the construct, then fails later, and has no `run`/`test`
either —

```
compile --format=smf: MIR lowering error: E-MIR-TYPE-ZeroKind: lower_type
received a well-formed HirType whose `kind` field is raw 0 (never written)
while lowering 'scope-tail:rt_math_sqrt'
```

`lint` is blocked separately by the same stale-binary class, on a different
file: `parse: in "src/lib/common/perf/execution_metrics.spl": Unexpected token:
expected expression, found Indent`.

**Consequence for that lane.** No acceptance `it` in either plan can be
executed on this host, so no plan checkbox was ticked even where the
implementation work is complete. Same fix as above: rebuild and redeploy the
seed.

## Second manifestation (2026-09-05, later): NO spec runs on this host at all

Found while closing the open checkboxes of
`doc/03_plan/compiler/startup_performance/startup_perf_plan_2026-08-17.md` and
`doc/03_plan/sys_test/compiler_loader_script_crosslang_perf.md`, whose acceptance
oracles live in `test/03_system/plan_acceptance/`.

The staleness is not limited to individual product files — it reaches `std.spec`
itself, so the entire per-spec lane is dead on this Mac:

| Probe | Command | Result |
|---|---|---|
| Minimal spec (`describe`/`it`/`expect(1+1)`, nothing else) | `bin/release/aarch64-apple-darwin/simple_seed run <mini_spec.spl>` | **CONTRADICTED — see the correction below. Re-measured: `1 example, 0 failures`, rc=0.** |
| `test/03_system/plan_acceptance/compiler_loader_script_crosslang_perf_spec.spl` | same seed, `run` | same `always_inline` failure — the spec never loads |
| `test/03_system/plan_acceptance/startup_perf_plan_spec.spl` | same seed, `run` | `parse: in src/app/cli/help_surface_inventory.spl: Unexpected token: expected expression, found Indent` (unparenthesized multi-line boolean continuation at `help_surface_inventory.spl:77,84-85,98,119-121,127,132,139`, and the same class in `src/app/cli/command_registry.spl`) |
| `bin/simple` (`bin/release/aarch64-apple-darwin-macho/simple`, Aug 10) | `run`/`test` | `error: unknown command 'run'` — bootstrap CLI, `compile`/`native-build` only |
| `bin/local/phase2-aarch64-apple-darwin/simple` (Sep 5 11:51, `1.0.0-rc.1`) | `--help` | no `run`/`test` subcommand either |

### CORRECTION 2026-09-05 — `@always_inline` does NOT kill every spec

> **This correction was itself partly wrong — read the "Scope correction"
> section below before acting on it.** The measurements here are real: a bare
> `use std.spec` spec does print `1 example, 0 failures`, rc=0. But that green
> is a FALSE GREEN. Bare `use std.spec` emits `[WARN] Failed to load imported
> types from ["std"] ... module 'std' not found (E1034)` and silently degrades
> to the interpreter's BUILT-IN describe/it/expect shims — so it is evidence
> about the shims, not about `std.spec`. Proof, re-measured: under the bare
> form `expect("x")` with no matcher reports `✓ vacuous`, whereas the real
> module (`spec.spl:739-745`) fails a non-bool `expect(...)` that no matcher
> consumed. Real assertions do still discriminate (`expect(1+1).to_equal(3)`
> fails correctly), which is exactly what makes the false green convincing.
>
> The E1034 warning was visible in the very first run recorded below and was
> not weighed. That is the mistake worth keeping on the page: the evidence
> that the lane had degraded was in the output all along.
>
> The actual trigger is narrower than "braced imports": `expect` alone. It is
> the only spec symbol defined in `src/lib/nogc_sync_mut/spec.spl` (:734,739),
> which imports `std.io_runtime` (:351-353), and `io_runtime.spl` carries BOTH
> unparseable constructs — `@always_inline` (:178,252,316) and
> `unsafe(capabilities: [ffi]):` (:180).


The row above and the "Cause of the new symptom" paragraph below it were
**wrong**, and are left visible rather than quietly edited because the wrong
claim is the instructive part: it was generalised from one failing spec to
"the entire per-spec lane is dead", and that generalisation was relayed to
four other lanes before anyone re-measured it.

Re-measured on the same binary (`bin/release/aarch64-apple-darwin/simple_seed`,
20,392,352 bytes, 2026-07-25 13:12:54), twice — once from a scratchpad path
and once from inside `test/01_unit/`, in case module resolution differed:

```
use std.spec

describe "m":
    it "adds":
        expect(1 + 1).to_equal(2)
```
→ `m` / `✓ adds` / `1 example, 0 failures`, **rc=0**, both times. Adding
`use std.spec.{step}` and a `step(...)` call is also green.

So `std.spec`'s import closure loads fine under the Jul-25 seed, and the
`@always_inline` attribute at `io_runtime.spl:178,252,316` is not fatal on
that path. Whatever produced `semantic: variable 'always_inline' not found`
came from something specific to that spec's own import chain, and has not
been identified — the bisect was never done, because the failure was
generalised instead.

**What IS confirmed blocked**, verified in both directions: an import chain
reaching `std.common.math.math` fails with `parse: Unexpected token:
expected expression, found Colon`, because that file carries 24 `unsafe(...)`
blocks (`grep -c 'unsafe(' src/lib/common/math/math.spl` = 24) the seed
cannot parse. A spec importing `MATH_PI` fails; a spec importing only
`std.spec` does not. The `help_surface_inventory.spl` continuation failure
and the x86-64-ELF exit-126 finding are also unaffected by this correction.

The practical consequence: specs CAN be executed on this host today, as long
as their import chain avoids the poisoned modules. A lane that hits a load
failure must bisect its imports and name the offending module, not conclude
that nothing runs.

Cause of the new symptom — **bisect now done** (the correction above says it
never was; it has been, see "Scope correction" at the end of this record):
the offending module is `src/lib/nogc_sync_mut/io_runtime.spl`
(`@always_inline` at `:178,252,316` and `unsafe(capabilities: [ffi]):` at
`:180`), reached from `src/lib/nogc_sync_mut/spec.spl:351-353`. The single
trigger is `use std.spec.{expect}` — `{describe}`, `{it}`, `{context}` and
`{step}` are all green, because only `expect` lives in the module that imports
`std.io_runtime`. Crucially, the bare-`use std.spec` green does **not** show
that closure loading: that path silently falls back to the interpreter's
built-in shims (proof in the scope-correction section).

Consequence for the two plans above: their acceptance `it`s cannot be executed
here, so their checkboxes stay open regardless of implementation state. The
`deps_growth_band_verdict` interface promised by the startup plan's Phase E box
has been landed (`src/app/deps/growth_band.spl`) and its verdict table verified
by a direct driver under the same seed (a driver that imports only that module
avoids the `std.spec` closure), but the plan-acceptance `it` itself remains
unexecuted.

Unblock condition: a rebuilt seed or a deployed self-hosted full CLI on this
host. Do NOT parenthesize the multi-line boolean chains to satisfy the old
parser (user directive recorded above).

### Third independent construct, same staleness (confirmed 2026-09-05)

The parallel office lane attributed the host-wide spec outage to commit
`1b4edca296c` ("SFFI v2 source-boundary hardening"), which added `unsafe(...)`
capability blocks to `src/lib/common/math/math.spl`. Verified here directly:
`grep -c 'unsafe(' src/lib/common/math/math.spl` = **24**, and a two-line driver
`use std.common.math.math.{abs}` under the Jul-25 seed fails with
`parse: in src/lib/common/math/math.spl: Unexpected token: expected expression,
found Colon`.

So there are **three** independent current-language constructs the deployed
binaries reject, not one — which failure a given module reports is just whichever
import edge is walked first:

1. `@always_inline` (2026-08-26) — `src/lib/nogc_sync_mut/io_runtime.spl:178,252,316`;
   reached by `std.spec.{...}` (see the scope correction below). Reported as
   `semantic: variable 'always_inline' not found`.
2. Unparenthesized multi-line boolean continuation — e.g.
   `src/app/cli/help_surface_inventory.spl:77,84-85,98,119-121,127,132,139`.
   Reported as `expected expression, found Indent`.
3. `unsafe(...)` block expression (`1b4edca296c`) —
   `src/lib/common/math/math.spl`, 24 sites. Reported as
   `expected expression, found Colon`.

All three are fixed in current toolchain SOURCE; only the deployed artifacts are
stale. A seed rebuild (`cargo build --profile bootstrap -p simple-driver -p
simple-native-all`) was started by another session at 12:27. Do not edit stdlib
source to satisfy the old parser.

### Scope correction (2026-09-05): "no spec runs" is too broad — and the counter-example is a FALSE GREEN

An earlier revision of this record said the `@always_inline` failure "kills every
spec". A parallel lane correctly challenged that: a spec written with bare
`use std.spec` runs green on the same Jul-25 seed. Re-measured here, both halves
reproduce exactly — and the reason is worse than a scoping nuance.

| Import form | Result on `bin/release/aarch64-apple-darwin/simple_seed` |
|---|---|
| `use std.spec` (bare) | `✓ adds` — green |
| `use std.spec.{describe}` / `{it}` / `{context}` / `{step}` | green |
| `use std.spec.{expect}` | `semantic: variable 'always_inline' not found` |

`expect` is the sole trigger because `expect` lives in
`src/lib/nogc_sync_mut/spec.spl:734,739`, which imports `std.io_runtime`
(`:351-353`) — and `src/lib/nogc_sync_mut/io_runtime.spl` carries BOTH
unparseable constructs (`@always_inline` at `:178,252,316` and
`unsafe(capabilities: [ffi]):` at `:180`). Importing `std.io_runtime` directly
fails in **both** the bare and braced forms, so this is not a braced-import quirk.

**The bare-form green does not mean `std.spec` loaded.** Two proofs it did not:

1. Bare `use std.spec` prints
   `[WARN] Failed to load imported types from ["std"]: cannot resolve import:
   module 'std' not found (E1034)` — the import silently degrades to a warning
   and execution continues on the interpreter's BUILT-IN `describe`/`it`/`expect`
   shims (the same shims `test_runner_execute.spl:452` and
   `test_result_wrapper.spl:36` inject as source text).
2. Under bare `use std.spec`, `expect("x")` with no matcher reports **`✓ vacuous`**.
   The real module mandates the opposite: `spec.spl:739-745` fails a non-bool
   `expect(...)` that no matcher consumed ("vacuous expect"). The shim has no
   such guard.

So the accurate scope is: **specs that reach the real stdlib spec module (or any
other `std.io_runtime` / `std.common.math.math` importer) cannot run on this
host; specs that only touch the interpreter's built-in shims appear to run, with
silently weaker assertions.** A bare-`use std.spec` green on this host is
evidence about the shims, not about the code under test — do not admit it as a
spec verdict until a current binary is deployed.

Both `test/03_system/plan_acceptance/` specs are in the genuinely-blocked class:
they use braced imports of `expect` and of real product modules
(`app.cli.help_surface_inventory`, `app.deps.growth_band`).
