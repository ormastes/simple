# Stage-3 `warning: unresolved call` family — incomplete diagnostic + cross-module static-method resolution hole

- **Date:** 2026-08-07
- **Status:** OPEN (two members fixed; `runtime_args` and `kind_to_text`
  confirmed non-bugs/stale in current source; **`run_check` REPRODUCED and
  root-caused 2026-08-09 — mechanism C, a hardcoded `*check.spl` exclusion in
  the Rust seed's source collector, §2b; not fixed here per "fix .spl not
  Rust"**; rest classified as out-of-scope or non-code build-config issues).
  - **FIXED** `d328200332e` — `target_is_float` (mechanism B,
    `src/compiler/35.semantics/semantics/cast_rules.spl`).
  - **FIXED** (this pass) — `kind_can_follow` (mechanism B,
    `src/compiler/35.semantics/macro_check/template.spl`): restored the
    missing free-function body as `fn kind_can_follow(kind, prev_kind)`,
    following Rust `macro_rules` follow-set rules (nothing may directly
    follow an `expr`/`stmt` fragment). Regression spec:
    `test/01_unit/compiler/macros/template_kind_can_follow_spec.spl`
    (RED before the fix: 0/4 pass, "unresolved call"; GREEN after: 4/4 pass).
  - **NOT reproduced as a bare unresolved call** — `kind_to_text`: no bare
    `kind_to_text(...)` call site exists anywhere in the current tree (only
    qualified siblings like `borrow_kind_to_text`, `transport_kind_to_text`,
    `objectprovider_backend_kind_to_text`, all defined). The one call site in
    `template.spl` uses the already-working `kind.to_text()` method form. This
    may have been the stage-3 log capturing a desugared method-call lookup
    rather than a literal bare call, or the log line no longer reproduces
    against current source; cannot confirm without a full stage-3 repro run
    (out of budget for this pass).
  - **mechanism A** (`hygienetransformer_create`, `templatetypechecker_create`
    x2, `templatevalidator_create` x2) — deliberately **not fixed**: root
    cause confirmed still present at `mangle.rs:236-243` /
    `imports.rs:184-188` (see §2); fixing it means loosening the fuzzy global
    suffix resolver on the bootstrap critical path, which needs its own
    change per the doc's existing recommendation, and per CLAUDE.md ("fix
    .spl not Rust") is out of scope for a `.spl`-only pass regardless. All six
    call sites live in the dead `macro_check/` module (zero importers).
  - `rsa_sig_valid`, `handle_os` — confirmed non-bug: `src/os` is not in the
    `--source` build set; this is a build-config scope question, not a code
    defect.
  - `t32_cli_main` — confirmed not independently fixable here: `src/app/t32_cli`
    is a symlink out of the tree; the `-> i32` vs. caller-as-`i64` mismatch
    lives in code outside this repo's tracked tree.
  - `parse_hostcomm_config` — confirmed still undefined; imports a
    nonexistent module `std.nogc_sync_mut.baremetal.config`, and the function
    itself has no definition anywhere (only `default_hostcomm_config()`
    exists in `types.spl`). Left open: no clear single correct restoration
    without knowing the intended config-loading API, and the call site risks
    overlapping other in-flight baremetal/config lanes.
  - `runtime_args` — **confirmed non-bug, already resolved in current
    source**: the sole 2026-08-06 warning site,
    `app__cli__api_surface_snapshot__main`, now reads
    `src/app/cli/api_surface_snapshot.spl:30,272`
    (`use app.io.args_ops.{get_args}` / `val args: [text] = get_args()`) —
    exactly the `get_args()` rename this doc already recommended. There is
    no remaining `runtime_args(` call site anywhere in `src/` (full-tree
    grep). No fix needed; the family member is stale.
  - `kind_to_text` — re-checked at higher resolution. The 2026-08-06 warning
    site was
    `compiler__semantics__macro_check__template__TemplateTypeChecker.infer_expansion_type`
    (`src/compiler/35.semantics/macro_check/template.spl:304-332`). Read the
    full method body: the only fragment-kind-to-text call in it is
    `kind.to_text()` at line 319 (method form, resolves fine); there is no
    bare `kind_to_text(...)` anywhere in that function or file. Sharpens the
    earlier "not reproduced" finding to a specific, checked function — clean
    in current source. `macro_check/` remains dead code (zero importers), so
    even if this were stale it isn't runtime-reachable. No fix needed.
  - `run_check` — investigated, **no code defect found in current source**.
    Both 2026-08-06 call sites (`src/app/build/cli_entry.spl:60` inside
    `handle_build`, `src/app/cli/_CliMain/main_and_help.spl:346` inside
    `main`) correctly `use app.cli.check.{run_check}` and call
    `run_check(args)` / `run_check(check_args)`; `run_check` is defined at
    `src/app/cli/check.spl:297`, and every transitive import of `check.spl`
    (`app.cli.query_rich_common`, `app.cli.repo_hygiene_gate`,
    `app.cli.check_options`, `app.check.sspec_source`,
    `app.check.concurrency_lint`) resolves to an existing file. The
    `app.build.quality` / `lib.database.*` import failures visible in the
    2026-08-06 log come from unrelated files elsewhere in the source set
    (`src/app/ui.render/core.spl`, `src/lib/*/database/mod.spl`) — not from
    `check.spl` or either caller — so they don't explain the warning. One
    lead surfaced but **not confirmed**: `run_check` is not a unique bare
    name — `src/app/cli/check_dbs.spl`, `src/app/cli/check_tier.spl`, and
    `src/os/port/initramfs_pack.spl` each define their own free function
    also named `run_check` (all non-`pub`). This duplicate-name shape is
    superficially similar to the documented mechanism-A ambiguity, but
    unlike mechanism A this is a direct qualified `use module.{run_check}`
    import, not a suffix-heuristic method call, so the same root cause
    doesn't obviously apply. A same-worktree live stage3 repro
    (`run_stage3.shs <worktree> probe`) was started to confirm one way or
    the other but did not finish inside this pass's time budget (stage2
    native-build was still running against `--source src/compiler --source
    src/lib --source src/app` after 15+ minutes of wall time). **Left open,
    unconfirmed** — re-run the repro to completion before deciding whether
    this is a real bug or a third stale/non-repro log line alongside its two
    siblings above.
  - **2026-08-09 follow-up:** rebuilt the `simple-s3red` scratch worktree to
    current `origin/main` (`5b415080f6e2`, `git fetch` + `git reset --hard`)
    and re-ran the same `run_stage3.shs` repro fresh (`build/probe2`) to
    settle the open item above. The process ran for **1h25m59s** wall time
    (`Rl` state throughout, steady ~34.8GB RSS, CPU consistently pegged —
    not hung/zombied, genuinely still computing) without ever writing
    `stage3.log` content or a `stage3.rc` marker, on a host that was
    simultaneously running at least one other concurrent full-tree
    `native-build` (a pre-existing `build/probe` process, unrelated to this
    task) and where free disk fell from 83G to 48G over the same window from
    other concurrent sessions' activity — i.e. heavy shared-host contention.
    Per an explicit time-and-resource budget decision, the process was
    killed (`kill 721957`, confirmed dead) before producing a verdict rather
    than let it run indefinitely or risk the ENOSPC failure mode this repo's
    memory notes record twice at this fill level. **Result: inconclusive —
    live confirmation did not complete within budget, due to resource
    contention, not any observed defect signal (no crash, no error, no
    partial-failure output was ever captured from this run).** This is not a
    negative result and does not by itself confirm or refute the warning.
    Combined with the unchanged static analysis (both call sites resolve
    correctly via qualified `use app.cli.check.{run_check}`; the only open
    lead is the non-unique bare name shared with `check_dbs.spl`,
    `check_tier.spl`, `src/os/port/initramfs_pack.spl`, whose relationship to
    mechanism A remains unconfirmed either way), `run_check` remains **OPEN,
    unconfirmed** — same disposition as before this pass, now with one more
    documented non-completing repro attempt. A future pass should retry the
    repro on a quieter host, or independently under `run_check`'s own
    stage-3 log-line context to shortcut the full-tree build.
  - **2026-08-09 RESOLVED (root cause) — `run_check` REPRODUCED; cause is
    mechanism C, a hardcoded `check.spl` filename exclusion.** See §2b. The
    full-tree repro is *not needed*: a **3-file minimal probe** reproduces the
    exact 2026-08-06 log line in ~60s. The "non-unique bare name" lead recorded
    above is **REFUTED** — see §2b for both.
  - The §1 finding (diagnostic is a partial sample) and §5 recommendation
    (promote to error once coverage is fixed) both still hold; not addressed
    here.
- **Severity:** HIGH — a warning-level diagnostic for "this call resolves to no
  definition", emitted by a build that also runs with `SIMPLE_NO_STUB_FALLBACK=1`.
  Any member reached at runtime is a call into nothing.
- **Repro:** `/home/ormastes/dev/simple-s3red/run_stage3.shs <worktree> <tag>`
  (stage2 = `simple-s3clean/build/clean/stage2-simple`, `SIMPLE_BOOTSTRAP=1`).
  Baselines: `simple-s3red/build/red/stage3.log`,
  `simple-s3family/build/green/stage3.log` (identical, 28 lines, rc=1).
  **Stale as of 2026-08-09:** both paths `run_stage3.shs` hardcodes are gone
  (`simple-s3clean/build/clean/stage2-simple` and the
  `simple-t3-final-20260806/...stage2-runtime-authority` runtime), so the script
  fails at `exit 90` / missing-binary. Substitute a current stage2 (e.g.
  `pub/simple-wt-base/.s2build/stage2-simple`) and runtime (e.g.
  `pub/simple/build/bootstrap-mlkem-stage2-20260808b/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority`).
  **Prefer the 3-file minimal repro in §2b** — ~60s instead of >1h25m, and it
  isolates the cause instead of merely observing the warning.

## 1. The warning list is a PARTIAL SAMPLE, not an enumeration

This is the headline finding and it invalidates any attempt to size the family
from the log.

In `src/compiler/35.semantics/macro_check/mod.spl`, function `define_macro`:

| line | call | defined anywhere? | warned? |
|------|------|-------------------|---------|
| 153  | `templatevalidator_create()` | **no** (0 defs) | **yes** |
| 166  | `macrodef_create(name)`      | **no** (0 defs) | **NO**  |

Both are bare, undefined, free-function calls in the **same function body**.
Codegen provably walked `define_macro` — it emitted the line-153 warning. Yet
line 166 produced nothing. Same pattern for `params_len` / `macros_get`
(0 definitions each, never warned).

**Therefore the 16 `unresolved call` lines in the stage-3 log are a floor, not a
count.** The true family must be enumerated from source, not from the log.

Additional truncation on top of that: the build **aborts** at
`error: <inline asm>:2:25: unexpected token in argument list /
movzx eax, byte ptr [{addr}]` (blocker #10 lane,
`src/compiler/35.semantics/volatile.spl:160`), so codegen never finishes the
walk. Note this error is **not** contributed by the `--source` worktree: a 9-line
`.spl` with no compiler sources reproduces it, because `native-build` resolves an
implicit source root from the stage2 binary's own install tree. Stripping
`volatile.spl` in the worktree under test does NOT unblock it.

## 2. Mechanism A — cross-module `<lowertype>_<method>()` can never resolve

Applies to: `hygienetransformer_create`, `templatetypechecker_create` (x2),
`templatevalidator_create` (x2) — 6 of the 16 lines.

There is **no `_create` desugaring in the `.spl` compiler.** Resolution is a
generic suffix heuristic in the bootstrap driver
(`src/compiler_rust/compiler/src/pipeline/native_project/`). Two suffix indexes
are built, and they differ by exactly one condition:

`mangle.rs:236-243` (local, per-module):
```rust
let sub_suffix = &suffix[dot_pos + 1..];
if !sub_suffix.is_empty() {
    local_suffix_index.entry(sub_suffix.to_string()).or_default().push(...);
}
```

`imports.rs:184-188` (global, cross-module):
```rust
let sub_suffix = &suffix[dot_pos + 1..];
if !sub_suffix.is_empty() && sub_suffix.starts_with(|c: char| c.is_ascii_uppercase()) {
    index.entry(sub_suffix.to_string()).or_default().push(...);
}
```

Mangled statics are `<module>__<ClassName>.<method>`, so the sub-suffix is the
**method name** — always lowercase by convention (`create`, `is_float`,
`to_text`). The uppercase guard means **no method name is ever a key in the
global index**. Consequently:

- same-module `MacroDef.create` → present in the local index → resolves silently;
- cross-module `TemplateValidator.create` / `HygieneTransformer.create` → absent
  from the global index → unresolved.

That is the exact asymmetry observed. Wildcard `use mod.*` does not help:
`collect_use_imports` (`imports.rs:973,991`) filters `!raw_name.contains('.')`,
so dotted `Class.method` entries are explicitly skipped.

**Not fixed here deliberately.** `resolve_by_suffix` matches candidates with a
fuzzy `candidate.to_lowercase().contains(prefix.to_lowercase())`. Dropping the
uppercase guard would admit lowercase method names into a *fuzzy* global
resolver, which can bind a call to the wrong class. Loosening a fuzzy global
resolver on the bootstrap critical path needs its own change with its own
verification, not a drive-by.

## 2b. Mechanism C — `collect_spl_files_recursive` silently SKIPS every `*check.spl`

**Confirmed 2026-08-09 by live repro.** Applies to: `run_check`.

`src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:1632-1637`, in
`collect_spl_files_recursive` (the function that gathers the `--source` set):

```rust
} else if path.extension().is_some_and(|e| e == "spl") {
    if let Some(p) = path.to_str() {
        if p.contains("check.spl") {
            continue;                 // <-- unconditional, uncommented, substring match
        }
    }
    if path.is_file() {
        out.push(path);
    }
}
```

`src/app/cli/check.spl` is therefore **never compiled**, so `run_check` has no
definition in the closure and every caller warns. There is no defect in the
`.spl` sources at all — both call sites and the definition are correct, exactly
as the earlier static analysis found. The static analysis was right about the
code and simply could not see the build-system exclusion.

Three properties make this worse than a plain exclusion:

1. **Substring, not filename.** `p.contains("check.spl")` matches any path
   *ending* in `check.spl`, so it also drops `arch_check.spl`,
   `bootstrap_check.spl`, `simd_check.spl`, `health_check.spl`, … — **14 files
   in the `--source src/compiler --source src/lib --source src/app` set**
   (15 repo-wide under `src/`): `src/compiler/30.types/variance_tests_check.spl`,
   `src/compiler/35.semantics/{simd_check,gc_boundary_check}.spl`,
   `src/compiler/90.tools/coupling/layer_check.spl`,
   `src/lib/nogc_async_mut/mcp/health_check.spl`,
   `src/app/check/wm_lane_boundary_check.spl`,
   `src/app/cli/{arch_check,bootstrap_check,check,query_check}.spl`,
   `src/app/grammar_doc/tier_check.spl`,
   `src/app/gui_perf/macos_smf_dynlib_transcript_check.spl`,
   `src/app/startup/launch_meta_check.spl`,
   `src/app/vscode_extension/manifest_check.spl`.
2. **The symlink branch does not apply the filter** (line 1628-1631 pushes any
   `.spl` symlink unconditionally), so the same file is included or excluded
   depending only on whether it is a symlink — an inconsistency, not a policy.
3. **A unit test appears to cover this and does not.**
   `native_project/tests.rs:3998 test_build_use_map_keeps_production_check_modules`
   builds a `cli/check.spl` and asserts `use_map["run_check"]` resolves — and it
   **passes**, because it calls `build_import_map` / `build_use_map_from_ast`
   directly on a hand-supplied `file_sources` vec. It never goes through
   `collect_spl_files_recursive`, which is where the file is dropped. A green
   test named for exactly this production case is why the bug survived.

### Repro (replaces the hour-long full-tree run)

Three files, `--source src`, entry `src/app/cli/bootstrap_main.spl`:

- `src/app/cli/check.spl`: `fn run_check(args: [text]) -> i64:` / `return 7`
- `src/app/build/cli_entry.spl`: `use app.cli.check.{run_check}` +
  `fn handle_build(a) -> i64: return run_check(a[1:])`
- `src/app/cli/bootstrap_main.spl`: calls `handle_build`

Emits, in ~60s, byte-identical to the 2026-08-06 stage-3 log line:

```
warning: unresolved call `run_check` in function `app__build__cli_entry__handle_build` (module: app__build__cli_entry)
```

### Controlled variant matrix (each an independent build)

| variant | result |
|---|---|
| `fn run_check` in `cli/check.spl` | rc=1, **1 unresolved** |
| `pub fn run_check` in `cli/check.spl` | rc=1, **1 unresolved** — `pub` is irrelevant |
| `fn run_check` in `cli/`**`verify.spl`** | **rc=0, 0 unresolved** — module rename fixes it |
| `fn do_verify` in `cli/check.spl` | rc=1, **1 unresolved** — function rename does NOT fix it |

The trigger is the **module filename**, not the function name, not visibility.

### The "non-unique bare name" lead is REFUTED

Two independent disproofs:

1. The minimal probe above contains **exactly one** `run_check` definition and
   still warns. Ambiguity cannot be the cause.
2. The three "competing definitions" recorded in the 2026-08-09 entry do not
   exist. An **unanchored** grep matched *prefixes*: the real names are
   `run_check_dbs` (`check_dbs.spl:134`), `run_check_tier`
   (`check_tier.spl:557`) and `run_check`**`ed`** (`initramfs_pack.spl:185`) —
   all distinct symbols. Anchored, `^\s*(pub )?fn run_check\b` has exactly
   **one** `.spl` definition tree-wide: `src/app/cli/check.spl:297`.
   (Cf. the standing "anchor greps when counting symbol classes" rule.)

This also means `run_check` is **not** an instance of mechanism A: it is not a
suffix-heuristic method call and has nothing to do with the `mangle.rs` /
`imports.rs` uppercase guard.

### Fix — out of scope here, but unlike mechanism A it is not risky

The defect is in the **Rust seed** (`src/compiler_rust/...`), so per CLAUDE.md
("fix .spl not Rust") it is not fixed in this `.spl` pass. Recording the shape
because, unlike mechanism A, there is no fuzzy-resolver hazard: the exclusion is
an unconditional, uncommented, unjustified `continue` with no test asserting the
skip. The likely intent was to skip *test/check-harness* inputs, but the
implementation catches production modules by substring. Recommended change:
delete the branch, or narrow it to an explicit opt-out that cannot match
production paths — and add a test that drives `collect_spl_files_recursive`
itself, since the existing `tests.rs` test bypasses it. Blast radius is the 14
files listed above, several of which are compiler internals.

## 3. Mechanism B — the `impl X:` → free-function refactor dropped bodies

76 files carry the marker `# ... Methods (was: impl X:)`. The conversion
renamed methods to free `fn <lowertype>_<method>` — but in places it emitted the
call site as `<VARNAME>_<method>` (named after the *variable*, not the type), a
name that could never resolve, and in at least one place **deleted the impl block
contents outright**, leaving the header comment with an empty body.

Confirmed instance (**FIXED**, commit `d328200332e`):
`src/compiler/35.semantics/semantics/cast_rules.spl` — the section
`# NumericType Methods (was: impl NumericType:)` was empty, and
`cast_bool_to_numeric` called `target_is_float(target)` (variable name `target`,
not type name `NumericType`). Sibling `BoolCast` / `StringCast` sections in the
same file kept their converted methods, so only this impl block was lost.
Restored as `fn numerictype_is_float`.

Same fingerprint, still open, in `macro_check/`:
`self.macros_get(macros, ...)`, `validator.params_len(params)`,
`self.validator_validate_matcher(validator, ...)`, `param.kind_to_text(kind)`,
`kind_to_text(kind)`, `kind_can_follow(kind, prev_kind)` — all reference bare
undefined names. Line 168 of `template.spl` uses the correct form
`kind.to_text()`, so the converter's output is inconsistent within one file.

## 4. Remaining members, classified

| callee | classification |
|---|---|
| `target_is_float` | **FIXED** `d328200332e` — mechanism B |
| `hygienetransformer_create`, `templatetypechecker_create` (x2), `templatevalidator_create` (x2) | mechanism A; in **dead** code (`macro_check/` has zero importers, `MacroChecker` zero users) |
| `kind_can_follow`, `kind_to_text` | mechanism B; same dead module |
| `rsa_sig_valid` (`src/os/crypto/rsa.spl`), `handle_os` (`src/os/cli.spl`) | definitions exist but `src/os` is **not in the `--source` set** (`--source src/compiler src/lib src/app`). Build-config/source-set question, not a code bug. |
| `t32_cli_main` | defined `pub fn` at `src/app/t32_cli/mod.spl:25`, but `src/app/t32_cli` is a **symlink out of the tree** (`../../examples/10_tooling/trace32_tools/t32_cli`). Signature is `-> i32` while the caller returns it as `i64`. |
| `parse_hostcomm_config` | `use std.nogc_sync_mut.baremetal.config...` names a module that **does not exist** (`src/lib/nogc_sync_mut/baremetal/` has no `config.spl`), and the function is defined nowhere. Only `default_hostcomm_config()` exists, in `types.spl`. |
| `run_check` | **REPRODUCED + root-caused 2026-08-09 — mechanism C (§2b).** `.spl` sources are correct; `src/app/cli/check.spl` is never compiled because `collect_spl_files_recursive` (`native_project/mod.rs:1634`) skips any path containing `check.spl`. Rust-seed defect, not fixed here. Also silently drops 13 other production modules. |
| `runtime_args` | **stale/non-bug (2026-08-09):** no remaining call site; `src/app/cli/api_surface_snapshot.spl` already calls `get_args()` from `src/app/io/args_ops.spl:6`. |

`macro_check/` is dead but **must not be blind-deleted**: `MacroDef`,
`MacroRule` and `MacroCall` are referenced outside it (`src/compiler/30.types/`,
`src/app/interpreter/`), so deletion needs a per-symbol check that those are
genuinely separate definitions.

## 5. It should be an error, not a warning

`compiler.rs:851-857` justifies the warning as "continuing so normal stub/link
closure can resolve what bootstrap export discovery cannot" — i.e. unresolved
names are left as raw symbols for the linker. That story does not hold here:

1. The harness sets `SIMPLE_NO_STUB_FALLBACK=1`. There is no late-binding story.
2. Several members (`target_is_float`, `macrodef_create`, `kind_to_text`) have
   **zero definitions anywhere in the tree** — no linker can close them.
3. The diagnostic is **also incomplete** (§1): it misses undefined calls in
   functions it demonstrably walked. A warning that is both non-fatal and
   unsound is worse than either failure alone.

**Recommendation:** promote to an error once §1 is fixed, gated on
`SIMPLE_NO_STUB_FALLBACK`; and fix the emitter's coverage first, because
promoting an incomplete check to fatal would give false confidence.

**Do not** make the family smaller by weakening the diagnostic.
