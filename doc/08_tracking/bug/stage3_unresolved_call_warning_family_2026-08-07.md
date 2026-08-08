# Stage-3 `warning: unresolved call` family — incomplete diagnostic + cross-module static-method resolution hole

- **Date:** 2026-08-07
- **Status:** OPEN (two members fixed, rest classified as out-of-scope or
  non-code build-config issues).
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
  - `run_check`, `runtime_args` — left open: not touched this pass because
    resolving them (a caller-scope/import-failure question for `run_check`,
    and a rename to `get_args()` for `runtime_args`) sits in `src/app/cli` and
    `src/app/io`, areas this pass did not have budget to safely cross-check
    against the excluded parallel lanes (nil-coalesce/vacuous-binary/SIGILL/
    Symbol-alias/ByteOrder/measurement-baseline work).
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
| `run_check` | defined `src/app/cli/check.spl:297`, in scope, yet unresolved from two callers — one preceded by a failed `app.build.quality` import. |
| `runtime_args` | no definition; `src/app/io/args_ops.spl:6` defines `fn get_args()`. |

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
