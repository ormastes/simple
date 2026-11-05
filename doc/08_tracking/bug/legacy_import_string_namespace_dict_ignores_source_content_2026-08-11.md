# `import string` namespace dict ignores src/lib/string.spl source content

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
export used by `src/lib/nogc_sync_mut/oauth/utilities.spl` and its
`gc_async_mut`/`nogc_async_mut` sibling copies.

## Symptom

Under the currently deployed self-hosted binary
(`bin/release/x86_64-unknown-linux-gnu/simple`), any legacy `import string`
caller resolving `string.<name>(...)` gets a namespace dict containing ONLY
the 8 `bm_*` symbols from `nogc_async_mut_noalloc.string.mod`
(`bm_hex_to_int`, `bm_int_to_str`, `bm_str_ends_with`, `bm_str_eq`,
`bm_str_find`, `bm_str_len`, `bm_str_starts_with`, `bm_str_to_int`) —
regardless of what `src/lib/string.spl` actually contains.

This affects both `bin/simple test` and `bin/simple run`.

## Repro

1. Edit `src/lib/string.spl` in any way (add a new exported wrapper fn,
   consolidate export statements, even append syntactically invalid text).
2. Run any script/spec that does `import string` (or `use string`,
   compiler-deprecation-warns but still resolves) and calls
   `string.str_char_at(...)` or `string.char_at(...)`.
3. Observe: `semantic: method 'str_char_at' not found on type 'dict'
   (receiver value: {bm_hex_to_int: ..., ... bm_str_len: ..., b)` — same
   dict, same 8 keys, every time.
4. Decisive check: append `!!!totally broken syntax!!!` as a new line to
   `src/lib/string.spl` and rerun. No parse error is raised, and the exact
   same stale dict is reported. `strace -f -e trace=openat bin/simple run
   ...` confirms the deployed binary does call
   `openat("/home/ormastes/dev/pub/simple/src/lib/string.spl", O_RDONLY...)`
   — so the file is opened, but its content is not what drives the
   resulting `string` namespace object.

## Hypothesis (unconfirmed — needs compiler-side investigation)

Some cached/baked-in representation of the `string` module (possibly from
the self-hosted binary's own build-time embedded stdlib, or a resolver that
matches `import string` to a different internal registration than the
`use std.string_core...` / `use nogc_async_mut_noalloc.string.mod...`
re-export shim at `src/lib/string.spl`) is served instead of a live parse
of the file. The `openat()` call may be for an existence/mtime check only,
not a content read that flows into namespace-dict construction.

## Impact

Every legacy `import string` caller in the oauth module family
(`src/lib/nogc_sync_mut/oauth/{utilities,authorize,validate}.spl` and its
`gc_async_mut`/`nogc_async_mut` sibling copies, 9 files total) that calls
`string.char_at`, `string.equals`, `string.length`, `string.char_code`, etc.
fails at runtime with "method not found on type dict" for every symbol
except the 8 `bm_*` ones — independent of whether those symbols are
exported correctly in `src/lib/string.spl` source.

## What was still done despite this

`src/lib/string.spl` was fixed at the source level regardless (added a
`char_at` alias wrapping `str_char_at`, consolidated to a single `export`
statement) because it is the textually and semantically correct fix and
matches the call-site convention used by all 9 legacy callers (only
`char_at` is called, never `str_char_at`). This fix cannot be proven to
take live effect under the currently deployed binary due to the defect
described above. Re-verify once resolved (or once a full compiler
rebuild+redeploy is possible — see `.claude/rules/bootstrap.md`, "Stage 3
self-host fails", which is a separate, currently-open blocker).

## Unblock condition

Re-run the repro above after either (a) this defect is root-caused and
fixed in the module loader/resolver, or (b) `bin/release/<triple>/simple`
is rebuilt+redeployed from current source via a working full bootstrap.

## 2026-08-17 (lane w04) — STILL LIVE, reproduced verbatim

Two-line reproducer on `bin/simple run`:

```
import string

fn main():
    print("char_at=" + string.char_at("hello", 1))
```

Error, matching this doc's symptom exactly (same 8 `bm_*` keys, same truncation):

```
error: semantic: method `char_at` not found on type `dict` (receiver value:
{bm_hex_to_int: <fn:bm_hex_to_int>, bm_int_to_str: <fn:bm_int_to_str>,
bm_str_ends_with: <fn:bm_str_ends_with>, bm_str_eq: <fn:bm_str_eq>,
bm_str_find: <fn:bm_str_find>, bm_str_len: <fn:bm_str_len>, b)
```

Preceded by a codegen diagnostic that names the real shape of the defect:

```
[CODEGEN BODY] Function 'main' body compilation failed: GlobalLoad: unresolved
identifier 'string' (not a global, function, const-data name, or import)
[CODEGEN-STUB-FALLBACK] body compilation failed for 'main'
```

`src/lib/string.spl` is innocent and was not modified: it defines
`fn char_at(s: text, idx: i64) -> text` and names `char_at` in its single
`export` line, alongside `char_from_code`, `char_code`, `str_char_at`,
`str_repeat`. The namespace dict served to `import string` callers still ignores
all of it. Root cause is in the resolver's `import <bare-name>` namespace-object
construction (Rust seed), not in `src/lib/**`; out of scope for stdlib lanes.

## 2026-11-03 — Pure-Simple source candidate, behavioral verification blocked

Claim: `p2-string-20261103`; base release source
`89d4e41ec88d781ec7191f2f3fe5b7334560ee21`.

Current Pure-Simple source has two attributable compatibility gaps:

- A bare import from outside the library tree never probes the root
  `src/lib/<module>.spl` facade after caller-relative/source lookup misses.
- Full unaliased imports bind exported bare names but do not register their
  module namespace, although explicit aliases already use a caller/physical
  owner namespace table.

The candidate probes the actual root facade only after existing caller/family
lookup and binds the full module's final path component to its resolved physical
owner. Existing facade re-export bindings supply the members; no string-specific
member table or fabricated implementation is introduced. `src/lib/string.spl`
already contains the real `char_at` wrapper and remains unchanged. Explicit
family resolution ordering is unchanged.

Authored regressions:

- `test/01_unit/compiler/interpreter/full_module_source_namespace_spec.spl`:
  exact bare-string path/owner, retained bare exports, arbitrary renamed facade
  forwarding, missing-member/caller isolation, and caller-local source precedence.
- `test/02_integration/compiler/interpreter/legacy_string_source_namespace_spec.spl`:
  actual `char_at`/`str_char_at` values and adjacent arbitrary source functions,
  renamed re-exports, explicit module alias and caller-name collision.

**TEST_BLOCKED:** this Windows environment has no qualified self-hosted full
CLI in `bin/release`. The tracked Rust seed and frozen diagnostic artifacts are
not behavioral substitutes. No regression cases have executed (positive executed
count: 0). The historical deployed Rust dictionary symptom therefore remains
unverified; this source candidate alone does not establish that its original
producer was repaired. Keep the bug open pending admitted interpreter/native
regressions and the compiler/core/lib/MCP checks required by repository policy.


## 2026-11-05 — ROOT-CAUSED + FIXED (Rust seed resolver), partial regression admission

Root cause (Rust seed, `src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs`):
for a bare single-segment import such as legacy `import string`, the final
fallback search in `resolve_module_path_uncached` probed ONLY the concurrency
family subdirectories (`src/lib/<family>/string.spl` /
`src/lib/<family>/string/__init__.spl`). It never probed the root facade
`src/lib/string.spl`. The family scan hit
`src/lib/nogc_async_mut_noalloc/string/__init__.spl` — whose entire export
surface is the 8 `bm_*` symbols — so `import string` from any caller outside
the library tree bound a namespace dict containing exactly those 8 keys,
ignoring `src/lib/string.spl` entirely (its `char_at`, `str_char_at`,
`char_code`, `str_repeat`, ...). That is the exact stale-dict symptom observed
since 2026-08-11. Scripts inside `src/lib` were unaffected because the
parent-directory climb resolves the facade before the fallback ever runs.

Fix: in the same fallback block, probe the ROOT facade
(`src/lib/<name>.spl`, then `src/lib/<name>/__init__.spl`) BEFORE the family
subdirectory scan, mirroring the pure-Simple resolver semantics already
asserted by `test/01_unit/compiler/interpreter/full_module_source_namespace_spec.spl`
(root facade wins for bare `string`; caller-local source still wins via the
earlier caller-relative strategies, unchanged). Blast radius: only bare
non-stdlib imports whose first segment names an existing root `src/lib` file
or package change target — verified no such other legacy import exists in
`test/01_unit`, `test/02_integration`, `test/00_unit`, `test/00_quick`, or
`examples` (only Python `import os`-style lines matched).

Verification (worktree /tmp/wt-libbug-strns on release/1.0.0 base
adfeae3765c; host aarch64 Linux; `bin/simple` absent — RED ran on the
phase1 snapshot seed, GREEN on the worktree-rebuilt seed
`src/compiler_rust/target/release/simple` from this fix, cargo
`--release --bin simple`):

- `simple run` of the doc's two-line reproducer now prints `char_at=e`
  (previously: `method 'char_at' not found on type 'dict'` with the 8
  `bm_*` keys).
- `test/02_integration/compiler/interpreter/legacy_string_source_namespace_spec.spl`
  example 1 (the exact legacy string repro: `char_at`, `str_char_at`,
  `char_code`, `str_repeat` values) PASSES. Example 2 still fails on its
  FINAL assertion (`expect(transform(7)).to_equal(-93)`: the caller's own
  local `fn transform` dispatches to the imported provider's body) — that
  misdispatch reproduces verbatim on the UNMODIFIED phase1 seed and is
  independent of `import string` (fails without the import line, on both
  binaries). It is a separate pre-existing seed defect (imported module's
  same-named fn shadows the caller's local fn via the merged flat function
  table), out of scope for this bug.
- Regression, all PASS on the rebuilt seed: string_core_spec (2),
  string_core_basic_coverage_spec (279), string_core_ops_spec (207),
  string_builder_spec (10), rt_string_ends_with_extern_dispatch_spec (12),
  full_module_source_namespace_spec (4), tool_checker_spec (3, exercises
  bare `import spipe` — confirms non-facade bare imports still reach the
  family fallback unchanged).

Status: the original stale-8-`bm_*`-dict symptom is FIXED in the seed
resolver source. Re-verify against a redeployed `bin/release/<triple>/simple`
built from this source before closing. The separate caller-local-fn
shadowing defect above should get its own bug entry if none exists.
