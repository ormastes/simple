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
