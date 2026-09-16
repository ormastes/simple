# CORRECTION (2026-08-31, after this record was drafted)

**The parser gap described below is NOT a code defect. The fix is already in the
tree, and every failure recorded here is a STALE BINARY.**

Verified two ways:

1. `cargo test -p simple-parser --release unsafe_inline_body` -> **4 passed,
   0 failed**. The regression test `parser/src/unsafe_inline_body_test.rs`
   exists, is wired in at `parser/src/lib.rs:54`, and documents this exact
   symptom ("expected Newline, found Identifier": `parse_unsafe_block_primary`
   called `parse_block`, which accepts only the indented form).
2. A seed built TODAY (`build/phase_snapshots/phase1_1788135602/simple`,
   Aug 31 09:19) compiles the inline form with **rc=0**.

The binaries this record measured are simply older than the fix:

| binary | date | has fix |
|---|---|---|
| `src/compiler_rust/target/release/simple` | Aug 25 | NO |
| `bin/release/aarch64-apple-darwin/simple` (full CLI) | **Jul 25** | NO |
| `build/phase_snapshots/phase1_*/simple` (today) | Aug 31 | **YES** |

So the conclusion "no binary on this machine can unblock the lane" is wrong: a
current seed already parses it. What IS still true and still worth fixing is the
DEPLOY problem in the second half of this record -- `bin/simple` resolves to a
bootstrap CLI in the stage-4 full-CLI slot, and the only full CLI on the machine
is a Jul-25 build. That is a stale-deployment defect, not a parser defect, and it
is the real reason `bin/simple test` cannot run.

Everything below is retained as the original investigation, including the parts
this correction supersedes.

---

# macOS: `bin/simple test` is unrunnable — wrapper points at the bootstrap CLI, and no deployed binary parses inline `unsafe(...): expr`

- Date: 2026-08-31
- Host: macOS aarch64 (aarch64-apple-darwin), `/Users/ormastes/simple`
- Area: deploy slot + parser/grammar. **Not** `src/compiler/50.mir/**` or `src/compiler/20.hir/**`.
- Status: OPEN. Two independent defects, both blocking the documented test path.

## Binary identities (recorded, since slots are repointed mid-session)

| path | size | mtime | `--version` line 1 | sha256 |
|---|---|---|---|---|
| `bin/simple` | 431 | Jul 25 03:47 | (sh wrapper) | — |
| `bin/release/aarch64-apple-darwin-macho/simple` | 132398344 | Aug 10 09:00 | `simple-bootstrap 1.0.0-beta` | `1860830a88ac901b3a608efe428ed1d70c18eaa23bc81fbfeb9a8c757afc6164` |
| `bin/release/aarch64-apple-darwin/simple` | 29315096 | Jul 25 14:15 | `Simple v1.0.0-beta` (full CLI) | `f2c216a660da83da1a253d2e8191a3059a66b1d9dc11bbcbaf237fe7e5b8d2bc` |
| `bin/release/macos-arm64/simple` | 24868632 | Apr 11 12:04 | `Simple v0.9.5` | — |
| `src/compiler_rust/target/release/simple` | 146661352 | Aug 25 00:11 | Rust seed (self-declaring) | — |

`bin/release/darwin-aarch64/simple` resolves to the same inode as the `-macho` slot.
`bin/simple_seed` does not exist (only `bin/release/*/simple_seed`, Jul 25 13:12).

## Defect 1 — `bin/simple` resolves to the BOOTSTRAP CLI, so `test` does not exist

`bin/simple` is a shell wrapper that `exec`s
`bin/release/aarch64-apple-darwin-macho/simple`. That slot was the stage-4 **full-CLI**
deploy target; since Aug 10 09:00 it holds a 132MB binary that identifies as
`simple-bootstrap 1.0.0-beta` and whose `--help` says *"Simple Bootstrap Compiler"*.

```
$ bin/simple --version | head -1
simple-bootstrap 1.0.0-beta
$ bin/simple test test/01_unit
error: unknown command 'test'
```

This is **not** the "probing a stage binary for `test` is a category error" trap: the
supported, documented tool path `bin/simple test` is what was invoked, and the wrapper
is what routes it to a bootstrap CLI.

A full CLI **is** still deployed, at the sibling slot
`bin/release/aarch64-apple-darwin/simple` (`Simple v1.0.0-beta`), and its `--help`
lists `test`, `watch`, `targets`, `sim`, etc.

**Not repointed here** — other sessions are live against the current wrapper. The fix is
either to redeploy the full CLI into the `-macho` slot or to repoint the wrapper, and
that decision belongs to whoever owns the deploy.

## Defect 2 — inline `unsafe(...): <expr>` parses nowhere, and it is in the app.io hub

Running the same small spec through the **full CLI** gets all the way through runner
startup and then dies in module load:

```
$ TMPDIR=<fresh> bin/release/aarch64-apple-darwin/simple test \
      test/01_unit/scripts/recursion_guard_spec.spl
Simple Test Runner v0.8.1
Running 1 test file(s) [mode: interpreter]...
Session setup: 10167ms
  FAIL  test/01_unit/scripts/recursion_guard_spec.spl (0 passed, 1 failed, 492ms)
        Error: error: compile failed: parse: in "/Users/ormastes/simple/src/app/io/mod.spl":
               Unexpected token: expected expression, found Colon
Results: 1 total, 0 passed, 1 failed        # exit 1
```

The Rust seed (Aug 25) fails on the same file with its own wording:

```
error: compile failed: parse: in ".../src/app/io/mod.spl":
Unexpected token: expected Newline, found Identifier { name: "rt_random_uniform", ... }
```

The runner infrastructure itself is healthy — discovery, session setup, execution and
reporting all work. The blocker is purely that `src/app/io/mod.spl` cannot be parsed,
and `app.io.mod` is the hub every spec pulls in.

### Minimal reproduction

`inline.spl` — **FAILS** on both the full CLI and the Rust seed:

```
@unsafe(reason: "x", capabilities: [ffi])
extern fn rt_random_randint(min: i64, max: i64) -> i64

fn f(a: i64, b: i64) -> i64:
    unsafe(capabilities: [ffi]): rt_random_randint(a, b)

fn main():
    print("ok")
```

`block.spl` — **PASSES** (`ok`): identical but with the body on its own indented line.

So the suffixed single-line form of the `unsafe(...)` block is what is unsupported. The
compact form is exactly the case CLAUDE.md says must be fixed or filed rather than
silently normalized — hence this record instead of rewriting the call sites.

### Blast radius

The inline form was introduced by `1b4edca296c` *"SFFI v2 source-boundary hardening
(#75)"* (2026-08-27), after the Aug-25 seed was built. It is now used at **53 sites
across 17 files**:

```
/usr/bin/grep -rn --include='*.spl' -E '^[[:space:]]*unsafe\(.*\):[[:space:]]+[A-Za-z_]' src/
```

including `src/app/io/mod.spl`, `src/app/cli/bootstrap_main.spl`, `src/app/check/main.spl`,
`src/lib/common/math/math.spl`, `src/lib/common/encoding/utf8.spl`,
`src/lib/common/science_math/{linalg,statistics,ml_metrics}.spl`,
`src/lib/common/engine/{math2d,math3d}.spl`, `src/lib/nogc_sync_mut/gpu/engine3d/*`,
`src/os/installer/*`.

### Where the support gap is

The pure-Simple parser has the construct at
`src/compiler/10.frontend/core/parser_stmts.spl:526` (`parse_unsafe_block_expr_if_present`,
both the bare and the `(reason:/capabilities:)` forms, delegating to `parse_block()`), and
a current stage-2 binary built from this source **does** get past parse on `inline.spl`
(it reaches HIR before dying for the unrelated reason below). So the gap is in the
**Rust seed's** parser and in the **stale Jul-25 deployed full CLI**, not in current
pure-Simple source. Consequence: the test lane cannot be unblocked by any binary
currently on this machine — it needs either a seed parser fix or a fresh full-CLI deploy.

## Adjacent measurement — the phase-2/stage-2 binary (for the record, cause is elsewhere)

Binary: scratchpad `s2bin/capturedD` copied to `s2bin_myD`,
sha256 `f9dab919a68fd74917a34f0c22cdb1cb2921fb5a9388ccb833877eb00541eff2`,
32007624 bytes, Aug 31 08:39:18 2026. `--version` → `simple-bootstrap 1.0.0-rc.1`.

It is the bootstrap CLI, so only `--version`, `--help`, `compile`, `native-build` exist —
there is no interpreter (`run`) and no `test` on it, by design, and probing for those
proves nothing.

Counts, each run in a fresh per-run `TMPDIR`, all with `--backend=llvm`:

| command | input | runs | rc=139 (SIGSEGV) | rc=0 |
|---|---|---|---|---|
| `--version` | — | 1 | 0 | 1 |
| `compile` | 3-line hello world | 5 | **5** | 0 |
| `compile` | `inline.spl` above | 3 | **3** | 0 |
| `native-build` | 3-line hello world | 3 | **3** | 0 |

11/11 SEGV, deterministic — no bimodality observed on this binary. The trace shows it
completing `load_sources`, `parse`, `surface_build`, `surface_alias`, then emitting
`[bootstrap-error-count] source_idx=0 point=post-lowering count=0` and `[hir-fatal]`
before the fault — i.e. the failure is at/after HIR lowering, which is the MIR-lowering
defect already being worked in `src/compiler/50.mir/**` + `20.hir/**`. Recorded here only
so the numbers exist; **not** a separate bug.

Note this also confirms the Defect-2 diagnosis: a binary built from *current* source
parses `inline.spl` fine.

## Suggested fixes

1. Redeploy a current full CLI into `bin/release/aarch64-apple-darwin-macho/` (the slot
   the wrapper uses), or repoint `bin/simple` at `aarch64-apple-darwin/`. Whoever owns
   the deploy should pick; a wrapper edit mid-session breaks other lanes.
2. Teach the Rust seed's parser the suffixed `unsafe(...): <expr>` form so the seed can
   still build current source. Do **not** rewrite the 53 call sites to the block form —
   that normalizes a workaround over a compact form the language is supposed to accept.
