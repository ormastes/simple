# bin/simple had no test/lint/run/check/build subcommands (bootstrap-stage artifact deployed to the production path)

Date: 2026-08-01
Status: FIXED (redeployed)
Area: bootstrap / deploy / CLI surface

## Symptom

`./bin/simple --help` printed a 6-line banner and nothing else:

```
Simple Bootstrap Compiler v1.0.0-beta
Built from Simple source via the staged bootstrap

Compile-related flags include:
  --opt-level=<none|basic|standard|aggressive>
  --list-optimizations
```

Every subcommand was rejected. PROVED by direct invocation, not by reading help:

| invocation | exit | output |
|---|---|---|
| `bin/simple test --help` | 1 | `error: unknown command 'test'` |
| `bin/simple run --help` | 1 | `error: unknown command 'run'` |
| `bin/simple lint --help` | 1 | `error: unknown command 'lint'` |
| `bin/simple check --help` | 1 | `error: unknown command 'check'` |
| `bin/simple build --help` | 1 | `error: unknown command 'build'` |
| `bin/simple version --help` | 1 | `error: unknown command 'version'` |

Multiple lanes could not verify `.spl` changes at all. One lane declined to edit
MIR enum lowering because nothing could compile-check it.

## Root cause (PROVED)

The deployed binary was **not the full CLI**. It was a bootstrap-stage artifact
built from `src/app/cli/bootstrap_main.spl`, a minimal driver whose entire
command surface is `compile`.

The exact help text traces to that file at origin/main:

- line 443: `print "Simple Bootstrap Compiler v{bootstrap_version()}"`
- line 450: `print "Compile-related flags include:"`
- line 452: `print "  --list-optimizations"`

and its only command match, line 454: `if first.len() == 7 and first.starts_with("compile")`.

The full CLI lives at `src/app/cli/main.spl` with `src/app/cli/dispatch.spl` and
`src/app/cli/dispatch/table.spl`.

So nothing was "lost". A **stage artifact was deployed over the production
`bin/simple` path**. This is the same class of incident as
`reference_deployed_binary_lost_llvm_codegen_2026-07-29` and
`reference_live_bin_simple_lost_all_subcommands_2026-08-01`: a banner that looks
plausible while the dispatch table is a different, smaller one.

Corroborating binary fingerprints (`strings -a | grep -c`):

| binary | size | LLVM syms | `Run tests (default:` | `bootstrap seed only` |
|---|---|---|---|---|
| deployed (broken) | 130,366,776 | 58 | 0 | 0 |
| `simple.pre-segv-fix-20260731` | 154,095,344 | 282 | 1 | 1 |
| `simple_seed` | 57,029,288 | 0 | 1 | 1 |

The broken binary carried **zero** full-CLI help strings — consistent with a
different entry point, not a truncated or partial copy. Size alone would not have
caught it: at 130 MB it sits inside the "looks canonical" band.

A related stage output, `build/bootstrap-segv-fix/stage3-fixed/simple`
(127,498,696 B, sha256 `b41ad86af245…`, Jul 31 04:36), is the same family but not
byte-identical, so the exact producing run is INFERRED, not proved. The class of
artifact is PROVED by the help-string trace above.

## Fix

Rebuilt the canonical driver binary with LLVM from a verified origin commit and
redeployed.

Build (isolated tree, so no shared-WC uncommitted work could leak in):

```
git archive b0878b9f3f980de715ef29c5b2d68c6bd8d2e95b | tar -x -C /home/ormastes/dev/pub/.simple-build-36f5e286
LLVM_SYS_180_PREFIX=/usr/lib/llvm-18 \
  cargo build --profile bootstrap -p simple-driver --bin simple --features llvm -j 10
```

The shared working copy was **not** used as the build source: it carried 21 files
behind origin plus ~20 uncommitted modifications under
`src/compiler_rust/compiler/src/{hir,codegen}/`, which would have made the
artifact's provenance unknowable.

## Provenance

**Source commit**: `b0878b9f3f980de715ef29c5b2d68c6bd8d2e95b`

- Verified against `git ls-remote origin main` at build time.
- Tree entry count `109620`, duplicate paths `0` (`git ls-tree -r --name-only | sort | uniq -d`).
- Required fixes confirmed ancestors via `git merge-base --is-ancestor`:
  - `2360403891717f5df2efe1534aabdc7062fb8615` — `in` / `not in` boxing + `rt_value_int`/`rt_value_float`
  - `6469d70eb4e` — JIT text ordering compared heap handles, not content
  - `73a041794404` — `text.repeat()` had no runtime definition
  - `36f5e286ad6` — earlier tip this lane first built from

**Deployed artifact** (`bin/release/x86_64-unknown-linux-gnu/simple`, target of the `bin/simple` symlink):

- size `154,185,152`
- sha256 `6c1dcb2b05395d1f7fce1fdc0beb85df3c62d0c8c34375a5e4e4e2968e565854`
- LLVM symbol count `282` (canonical; 57 MB / 0 syms would mean no LLVM codegen)

**Replaced artifact**, preserved at
`bin/release/x86_64-unknown-linux-gnu/simple.bootstrap-main-stage-2026-08-01.bak`:

- size `130,366,776`
- sha256 `65d941e899293934c1785f4fd6f56c2d5ebdc811c6a092da77e00e6eca79e782`
- The backup was hash-verified to equal the pre-existing deployed binary **before**
  the swap, so it is a real rollback point and not a copy of the replacement.

Pre-existing rollback points left untouched: `simple.pre-segv-fix-20260731`,
`simple.rollback-llvm-seed-2026-07-30`,
`simple.pre-parserfix-79ca755d-2026-07-30.bak`,
`simple_seed.pre-parserfix-2026-08-01.bak`,
`simple_seed.rollback2-jul30-workingcopy-2026-08-01.bak`.

Deploy used `cp` to `simple.new` then `mv` (a direct `cp` over a running binary
hits "Text file busy"), and the staged file was hash-compared to the build output
before and after the `mv`.

`bin/release/linux-x86_64/` holds only the two MCP server binaries; it has no
`simple`, so no second copy needed updating.

## Verification (post-deploy, through `./bin/simple`)

Each subcommand was exercised with real work and with a negative control, because
a subcommand that prints usage and does nothing is the recurring failure mode here.

| check | expected | result |
|---|---|---|
| `--help` subcommand lines | > 0 | 20 matching `simple (test\|lint\|run\|check\|build)` |
| `run good.spl` | prints 42, exit 0 | `PROBE_RESULT=42`, exit 0 |
| `run bad.spl` (syntax error) | nonzero + diagnostic | exit 1, `expected expression, found Assign` |
| `run typebad.spl` (unresolved symbol) | nonzero | exit 1 |
| `test pass_spec.spl` | 2 passed, exit 0 | `Results: 2 total, 2 passed, 0 failed`, exit 0 |
| `test fail_spec.spl` | 1 failed, exit 1 | `Results: 1 total, 0 passed, 1 failed`, exit 1 |
| `lint src/app/cli/bootstrap_main.spl` | real findings, nonzero | exit 1, `Found 2 error(s), 1 warning(s)` |
| `compile good.spl -o good.smf` | artifact exists, exit 0 | 5,232 B `.smf`, exit 0 |
| `fmt --check good.spl` | real verdict | `OK ... is formatted`, exit 0 |
| `check --help` / `build --help` | real handler | dispatches; `build` prints `Simple Build System` |

The `test` pass/fail pair is the load-bearing one: it proves `test` evaluates
rather than rubber-stamping.

Carried runtime fixes, verified under `SIMPLE_JIT_STRICT=1` so an interpreter
fallback cannot false-green the result:

```
INT_IN=true FLOAT_IN=true BOOL_IN=true DICT_IN=true NOT_IN=true
TEXT_LT=true TEXT_GT=true REPEAT=appleapple
```

with `jit-fallback` / `falling back to interpreter` occurrences = **0**. That
confirms `2360403`, `6469d70eb4e` and `73a041794404` are present and effective in
the deployed artifact.

## Known caveat

The deployed binary is the **Rust-built driver with LLVM**, and it prints:

```
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
```

That warning is accurate. Per `CLAUDE.md` the intended default tooling is the
pure-Simple self-hosted binary, but the pure-Simple compiler cannot self-host at
current HEAD (see `project_stage3_selfhost_blocked_2026-07-31`), and the only
pure-Simple artifact available for the production path was the `bootstrap_main`
stage build that caused this outage. Restoring verification capability for ~34
blocked lanes took priority. This is a **known, temporary** deviation, not a
silent one.

Follow-up: once the pure-Simple stage produces an artifact built from
`src/app/cli/main.spl` (not `bootstrap_main.spl`), redeploy that instead — and
gate the deploy on the subcommand surface, not on the banner or the file size.

## Recommended guard

The deploy step should refuse any `bin/simple` candidate that fails a positive
subcommand probe. A sufficient gate, all three required:

1. `simple test <a spec that passes>` exits 0 and reports `N passed`
2. `simple test <a spec that fails>` exits nonzero and reports `N failed`
3. `simple lint <a file with known findings>` exits nonzero with a findings line

Banner text and byte size are both insufficient: this binary had a plausible
banner and a size inside the canonical band.

`test/02_integration/simple_launcher_dispatch_spec.spl` already covers in-process
subcommand dispatch and would have caught this had it been run against the
candidate before deploying.
