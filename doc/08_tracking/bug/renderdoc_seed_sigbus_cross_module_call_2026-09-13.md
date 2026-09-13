# Seed SIGBUS (rc 138) on a cross-module call in the renderdoc tooling — 2026-09-13

Status: OPEN. Host: macOS 25.5.0, Apple M4. Binary:
`src/compiler_rust/target/bootstrap/simple` (Rust seed, 2026-09-05 build, 130,402,384
bytes) — the only binary on this Mac that has a `run` subcommand.

## Symptom

`scripts/check/check-renderdoc-web-diff.shs --selftest` cannot run here. It reports:

```
renderdoc_diff_status=blocked:simple-binary-cannot-run
RENDERDOC DIFF: ERROR — nothing was checked (... produced no verdict; it likely has
no 'run' subcommand)
```

The diagnosis in that message is WRONG, and the wrong diagnosis is the most useful
part of this record: the binary does have `run` (a hello-world runs, rc 0). What
actually happens is that the differ aborts with **rc 138** (128 + SIGBUS/10),
**silently** — no stdout, no stderr beyond the usual seed warnings, no Simple-level
error. The gate's liveness probe sees "no verdict line" and attributes it to a
missing subcommand.

```
$ .../bootstrap/simple run src/app/ui/renderdoc_diff/main.spl \
    test/fixtures/renderdoc_diff/identical_a.events.json \
    test/fixtures/renderdoc_diff/identical_b.events.json --out /tmp/rdx
rc=138        # stdout empty
```

## What was bisected

Building a new counter (`src/app/ui/renderdoc_metrics/`) reproduced it from scratch
and let it be narrowed. Each row is a real run on the seed above:

| program | rc |
|---|---|
| hello world | 0 |
| `std.sffi.cli` argv loop with `continue` | 0 |
| `renderdoc_diff.jsonflat` parse of a real events.json | 0 |
| `renderdoc_diff.events` parse of a real events.json | 0 |
| own module's fold + row formatting, synthetic columns | 0 |
| `std.io_runtime` `file_write`/`dir_create_all` call sites | 0 |
| `cli_exit(<variable>)` | 0 |
| main truncated after printing both metric rows (real parse, cross-module fold) | 0 |
| the same main plus ONE more cross-module call taking the folded values | **138** |
| `renderdoc_diff/main.spl` (4 sibling modules) | **138** |

So: not the imports alone, not io, not exit, not the parse. The crash appears when
`main` additionally carries a call site into a sibling module that takes values
produced by an earlier cross-module call. The truncated variant prints three lines;
the full variant prints **nothing at all**, even though its first three statements are
byte-identical and execute before anything new.

That points at a crash **before `main` runs** (JIT-compile time), but it is not
disambiguated: a runtime abort that loses buffered stdout looks the same. Re-running
the differ under `script -q /dev/null` (tty, line-buffered) still produced no program
output, which is consistent with the compile-time reading without proving it — that
program emits nothing until its end either way. Whoever picks this up should settle it
with a debugger rather than inherit the inference.

Rewriting the shapes did not help: primitive-column parameters instead of a class,
a class of arrays, returning a rendered text block instead of a class array — all
138. Collapsing every function into ONE module removed it, which is what
`src/app/ui/renderdoc_metrics/main.spl` does today, with that constraint stated in
its docstring so nobody "tidies" it back into layers and silently breaks the gate.

## Impact

1. `check-renderdoc-web-diff.shs --selftest` is ERROR on macOS, and its message
   misattributes the cause. The 8 alignment fixtures have never been exercised here.
2. Any new pure-Simple tool in this area must be single-module until this is fixed,
   which is at odds with MDSOC layering.

## Not fixed here, and what would fix it

This is a seed-codegen defect, not a Simple-source defect; the correct repair is in
the compiler, not in the callers. It needs a Linux/x86_64 reproduction (the seed
there is a different build) and a JIT-level diagnosis. Until then:

- do not "restore layering" in `src/app/ui/renderdoc_metrics/main.spl`;
- treat `rc=138` with empty stdout from any `simple run` as THIS bug, not as a
  missing subcommand — the liveness probe's wording in
  `check-renderdoc-web-diff.shs` should be widened to say so.

Unblock command for a real re-diagnosis (Linux host with a current seed):

```sh
SIMPLE_SEED=<linux-seed> sh scripts/check/check-renderdoc-web-diff.shs --selftest
```

If that PASSes on Linux, the defect is macOS/aarch64-specific in the seed's JIT.
