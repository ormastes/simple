# EntryClosureReceiptV1 — measuring an entry point's import closure

Status: **v1, frozen for the L5 wave (2026-09-12).** Producer
`scripts/perf/measure-entry-closure.shs`; consumer/ratchet
`scripts/check/check-entry-closure-ratchet.shs`; frozen numbers
`config/perf/entry_closure_baselines.sdn`.

## What this measures, and why it is not "binary size"

The seed reads the stdlib and the application tree as **source** on every process
start — `.claude/rules/commands.md` records 82 `.spl` opens and zero `.smf` for a
trivial run, and nothing is baked into the binary. So what an entry point costs
at startup is not the size of `bin/simple`; it is how many distinct source files
the entry drags in before it does any work.

Two independent effects inflate that, and they have different fixes, so the
receipt reports them separately:

1. **Alias spellings and cross-lane reads.** One physical file opened under
   several path strings (`src/app/x.spl`, `./src/app/x.spl`, an absolute path),
   and read once by the HIR lowerer and again by the interpreter with no shared
   cache. This is a seed design item (L5-E). It inflates `spl_opens` and
   `unit_spellings`; it does **not** change `physical_files`.
2. **Genuinely eager imports.** A hub module pulled in by an entry that uses a
   handful of leaf functions. This is fixed in pure Simple by importing the leaf
   owner. It changes `physical_files` and `source_bytes_physical`.

**Only the physical pair is ratcheted.** Freezing `spl_opens` would report
L5-E's caching work as an import regression, and would make an import fix look
smaller than it is.

## Execution lane (contract amendment, 2026-09-12)

`--lane default|interpreter` selects how the measured process executes:

| lane | environment | what it is |
|---|---|---|
| `default` | `SIMPLE_EXECUTION_MODE` **unset** | the JIT-attempt lane, which whole-module-compiles |
| `interpreter` | `SIMPLE_EXECUTION_MODE=interpreter` | the tree-walk lane |

The two lanes have **different closures for the same entry**. L5-C found that a
function-local `use` shrinks only the interpreter lane while the default lane
still pulls the module in, so a closure number without a lane is ambiguous, and a
per-entry-only baseline would let a real default-lane regression hide behind an
interpreter-lane improvement. `lane` is therefore recorded in the receipt (last
column) and the baselines are keyed by `(entry_id, lane)`, both ratcheted
independently. Measured on `lspmcp-help`: default 122 opens / 51 spellings,
interpreter 83 / 62 — same 38 physical files.

`env -u SIMPLE_EXECUTION_MODE` is applied before the lane's own setting, so an
inherited value in the caller's shell cannot turn a `default` measurement into an
interpreter one.

## Cold measurement, and one thing that does NOT work

A warm content cache can serve source without an `openat` and silently
under-report the closure. Two defences:

1. **Hermetic `HOME`** (default; `--keep-home` opts out). The measured process
   gets a fresh empty `HOME`, so nothing under `~/.simple` can suppress a read.
   Measured 2026-09-12: an empty `HOME` leaves the `.spl` spelling set
   byte-identical (178 both ways for `mcp-help`) while removing 1,371 unrelated
   `openat` calls — it changes what is *not* measured, not what is. Confirmed
   across the whole set afterwards: every one of the ten default-lane physical
   numbers is byte-identical to a pre-hermetic run, `test-one-spec` (the entry
   most likely to read `$HOME`) included at 352 / 3,004,187.
2. **`--verify-cold`**: trace the entry a second time in the same environment and
   require an identical physical set. Anything the first run warmed shows up as a
   smaller second set. Used when recording a baseline, not on every check.
   Verified on `lspmcp-help` 2026-09-12: cold-stable.
3. **A killed run is refused.** `timeout` leaves a log that is *complete up to the
   kill*, so a timed-out entry parses cleanly and yields a SMALLER closure — which
   reads as an improvement and would be frozen as the baseline. rc 124/137/152 is
   therefore an ERROR. A non-zero exit from the entry itself is still accepted
   (`mcp-info-call` exits 1 on the E1002 below); it finished loading what it loads.
   All three heavy interpreter-lane pairs were re-run individually and report
   rc=0, so the lane gaps in the table below are completed runs.

**What does not work, stated because it was proposed and is intuitive:**
"detect the warm-cache case by an opens count below `physical_files`". With this
method that is unreachable by construction — every physical file is the realpath
of at least one counted open, so `spl_opens >= unit_spellings >= physical_files`
*always* holds and the check can never fire. A warm cache does not show up as
fewer opens; it shows up as fewer **physical files**, which reads as an
improvement and would sail straight through the ratchet. The inequality is still
asserted, but only as an internal-consistency check on the parser, and it is
labelled as such in the source rather than sold as the cache defence.

## Method — `strace-openat-realpath` (contract-fixed)

```
strace -f -s 4096 -e trace=openat -o <log> timeout <N> <binary> <argv> < <stdin>
```

- A **unit** is any `openat` of a path ending `.spl` that returned ≥ 0.
- `unit_spellings` = distinct path strings. `physical_files` = distinct
  `realpath` of units. `source_bytes_spellings` sums sizes over spellings;
  `source_bytes_physical` sums over physical files.
- `timeout` sits **inside** `strace` so a server entry that never sees EOF is
  killed as the tracee and the log stays complete; with `timeout` outside,
  `strace` itself would be killed and the log could end mid-line.
- The measurement cwd is the repo root of the checkout the script lives in.
  Relative spellings resolve against it, so a run from elsewhere would attribute
  another worktree's files to this tree's closure.
- No environment is set. `SIMPLE_MCP_TOOL_SET` and friends change the closure;
  leaving them unset is what makes a baseline reproducible.

Fail-closed behaviours (each has a selftest fixture):

| situation | handling |
|---|---|
| `= -1 ENOENT` | not a unit |
| `-f` `<unfinished …>` / `<… openat resumed>` split | demuxed by pid; a resumed `-1` still rejected |
| non-ASCII path (3-digit octal from strace) | decoded |
| path strace truncated with `...` | **whole parse ERRORs** — a truncated path stops ending in `.spl` and would be silently dropped |
| a spelling that does not `realpath -e` | ERROR |
| non-native entry opened 0 `.spl` | ERROR |
| `strace` or the binary missing | ERROR |

`wall_ms_p50` / `max_rss_kib` are informative only. This host is shared and
routinely over load 30; **never gate on them**.

## Receipt schema (SDN)

```
entry_closure_receipt |schema, entry_id, argv, cwd, binary_path, binary_sha256, binary_size, binary_mtime_utc, method, spl_opens, unit_spellings, physical_files, source_bytes_spellings, source_bytes_physical, wall_ms_p50, wall_samples, max_rss_kib, measured_at_utc, host_arch, host_load1, lane|
    "simple.entry-closure-receipt/v1", <entry_id>, "<argv joined by U+241F>", <cwd>, <path>, <sha256>, <bytes>, <ISO8601Z>, "strace-openat-realpath", <int>, <int>, <int>, <int>, <int>, <int>, <int>, <int>, <ISO8601Z>, <text>, <float>, "<default|interpreter>"
units |entry_id, spelling, realpath, size, lanes|
    <entry_id>, <path as opened>, <realpath>, <bytes>, "<hir|interp|hir+interp|unknown>"
```

`argv` is joined with **U+241F ␟ SYMBOL FOR UNIT SEPARATOR** — the printable
glyph, not the ASCII 0x1F control byte, so the SDN string stays printable.

`lanes` is `unknown` unless `--lanes` is passed, which costs one extra untraced
run with `SIMPLE_READ_TRACE=1` (`read_trace.rs` prints `[read] <file>:<line>
<path>`). The lane is classified from the **reader's** Rust source path; anything
unrecognised stays `unknown` rather than being guessed. The match is against the
path **as opened** (the spelling), because that is what `read_trace.rs` prints —
matching the realpath instead silently returns `unknown` for every relative
spelling, which is most of them. Verified on `lspmcp-help`: 36 `interp`,
15 `unknown`, 0 `hir` — on that entry nothing traced is read by the lowerer.

## Entry ids (frozen set)

`cli-version`, `cli-help`, `mcp-help`, `mcp-info-call`, `lspmcp-help`,
`lspmcp-3frame`, `query-help`, `check-help`, `lint-one-file`, `test-one-spec`.

| entry_id | argv after the binary | stdin | native |
|---|---|---|---|
| `cli-version` | `--version` | — | yes |
| `cli-help` | `--help` | — | yes |
| `mcp-help` | `run src/app/mcp/main.spl --help` | — | |
| `mcp-info-call` | `run src/app/mcp/main.spl` | `initialize`, `tools/call simple_info` | |
| `lspmcp-help` | `run src/app/simple_lsp_mcp/main.spl --help` | — | |
| `lspmcp-3frame` | `run src/app/simple_lsp_mcp/main.spl` | `initialize`, `tools/list`, `tools/list` | |
| `query-help` | `query --help` | — | |
| `check-help` | `check --help` | — | |
| `lint-one-file` | `lint src/lib/common/net/oid.spl` | — | |
| `test-one-spec` | `test test/01_unit/app/examples_check_entry_args_spec.spl` | — | |

`cli-version` / `cli-help` are **native**: 0 opens is the correct answer for
them, and a 0/0 baseline compares equal and PASSes. Every other entry reporting
0 opens is an ERROR.

### Adding an entry

1. Add a `case` arm to `entry_argv` (and `entry_stdin` / `entry_native_ok` /
   `entry_timeout` if it needs them) in `scripts/perf/measure-entry-closure.shs`,
   and the id to `ENTRY_IDS`.
2. Point it at a **tracked** fixture path hard-coded in the script — a fixture
   chosen at run time makes tomorrow's baseline unreproducible.
3. Add **one row per lane** to `config/perf/entry_closure_baselines.sdn`, each
   with a written reason. An entry with no row is an ERROR, not a skip.

## Usage

```sh
sh scripts/perf/measure-entry-closure.shs <entry_id> --binary <path> --out <sdn> \
    [--lane default|interpreter] [--samples N] [--lanes] [--keep-home] [--verify-cold]
sh scripts/perf/measure-entry-closure.shs --list-entries
sh scripts/perf/measure-entry-closure.shs --parse-log <strace.log> --parse-cwd <dir>
sh scripts/perf/measure-entry-closure.shs --selftest        # 21 assertions over 9 fixtures
```

Binary resolution is `--binary` → `$SIMPLE_BIN` → `<root>/bin/simple` → ERROR.
**The deployed aarch64 seed lacks `rt_env_vars` and is not a usable measurement
binary**; pass a Rust-seed build explicitly.

The verdict is the last line of stdout and carries every number, so a spec can
`tail -1` it:

```
PASS — 239 unit spelling(s) checked for mcp-help lane=default: spl_opens=571 unit_spellings=239 physical_files=131 source_bytes_spellings=2456996 source_bytes_physical=1323864 (binary <sha256>, rc=0)
```

`ERROR — nothing was checked (<reason>)` exits 2. There is deliberately no FAIL:
this is a producer, not a gate.

## Baselines file schema

```
entry_closure_baselines |entry_id, lane, physical_files, source_bytes_physical, recorded_at_utc, binary_sha256, reason|
    <entry_id>, <default|interpreter>, <int>, <int>, <ISO8601Z>, <sha256>, "<reason>"
```

`lane` sits at **position 2, not appended last**: `reason` is free text that may
contain commas, so no column placed after it can be addressed by field index.
(The receipt row is the opposite case — `lane` is appended at the END there, to
keep every pre-existing column at its original position.) One row per
(entry, lane); a selected pair with no row is an ERROR, not a skip.

## The ratchet

```sh
sh scripts/check/check-entry-closure-ratchet.shs [--quick|--all] [--entries a,b] \
    [--lane default|interpreter] [--binary <path>]
sh scripts/check/check-entry-closure-ratchet.shs --update-baseline --reason "<text>"
sh scripts/check/check-entry-closure-ratchet.shs --selftest     # 9 fixtures
```

FAILs when `physical_files` **or** `source_bytes_physical` grows above baseline
for any checked **(entry, lane) pair**, naming the offender as `entry[lane]`;
PASS names every pair with current-vs-baseline. Zero pairs checked is ERROR,
never a pass. `--lane` narrows to one lane; without it, a two-lane entry counts
as two pairs. It never re-implements the strace method
— it shells out to the producer, so the baseline number cannot drift away from
what the receipt means.

`--quick` is the six cheap `--help`-class entries **in both lanes** — 12 pairs,
measured **67.5 s** wall on this loaded shared host — and is what the push tier
runs; `--all` is all 20 pairs (~9 min, mostly `lint-one-file` and
`test-one-spec`) and is what CI's advisory job runs. Both name what they checked.

`--update-baseline --reason "<text>"` is for **reviewed landings only**, the same
philosophy as the tree-size guard's `--expect-files`. A FAIL naming a grown entry
is real new debt; regenerating hides it. The update **edits** the file: every
comment and every row it did not select is carried through byte-for-byte, and it
prints `old -> new` for both numbers of each row it rewrote, so a re-baseline
states what it moved instead of only why. `--entries` narrows an update
regardless of where it appears in the argv (scope is resolved after the whole
command line is parsed). It records the sha256 the **producer** reported, not a
re-hash of whatever the gate thinks the binary is.

Wiring: manifest row `push-entry-closure-ratchet` (`push`, `push_blocking:
false`, `tree`) in `config/check/must_check_gates.sdn`, its exact dispatch case
in `scripts/check/check-push-must-pass.shs`, and an advisory step in
`.github/workflows/repo-hygiene.yml`'s `advisory-gates` job. Advisory because it
**executes** the entry under strace: a host without strace or without a binary
carrying `rt_env_vars` answers ERROR by contract, which as a blocking row would
block every push from such a host — the same class as `push-dual-run-shadow`.

## Baseline, 2026-09-12

Binary `/home/yoon/dev/simple-wave/src/compiler_rust/target/release/simple`,
measured from a clean worktree at `c7c5bef3ca3`. That binary was **rebuilt by
another lane mid-session**, which turned into a free validation of the ratchet's
scope: every entry was measured on both builds and

| build | size | sha256 | `lspmcp-help` opens / spellings / **physical** |
|---|---:|---|---|
| 11:54 | 51,308,600 | `ef528c60…15562` | 158 / 67 / **38** |
| 14:27 | 51,256,576 | `ee2a35f7…a0367` | 122 / 51 / **38** |

**all ten physical pairs came out byte-identical across the two builds**, while
`spl_opens` and `unit_spellings` moved by up to 23 %. That is the ratchet's thesis
measured rather than argued: the physical pair tracks imports, the other two track
how many times the seed re-reads the same file. Rows below and in the baselines
file carry the later sha (`ee2a35f7…`). Approximate wall per traced run on the
11:54 build, for budgeting only: `cli-*` 0.4 s, `lspmcp-help` 3 s, `lspmcp-3frame`
6 s, `check-help` 8 s, `mcp-help` 10 s, `query-help` 11 s, `mcp-info-call` 13 s,
`lint-one-file` 36 s, `test-one-spec` 79 s.

| entry_id | lane | opens | spellings | **physical** | **bytes (physical)** |
|---|---|---:|---:|---:|---:|
| `cli-version` / `cli-help` | both | 0 | 0 | **0** | **0** |
| `mcp-help` | default | 571 | 239 | **131** | **1,323,864** |
| `mcp-help` | interpreter | — | — | **131** | **1,323,864** |
| `mcp-info-call` | default | 571 | 239 | **131** | **1,323,864** |
| `mcp-info-call` | interpreter | — | — | **131** | **1,323,864** |
| `lspmcp-help` | default | 122 | 51 | **38** | **325,005** |
| `lspmcp-help` | interpreter | 83 | 62 | **38** | **325,005** |
| `lspmcp-3frame` | default | — | — | **38** | **325,005** |
| `lspmcp-3frame` | interpreter | — | — | **38** | **325,005** |
| `query-help` | default | 184 | 126 | **125** | **1,262,376** |
| `query-help` | interpreter | — | — | **107** | **1,140,426** |
| `check-help` | default | 200 | 133 | **132** | **1,302,861** |
| `check-help` | interpreter | — | — | **114** | **1,180,911** |
| `lint-one-file` | default | 804 | 507 | **387** | **4,307,651** |
| `lint-one-file` | interpreter | 765 | 530 | **291** | **3,645,845** |
| `test-one-spec` | default | 3,780 | 571 | **352** | **3,004,187** |
| `test-one-spec` | interpreter | — | — | **352** | **3,004,187** |

**The lanes diverge exactly where the check/lint entries live.** `query-help`,
`check-help` and `lint-one-file` are 14–25 % smaller in the interpreter lane with
no code change at all (`lint-one-file` 387 → 291, a 96-file gap, rc=0 — a
completed run, not a truncated one). MCP, LSP-MCP and the test runner are
lane-identical today. This is why both lanes are frozen: an import fix judged only
on the interpreter number would bank a quarter of its target from the lane gap.

Note the `lspmcp-help` lane pair: the interpreter lane has FEWER opens (83 vs 122)
but MORE spellings (62 vs 51) for the same 38 physical files — the two lanes
reach the same sources by different spellings and re-read them different numbers
of times, which is exactly the pair of numbers a baseline must not freeze.

The hermetic `HOME` changed **no** physical number for any of the ten entries:
the default-lane rows above are byte-identical to a pre-amendment run made with
the real `HOME`.

`mcp-help` and `query-help` reproduce the L5 plan's independently measured
ground-truth rows exactly (571/239/131 and 184/126).

Two rows need reading carefully rather than at face value:

- **`mcp-info-call` is identical to `mcp-help`** because the tool call currently
  fails before loading anything extra: `error[E1002]: function
  'project_child_storage_environment' not found` —
  `src/lib/nogc_sync_mut/storage_roots/tooling_paths.spl:67` calls it without
  importing it from `storage_roots/child_environment.spl:49`. That is a
  pre-existing defect, not an artefact of this measurement. The closure up to the
  failure is real and is a valid floor, but if the defect is fixed the closure may
  legitimately grow; re-baseline with a written reason rather than absorbing it.
- **`test-one-spec` has 3,780 opens against 571 spellings** — a 6.6× re-read
  ratio, by far the worst of the ten, and the single loudest piece of evidence
  for L5-E's cross-lane parsed-source cache.

The `--help` entries mostly have `physical ≈ spellings` (`query-help`: 125 of
126), so alias dedup buys them almost nothing; `mcp-help` (131 of 239) and
`lint-one-file` (387 of 507) are where the alias effect is real.
