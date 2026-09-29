# API surface classification — HAL / SOSIX / group — 2026-09-06

Base: `63924350c16` (`origin/main`). Host: **aarch64** Linux (`uname -m`),
`rg` 15.2.0, GNU awk 5.2.1. No `bin/simple` is deployed in this worktree (`bin/simple` is a
dangling symlink, not executable), so nothing here was measured by running the
compiler; every number is the output of a text scan, and the scanner
definitions are named so each one can be re-run.

**What this doc adds, and what it deliberately does not repeat.** The symbol
census — how many `rt_*` symbols exist, how the family heuristic derives 181
groups, the 35x call-site collapse — is
`doc/01_research/runtime/rt_api/rt_api_group_census_2026-09-06.md`, arriving
with PR #405/#419/#431. That census answers *how many groups*. It does not
answer the owner's actual question, which was **"list up hal api groups sosix,
and other"** — a three-way classification of those groups by which seam they
must route through. That is what this doc measures, plus the one question the
existing lanes explicitly left open: whether the 22 zero-call-site groups are
dead code or unconsumed API surface.

Read this alongside, not instead of, that census.

---

## 0. Instruments, and their limits stated up front

Two scanners, both reusing `check-no-direct-rt.shs`'s own definitions verbatim
so the numbers compose with the gates already in the tree:

```
RT_RE    '^[^#]*\brt_[a-z0-9_]*\('           a direct call-site line
DECL_RE  '^\s*extern\s+fn\s+rt_[a-z0-9_]*\(' an extern declaration, NOT a call
allowlist scripts/check/no_direct_rt_allowlist.txt (exact / dir / suffix: forms)
```

Attribution is per TOKEN, not per line, so a line carrying two calls counts
twice — the same convention `rt-call-site-census.shs` uses and reports.

**Word-boundary trap, recorded because it bit this session.** GNU awk does not
treat `\b` as a word boundary (it is `\y`), so a first pass extracted zero
symbols and a second ad-hoc grep without a boundary reported `rt_v1`,
`rt_complete` and `rt_submit` as real symbols — they are substrings of
`support_v1(`, `..._complete(` and similar. Every count below comes from the
boundary-checked extractor (preceding character asserted non-word), not from
the ad-hoc grep.

Measured at `63924350c16`:

| quantity | value |
|---|---|
| direct `rt_*` call tokens under `src/**.spl` (non-vendor) | 12,482 |
| — allowlisted (inside a declared provider) | 6,052 |
| — **forbidden** (product code reaching past a seam) | **6,430** |
| distinct symbols called at a forbidden site | 1,809 |
| groups those forbidden symbols fall into | 127, plus an `UNREGISTERED` pseudo-group (see below) |
| groups in the registry (all, incl. zero-site) | 181 |

The forbidden total differs from the census's 6,269 because the base commit is
different (`63924350c16` vs `c26107f3306`) and because that census excluded the
five providers named on 2026-09-06. Neither number is wrong; they are two
measurements of a moving tree, and this doc does not claim they are the same
population.

### The registry is already stale at this base, which is the gate working

Joining my scan against the `api_symbols` rows of the enforce lane's
`config/api/api_registry.sdn`: **31 distinct symbols are called from a
forbidden site and appear in no registry row**, across **59 forbidden sites**.
They are a coherent set, not noise — a whole new `rt_cache_host_*_v1` family
(`open_child`, `open_read`, `open_cas_shard`, `secure_temp`, `close`,
`release_daemon_receipt`), plus `rt_secure_temp_dir`, `rt_file_publish_noreplace`
and three `rt_driver_*` names — that landed on `main` after the registry was
generated. `check-rt-api-groups.shs`'s registration check would fire on exactly
this. That is worth stating plainly: the check is **live, not decorative**, and
this is the second independent time it has been shown to fire on real drift
(the first, `rt_fd_pread`/`rt_fd_pwrite`, is in the enforce lane's policy §7).

---

## 1. The three-way classification

The owner asked for HAL groups, SOSIX groups, and other. A three-way split is
only worth anything if each bucket has a criterion that a second person can
re-run and get the same answer. So each bucket below is defined by **measured
predicates**, and where two predicates disagree the disagreement is listed
rather than resolved by taste.

### 1.1 HAL — the machine boundary

The HAL is defined by `doc/07_guide/os/hal/pure_simple_hal.md`: the layer that
touches the machine — registers, ports, MMIO, interrupts, boot, per-arch
primitives. Two independent predicates:

- **P1 (call-site locality).** >= 90% of the group's forbidden call sites are
  under `src/os/**`. Below-OS primitives are called by kernel, driver and boot
  code, essentially nowhere else.
- **P2 (machine backing).** Either **P2a**: fewer than half the group's symbols
  have any host-runtime definition (no C under `src/runtime`, no Rust under
  `src/compiler_rust`) — the host cannot implement it, because it is a machine
  operation; or **P2b**: at least half of its C definitions live under
  `src/runtime/platform/**` or a baremetal file.

**HAL := P1 AND P2.** Seventeen groups qualify, carrying **578 forbidden call
sites**:

| group | sites | syms | host-defined | which predicate |
|---|---|---|---|---|
| net | 76 | 26 | 5 | P2a no-host-def |
| arm64 | 75 | 59 | 0 | P2a |
| arm | 61 | 36 | 0 | P2a |
| port | 53 | 7 | 7 | **P2b** platform-def |
| x86 | 46 | 37 | 0 | P2a |
| hosted | 44 | 25 | 9 | P2a |
| arm32 | 42 | 38 | 0 | P2a |
| boot | 38 | 20 | 0 | P2a |
| rv32 | 26 | 23 | 0 | P2a |
| gui | 25 | 19 | 1 | P2a |
| driver | 24 | 24 | 24 | **P2b** |
| starfive | 21 | 5 | 0 | P2a |
| read | 16 | 10 | 8 | **P2b** |
| display | 11 | 7 | 0 | P2a |
| staged | 9 | 8 | 0 | P2a |
| limine | 6 | 6 | 0 | P2a |
| storage | 5 | 5 | 0 | P2a |

**Two rows inside the AGREEMENT set are doubtful, and are flagged rather
than hidden.** `hosted` (44 sites) and `gui` (25 sites) satisfy both
predicates, but `rt_hosted_*` is the host-machine compositor backend — closer
to the inverse of a machine boundary than to one — and `rt_gui_*` is the
compositor's widget surface. They pass because the compositor lives under
`src/os/**` and is not host-runtime-defined. The mechanical rule has a cost,
and this is where it is paid: 15 of 17 rows are unambiguous, 2 need a human
verdict before they are treated as HAL.

Why two predicates and not one, demonstrated: a single-predicate HAL is wrong
in both directions.

- **P1 alone over-collects.** `array` has 268 forbidden sites, 187 of them
  (70%) under `src/os/**` — it passes an OS-share test comfortably, and it is
  obviously not HAL. It is value representation that the kernel happens to use
  heavily. `bytes` (215 sites, 169 in `src/os`) and `string` are the same
  shape. P2 rejects all three: they are fully host-defined.
- **P2 alone over-collects.** 32 groups satisfy exactly one predicate
  (`winit`, `tls13`, `debug`, `hook`, `ftp`, `gamepad`, `dwarf`, `tar`, `zip`
  …). Most are ordinary userland libraries with no host C/Rust definition
  because they are pure-Simple or unbacked — absence of a definition is not
  evidence of a machine boundary.

**The 32 disagreements, listed rather than silently bucketed.** These are the
rows where P1 and P2 differ, and they are where a human decision is actually
needed. The largest, with the reason each is *not* filed as HAL by the
mechanical rule:

| group | sites | P1 | P2 | reading |
|---|---|---|---|---|
| winit | 113 | no (85/113 in os) | yes | windowing library; 17 sites in `src/lib` |
| tls13 | 111 | no | yes | crypto, not machine |
| debug | 99 | no (0 in os) | yes | tooling |
| hook | 77 | no (0 in os) | yes | instrumentation |
| hal | 58 | no (0 in os, 20 in compiler) | yes | **the `rt_hal_*` names are the dual-run boundary framework** (`src/lib/nogc_sync_mut/rt_hal/`), not the HAL itself — `check-no-direct-rt.shs` already documents this directory as a false-positive source |
| typed | 44 | yes | no (26/26 host-defined) | host-implemented, called from os |
| cocoa | 31 | yes | no (12/12 host-defined) | a hosted macOS backend, owned since PR #405 |
| criticality | 31 | no (31 in compiler) | yes | `rt_criticality_*` are **compiler analysis predicates**, not runtime calls — the documented false-positive population |
| win32 | 26 | yes | no | host-defined Windows backend |
| host / simpleos / browser / driver-adjacent | 17-24 | yes | no | host-defined, os-called |

Two of these deserve emphasis because they inflate every raw `rt_*` count in
the tree: **`hal` (58 sites) and `criticality` (31 sites) are not runtime calls
at all.** `rt_expr_dispatches`, `rt_block_allocates` and friends are compiler
predicates that merely follow the `rt_` naming convention. Any policy that
counts them as runtime access is counting 89 sites that can never be migrated.

### 1.2 SOSIX — the host-OS boundary

**What SOSIX actually is in this repo — two trees, not one.** This matters,
because the enforce lane's policy §3 describes only the first and puts its
surface at "7 entry points", which is a substantial understatement.

| tree | what it is | measured |
|---|---|---|
| `src/lib/nogc_async_mut/sosix/` | the **hosted capsule** — the seam host tools depend on. 7 modules: `host_facade`, `fs`, `sync`, `posix`, `time`, `file_driver`, `__init__` | **29 exported names**, 13 importing files under `src/`+`test/` |
| `src/os/sosix/` | **SimpleOS-internal**, 61 `.spl` files. Calls `os.userlib.syscall_raw.syscall`, imports `os.kernel.errno`, has no host backend | not part of the host seam; deliberately reuses the vocabulary |
| `src/lib/common/contracts/sosix/` | the **shared vocabulary**: 7 contract modules — `operation_v1`, `file_operation_v1`, `completion_v1`, `wait_v1`, `error_v1`, `capability_ref_v1`, `service_ids_v1` | both trees bind these |

The contracts are the load-bearing part. SOSIX is not "the process facade"; it
is *the set of operation classes both a host backend and SimpleOS can bind
behind identical names*. `host_facade.spl` says so directly: tools depend on
`sosix_*` names "so a future Windows backend (and, later, SimpleOS binding the
same names) can be swapped in behind one seam".

**Measured surface: 29 exported names, not 7.** The `__init__.spl` export block
publishes `SosixRun`, `SosixProcUsage`, `sosix_platform`, `sosix_run`,
`sosix_spawn`, `sosix_is_running`, `sosix_kill`, `sosix_proc_usage`,
`sosix_which` (the 7 the policy names, plus 2 types), **and** the `fs` capsule
(`SosixFsSubmit`, `SosixFsTaken`, `SosixHostedFs`), the file driver, the sync
adapter (`sosix_sync_fs_read_at`, `sosix_sync_fs_write_at`), the time leaves,
and the exact-POSIX leg (`sosix_posix_open/close/pread/pwrite` + 3 open-mode
constants).

**One contradiction found, reported rather than resolved.** The `__init__.spl`
docstring says *"The exact-POSIX leg (`posix`) is absent until the
runtime-owned `rt_fd_pread`/`rt_fd_pwrite` externs land"* — but the same file's
export block re-exports `sosix_posix_*`, and `posix.spl`'s own docstring says
"Re-exported from the capsule `__init__` since the 2026-09-05 deploy backs the
pair on this host." The export block and `posix.spl` agree; the `__init__`
docstring is stale prose. I did not run anything to confirm the externs are
backed on this host (no `bin/simple`), so I report the documentation conflict,
not a verdict on the runtime.

**Which rt groups already route through SOSIX (measured, 2 hops).** Hop 1: the
22 distinct `use std.*` targets of the capsule's 7 modules, of which 23 files
resolve. Hop 2: the `rt_*` symbols those files themselves call. 79 symbols, in
12 groups:

```
file 31 | dir 9 | io 8 | time 6 | process 5 | fd 5 | path 4
misc 3  | env 3 | thread 1 | shell 1 | hash 1
```

**Method caveat, stated because the first attempt was wrong by 9x.** Scoping
hop 2 to the *directory* of each resolved module instead of the module *file*
inflates this to 106 groups including `vulkan`, `cuda` and `sdl2` — because
`std.nogc_sync_mut.sffi.fs` resolves into `src/lib/nogc_sync_mut/sffi/`, which
holds every SFFI binding in the tree. The 12-group figure is the file-scoped
one and is the honest answer.

**Criterion for "SOSIX is the required path".** A group is SOSIX-routed iff its
subject is a **host operating-system service that SimpleOS must also be able to
provide** — i.e. it falls under one of the seven contracts. Concretely:
positioned file I/O, directory enumeration, path resolution, descriptor
lifetime, process lifecycle, environment, time, and completion/wait. Everything
in the measured 12 satisfies this. It is also why the bucket cannot be defined
by "has a `sosix_*` name today": that would freeze the facade at its current
size and make the policy circular.

**The SOSIX gap — POSIX-shaped groups the capsule does NOT yet cover:**

| group | forbidden sites | why it belongs to SOSIX |
|---|---|---|
| `env` | 283 | environment is contract-shaped and SimpleOS must provide it; the capsule imports `nogc_async_mut.env` but publishes no `sosix_env_*` name |
| `time` | 221 | `time.spl` exists in the capsule; 221 sites still call `rt_time_*` directly |
| `process` | 200 | `sosix_run`/`sosix_spawn`/`sosix_kill` exist and cover part of it |
| `io` | 183 | partially covered via `fs`/`sync` |
| `file` | 808 | the largest group in the tree; `fs` + `posix` cover positioned I/O only |
| `socket` | 8 | no contract yet; SimpleOS will need one |
| `pty` | 4 | no contract yet |

That is the concrete Stage-1 work list for SOSIX, and it is ~1,700 call sites —
about 26% of the entire forbidden population — behind **one** facade rather
than seven group providers. This is the strongest single argument in the whole
policy: SOSIX is not one seam among 181, it is the seam with by far the best
ratio.

### 1.3 Other — everything with no OS analogue

The residual, 130 of 181 groups (181 total, less 17 HAL, less 22 unconsumed, less the 12 SOSIX-reachable). Its criterion is negative and deliberately so:
a group is `group`-routed when it is neither a machine primitive (no HAL) nor
an operating-system service SimpleOS would have to provide (no SOSIX). In
practice three coherent families:

- **Graphics / windowing:** `vulkan` (110 syms), `metal`, `sdl2`, `sdl3`,
  `opengl`, `glfw`, `winit`, `font`, `image`.
- **Compute / ML:** `torch` (139), `cuda`, `rocm`, `opencl`, `oneapi`, `simd`,
  `blas`, `math`.
- **Value representation:** `array` (74 syms / 268 sites), `string` (69),
  `bytes` (10 syms / 210 sites), `enum` (7 syms / 179 sites), `dict`, `ptr`.

These have no OS analogue: SimpleOS will not "provide" a Vulkan device or an
array header, so routing them through a POSIX-shaped facade would be a category
error. They belong behind a named group provider — which is exactly what PR
#405/#419 already builds.

### 1.4 The three-way split, summarised

| bucket | groups | forbidden sites | criterion |
|---|---|---|---|
| **HAL** | 17 | 578 | P1 (>=90% sites in `src/os`) AND P2 (no host def, or platform/baremetal C def) |
| **SOSIX** | 12 measured today, 14 target (`socket`, `pty` added; the other five gap rows are already among the 12, partially covered) | 1,700+ target | subject falls under a `std.common.contracts.sosix.*` operation class |
| **other (group)** | 130 | remainder | neither of the above |
| *disagreement* | 32 | — | P1 and P2 differ; listed in §1.1, decided case by case |
| *unconsumed* | 22 | 0 | no Simple call site at all — see §2 |

The buckets are not disjoint by construction and one group (`driver`) is both
HAL by measurement and already owned by a provider. Where a group is both HAL
and SOSIX-shaped, HAL wins: the machine boundary is below the OS boundary.

---

## 2. The 22 zero-call-site groups: unconsumed surface, not dead code

The owners lane (PR #431) established that 22 of the 43 unowned groups have
zero call sites anywhere under `src/**.spl`, and correctly concluded that they
**cannot be owned under the current provider derivation, ever** — a provider is
derived from allowlisted call sites, and a group with no call sites has none.
It filed that as a blocker on promoting `--critical` and left the dead-vs-alive
question open. This section answers it.

**Independent replication first.** My scan reproduces exactly the same 22
names from a different scanner and a different base commit:
`ab aop blas btreemap btreeset clear contract generator handle hashmap hashset
mlkem monoio object par resource security semaphore sffi shared unique vec`
— 304 symbols in total.

**The discriminator.** A group is dead only if its symbols appear nowhere
except their own definition. So each symbol was looked for in three other
surfaces: `src/compiler/**/*.spl` (codegen emits `rt_*` names as string
literals), `src/compiler_rust/**/*.rs` and `src/runtime/**/*.{c,h}` (runtime
lanes referencing each other), and `test/**/*.spl`.

| group | syms | in compiler `.spl` | in Rust | in C | in tests | verdict |
|---|---|---|---|---|---|---|
| monoio | 67 | 0 | 67 | 0 | 0 | runtime-internal |
| security | 30 | 0 | 30 | 0 | 0 | runtime-internal |
| vec | 27 | 0 | 27 | 13 | 13 | runtime-internal |
| par | 21 | 0 | 21 | 3 | 3 | runtime-internal |
| **sffi** | 19 | **5** | 19 | 0 | 0 | **codegen-abi** |
| btreeset | 16 | 0 | 16 | 0 | 0 | runtime-internal |
| hashset | 14 | 0 | 14 | 0 | 0 | runtime-internal |
| btreemap | 13 | 0 | 13 | 0 | 6 | runtime-internal |
| hashmap | 11 | 0 | 11 | 0 | 6 | runtime-internal |
| generator | 10 | 0 | 10 | 2 | 2 | runtime-internal |
| ab | 9 | 0 | 0 | 9 | 0 | runtime-internal |
| resource | 8 | 0 | 8 | 0 | 0 | runtime-internal |
| blas | 7 | 0 | 0 | 7 | 3 | runtime-internal |
| semaphore | 7 | 0 | 7 | 0 | 0 | runtime-internal |
| shared | 7 | 0 | 7 | 2 | 2 | runtime-internal |
| clear | 6 | 0 | 6 | 1 | 0 | runtime-internal |
| mlkem | 6 | 0 | 0 | 6 | 0 | runtime-internal |
| object | 6 | 0 | 6 | 0 | 0 | runtime-internal |
| aop | 5 | 0 | 5 | 0 | 0 | runtime-internal |
| **contract** | 5 | **1** | 5 | 0 | 0 | **codegen-abi** |
| handle | 5 | 0 | 5 | 2 | 2 | runtime-internal |
| unique | 5 | 0 | 5 | 2 | 2 | runtime-internal |

**Result: zero of the 22 are dead. Not one has "no reference".** 20 are
**runtime-internal** — defined and used entirely within the Rust or C runtime,
never crossing into Simple. 2 are **codegen-ABI** — named as string literals by
the compiler, which emits calls to them; `rt_sffi_*` is the clearest case, with
5 of its 19 symbols appearing in `src/compiler/**/*.spl`.

**What this means for policy, and it is decisive.** These groups are not
migration debt and they are not deletable:

- Deleting them breaks the runtime (`monoio` is the async I/O core; `hashmap`,
  `btreemap`, `vec` are the collection ABI) or breaks codegen (`sffi`).
- Owning them is *impossible by construction*, not merely undone. Requiring a
  provider for a symbol Simple never calls is requiring a seam with nothing on
  either side of it.

So the policy needs a third access class beyond `group` and `unowned`, and it
must be earned by measurement rather than declared:

- `access: runtime-internal` — 0 call sites under `src/**.spl`, referenced in a
  runtime lane. 20 groups, 280 symbols.
- `access: codegen-abi` — 0 call sites, but named by `src/compiler/**/*.spl`.
  2 groups, 24 symbols.

Both stay **registered** (so a new symbol in them is still caught by the
registration check) and are **exempt from provider ownership**. With those two
classes applied, the `--critical` mode's unowned population falls from 43 to
**21** — and 21 groups needing a seam BUILT is a finite, fundable work item,
whereas 43 including 22 unownable ones is a gate that can never go green.

**Limit of this finding.** "Runtime-internal" is measured by text reference,
not by linkage. A symbol could be referenced in a Rust file and still be dead
(e.g. only in a comment). `extern-backing-census.shs` remains the authority on
whether a symbol is genuinely backed; this classification answers only "is
anything other than its own definition referring to it", which is the question
that separates *unconsumed* from *dead*.

---

## 3. The stdlib surface — the same question asked of `src/lib`

The owner's fourth ask was "db like access to all other api also". The rt
registry's schema was designed to generalise (its `surface` column already
admits `hal`, `sosix`, `stdlib`), but nothing had ever populated a non-`rt`
surface, so the claim was untested. This section tests it by populating one.

**The analogy that makes the schema transfer.** On the rt surface, the thing
being ratcheted is a *forbidden direct call*: a consumer reaching past the
declared seam to touch the primitive. The stdlib has an exact structural
equivalent — a **bypass import**. `src/lib/<space>/<family>/__init__.spl` is
the module `use std.<space>.<family>` resolves to; it *is* the provider. A file
outside the family that writes `use std.<space>.<family>.<submodule>` has
reached past it, pinning itself to an internal file so the family can no longer
reorganise behind its own facade. Same defect, same countable unit, same
ratchet.

Measured for the `nogc_async_mut` space (the space SOSIX lives in), by
`scripts/check/gen-stdlib-api-registry.shs`:

| quantity | value |
|---|---|
| families (dirs under `src/lib/nogc_async_mut/` with an `__init__.spl`) | 83 |
| public symbols across them | 2,709 |
| families publishing a surface (`access: group`) | 76 |
| families publishing nothing (`access: unowned`) | 7 |
| **bypass imports from `src/`** | **549** |
| bypass imports from `test/` (excluded from `sites`, reported in the header) | 956 |

Worst offenders, and the shape of the problem:

| family | published symbols | bypass imports from `src/` |
|---|---|---|
| `nogc_async_mut.io` | 186 | 132 |
| `nogc_async_mut.engine` | 16 | 94 |
| `nogc_async_mut.mcp` | 319 | 84 |
| `nogc_async_mut.test_runner` | 1 | 49 |
| `nogc_async_mut.gpu` | 111 | 29 |
| `nogc_async_mut.concurrent` | **0** | **17** |
| `nogc_async_mut.sosix` | 29 | **0** |

Two rows carry the whole argument. `nogc_async_mut.concurrent` publishes
*nothing* and has 17 consumers — every one of them is forced to reach inside,
because there is no seam to route through. That is `access: unowned` on the rt
surface, in the stdlib, with the same meaning and the same remedy.
`nogc_async_mut.sosix` is the opposite pole: 29 published names, **zero** src/
bypasses. Its only deep imports are its own 7 spec files, which legitimately
test submodules. (That spec-file breakdown came from an ad-hoc grep, not from
the generator; the generator reports the src/ and test/ totals, not per-file
provenance.) SOSIX is not just the seam the policy recommends — it is,
measurably, the best-encapsulated family in its space.

**A false finding from the first cut, recorded because it nearly shipped.**
The generator's first version handled only `export use m.{X, Y}` and reported
**70 of 83 families as publishing nothing**, with `engine`, `mcp` and
`test_runner` among them. That was a scanner artifact. The tree publishes
through four distinct forms, and three were being dropped:

1. `export use std.a.b.{X, Y}` — the only one the first cut saw
2. `export X, Y, Z` — a bare name list (this is what `mcp` and `gpu` use)
3. `export mod.*` / `export use std.a.b.*` — a wildcard (this is what `engine`
   and `test_runner` use); its name set is not statically enumerable, so it is
   recorded as one row naming the wildcard rather than expanded or dropped
4. `pub fn X` / `pub val X` / ... declared in `__init__.spl` itself

With all four supported the real numbers are the ones in the table above:
**76 of 83 families do publish a surface**, and the problem is not a missing
facade but 549 consumers bypassing facades that exist. Fixture 5 of the
generator's selftest is a permanent regression fence for exactly this, and was
verified to discriminate by sabotaging the form-2 handler and confirming the
fixture fails.

**Generalisation, and its honest limit.** The generator takes `--space` and the
same scan applies to all five memory spaces; only `nogc_async_mut` is populated
here, because "one family done properly beats a stub covering everything". The
untested part of the claim is `src/lib/common/`, which is organised by topic
rather than by capsule and may not follow the `__init__.spl` provider
convention as cleanly. That is unmeasured, and is named as unmeasured.

---

## 4. What was measured versus what was inferred

**Measured** (a command produced the number; re-runnable from this base):

- All call-site, symbol, group, lane, definition-site and bypass counts.
- The 22 zero-call-site groups and their references in the three other
  surfaces — replicated independently of PR #431's census.
- The SOSIX capsule's 29 exported names, 13 consumers, 0 src/ bypasses; the 7
  contract modules; the 12 rt groups reachable in 2 file-scoped hops.
- The 31 registry-stale symbols across 59 forbidden sites.
- The stdlib registry for `nogc_async_mut`: 83 families, 2,709 symbols, 549
  bypasses.

**Inferred** (a judgement on top of the numbers; a reviewer may disagree):

- That P1 AND P2 is the right HAL criterion. The predicates are measured; the
  conjunction is a choice, defended by showing each predicate alone
  misclassifies (`array` under P1, `winit` under P2).
- That the 12 SOSIX-reachable groups *should* grow to include `env`, `time`,
  `socket` and `pty`. Their contract-shape is a reading of the seven contract
  modules, not a measurement.
- That `runtime-internal` and `codegen-abi` are the right exemption names.
- That 549 bypass imports are a defect rather than deliberate design. Each one
  was counted, none was individually adjudicated.

**Not measured, and not asserted:**

- Nothing was compiled, linked or executed. No `bin/simple` in this worktree.
- Whether `rt_fd_pread`/`rt_fd_pwrite` are genuinely backed on this host — only
  the documentation conflict about it is reported.
- Whether any of the 304 unconsumed symbols is dead in the linkage sense.
- The `src/lib/common/` stdlib surface.
- `simple_ctx_*` MCP tools returned empty results for every call this session,
  as they did for the enforce lane. **No ctx source labels exist for this
  work**; every number here came from `rg`/`awk` in the worktree.
