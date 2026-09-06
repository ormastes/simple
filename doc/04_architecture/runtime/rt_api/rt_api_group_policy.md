# RT API group policy

**Status:** active, enforced ADVISORY (`push-rt-api-groups`).
**Measurements:** `doc/01_research/runtime/rt_api/rt_api_group_census_2026-09-06.md`.
**Registry:** `config/api/api_registry.sdn` (generated mirror of the tree).
**Overrides:** `config/api/api_group_overrides.sdn` (the one curated input).
**Frozen baseline:** `scripts/check/rt_api_group_baseline.txt` (the reviewed floor).
**Gate:** `scripts/check/check-rt-api-groups.shs`.

---

## The rule

> **No product code calls an `rt_*` symbol one-off. All `rt_*` access goes
> through SOSIX or through a named API GROUP's provider.**

Today `src/` holds **6269** forbidden direct `rt_*` call sites against **1712**
distinct symbols. Those symbols belong to **181** groups — so the entire ad-hoc
surface is reachable through 181 entry points, ~35 call sites each. That ratio
is the whole argument: 181 seams are reviewable, 6269 are not.

This is a **ratchet, not a flag day.** Nothing existing is broken by this
policy. What it forbids is *growth*: a new ungrouped `rt_*` API, and a group
whose direct call sites increase.

---

## 1. What an API GROUP is

A group is a named set of runtime symbols that share one boundary and one
owner. Every `rt_*` symbol belongs to exactly one, recorded as a row in
`config/api/api_registry.sdn`.

Groups are **derived, not invented** (the derivation and why alternatives were
rejected are in the census, §3):

- `family` = the first `_`-delimited token after `rt_`
  (`rt_vulkan_create_device` → `vulkan`).
- A family with **>= 5 distinct symbols is a group**.
- Everything smaller falls into the residual group **`misc`** — *not* `core`,
  which is a real family (`rt_core_*`).

`misc` is not an API group. It is 417 symbols and 828 call sites of work
queue, kept visible precisely so it can be split. A family that grows past 5
symbols becomes its own group at the next regeneration, automatically.

Adding a group is not a design act: define 5+ symbols with a shared prefix and
regenerate. What *is* a design act is naming its provider.

**A symbol in `misc` is UNGROUPED, and the gate errors on a new one**
(added 2026-09-06 — see §7 for why the first cut could not). The frozen
`scripts/check/rt_api_group_baseline.txt` lists the 417 admitted today; any
symbol that lands in `misc` and is not on that list FAILs. The remedy is
**not** a wider baseline: it is a row in `config/api/api_group_overrides.sdn`
assigning the symbol to a group that already exists. That file is the only
hand-maintained input the generator reads, every row carries a reason, and it
cannot invent a group — a genuine new group is still 5+ symbols sharing a
prefix, which the heuristic forms on its own.

Seeded 2026-09-06 with 7 rows on the evidence that the symbol operates on the
group's own subject matter: `rt_readdir_{count,entry,free}` → `dir`
(directory enumeration), `rt_utf8_{validate,find_invalid,count_codepoints,
width}` → `string` (UTF-8 over string storage).

## 2. What an allowlisted provider is

A provider is the file or directory permitted to hold direct `rt_*` calls into
a group, because it **is** the runtime boundary — the place where the unsafe,
untyped, ABI-shaped call is written once so nothing else has to.

This policy invents no new notion of provider. A provider is exactly an entry
in `scripts/check/no_direct_rt_allowlist.txt` — the same 93 entries
`check-no-direct-rt.shs` has always honoured, in the same three forms (exact
path, trailing-slash directory prefix, `suffix:`). Typical entries:
`src/lib/nogc_sync_mut/sffi/`, `src/lib/**/ffi/`, `src/runtime/simple_core/`,
`suffix:_sffi.spl`.

A group's `provider` column is **measured**: the allowlist entry that already
serves the most of that group's allowlisted calls. A group with no such entry
is recorded `access: unowned` with `provider: "-"`.

**43 of 181 groups are `unowned`** (48 of 180 before 2026-09-06). That is the
honest state. `unowned` is a debt marker, never a licence to call directly —
it means the seam has not been built yet, and the fix is to build it, not to
widen the allowlist.

**Naming a provider that already exists is not widening the allowlist**, and
is exactly Stage 1's "naming *or* creating". The criterion applied 2026-09-06,
recorded in `no_direct_rt_allowlist.txt` beside the entries so it can be
re-checked: **100% of the group's direct `rt_*` call sites under `src/`
already live in one file, AND that file's role is the ABI seam itself** — a
shim, a bridge, a hosted backend, a platform-event demultiplexer — rather than
logic that merely happens to call the primitive. Five groups met it:

| group | provider named | sites moved |
|---|---|---|
| `driver` | `src/os/kernel/net/driver_shim.spl` | 33 → 0 |
| `cocoa` | `src/os/compositor/hosted_backend_cocoa.spl` | 31 → 0 |
| `sdl` | `src/lib/editor/70.backend/gui_sdl_bridge.spl` | 19 → 0 |
| `kqueue` | `src/lib/nogc_async_mut/io/platform_event.spl` | 7 → 0 |
| `iocp` | `src/lib/nogc_async_mut/io/platform_event.spl` | 7 → 0 |

Deliberately **not** closed, though single-file: `display`
(`src/os/kernel/arch/riscv64/display.spl`) and `limine`
(`src/os/kernel/boot/limine_boot_aarch64.spl`) are ordinary arch/boot code
that happens to be the only current caller, not declared seams — naming them
would be inventing ownership. The remaining 43 stay red; the biggest
(`arm64` 75 sites, `dma` 61, `port` 53, `x86` 46, `arm32` 42) each spread
across many kernel files and need a seam BUILT, which is Stage 1 work, not a
line in a list.

## 3. When SOSIX is the required path, and when a group is

**SOSIX is required for host OS process and platform operations.** Where a
`sosix_*` name exists, tools and apps depend on it and never on the underlying
primitive — that is the whole point of the facade
(`src/lib/nogc_async_mut/sosix/host_facade.spl`): a future Windows backend, and
later SimpleOS binding the same names, swap in behind one seam. The POSIX path
costs nothing; the pass-throughs are `@always_inline`. Registry rows carry
`access: sosix`.

Current SOSIX surface (7 entry points): `sosix_platform`, `sosix_run`,
`sosix_spawn`, `sosix_is_running`, `sosix_kill`, `sosix_proc_usage`,
`sosix_which`.

**A group is the required path for everything else** — graphics (`vulkan`,
`metal`, `sdl2`), compute (`cuda`, `torch`, `simd`), value representation
(`array`, `string`, `enum`, `bytes`), I/O (`file`, `io`, `dir`), and the rest.
Registry rows carry `access: group`.

Decision order for any new call:

1. Is there a `sosix_*` name for it? Use it. Done.
2. Is there a typed std alias in the registry's `alias` column
   (462 symbols have one)? Use it. Done.
3. Otherwise the call belongs **inside the group's provider**, behind a typed
   function the caller uses instead. If the group is `unowned`, creating that
   provider is the change; adding one more direct call is not.

## 4. Migration path for the existing 6269 sites

A flag day is impossible and has never been attempted here. The path is four
ratchets that already interlock:

**Stage 0 — freeze.** Every symbol is registered with a group and its current
site count. `check-rt-api-groups.shs` fails a new unregistered `rt_*`, a new
UNGROUPED one (`misc`, absent from the frozen baseline), a stale baseline
entry, and any group whose sites exceed its **frozen** budget. Landed
**advisory** because it is brand new; it records its verdict before it blocks,
following the `push-parser-source-global-ratchet` precedent.

**Stage 1 — own the groups.** Drive `unowned` from 48 to 0 by naming or
creating a provider for each. This is the only stage that needs design work.
Progress is one number: `access=unowned` in the registry. **43 remain**
(2026-09-06); the criterion for naming one is in §2.

**Stage 2 — collapse the biggest groups.** Work highest-leverage first, by
sites-per-symbol: `enum` (179 sites / 7 symbols), `bytes` (210/10),
`env` (283/14), `time` (221/23) — each is a handful of typed wrappers for a
large fraction of the debt. `file` (808/82) and `array` (268/79) are the volume
targets. Each landed batch lowers the group's registry count, and the ratchet
holds the new floor.

**Stage 3 — split `misc`.** 417 symbols, 828 sites. As sub-families reach 5
symbols they become groups automatically at regeneration; smaller ones move by
an `api_group_overrides.sdn` row. Progress is one number: `ungrouped` lines in
`scripts/check/rt_api_group_baseline.txt`, which only ever goes down —
`--generate-baseline` re-freezes it, and it is for reviewed updates only. Do
NOT run it to clear a FAIL without reading the diff.

**Stage 4 — promote to blocking, then critical.** When the gate has run green
through a release cycle, flip `push_blocking: true` in
`config/check/must_check_gates.sdn`. `--critical` (already implemented, and
honestly RED today) fails on any `unowned` group and is the bar for
mission-critical lanes — the same phase-A/phase-C shape
`check-no-direct-rt.shs --critical` already uses.

Nothing in this policy relaxes an existing gate. `check-no-direct-rt.shs` keeps
its global baseline; this gate adds a **per-group** floor on the same
population, which is strictly stronger — a lane can no longer add 40
`rt_vulkan_*` calls and stay green by deleting 40 `rt_file_*` ones.

## 5. The registry, and why one schema covers every surface

`config/api/api_registry.sdn` — beside `config/check/must_check_gates.sdn`,
because it is a canonical cross-cutting database read by more than one
consumer, not a gate's private baseline. (`scripts/check/*.txt` is where a
single gate's baseline lives; this is not that.)

Two SDN tables:

```
api_groups  |surface, group, symbols, sites, provider, access|
api_symbols |surface, group, symbol, lane, backing, class, sites, twin, alias, desc|
```

`surface` is a column, not a file: `rt`, `hal`, `sosix`, `stdlib` all live in
one database with one reader, because the question — *which group, and who may
call it* — is identical for each. The `rt` surface is fully populated (4163
symbols, 181 groups); `sosix` carries its 7 real entry points; `hal` and
`stdlib` are seeded rows awaiting the same census treatment.

Column meanings:

| column | meaning |
|---|---|
| `lane` | `both` / `c` / `rust` / `none`. **C and Rust**, not C and Simple — the Simple side is `twin`. `none` = called but defined in neither lane. |
| `backing` | `nm` / `text` / `unbacked` — *which instrument* saw the symbol. `extern-backing-census.shs` remains the authority on backing; this records provenance, it does not re-derive it. |
| `class` | `rt_alias_map.sdn`'s migration class: `same` / `adapted` / `provider` / `missing` / `unclassified`. |
| `sites` | forbidden direct call sites under `src/` at generation time. **Informative, not the floor** — the floor is `scripts/check/rt_api_group_baseline.txt`; see §7. |
| `twin` | a Simple twin is recorded in `doc/08_tracking/c_migration/c_migration_inventory.sdn`. |
| `alias` | typed std alias `module.fn`, or `-`. |
| `desc` | one line, **mechanically derived from the symbol name** unless a group owner has replaced it. A placeholder, not prose. |

**Rows are generated, never hand-edited**:
`sh scripts/check/gen-api-registry.shs`. Editing a row by hand makes the
registry disagree with the tree at the next regeneration. The one curated
input is `config/api/api_group_overrides.sdn`
(`api_group_overrides |surface, symbol, group, reason|`), which the generator
reads and applies with precedence over the family heuristic.

Reader: `src/lib/common/api_registry.spl` (`api_registry_parse`,
`api_registry_group_of`, `api_registry_provider_of`, `api_registry_groups`,
`api_registry_symbols_in`), pinned by
`test/01_unit/lib/api_registry_spec.spl`.

## 6. The gate

```sh
sh scripts/check/check-rt-api-groups.shs                     # default ratchet
sh scripts/check/check-rt-api-groups.shs --census F          # + stale-row check
sh scripts/check/check-rt-api-groups.shs --critical          # unowned groups fail
sh scripts/check/check-rt-api-groups.shs --selftest          # 15 fixtures, fatal
sh scripts/check/check-rt-api-groups.shs --generate-baseline # reviewed re-freeze ONLY
```

Verdict is always the last stdout line; a run that checked 0 things is
`ERROR`, never a pass. Measured 2026-09-06 at `c26107f3306`, ~1s:

```
PASS — 15 selftest fixture(s) checked
PASS — 4064 rt_* symbol(s) checked, 0 unregistered, 0 newly ungrouped, 0 group(s) over budget, 0 stale baseline entries, stale-row check OFF (no --census), 43 group(s) still unowned
FAIL — critical mode: 4064 rt_* symbol(s) checked, all registered and grouped, but 43 group(s) have no allowlisted provider (access=unowned)
```

With the full census (`rt-dual-implementation-census.shs --out F`, 2,680 rows,
~2 min) the universe is the whole registry rather than the text-visible slice,
and the stale-ROW check turns on:

```
PASS — 4163 rt_* symbol(s) checked, 0 unregistered, 0 newly ungrouped, 0 group(s) over budget, 0 stale baseline entries, stale-row=0, 43 group(s) still unowned
```

Each failing condition, demonstrated against the real tree rather than only a
fixture (injected, measured, reverted — 2026-09-06):

```
# a new rt_* symbol nothing registered
FAIL — 4065 rt_* symbol(s) checked, 1 unregistered, 0 ungrouped ...; rt_zzznew_widget
# ...and after applying the old remedy, `gen-api-registry.shs`, which used to
# make this green by dropping the symbol into `misc`:
FAIL — 4065 rt_* symbol(s) checked, 0 unregistered, 1 ungrouped (in `misc`, not in the frozen baseline), ...; ungrouped:rt_zzznew_widget
# three new direct rt_file_* calls from a non-provider file
FAIL — 4064 rt_* symbol(s) checked, ... 1 group(s) over their frozen call-site budget, ...; file:811>808
# a baseline entry that no longer describes the tree
FAIL — 4064 rt_* symbol(s) checked, ... 1 stale baseline entry(ies), ...; stale-baseline:rt_file_exists(now file)
# no floor to measure against
ERROR — nothing was checked (no baseline /nonexistent)
```

**Known limit, stated rather than papered over.** The default universe is
text-derived (definition lines + called symbols) so the gate stays fast enough
for a push hook. `nm` sees ~100 symbols with no greppable definition line, so a
cheap run cannot distinguish "registered and nm-only" from "stale" — the
stale-row check therefore runs only with `--census`, and a brand-new nm-only
symbol is invisible to a cheap run. Pass `--census` on the lane that can afford
the full census (~2 min, it compiles the C runtime).

---

## 7. Why the first cut could not error, and what changed (2026-09-06)

The owner's ask was "not grouped rt api lint error". The first cut of this
gate looked like it delivered that, and partly did. The audit that followed
found two ways it was decoration, and one way it was already real. All three
are recorded here because the difference is the whole value of the gate.

**Already real — registration.** Check A does fire. On the merged tree at
`c26107f3306` it said, unprompted:

```
FAIL — 4076 rt_* symbol(s) checked, 2 ungrouped, 0 group(s) over their call-site budget, stale-row check OFF (no --census); rt_fd_pread rt_fd_pwrite
```

Two symbols had landed in `src/runtime/runtime_native.c` after the registry
was generated. That is not a vacuous check. (Both are now registered; with
`rt_fd_pread`/`rt_fd_pwrite` the `rt_fd_*` family reached 5 and became a
group of its own, which is the heuristic working as designed.)

**Decoration 1 — `misc` counted as a group.** The required remedy for check
A is to run `gen-api-registry.shs`, and that generator drops any family below
5 symbols straight into the residual bucket `misc` and reports it as grouped.
So "ungrouped" only ever meant "absent from the file", never "has no group" —
and one command turned the former into the latter with no reviewer input.
Fixed by treating `misc` as what §1 always said it was (not a group) and
ratcheting its population against a frozen list, with
`api_group_overrides.sdn` as the remedy that actually assigns a group.

**Decoration 2 — the floor moved with the debt.** The per-group ratchet read
the `sites` column of the registry, and that same mandatory regeneration
rewrites every `sites` cell. Measured on this tree, one regeneration silently
moved the floor for `misc` (846 → 836) and `port` (55 → 53). A ratchet whose
floor is written by the step you are required to run is not a ratchet. Fixed
by moving the floor into `scripts/check/rt_api_group_baseline.txt`, which the
generator cannot write — only `check-rt-api-groups.shs --generate-baseline`
can, and a verification run rewriting it is a fatal selftest failure
(fixture 12, the same regression fence `check-no-direct-rt.shs` carries).

**Composition, restated.** The per-group budgets ratchet exactly the
population `check-no-direct-rt.shs` calls forbidden, through the same scanner
and the same allowlist, via `rt-call-site-census.shs`. Nothing here relaxes
that gate: after the five providers named in §2 it reads
`PASS — 16261 file(s) scanned (roots=src, src=6145), forbidden=6145 ...
(baseline 7776)`, down from 6261, still far under its own floor.

**Wiring.** Still `push_blocking: false`. It is green at tip and costs ~1s
with no `bin/simple`, so blocking is technically possible — but
`rt-call-site-census.shs` ERRORs without `rg` on PATH, and as a blocking gate
that would block every push from a host without it. Promote to blocking once
the `rg` dependency is either satisfied everywhere or made a documented SKIP,
and once the new ungrouped/frozen-budget semantics have soaked.

**Two limits found while proving the above, recorded rather than papered over.**

*The baseline is frozen from the REGISTRY, not from the cheap scan.* The first
cut froze the 408 `misc` symbols a text scan can see, but the registry holds
417 — nine (`rt_fb_blit32`, `rt_fstring_format`, `rt_lapack_dge{sv,trf,trs}`,
`rt_pointer_{new,ref,deref}`, `rt_vtable_lookup`) are nm-only, invisible to a
grep. A `--census` run, which adds every census symbol to the visible set,
therefore reported those nine as newly ungrouped on a tree nobody had touched.
Fixed: `--generate-baseline` freezes every registry row in `misc`. For the
same reason the "baselined symbol has LEFT the tree" half of the stale-baseline
check runs only under `--census`; the "baselined symbol is now grouped" half
reads the registry and is always decidable.

*A symbol called only from its provider is invisible to this gate.* The
universe is "defined in C/Rust text, or **forbidden**-called from Simple".
Naming the five providers above moved 8 `lane=none` symbols — externs declared
and called nowhere but inside those files — out of the universe entirely
(4171 → 4163, unbacked 908 → 900). That is a pre-existing property of the
generator, newly visible. It is not load-bearing here (`--census` still sees
the whole registry) but it means the cheap universe shrinks as ownership
improves, and a genuinely new provider-only extern would not be caught by a
cheap run. `extern-backing-census.shs` remains the authority on that question.

*An override cannot invent a group, and this is now enforced* rather than only
claimed: `gen-api-registry.shs` exits 2 naming any override row whose group was
not formed by the family heuristic
(`ERROR — nothing was generated (override names a group that does not exist:
rt_typo_sym->notagroup)`).
