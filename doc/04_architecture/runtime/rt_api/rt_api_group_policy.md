# RT API group policy

**Status:** active, enforced ADVISORY (`push-rt-api-groups`).
**Measurements:** `doc/01_research/runtime/rt_api/rt_api_group_census_2026-09-06.md`.
**Registry:** `config/api/api_registry.sdn`.
**Gate:** `scripts/check/check-rt-api-groups.shs`.

---

## The rule

> **No product code calls an `rt_*` symbol one-off. All `rt_*` access goes
> through SOSIX or through a named API GROUP's provider.**

Today `src/` holds **6388** forbidden direct `rt_*` call sites against **1786**
distinct symbols. Those symbols belong to **180** groups — so the entire ad-hoc
surface is reachable through 180 entry points, ~36 call sites each. That ratio
is the whole argument: 180 seams are reviewable, 6388 are not.

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

`misc` is not an API group. It is 427 symbols and 846 call sites of work
queue, kept visible precisely so it can be split. A family that grows past 5
symbols becomes its own group at the next regeneration, automatically.

Adding a group is not a design act: define 5+ symbols with a shared prefix and
regenerate. What *is* a design act is naming its provider.

## 2. What an allowlisted provider is

A provider is the file or directory permitted to hold direct `rt_*` calls into
a group, because it **is** the runtime boundary — the place where the unsafe,
untyped, ABI-shaped call is written once so nothing else has to.

This policy invents no new notion of provider. A provider is exactly an entry
in `scripts/check/no_direct_rt_allowlist.txt` — the same 89 entries
`check-no-direct-rt.shs` has always honoured, in the same three forms (exact
path, trailing-slash directory prefix, `suffix:`). Typical entries:
`src/lib/nogc_sync_mut/sffi/`, `src/lib/**/ffi/`, `src/runtime/simple_core/`,
`suffix:_sffi.spl`.

A group's `provider` column is **measured**: the allowlist entry that already
serves the most of that group's allowlisted calls. A group with no such entry
is recorded `access: unowned` with `provider: "-"`.

**48 of 180 groups are `unowned`.** That is the honest state. `unowned` is a
debt marker, never a licence to call directly — it means the seam has not been
built yet, and the fix is to build it, not to widen the allowlist.

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

## 4. Migration path for the existing 6388 sites

A flag day is impossible and has never been attempted here. The path is four
ratchets that already interlock:

**Stage 0 — freeze (this change).** Every symbol is registered with a group and
its current site count. `check-rt-api-groups.shs` fails a new ungrouped `rt_*`
and fails any group whose sites exceed the recorded count. Landed **advisory**
because it is brand new; it records its verdict before it blocks, following the
`push-parser-source-global-ratchet` precedent.

**Stage 1 — own the groups.** Drive `unowned` from 48 to 0 by naming or
creating a provider for each. This is the only stage that needs design work.
Progress is one number: `access=unowned` in the registry.

**Stage 2 — collapse the biggest groups.** Work highest-leverage first, by
sites-per-symbol: `enum` (179 sites / 7 symbols), `bytes` (210/10),
`env` (283/14), `time` (221/23) — each is a handful of typed wrappers for a
large fraction of the debt. `file` (808/82) and `array` (268/79) are the volume
targets. Each landed batch lowers the group's registry count, and the ratchet
holds the new floor.

**Stage 3 — split `misc`.** 427 symbols, 846 sites. As sub-families reach 5
symbols they become groups automatically at regeneration.

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
call it* — is identical for each. The `rt` surface is fully populated (4168
symbols, 180 groups); `sosix` carries its 7 real entry points; `hal` and
`stdlib` are seeded rows awaiting the same census treatment.

Column meanings:

| column | meaning |
|---|---|
| `lane` | `both` / `c` / `rust` / `none`. **C and Rust**, not C and Simple — the Simple side is `twin`. `none` = called but defined in neither lane. |
| `backing` | `nm` / `text` / `unbacked` — *which instrument* saw the symbol. `extern-backing-census.shs` remains the authority on backing; this records provenance, it does not re-derive it. |
| `class` | `rt_alias_map.sdn`'s migration class: `same` / `adapted` / `provider` / `missing` / `unclassified`. |
| `sites` | forbidden direct call sites under `src/` at generation time. The per-group sum is the ratchet floor. |
| `twin` | a Simple twin is recorded in `doc/08_tracking/c_migration/c_migration_inventory.sdn`. |
| `alias` | typed std alias `module.fn`, or `-`. |
| `desc` | one line, **mechanically derived from the symbol name** unless a group owner has replaced it. A placeholder, not prose. |

**Rows are generated, never hand-edited**:
`sh scripts/check/gen-api-registry.shs`. Editing a row by hand makes the
registry disagree with the tree at the next regeneration.

Reader: `src/lib/common/api_registry.spl` (`api_registry_parse`,
`api_registry_group_of`, `api_registry_provider_of`, `api_registry_groups`,
`api_registry_symbols_in`), pinned by
`test/01_unit/lib/api_registry_spec.spl`.

## 6. The gate

```sh
sh scripts/check/check-rt-api-groups.shs                # default ratchet
sh scripts/check/check-rt-api-groups.shs --census F     # + stale-row check
sh scripts/check/check-rt-api-groups.shs --critical     # unowned groups fail
sh scripts/check/check-rt-api-groups.shs --selftest     # 7 fixtures, fatal
```

Verdict is always the last stdout line; a run that checked 0 things is
`ERROR`, never a pass. Measured 2026-09-06 at `ef8b58f3dab`:

```
PASS — 4168 rt_* symbol(s) checked, 0 ungrouped, 0 group(s) over budget, stale=0, 48 group(s) still unowned
FAIL — critical mode: 4074 rt_* symbol(s) checked, all grouped, but 48 group(s) have no allowlisted provider (access=unowned)
```

**Known limit, stated rather than papered over.** The default universe is
text-derived (definition lines + called symbols) so the gate stays fast enough
for a push hook. `nm` sees ~100 symbols with no greppable definition line, so a
cheap run cannot distinguish "registered and nm-only" from "stale" — the
stale-row check therefore runs only with `--census`, and a brand-new nm-only
symbol is invisible to a cheap run. Pass `--census` on the lane that can afford
the full census (~2 min, it compiles the C runtime).
