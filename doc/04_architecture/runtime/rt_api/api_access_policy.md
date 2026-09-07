# API access policy — every callable surface in the tree

**Status:** proposed. Nothing here is enforced by a blocking gate yet; §6 says
exactly what is and is not wired.
**Measurements:** `doc/01_research/runtime/rt_api/api_surface_classification_2026-09-06.md`.
**Scope of this doc vs. the group policy:** `rt_api_group_policy.md` (arriving
via PR #405/#419) defines *what an rt group is* and ratchets it. This doc is
the layer above: it says **which of three seams** a given group must route
through, defines the exemption classes that make that decidable, and extends
the same database to non-`rt` surfaces. Where the two overlap, the group policy
is authoritative on group mechanics and this doc is authoritative on routing.

---

## The rule

> **No product code reaches past a seam.**
>
> For runtime access that means: every `rt_*` call is made through **SOSIX**,
> through the **HAL owner** for its machine boundary, or through the **named
> group provider** — never one-off from the caller.
>
> For stdlib access it means the same defect in its own shape: every
> `use std.<space>.<family>` resolves through the family's `__init__.spl`,
> never past it into a submodule.

Measured at `63924350c16`, the tree violates this 6,430 times on the runtime
surface and 549 times on the `nogc_async_mut` stdlib surface. This is a
**ratchet, not a flag day**: nothing existing is broken by this policy, and
what it forbids is growth.

---

## 1. The three seams, and how to tell which one applies

A routing rule is only a rule if a second person applies it and gets the same
answer. Each seam therefore has a criterion that was applied mechanically to
all 181 groups and produced the classification in the research doc's §1.4.

### SOSIX — host operating-system services

**Criterion.** The group's subject is an operating-system service that
**SimpleOS must also be able to provide**: it falls under one of the seven
contracts in `src/lib/common/contracts/sosix/` — `operation_v1`,
`file_operation_v1`, `completion_v1`, `wait_v1`, `error_v1`,
`capability_ref_v1`, `service_ids_v1`. In practice: positioned file I/O,
directory enumeration, path resolution, descriptor lifetime, process
lifecycle, environment, time, completion/wait.

**Why SOSIX and not a group provider for these.** SOSIX is not one seam among
181. It is the only seam in the tree with **two independent implementations of
the same vocabulary**: the hosted capsule `src/lib/nogc_async_mut/sosix/` (29
published names, POSIX today, a Windows backend later) and the SimpleOS-internal
`src/os/sosix/` (61 files over `syscall_raw`). Routing an OS service through a
group provider instead would build a seam that only ever has one side. Routing
it through SOSIX is what makes the same source run on both.

The overhead objection is already answered in the tree: the POSIX path is
`@always_inline` pass-throughs, so the facade costs nothing at a call site.

**Coverage today: 12 rt groups** (`file dir io time process fd path env misc
thread shell hash`, measured two hops from the capsule). **Target: add `socket`
and `pty`, and grow `env`/`time`/`process`/`file` from partial to full** — about
1,700 forbidden call sites, ~26% of the whole runtime debt, behind one facade.
That ratio is why SOSIX is first in the decision order below.

### HAL — the machine boundary

**Criterion (two predicates, both required).**
- **P1:** >= 90% of the group's forbidden call sites are under `src/os/**`.
- **P2:** the host cannot implement it — either fewer than half its symbols
  have any host-runtime definition, or at least half its C definitions live
  under `src/runtime/platform/**` or a baremetal file.

**Why both.** Each predicate alone misclassifies, demonstrably: P1 alone admits
`array` (268 sites, 70% of them in `src/os` — value representation the kernel
uses heavily, not a machine boundary); P2 alone admits `winit`, `tls13`,
`debug`, `ftp` and 28 others whose lack of a host definition means only that
they are pure-Simple or unbacked. Absence of a definition is not evidence of a
machine boundary.

**Membership today: 17 groups, 578 call sites** — `net arm64 arm port x86
hosted arm32 boot rv32 gui driver starfive read display staged limine storage`.

**HAL beats SOSIX when a group is both.** The machine boundary sits below the
OS boundary, so a group that is a machine primitive routes through its arch
owner even if an OS service is built on top of it.

**Language policy for a HAL owner** is not restated here — it is
`doc/07_guide/os/hal/pure_simple_hal.md`: pure Simple first, C only as a
bootstrap boundary with a Simple twin, inline asm only for architecturally
irreplaceable operations, twins gated by `check-dual-run-shadow.shs`.

**Two `rt_*` families are NOT the HAL despite their names**, and any count that
treats them as runtime access is wrong by 89 sites:
- `rt_hal_*` (58 sites) is the **dual-run boundary framework**
  (`src/lib/nogc_sync_mut/rt_hal/`), a test harness, not a hardware layer.
- `rt_criticality_*` (31 sites) are **compiler analysis predicates**
  (`rt_expr_dispatches`, `rt_block_allocates`) that merely follow the naming
  convention. `check-no-direct-rt.shs` already documents both as false
  positives; this policy inherits that caveat rather than re-litigating it.

### Group provider — everything with no OS analogue

**Criterion.** Neither of the above: not a machine primitive, and not a service
SimpleOS would have to provide. 130 groups. Three coherent families: graphics
and windowing (`vulkan metal sdl2 sdl3 opengl glfw winit font image`), compute
and ML (`torch cuda rocm opencl oneapi simd blas math`), and value
representation (`array string bytes enum dict ptr`).

SimpleOS will not "provide" a Vulkan device or an array header, so routing
these through a POSIX-shaped facade would be a category error. Group mechanics
— what a provider is, how one is named, the allowlist forms — are
`rt_api_group_policy.md` §2, unchanged by this doc.

### Decision order for any new call

1. Does a `sosix_*` name cover it, or does its subject fall under a SOSIX
   contract? Use SOSIX, or extend SOSIX. Done.
2. Is it a machine primitive by P1+P2? It belongs in the arch/board owner under
   `src/os/kernel/arch/**` or the driver seam. Done.
3. Is there a typed std alias in the registry's `alias` column? Use it. Done.
4. Otherwise it belongs **inside the group's provider**, behind a typed
   function. If the group is `unowned`, creating that provider *is* the change;
   adding one more direct call is not.

---

## 2. Exemption classes — and why two of them are mandatory

An access class says who may call a symbol. `rt_api_group_policy.md` defines
two: `group` (a provider exists) and `unowned` (no provider — a debt marker,
never a licence). Those two are not sufficient, and the gap is not cosmetic:
**43 groups are `unowned`, and 22 of them have zero call sites anywhere under
`src/**.spl`.** A provider is derived from allowlisted call sites, so a group
with no call sites has nothing to derive from and is unownable **by
construction, forever**. PR #431 correctly identified this as a hard blocker on
promoting `--critical` to blocking, and left open whether those 22 are dead.

They are not dead. Measured across all 304 of their symbols (research doc §2):
**zero have "no reference"**. Hence two further classes, each earned by
measurement:

| class | criterion (mechanical) | population | may a caller call it directly? |
|---|---|---|---|
| `group` | an allowlisted provider serves the group | 138 groups | only from the provider |
| `unowned` | call sites exist, no provider yet | **21** groups | **no** — debt marker; build the seam |
| `runtime-internal` | 0 call sites under `src/**.spl`, referenced in `src/compiler_rust/**/*.rs` or `src/runtime/**/*.{c,h}` | 20 groups, 280 symbols | n/a — Simple never calls it |
| `codegen-abi` | 0 call sites, but named as a literal in `src/compiler/**/*.spl` | 2 groups (`sffi`, `contract`), 24 symbols | only the compiler backend emits it |

Both new classes stay **registered** — a new symbol landing in one is still
caught by the registration check — and are **exempt from provider ownership**.
Neither is a licence to add a direct call from Simple: by definition there are
none to add.

**The consequence is the point.** With these classes applied, `--critical`'s
unowned population falls from **43 to 21**. Forty-three, of which 22 are
unownable, is a gate that can never go green and will therefore never be
promoted. Twenty-one groups each needing a seam BUILT is a finite work item.

**These classes must be measured, never declared.** `runtime-internal` is
justified by a reference in a runtime lane; `codegen-abi` by a reference in
compiler source. A hand-written exemption row would reintroduce exactly the
"decoration" failure `rt_api_group_policy.md` §7 documents, where a required
regeneration silently laundered ungrouped symbols into a green verdict.

**Stated limit.** Both classes are decided by *text reference*, not linkage. A
symbol referenced only in a Rust comment would be misclassed `runtime-internal`
when it is genuinely dead. `extern-backing-census.shs` remains the authority on
backing; this classification answers only *unconsumed vs. dead*, which is the
question that decides exemption. Deletion of a genuinely dead symbol is
explicitly **out of scope** for this policy — the research measured references,
not liveness, and deleting on that evidence would be unsound.

---

## 3. How a new `rt_*` symbol is introduced

Adding a runtime symbol is four steps, and the order matters because step 3 is
the one people skip.

1. **Define it in a runtime lane** (C under `src/runtime/`, Rust under
   `src/compiler_rust/runtime/`), following the dual-implementation rule
   already gated by `check-rt-dual-implementation-ratchet.shs`.
2. **Give it a group.** Either its `rt_<family>_` prefix reaches 5 distinct
   symbols and the heuristic forms a group on its own, or it takes a row in
   `config/api/api_group_overrides.sdn` assigning it to a group that already
   exists. An override cannot invent a group — the generator exits 2 if it
   tries.
3. **Name its owner before its first non-provider caller.** Route it per §1:
   SOSIX name, HAL owner, or group provider. **This is a prerequisite, not
   follow-up work.** A symbol whose first caller is ordinary product code has
   already created the debt this policy exists to stop, and the ratchet will
   then hold that call site as the floor.
4. **Regenerate and commit the registry** — `sh scripts/check/gen-api-registry.shs`
   for the `rt` surface. Rows are generated, never hand-edited.

**Widening `no_direct_rt_allowlist.txt` is not step 3.** A provider is a file
whose *role* is the ABI seam. The criterion, from `rt_api_group_policy.md` §2
and unchanged here: 100% of the group's direct call sites already live in one
file, AND that file is a declared seam (a shim, a bridge, a hosted backend, a
platform demultiplexer) rather than logic that merely happens to call the
primitive. Ordinary arch code that is currently the only caller does not
qualify — naming it would be inventing ownership.

---

## 4. The database: one schema, every surface

`config/api/api_registry.sdn` (the `rt` surface, arriving via PR #405/#419) and
`config/api/api_registry_stdlib.sdn` (the `stdlib` surface, this lane) are two
**shards of one database**: identical table names, identical column names,
distinguished by the `surface` column.

```
api_groups  |surface, group, symbols, sites, provider, access|
api_symbols |surface, group, symbol, lane, backing, class, sites, twin, alias, desc|
```

They are separate files only so this lane does not conflict with a 4,389-line
generated file being landed by three other branches; shards concatenate under
one reader, and merging them into a single file is a mechanical change once
those PRs land.

The claim "`surface` is a column, not a file — one schema covers every surface"
was made by the rt lane and was, until now, **untested**: no non-`rt` surface
had ever been populated. §5 tests it.

---

## 5. The stdlib surface — the same rule, the same ratchet

**The analogy that makes the schema transfer.** On the rt surface the counted
defect is a *forbidden direct call*: a consumer reaching past a seam to the
primitive. The stdlib's exact structural equivalent is a **bypass import**.
`src/lib/<space>/<family>/__init__.spl` is what `use std.<space>.<family>`
resolves to — it *is* the provider. A file outside the family writing
`use std.<space>.<family>.<submodule>` has pinned itself to an internal file,
so the family can no longer reorganise behind its own facade. Same defect,
same countable unit, same ratchet.

Per-surface column meanings are carried in the generated file's own header, so
a reader never has to guess; in summary, for `stdlib`: `group` is
`<memory-space>.<family>`, `provider` is that family's `__init__.spl`, `sites`
is bypass imports **from `src/`** (test files are excluded from the column and
counted in the emitted header — 956 for `nogc_async_mut` — because a spec for a
submodule legitimately imports that submodule),
`lane` is the memory space, `backing` is how the name is published
(`export-use` / `export-list` / `export-glob` / `pub-decl`), and `twin` is
always `-` because the C-migration twin inventory is an rt-surface concept and
is not fabricated here.

Measured for `nogc_async_mut` (83 families, 2,709 public symbols): **549 bypass
imports from `src/`**, 7 families publishing nothing. `nogc_async_mut.concurrent`
publishes zero names and has 17 consumers, every one of which must reach
inside — `unowned`, in the stdlib, with the same meaning and remedy.
`nogc_async_mut.sosix` is the opposite pole: 29 published names, **zero** src/
bypasses, the best-encapsulated family in its space.

**Access classes for `stdlib`:** `group` (the family publishes a surface
through its provider) and `unowned` (an `__init__.spl` exists but publishes
nothing, so there is no seam at all). The rt surface's `runtime-internal` and
`codegen-abi` do not arise here.

**A wildcard export is recorded, never expanded.** `export mod.*` publishes a
name set no text scanner can enumerate. It is emitted as ONE row naming the
wildcard, with `backing: export-glob`. The family counts as publishing a
surface; its symbol count understates it. Silently expanding or silently
dropping such a row would both be worse than saying so.

**Only `nogc_async_mut` is populated.** The generator takes `--space` and the
same scan applies to all five memory spaces, but one space done properly beats
five stubbed. `src/lib/common/` is organised by topic rather than by capsule
and may not follow the provider convention as cleanly; that is unmeasured and
is named as unmeasured.

---

## 6. What is enforced, honestly

| gate | tier | verdict at this base |
|---|---|---|
| `check-no-direct-rt.shs` | push, blocking | **pre-existing red on `origin/main`**, re-measured at `63924350c16`: `FAIL — forbidden direct rt_* count 27519 exceeds baseline 7776 (roots=src,examples,tools,scripts,test, src=6322 ...)`, exit 1. The `src=6322` leg matches the known `R5:direct-rt-src=6322>ceiling=6240`. This lane adds no `.spl` under `src/` and so cannot change it; **no ceiling or baseline is raised here** |
| `check-rt-api-groups.shs` | push, advisory (PR #419) | green at its own base; would fire on the 31 registry-stale symbols measured here |
| `gen-stdlib-api-registry.shs --check` | **not wired** | `PASS — 2709 stdlib symbol(s) checked in space nogc_async_mut, 0 unregistered, 0 stale, 549 bypass import(s) from src/ (956 more from test/, excluded), 7 family(ies) publishing nothing` |

The stdlib gate is deliberately **not** added to `config/check/must_check_gates.sdn`
in this lane. It ratchets registration and staleness only — it does not yet
freeze the 549 bypasses against a baseline, and wiring a gate that cannot fail
on the debt it measures would be decoration of exactly the kind
`rt_api_group_policy.md` §7 dissects. Freezing that floor is the next slice.

Verdict convention, mandatory for every gate named here: the **last stdout
line** is `PASS — <n> ... checked` with n > 0, `FAIL — ...`, or
`ERROR — nothing was checked (<reason>)`. Zero checked is ERROR, never PASS.
The generator's `--selftest` runs 6 fixtures and was verified to
**discriminate**: sabotaging the `export X, Y` handler makes fixture 5 fail
with the exact diagnostic, and restoring it makes it pass.

Every `--check` branch was also demonstrated **against the real tree**, not
only against a fixture — the repo's stated bar. Injected, measured, reverted at
`63924350c16`:

```
# a symbol row deleted from the registry
FAIL — 2709 stdlib symbol(s) checked in space nogc_async_mut, 1 unregistered,
       0 stale; unregistered:nogc_async_mut.sosix.sosix_which
# a row renamed, so one symbol is unregistered AND one row is stale
FAIL — 2709 stdlib symbol(s) checked in space nogc_async_mut, 1 unregistered,
       1 stale; unregistered:nogc_async_mut.sosix.sosix_kill
       stale:nogc_async_mut.sosix.sosix_ghost_symbol
# no registry to measure against
ERROR — nothing was checked (no registry /nonexistent)
```

---

## 7. Migration order

Ordered by sites-per-seam, because that ratio is the entire argument for
seams over call sites.

1. **SOSIX first — ~1,700 sites behind one facade.** Extend the capsule to
   cover `env` (283 sites), `time` (221), `process` (200), `io` (183) and the
   rest of `file` (808), then add `socket` and `pty` contracts. Best ratio in
   the tree by a wide margin.
2. **Apply the two exemption classes** so `--critical` measures 21 genuinely
   unowned groups instead of 43 including 22 unownable ones. This is a
   generator change, not a migration, and it unblocks promotion.
3. **Build the 17 HAL seams — 578 sites.** `port` and `dma` are already done
   (PR #431). `arm64` (75), `x86` (46), `arm32` (42) and `boot` (38) each need
   an arch owner built, which is design work, not a line in an allowlist.
4. **Collapse the highest-leverage groups** — `enum` (179 sites / 7 symbols),
   `bytes` (210/10), `array` (268/79). A handful of typed wrappers each.
5. **Ratchet the stdlib bypasses.** Freeze 549 as a floor, then drive
   `nogc_async_mut.io` (132) and `nogc_async_mut.engine` (94) down, and give
   `nogc_async_mut.concurrent` a published surface so its 17 consumers have
   something to route through.
6. **Extend the DB to the other four memory spaces**, then to `src/lib/common/`
   once its provider convention is measured rather than assumed.

Nothing in this policy relaxes an existing gate, raises any ceiling, or
regenerates any baseline.
