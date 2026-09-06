# rt_* API group census — 2026-09-06

Base: `ef8b58f3dab`. Host: aarch64 Linux. Every number below is a command's
output, not an estimate; the commands are named so each one can be re-run.

The question this census exists to answer: **can direct `rt_*` access be
replaced by a small number of named group entry points, and how small is
"small"?** The policy derived from it is
`doc/04_architecture/runtime/rt_api/rt_api_group_policy.md`.

---

## 1. What already existed (read before designing)

| Artifact | What it holds | Reused how |
|---|---|---|
| `scripts/check/check-no-direct-rt.shs` | Global ratchet on direct `rt_*` call sites in Simple, split by `no_direct_rt_allowlist.txt`, baselined in `no_direct_rt_baseline.txt` (7776) | Its scanner definition (`RT_RE`, `DECL_RE`, allowlist matching) is reused verbatim; the new gate ratchets the same population **per group** |
| `scripts/check/rt-dual-implementation-census.shs` | Symbol universe + C/Rust lane split, read from link artifacts via `nm` | The registry's symbol universe and `lane`/`backing` columns |
| `scripts/check/check-rt-dual-implementation-ratchet.shs` | Freezes 2509 single-lane symbols | Not re-adjudicated; recorded only |
| `scripts/check/extern-backing-census.shs` | Authority on whether an extern is backed (`nm` over real link artifacts) | The `backing` column records which instrument saw a symbol; backing is not re-derived here |
| `scripts/check/rt_alias_map.sdn` | 892 symbols with a migration class (`same`/`adapted`/`provider`/`missing`) and, where one exists, the typed std alias `module.fn` | The registry's `class` and `alias` columns |

Nothing above answers "which group", and nothing is queryable from Simple.
That is the gap.

---

## 2. Symbol universe

```sh
sh scripts/check/rt-dual-implementation-census.shs --out census.tsv
```

```
c_lane_mode=nm c_files=131 c_compiled=121 c_uncompilable_external=10
rust_lane_mode=text-fallback
counts: total=2930 c=1542 rust=2078 simple_twin=68 dual_pair=41
class: both=690 c-only=852 rust-only=1388
```

**The Rust lane is a text fallback here** — this worktree has no
`libsimple_runtime.rlib`, so `nm` had nothing to read and the census fell back
to grepping `fn rt_*`. The registry header copies that mode string verbatim so
no reader mistakes it for an `nm` measurement.

`nm` and text-grep each see symbols the other misses, and the gap is not small:

```
text-visible but never reported by nm : 328
nm-reported with no greppable defn    : 100   (macro-generated definitions)
```

So the registry universe is the **union** of three sources — `nm` census,
text-visible definitions in both lanes, and symbols actually *called* from
product Simple:

| universe | count |
|---|---|
| `nm` census (C nm + Rust text) | 2930 |
| + text-visible C/Rust definitions | |
| + symbols called from `src/**/*.spl` | |
| **= registry** | **4168** |

Lane split as recorded in the registry (union universe):

```
both=707  c-only=1182  rust-only=1371  none(unbacked)=908
```

**Naming caution.** The task framed the split as "C / Simple / both". The
census's two lanes are **C and Rust**, which is not the same axis. The Simple
side is the `twin` column, sourced from
`doc/08_tracking/c_migration/c_migration_inventory.sdn`: **46** registry rows
carry `twin=yes` (68 symbols appear in that inventory; 46 of them are in the
registry universe). Read `lane` as C/Rust and `twin` as "has a Simple twin".

`none` (908) means a symbol is *called* but defined in neither runtime lane.
That population is a mixture of genuinely unbacked externs and pure-Simple
functions that merely follow an `rt_` naming convention — a measurement caveat
`check-no-direct-rt.shs` already documents for
`src/lib/nogc_sync_mut/rt_hal/` and
`src/compiler/35.semantics/rt_criticality_validation.spl` (155 sites, none of
them runtime calls: `rt_expr_dispatches`, `rt_block_allocates`, …). This
census does not fix that caveat; it inherits it, and the registry makes those
symbols visible as `lane=none, backing=unbacked` rather than hiding them.

---

## 3. How the groups were derived

Mechanically, with no curation:

1. `family` = the first `_`-delimited token after the `rt_` prefix
   (`rt_vulkan_create_device` → `vulkan`).
2. A family with **>= 5 distinct symbols is a group**.
3. Everything below the threshold falls into a single residual group `misc`.

Why this rule and not something cleverer:

- **Prefix families are already how the tree is organised.** The raw
  distribution over 4168 symbols has 299 first-token families; the top of it
  reads `torch 139, vulkan 110, array 74, simd 71, string 69, vk 67,
  monoio 67, file 67, sdl2 65, cli 61, io 59, cuda 53, metal 52, gpu 48,
  process 41 …` — these are real API surfaces, not accidents of spelling.
- **Defining-file attribution was tried and rejected for the residual.**
  Mapping the sub-threshold symbols to their defining C file collapses 124 of
  313 onto `runtime_native.c` — the catch-all file. It discriminates nothing,
  so the residual is a named bucket (`misc`) that stays visible rather than a
  fake grouping.
- **The residual is deliberately NOT called `core`.** `rt_core_*` is a real
  family of its own; reusing that name would silently merge a genuine group
  with the leftovers.
- Threshold 5 matches the `--min-files=5` precedent already used by
  `check-no-revert-push.shs` and `check-runtime-api-regression-push.shs` for
  "a handful is routine, a mass is not".

Result: **180 rt groups** — 179 named families plus `misc`.
`misc` holds 427 symbols and 846 call sites (13% of the forbidden total). It
is not an API group; it is the work queue.

---

## 4. The collapse — the number the policy rests on

```sh
sh scripts/check/rt-call-site-census.shs --roots src --out sites.tsv
```

```
roots=src allowlist=scripts/check/no_direct_rt_allowlist.txt
totals: forbidden_sites=6388 distinct_symbols=1786 allowlisted_sites=6051 call_lines=12224
```

| level | count | ratio vs. sites |
|---|---|---|
| forbidden direct call sites under `src/` | **6388** | 1× |
| distinct symbols they call | **1786** | 3.6× collapse |
| groups those symbols belong to | **180** | **35.5× collapse** |
| groups excluding the `misc` residual | 179 (5542 sites) | 31× |

So the ~6.4k ad-hoc call sites in `src/` are reachable through **180 group
entry points** — about 36 call sites per group, 10 symbols per group. Nine
groups carry more than 200 sites each:

```
misc 846(427 syms) | file 808(82) | env 283(14) | array 268(79) | time 221(23)
bytes 210(10) | process 200(53) | io 183(61) | enum 179(7)
```

`enum` is the extreme: 7 symbols, 179 call sites — a 26:1 collapse from one
group alone.

### The task's "~12948" figure is stale

`check-no-direct-rt.shs` measured `forbidden=12948` on 2026-08-18 under
different roots. Measured today:

- `--roots src` (the wired gate): **6230** forbidden, baseline **7776** — the
  gate is green with 1546 of headroom.
- token-counted by the new per-symbol census: **6388** (a line with two calls
  counts twice; the line-counted gate counts it once).
- total direct calls in `src/`, forbidden + allowlisted: 6388 + 6051 =
  **12439**. That is close to the old 12948, but the two were measured
  differently and this census does not claim they are the same population.

---

## 5. Providers

An **allowlisted provider** is exactly what `no_direct_rt_allowlist.txt`
already defines: a file or directory permitted to hold direct `rt_*` calls
because it *is* the runtime boundary (89 entries: `src/lib/**/sffi/`,
`src/lib/**/ffi/`, `src/runtime/simple_core/`, `suffix:_sffi.spl`, …).

The registry's group `provider` is **measured, not declared**: for each group,
the allowlist entry that already serves the most of that group's allowlisted
call sites (`rt-call-site-census.shs --provider-out`, 3404 symbol→provider
pairs).

```
groups with a measured provider : 132
groups with none (access=unowned):  48
```

48 unowned groups is the honest state, and it is what `--critical` fails on.

---

## 6. Other findings, recorded rather than fixed

- **120 of the 892 `rt_alias_map.sdn` entries are neither defined in either
  runtime lane nor called anywhere in `src/`.** They are probably stale alias
  rows. Not touched here.
- **462 registry rows carry a typed std alias**; the remaining 3706 have none,
  so a group entry point has to be written for them.
- **`config/check/must_check_gates.sdn` could not be read from Simple at all.**
  The stdlib SDN parser supported only the anonymous top-level `|h1, h2|`
  table; the `name |h1, h2|` form every table SDN in this repo actually uses
  parsed to a bare string with the table silently dropped, and a `#` comment
  line carrying a colon became a real dict key. Both are fixed in
  `src/lib/common/sdn/parser.spl` and pinned by
  `test/01_unit/common/sdn_named_table_spec.spl`; the manifest now parses to
  6 headers × 74 rows. Six existing SDN specs were run before and after the
  change with byte-identical results (`coverage_sdn_spec` 1/0,
  `sdn_parsing_spec` 4/0, `env_access_plan_sdn_spec` 6/5 both sides,
  `sdn_coverage_spec` 5/3 both sides, `parsers_sdn_coverage_spec` 5/3 both
  sides, `app/sdn_spec` parse-error both sides — all pre-existing).
- **The `desc` column is a name-derived placeholder**, not prose
  (`rt_file_read_text` → `"file: read text"`). Fabricating 4168 descriptions
  would be worse than admitting they are mechanical. Filling them per group is
  part of the migration, not a prerequisite for it.
- **The `simple_ctx_*` MCP tools returned empty stubs for every call** in this
  session, so no ctx source labels exist for this work.
