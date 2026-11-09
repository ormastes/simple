# stage2 `native-build` fails admission: `SCV-E-ADMISSION: git-event-refresh-failed` (erased-receiver `byte_len` in the inventory line walk)

Severity: P0 (phase-3 bootstrap blocker, phase_blockers item 7). Status: fix-implemented-verification-pending.

## Symptom

`C:/dev/p3new/stage2new/stage2_new4.exe native-build ...` (bootstrap_main entry, project root
`C:/dev/wt/stage2-rel` @ c4a6c6ac91f, also at origin/release/1.0.0 91fecec397f) exits 1 after
~20 s with `SCV-E-ADMISSION: git-event-refresh-failed`. GIT_TRACE shows `rev-parse HEAD` and one
successful `ls-files -t --cached --others --exclude-standard -- src test examples/10_tooling`
(6.4 MB, ~7 s); `_compiler_inventory_git_events_traced_cost_v1` then returns nil. The same
invocation through the Rust seed passes (its admission is Rust-side), so the stage2 binary that
the seed produced is what fails.

Ruled out by the blocker owner: disk, memory, dirtiness, untracked/deleted files, tab/CR paths,
`core.quotePath` (the code already passes `-c core.quotePath=false`), PR #7895 (it only changed
`src/app/bug/workaround_store.spl`, which never runs on this path).

## Root cause

`src/app/compiler_entrypoint/inventory_events.spl` (since `4183b795175`, 2026-11-07, the
`len()` -> `byte_len()` migration) walks the listing as

```simple
for line in listed!.split("\n"):
    if line.byte_len() <= 2 or line.substring(1, 2) != " ":
        return nil
```

`line` is an element of a `split()` result, i.e. an **erased receiver** in the seed's HIR. The
seed that built stage2_new4 (`seed.exe` 2026-11-09 02:11, from c4a6c6ac91f) carries `177e47d13d9`
(typed `text` receiver `byte_len` -> I64) but **not** `9a80b3cb557` (erased-receiver table,
`seed_untyped_byte_len_binding_raw_i64_misdecoded_2026_11_09`, merged 2026-11-09 01:44 — after
stage2-rel's base). So in the seed's LLVM lane `line.byte_len()` is typed ANY, no `BoxInt` is
emitted, and the raw i64 is treated as a tagged word: `str(line.byte_len())` prints `true` for
11 and `<value:0x16>` for 22 (inv-dbg trace, seed-built probe). The `<= 2` compare then goes
through the dynamic `rt_native_cmp`, misreads the raw 11, and the fail-closed arm returns nil.
Which rows fail depends only on the row's byte length (11-byte rows such as `H src/c.spl` always
fail; the real tree dies on its 255th row, hence "254 events" in the inventory trace), so the
blocker looked like a per-file inventory defect.

The porcelain (warm) walk at `compiler_inventory_parse_porcelain_cost_v1` has the identical
shape (`line.byte_len() <= 3`) and is fixed the same way.

## Evidence

Seed-built probe (`seed.exe native-build` of a 7-line program calling
`compiler_inventory_refresh_v1(root, root + "/build/scv", ["src"], true)`):

| repo | before | after typed binding |
|---|---|---|
| `src/c.spl` + `src/main.spl` | `git-event-refresh-failed` | ok |
| `src/main.spl` + `src/x.spl` | `git-event-refresh-failed` | ok |
| real `src/app` subtree (3689 files) | `git-event-refresh-failed` (events=0) | ok |
| `src/app/__init__.spl` + `src/main.spl` | ok | ok |
| 301 trivial files | ok | ok |

Fixture `test/01_unit/app/compiler_entrypoint/fixtures/inventory_split_line_byte_len_fixture.spl`
under the deployed seed `bin/simple.exe run` (2026-11-04): `lens=true,<value:0xe>, short=1`
(red). `seed.exe run` (JIT, has 177e): `lens=11,14, short=0`; the same seed's LLVM lane is red,
which is the lane stage2 is built with.

## Fix

- Root fix is already on origin/release/1.0.0: `9a80b3cb557` (seed HIR erased-receiver
  `byte_len`/`char_count` -> I64). It needs a seed rebuilt from a base that includes it.
- This change: `# @workaround bug=seed_untyped_byte_len_binding_raw_i64_misdecoded_2026_11_09`
  in `inventory_events.spl` — bind each split row through a declared `text` (`val line: text =
  row`) in both the cold-init and porcelain walks so a stage2 built with the current seed.exe
  types the receiver and takes the i64 path. Remove once the deployed seed carries 9a80b3cb557.
- Spec: `test/01_unit/app/compiler_entrypoint/inventory_split_line_byte_len_spec.spl`.

## Phase-runner workaround (now)

Rebuild stage2 with the existing `seed.exe` from a stage2-rel that carries this PR's
`inventory_events.spl` (cherry-pick, or apply the two `val line: text = row` bindings as a tagged
WA). No seed rebuild is needed. Presetting `SIMPLE_SCV_SNAPSHOT_ROOT` to skip the coordinator's
authority acquisition is NOT viable: admission is skipped but the parse-shard closure then fails
with `snapshot-open-not-owned`. No env knob disables the inventory.
