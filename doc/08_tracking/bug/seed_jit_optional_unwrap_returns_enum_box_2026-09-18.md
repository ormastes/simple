# The deployed seed's JIT lane returns the Option BOX from `!`, silently — and it wedges SCV cold-init in every fresh worktree

- **id:** seed_jit_optional_unwrap_returns_enum_box_2026-09-18
- **status:** RESOLVED (2026-09-18) — remedy applied: the binary was redeployed from current source; see "Redeployed" below
- **severity:** P1 (silent wrong answers on the default lane, plus a permanent native-build wedge)
- **found:** 2026-09-18, while reproducing `native_empty_dict_text_value_sigsegv_2026-07-20`
- **binary at fault:** `bin/release/aarch64-unknown-linux-gnu/simple`, 50,093,192 B, built 2026-09-06, sha256 `3d120a6f9ab5704b2225…` (the symlink target of `bin/simple`)

## Symptom

`!` applied to an Option yields the Option **box** instead of its payload, on the
**JIT lane only** — which is the DEFAULT lane for `bin/simple run`. No error, no
warning, exit 0.

Probe (`opt_types.spl`, 20 lines, whole file in the Verification section):

| expression | expected | deployed seed, `run` (JIT) | deployed seed, `SIMPLE_EXECUTION_MODE=interpret` |
|---|---|---|---|
| `Some(42)!` → `to_text()` | `42` | **`<enum@0x…>`** | `42` |
| `Some(true)!` → `to_text()` | `true` | **`<enum@0x…>`** | `true` |
| `Some([1,2,3])!.len()` | `3` | `3` | `3` |
| `Some("hello")!.len()` | `5` | **`-1`** | `5` |
| `"[" + Some("hello")! + "]"` | `[hello]` | **the `print` emitted NOTHING AT ALL** | `[hello]` |
| `Some("hello")! == "hello"` | `true` | **`false`** | `true` |

Two observations that make this worse than a formatting bug:

- **`==` silently answers `false`.** Any `val s = opt!; if s == "x"` takes the
  wrong branch with no diagnostic. That is a wrong-answer defect, not a display one.
- **A whole `print` statement vanished.** The text-concatenation line produced no
  output on the JIT lane while every sibling line printed.

Container payloads (`[i64]?`) unwrap correctly, so a suite that only exercises
container optionals reports green on a binary that miscompiles every scalar one.

## This is a STALE-BINARY defect, not a source defect

Two seeds built from newer source answer **all six rows correctly, on both lanes**:

| seed | built | `run` (JIT) | `interpret` |
|---|---|---|---|
| deployed `bin/simple` | 2026-09-06 | **wrong (6 rows)** | correct |
| `/home/yoon/cargo-fulltest/release/simple` | 2026-09-13 | correct | correct |
| `/home/yoon/cargo-unitp2/release/simple` | 2026-09-14 | correct | correct |

So the fix already exists in the tree; the deployed binary predates it by 12 days
and was never redeployed. Every agent lane, every `bin/simple run`, and every tool
that shells out to `bin/simple` on this host has been running on it.

## Consequence: SCV cold-init publishes an EMPTY inventory and wedges the worktree permanently

`compiler_inventory_git_lines_v1` (`src/app/compiler_entrypoint/inventory_events.spl`)
returns `text?`. The cold-init branch of `compiler_inventory_git_events_v1`
unwraps it with `!` and splits it:

```
val listed = compiler_inventory_git_lines_v1(root, [... "ls-files" ...])
for path in listed!.split("\n"):
```

On the deployed seed `listed!.len()` is **-1** and `.split("\n")` yields nothing,
so **zero** events are produced. Measured, with the instrumentation removed again
afterwards:

```
[dbg2] listed_bytes=-1 roots=1 root=/home/yoon/dev/simple-rob1
[dbg2] nonempty_paths=0 events=0
[dbg]  git_events=0 cold_init=true
```

The same `git ls-files` run by hand, and the same `process_run_bounded` call from
a standalone Simple program, both return **3,597,622 bytes / 60,724 lines**
(16,791 of them `.spl`). Only the unwrap loses it.

An empty inventory is then **published** (`generation=0 count=0`) and the trap closes:

| run | command | result |
|---|---|---|
| 1 | clean cache + `SIMPLE_SCV_INVENTORY_COLD_INIT=1` | publishes `generation=0 count=0`, then `SCV-E-SNAPSHOT: snapshot-inventory-empty` |
| 2 | same cache + `SIMPLE_SCV_INVENTORY_COLD_INIT=1` | `SCV-E-ADMISSION: git-event-apply:inventory-publication-failed` |
| 3 | same cache, no cold-init | `SCV-E-ADMISSION: compile-event-journal-missing (first build in this checkout: rerun with SIMPLE_SCV_INVENTORY_COLD_INIT=1)` |

Run 3's message sends the user to run 2, which fails; run 2 can never succeed
because `compile_source_inventory_publish_v1` refuses a same-generation publish
whose digest differs from the empty one already recorded. **The only escape is
`rm -rf build/scv`, and nothing anywhere says so.** With a correct seed the very
same command publishes `generation=16797 count=16797` and native-build proceeds.

This is the cause of the "fresh worktree cannot native-build" friction that has
hit multiple lanes for days, including the `native-build entry closure is empty
(source snapshot unavailable)` face of it.

## Two source defects this exposed (independent of the stale binary)

1. **An empty inventory is publishable.** For a repo with 16,791 compilable
   sources, an inventory of 0 entries is not a legitimate state, yet it is
   written and becomes authoritative. It should fail closed at publish time.
2. **`inventory-publication-failed` names none of its causes.**
   `compile_source_inventory_publish_v1` (`src/lib/scv/compile_source_inventory.spl`)
   has **eight** distinct `return ""` paths — invalid cache root, empty encode,
   `dir_create_all` failure, lock failure, a newer generation already published,
   a same-generation digest divergence, generation-file staging failure, and
   CURRENT staging failure. All eight reach the user as one opaque string, so a
   retryable race is indistinguishable from a full disk or a permanent wedge.

## Verification

Probe used for every row above:

```simple
fn gi() -> i64?:
    Some(42)
fn gt() -> text?:
    Some("hello")
fn gb() -> bool?:
    Some(true)
fn ga() -> [i64]?:
    Some([1, 2, 3])

fn main() -> i64:
    print "i64  bang   = " + (gi()!).to_text()
    print "i64  coal   = " + (gi() ?? 0).to_text()
    print "bool bang   = " + (gb()!).to_text()
    print "arr  bang   = " + (ga()!).len().to_text()
    print "text bang   = " + (gt()!).len().to_text()
    print "text concat = " + ("[" + (gt()!) + "]")
    val t = gt()!
    print "text eq     = " + (t == "hello").to_text()
    0
```

```
bin/simple run opt_types.spl                              # JIT default: 6 wrong rows
SIMPLE_EXECUTION_MODE=interpret bin/simple run opt_types.spl   # all correct
SIMPLE_EXECUTION_MODE=jit /home/yoon/cargo-unitp2/release/simple run opt_types.spl   # all correct
```

The spec lane does **not** discriminate: `bin/simple test` runs specs on the
interpret route, so `test/01_unit/interpreter/optional_unwrap_payload_spec.spl`
(added with this record) passes on both the broken and the correct binary. It pins
the contract; it cannot catch a bad binary. That is what
`scripts/check/check-deployed-binary-optional-unwrap.shs` is for — it runs the
probe through the deployed binary's own default lane and compares it against the
interpret lane, so any binary that loses a payload fails closed.

## Remedy

1. **Redeploy `bin/simple` from current source.** The deployed seed is 12 days
   stale and miscompiles the default lane. This is a shared artifact on this host
   (other sessions use the same symlink), so it needs the owner's go-ahead rather
   than an in-flight replacement.
2. Land the two source hardenings above so that a future bad listing fails closed
   instead of poisoning the cache.
3. Until (1), any lane that must native-build in a fresh worktree either runs with
   a seed built from current source, or clears `build/scv` after each wedge.

## Related

- `native_empty_dict_text_value_sigsegv_2026-07-20` — the P1 this session set out
  to reproduce; its own analysis ("the read side treats the tagged string handle
  as an i64 (`>>3` decode / raw compare)") is the same erased-type decode family.
- `parse_family_strips_option_jit_native_2026-08-02`,
  `interp_u64_high_bit_option_unwrap_corruption_2026-07-11`,
  `native_try_op_on_option_silent_wrong_2026-07-14` — the optional-payload family
  this belongs to.
- `stage2_native_class_field_text_dict_owner_lost_2026-09-14` — the sibling
  static-type-erasure defect on the native lane.

## Redeployed 2026-09-18 17:03 KST

`bin/release/aarch64-unknown-linux-gnu/simple` — the target of the `bin/simple`
symlink — was replaced with a seed built from `origin/main` at the time of the
build:

| | before | after |
|---|---|---|
| sha256 | `3d120a6f9ab5704b2225…` | `308de6af84db5c26e2c0…` |
| size | 50,093,192 B | 51,645,288 B |
| built | 2026-09-06 | 2026-09-18 |

Method: staged beside the target and swapped with `mv -f`, so the rename is
atomic and the 31 processes already running the old inode (MCP servers across
several sessions) were untouched; they pick the new binary up on their next
start. The previous binary is kept for rollback at
`bin/release/aarch64-unknown-linux-gnu/simple.stale-2026-09-06` (gitignored);
restoring it is a single `mv` back over the same path.

Verified through the deployed `bin/simple` after the swap:

- `scripts/check/check-deployed-binary-optional-unwrap.shs` — `PASS — 6 row(s)
  checked, default and interpret lanes agree` (it FAILED on 5 rows before).
- `test/01_unit/interpreter/optional_unwrap_payload_spec.spl` — 11/11.
- `test/01_unit/interpreter/mutate_through_index_shapes_spec.spl` — 7/7; its
  three dict-value examples failed on the old binary.
- The SCV cold init that this record documents as wedging every fresh worktree
  now publishes `generation=16797 count=16797` where it previously published
  `generation=0 count=0`.

The two source hardenings from #1084 stay in force, and are what makes a future
bad listing fail closed instead of poisoning the cache again.
