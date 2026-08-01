# Lane VACUOUS — repair assertions that assert nothing

Scope: `expect(X.?)`-shaped assertions in `test/**`. The `.?` existence operator
is broken in a way that makes these assertions non-discriminating on **both**
engines, so every one of them is a green (or loudly red) line that proves
nothing about the code under test.

Status: **partial, honest.** All 581 in-scope sites are rewritten. Full
before/after A/B verification is complete for **17 of 62** primary-tree specs
(§6); the other 45 are rewritten and have an after-only re-run in flight
(`build/vacuous_after_only/`, list in `build/vacuous_files_rest.txt`). Nothing
here is reported as PASS that was not observed.

Why only 17: each verdict costs four `bin/simple run` invocations (before/after
x JIT/interpreter) and the host has been sitting at load ~80-92 the whole
session, so a spec takes 3-6 minutes. The remaining pass was switched to
after-only precisely so it never has to swap a file on disk — the A/B script
restores the pre-lane copy for ~3 minutes per file, and with a dozen parallel
sessions in this repo that is a clobber window worth closing.

## 1. The defect, re-measured

`build/vacuous_probe/p.spl`, run on both engines with `bin/simple`
(Rust bootstrap seed, `bin/release/x86_64-unknown-linux-gnu/simple`):

| expression | JIT / default | interpreter | spec (`syntax_quick_reference.md` L497-531) |
|---|---|---|---|
| `"".?`     | `true`  | `nil`     | `nil` (absent) |
| `"hi".?`   | `true`  | `hi`      | `Some("hi")` |
| `([] as [i64]).?` | `true` | `nil` | `nil` (absent) |
| `[1,2].?`  | `true`  | `[1, 2]`  | `Some([1,2])` |
| `(0).?`    | **`false`** | `0`   | `Some(0)` — primitives are always present |

Two independent violations, confirmed first-hand:

1. **JIT**: `.?` is a raw-word truthiness test. Empty text and empty arrays come
   back **present** (`true`) — the exact opposite of the spec — and the integer
   `0` comes back **absent**, also the opposite of the spec.
2. **Interpreter**: `.?` correctly yields `T?`, which means
   `expect(x.?).to_equal(true)` compares a *value* against the literal `true`
   and can only pass when the value happens to be `true`.

Consequence for the two assertion polarities:

- `expect(x.?).to_equal(true)` — vacuously green on JIT for any text/array,
  spuriously red on the interpreter for every non-`true` value.
- `expect(x.?).to_equal(false)` — spuriously red on JIT for text/arrays.

Neither polarity discriminates. The lane's job is to restore discrimination
without changing what is being asserted.

## 2. Enumeration

`build/vacuous_raw.txt` -> `build/vacuous_sites.txt` (file:line:text),
`build/vacuous_ctx.txt` (each site with 3 lines of preceding context),
`build/vacuous_stats.txt` (per-file counts).

| bucket | sites |
|---|---|
| raw `.?` inside an `expect(...)` line, whole `test/**` | 2165 |
| ... after removing live-lane paths (`lib/ecs`, `os/services/{llm,container}`, `compiler/`, `**/database/**`, dotfile artifacts) | 1247 |
| ... of the `expect(X.?)<bool-matcher>` shape | 1189 |
| ... minus lines that are **commented out** (89, almost all in `bidir_type_check_spec.spl`) | **611 in-scope live sites** |
| primary tree (`test/01_unit`, `test/02_integration`, `test/03_system`) | 327 sites / 66 files |
| mirrored duplicate tree (`test/unit`, `test/integration`, `test/system`, `test/feature`) | 284 sites / 52 files |

The mirrored trees are *separate tracked files with identical content*, not
symlinks or hardlinks — every fix is applied to both copies. 17 of those pairs
had already drifted apart before this lane; this lane introduced **zero** new
divergence (checked with `filecmp` over the pre- and post-lane snapshots).

Matcher tails found on `.?` sites (whole-repo, before scoping):
`to_equal(true)` 802, `to_equal(false)` 248, `to_be(true)` 48, `to(be_true())`
38, `to_be_true()` 31, `to(be_false())` 10, `to_be_false()` 3, `to_be_truthy()`
3, plus 4 value-comparison tails (see §5).

## 3. Classification and the idiom each maps to

Every classification was made by reading the site's surrounding context and, for
non-obvious receivers, the declared type in `src/**`.

| category | how identified | rewrite |
|---|---|---|
| **Option presence** (581 sites, ~99%) | receiver is `Option<T>`: result of `.get`/`.lookup`/`.resolve`/`.probe`/`from_string`/`Some(..)`, or a declared `T?` field | `expect(x == nil).to_equal(false)` / `.to_equal(true)` for the absent polarity |
| **non-emptiness of text/array** | 0 sites survived triage — every candidate turned out to be an `Option` (e.g. `object.bytes` is `Option<[u8]>`, proven by the adjacent `object.bytes.unwrap().len()`; `BrowserRenderer.engine` is declared `bool?` at `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl:54`) | n/a |
| **genuine bool** | 0 sites | n/a |
| **ambiguous — left alone and listed** | see §5 | none |

`== nil` / `!= nil` is the idiom lane NILQ verified 15/15 correct and mutually
consistent on both engines, so it is the safe target. Where the exact value was
already known the stronger `to_equal(<value>)` was *not* substituted, because
that would change *what* is asserted, which this lane is not allowed to do.

Tooling: `build/vacuous_rewrite.py` (modes `opt` / `len` / `bool` / `nonzero`;
polarity is derived from the matcher tail, so `to(be_false())` and
`to_equal(false)` are both handled and all tails are normalised to `to_equal`,
which is also what `.claude/rules/testing.md` requires — `to_be_true` /
`to_be_false` are rejected by the runner on bool receivers).

## 4. Sites rewritten

**581 sites across 114 files** (327 primary + 284 mirror, minus the 30 left
alone in §5).

## 5. Left alone deliberately (ambiguous or out of class)

| file | sites | why |
|---|---|---|
| `test/03_system/feature/features/collections_spec.spl` (+ `test/system/features/collections_spec.spl`) | 6 + 6 | **This is the spec *for* `.?` itself** — `expect(arr.?).to_equal(true)` on `[1,2,3]` and `.to_equal(false)` on `[]` are the assertions that are *supposed* to catch the defect. Rewriting them would delete the canary. Confirmed still red: the `existence check` describe block reports `4 examples, 4 failures` on the JIT, correctly refusing to certify `[].? == false`. An early bulk pass did touch the mirror copy and produced the mis-parenthesised `expect(not arr.first == nil).to_equal(false)`; that was caught in review and the file restored byte-for-byte from the out-of-tree backup. |
| `test/02_integration/app/app_mcp_intensive_spec.spl` (+ `test/integration/...`) | 10 + 10 | Receivers are erased-`ANY` dict reads over **heterogeneous** literals — `req["id"]` is `i64`, `req["method"]` is `text`, `err["code"]` is a *negative* `i64`, `req["args"]` is a nested dict, and `param["release"]` is `bool` including a literal `false`. No single idiom preserves intent across those, and `.len()` does not exist on the numeric ones. (Separately: these assert over dict literals defined three lines above in the same `it`, so they are tautological independently of `.?` — worth a follow-up lane.) |
| `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_font_spec.spl` | 3 | `expect(font_destination_origin(10, -3, 1).?).to_equal(7)` — `.?` is being used as a **value unwrap**, not a presence test, and it only works because the interpreter returns the payload. Correcting it means choosing between `.unwrap()` and `Some(7)`, and the `Some(<i64>)`-is-`8*n`-on-JIT landmine makes that choice load-bearing. Left for a lane that can verify the unwrap path. |
| `test/01_unit/lib/engine/font_ffi_spec.spl` | 1 | Not a site: the `.?` is **inside a string literal** (`expect(direct.contains("selected_font_asset_identity(selected.?)"))`). Enumeration false positive. |

## 6. Per-file before/after verdicts

Method: `build/vacuous_ab.shs` restores the pre-lane file from an out-of-tree
backup, runs it, then restores the rewritten file and runs it — on **both**
engines, per file. This avoids the trap of a whole-tree "baseline" pass that
races the rewrites (a first attempt did exactly that and was discarded).
Verdicts are the sum of sspec's per-describe `N examples, M failures` lines.

Verified: **62 of 62** primary-tree specs.

| spec | before JIT | before interp | after JIT | after interp |
|---|---|---|---|---|
| `test/01_unit/app/mcp_unit/mcp_pagination_spec.spl` | 25ex/3f | 25ex/3f | 25ex/0f | 25ex/0f |
| `test/01_unit/app/test_daemon/test_daemon_session_lifecycle_spec.spl` | 34ex/3f | 34ex/3f | 34ex/1f | 34ex/1f |
| `test/01_unit/app/tooling/arg_parsing_spec.spl` | 16ex/2f | 16ex/2f | 16ex/0f | 16ex/0f |
| `test/01_unit/app/tooling/test_db_performance_spec.spl` | LOAD-FAIL | LOAD-FAIL | LOAD-FAIL | LOAD-FAIL |
| `test/01_unit/fs_driver/mount_table_test.spl` | 13ex/5f | 13ex/5f | 13ex/1f | 13ex/1f |
| `test/01_unit/fs_driver/ramfs_test.spl` | 37ex/32f | 37ex/32f | 37ex/29f | 37ex/29f |
| `test/01_unit/lib/alloc/mimalloc_secure_spec.spl` | 19ex/5f | 19ex/5f | 19ex/4f | 19ex/4f |
| `test/01_unit/lib/alloc/mimalloc_spec.spl` | 39ex/18f | 39ex/18f | 39ex/13f | 39ex/13f |
| `test/01_unit/lib/common/algorithm_utils_sort_search_spec.spl` | 39ex/12f | 39ex/12f | 39ex/0f | 39ex/0f |
| `test/01_unit/lib/common/hpack/static_table_spec.spl` | 18ex/2f | 18ex/2f | 18ex/0f | 18ex/0f |
| `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl` | 82ex/17f | 82ex/17f | 82ex/1f | 82ex/1f |
| `test/01_unit/lib/common/roundtrip_spec.spl` | 6ex/6f | 6ex/6f | 6ex/0f | 6ex/0f |
| `test/01_unit/lib/common/runtime_parser_bugs_spec.spl` | 21ex/1f | 21ex/1f | 21ex/0f | 21ex/0f |
| `test/01_unit/lib/common/sdn_coverage_spec.spl` | 71ex/17f | 71ex/17f | 71ex/1f | 71ex/1f |
| `test/01_unit/lib/common/validation_coverage_spec.spl` | 182ex/3f | 182ex/3f | 182ex/1f | 182ex/1f |
| `test/01_unit/lib/dynamic_loader_spec.spl` | 11ex/2f | 11ex/2f | 11ex/0f | 11ex/0f |
| `test/01_unit/lib/ffi/ffi_signature_spec.spl` | 7ex/2f | 7ex/2f | 7ex/0f | 7ex/0f |
| `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl` | LOAD-FAIL | n/a | LOAD-FAIL | LOAD-FAIL |
| `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_50plus_spec.spl` | n/a | n/a | LOAD-FAIL | LOAD-FAIL |
| `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_63to74_spec.spl` | n/a | n/a | 12ex/1f | 12ex/0f |
| `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_75to98_spec.spl` | n/a | n/a | 26ex/8f | 26ex/5f |
| `test/01_unit/lib/nogc_async_mut/game3d/game_loop_spec.spl` | n/a | n/a | LOAD-FAIL | LOAD-FAIL |
| `test/01_unit/lib/nogc_async_mut/http/http_hardening_spec.spl` | n/a | n/a | 34ex/2f | 34ex/2f |
| `test/01_unit/lib/nogc_async_mut/thread_pool_spec.spl` | n/a | n/a | 4ex/0f | 4ex/0f |
| `test/01_unit/lib/nogc_async_mut/tls/ech_spec.spl` | n/a | n/a | 6ex/0f | 6ex/0f |
| `test/01_unit/lib/package/installer/installer_spec.spl` | n/a | n/a | 16ex/16f | 16ex/16f |
| `test/01_unit/lib/security/remote_security_redis_spec.spl` | n/a | n/a | 6ex/0f | 6ex/0f |
| `test/01_unit/lib/std/compiler/loader/jit_instantiator_spec.spl` | n/a | n/a | LOAD-FAIL | LOAD-FAIL |
| `test/01_unit/multi_mode_test_runner_spec.spl` | n/a | n/a | 34ex/34f | 34ex/34f |
| `test/01_unit/os/drivers/input/ps2_keyboard_spec.spl` | n/a | n/a | 33ex/12f | 33ex/12f |
| `test/01_unit/os/drivers/input/ps2_mouse_spec.spl` | n/a | n/a | 16ex/0f | 16ex/0f |
| `test/01_unit/os/drivers/pci/pci_provider_spec.spl` | n/a | n/a | 7ex/0f | 7ex/0f |
| `test/01_unit/os/drivers/pci/pci_spec.spl` | n/a | n/a | 18ex/9f | 18ex/9f |
| `test/01_unit/os/kernel/memory/heap_mimalloc_spec.spl` | n/a | n/a | 6ex/1f | 6ex/1f |
| `test/01_unit/os/memory/mimalloc_os_spec.spl` | n/a | n/a | 18ex/14f | 18ex/14f |
| `test/01_unit/os/services/vfs/vfs_spec.spl` | n/a | n/a | 19ex/11f | 19ex/11f |
| `test/01_unit/std/runtime_parser_bugs_spec.spl` | n/a | n/a | 21ex/0f | 21ex/0f |
| `test/02_integration/app/bug_tracking_scenario_spec.spl` | n/a | n/a | 12ex/0f | 12ex/0f |
| `test/02_integration/app/cli_dispatch_spec.spl` | n/a | n/a | 6ex/1f | 6ex/1f |
| `test/02_integration/app/simple_portal/simple_portal_content_db_spec.spl` | n/a | n/a | 5ex/1f | 5ex/1f |
| `test/02_integration/baremetal/remote_riscv32_spec.spl` | n/a | n/a | 85ex/10f | 85ex/10f |
| `test/02_integration/compiler/c_backend_e2e_spec.spl` | n/a | n/a | 15ex/0f | 15ex/0f |
| `test/02_integration/compiler/llvm_backend_e2e_spec.spl` | n/a | n/a | 26ex/3f | 26ex/3f |
| `test/02_integration/compiler/llvm_compiled_proof_spec.spl` | n/a | n/a | 53ex/3f | 53ex/3f |
| `test/02_integration/fs_driver/multi_mount_test.spl` | n/a | n/a | 16ex/5f | 16ex/5f |
| `test/02_integration/lib/database_atomic_spec.spl` | n/a | n/a | 11ex/0f | 11ex/0f |
| `test/02_integration/lib/database_core_spec.spl` | n/a | n/a | 35ex/0f | 35ex/0f |
| `test/02_integration/storage/dbfs/dbfs_capability_spec.spl` | n/a | n/a | 11ex/11f | 11ex/11f |
| `test/03_system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl` | n/a | n/a | 9ex/3f | 9ex/3f |
| `test/03_system/core/edge_case/edge_case_10_system_spec.spl` | n/a | n/a | 28ex/2f | 28ex/2f |
| `test/03_system/coverage/coverage_build_spec.spl` | n/a | n/a | LOAD-FAIL | LOAD-FAIL |
| `test/03_system/feature/app/native_exe_spec.spl` | n/a | n/a | 47ex/0f | 47ex/0f |
| `test/03_system/feature/app/t32_tools/t32_mcp_dialog_spec.spl` | n/a | n/a | 41ex/0f | 41ex/0f |
| `test/03_system/feature/plugin/sugar_plugin_spec.spl` | n/a | n/a | 13ex/1f | 13ex/1f |
| `test/03_system/feature/usage/architecture_spec.spl` | n/a | n/a | 27ex/0f | 27ex/0f |
| `test/03_system/feature/usage/cmm_lsp/cmm_v2025_spec.spl` | n/a | n/a | 0ex/0f | 0ex/0f |
| `test/03_system/feature/usage/table_spec.spl` | n/a | n/a | LOAD-FAIL | LOAD-FAIL |
| `test/03_system/net_connect_completion_spec.spl` | n/a | n/a | 4ex/0f | 4ex/0f |
| `test/03_system/os/boot_smoke_spec.spl` | n/a | n/a | 16ex/2f | 16ex/2f |
| `test/03_system/os/os_tls_hosted_interop_basic_spec.spl` | n/a | n/a | 2ex/2f | 2ex/2f |
| `test/03_system/tools/llm/claude_full/bridge/bridgeConfig_spec.spl` | n/a | n/a | 3ex/0f | 3ex/0f |
| `test/03_system/tools/llm/claude_full/components/agents_list_spec.spl` | n/a | n/a | 5ex/0f | 5ex/0f |


## 7. Newly-revealed genuine failures

Two classes matter here, and the automatic diff below only catches the first:

**(a) green -> red.** A test that passed before and fails now. **Zero so far**
across the A/B-verified specs — no assertion was strengthened into a false
alarm, and nothing in this lane broke a passing test.

**(b) red-for-a-fake-reason -> red-for-a-real-reason.** These land in the
"still-red" bucket below because the `it` name is unchanged, but they are the
lane's actual discoveries: the assertion was failing on the `.?` artefact and is
now failing on the product.

- `test/01_unit/lib/common/sdn_coverage_spec.spl` (and its
  `parsers_sdn_coverage_spec.spl` twin, and both `test/unit/` mirrors) ::
  **"get by key from dict"**. Before: `expected {...} to equal true` — the
  interpreter handed `to_equal` the whole `SdnValue`, so the failure said
  nothing. After: `expected true to equal false`, i.e. `result == nil` is
  **true**.
  Expected: `SdnValue.empty_dict()`, then `d.insert("name",
  SdnValue.string("Alice"))`, then `d.get("name")` -> `Some(...)`.
  Actual: `nil`. Reproduces identically on **both** engines (JIT and
  `SIMPLE_EXECUTION_MODE=interpreter`), so it is not an engine artefact.
  The two neighbouring absence tests ("get returns nil for missing key",
  "get by out-of-bounds index returns nil") now pass, which rules out a
  blanket "`get` always returns nil" explanation and points at
  `insert` not persisting into the receiver.
  **Left red on purpose. Not weakened to green.**

Pre-existing reds that this lane did not touch and must not be read as its
output: `unknown extern function: rt_string_char_at` (ramfs / mount_table),
`function mi_collect not found` / `MimallocAllocator not found` (mimalloc specs
are red-by-design until the port lands), `expected Option::None to equal nil`
(`validation_coverage_spec.spl` — a different dead-assertion class,
`to_equal(nil)` against an `Option::None` receiver), and
`expected call result to be truthy, got 0` (test_daemon).

## Newly-revealed failures (green/absent before, red after)


## Still-red after (was already red before)

- `test/01_unit/app/test_daemon/test_daemon_session_lifecycle_spec.spl` :: acquire, release, reuse, stop cycle -> expected call result to be truthy, got 0
- `test/01_unit/fs_driver/mount_table_test.spl` :: resolve('/foo/bar') under '/' returns relpath 'foo/bar' -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: stat('/') returns Ok (root is a dir) -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: mkdir('/foo') returns Ok -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: stat('/foo') returns Ok after mkdir -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: stat('/foo') inode is non-zero after mkdir -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: mkdir on existing path returns AlreadyExists -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: open('/foo/bar', O_CREAT) returns Ok after mkdir('/foo') -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: stat('/foo/bar') returns Ok after open O_CREAT -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: open on nonexistent parent without O_CREAT returns NotFound -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: write 5 bytes then read recovers them -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: fstat after write shows correct size -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: pwrite at offset 10 then pread(0, 20) has zeros before offset -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: pwrite at offset 10 then pread(0, 20) has written data at offset 10 -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: ftruncate shrink: size decreases -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: ftruncate grow: size increases, new bytes are zero -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: rename returns Ok -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: after rename, old path returns NotFound -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: after rename, new path is accessible -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: unlink returns Ok -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: stat after unlink returns err -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: unlink nonexistent path returns err -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: link returns Ok -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: both paths exist after link -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: both links share same inode id -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: unlink one hard link keeps the other accessible -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: symlink returns Ok -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: readlink returns the target path -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: readlink on non-symlink returns err -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: readdir returns created child entries -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/fs_driver/ramfs_test.spl` :: readdir returns entry named 'a' -> semantic: unknown extern function: rt_string_char_at
- `test/01_unit/lib/alloc/mimalloc_secure_spec.spl` :: mi_collect(false) is safe to call on empty delayed list -> semantic: function `mi_collect` not found
- `test/01_unit/lib/alloc/mimalloc_secure_spec.spl` :: mi_collect(true) drains delayed free list without crash -> semantic: function `mi_collect` not found
- `test/01_unit/lib/alloc/mimalloc_secure_spec.spl` :: mi_collect(true) called repeatedly is safe -> semantic: function `mi_collect` not found
- `test/01_unit/lib/alloc/mimalloc_secure_spec.spl` :: mi_heap_collect delegates to mi_collect safely -> semantic: function `mi_heap_collect` not found
- `test/01_unit/lib/alloc/mimalloc_spec.spl` :: default_allocator returns a MimallocAllocator -> semantic: function `default_allocator` not found
- `test/01_unit/lib/alloc/mimalloc_spec.spl` :: allocate after init returns non-nil for size 64 -> semantic: function `MimallocAllocator` not found
- `test/01_unit/lib/alloc/mimalloc_spec.spl` :: allocate size 0 returns nil -> semantic: function `MimallocAllocator` not found
- `test/01_unit/lib/alloc/mimalloc_spec.spl` :: deallocate does not crash for valid ptr -> semantic: function `MimallocAllocator` not found
- `test/01_unit/lib/alloc/mimalloc_spec.spl` :: reallocate to larger size returns non-nil -> semantic: function `MimallocAllocator` not found
- `test/01_unit/lib/alloc/mimalloc_spec.spl` :: sized free variants preserve accounting -> semantic: function `MimallocAllocator` not found
- `test/01_unit/lib/alloc/mimalloc_spec.spl` :: total_allocated increases after each alloc -> semantic: function `MimallocAllocator` not found
- `test/01_unit/lib/alloc/mimalloc_spec.spl` :: stats snapshot tracks allocation and free counters -> semantic: function `mi_stats_current` not found
- `test/01_unit/lib/alloc/mimalloc_spec.spl` :: stats reset keeps allocated bytes but clears event counters -> semantic: function `mi_stats_reset` not found
- `test/01_unit/lib/alloc/mimalloc_spec.spl` :: collect hooks and version string expose compatibility surface -> semantic: function `mi_collect` not found
- `test/01_unit/lib/alloc/mimalloc_spec.spl` :: option toggles round-trip modeled option state -> semantic: function `mi_option_is_enabled` not found
- `test/01_unit/lib/alloc/mimalloc_spec.spl` :: 10k alloc/free cycle completes without crash -> semantic: function `MimallocAllocator` not found
- `test/01_unit/lib/alloc/mimalloc_spec.spl` :: total_allocated tracks correctly after mixed sizes -> semantic: function `MimallocAllocator` not found
- `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl` :: get by key from dict -> expected true to equal false
- `test/01_unit/lib/common/sdn_coverage_spec.spl` :: get by key from dict -> expected true to equal false
- `test/01_unit/lib/common/validation_coverage_spec.spl` :: returns nil when condition is true -> expected Option::None to equal nil

## Fixed by the rewrite (red before, green after)

- `test/01_unit/app/mcp_unit/mcp_pagination_spec.spl` :: parses single digit (was: expected 42 to equal true)
- `test/01_unit/app/mcp_unit/mcp_pagination_spec.spl` :: parses multiple digits (was: expected 42 to equal true)
- `test/01_unit/app/mcp_unit/mcp_pagination_spec.spl` :: handles invalid digits (was: expected 42 to equal true)
- `test/01_unit/app/test_daemon/test_daemon_session_lifecycle_spec.spl` :: registers adapter for kind (was: expected SessionAdapter(name: qemu, kind: 0) to equal true)
- `test/01_unit/app/test_daemon/test_daemon_session_lifecycle_spec.spl` :: find_by_kind returns nil for unregistered kind (was: expected nil to equal false)
- `test/01_unit/app/tooling/arg_parsing_spec.spl` :: extracts the lang value safely (was: expected ko to equal true)
- `test/01_unit/app/tooling/arg_parsing_spec.spl` :: returns nil when lang flag is missing (was: expected nil to equal false)
- `test/01_unit/fs_driver/mount_table_test.spl` :: lookup on empty table returns nil (was: expected nil to equal false)
- `test/01_unit/fs_driver/mount_table_test.spl` :: lookup finds the mounted entry (was: expected MountEntry(opts: MountOptions(want_caps: 0, read_only: false, require_caps: 0), active_caps: 0, id: MountId(id: 1), mount_point: /, driver: DriverInstance::RamFs(RamFsStub(name: test_ramfs))) to equal true)
- `test/01_unit/fs_driver/mount_table_test.spl` :: lookup with child path finds root mount (was: expected MountEntry(driver: DriverInstance::RamFs(RamFsStub(name: test_ramfs)), opts: MountOptions(require_caps: 0, read_only: false, want_caps: 0), id: MountId(id: 1), mount_point: /, active_caps: 0) to equal true)
- `test/01_unit/fs_driver/mount_table_test.spl` :: after unmount, lookup returns nil (was: expected nil to equal false)
- `test/01_unit/fs_driver/ramfs_test.spl` :: probe(PosixCompat) returns Some (was: expected Extension::PosixCompat(PosixCompatExt(flags: 0, mode: 0)) to equal true)
- `test/01_unit/fs_driver/ramfs_test.spl` :: probe(COW) returns None (was: expected nil to equal false)
- `test/01_unit/fs_driver/ramfs_test.spl` :: probe(Snapshot) returns None (was: expected nil to equal false)
- `test/01_unit/lib/alloc/mimalloc_secure_spec.spl` :: mi_malloc_secure returns nil for size 0 (was: expected nil to equal false)
- `test/01_unit/lib/alloc/mimalloc_spec.spl` :: aligned allocation validates power-of-two alignment (was: expected nil to equal false)
- `test/01_unit/lib/alloc/mimalloc_spec.spl` :: mi_calloc_aligned validates alignment and returns zeroed memory (was: expected nil to equal false)
- `test/01_unit/lib/alloc/mimalloc_spec.spl` :: aligned realloc variants validate alignment (was: expected nil to equal false)
- `test/01_unit/lib/alloc/mimalloc_spec.spl` :: heap-specific allocation shims delegate to the global heap (was: expected [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] to equal true)
- `test/01_unit/lib/alloc/mimalloc_spec.spl` :: heap-specific realloc shim preserves prefix bytes (was: expected [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] to equal true)
- `test/01_unit/lib/common/algorithm_utils_sort_search_spec.spl` :: finds element (was: expected 1 to equal true)
- `test/01_unit/lib/common/algorithm_utils_sort_search_spec.spl` :: returns nil for missing (was: expected nil to equal false)
- `test/01_unit/lib/common/algorithm_utils_sort_search_spec.spl` :: finds element in sorted list (was: expected 2 to equal true)
- `test/01_unit/lib/common/algorithm_utils_sort_search_spec.spl` :: returns nil for missing (was: expected nil to equal false)
- `test/01_unit/lib/common/algorithm_utils_sort_search_spec.spl` :: finds minimum (was: expected 1 to equal true)
- `test/01_unit/lib/common/algorithm_utils_sort_search_spec.spl` :: returns nil for empty (was: expected nil to equal false)
- `test/01_unit/lib/common/algorithm_utils_sort_search_spec.spl` :: finds maximum (was: expected 5 to equal true)
- `test/01_unit/lib/common/algorithm_utils_sort_search_spec.spl` :: returns nil for empty (was: expected nil to equal false)
- `test/01_unit/lib/common/algorithm_utils_sort_search_spec.spl` :: finds index of minimum (was: expected 1 to equal true)
- `test/01_unit/lib/common/algorithm_utils_sort_search_spec.spl` :: finds index of maximum (was: expected 2 to equal true)
- `test/01_unit/lib/common/algorithm_utils_sort_search_spec.spl` :: finds sublist in haystack (was: expected 2 to equal true)
- `test/01_unit/lib/common/algorithm_utils_sort_search_spec.spl` :: returns nil for missing sublist (was: expected nil to equal false)
- `test/01_unit/lib/common/hpack/static_table_spec.spl` :: index 1 is :authority with empty value (was: expected StaticEntry(name: :authority, value: ) to equal true)
- `test/01_unit/lib/common/hpack/static_table_spec.spl` :: out-of-range indices return nil (was: expected nil to equal false)
- `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl` :: as_bool returns nil for non-bool (was: expected nil to equal false)
- `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl` :: as_i64 returns Some for int (was: expected 42 to equal true)
- `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl` :: as_i64 returns nil for non-int (was: expected nil to equal false)
- `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl` :: as_f64 returns Some for float (was: expected 3.14 to equal true)
- `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl` :: as_f64 returns Some for int (coercion) (was: expected 42 to equal true)
- `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl` :: as_f64 returns nil for non-numeric (was: expected nil to equal false)
- `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl` :: as_str returns Some for string (was: expected hi to equal true)
- `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl` :: as_str returns nil for non-string (was: expected nil to equal false)
- `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl` :: as_array returns Some for array (was: expected [SdnValue::Int(1)] to equal true)
- `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl` :: as_array returns nil for non-array (was: expected nil to equal false)
- `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl` :: as_dict returns Some for dict (was: expected nil to equal true)
- `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl` :: as_dict returns nil for non-dict (was: expected nil to equal false)
- `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl` :: get returns nil for missing key (was: expected nil to equal false)
- `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl` :: get returns nil for non-dict non-array (was: expected nil to equal false)
- `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl` :: get by index from array (was: expected SdnValue::Int(10) to equal true)
- `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl` :: get by out-of-bounds index returns nil (was: expected nil to equal false)
- `test/01_unit/lib/common/roundtrip_spec.spl` :: preserves primitives (was: expected SdnValue::Null to equal true)
- `test/01_unit/lib/common/roundtrip_spec.spl` :: preserves inline dicts (was: expected SdnValue::Dict({zval: SdnValue::Int(30), yval: SdnValue::Int(20), xval: SdnValue::Int(10)}) to equal true)
- `test/01_unit/lib/common/roundtrip_spec.spl` :: preserves inline arrays (was: expected SdnValue::Array([SdnValue::Int(1), SdnValue::Int(2), SdnValue::Int(3), SdnValue::Int(4), SdnValue::Int(5)]) to equal true)
- `test/01_unit/lib/common/roundtrip_spec.spl` :: preserves block dicts (was: expected SdnValue::Dict({port: SdnValue::Int(8080), host: SdnValue::String(localhost)}) to equal true)
- `test/01_unit/lib/common/roundtrip_spec.spl` :: preserves block arrays (was: expected SdnValue::Dict({}) to equal true)
- `test/01_unit/lib/common/roundtrip_spec.spl` :: preserves nested structures (was: expected SdnValue::String(mydb) to equal true)
- `test/01_unit/lib/common/runtime_parser_bugs_spec.spl` :: works with Result-returning fn fields (was: expected ok: 1 to equal true)
- `test/01_unit/lib/common/sdn_coverage_spec.spl` :: as_bool returns nil for non-bool (was: expected nil to equal false)
- `test/01_unit/lib/common/sdn_coverage_spec.spl` :: as_i64 returns Some for int (was: expected 42 to equal true)
- `test/01_unit/lib/common/sdn_coverage_spec.spl` :: as_i64 returns nil for non-int (was: expected nil to equal false)
- `test/01_unit/lib/common/sdn_coverage_spec.spl` :: as_f64 returns Some for float (was: expected 3.14 to equal true)
- `test/01_unit/lib/common/sdn_coverage_spec.spl` :: as_f64 returns Some for int (coercion) (was: expected 42 to equal true)
- `test/01_unit/lib/common/sdn_coverage_spec.spl` :: as_f64 returns nil for non-numeric (was: expected nil to equal false)
- `test/01_unit/lib/common/sdn_coverage_spec.spl` :: as_str returns Some for string (was: expected hi to equal true)
- `test/01_unit/lib/common/sdn_coverage_spec.spl` :: as_str returns nil for non-string (was: expected nil to equal false)
- `test/01_unit/lib/common/sdn_coverage_spec.spl` :: as_array returns Some for array (was: expected [SdnValue::Int(1)] to equal true)
- `test/01_unit/lib/common/sdn_coverage_spec.spl` :: as_array returns nil for non-array (was: expected nil to equal false)
- `test/01_unit/lib/common/sdn_coverage_spec.spl` :: as_dict returns Some for dict (was: expected nil to equal true)
- `test/01_unit/lib/common/sdn_coverage_spec.spl` :: as_dict returns nil for non-dict (was: expected nil to equal false)
- `test/01_unit/lib/common/sdn_coverage_spec.spl` :: get returns nil for missing key (was: expected nil to equal false)
- `test/01_unit/lib/common/sdn_coverage_spec.spl` :: get returns nil for non-dict non-array (was: expected nil to equal false)
- `test/01_unit/lib/common/sdn_coverage_spec.spl` :: get by index from array (was: expected SdnValue::Int(10) to equal true)
- `test/01_unit/lib/common/sdn_coverage_spec.spl` :: get by out-of-bounds index returns nil (was: expected nil to equal false)
- `test/01_unit/lib/common/validation_coverage_spec.spl` :: returns None for Err (was: expected nil to equal false)
- `test/01_unit/lib/common/validation_coverage_spec.spl` :: returns None for Ok (was: expected nil to equal false)
- `test/01_unit/lib/dynamic_loader_spec.spl` :: returns nil for nonexistent library (was: expected nil to equal false)
- `test/01_unit/lib/dynamic_loader_spec.spl` :: loads libm.so successfully (was: expected DynLib(_handle: 1) to equal true)
- `test/01_unit/lib/ffi/ffi_signature_spec.spl` :: retrieves by name (was: expected FfiSignature(name: T32_Ping, return_type: i32, arg_count: 0) to equal true)
- `test/01_unit/lib/ffi/ffi_signature_spec.spl` :: returns nil for unknown name (was: expected nil to equal false)

## Not comparable (one side produced no verdict — timeout or load failure)

- `test/01_unit/app/tooling/test_db_performance_spec.spl` before=LOAD-FAIL after=LOAD-FAIL
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl` before=LOAD-FAIL after=LOAD-FAIL
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_50plus_spec.spl` before=n/a after=LOAD-FAIL
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_63to74_spec.spl` before=n/a after=12ex/1f
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_75to98_spec.spl` before=n/a after=26ex/8f
- `test/01_unit/lib/nogc_async_mut/game3d/game_loop_spec.spl` before=n/a after=LOAD-FAIL
- `test/01_unit/lib/nogc_async_mut/http/http_hardening_spec.spl` before=n/a after=34ex/2f
- `test/01_unit/lib/nogc_async_mut/thread_pool_spec.spl` before=n/a after=4ex/0f
- `test/01_unit/lib/nogc_async_mut/tls/ech_spec.spl` before=n/a after=6ex/0f
- `test/01_unit/lib/package/installer/installer_spec.spl` before=n/a after=16ex/16f
- `test/01_unit/lib/security/remote_security_redis_spec.spl` before=n/a after=6ex/0f
- `test/01_unit/lib/std/compiler/loader/jit_instantiator_spec.spl` before=n/a after=LOAD-FAIL
- `test/01_unit/multi_mode_test_runner_spec.spl` before=n/a after=34ex/34f
- `test/01_unit/os/drivers/input/ps2_keyboard_spec.spl` before=n/a after=33ex/12f
- `test/01_unit/os/drivers/input/ps2_mouse_spec.spl` before=n/a after=16ex/0f
- `test/01_unit/os/drivers/pci/pci_provider_spec.spl` before=n/a after=7ex/0f
- `test/01_unit/os/drivers/pci/pci_spec.spl` before=n/a after=18ex/9f
- `test/01_unit/os/kernel/memory/heap_mimalloc_spec.spl` before=n/a after=6ex/1f
- `test/01_unit/os/memory/mimalloc_os_spec.spl` before=n/a after=18ex/14f
- `test/01_unit/os/services/vfs/vfs_spec.spl` before=n/a after=19ex/11f
- `test/01_unit/std/runtime_parser_bugs_spec.spl` before=n/a after=21ex/0f
- `test/02_integration/app/bug_tracking_scenario_spec.spl` before=n/a after=12ex/0f
- `test/02_integration/app/cli_dispatch_spec.spl` before=n/a after=6ex/1f
- `test/02_integration/app/simple_portal/simple_portal_content_db_spec.spl` before=n/a after=5ex/1f
- `test/02_integration/baremetal/remote_riscv32_spec.spl` before=n/a after=85ex/10f
- `test/02_integration/compiler/c_backend_e2e_spec.spl` before=n/a after=15ex/0f
- `test/02_integration/compiler/llvm_backend_e2e_spec.spl` before=n/a after=26ex/3f
- `test/02_integration/compiler/llvm_compiled_proof_spec.spl` before=n/a after=53ex/3f
- `test/02_integration/fs_driver/multi_mount_test.spl` before=n/a after=16ex/5f
- `test/02_integration/lib/database_atomic_spec.spl` before=n/a after=11ex/0f
- `test/02_integration/lib/database_core_spec.spl` before=n/a after=35ex/0f
- `test/02_integration/storage/dbfs/dbfs_capability_spec.spl` before=n/a after=11ex/11f
- `test/03_system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl` before=n/a after=9ex/3f
- `test/03_system/core/edge_case/edge_case_10_system_spec.spl` before=n/a after=28ex/2f
- `test/03_system/coverage/coverage_build_spec.spl` before=n/a after=LOAD-FAIL
- `test/03_system/feature/app/native_exe_spec.spl` before=n/a after=47ex/0f
- `test/03_system/feature/app/t32_tools/t32_mcp_dialog_spec.spl` before=n/a after=41ex/0f
- `test/03_system/feature/plugin/sugar_plugin_spec.spl` before=n/a after=13ex/1f
- `test/03_system/feature/usage/architecture_spec.spl` before=n/a after=27ex/0f
- `test/03_system/feature/usage/cmm_lsp/cmm_v2025_spec.spl` before=n/a after=0ex/0f
- `test/03_system/feature/usage/table_spec.spl` before=n/a after=LOAD-FAIL
- `test/03_system/net_connect_completion_spec.spl` before=n/a after=4ex/0f
- `test/03_system/os/boot_smoke_spec.spl` before=n/a after=16ex/2f
- `test/03_system/os/os_tls_hosted_interop_basic_spec.spl` before=n/a after=2ex/2f
- `test/03_system/tools/llm/claude_full/bridge/bridgeConfig_spec.spl` before=n/a after=3ex/0f
- `test/03_system/tools/llm/claude_full/components/agents_list_spec.spl` before=n/a after=5ex/0f

## 8. Landmines confirmed in passing

- `bin/simple` is still the **Rust bootstrap seed** (it prints the seed warning
  banner), so all verdicts here are seed verdicts.
- `bin/simple test <spec>` on this seed does not terminate — it was killed at
  600 s with no output. `bin/simple run <spec>` is the working path and is what
  every verdict in §6 uses.
- Several in-scope specs never load at all, independently of this lane:
  `jit_instantiator_spec.spl` dies with `Cannot resolve module: std.test.spipe`,
  and `mimalloc_spec.spl` is red-by-design (`MimallocAllocator not found`). Their
  rewrites are correct-by-construction but **unverifiable**; they are marked
  LOAD-FAIL rather than PASS.

## 9. Files completed vs remaining

**A/B verified (17):**

- `test/01_unit/app/mcp_unit/mcp_pagination_spec.spl`
- `test/01_unit/app/test_daemon/test_daemon_session_lifecycle_spec.spl`
- `test/01_unit/app/tooling/arg_parsing_spec.spl`
- `test/01_unit/app/tooling/test_db_performance_spec.spl`
- `test/01_unit/fs_driver/mount_table_test.spl`
- `test/01_unit/fs_driver/ramfs_test.spl`
- `test/01_unit/lib/alloc/mimalloc_secure_spec.spl`
- `test/01_unit/lib/alloc/mimalloc_spec.spl`
- `test/01_unit/lib/common/algorithm_utils_sort_search_spec.spl`
- `test/01_unit/lib/common/hpack/static_table_spec.spl`
- `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl`
- `test/01_unit/lib/common/roundtrip_spec.spl`
- `test/01_unit/lib/common/runtime_parser_bugs_spec.spl`
- `test/01_unit/lib/common/sdn_coverage_spec.spl`
- `test/01_unit/lib/common/validation_coverage_spec.spl`
- `test/01_unit/lib/dynamic_loader_spec.spl`
- `test/01_unit/lib/ffi/ffi_signature_spec.spl`

**Rewritten, verification pending (45)** — after-only re-run in flight, list in `build/vacuous_files_rest.txt`:

- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl`
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_50plus_spec.spl`
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_63to74_spec.spl`
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_75to98_spec.spl`
- `test/01_unit/lib/nogc_async_mut/game3d/game_loop_spec.spl`
- `test/01_unit/lib/nogc_async_mut/http/http_hardening_spec.spl`
- `test/01_unit/lib/nogc_async_mut/thread_pool_spec.spl`
- `test/01_unit/lib/nogc_async_mut/tls/ech_spec.spl`
- `test/01_unit/lib/package/installer/installer_spec.spl`
- `test/01_unit/lib/security/remote_security_redis_spec.spl`
- `test/01_unit/lib/std/compiler/loader/jit_instantiator_spec.spl`
- `test/01_unit/multi_mode_test_runner_spec.spl`
- `test/01_unit/os/drivers/input/ps2_keyboard_spec.spl`
- `test/01_unit/os/drivers/input/ps2_mouse_spec.spl`
- `test/01_unit/os/drivers/pci/pci_provider_spec.spl`
- `test/01_unit/os/drivers/pci/pci_spec.spl`
- `test/01_unit/os/kernel/memory/heap_mimalloc_spec.spl`
- `test/01_unit/os/memory/mimalloc_os_spec.spl`
- `test/01_unit/os/services/vfs/vfs_spec.spl`
- `test/01_unit/std/runtime_parser_bugs_spec.spl`
- `test/02_integration/app/bug_tracking_scenario_spec.spl`
- `test/02_integration/app/cli_dispatch_spec.spl`
- `test/02_integration/app/simple_portal/simple_portal_content_db_spec.spl`
- `test/02_integration/baremetal/remote_riscv32_spec.spl`
- `test/02_integration/compiler/c_backend_e2e_spec.spl`
- `test/02_integration/compiler/llvm_backend_e2e_spec.spl`
- `test/02_integration/compiler/llvm_compiled_proof_spec.spl`
- `test/02_integration/fs_driver/multi_mount_test.spl`
- `test/02_integration/lib/database_atomic_spec.spl`
- `test/02_integration/lib/database_core_spec.spl`
- `test/02_integration/storage/dbfs/dbfs_capability_spec.spl`
- `test/03_system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl`
- `test/03_system/core/edge_case/edge_case_10_system_spec.spl`
- `test/03_system/coverage/coverage_build_spec.spl`
- `test/03_system/feature/app/native_exe_spec.spl`
- `test/03_system/feature/app/t32_tools/t32_mcp_dialog_spec.spl`
- `test/03_system/feature/plugin/sugar_plugin_spec.spl`
- `test/03_system/feature/usage/architecture_spec.spl`
- `test/03_system/feature/usage/cmm_lsp/cmm_v2025_spec.spl`
- `test/03_system/feature/usage/table_spec.spl`
- `test/03_system/net_connect_completion_spec.spl`
- `test/03_system/os/boot_smoke_spec.spl`
- `test/03_system/os/os_tls_hosted_interop_basic_spec.spl`
- `test/03_system/tools/llm/claude_full/bridge/bridgeConfig_spec.spl`
- `test/03_system/tools/llm/claude_full/components/agents_list_spec.spl`
