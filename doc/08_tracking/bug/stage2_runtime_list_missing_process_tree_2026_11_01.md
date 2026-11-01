# Frozen stage2 omits runtime_process_tree from its runtime source list

- **ID:** stage2_runtime_list_missing_process_tree_2026_11_01
- **Severity:** P1 (blocks every stage3 final link done by the frozen stage2)
- **Status:** open, workaround landed
- **Workaround tag:** `@workaround bug=stage2_runtime_list_missing_process_tree_2026_11_01`
- **Workaround:** `scripts/bootstrap/workarounds/stage2-runtime-process-tree-shadow.shs`

## Symptom

`C:/dev/p3new/stage2.exe` (== `stage2.ef0681fc0e1.exe`, built 2026-10-27)
emits stage3 objects. The final link then fails:

```
ld.lld: error: undefined symbol: rt_process_spawn_session
ld.lld: error: undefined symbol: rt_proc_start_time
```

Repro: `native-build --entry-closure --entry src/app/dashboard/main.spl
--source src/app --source src/lib --target x86_64-pc-windows-gnu --backend llvm
--runtime-bundle core-c-bootstrap`, run from a checkout at or past
`e2e83308682` (seen at phase3 tip `eb72b5c9fde`).

## Root cause

The runtime C source list is baked into the compiler
(`src/compiler/70.backend/backend/runtime_compiler.spl`, the core list at :647
and the full list at :739). `e2e83308682` ("session-owned process trees, one C
owner for every host") added `runtime_process_tree` to both lists and moved
`rt_process_spawn_session` / `rt_proc_start_time` into
`src/runtime/runtime_process_tree.c`. `runtime_native.c`, `runtime_process.c` and
`runtime_process_owned.c` call them.

`e2e83308682` lands after `ef0681fc0e1`
(`git log ef0681fc0e1..origin/release/1.0.0 -- runtime_compiler.spl` lists it). At
`ef0681fc0e1`, lines 631 and 723 of `runtime_compiler.spl` carry
`runtime_process` and `runtime_process_owned` but no `runtime_process_tree`. So
the frozen stage2 compiles the current C sources that reference the symbols, but
never the file that defines them. The link command
(`*.link-command.txt`, 41 `simple_rt_*` objects) confirms this: there is no
`runtime_process_tree.o`.

That stage2 has no CFLAGS hook, no extra-source env and no way to add a link
object. Managed links refuse `SIMPLE_LINK_OBJECTS`, and `--runtime-path` goes
through strict archive admission. The one runtime-source input it reads is
`SIMPLE_PROJECT_ROOT`, used only by `find_runtime_source_dir`. Nothing else in
that commit reads it, apart from the cache identity key.

## Workaround (semantics-neutral, no stage2 rebuild, checkout untouched)

`stage2-runtime-process-tree-shadow.shs <checkout> <shadow>` copies
`<checkout>/src/runtime` into `<shadow>/src/runtime`, along with the two header
dirs it includes relatively: `src/compiler/70.backend/backend_plugin/abi` and
`tools/counterpart/sdk/c`. The copy is byte-identical except for one change:
`runtime_process_owned.c`, which the old list does compile, gets
`#include "runtime_process_tree.c"` appended. The defined functions are the
same ones the current compiler links from its own `runtime_process_tree.o`.

Launcher contract for frozen-stage2 runs:

```sh
sh scripts/bootstrap/workarounds/stage2-runtime-process-tree-shadow.shs "$CHECKOUT" "$SHADOW"
export SIMPLE_PROJECT_ROOT="$SHADOW"
# Optional: keep the runtime-object cache separate from other lanes.
export SIMPLE_RT_OBJ_CACHE_DIR="$SHADOW.rtcache"
```

Regenerate the shadow whenever the checkout's `src/runtime` changes. **Do not**
set this for a compiler built from a commit at or past `e2e83308682`. Such a
compiler also compiles `runtime_process_tree.c` as its own object, which would
define the symbols twice.

## Removal

Delete the script and this env once stage2 is rebuilt from a commit containing
`e2e83308682`.
