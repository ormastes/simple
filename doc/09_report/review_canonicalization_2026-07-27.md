# Adversarial review — `cb7d2cc35e51` module-name canonicalization

**Target:** `cb7d2cc35e51` / local `584e74ece31d` — +120 lines, zero deletions, in
`src/compiler/80.driver/driver_source_loading.spl`.
**Mode:** read-only. No build was run. All line numbers are post-commit unless stated.
**Date:** 2026-07-27

## Verdict: **RISKY**

The canonicalization arithmetic is sound and I could not break it: it is empirically
collision-free, the fallback path cannot produce an empty or garbage name, and the
closure-path aliases provably cannot reach Phase 3 lowering. But **three claims in the
commit message are false or unverified**, the change silently renames the primary module
of every symlinked `src/app/*` tree (one of them to a bare `tool.*`), and it inflates the
Phase-2 source/registry population by a measured **1.76x** in the one pipeline with a
documented 64 GB OOM history. It should not be treated as validated until the single
probe in the last section is run.

---

## Findings, ranked by severity

### S1 — HIGH — "the bulk collector keeps the narrow legacy branches" is FALSE

The commit message states the bulk collector is deliberately left on the legacy branches.
It is not. The gate is an **ambient environment variable, not a call site**:

- `driver_source_loading.spl:186-187` — `_driver_entry_closure_mode()` reads
  `rt_env_get("SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE") == "1"`.
- `driver_source_loading.spl:768` — the **bulk** collector `_driver_collect_sources`
  calls `_driver_module_aliases(p, content, module_name)`.
- `driver_source_loading.spl:732` — the closure collector calls it too.

Both call sites take the new branch whenever that variable is `1` in the inherited
environment. It routinely is: `src/app/cli/bootstrap_main.spl:114`,
`src/app/cli/bootstrap_focused_native_build.spl:140-148`, and
`src/compiler/70.backend/backend/llvm_native_link.spl:1141` read/save/restore it, and
`src/app/cli/vhdl_compile_entry.spl:61` explicitly sets it to `"0"` because it leaks.

**Failure scenario.** A wrapper exports the var, then `driver.spl:481`
(`_driver_collect_sources(input_path)`) bulk-loads an explicit `--source` root with the
new 1.76x alias fan-out. That fan-out is currently kept out of Phase 3 only because
`parse_all_impl` (`driver.spl:635`) happens to gate on the *same* variable and dedupes via
`entry_ctx.sources = unique_entry_sources` (`driver.spl:657, 705`). The safety is
accidental coupling between two independent env reads, not a design. The author's own
comment at `driver_source_loading.spl:280-283` asserts the opposite invariant, so the next
maintainer who decouples the two flags reintroduces the ~28% duplicate-diagnostics /
duplicate-HIR regression the code at `driver.spl:611-613` was written to fix.

Secondary effect: `test/01_unit/compiler/driver/driver_source_loading_spec.spl:2,27,32`
calls `_driver_collect_sources` and `_driver_module_aliases` directly. Their return values
now depend on ambient environment state, so that spec is green-or-red by inheritance.

### S2 — HIGH — canonical name is amputated for `src/app/*` symlinks into `examples/`

`_driver_physical_module_name` (`driver_source_loading.spl:240-248`) is careful to
re-relativize against `rt_path_absolute(".")` rather than search for `/src/` — its own
docstring at `:243-245` says searching for `/src/` "would mis-split when the checkout
itself lives under a `.../src/...` directory". It then hands the result straight to
`_driver_module_name_from_path(rel)` (`:248`), which performs **exactly that search
internally** at `:71-73`:

```
val absolute_src = mod_path.find("/src/") ?? -1
if absolute_src >= 0:
    mod_path = mod_path.substring(absolute_src + 5)
```

Verified against the real symlink inventory (`readlink` on each):

| walked path | realpath target | canonical (new primary name) |
|---|---|---|
| `src/app/spostgre/main.spl` | `examples/spostgre/src/tool/main.spl` | **`tool.main`** |
| `src/app/mcp_t32/*.spl` | `examples/10_tooling/trace32_tools/t32_mcp/*` | `examples.10_tooling.trace32_tools.t32_mcp.*` |
| `src/app/t32_cli/*`, `src/app/t32_lsp_mcp/*` | same shape | same shape |
| `src/app/lsp/server.spl` | `src/lib/nogc_sync_mut/lsp/server.spl` | `lib.nogc_sync_mut.lsp.server` |
| `src/app/debug/coordinator.spl` | `src/lib/nogc_sync_mut/debug/coordinator.spl` | `lib.nogc_sync_mut.debug.coordinator` |

Because the canonical name is pushed **first** (`:298-299`) and
`_driver_unique_physical_sources` keeps the first entry per path, this amputated name
becomes the `module_name` of the `SourceFile` that Phase 3 lowers. `app.spostgre.main`
survives only as alias #2. The commit's "Follow-up (not done here)" paragraph acknowledges
that `src/app/lsp` needs a reverse route table, but does **not** acknowledge that the
change already flips those files' primary spelling today.

`tool.main` is additionally a single-segment package name, which trips the
`self_segs.len() < 2` early return in `resolve_package_sibling_symbols`
(`20.hir/hir_lowering/_Items/module_lowering.spl:927-928`) if that name is ever the
lowering key rather than the path.

### S3 — HIGH (conditional) — entry-symbol match can go false for symlinked entries

`llvm_module_is_native_entry`
(`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:111-115`) does:

```
module_name == llvm_module_name_from_entry_path(native_entry)
```

and `core_codegen.spl:132` feeds it `module.name`. `llvm_module_name_from_entry_path`
(`core_codegen.spl:66`) is one of the four byte-identical **path-lexical** copies — no
tier drop, no `std.`→`lib.` fold. If the MIR module name in the entry-closure path derives
from the driver's (now canonical) `SourceFile.module_name`, then `--entry
src/app/lsp/main.spl` produces `lib.nogc_sync_mut.lsp.main` on one side and `app.lsp.main`
on the other → `entry_main_symbol` false → **no `__simple_main` emitted** → link failure.

This is the precise regression the file's own comment at `driver_source_loading.spl:56-62`
records ("the drift made `entry_main_symbol` false for every out-of-tree entry -> no
`__simple_main` -> 0/19 matrix"). The stage-4 bootstrap entry
(`src/app/cli/bootstrap_main.spl`) is not symlinked, so its canonical == walked and
bootstrap itself is not exposed. Every userland entry under `src/app/{lsp,spostgre,
mcp_t32,t32_cli,t32_lsp_mcp}` is. The commit invalidates the four-copy byte-identity
invariant at the **value** level while leaving the code identical, which is why a
byte-identity check will not catch it.

### S4 — MEDIUM-HIGH — measured 1.76x alias growth into an OOM-prone pipeline

Static simulation of `_driver_module_aliases`' new branch over
`find -L src/{compiler,lib,app,runtime} -name '*.spl'` (12,498 files, vendor/node_modules/
test excluded), old rule vs new:

| | old | new | growth |
|---|---|---|---|
| alias `SourceFile` entries | 12,792 | 22,498 | **×1.76** |
| distinct registry keys | 12,302 | 19,140 | ×1.56 |

Per-file alias histogram (new): 2,734 files ×1, **9,528 ×2**, 236 ×3.

The ×2 bucket is almost entirely the unconditional `std.` twin at
`driver_source_loading.spl:166-167`, emitted for **every** `lib.*` file regardless of
whether anything in the closure imports `std.*`. That single line doubles the entire
stdlib tree's registry population.

Concretely: `driver.spl:611-613` records today's figure as "1723 aliases for 1303 physical
files in the full CLI closure". At ×1.76 that becomes ~3,030 entries. Each is a
`SourceFile` carrying `content`, and each becomes a key in `entry_modules: Dict<text,
Module>` (`driver.spl:685`) whose value is a parsed `Module`. Per the repo's own
value-semantics rule (arrays are value types, passed by copy), storing the same parsed
module under N keys is a candidate for N copies of the AST. This lands in the exact
no-GC bootstrap path with a documented history of being SIGTERM'd at a 64 GB
resource-monitor cap. The commit does not measure this and the memory delta is unstated.

### S5 — MEDIUM — recorded owner-module spelling can diverge from the definition site

`resolve_package_sibling_symbols` (`module_lowering.spl:913-947`) derives `self_name` from
`module.name` — the raw **path** under `SIMPLE_BOOTSTRAP=1` (`module_lowering.spl:92-96`) —
with no tier drop and no `std.` fold, then matches `modules_by_name` keys by
`pkg_prefix` and calls:

```
self.register_glob_imported_symbols(self.modules_by_name[sibling_name], sibling_name, sibling_span)
```

`sibling_name` is the **alias registry key**, and `register_imported_symbol` stores it as
the symbol's owner module (`Some(imported_mod_name)`, `module_lowering.spl:469, 483, 487,
491`). Downstream, owner names are re-derived through `hir_module_logical_name_from_path`
— e.g. `35.semantics/value_struct_layout.spl:26` builds the layout key
`hir_module_logical_name_from_path(module_name) + "|" + struct_name` — while the
**definition** site keys on the defining module's own path-derived name
(`module_lowering.spl:1145, 1350, 1372`).

Where two files in one package were walked through different spellings — the exact case
this commit makes resolvable — the use site now records the consumer's prefix spelling and
the definition site records the sibling's own path spelling. The HIR "unresolved name"
error disappears, but the struct-layout / mangled-call key can silently miss. **A loud HIR
error may be converted into a link error or wrong codegen at stage 4.** Nothing in the
commit tests this, and no build has run.

### S6 — MEDIUM — "canonical-first makes it deterministic" is only half true

`_driver_unique_physical_sources` (`driver_source_loading.spl:158-170`) keys on
`_driver_canonical_source_path(source.path)`, which is **purely lexical** and explicitly
does no symlink I/O (its docstring, `:102-105`: "Source discovery is repo-local, so
resolving `.`/`..`, repeated separators, and Windows separators is sufficient without
filesystem/symlink I/O").

- Within one `_driver_module_aliases` call every alias shares the same `path`
  (`:301-302`), so the first entry survives and canonical-first **does** hold. Claim
  verified for that case.
- But the same physical file reached under two lexically different paths
  (`src/std/x.spl` vs `src/lib/x.spl`; `src/app/lsp/x.spl` vs
  `src/lib/nogc_sync_mut/lsp/x.spl`) still yields two distinct keys → **two survivors →
  parsed and lowered twice** (`driver.spl:657-676`). This is unchanged by the commit,
  despite "Lowering stays once per physical file".
- It is arguably worse: both survivors now carry the **same** canonical `module_name`, so
  `entry_modules[source.module_name] = parsed_entry_modules[parsed_idx]`
  (`driver.spl:686`) overwrites, and which parse wins is again discovery-order dependent.
  The nondeterminism is relocated, not removed.

The one-line change the commit did **not** make: key
`_driver_unique_physical_sources` on `rt_path_absolute(source.path)` instead of the
lexical normalizer. That is where "once per physical file" is actually enforced.

### S7 — LOW / scope — non-closure paths keep the old inconsistent spellings. Plainly: yes.

`SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE` is set at `driver.spl:590` only under
`nb_entry_env != "" and ... self.ctx.options.mode == CompileMode.Aot` (`driver.spl:506`).
Therefore `bin/simple test`, `bin/simple run`, `CompileMode.Check`, LSP and MCP never take
the new branch and **retain the sibling-resolution bug this commit exists to fix**. The
fix is native-AOT-entry-closure only.

Additionally, `src/compiler/80.driver/driver_helpers.spl:85-107` holds a **fifth**,
divergent `_driver_collect_sources` that emits no aliases at all and does not even perform
the inner `/src/` strip — a pre-existing hazard the commit neither touches nor mentions.

### S8 — INFO — the correctness questions I tried to break, and could not

- **`rt_path_absolute` failure.** `_driver_physical_module_name:241-247` returns the
  lexical `fallback` on each of: empty resolved path, empty root, resolved path outside
  the root, and rel not under `src/`/`examples/`. **No empty or garbage module name is
  reachable.** `rt_path_absolute` is declared at `driver_source_loading.spl:21` in this
  file, as is `rt_env_get` at `:19` — no missing extern.
- **Digits-only directories with legitimate meaning.** The complete set of all-digit
  dotted segments across `src/**/*.spl` is `{00,10,15,20,25,30,35,40,50,55,60,70,80,85,
  90,95,99}` — every one a `src/compiler/NN.name` tier. `examples/10_tooling` survives
  (not all-digit). `_driver_module_name_segment_is_tier:194-195` correctly refuses the
  empty segment.
- **`std.`→`lib.` colliding with a genuinely different file.** `src/std` is a pure symlink
  to `lib` (`readlink src/std` → `lib`), so no physical file ever canonicalizes to `std.*`
  and the fold cannot merge two distinct files.
- **Collision-free claim.** Verified independently over 12,498 files: **0** new collisions
  introduced by tier-drop + `std.` fold, and **0** newly-colliding alias names. 163 names
  map to multiple physical files both before and after — all pre-existing, all from the
  inner-`/src/` amputation in `_driver_module_name_from_path:71-73` (e.g.
  `collections.btree` shared by `gc_async_mut`, `gc_sync_mut`, `nogc_async_mut`
  `.../src/collections/btree.spl`). Those are guarded from hard-erroring by the realpath
  comparison in `_driver_module_name_collision:178-180`.
- **Item 4 — do the kept special cases double-register?** No. The closure branch returns
  early at `:305` (`return closure_aliases`), before the legacy branches at `:307-327`.
  They are unreachable in closure mode, so no name is registered twice for one file. The
  `compiler.core.*` alias has no physical owner (`src/compiler/` has `00.common`, not
  `00.core`), so it cannot collide with a real module.
- **Item 3 — can closure aliases reach lowering?** No, verified independently.
  `driver.spl:705` sets `entry_ctx.sources = unique_entry_sources`, and every alias in one
  group shares `path`, so `_driver_unique_physical_sources` collapses them. Worst case is
  3 `SourceFile` entries per file (histogram above), all but one dropped before Phase 3.
- **Item 6 — `Dict.len()` / struct-valued `.get()`.** The new code uses **no `Dict` at
  all**: only array `.len()` and indexing (`_driver_push_unique_module_name:122-132`), and
  its docstring at `:123-124` explicitly cites the native `Dict.len() == -1` bug as the
  reason. Clean. (The pre-existing `Dict<text, text>` + `.get()` in
  `_driver_module_name_collision:173-183` is untouched and text-valued.)

---

## The single cheapest probe

**Run the driver in `CompileMode.Check` with the closure flag on and read one existing log
line — no codegen, no link, no bootstrap.**

```
SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1 SIMPLE_NATIVE_BUILD_ENTRY=src/app/cli/bootstrap_main.spl \
  <self-hosted simple> --check src/app/cli/bootstrap_main.spl 2>&1 \
  | grep 'phase2:parse:closure:sources'
```

`driver.spl:658` already prints `phase2:parse:closure:sources collected=N unique=M`. That
one line settles the three open questions at once:

- **N** validates or refutes S4 — it should be ~1723 before the change and ~3030 after. If
  N is materially higher than 3030, the memory risk is worse than modelled.
- **M** independently proves S1/item 3 — `M` must stay at 1303 (one per physical file). Any
  increase means aliases are reaching Phase 3 and the duplicate-lowering regression is live.
- **M > 1303 with N/M near 1** would instead confirm S6's two-lexical-paths duplicate.

Pair it with `--check` on a symlinked entry (`--entry src/app/lsp/...`) and grep for a
missing `__simple_main` / entry-module mismatch to settle S3. Both are parse-only and cost
seconds; neither is a build.

Not settled by any cheap probe: **S5**. It requires a stage-4 link and is the reason this
change should not be assumed safe until one runs.
