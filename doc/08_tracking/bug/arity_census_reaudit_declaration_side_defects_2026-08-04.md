# Arity census re-audit: the declaration is not ground truth

**Date:** 2026-08-04
**Status:** 1 fix landed (`3c45274ba4b`); remainder filed below.

## Why this re-audit happened

A repo-wide call-site arity census checked 237,215 call sites and reduced
1,012 raw candidates to 154 "real" mismatches. It treated every **declaration**
as ground truth by construction: a cluster where N call sites disagreed with
one declaration was always scored as N call-site defects.

Its largest cluster was `wine_vm_commit` — reported as 4 declared parameters
and 96 call sites passing 3. That was **inverted**. The real signature always
had three parameters; `src/lib/common/wine_vm_adapter.spl` was an 89-line stub
that commit `3734fb4a868` re-grew from a 15-line remnant by guessing the API
after a tree wipe destroyed the real 322-line module. Every call site was
correct, and there were 109 of them, not 96.

**The rule the census lacked:** when every call site disagrees with a
declaration in the same way, that is evidence *against the declaration*.

## Measurement trap that nearly repeated the same error

The re-audit's first pass ran against a **stale local checkout**
(`53492af8dc4`), not `origin/main`. At that stale tree `wine_vm_adapter.spl`
was still 89 lines and `awk_tool.spl` still 421 lines, so both looked like
open defects. At the true base both were already restored (322 and 648 lines).
Roughly 127 of the 154 candidates were already dead before this audit started.

**Always re-derive the base from `git ls-remote` before scoring a census.** A
census scored against a stale tree manufactures defects that other lanes have
already fixed.

## Re-classification of all 154 candidates

| Class | Count | What |
|-------|-------|------|
| (ii) **declaration wrong** | **105** | 96 `wine_vm_commit` + 9 `dyn_torch_tensor_*` |
| (i) call sites wrong | 28 | genuine caller defects (20 already fixed by other lanes) |
| (iii) not a call at all | 21 | prose, doctests, AOP pointcuts, deliberate negative fixtures |

Plus the 9 `SAMEFILE` rows the census reported alongside the 154: 5
`_exec_action` (declaration side — `awk_tool.spl` truncation, since restored)
and 4 that are not calls (AOP pointcuts, `>>>` doctests).

**The census's central assumption failed on 68% of its own findings.** It was
right about the direction on only 28 of 154.

### (ii) Declaration wrong — 105

- **`wine_vm_commit` ×96** — the originating case. Fixed upstream before this
  audit; `wine_vm_adapter.spl` is 322 lines at base and declares
  `(space, base, perms)`. All 109 call sites agree.
- **`dyn_torch_tensor_{sum,mean,max,min}_dim`, `argmax`, `argmin`, `slice` ×9**
  — **fixed here, `3c45274ba4b`.** See below.

### (i) Call sites wrong — 28

Still open (8): `terminal_execute` ×1 (passes a `timeout_ms` the declaration
has no parameter for), `scv_export_git_fast_import` ×1 (omits `since`),
`read_log` ×1 (passes 1 of 3), `gui_adapter_new` ×1 (passes 0 of 1),
`compile_options_hash_compute` ×2 (5 of 7; 26 sibling call sites pass 7),
`generate_csrf_token` ×2 (0 of 2, in the stale `test/unit/` duplicate tree
only — the `test/01_unit/` copy is correct).

Already fixed by other lanes (20): `glass_tokens_to_css` ×18,
`build_tree_with_title` ×2 — plus `tool_awk` ×1, counted under `awk_tool.spl`.

Not padded, deliberately: the correct argument *value* is not derivable
(what timeout? which `since` revision? which GUI mode?). Padding a call site
with a guessed value is the same error as guessing a declaration.

### (i) but dead code — the callers never compiled

Two clusters have **unanimous** call-site disagreement yet a coherent,
complete, self-consistent declaration. Unanimity did **not** mean the
declaration was wrong here:

- **`ifconfig` 3/3 pass 0 args.** `src/os/userlib/net.spl` declares
  `ifconfig(if_index: u32) -> Result<NetIfInfo, text>` and implements it over
  syscall 77 for one interface. All three callers write `val ifaces =
  ifconfig()` and then `for iface in ifaces` / `ifaces.len()` — iterating a
  `Result`. The callers were written against an `ifconfig() -> [NetIfInfo]`
  that has never existed.
- **`verify_rv64_qemu_user_proof_contract` 4/4 pass 1 arg.**
  `riscv_formal.spl` declares `(code_start: i64, exit_code: i64)` and forwards
  to `rt_ghdl_verify_return_zero_contract(code_start, exit_code, "rv64")`.
  All four callers pass a single `output` text.

**Refinement of the rule:** unanimous call-site disagreement is evidence
against the declaration *only when the declaration shows independent stub or
reconstruction signs*. When the declaration is coherent and the callers are
incoherent — calling `.len()` on a `Result` — the callers are the dead side.
Check which side is internally consistent, not just which side is outnumbered.

### (iii) Not calls — 21

The census's docstring filter let these through:

- `glass_tokens_to_css` ×6 and `tool_awk` ×2 — **markdown prose** inside spec
  files (`- glass_tokens_to_css() emits ...`, `| tool_awk | Entry fn: ... |`).
- `hart64_step_body`, `hart32_step_body` — **AOP pointcut syntax**,
  `on pc{ execution(* hart64_step_body(..)) }`. Not calls.
- `spawn_isolated` ×2 — `>>>` doctest lines using trailing-closure syntax.
- `cooperative_green_spawn`, `green_spawn`, `multicore_green_spawn`,
  `multicore_green_spawn_sliced`, `thread_spawn` ×5 — deliberate negative
  fixtures under `test/fixtures/concurrency_api_misuse/`, whose filenames are
  literally `*_wrong_arity.spl`. Wrong arity is the point.

## Fixed: 7 cross-crate ABI arity defects (`3c45274ba4b`)

`src/runtime/torch_sffi.h` is the authority — it is what the linker binds to.
Seven `extern fn rt_torch_torchtensor_*` in
`src/lib/common/torch/dyn_sffi_ops.spl` declared **one parameter fewer** than
the C header, and the public `dyn_torch_tensor_*` wrappers propagated it:

| symbol | C header | Simple (before) |
|--------|----------|-----------------|
| `rt_torch_torchtensor_sum_dim` | `(handle, dim, bool keepdim)` | `(handle, dim)` |
| `rt_torch_torchtensor_mean_dim` | `(handle, dim, bool keepdim)` | `(handle, dim)` |
| `rt_torch_torchtensor_max_dim` | `(handle, dim, bool keepdim)` | `(handle, dim)` |
| `rt_torch_torchtensor_min_dim` | `(handle, dim, bool keepdim)` | `(handle, dim)` |
| `rt_torch_torchtensor_argmax` | `(handle, dim, bool keepdim)` | `(handle, dim)` |
| `rt_torch_torchtensor_argmin` | `(handle, dim, bool keepdim)` | `(handle, dim)` |
| `rt_torch_torchtensor_slice` | `(handle, dim, start, end, step)` | `(handle, dim, start, end)` |

Calling a C function through a declaration one argument short leaves the
trailing parameter reading whatever is in the register — silent, not a
compile error.

Three independent lines of evidence put the defect on the declaration:

1. The **C header** declares the longer arity.
2. **All 9 call sites** in `torch_ndarray.spl` already passed it.
3. **`src/lib/gc_async_mut/torch/backend.spl` and `ops.spl`** import these same
   symbols and call them with the full arity
   (`rt_torch_torchtensor_sum_dim(h, dim, keepdim)`,
   `rt_torch_torchtensor_argmax(logits, 1, false)`).

Padding the call sites — the census's prescription — would have cemented the
wrong ABI in place.

**Proof by value:** a cross-check of every `extern fn rt_torch_*` against
`torch_sffi.h` reported **13** arity mismatches before, **6** after.
**Sabotage-verified:** restoring the 2-parameter `sum_dim` extern makes the
check report it again; shortening the `argmax` wrapper makes its call site
diverge again; both clean after restore.

## Open: 6 more torch ABI mismatches (not fixed — would require a guess)

The 6 survivors take a `SplArray* dims` in C but are declared with five scalar
dimension parameters in Simple:

| symbol | C header | Simple |
|--------|----------|--------|
| `rt_torch_tensor_zeros` | `(SplArray* dims)` | `(d0, d1, d2, d3, ndim)` |
| `rt_torch_tensor_ones` | `(SplArray* dims)` | `(d0, d1, d2, d3, ndim)` |
| `rt_torch_tensor_rand` | `(SplArray* dims)` | `(d0, d1, d2, d3, ndim)` |
| `rt_torch_tensor_randn` | `(SplArray* dims)` | `(d0, d1, d2, d3, ndim)` |
| `rt_torch_tensor_empty` | `(SplArray* dims)` | `(d0, d1, d2, d3, ndim)` |
| `rt_torch_tensor_full` | `(SplArray* dims, double)` | `(d0, d1, d2, d3, ndim, fill)` |

Fixing these needs the array-marshalling contract, not an arity edit. Filed
rather than guessed.

## Wipe-casualty sweep across owned `src/`

Method: for every `src/**.spl` at base, compare the current blob against the
largest historical blob for that path. 722 files are under 70% of their
historical maximum — but most are legitimate refactors, so a size drop alone
proves nothing. The discriminator that matched the `wine_vm_adapter` /
`awk_tool` signature is: **the file lost `fn` definitions, and a lost symbol
is still referenced somewhere while being defined nowhere in the tree.** A
split moves the definition, so it stays defined and is filtered out.

Confirmed instances:

| module | current | last intact | lost symbols still referenced |
|--------|---------|-------------|-------------------------------|
| `src/lib/nogc_sync_mut/js/engine/interpreter.spl` | 616 lines / 23,099 B | 165,652 B (13%) | `_find_class_proto`, `_is_object_frozen`, `_json_stringify`, `_json_parse_allocated`, and more |
| `src/lib/gc_async_mut/gpu/browser_engine/text_painter.spl` | 302 lines / 11,690 B | 16,168 B | `browser_render_vector_font_probe_pixels` |

Already repaired before this audit, recorded for the family:
`src/lib/common/wine_vm_adapter.spl` (89 → 322 lines) and
`src/os/tools/shell/awk/awk_tool.spl` (421 → 648 lines; had lost 9 functions
and referenced 3 — `_resolve_multi_expr`, `_exec_printf`, `_exec_assign` —
that it no longer defined).

### Why these two were NOT restored

Neither is a clean truncation; both are **divergent rewrites**, and restoring
wholesale would destroy newer work.

`text_painter.spl`: the historical version defines 14 functions the current
one lacks, but the current one defines **15 the historical one lacks** and
carries 288 lines that never existed in it (`_strip_tags`, `_wrap_text`,
`_estimate_char_width_px`, the famous-site corpus layout paths). Two lineages,
not one truncation. The same applies to the JS interpreter.

The dangling references are real defects either way — four symbols in the JS
engine are referenced by `interpreter_async.spl`, `interpreter_object.spl` and
`interpreter_native.spl` (in both the `gc_async_mut` and `nogc_async_mut` tier
copies) while being defined nowhere in owned `src/`. Repair needs a per-symbol
decision about which lineage is authoritative — exactly the judgement that,
skipped, produced the `wine_vm_adapter` stub in the first place.

## Recommendation for the census tooling

1. **Score direction, not just mismatch.** For every cluster, report the arg
   count distribution over *all* call sites. A 100%-disagreement cluster is a
   declaration suspect; a 4-of-34 cluster is a call-site suspect.
2. **Check the declaring file for stub signs** — dramatically shorter than its
   historical maximum, referencing symbols it does not define, re-created from
   a remnant.
3. **Prefer an external authority where one exists.** For `extern fn`, the C
   header settles it with no inference at all.
4. **Re-derive the base from `ls-remote`** before scoring anything.
