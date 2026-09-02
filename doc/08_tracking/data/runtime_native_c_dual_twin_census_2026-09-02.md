# runtime_native.c dual-implementation census and backlog (2026-09-02)

Scope: `src/runtime/runtime_native.c`. Method and counts are reproducible from
the commands recorded in this file; every number below was MEASURED, not estimated.

## Counting method (matters -- an earlier report was inflated by it)

```sh
# C definitions: a line that opens rt_NAME( and does NOT end in ';' (excludes prototypes)
grep -nE '^[A-Za-z_][A-Za-z0-9_ ]*\**[[:space:]]*rt_[A-Za-z0-9_]+[[:space:]]*\(' src/runtime/runtime_native.c \
  | grep -v ';[[:space:]]*$' | grep -oE 'rt_[A-Za-z0-9_]+' | sort -u
# Simple twins: DEFINITIONS only. Grepping all rt_* tokens is WRONG -- simple_core/*.spl
# declares 43 'extern fn rt_*' that call INTO C and are the opposite of a twin.
grep -hoE '^(pub )?fn (rt_[A-Za-z0-9_]+)' src/runtime/simple_core/*.spl | grep -oE 'rt_[A-Za-z0-9_]+' | sort -u
```

| quantity | count |
|---|---|
| C definitions in runtime_native.c | 845 |
| pure-Simple definitions in simple_core/*.spl (19 files) | 335 |
| of those, `extern fn rt_*` declarations (NOT twins) | 43 |
| runtime_native.c symbols that HAVE a simple_core twin | 224 |
| **runtime_native.c C-only, needing a twin** | **621** |

## Class breakdown of the 621 C-only symbols

| class | count | meaning |
|---|---|---|
| (a) implementable in pure Simple | 142 | pure computation: string/array/dict/math/format |
| (b) needs a syscall or OS primitive | 245 | file/process/thread/time/net/event-loop, plus external-library FFI (gpu, opengl, oneapi) |
| (c) inherently C-only | 234 | value tagging, pointer arithmetic, ABI shims, allocator internals |

Honest note on class (b): a "pure Simple" version of these would declare the same
`extern` and call the same primitive. That is still worth doing where it buys a
dual-run oracle for the surrounding LOGIC, but it is not a C-to-Simple migration
and must not be counted as one.

External-library FFI bindings (rt_host_gpu 28, rt_io_tcp 24, rt_io_udp 15,
rt_intel_engine2d 11, rt_opengl_draw 7, rt_oneapi 14, rt_webgpu 3) are inside (b)
and a pure-Simple twin is meaningless for them -- excluded from any paydown target.

## The real constraint: only 23 of the 142 class-(a) symbols are wireable

A dual-run pair needs its C oracle REGISTERED in the tree-walk interpreter's
extern dispatch (`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`,
2067 registered names). An unregistered extern silently returns nil, so a pair
built on one would certify agreement that never happened.

Intersection of class (a) with the registered set -- the ENTIRE wireable population:

  - rt_actor_recv
  - rt_array_free_deep
  - rt_black_box
  - rt_bytes_alloc
  - rt_bytes_from_raw
  - rt_bytes_to_text
  - rt_bytes_u8_at
  - rt_bytes_u8_set
  - rt_cpuid
  - rt_gui_get_glyph_8x16
  - rt_heap_registry_count
  - rt_math_pow
  - rt_mem_guard_stats
  - rt_memory_barrier
  - rt_print
  - rt_provider_query_v1_call
  - rt_random_hex
  - rt_shell_exec
  - rt_string_free
  - rt_text_is_ascii
  - rt_text_to_bytes
  - rt_text_to_lower_ascii
  - rt_text_to_upper_ascii

## Prioritised backlog

### P1 -- DONE this change (dual_run_tranche_c_spec.spl)
  - rt_text_to_lower_ascii  <- std.common.text_ascii.to_lower_ascii      (13 cases)
  - rt_math_pow             <- std.common.pow_pure.pow_int_exp_f64       (36 cases)

### P2 -- wireable, twin still to write
  - rt_bytes_u8_at, rt_bytes_u8_set : pure byte indexing. Write a twin that does
    NOT bottom out in the same builtin indexing, or the pair proves nothing.
  - rt_bytes_to_text, rt_text_to_bytes : the existing std.common.string_core
    versions route through the same runtime, so they are shared-implementation
    and NOT admissible; base_encoding.text_to_bytes_linear has the same problem.
    Needs a genuinely independent UTF-8 encoder first.
  - rt_gui_get_glyph_8x16 : a pure table lookup, mechanically easy, low value.

### P3 -- registered but NOT admissible as pairs, with the reason
  - rt_random_hex : non-deterministic. No value compare exists.
  - rt_print : side-effecting; needs record-compare mode, not value mode.
  - rt_cpuid, rt_memory_barrier, rt_black_box, rt_heap_registry_count,
    rt_mem_guard_stats : host- or run-dependent results.
  - rt_bytes_alloc, rt_bytes_from_raw, rt_string_free, rt_array_free_deep :
    allocator ABI; class (c) in substance despite the pure-looking name.
  - rt_actor_recv, rt_shell_exec : class (b), blocking/OS.
  - rt_text_is_ascii, rt_text_to_upper_ascii : ALREADY paired in
    test/01_unit/lib/common/spec/dual_run_shadow_spec.spl:345-346.

### P4 -- the 119 class-(a) symbols whose oracle is UNREGISTERED
Blocked on registration, not on Simple. Highest-value families, measured:
  rt_string_* (capitalize, center, chomp, find_all, is_alnum, char_count),
  rt_pred_is_* (alnum, alpha, digit, space), rt_ascii_lower/upper/punct,
  rt_str* (strcat, strcmp, strfind, strsplit, strreplace, substr),
  rt_array_* (all, any, at, filter, find, map, reduce, each, join_any),
  rt_sort/rt_sort_cmp/rt_reverse, rt_sha256_compress/rt_sha256_rotr.
Each needs an interpreter_extern registration before a pair can be honest.

## Correction to a prior report

The claim that `@dual_pair` "appears zero times in the tree" is WRONG.
Measured: 32 matching lines (30 pair annotations + 2 doc lines) across five
specs under test/01_unit/lib/common/spec/, which is exactly what
check-dual-run-shadow.shs reports as "30 pairs". Verify with:
```sh
grep -rn '@dual_pair' test/ --include='*.spl' | wc -l   # 32
```
(A `grep` over src/ only, or the .gitignore-honouring wrapped ugrep, misses them.)

There are TWO distinct twin mechanisms and they must not be conflated:
  1. `src/runtime/simple_core/*.spl` -- pure-Simple reimplementations of the
     runtime ABI, SAME name (`pub fn rt_math_sqrt`). 335 of these. The dual-run
     gate does not see them.
  2. dual-run pure twins under `src/lib/**`, with DIFFERENT names, paired to a C
     oracle by a `# @dual_pair:` comment in a spec file. Only these are gated.
