# Stage 2 Windows unresolved-symbol inventory (2026-08-31)

Authoritative, attributed inventory of every symbol the Windows Stage 2 link
cannot resolve. Read-only analysis; nothing was rebuilt.

Artifacts as of this measurement:

| artifact | mtime | size |
|---|---|---|
| `build/w/logs/x86_64-pc-windows-msvc/stage2-native-build.log` | 08:27 | 245,952 B |
| `build/w/stage3/x86_64-pc-windows-msvc/native-objects-1Spp4w/libspl_objects.a` | 08:27 | 20,863,030 B |
| `.../stage2-runtime-authority/simple_native_all.lib` | 07:14 | 354,283,286 B |
| `.../stage2-runtime-authority/simple_compiler_backfill.lib` | 07:14 | 12,564,412 B |

## Bottom line

**98 symbols** fail the link (`LNK1120: 98`). The archive-derived set is **100**;
the extra two (`_fltused`, `raise`) are supplied by the MSVC CRT and are not
errors. The two derivations agree exactly.

## Correction to the premise: the log was NOT truncated

The task warned the log may hold only a line or two. For this snapshot that is
false: it is 245,952 bytes, a single complete run, with 98 `LNK2019` lines and
one terminal `LNK1120: 98`. It is usable as a primary source here — but it is
still rewritten in place, so re-check its size before reusing it.

## Reproduction

```sh
export PATH=/c/dev/tool/msys2/mingw64/bin:$PATH          # DLLs; required
NM=/c/dev/install/clang+llvm-18.1.8-x86_64-pc-windows-msvc/bin/llvm-nm.exe
# (the mingw64 llvm-nm on PATH dies rc=127 with an empty error — use the full path)
cd /c/Users/ormas/dev/simple-rebase
D=build/w/stage3/x86_64-pc-windows-msvc
A=$D/native-objects-1Spp4w
export LC_ALL=C

"$NM" --undefined-only $A/libspl_objects.a | awk '{print $NF}' | sort -u > u.sym   # 6309
"$NM" --defined-only   $A/libspl_objects.a | awk '$1!="U"{print $NF}' | sort -u > d.sym  # 23944
comm -23 u.sym d.sym > need.sym                                                    # 541

for L in simple_native_all.lib simple_compiler_backfill.lib; do
  "$NM" --defined-only $D/stage2-runtime-authority/$L | awk '$1!="U"&&NF>1{print $NF}'
done | sort -u > rt.sym                                                            # 362011
comm -23 need.sym rt.sym > unres.sym                                               # 133

# the link also feeds three non-archive object sets from the same directory
"$NM" --defined-only $A/_init_all.o $A/_main_stub.o \
      $A/core_c_bootstrap_supplement/*.obj | awk '$1!="U"&&NF>1{print $NF}' \
      | sort -u > supp.sym                                                         # 2366
comm -23 unres.sym supp.sym > final.sym                                            # 100
```

`comm` requires `LC_ALL=C` on both inputs, and any log-derived list must be
`tr -d '\r'`-cleaned first; otherwise every comparison silently reports zero
overlap.

Cross-check against the linker:

```sh
grep -c LNK2019 build/w/logs/x86_64-pc-windows-msvc/stage2-native-build.log   # 98
comm -23 final.sym log.sym   # _fltused, raise      <- CRT-supplied
comm -13 final.sym log.sym   # (empty)
```

Exit statuses were read into a variable directly, never through a pipe.

The 33 symbols that `need.sym` lists but the link resolves come from
`core_c_bootstrap_supplement/*.obj` (`rt_iocp_*`, `rt_kqueue_*`,
`rt_event_ports_*`, `rt_process_*`, `rt_path_extension/filename`, `rt_text_*`,
`rt_sleep_secs`, `rt_time_ms`, `spl_dynlib_snapshot_linux`, ...) — they are in
the archive's undefined set only because they cross object files.

## Attribution

**98 of 98 (100%) attributed** — but *not* from the mangle-time warnings.

- `mangle.rs` `unresolved call` warnings across `build/w/logs/**` and
  `build/bootstrap-logs/**`: **1 line total**, covering `raise`
  (`compiler__hir__generated__hir_visitor__hir_walk_unhandled`). That lane
  covers **1/98**.
- The MSVC `LNK2019` lines carry object + symbol + referencing function and
  cover **98/98**. Note the localized (Korean) message concatenates symbol and
  function with **no separator and no quotes**; split by longest-prefix match
  against the known symbol set.

## Groups

Class key: **CODEGEN** = codegen emitted an unmangled Simple name;
**NO-NATIVE-DEF** = the extern exists only as an interpreter implementation in
`src/compiler_rust/compiler/src/interpreter_extern/`, with no `extern "C"` Rust
and no C definition anywhere in `src/`; **C-NOT-COMPILED** = a C definition
exists but its translation unit is not in the core-C build list; **CRT** =
supplied by the C runtime.

| # | group | n | class | examples | platform |
|---|---|---|---|---|---|
| A | `OutlineModule.*_push` | 14 | CODEGEN | `OutlineModule.functions_push`, `.imports_push` | indep |
| B | `str.*` free forms | 8 | CODEGEN | `str.lines`, `str.partition`, `str.parse_int_radix` | indep |
| C | `rt_simd_*` | 32 | NO-NATIVE-DEF | `rt_simd_add_f32x4`, `rt_simd_xor_u64x4` | indep |
| D | `rt_time_*` / `rt_timestamp_*` | 16 | NO-NATIVE-DEF | `rt_time_now`, `rt_timestamp_to_iso` | indep |
| E | `runtime.c` not compiled | 7 | C-NOT-COMPILED (**do not add the TU wholesale — see below**) | `rt_readdir`, `rt_mkdir`, `rt_random_i64` | indep |
| F | stdin / terminal | 4 | NO-NATIVE-DEF | `rt_stdin_read`, `rt_term_write` | indep |
| G | sffi io singles | 4 | NO-NATIVE-DEF | `rt_file_modified`, `rt_path_normalize` | indep |
| H | `LazyInstantiator.*` / `PreLexInfo.*` / `Array.data_ptr` | 5 | CODEGEN | `LazyInstantiator.load_metadata` | indep |
| I | system singles | 4 | NO-NATIVE-DEF | `rt_cpu_count`, `rt_uuid_v4`, `rt_shell`, `rt_process_output` | indep |
| J | string <-> byte array | 2 | NO-NATIVE-DEF | `rt_string_to_byte_array` | indep |
| K | event-loop `*_deregister` | 2 | C-NOT-COMPILED (partial stub) | `rt_iocp_deregister`, `rt_event_ports_deregister` | **Windows-relevant** |
| — | CRT (not link errors) | 2 | CRT | `_fltused`, `raise` | Windows-specific |

Sum of A..K = **98**; +2 CRT = the 100 the archive math yields.

### Platform-independence evidence

Everything except group K and the CRT pair is **platform-independent in
origin**, and the evidence is source-level, not build-level:

- Groups C, D, F, G, I, J: the names exist only as interpreter externs, e.g.
  `interpreter_extern/simd.rs:1102 pub fn rt_simd_add_f32x4`,
  `interpreter_extern/time.rs:68 pub fn rt_time_now`. There is **no**
  `extern "C" fn rt_simd_add_f32x4` in `src/compiler_rust/runtime/src` and no C
  definition in `src/runtime/**`. This is the documented "unbacked extern"
  class — a native build on any host would want the same definitions.
  `runtime_simd_dispatch.obj` *is* compiled, but it defines
  `rt_engine2d_simd_*`, `rt_mlkem_ntt_simd_*` and `rt_opencl_*` only; the
  generic `rt_simd_<op>_<lane>` family is a different, unimplemented surface.
- Group E: `src/runtime/runtime.c` defines all seven
  (`runtime.c:2206 rt_shell_output`, plus `rt_mkdir`, `rt_random_i64`,
  `rt_readdir{,_count,_entry,_free}`) and is **absent from the core-C source
  list** at `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs`
  (`build_c_runtime_library`, list starting line 341). The OS conditioning in
  that function comes later; the omission of `runtime.c` itself is
  unconditional. This is the same failure mode the list's own comments record
  for `runtime_contracts.c` (2026-07-30) and `runtime_terminal.c`.

  **But do NOT simply add `runtime.c` to that list.** Measured, same method as
  above: `runtime.c` defines 121 `rt_*` symbols, of which **53 already collide
  with `core_c_bootstrap_supplement/*.obj`** and **69 with the Rust runtime
  libs** (`rt_atexit_*`, `rt_atomic_*`, `rt_bdd_*`, `rt_bytes_to_text`,
  `rt_crc32_text`, ...). Adding the TU wholesale produces duplicate-definition
  failures — the same trap already recorded for `runtime_native.c`
  ("DISPROVE the 'just add runtime_native.c' fix — 475 symbol collisions,
  measured"). The correct move is to **extract the seven needed definitions into
  a small new TU** and add that, or resolve the 53/69 collisions deliberately.
  Reproduce with:

  ```sh
  grep -rn --include=*.c -E '^[A-Za-z_][A-Za-z0-9_ *]*\b(rt_[a-z0-9_]+)\s*\(' src/runtime > cdefs.txt
  grep '^src/runtime/runtime\.c:' cdefs.txt | grep -oE '\brt_[a-z0-9_]+\s*\(' \
    | sed 's/[ (]*$//' | sort -u > rc_def.txt     # 121
  comm -12 rc_def.txt supp.sym | wc -l            # 53
  comm -12 rc_def.txt rt.sym   | wc -l            # 69
  ```

  (Counts are a lower bound: the definition regex is line-anchored and misses
  multi-line signatures.)
- Groups A, B, H: codegen emits the source-level Simple name
  (`OutlineModule.functions_push`, `str.lines`) instead of a mangled symbol — a
  routing gap in the mangler, independent of target.
- **Group K is the one genuinely Windows-shaped item.**
  `core_c_bootstrap_supplement` defines `rt_iocp_{create,close,poll,register}`
  and `rt_event_ports_{create,close,poll,register}` but **not** the
  `_deregister` member of either family (verified by `llvm-nm --defined-only`
  over `core_c_bootstrap_supplement/*.obj`). That is an incomplete stub inside a
  file that *is* compiled — a different defect from every other group here, and
  it bites on Windows because `PlatformEvent.deregister` routes to IOCP.
- `_fltused` and `raise` are MSVC CRT concerns; the linker resolves both, so
  they need no work.

## Attributed subset (symbol -> referencing function -> module)

All 98, plus `raise` (CRT-resolved, not one of the 98; attributed via the one
mangle warning). `mod_NNN` is the archive member (`mod_NNN.o`).

| symbol | referencing function (module) | obj |
|---|---|---|
| `Array.data_ptr` | `lib__common__crypto__secure_memory__secure_zero_u8_range` | mod_706 |
| `LazyInstantiator.instantiate_all_missing` | `compiler__backend__linker__link__Linker.unify_hints` | mod_588 |
| `LazyInstantiator.load_metadata` | `compiler__backend__linker__link__Linker.load_inputs` | mod_588 |
| `OutlineModule.{actors,bitfields,classes,constants,enums,errors,exports,functions,impls,imports,static_asserts,structs,traits,type_aliases}_push` (14) | `compiler__frontend__treesitter__outline__TreeSitter.parse_outline` | mod_168 |
| `PreLexInfo.is_in_comment` | `compiler__blocks__blocks__builtin_blocks_math___math_lex` | mod_177 |
| `PreLexInfo.is_protected` | `compiler__blocks__blocks__builtin_blocks_math___math_treesitter_outline` | mod_177 |
| `str.is_alphabetic`, `str.is_alphanumeric`, `str.is_digit`, `str.is_whitespace` | `compiler__blocks__blocks__builtin_blocks_data__SqlBlockDef.highlight` | mod_175 |
| `str.join2` | `lib__nogc_async_mut__file_system__dir_ops__dir_list_detailed` | mod_755 |
| `str.lines` | `compiler__common__assurance__trust_audit__audit_lean_axiom_report` | mod_29 |
| `str.parse_int_radix` | `compiler__frontend__treesitter__outline_members__treesitter_parse_int_literal` | mod_171 |
| `str.partition` | `lib__log___syslog_parse_sd` | mod_741 |
| `rt_simd_*` (25 of 32) | `lib__nogc_sync_mut__simd__simd_<op>` | mod_814 |
| `rt_simd_{and,or,shl,shr,xor}_u64x4`, `rt_simd_shuffle_u8x16`, `rt_simd_vec4u64_get` (7) | `lib__nogc_sync_mut__simd_crypto__*` (incl. `Vec4u64.lane`) | mod_815 |
| `rt_time_{day,hour,millis,minute,month,now,now_iso,now_unix_millis,second,year}`, `rt_timestamp_{diff_seconds,from_iso,parse,to_iso,to_string}` (15) | `lib__nogc_sync_mut__sffi__system__*` | mod_812 |
| `rt_time_format` | `lib__nogc_sync_mut__io__time_ops__time_format` | mod_799 |
| `rt_cpu_count` | `lib__nogc_sync_mut__sffi__system___cpu_count_raw` | mod_812 |
| `rt_process_output` | `lib__nogc_sync_mut__sffi__system___sffi_system_process_output_raw` | mod_812 |
| `rt_random_i64` | `lib__nogc_sync_mut__sffi__system__random_i64` | mod_812 |
| `rt_shell` | `lib__nogc_sync_mut__sffi__system__shell` | mod_812 |
| `rt_shell_output` | `lib__nogc_sync_mut__sffi__system__shell_output` | mod_812 |
| `rt_uuid_v4` | `lib__nogc_sync_mut__sffi__system__uuid_v4` | mod_812 |
| `rt_file_modified`, `rt_file_modified_time`, `rt_list_dir_recursive`, `rt_path_normalize` | `lib__nogc_sync_mut__sffi__io__*` | mod_809 |
| `rt_mkdir` | `lib__nogc_async_mut__io__file__AsyncDir.mkdir` | mod_767 |
| `rt_readdir_count`, `rt_readdir_entry` | `lib__nogc_async_mut__io__file__AsyncDir.readdir` | mod_767 |
| `rt_readdir`, `rt_readdir_free` | `lib__nogc_async_mut__io__file__AsyncFile.write_all` | mod_767 |
| `rt_event_ports_deregister`, `rt_iocp_deregister` | `lib__nogc_async_mut__io__platform_event__PlatformEvent.deregister` | mod_769 |
| `rt_stdin_read`, `rt_stdin_read_all` | `lib__nogc_sync_mut__io__pipe__Stdin.{read,read_all}` | mod_793 |
| `rt_term_flush`, `rt_term_write` | `lib__nogc_sync_mut__io__pipe__{term_flush,term_write}` | mod_793 |
| `rt_string_from_byte_array`, `rt_string_to_byte_array` | `lib__common__string_core__string_{from,to}_byte_array` | mod_726 |
| `raise` | `compiler__hir__generated__hir_visitor__hir_walk_unhandled` | (mangle warning) |

The referencing function is a single call site per group in almost every case:
the entire 14-symbol `OutlineModule` group comes from **one** function,
`TreeSitter.parse_outline`; the 32 `rt_simd_*` from **two** modules; the 16
time/timestamp symbols almost all from `sffi/system`.

## Ownership

**Claimed as fixed but NOT present in this build** — the 08:27 artifact and log
both still show them unresolved. Stated as evidence, not as contradiction: the
fixes may exist and simply not have landed in the 08:27 stage2 run.

- `OutlineModule.*_push` (group A, 14) — reported fixed.
- `str.*` (group B, 8), `LazyInstantiator.*` / `PreLexInfo.*` / `Array.data_ptr`
  (group H, 5) — reported in flight.

**Confirmed already resolved** — `progress_*`, `spl_*` and `_abi_timestamp_*`
appear nowhere in the current 98. Those lanes landed.

**Not claimed by anyone (the real remaining work) — 71 symbols:**

| group | n | what it needs |
|---|---|---|
| C `rt_simd_*` | 32 | native `extern "C"` implementations (Rust runtime or a new C TU); today interpreter-only |
| D `rt_time_*` / `rt_timestamp_*` | 16 | same — 16 externs with no native backing |
| E `runtime.c` group | 7 | extract the 7 into a new TU and add THAT to the core-C list in `native_project/tools.rs`; adding `runtime.c` itself collides on 53/69 symbols |
| F stdin/terminal | 4 | native backing for `rt_stdin_read{,_all}`, `rt_term_{write,flush}` |
| G sffi io singles | 4 | `rt_file_modified`, `rt_file_modified_time`, `rt_list_dir_recursive`, `rt_path_normalize` |
| I system singles | 4 | `rt_cpu_count`, `rt_uuid_v4`, `rt_shell`, `rt_process_output` |
| J string<->bytes | 2 | `rt_string_{to,from}_byte_array` |
| K `*_deregister` | 2 | complete the IOCP / event-ports stubs — **Windows-blocking** |

Group K is the smallest and the only Windows-blocking one; groups C and D are 48
of the 71 and are one coherent job each. Group E is small but is **not** the
one-line fix it looks like — see the collision measurement above.

## Done criterion

Re-run the reproduction above against a fresh `native-objects-*` directory. The
build is finished when `final.sym` contains exactly `_fltused` and `raise`.
