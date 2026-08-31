# POSIX-gated runtime symbols "invisible on Windows" — the 90 is REFUTED; the real gap is file selection, not `#if`

- **Date:** 2026-08-31
- **Status:** OPEN as a **guard gap**. The *symbol population* claimed by the
  triggering finding does not exist.
- **Host:** `MINGW64_NT-10.0-26200`, main checkout `C:\Users\ormas\dev\simple`.
- **Method:** read-only. No build, no bootstrap, no `bin/simple` invocation.
- **Refutes:** `doc/08_tracking/bug/rt_c_vs_simple_coverage_census_2026-08-31.md`
  §4 and §6 ("Secondary, and genuinely unfiled: the 90 POSIX-gated symbols").
- **Confirms and refines:**
  `doc/08_tracking/bug/bootstrap_stage2_windows_link_unresolved_rt_and_dup_kernel32_2026-08-24.md`
  (the 68 / 31 / 37 split), `doc/08_tracking/bug/c_runtime_source_list_divergence_2026-08-30.md`
  (three C source lists).

---

## 1. The claim under test

The census reported:

> POSIX-gated-only, referenced, and with **no** Simple body — **90**
> … On Windows they resolve to nothing.

## 2. Verified answer: **0**, not 90

Derived independently, with a three-valued C-preprocessor evaluator rather than
a "does a platform macro appear anywhere in an enclosing conditional" text test.

| measurement | count |
|---|---|
| non-vendored `src/runtime/**/*.c` scanned | 120 |
| `rt_*` definition sites found | 2,161 |
| ... `static` (cannot back a Simple `extern`) | 337 |
| ... inside at least one platform conditional | 421 |
| distinct non-`static` `rt_*` names defined in C | 1,338 |
| **names with NO Windows-reachable C definition** | **9** |
| ... of those, referenced from any `.spl` | **0** |
| **→ referenced, POSIX-gated-only, no Simple body, no Rust def** | **0** |

The 9, with their gates, are entirely test hooks and raw Linux syscall wrappers:

```
rt_epoll_create / rt_epoll_ctl / rt_epoll_wait   platform/async_linux_epoll.c  [if defined(__linux__)]
rt_browser_renderer_namespaces_active            runtime_process.c  [else-of ifdef _WIN32] && [ifdef __linux__]
rt_browser_renderer_preinit_active_for_test      runtime_process.c  [same]
rt_process_owned_test_force_collision            runtime_process_owned.c
rt_process_owned_test_force_read_failure           [if !defined(_WIN32) && defined(__unix__)]
rt_process_owned_test_force_signal_failure         && [if defined(RT_PROCESS_OWNED_TESTING) || ...]
rt_process_owned_test_legacy_cancel_v2
```

Not one appears in any `.spl` file (`ref=0` for all nine, measured).

### Why the census got 90

The census's §4 test was *"all of this name's definitions sit inside a platform
conditional, and one of those conditionals excludes `_WIN32`"*. The dominant C
idiom in this tree is

```c
#if !defined(_WIN32)
int rt_io_udp_recv_from(...) { /* POSIX */ }
#else
int rt_io_udp_recv_from(...) { /* Windows */ }
#endif
```

Both branches define the symbol, so the name **is** available on Windows — but
it satisfies the census test, because *every* site is platform-gated and one
site excludes `_WIN32`. `rt_io_udp_recv_from` is a measured instance
(`runtime_native.c:11527` POSIX branch, `:11573` Windows branch). The census
counted the POSIX half of if/else pairs.

Reproducing the census's own intermediate figures with this extractor gives
177 "all sites platform-gated" (census: 209 — the delta is `static` definitions,
which the census did not exclude) and 421 gated sites (census: 423). So the
extractors agree; only the *availability predicate* differed.

### Cross-check against reality: the actual Windows link

The strongest possible oracle already exists on disk —
`build/bootstrap/logs/x86_64-pc-windows-gnu/stage2-native-build.log`
(2026-08-24, the 68-unresolved run). Classifying its 68 undefined `rt_*` names
against this model:

| class | count |
|---|---|
| C definition exists and is Windows-reachable (build-config problem) | **31** |
| C definition exists but is **POSIX-gated only** | **0** |
| no C definition anywhere | **37** |
| Rust definition exists | 0 |
| pure-Simple body exists | 0 |

**Zero of the real Windows link failures are the claimed class.** The 31/37 split
independently reproduces the split already recorded in the Stage 2 bug record,
from a different direction.

Symmetric delta, computed by re-running the same evaluator under a Linux macro
model: C names reachable on Linux but not Windows = **9** (the list above);
reachable on Windows but not Linux = 2
(`rt_array_bytes_basis_len_packed_span_default`,
`rt_array_bytes_basis_ptr_packed_span_default`). The owned C runtime is almost
perfectly symmetric at the preprocessor level.

---

## 3. The gap that IS real: **file selection**, not `#if`

Preprocessor tracking cannot see a file that a target never compiles. There is
exactly one such divergence in the owned tree, and it is inverted:

`src/compiler_rust/compiler/src/pipeline/native_project/tools.rs:398-402`

```rust
if target.os == simple_common::target::TargetOS::Linux {
    runtime_inputs.extend(["hosted_cocoa.c", "hosted_win32.c"]);
}
```

and `src/compiler_rust/runtime/build.rs:338`

```rust
if target_os != "windows" && !native_all_provider { c_sources.push("hosted_win32.c"); }
```

`hosted_win32.c` is compiled into the core-C archive **only when the target is
not Windows.** It defines 28 non-`static` `rt_*` symbols, of which **11 are
referenced from Simple and have no Rust and no Simple implementation**:

```
rt_win32_window_new  rt_win32_window_resize  rt_win32_window_close
rt_win32_message_pump  rt_win32_dib_create  rt_win32_dib_resize
rt_win32_dib_free  rt_win32_dib_fill_rect  rt_win32_dib_present
rt_win32_dib_present_rect  rt_win32_dib_read_pixel
```

The third source list (`src/compiler/70.backend/backend/runtime_compiler.spl:366`)
is flat and unconditional, so it contributes no target divergence — but it also
never lists `hosted_win32.c` at all.

---

## 4. Ranked: live vs latent

**LIVE (reached by the Windows Stage 2/3 bootstrap closure): 42 symbols — none
of them POSIX-gated.**

| rank | group | n | status |
|---|---|---|---|
| 1 | no C/Rust/Simple definition anywhere, SIMD vector returns | 26 | must be implemented; ABI must be derived from the lowering, not guessed |
| 2 | no definition anywhere, scalar/stdio/misc | 11 | `rt_stdin_read`, `rt_stdin_read_all`, `rt_black_box`, `rt_iocp_deregister`, `rt_event_ports_deregister`, `rt_host_gpu_active_backend_handle`, `rt_simd_vec4u64_get`, … |
| 3 | defined in `runtime.c`, which this lane never compiles | 5 | build-config, lane-scoped: `runtime.c` IS the first entry of list 2 (`runtime_compiler.spl:366`), but the seed core-C list only *probes* for it (`find_core_c_runtime_source_root()`) and `runtime/build.rs` omits it — and Stage 2 runs neither list 2 nor the core-C path |

**LATENT (referenced only from platform/optional lanes): 11 symbols.**
The `rt_win32_*` set above. Referencing files are
`src/os/compositor/hosted_backend_win32.spl` and
`src/os/hosted/hosted_win32_mdi_probe.spl`; the only `src/compiler` mention is a
string literal in an ABI name table (`50.mir/text_extern_abi.spl:136`), not a
call. Nothing in the Stage 2/3 closure reaches them, so they are a real gap that
cannot fail a bootstrap.

**NOT A GAP: 9.** The POSIX-gated names of §2 — unreferenced from Simple.

---

## 5. Already resolved this session

`e463dd5035e` ("make `runtime_native.c` compile under clang-cl") unblocks the
core-C archive on the MSVC lane. Of the 68:

| | count |
|---|---|
| defined in `runtime_native.c` → resolved once the core-C archive is linked | **26** |
| defined in `runtime.c` → still in no build list | 5 |
| defined nowhere → still to implement | 37 |

So **26 of 68 are resolved in principle** (contingent on the core-C archive
actually reaching the Stage 2 link — `native_project/config.rs` still
short-circuits to `libsimple_native_all.a` for a `bootstrap_main` entry, and the
alternative — adding `runtime_native.c` to `native_all` — is the 475-collision
route this record's predecessor already DISPROVED at `8ca87866c61`), and
**42 genuinely remain**. **0 of the 90 claimed POSIX-gated symbols are among
either group, because the set is empty.**

---

## 6. Guard gap

`scripts/check/check-unbacked-extern-ratchet.shs` delegates classification to
`scripts/check/extern-backing-census.shs`, which answers *"is this symbol backed
anywhere"* by reading `nm --defined-only` from **one** artifact set: the deployed
Linux `bin/release/x86_64-unknown-linux-gnu/simple`, plus
`/lib/x86_64-linux-gnu/libc.so.6` and friends. It is therefore not merely
target-unaware — **it cannot run on Windows at all**: hardcoded glibc paths, and
a `BIN` that does not exist here.

But note what §2 proves: a target-aware *preprocessor* check would have found
**nothing**. The defect class Windows actually catches is
(a) per-target **file-list** membership (§3) and (b) **linker tolerance** — ELF
lazy binding lets Linux link past an undefined symbol and pay for it later as a
SIGSEGV, while PE refuses at link time. A guard built on the wrong axis would be
green and useless.

### Smallest change that catches the real thing

**Step 1 (cheap, static, no artifact required, catches §3 today).** Add
`--target <triple>` to `extern-backing-census.shs`, and one new backed tier:

```
c_source_target_excluded   a non-static C definition exists, but for this target
                           either (i) every definition site is unreachable under
                           the target's platform macros, or (ii) the defining
                           file is not in any C source list for that target
```

Both halves are pure static analysis over content already in the tree: the three
source lists (`tools.rs`, `runtime/build.rs`,
`70.backend/backend/runtime_compiler.spl`) and the preprocessor evaluator of §7.
No Windows link artifact, no `nm`, no cross-compiler. The ratchet then takes
`--target` and a **per-target baseline** —
`unbacked_extern_baseline.<triple>.txt` — with the existing verdict contract
unchanged (`PASS — <n> ... 0 new, 0 stale` / `FAIL` / `ERROR — nothing was
checked` on 0 symbols compared, `--selftest` fatal and run first). Cost: one new
baseline file per target the repo claims to support, plus two selftest fixtures
(a symbol excluded by gate, a symbol excluded by file list). Seeded from this
record, the `x86_64-pc-windows-*` baseline starts at the 11 `rt_win32_*` names.

**Step 2 (authoritative, blocked on an artifact).** Keep `nm` as the oracle when
a target link artifact exists: `SIMPLE_BIN` / `--artifact` pointing at the
Windows `libsimple_native_all.a` or a linked stage binary. That is what
`check-no-unresolved-runtime-symbols.shs` already does, and the Stage 2 record
already recommends promoting it from ADVISORY once a Windows link exists. That
guard — not the extern ratchet — is the right home for the linker-tolerance
half. **Do not** wire step 2 before an unstripped Windows artifact is produced;
a guard with nothing to read must ERROR, and an always-ERROR guard trains
`--no-verify`.

**Explicitly rejected:** promoting the census's §4 heuristic ("all definitions
platform-gated, one excludes `_WIN32`") into a guard. It would baseline 64-150
names that are demonstrably present on Windows — failing open on the real
defects and closed on non-defects.

---

## 7. Reproduce

Every command below is read-only. Exit statuses are read directly into a
variable, never through a pipe.

```sh
D=/tmp/pg; mkdir -p $D
/usr/bin/find src/runtime -name '*.c' -not -path 'src/runtime/vendor/*' | sort > $D/cfiles.txt

# Evaluator (committed): doc/08_tracking/bug/data/posix_gate_availability_2026-08-31.awk
# It is a three-valued #if/#ifdef/#ifndef/#elif/#else/#endif evaluator over
# the platform macro set, tracking nesting and #else/#elif polarity.
# Emits: <sym> TAB <winstate: 1 present | 0 absent | -1 unknown> TAB
#        <isstatic> TAB <file:line> TAB <gate stack>
/usr/bin/awk -f $D/gate.awk $(cat $D/cfiles.txt) > $D/sites.tsv

# per-name Windows availability over NON-static sites (1 beats -1 beats 0)
awk -F'\t' '$3==0{s=$2; if(!($1 in b)) b[$1]=s;
  else { if(s==1) b[$1]=1; else if(s==-1 && b[$1]==0) b[$1]=-1 } }
  END{for(k in b) print k"\t"b[k]}' $D/sites.tsv | sort > $D/state.tsv
awk -F'\t' '$2==0{print $1}' $D/state.tsv > $D/win_absent.txt   # -> 9

# referenced universe from Simple (extern decl OR call site)
/usr/bin/grep -rhoE '\brt_[A-Za-z0-9_]+[[:space:]]*\(' src --include=*.spl \
  | /usr/bin/grep -oE 'rt_[A-Za-z0-9_]+' | sort -u > $D/ref_call.txt
/usr/bin/grep -rhoE '\bextern[[:space:]]+(unsafe[[:space:]]+)?fn[[:space:]]+rt_[A-Za-z0-9_]+' \
  src --include=*.spl | /usr/bin/grep -oE 'rt_[A-Za-z0-9_]+' | sort -u > $D/ref_extern.txt
sort -u $D/ref_call.txt $D/ref_extern.txt > $D/ref.txt          # -> 3452

comm -12 $D/win_absent.txt $D/ref.txt | wc -l                   # -> 0   THE ANSWER

# cross-check against the real Windows link
L=build/bootstrap/logs/x86_64-pc-windows-gnu/stage2-native-build.log
/usr/bin/grep -oE "undefined reference to .rt_[A-Za-z0-9_]+" $L \
  | /usr/bin/grep -oE 'rt_[A-Za-z0-9_]+' | sort -u > $D/undef.txt   # -> 68
awk -F'\t' '$2!=0{print $1}' $D/state.tsv | sort > $D/win_ok.txt
comm -12 $D/undef.txt $D/win_ok.txt      | wc -l                # -> 31 build-config
comm -12 $D/undef.txt $D/win_absent.txt  | wc -l                # -> 0  POSIX-gated
cut -f1 $D/state.tsv | sort -u > $D/c_any.txt
comm -23 $D/undef.txt $D/c_any.txt       | wc -l                # -> 37 unimplemented
```

The Linux-model counterpart is the same evaluator with the two macro tables
swapped (`_WIN32`… → 0, `__linux__`/`__unix__`/POSIX → 1, other OS macros → 0);
`comm -23 linux_ok.txt win_ok.txt` yields the 9, `comm -13` yields the 2.

## 8. Known limits (stated, not papered over)

- `.h` files were not scanned for definitions. A non-`static` definition in a
  header would be missed; the 2026-08-30 Windows census scanned headers and
  found that population dominated by `static inline`, which cannot back an
  `extern` anyway.
- The C definition regex requires the signature to open on one line, matching
  `check-runtime-api-regression-push.shs` so the numbers stay comparable.
- Unknown macros (`SPL_HAVE_OPENSSL`, `SIMPLE_RUNTIME_PROCESS_RUST_CORE`,
  `SIMPLE_CORE_C_STANDALONE`, feature flags) evaluate to *unknown*, and unknown
  counts as **possibly present**. The 9 is therefore a floor on "definitely
  absent", which is the conservative direction for a refutation: a looser model
  would report fewer, never more.
- 60 names sit entirely behind unknown macros on the Windows model (72 on the
  Linux model). They are OpenSSL, SIMD-dispatch, baremetal port I/O and
  `SIMPLE_RUNTIME_TESTING` hooks — build-configuration questions, not platform
  questions.
- Nothing here was validated against `nm` on a built artifact; that needs a
  build, which was out of scope. The stage-2 link log is used instead, and for
  this specific question it is a *stronger* oracle than `nm` on a tolerant ELF.
