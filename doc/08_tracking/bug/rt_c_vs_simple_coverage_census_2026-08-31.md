# `rt_*` coverage census: C vs PURE SIMPLE vs Rust

**Date:** 2026-08-31. **Analysis-only** — no source was modified to produce this.
**Repo:** `C:\Users\ormas\dev\simple` (main checkout), working tree at HEAD.

This answers a question the 2026-08-18 census
(`doc/04_architecture/runtime/rt_symbol_ownership.md`) did **not**: not "C vs
Rust", but **which `rt_*` entry points have a C implementation, which have a
PURE SIMPLE implementation, and which have neither or only one**.

---

## 0. The methodological crux: declaration is not implementation

`extern fn rt_X(...)` in a `.spl` file is a **binding to a native symbol**. It
has no body and implements nothing. A census that counted those as Simple
implementations would report ~3,106 "Simple implementations" and be worthless.

The two are separated **syntactically**, because Simple makes them distinct
grammatical forms:

| form | meaning | regex used |
|---|---|---|
| `extern fn rt_X(...) -> T` | declaration / binding — **NOT** an impl | `\bextern[[:space:]]+(unsafe[[:space:]]+)?fn[[:space:]]+rt_[A-Za-z0-9_]+` |
| `pub fn rt_X(...) -> T:` + body | **real implementation** | `^[[:space:]]*(pub[[:space:]]+)?(fn\|me)[[:space:]]+rt_[A-Za-z0-9_]+[[:space:]]*\(` |

The `extern` keyword is the discriminator, and the implementation regex is
anchored at `^` with an optional `pub`, so an `extern fn` line can never match
it. Cross-check: the two sets overlap on **250** names — which is exactly what a
provider/consumer split should look like (module A declares `extern fn rt_X`,
module B in the runtime lane defines `pub fn rt_X`). That overlap is not double
counting, because every count below is taken from the *implementation* set only.

Spot-verified by reading bodies, e.g. `src/runtime/simple_core/core_any_ops.spl:17`:

```
pub fn rt_any_sub(left: i64, right: i64) -> i64:
    if any_is_float(left) or any_is_float(right):
        return any_box_f64(any_as_f64(left) - any_as_f64(right))
    rt_value_int(rt_value_as_int(left) - rt_value_as_int(right))
```

That is a real body, not a binding. The same file *also* carries
`extern fn rt_value_int(value: i64) -> i64` with no body — the distinction is
visible within a single file, which is why the syntactic split is trustworthy.

---

## 1. Reproducible commands

Run from the repo root. `/usr/bin/grep` is used deliberately: the wrapped `grep`
on this host is ugrep honouring `.gitignore` and under-reports.

```sh
D=/tmp/rtcensus; mkdir -p $D

# C definitions (non-vendored)
/usr/bin/find src/runtime -name '*.c' -not -path 'src/runtime/vendor/*' > $D/cfiles.txt
/usr/bin/grep -hnoE '^[A-Za-z_][A-Za-z0-9_ \*]*[ \*](rt_[A-Za-z0-9_]+)[[:space:]]*\(' $(cat $D/cfiles.txt) \
  | /usr/bin/grep -oE 'rt_[A-Za-z0-9_]+[[:space:]]*\($' | sed 's/[[:space:]]*($//' | sort -u > $D/c_defs.txt

# Rust definitions
/usr/bin/grep -rhoE 'pub (extern "C" )?fn (rt_[A-Za-z0-9_]+)' src/compiler_rust/runtime/src --include=*.rs \
  | /usr/bin/grep -oE 'rt_[A-Za-z0-9_]+' | sort -u > $D/rust_defs.txt

# Simple: extern DECLARATIONS (bindings — NOT implementations)
/usr/bin/grep -rhoE '\bextern[[:space:]]+(unsafe[[:space:]]+)?fn[[:space:]]+rt_[A-Za-z0-9_]+' src --include=*.spl \
  | /usr/bin/grep -oE 'rt_[A-Za-z0-9_]+' | sort -u > $D/spl_externs.txt

# Simple: real bodies
/usr/bin/grep -rnE '^[[:space:]]*(pub[[:space:]]+)?(fn|me)[[:space:]]+rt_[A-Za-z0-9_]+[[:space:]]*\(' \
  src --include=*.spl > $D/spl_impl_sites.txt
/usr/bin/grep -oE '(fn|me)[[:space:]]+rt_[A-Za-z0-9_]+' $D/spl_impl_sites.txt \
  | /usr/bin/grep -oE 'rt_[A-Za-z0-9_]+' | sort -u > $D/spl_impls.txt

# Referenced universe (extern decl OR call site) in Simple
/usr/bin/grep -rhoE '\brt_[A-Za-z0-9_]+[[:space:]]*\(' src --include=*.spl \
  | /usr/bin/grep -oE 'rt_[A-Za-z0-9_]+' | sort -u > $D/spl_calls.txt
sort -u $D/spl_externs.txt $D/spl_calls.txt > $D/ref_tight.txt

# Buckets
comm -12 $D/c_defs.txt $D/spl_impls.txt > $D/both.txt
comm -23 $D/c_defs.txt $D/spl_impls.txt > $D/c_only.txt
comm -13 $D/c_defs.txt $D/spl_impls.txt > $D/simple_only.txt
```

Exit statuses were read directly into variables, never through a pipe (a
pipeline's `$?` is the last stage's status and has produced false greens in this
repo before).

The core-required ABI contract (§6) is extracted with:

```sh
# Bounded at the array's own `];` — NOT at a fixed line number, so a neighbouring
# string-bearing const can never be swept in.
awk 'NR>=118{print; if(/\];/) exit}' src/compiler_rust/common/src/runtime_symbols.rs \
  | /usr/bin/grep -oE '"[A-Za-z0-9_]+"' | tr -d '"' | sort -u > $D/core_req.txt
comm -23 $D/core_req.txt $D/simplecore_impls.txt   # the gap
```

This was cross-checked against a naive fixed-range `sed -n '118,210p'`
extraction: both yield **88** symbols with a byte-identical set (the array spans
90 lines and closes before any neighbour), so the count is not an artifact of the
range. Stating this because the delta against the 2026-08-22 bug record's "8
missing" would otherwise be equally explainable by over-capture.

---

## 2. Raw set sizes

| set | count |
|---|---|
| non-vendored C files scanned | 120 |
| **C definitions** (`src/runtime/**/*.c`) | **1,639** |
| **Rust definitions** (`src/compiler_rust/runtime/src/**/*.rs`) | **1,804** |
| **Pure-Simple implementations** (real `.spl` bodies) | **523** |
| Simple `extern` DECLARATIONS (bindings, *not* impls) | 3,106 |
| Simple call sites `rt_X(` | 3,443 |
| Referenced universe (extern ∪ call site) | 3,452 |
| Union of all definitions (C ∪ Rust ∪ Simple) | 3,076 |
| **Total universe** (referenced ∪ defined) | **4,681** |

Note the shape: **3,106 extern declarations against 523 real Simple bodies.** Had
declarations been counted as implementations, the answer would have been wrong by
a factor of six.

---

## 3. The four-way buckets (C vs pure-Simple)

| bucket | count | notes |
|---|---|---|
| **Both C and pure-Simple** | **282** | the transitional overlap of the core lane |
| **C only** | **1,357** | library/platform bindings — by design (§5) |
| **Simple only** | **241** | kernel/OS lane, TLS, async, drivers |
| **Neither** (no C, no Rust, no Simple) | **1,605** | all of them referenced — see §3b |

### 3a. Full C / Simple / Rust cross-tabulation

`C`/`S`/`R` = has a definition in that language; `-` = does not.

| C | S | R | total | of which referenced in `.spl` |
|---|---|---|---|---|
| C | S | R | 214 | 214 |
| C | S | - | 68 | 68 |
| C | - | R | 292 | 199 |
| C | - | - | 1,065 | 597 |
| - | S | R | 102 | 102 |
| - | S | - | 139 | 139 |
| - | - | R | 1,196 | 528 |
| - | - | - | 2,896 | 1,605 |

**Do not sum the `total` column against §2's universe of 4,681.** The column sums
to 5,972 because the `---` row's 2,896 is computed over the *wide* reference set
(which also admits bare textual `rt_` mentions inside the Rust seed). Of those
2,896, only **1,605** are `.spl`-referenced and therefore in §2's universe; the
other 1,291 are seed-internal textual mentions — mangled names, string literals,
comments — that are neither defined anywhere nor referenced from Simple. Every
other row is unaffected: the C rows sum to 1,639, the S rows to 523, and the R
rows to 1,804, each matching §2 exactly.

### 3b. "Neither" split — real gaps vs dead names

Every one of the 1,605 "neither" names **is** referenced from `.spl`. This is
true by construction: a name with no definition anywhere can enter the universe
only via a reference. So there are no dead names inside the "neither" bucket.

Dead names live in the *defined* set instead:

| | count |
|---|---|
| defined somewhere but never referenced from `.spl` | 1,229 |
| defined somewhere and referenced nowhere at all (incl. the Rust seed) | 399 |

**The 1,605 are not a new backlog.** Their family profile is decisive:

| family | count | family | count |
|---|---|---|---|
| `rt_torch_*` | 149 | `rt_lyon_*` | 49 |
| `rt_cranelift_*` | 76 | `rt_rapier2d_*` | 48 |
| `rt_arm64_*` | 53 | `rt_winit_*` | 44 |
| `rt_tls13_*` | 51 | `rt_cuda_*` | 38 |
| `rt_arm_*` | 39 | `rt_wgpu_*` | 29 |

These are optional, feature-gated FFI bindings to external libraries (libtorch,
Cranelift, CUDA, wgpu, Rapier, Lyon, winit) plus per-architecture backend
surfaces. They are declared so the Simple side can *name* them, and are backed
only when the corresponding feature or library is linked. This population is
**already tracked and ratcheted** by
`scripts/check/check-unbacked-extern-ratchet.shs` against
`scripts/check/unbacked_extern_baseline.txt` (baseline 1,466 — same order of
magnitude, same population). Stage 2 of
`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md` verified that
these declarations are **not** dead and must not be deleted.

---

## 4. Platform-conditional C definitions

A C definition inside `#if !defined(_WIN32)` is effectively absent on Windows.
Detected with an `awk` preprocessor-nesting tracker (tracks `#if`/`#ifdef`/
`#ifndef` depth, re-gates on `#else`/`#elif`, pops on `#endif`) over the 120
non-vendored `.c` files, flagging any `rt_*` definition with a platform macro
(`_WIN32`, `_MSC_VER`, `__linux__`, `__APPLE__`, `__unix__`, `__FreeBSD__`,
`POSIX`, `__EMSCRIPTEN__`, `__wasm`, `SPL_BAREMETAL`, `__ANDROID__`) anywhere in
an enclosing conditional.

| | count |
|---|---|
| C definition *sites* scanned | 2,333 |
| sites inside a platform conditional | 423 |
| **names whose C definitions are ALL platform-gated** | **209** |
| of those, gated to exclude `_WIN32` (POSIX-only) | 150 |
| POSIX-gated-only, referenced, and with **no** Simple body | **90** |
| gated-only names that do have some Simple body | 24 |
| gated-only names covered by `simple_core` specifically | **0** |

**REFUTED 2026-08-31 — do not cite the 90.** Independently re-derived with a
three-valued preprocessor evaluator (not a "platform macro appears in an
enclosing conditional" text test): only **9** names have no Windows-reachable C
definition, and **0** of those are referenced from Simple. The 90 counted the
POSIX half of `#if !defined(_WIN32) ... #else ... #endif` pairs whose OTHER
branch also defines the symbol. Cross-checked against the real Windows stage-2
link log: 0 of its 68 undefined names are POSIX-gated. See
`doc/08_tracking/bug/posix_gated_runtime_symbols_invisible_on_windows_2026-08-31.md`.

**Flag:** those **90** names are referenced from Simple, have their only C
definition behind a POSIX gate, and have no pure-Simple fallback. On Windows they
resolve to nothing. This is the most concrete portability finding in this census,
and it is *not* covered by the existing extern ratchet — that guard asks whether
a symbol is backed *somewhere*, not whether it is backed *on this platform*.

---

## 5. Is dual C + pure-Simple implementation the intended design?

**No — not as a universal rule, and this census must not be read as a defect
list.** The repo's own architecture and requirements documents state a different
intent, in three parts. Evidence, all primary:

**(a) The direction is REPLACEMENT within a bounded core, not permanent duality.**
`doc/02_requirements/runtime/simple_core_runtime_completeness_2026-06-02.md`
(#FR-SIMPLECORE-001):

> Make the pure-Simple `simple_core` runtime (`src/runtime/simple_core/*.spl`)
> complete enough to be the runtime for the core-c native lane, **replacing** the
> hand-written C runtime (`src/runtime/runtime_native.c` …). This realizes the
> "interpreter/compiler/lib/runtime in pure Simple, **C only where required**"
> direction.

So where both exist today, that is a **transitional overlap** on the way to the
Simple side winning — not a target state to be extended to every symbol. The 282
"both" names are the migration frontier, and the same document scopes the job to
a measured closure (it counted 173 symbols pulled by one native binary, not the
whole `rt_*` surface).

**(b) C is the sole implementation *by design* for library and platform bindings.**
"C only where required" is borne out by what is actually in the C-only bucket.
Family profile of the 1,357:

| family | n | family | n | family | n |
|---|---|---|---|---|---|
| `rt_core_*` | 107 | `rt_audio_*` | 41 | `rt_opencl_*` | 26 |
| `rt_pool_*` | 75 | `rt_process_*` | 36 | `rt_sdl3_*` | 24 |
| `rt_sdl2_*` | 66 | `rt_rocm_*` | 31 | `rt_db_*` | 21 |
| `rt_glfw_*` | 49 | `rt_http_*` | 28 | `rt_opengl_*` | 18 |
| `rt_string_*` | 45 | `rt_sqlite_*` | 27 | `rt_font_*` | 18 |
| `rt_host_*` | 30 | `rt_file_*` | 25 | `rt_win32_*` | 14 |

SDL2/SDL3, GLFW, OpenGL, OpenCL, ROCm, SQLite, audio, fonts, Win32 — these are
bindings to C libraries. Reimplementing them "in pure Simple" is not a coherent
goal; the C shim *is* the implementation.

**(c) The link contract targets ONE archive per lane, never a merged C+Simple one.**
`doc/04_architecture/runtime/default_native_runtime_shift_to_c_core_abi.md`:

> - `simple-core`: the preferred pure-Simple lane when an ABI-complete pure-Simple
>   core runtime archive is present. It links `libsimple_runtime.a` only.
> - `core-c-bootstrap`: the C bootstrap lane when `simple-core` is not present or
>   not ABI-complete yet. It also links `libsimple_runtime.a` only.
> 4. `--runtime-bundle rust-hosted`, `hosted`, … are removed and **fail closed**.

Two *alternative* lanes, selected by `--runtime-bundle auto`, each linking a
single archive. Duality exists so one lane can substitute for the other — a
fallback relationship, not a requirement that every symbol be written twice. The
same document retires the Rust lane, which is why the 1,804 Rust definitions are
legacy rather than a third target; `doc/04_architecture/runtime/rt_symbol_ownership.md`
§3 separately measures that Rust currently wins the link by default through
selective archive extraction.

**Conclusion for task 4: "not all `rt_*` is implemented in both" is BY DESIGN.**
Generating implementation tasks for the 1,357 C-only symbols would be fabricated
work. The genuine, bounded obligation is only §6.

---

## 6. The genuine gap, ranked

The design supplies an exact, machine-checked definition of "done" for the Simple
lane: `CORE_REQUIRED_RUNTIME_SYMBOLS` at
`src/compiler_rust/common/src/runtime_symbols.rs:118`, asserted by
`pipeline::native_project::tests::test_simple_core_source_tree_emits_partial_runtime_archive`.
That contract is **88 symbols**. Measured today:

| | count |
|---|---|
| core-required symbols | 88 |
| already implemented in `src/runtime/simple_core/**` | 75 |
| **still missing — the real gap** | **13** |

(71 of the 88 match the `rt_` regex; the remaining four — `print_raw`,
`stdin_read_char`, `__simple_runtime_init`, `__simple_runtime_shutdown` — were
individually verified present in `core_string.spl:1011,1131` and
`core_values.spl:15,18`.)

### Ranked gap list

All 13 **do** have a C definition, so the C lane is unaffected — this blocks only
the `simple-core` lane's ABI completeness.

**Reference-count is the wrong priority oracle here, and measuring it proved
why.** Only **8 of the 13** are referenced from `.spl` — and they are not the
eight you would guess. The four most semantically central symbols
(`rt_struct_alloc`, `rt_struct_receiver_valid`, `rt_native_cmp`,
`rt_is_jit_runtime`) are **unreferenced from Simple source**, because they are
emitted by **codegen**, not called from `.spl`. Their absence from `ref_tight` is
evidence of how they are invoked, not evidence that nothing needs them. For this
bucket, membership in `CORE_REQUIRED_RUNTIME_SYMBOLS` *is* the requirement, and
ranking below is by blast radius, with the measured `.spl` reference recorded as
a fact rather than used as the ranking key.

| rank | symbol | C impl? | `.spl` ref? | why it ranks here |
|---|---|---|---|---|
| 1 | `rt_struct_alloc` | yes | no (codegen) | struct allocation — nothing non-trivial runs without it |
| 2 | `rt_struct_receiver_valid` | yes | no (codegen) | paired with the above; method-receiver validity |
| 3 | `rt_native_cmp` | yes | no (codegen) | generic comparison; broad codegen fan-in |
| 4 | `rt_is_jit_runtime` | yes | no (codegen) | one-line predicate; trivially closable |
| 5 | `rt_transient_array_scope_begin` | yes | yes | transient-heap scope quartet — must land together |
| 6 | `rt_transient_array_scope_pause` | yes | yes | ” |
| 7 | `rt_transient_array_scope_end` | yes | yes | ” |
| 8 | `rt_transient_heap_promote` | yes | yes | ” |
| 9 | `rt_transient_last_promoted_bytes` | yes | yes | promotion **statistics** only; no semantics depend on them |
| 10 | `rt_transient_last_promoted_nodes` | yes | yes | ” |
| 11 | `rt_transient_scope_promoted_bytes` | yes | yes | ” |
| 12 | `rt_transient_scope_promoted_nodes` | yes | yes | ” |
| 13 | `rt_transient_promotion_stats_reset` | yes | no | statistics reset; lowest blast radius of all 13 |

Ranks 1-8 are exactly the eight already filed as
`doc/08_tracking/bug/simple_core_lane_missing_heap_registry_abi_2026-08-22.md`
("OPEN — product decision, test left red on purpose"), whose diagnosis is that
they need the **C heap-registry design ported**, not merely retyped. Ranks 9-13
are five statistics siblings that have since been added to the contract and are
not named in that record — the only genuinely *new* finding in this section. The
extraction bound was validated (see §1) specifically so this delta cannot be
dismissed as over-capture.

**Recommendation: file nothing new beyond adding ranks 9-13 to the existing
record.** The gap is 13 symbols against a written contract with a red test
already pointing at it — a finishing task, not a program of work.

### Secondary — the 90 POSIX-gated symbols (REFUTED: the set is EMPTY)

Re-derived 2026-08-31: the count is **0**, not 90. The real target-specific
absence is FILE selection (`hosted_win32.c` is compiled only when the target is
NOT Windows), not `#if` gating. Record:
`doc/08_tracking/bug/posix_gated_runtime_symbols_invisible_on_windows_2026-08-31.md`.


§4's 90 names (referenced, C definition POSIX-gated only, no Simple fallback) are
a real portability hole on Windows that no existing guard detects, because
`check-unbacked-extern-ratchet.shs` asks "backed anywhere?" and not "backed on
this target?". Worth its own record if Windows is a supported host for these
paths.

---

## 7. Known extraction limits (stated, not papered over)

- The C regex requires the definition to open on one line and is blind to
  macro-generated definitions — the same limit as
  `scripts/check/check-runtime-api-regression-push.shs`, so the numbers stay
  comparable to that guard.
- The Rust regex counts `pub fn rt_*` even where the item is not `extern "C"`.
- `.h` files were excluded from the C set. The 2026-08-18 census included them,
  which is why its C figure is 1,450 against this one's 1,639 — a different
  scope, not a contradiction.
- No list was cross-checked against `nm` output of a built archive. That requires
  a build, which was out of scope for this read-only pass.
- Simple bodies were counted by name, so a `fn rt_X` that is a soft stub — e.g.
  `src/app/io/jit_ffi.spl:53`, `fn rt_get_jit_backend() -> text: "interpreter"` —
  counts as an implementation here. 28 of the 523 sit under `src/app/io` and are
  of that shim character; the `simple_core` and `src/os/kernel` bodies were
  spot-read and are real.

### Simple implementations by providing lane

| lane | names | also in C | also in Rust | Simple-only |
|---|---|---|---|---|
| `src/runtime/simple_core` | 316 | 229 | 238 | 18 |
| `src/os/kernel` | 127 | 51 | 73 | 47 |
| `src/lib` | 59 | 2 | 4 | 54 |
| `src/app/io` (shims) | 28 | 0 | 1 | 27 |
| `src/os/userlib` | 5 | 5 | 2 | 0 |
| `src/compiler` | 3 | 0 | 0 | 3 |
| `src/os/drivers` | 1 | 0 | 0 | 1 |

`simple_core` overlapping C at 229 of 316 is the migration frontier of §5(a) made
visible: it is deliberately re-implementing what C already provides, for the
bounded core ABI, and nothing wider. `src/os/kernel` is a separate lane
(SimpleOS baremetal), which is why its 47 Simple-only names are expected rather
than gaps in the hosted runtime.
