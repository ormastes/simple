# `rt_*` TEST coverage audit — which runtime entry points are actually tested

- **Date:** 2026-08-31
- **Repo:** `C:\Users\ormas\dev\simple` (main checkout), working tree at HEAD.
- **Host:** `MINGW64_NT-10.0-26200`, Windows 11.
- **Method:** read-only measurement, then five new tests written and RUN.
  No bootstrap, no cargo, no worktree.
- **Complements (does not redo):**
  - `doc/08_tracking/bug/rt_c_vs_simple_coverage_census_2026-08-31.md`
    (C vs pure-Simple *implementation* coverage)
  - `doc/08_tracking/bug/rt_symbol_census_windows_2026-08-30.md`
  - `doc/08_tracking/bug/bootstrap_stage2_windows_link_unresolved_rt_and_dup_kernel32_2026-08-24.md`
    — the Stage 2 unresolved set. (The file named
    `stage2_windows_unresolved_inventory_2026-08-31.md` does not exist in this
    tree; this is the closest existing record, and it does carry that content:
    68 distinct unresolved `rt_*` names at the Stage 2 link, listed by name.)
    **`rt_black_box` is one of those 68** — so the symbol §5 shows to be
    untested-in-effect is also one the Windows bootstrap currently cannot
    resolve. That raises its rank, and it is why it is a top-5 target here.

Those censuses answer *"is it implemented?"*. This one answers **"is it
tested?"** — a strictly different question, and the one nothing had asked.

---

## 0. Two methodological points that change the answer

### 0a. There are FOUR implementation lanes, not two

The prior census scanned C (`src/runtime/**/*.c`), Rust
(`src/compiler_rust/runtime/src/**`) and pure Simple. It did not scan
`src/compiler_rust/compiler/src/interpreter_extern/**`, which registers
**1,355** `rt_*` builtins via `insert_simple!`. **400 of those exist in no
other lane** — they are interpreter-only. Every symbol this task named as a
known divergence (`rt_black_box`, `rt_simd_hmax_f32x4`, `rt_simd_hmin_f32x4`,
`rt_simd_vec4u64_get`) lives there and *only* there. An untested-anywhere set
computed against the prior 3,076-symbol universe would have been wrong; the
universe used here is **4,010**.

This also means: **a Simple spec run by `bin/simple test` exercises the
interpreter_extern lane, not the C lane.** The tables below keep the lanes
separate for exactly that reason. There is no single "tested" bit per symbol.

### 0b. Simple coverage is reported as a floor AND a ceiling

- **Floor** — a `rt_*` name appearing in `test/**/*.spl`: certain, direct.
- **Ceiling** — the floor plus every `rt_*` called anywhere in `src/lib/**`,
  i.e. every symbol a spec *could* reach through some stdlib wrapper. This
  over-approximates badly (it credits a symbol as covered because some
  unrelated stdlib module calls it), and it is used deliberately: the
  untested set is computed against the **ceiling**, so **everything listed as
  untested is certifiably untested**, with no argument available that a spec
  reached it indirectly.

The ceiling is the wrong tool for a second, subtler failure that §5 records:
a symbol can be *reached* by a spec and still not be *tested*, because the
wrapper erases the failure mode.

---

## 1. Reproducible commands

Run from the repo root. Exit statuses are read directly into a variable on
the line after the command, never through a pipe.

```sh
D=/tmp/rtcov; rm -rf $D; mkdir -p $D

# ---- implemented universe (4 lanes) ----
find src/runtime -name '*.c' -not -path 'src/runtime/vendor/*' > $D/cfiles.txt
grep -hnoE '^[A-Za-z_][A-Za-z0-9_ \*]*[ \*](rt_[A-Za-z0-9_]+)[[:space:]]*\(' $(cat $D/cfiles.txt) \
  | grep -oE 'rt_[A-Za-z0-9_]+[[:space:]]*\($' | sed 's/[[:space:]]*($//' | sort -u > $D/c_defs.txt
grep -rhoE 'pub (extern "C" )?fn (rt_[A-Za-z0-9_]+)' src/compiler_rust/runtime/src --include=*.rs \
  | grep -oE 'rt_[A-Za-z0-9_]+' | sort -u > $D/rust_defs.txt
grep -rnE '^[[:space:]]*(pub[[:space:]]+)?(fn|me)[[:space:]]+rt_[A-Za-z0-9_]+[[:space:]]*\(' \
  src --include=*.spl | grep -oE '(fn|me)[[:space:]]+rt_[A-Za-z0-9_]+' \
  | grep -oE 'rt_[A-Za-z0-9_]+' | sort -u > $D/spl_impls.txt
grep -rhoE 'insert_simple!\("(rt_[A-Za-z0-9_]+)"' \
  src/compiler_rust/compiler/src/interpreter_extern --include=*.rs \
  | grep -oE 'rt_[A-Za-z0-9_]+' | sort -u > $D/interp_registered.txt
sort -u $D/c_defs.txt $D/rust_defs.txt $D/spl_impls.txt $D/interp_registered.txt > $D/impl_universe.txt

# ---- tested-in-C: per FILE, mentions minus that file's OWN definitions ----
# Per-file matters: several selfchecks define local STUBS (rt_string_new in
# runtime_process_owned_adapter_selfcheck.c) while others extern-declare and
# genuinely link the real symbol. A tree-wide subtraction erases real coverage.
# `extern` lines and lines ending in `;` are declarations, never definitions.
find test src/runtime/test -name '*.c' | sort -u > $D/ctestfiles.txt
rm -f $D/tested_c.txt
while read f; do
  grep -ohE '\brt_[A-Za-z0-9_]+[[:space:]]*\(' "$f" \
    | grep -oE 'rt_[A-Za-z0-9_]+' | sort -u > $D/_m.txt
  grep -hnE '^[A-Za-z_][A-Za-z0-9_ \*]*[ \*]rt_[A-Za-z0-9_]+[[:space:]]*\(' "$f" \
    | grep -v ':[[:space:]]*extern' | grep -vE ';[[:space:]]*$' \
    | grep -oE 'rt_[A-Za-z0-9_]+[[:space:]]*\(' | sed 's/[[:space:]]*(//' | sort -u > $D/_d.txt
  comm -23 $D/_m.txt $D/_d.txt >> $D/tested_c.txt
done < $D/ctestfiles.txt
sort -u -o $D/tested_c.txt $D/tested_c.txt

# ---- tested-in-Rust: rt_* CALLED inside #[cfg(test)] bodies (brace-depth scan) ----
find src/compiler_rust/runtime/src -name '*.rs' | while read f; do
  awk '/#\[cfg\(test\)\]/{pend=1} pend&&/\{/&&!it{it=1;depth=0;pend=0}
       it{print; n=gsub(/\{/,"{"); m=gsub(/\}/,"}"); depth+=n-m; if(depth<=0)it=0}' "$f"
done > $D/rust_test_bodies.txt
grep -oE '\brt_[A-Za-z0-9_]+[[:space:]]*\(' $D/rust_test_bodies.txt \
  | grep -oE 'rt_[A-Za-z0-9_]+' | sort -u > $D/tested_rust_calls.txt

# ---- tested-in-interpreter_extern: same scan over that crate ----
find src/compiler_rust/compiler/src/interpreter_extern -name '*.rs' | while read f; do
  awk '/#\[cfg\(test\)\]/{pend=1} pend&&/\{/&&!it{it=1;depth=0;pend=0}
       it{print; n=gsub(/\{/,"{"); m=gsub(/\}/,"}"); depth+=n-m; if(depth<=0)it=0}' "$f"
done > $D/interp_test_bodies.txt
grep -oE '\brt_[A-Za-z0-9_]+' $D/interp_test_bodies.txt | sort -u > $D/tested_interp.txt

# ---- tested-from-Simple: floor (direct) and ceiling (+ stdlib reach) ----
grep -rhoE '\brt_[A-Za-z0-9_]+[[:space:]]*\(' test --include=*.spl \
  | grep -oE 'rt_[A-Za-z0-9_]+' | sort -u > $D/tested_spl_direct.txt
grep -rhoE '\brt_[A-Za-z0-9_]+[[:space:]]*\(' src/lib --include=*.spl \
  | grep -oE 'rt_[A-Za-z0-9_]+' | sort -u > $D/lib_reach.txt

sort -u $D/tested_c.txt $D/tested_rust_calls.txt $D/tested_interp.txt \
        $D/tested_spl_direct.txt > $D/tested_direct.txt
sort -u $D/tested_direct.txt $D/lib_reach.txt > $D/tested_upper.txt
comm -23 $D/impl_universe.txt $D/tested_upper.txt > $D/untested.txt

# ---- risk weighting: the bootstrap closure ----
awk 'NR>=118{print; if(/\];/) exit}' src/compiler_rust/common/src/runtime_symbols.rs \
  | grep -oE '"[A-Za-z0-9_]+"' | tr -d '"' | sort -u > $D/core_req.txt   # 88 core-required
grep -rhoE '\brt_[A-Za-z0-9_]+[[:space:]]*\(' src/compiler --include=*.spl \
  | grep -oE 'rt_[A-Za-z0-9_]+' | sort -u > $D/compiler_calls.txt
sort -u $D/core_req.txt $D/compiler_calls.txt > $D/bootstrap_closure.txt
comm -12 $D/untested.txt $D/bootstrap_closure.txt > $D/untested_boot.txt
comm -12 $D/untested.txt $D/core_req.txt          > $D/untested_core.txt
```

Cross-check that the extraction is sound: `c_defs` = 1,639, `rust_defs` =
1,804, `spl_impls` = 523 — byte-identical to the 2026-08-31 implementation
census, which used an independently written pipeline.

---

## 2. Test surface, measured

| lane | test artifacts | `rt_*` reached |
|---|---|---|
| C selfchecks (`src/runtime/test/*.c` + `test/**/*.c`) | 144 files | **385** |
| Rust `#[cfg(test)]` (`src/compiler_rust/runtime/src/**`) | 1,557 `#[test]` fns in 198 files, 19,117 lines of test bodies | **645** |
| interpreter_extern `#[cfg(test)]` | 288 `#[test]` fns, 4,836 lines | **353** |
| Simple specs (`test/**/*.spl`), direct | 21,289 `*_spec.spl` files | **894** |

`test/**/*.c` matters and is easy to miss: `test/01_unit/runtime/runtime_native_focus_test.c`
and `test/02_integration/os/cosmos/cosmos_runtime_contract_test.c` are the only
tests for `rt_slice` and `rt_memcmp` respectively, and a scan restricted to
`src/runtime/test/` reports both as untested.

---

## 3. The four coverage buckets

Over the **4,010**-symbol implemented universe:

| bucket | count | % |
|---|---|---|
| **tested-in-C** | **379** | 9.5% |
| **tested-in-Rust** (`simple-runtime` crate `#[cfg(test)]`) | **603** | 15.0% |
| **tested-via-interpreter** (`interpreter_extern` `#[cfg(test)]`) | **278** | 6.9% |
| **tested-from-Simple** (direct, floor) | **735** | 18.3% |
| union of the four (direct evidence) | 1,450 | 36.2% |
| union + stdlib-reach ceiling | 2,257 | 56.3% |
| **UNTESTED ANYWHERE** (certifiable, computed vs. the ceiling) | **1,753** | **43.7%** |
| untested by direct evidence only (upper bound on the gap) | 2,560 | 63.8% |

The two untested figures bracket the truth: **at least 1,753** `rt_*` entry
points have no test of any kind, and at most 2,560 do. The lower bound is the
one to act on — every symbol in it is provably untested.

Lane overlap is small: only **95** symbols are tested in both C and Rust, and
**172** are tested in C and nowhere else. The lanes are not redundant backups
for each other.

---

## 4. Ranked untested-and-risky

Ranked by blast radius, not by count.

### Tier 1 — core-required bootstrap ABI, untested anywhere (9)

These are in the `runtime_symbols.rs` core-required array (the 88 symbols
every bootstrap stage must resolve). A defect here blocks everything and is
not caught by any test in the tree:

```
rt_str_hash   rt_len   rt_string_trim   rt_string_to_int
rt_string_to_int_lenient   rt_array_set_text   rt_array_set_len_known_text
rt_time_now_unix   rt_typed_words_u32_push
```

### Tier 2 — reached by the self-hosted compiler, untested anywhere (46)

`untested ∩ (core_req ∪ rt_* called from src/compiler/**)` — the full 46,
Tier 1's nine included:

```
rt_array_get_operand   rt_array_len_operand   rt_array_push_i64_raw
rt_array_push_operand  rt_array_repeat        rt_array_write_span
rt_array_set_len_known_text                   rt_array_set_text
rt_core_register_scoped_immortal              rt_cpuid
rt_cpu_is_aarch64      rt_cpu_is_riscv64      rt_cpu_is_x86_64
rt_exec_manager_backend_name  rt_exec_manager_cleanup  rt_exec_manager_compile
rt_exec_manager_create        rt_exec_manager_execute  rt_exec_manager_has_function
rt_get_jit_backend     rt_set_jit_backend     rt_jit_call_i64_i64
rt_getenv              rt_setenv              rt_range   rt_range_inclusive
rt_len                 rt_str_hash            rt_string_join
rt_string_to_int       rt_string_to_int_lenient  rt_string_trim
rt_strfind             rt_strreplace          rt_substr  rt_text_find
rt_time_monotonic_ns   rt_time_now_unix       rt_timestamp_iso8601
rt_sin                 rt_cos                 rt_pow
rt_process_run_tuple   rt_process_run_timeout_tuple  rt_process_run_inherit_value
rt_typed_words_u32_push
```

Note what is **not** in that list. A first pass scanning only
`src/runtime/test/` reported 60 here, including `rt_slice`, `rt_memcmp`,
`rt_array_last`, `rt_bytes_u32_le_at`, `rt_bytes_u64_le_at`,
`rt_typed_words_u32_at`, `rt_typed_words_u32_set` and `rt_value_as_u64`.
Fourteen symbols dropped out once `test/**/*.c` was included — those eight
among them. They are covered by C tests living under `test/**`, not
`src/runtime/test/` (`rt_slice` by `test/01_unit/runtime/runtime_native_focus_test.c:162`,
`rt_memcmp` by `test/02_integration/os/cosmos/cosmos_runtime_contract_test.c:145`,
one test each). That is a 23% false-gap rate from one scoping mistake, which
is why §1's `ctestfiles.txt` unions both trees.

The `rt_exec_manager_*` / `rt_*_jit_backend` cluster (9 symbols) is the JIT
execution manager surface — untested, and on the path every `bin/simple run`
takes.

### Tier 3 — security- and correctness-critical, untested anywhere

- **Registry / heap:** `rt_core_register_{array,dict,enum,closure,float,
  string,persistent_string,mutex,immortal_ptr,scoped_immortal}`,
  `rt_core_unregister_{string,immortal_ptr}`,
  `rt_core_transient_raw_register_state` — the heap registry is what makes
  every tag-decode (`rt_core_as_string`, `rt_core_as_array`) safe. 13 symbols,
  none tested.
- **Comparison / ordering:** `rt_core_value_eq_inner`, `rt_native_eq_inner`,
  `rt_native_eq_fn`, `rt_core_array_eq`, `rt_core_enum_eq`,
  `rt_core_generic_int_eq`, `rt_core_dict_key_eq`, `rt_core_dict_hash`,
  `rt_core_immortal_hash_ptr` — the primitives `==` lowers to.
- **Crypto:** `rt_aes_gcm_{encrypt,decrypt}(_with_len)`,
  `rt_aes256_encrypt_block_into`, `rt_pbkdf2_hmac_sha1`.
- **Entropy / RNG:** `rt_entropy_hardware_ready_fn`, `rt_random_next_fn`,
  `rt_random_i64_fn`, `rt_random_hex_fn`, `rt_random_getstate_fn`.
- **Whole containers:** every `rt_hashset_*` (17 symbols — `new`, `insert`,
  `contains`, `remove`, `union`, `intersection`, `difference`,
  `symmetric_difference`, `is_subset`, `is_superset`, `len`, `to_array`,
  `clear`, `drop`, …) and `rt_hashmap_{keys,values,entries,clear,drop}`.

### Tier 4 — reached but NOT DISCRIMINATINGLY tested (see §5)

`rt_black_box`, `rt_simd_hmax_f32x4`, `rt_simd_hmin_f32x4`,
`rt_simd_vec4u64_get`. These are excluded from the certifiable-untested set
by the ceiling (a stdlib wrapper calls each), yet none had a test that could
detect the entry point being broken.

---

## 5. The discrimination failure the ceiling cannot see

`test/01_unit/lib/crypto/black_box_spec.spl` exists, passes 5/5, and **cannot
detect `rt_black_box` being broken**. Every one of its assertions goes through
`std.crypto.constant_time.black_box`, which is:

```
pub fn black_box(value: i64) -> i64:
    rt_black_box(value) ?? value          # constant_time.spl:22
```

If `rt_black_box` returned nil, `?? value` substitutes the original argument
and all five assertions still pass. The wrapper's fallback is what is tested,
not the runtime entry point — and `rt_black_box` is the optimization barrier
that keeps `ct_eq`, ML-KEM rejection sampling and Curve25519 conditional swap
from being rewritten into data-dependent early-exit branches.

This is not hypothesised. It is **executed** as `B6 NEGATIVE CONTROL` in the
new spec (§6.2): a deliberately nil-returning stub is shown passing the
wrapper-shaped assertions and failing the direct-call assertion, in the same
run.

**Generalisation:** any `?? default`, `.unwrap_or`, or `or_else` between a
spec and an extern converts a hard failure into a silent substitution. The
ceiling model in §0b credits such a symbol as reached; it is not tested.

---

## 6. Tests written and RUN

Five top-risk targets, chosen from Tier 1 (bootstrap ABI) and Tier 4 (known
divergences): `rt_str_hash`, `rt_len`, `rt_string_trim`,
`rt_string_to_int`/`_lenient`, `rt_black_box` — plus the SIMD divergence pins.

### 6.1 `src/runtime/test/rt_core_abi_untested_selfcheck.c` — **FAIL, 3 real defects**

Follows the established pattern of the sibling selfchecks (extern-declare the
symbols under test, `check`-style PASS/FAIL printer, non-zero exit on any
failure), and uses an independently written FNV-1a-64 as an oracle rather than
re-running the implementation under test.

Build and run (MinGW; `runtime.c`, `runtime_simd_search.c`,
`counterpart_worker_runtime.c` and `scv_wasm_shim.c` do not compile under
mingw, so TUs are compiled individually and the survivors linked with
`--allow-multiple-definition`, the runtime dir holding mutually-exclusive
alternative TUs):

```sh
export PATH=/c/dev/tool/msys2/mingw64/bin:$PATH
mkdir -p /tmp/rtb/obj /tmp/rtb/use
for f in src/runtime/*.c src/runtime/platform/*.c; do
  b=$(echo "$f" | tr '/' '_'); b=${b%.c}
  gcc -std=gnu11 -O1 -w -c -o /tmp/rtb/obj/$b.o "$f" 2>/dev/null
done                                   # 50 of 54 TUs compile
for o in /tmp/rtb/obj/*.o; do
  case "$(basename $o)" in
    *hosted_win32*|*hosted_cocoa*|*directx*|*sqlite*|*glfw*) ;;   # need SDKs
    *) cp "$o" /tmp/rtb/use/ ;;
  esac
done
# 8 symbols live only in the TUs that do not build under mingw. Stub them so a
# test path that reached one ABORTS loudly rather than passing quietly — the
# two heap counters are the only ones given a real (harmless) value, because
# nothing under test reads them for a verdict.
cat > /tmp/rtb/stubs.c <<'STUBS'
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static void unreachable(const char* n){ fprintf(stderr,"stub reached: %s\n", n); abort(); }
int64_t rt_array_bytes_copy_checked(void){ unreachable("rt_array_bytes_copy_checked"); return 0; }
int64_t rt_array_bytes_store_checked(void){ unreachable("rt_array_bytes_store_checked"); return 0; }
int64_t rt_array_bytes_validate(void){ unreachable("rt_array_bytes_validate"); return 0; }
int64_t rt_heap_live_bytes(void){ return 0; }
int64_t rt_heap_peak_bytes(void){ return 0; }
int64_t simpleos_syscall(void){ unreachable("simpleos_syscall"); return 0; }
int64_t spl_array_get_i64(void){ unreachable("spl_array_get_i64"); return 0; }
double  spl_as_float(void){ unreachable("spl_as_float"); return 0; }
STUBS

gcc -std=gnu11 -O1 -w -Wl,--allow-multiple-definition -o /tmp/rtb/coreabi.exe \
  src/runtime/test/rt_core_abi_untested_selfcheck.c /tmp/rtb/stubs.c \
  /tmp/rtb/use/*.o -lm -lws2_32 -lbcrypt -lmswsock
rc=$?; echo "LINK_RC=$rc"          # measured: 0
/tmp/rtb/coreabi.exe
rc=$?; echo "RUN_RC=$rc"           # measured: 1
```

Real output — **23 checks, 3 failures**:

```
FAIL H0 rt_str_hash(empty) == FNV-1a-64 offset basis (got 1469598103934665603, want -3750763034362895579)
FAIL H1 rt_str_hash(simple) == reference FNV-1a-64 (got 9140951567409697905, want -5909502519632118881)
PASS H2 rt_str_hash order-sensitive (ab vs ba) (-7229320835136510740 != -7230417048229647882)
PASS H3 rt_str_hash(abc) is not strlen (-2204510569963675907 != 3)
PASS L0 rt_len(hello) == 5 (got 5)
PASS L1 rt_len(empty) == 0 (got 0)
PASS L2 rt_len(abcdefghij) == 10 (got 10)
PASS L3 rt_len(2-byte UTF-8 codepoint) == 2 (bytes, not codepoints) (got 2)
PASS L4 rt_len(non-container) == 0 [weak: a 0-stub also passes] (got 0)
PASS T0 trim(  hi  ) (got len=2)
PASS T1 trim( a b ) keeps the interior space (got len=3)
PASS T2 trim(hi) is a no-op (got len=2)
PASS T3 trim(spaces) == empty (got len=0)
PASS T4 trim strips tab/CR/LF too (got len=1)
PASS T5 trim does not collapse an interior tab (got len=3)
PASS I0 to_int(42) == 42 (got 42)
PASS I1 to_int(-17) == -17 (got -17)
PASS I2 to_int( 42 ) == 42 (got 42)
PASS I3 to_int(abc) == 0 (got 0)
PASS I4 to_int(42abc) == 42 [C lenient; Rust crate is strict -> 0] (got 42)
FAIL I5 to_int(64-byte 0...042) == 42 [63-byte truncation RED] (got 4, want 42)
PASS I6 C to_int and to_int_lenient agree on 7 cases (got 1)
PASS I7 lenient(4.2) == 4 (got 4)
FAIL: 23 check(s), 3 failure(s)
```

### 6.2 `test/01_unit/lib/crypto/rt_black_box_direct_spec.spl` — PASS 7/7

```sh
./bin/simple.exe test test/01_unit/lib/crypto/rt_black_box_direct_spec.spl
```
```
✓ B0 returns a present value, not nil
✓ B1 is the identity on a positive value
✓ B2 is the identity on zero
✓ B3 is the identity on a negative value
✓ B4 depends on its argument (not a constant)
✓ B5 preserves the ct_eq accumulator semantics end to end
✓ B6 NEGATIVE CONTROL: proves B0 discriminates where the wrapper does not
SPEC FILE VERDICT: ... outcome=OK declared>=7 executed=7 passed=7 failed=0
Results: 7 total, 7 passed, 0 failed
```

### 6.3 `test/01_unit/lib/simd/rt_simd_divergence_spec.spl` — PASS 12/12

```sh
./bin/simple.exe test test/01_unit/lib/simd/rt_simd_divergence_spec.spl
```
```
✓ H1..H4, M1, M2   (rt_simd_hmax_f32x4 / rt_simd_hmin_f32x4)
✓ G0..G3           (rt_simd_vec4u64_get)
✓ A1, A2           (Vec4f.to_array / from_array)
SPEC FILE VERDICT: ... outcome=OK declared>=12 executed=12 passed=12 failed=0
Results: 12 total, 12 passed, 0 failed
```

### Discrimination self-assessment

| assertion | discriminating? | against what |
|---|---|---|
| H0, H1 | yes | any stub, and the wrong FNV basis (this is the RED) |
| H2 | yes | commutative sum/xor-of-bytes stub |
| H3 | yes | strlen stub |
| L0–L2 | yes | constant / 0 / -1 stub (three distinct lengths) |
| L3 | yes | a UTF-8-codepoint-counting implementation |
| **L4** | **NO** | a stub returning 0 also passes. Labelled in place as a contract pin, not a defect detector. |
| T0–T5 | yes | T1/T5 specifically kill a strip-all-whitespace stub that T0 alone would pass |
| I0–I3, I7 | yes | sign, empty, non-numeric, prefix-parse each distinct |
| I4 | yes for the C lane | *records* the intentional C-vs-Rust split rather than asserting one answer |
| I5 | yes | no plausible stub returns 4 here (this is the RED) |
| I6 | yes | a future divergence between the two aliased entry points |
| B0–B4 | yes | nil / constant / argument-ignoring stub |
| **B5** | **NO** | optimizer *opacity* is a property of generated code and is not observable from any value. Stated in the spec header, not assumed. |
| B6 | yes — it *is* the discrimination proof, executed | |
| H1–H4, M1, M2 | yes | M1 specifically kills a build where hmax/hmin were cross-wired |
| G0, G2 | yes | G0 four distinct lanes; G2 kills a 32-bit truncating read |
| **G1 (OOB half)** | **NOT ASSERTABLE** | the interpreter *raises* on an out-of-range index, so the call cannot be executed without aborting the example. The native lane's "returns 0" is recorded in §7 and in the spec header instead. |
| A1, A2 | yes | lane order and value |

---

## 7. New defects found by writing these tests

### R1 — `rt_str_hash` uses a TRUNCATED FNV-1a offset basis in the bootstrap lane

`rt_str_hash` has two definitions, and they use **different** constants:

| file:line | constant | digits | is it FNV-1a-64's basis? |
|---|---|---|---|
| `src/runtime/runtime.c:541` | `14695981039346656037` | 20 | yes (`0xcbf29ce484222325`) |
| `src/runtime/runtime_legacy_core.c:243` | `1469598103934665603` | 19 | **no — the trailing `7` is dropped** |

The two are the same digit string with the last digit missing. Both files are
recorded as co-defining the symbol in
`scripts/check/runtime_bundle_duplicate_symbols_baseline.txt`
(`rt_str_hash  runtime.c,runtime_legacy_core.c`), and the **core-C bootstrap
capsule** (`scripts/check/build-core-c-bootstrap-runtime-capsule.shs:104`)
compiles `runtime_legacy_core.c` and **not** `runtime.c` — so the bootstrap
lane is the one running the truncated constant.

Measured, not inferred. `nm` on the linked build confirms the definition came
from `src_runtime_runtime_legacy_core.o`, and `rt_str_hash("")` returned
exactly `1469598103934665603`.

Consequence: `rt_str_hash` is **not a single function**. A hash written by a
binary linked against `runtime.c` cannot be read back by one linked against
the capsule. Anything that persists a hash across those lanes — a cache key,
a content address — silently mismatches.

The same truncated constant, labelled "FNV offset basis", appears in eight
more places, all pure Simple or C:

```
src/compiler/40.mono/monomorphize/mono_key.spl:61        monomorphization keys
src/compiler/35.semantics/lint/lint_cache.spl:13         lint cache keys
src/lib/nogc_async_mut/gpu/store/cas_store.spl:189       CONTENT-ADDRESSED store
src/os/kernel/memory/memory_swap.spl:47                  kernel swap
src/os/services/audio/audio_service.spl:202
src/lib/nogc_sync_mut/game2d/ports/doomgeneric.spl:61
src/app/ui.chromium/snapshot.spl:163
src/runtime/runtime_directx_core.c:61, runtime_rocm.c:265
```

against four that use the correct one (`runtime.c`, `stubs.rs:727`,
`platform/test_cpu_common.h:261`, `compiler_rust/lib/std/src/infra/hash.spl:316`).

Severity note, stated honestly: FNV-1a with a different *non-zero* basis is
still a serviceable hash — the distribution is not catastrophically worse, and
this is not a crypto hash. The defect is the **divergence**, not the
distribution: one symbol, two answers, decided by which TU the link picked.

### R2 — `rt_string_to_int` silently truncates its input at 63 bytes

`src/runtime/runtime_native.c:5391`:

```c
char buf[64];
uint64_t n = s->len < sizeof(buf) - 1 ? s->len : sizeof(buf) - 1;
if (n > 0) memcpy(buf, s->data, (size_t)n);
buf[n] = '\0';
return (int64_t)strtoll(buf, NULL, 10);
```

A 64-byte numeric string is parsed as its first 63 bytes. Measured: the
64-character string `"0"×62 + "42"` — whose value is 42 and fits in i64 —
returns **4**. No diagnostic, no saturation, no error: a wrong number.
`rt_string_to_int_lenient` aliases this body, so it truncates identically.
The Rust crate's implementation (`collections.rs:4227`) has no such limit,
making this a third silent C-vs-Rust divergence on a core-required symbol.

### R3 — the existing `black_box_spec.spl` is non-discriminating

See §5. Not a runtime defect; a test-integrity defect on a security-relevant
symbol. Addressed by §6.2, which keeps the old spec (the wrapper's fallback is
worth pinning) and adds the direct-call spec beside it.

---

## 8. Recommended follow-ups

1. **File R1 and R2** as `doc/08_tracking/bug/` records. R1 needs a decision
   (which constant is canonical) before a fix; R2 is a one-line fix
   (parse the string in place, or size the buffer from `s->len`) but the
   selfcheck must stay RED until it lands, per `.claude/rules/testing.md`.
2. **Wire `rt_core_abi_untested_selfcheck.c` into the C selfcheck lane** once
   R1/R2 are fixed — it is currently honestly RED and would block pushes.
3. **Add a lint/guard for the `?? default`-between-spec-and-extern shape**
   (§5). It is mechanically detectable and it currently hides at least one
   security-relevant symbol.
4. **Tier 1's remaining 4 symbols** (`rt_array_set_text`,
   `rt_array_set_len_known_text`, `rt_time_now_unix`,
   `rt_typed_words_u32_push`) have no test and were not covered here.
5. **`rt_hashset_*` (17 symbols) is an entire untested container API** — the
   single highest-count coherent gap, and cheap to close in one spec file.
