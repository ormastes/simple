# Lane TRIPLEVOCAB — reconcile the two SimpleOS triple vocabularies in build.spl

Status: COMPLETE (uncommitted — lane instructed not to commit)
Owner: lane TRIPLEVOCAB
Date: 2026-07-28
Predecessor: `.spipe/llvm_compiler_rt_gate/state.md` §5

## 1. The inconsistency

`src/os/port/llvm/build.spl` carried two incompatible triple vocabularies:

| Site | Form |
|------|------|
| usage docstring (lines 3-6) | `x86_64-simpleos` |
| `SUPPORTED_TARGETS` | `x86_64-simpleos`, `aarch64-simpleos`, ... |
| `parse_args` default target | `x86_64-simpleos` |
| `CROSS_SUPPORTED_TARGETS` | `x86_64-unknown-simpleos`, ... (only) |
| `CrossBuildConfig.default()` | `x86_64-unknown-simpleos` |

Consequence: `--target x86_64-simpleos` — the form the file itself documents —
passes the new `-simpleos` shape gate (it ends in `-simpleos`) and is then
rejected by `cross_target_supported`'s exact-match allowlist, which is written
only in the `-unknown-simpleos` vocabulary. A user following the documented
usage line got "Unsupported SimpleOS target".

## 2. Evidence — which form is canonical

Canonical toolchain triple is the three-field **`<arch>-unknown-simpleos`**.
Not chosen by preference; every authority in the repo agrees:

- `src/os/port/llvm/build.shs:42` — `TRIPLE="${SIMPLEOS_TARGET_TRIPLE:-${SIMPLE_TARGET:-x86_64-unknown-simpleos}}"`
- `src/os/port/llvm/build.shs:272-274` — help text lists the five triples in `-unknown-simpleos` form
- `src/os/toolchain/llvm/simpleos_cross_toolchain.cmake:19` — `set(SIMPLEOS_TARGET_TRIPLE "x86_64-unknown-simpleos")`
- On-disk toolchain output: `build/os/llvm/cross-x86_64-unknown-simpleos/`
- On-disk release dirs: `bin/release/x86_64-unknown-simpleos/`, `bin/release/riscv64-unknown-simpleos/`
- Sysroot identity file `share/simpleos/target-triple.txt` is compared against `$TRIPLE` (`build.shs:115-116`)
- Clang resource dir asserted by spec: `lib/clang/20/lib/x86_64-unknown-simpleos`

**Both forms are nevertheless in genuine use** (file counts, excluding vendor):
`-unknown-simpleos` in 43 `src/os` + 21 `scripts/os` files; `<arch>-simpleos`
in 21 `src/os` + others. The short form is the **lane/selector** name.

**Decisive precedent** — the repo already resolves exactly this split by
normalizing, in `src/os/port/_BootstrapCross/cross_compile_stages.spl:54-64`:

    fn rust_target_spec_name(target: text) -> text:
        """Map SimpleOS guest lanes to the Rust custom-target JSON names."""
        if target == "x86_64-simpleos":
            return "x86_64-unknown-simpleos"
        ...

Same file also has `SUPPORTED_TARGET_ALIASES` + `normalize_target_selector`.
So the established repo model is: **`<arch>-simpleos` is a selector alias;
`<arch>-unknown-simpleos` is the toolchain triple.** Note host clang does NOT
normalize for us (`clang -print-target-triple -target x86_64-simpleos`
echoes `x86_64-simpleos` verbatim), so the normalization must be explicit.

## 3. Reconciliation applied

Normalization at the boundary (task's preferred option, since both forms are
in real use — silently rejecting a documented form was the bug).

New in `src/os/port/llvm/build.spl`, beside the gate predicate:

    fn canonical_simpleos_triple(triple: text) -> text:
        if not is_simpleos_triple(triple):
            return triple
        val parts = triple.split("-")
        if parts.len() != 2:
            return triple
        "{parts[0]}-unknown-simpleos"

Boundaries wired:

| Site | Change |
|------|--------|
| usage docstring | canonical form; explicit note that the selector alias is accepted + normalized |
| `SUPPORTED_TARGETS` | moved to canonical `-unknown-simpleos`, same vocabulary as `CROSS_SUPPORTED_TARGETS` |
| `parse_args` default | `x86_64-unknown-simpleos` |
| `parse_args --target` | normalized on read |
| `cross_target_supported` | normalize, then allowlist-compare |
| `cross_selected_targets` | normalize each `SIMPLE_TARGET` / `--targets` CSV entry |
| `build_compiler_rt_for_target` | gate on raw input, stage build dir + resource dir under `canon` |

## 4. The gate is NOT weakened

`canonical_simpleos_triple` only rewrites a triple that **already satisfies**
`is_simpleos_triple`. Nothing that would have been refused can be normalized
into acceptance, and normalization runs strictly after the shape gate at every
call site. Verified behaviourally (`bin/simple run`, interpreter):

| Input | `is_simpleos_triple` | `canonical_...` | `cross_target_supported` |
|-------|----------------------|-----------------|--------------------------|
| `x86_64-unknown-simpleos` | true | unchanged | **true** |
| `x86_64-simpleos` | true | `x86_64-unknown-simpleos` | **true** (was false — the bug) |
| `armv7-unknown-simpleos` | true | unchanged | true |
| `x86_64-unknown-linux-gnu` | false | unchanged | **false** |
| `aarch64-apple-darwin` | false | unchanged | false |
| `x86_64-pc-windows-msvc` | false | unchanged | false |
| `simpleos-x86_64` | false | unchanged | **false** (suffix, not substring) |
| `x86_64-simpleos-foo` | false | unchanged | false |
| `""` | false | unchanged | **false** (fail-closed) |
| `wat-simpleos` | true | unchanged (3-field guard n/a, arch unknown) | **false** (allowlist) |
| `mips64-unknown-simpleos` | true | unchanged | false |

`is_simpleos_triple` itself is untouched — still `triple.ends_with("-simpleos")`,
still enforced at all four sites the predecessor lane added.

## 5. Spec matrix

New behavioural `describe "SimpleOS LLVM triple vocabulary"` (8 `it` blocks)
added to BOTH `cross_build_plan_spec.spl` trees. These are **direct
behavioural** checks — they `use os.port.llvm.build.{...}` and call the
functions — not source-text guards, so they cannot pass vacuously.

1. normalizes the selector form onto the canonical triple (all 4 archs)
2. leaves an already-canonical triple untouched (idempotent)
3. accepts both spellings of every supported triple
4. still refuses host triples (linux-gnu / apple-darwin / windows-msvc)
5. still refuses the empty triple
6. treats `-simpleos` as a suffix, not a substring (`simpleos-x86_64`, `x86_64-simpleos-foo`)
7. refuses an unknown arch that merely ends in `-simpleos`
8. normalization cannot launder a refused triple into acceptance

One pre-existing source-text assertion in
`test/02_integration/.../cross_build_plan_spec.spl` asserted the old
`selected.push(trimmed)` body and was updated to the normalizing form.

### Trap check (both traps from the lane brief)

- **Vacuous-read trap:** the new block reads no files at all — it calls the
  functions. The pre-existing source-text blocks read `build.spl` /
  `build.shs` / `compiler_rt_cmake.cmake`, all confirmed present.
- **Brace-interpolation trap:** the new block asserts no string containing
  literal `{...}`. Existing `cross-{{triple}}` / `compiler-rt-{{triple}}`
  escapes left intact and still match.

### Deliberate-red calibration

`assert_false(cross_target_supported("x86_64-unknown-linux-gnu"))` was inverted
to `assert_true(...)` in `test/integration/.../cross_build_plan_spec.spl`.
Observed RED on exactly the intended block and nothing else:

    14 examples, 0 failures        <- untouched source-text describe
      ✗ still refuses host triples
    8 examples, 1 failure          <- new behavioural describe
    Results: 22 total, 21 passed, 1 failed

Reverted; re-run returned `22 total, 22 passed, 0 failed`. The new assertions
therefore execute and are not vacuous.

## 6. Results — per describe

All four specs run individually (never a whole-suite run; machine carries
20+ concurrent `simple` processes from parallel sessions, so each spec was
run detached and sequentially to respect the test-DB serial-access rule).

| Spec | describe | Result |
|------|----------|--------|
| `test/integration/.../cross_build_plan_spec.spl` | SimpleOS LLVM cross-build --print-plan scaffolding | 14 examples, 0 failures |
| " | SimpleOS LLVM triple vocabulary (new) | 8 examples, 0 failures |
| " | **file total** | **22 total, 22 passed, 0 failed** (baseline 14) |
| `test/integration/.../per_target_build_spec.spl` | SimpleOS LLVM per-target build (A4/A5) | 21 examples, 0 failures |
| " | **file total** | **21 total, 21 passed, 0 failed** (baseline 21, unchanged) |
| `test/02_integration/.../cross_build_plan_spec.spl` | SimpleOS LLVM cross-build --print-plan scaffolding | 21 examples, 0 failures |
| " | SimpleOS LLVM triple vocabulary (new) | 8 examples, 0 failures |
| " | **file total** | **29 total, 29 passed, 0 failed** (baseline 21) |
| `test/02_integration/.../per_target_build_spec.spl` | SimpleOS LLVM per-target build (A4/A5) | 60 examples, 0 failures |
| " | **file total** | **60 total, 60 passed, 0 failed** (baseline 60, unchanged) |

Net: +16 examples (8 per tree), zero regressions.

## 7. Not committed

Per lane instruction. Out-of-tree backup of the pre-change files:
`/tmp/llvm_triple_bak/`.

Follow-up worth considering (NOT done here, out of lane scope): the same
selector-vs-triple split exists in `src/os/port/rust/build.spl`
(`SUPPORTED_TARGETS` in short form) — it has its own normalizer via
`rust_target_spec_name`, so it is consistent, but the two `SUPPORTED_TARGETS`
constants across the LLVM and Rust ports now spell targets differently.
