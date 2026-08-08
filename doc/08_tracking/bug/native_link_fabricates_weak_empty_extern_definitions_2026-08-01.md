# Native link fabricates strong, non-empty definitions for unimplemented `@extern` fns

- **Date:** 2026-08-01
- **Status:** A link-time guard exists in the Rust seed's
  `linker/native_binary` code (`check_no_fabricated_extern_definitions`), but
  it is not reliably reached by the `native-build` CLI path — see the
  2026-08-08 update for the routing/attribution correction. The pure-Simple
  self-hosted compiler's own host-target `link_llvm_native` path is a
  separate, untested-by-this-fence code path (see update below).
- **Lane:** C1, native link path.
- **Naming note:** the ID/filename says "weak, empty" for historical
  continuity — the original 2026-08-01 evidence genuinely was a weak (`W`),
  zero-size symbol. The evidence now confirmed live (2026-08-08 update) is a
  **strong** (`T`), **non-empty** (3-byte) symbol instead — a different,
  more silent variant of the same fabrication defect. A rename of this file to
  `native_link_fabricates_strong_nonempty_extern_definitions` is recommended
  but not done here.
- **Family:** "an unregistered extern silently returns nil/0 on every lane."
  Interpreter lanes were fixed/gated earlier; this is the native-lane member.
- **Component:** `src/compiler_rust/compiler/src/linker/native_binary/`

## Symptom

An `@extern fn` with no implementation anywhere links clean and produces a
runnable binary. There is no link error and no diagnostic. Every call to the
symbol silently returns garbage.

Real-world instance already observed in the family: `src/lib/gc_async_mut/game2d/transform.spl`
declares `@extern fn _cos(x: f64) -> f64` and `@extern fn _sin(x: f64) -> f64`
with no implementation, so every rotated `Transform2D` computed a garbage world
matrix instead of failing.

## Root cause (measured, not assumed)

When an `@extern fn foo(...)` has no implementation, codegen does **not** leave
`foo` undefined. It emits a **weak, zero-size definition** of `foo` into the
object:

```
$ nm -S main.o
0000000000000000 W lane_definitely_absent      <- weak, DEFINED, no size, empty body
0000000000000000 000000000000000a T spl_main
```

Because the symbol is thereby *defined*, it never appears in `nm -u`. The
existing task-#97 guard `check_no_fake_rt_stubs` (`linker/native_binary/stubs.rs`)
reads `nm -u` output, so it is **structurally unable** to see the symbol.

Two consequences follow, and the second one was the surprise:

1. The `starts_with("rt_")` filter in that guard means a missing non-`rt_`
   symbol that *does* reach `nm -u` gets a fabricated weak `return 0` body from
   `gen_stub_code` with no error.
2. More importantly, **the `rt_` half of the guard does not work either** for
   the `@extern`-without-implementation case, for the reason above. Widening or
   narrowing the prefix filter alone therefore fixes nothing.

### Why the `rt_` prefix filter exists (do not simply remove it)

`check_no_fake_rt_stubs` compares undefined symbols against
`real_runtime_defined_symbols()`, which reads only `libsimple_runtime.a` /
`libsimple_compiler.a`. Non-`rt_` undefined symbols are legitimately satisfied
by libc/libm/system libraries that this function cannot see, so a blanket
extension of *that* guard to all undefined symbols would hard-fail on ordinary
libc references. The prefix filter is doing real work; the correct fix is a
different guard at a different observation point, not a wider filter.

## Reproduction (RED)

Seed binary `src/compiler_rust/target/bootstrap/simple`, relative invocation,
artifact asserted, live known-good control in the same run.

```
# p_nonrt.spl
@extern fn lane_definitely_absent(x: i64) -> i64
fn main() -> i64:
    return lane_definitely_absent(41)

# p_rt.spl  -- same, with an rt_-prefixed name
# p_ctrl.spl -- control, no extern: fn main() -> i64: return 7
```

`simple compile <file>.spl --native -o <file>.bin`:

| case | build exit | artifact | run |
|------|-----------|----------|-----|
| `p_nonrt` (non-`rt_` absent extern) | 0 | YES | hangs (timeout 124) |
| `p_rt` (`rt_` absent extern) | 0 | YES | hangs (timeout 124) |
| `p_ctrl` (control, no extern) | 0 | YES | **exit 7, correct** |

Reproduced identically **with and without** `SIMPLE_BOOTSTRAP=1`, confirming the
fabrication is in codegen and not in the bootstrap-gated auto-stub generator.

False-positive check: a real program (structs, `List<i64>`, string
interpolation, `print`) compiled through the same path yields **0** weak
zero-size definitions and runs correctly (`p=4,6`, `sum=15`, exit 0).

## Fix

New guard `check_no_fabricated_extern_definitions` in
`linker/native_binary/stubs.rs`, called from `builder.rs` on **every** link
(not gated on `bootstrap_mode`, because the fabrication is upstream of it).

It reads `nm --defined-only -S <obj>` and rejects any symbol that is weak (`W`)
**and** has no size. A weak zero-size function symbol has no body by
construction, so the test needs no heuristic and cannot false-positive on a real
function: Cranelift's `Preemptible` linkage also produces weak symbols, but a
real function always carries a non-zero size.

The failure is loud and named — it lists every offending symbol and the object
path.

There is **no env hatch and no allowlist** on this path, by design.

### Exemptions

- **Freestanding targets** (`TargetOS::Any | None | SimpleOS`) are skipped.
  Baremetal intrinsics — the `@extern("bare", ...)` family — are legitimately
  absent at compile time and are resolved by the boot layer. Those links go
  through `pipeline/native_project/stubs.rs`, which has its own per-entry
  fabricated-stub ratchet (`config/freestanding_fabricated_stub_baseline.sdn`).
- **MSVC** toolchains report symbols in a different format; skipped rather than
  misparsed.
- If `nm` cannot be run or fails, the guard fails **open** (same policy as the
  #97 guard) rather than blocking targets it cannot inspect.

Note on the `@extern("bare", ...)` marker: it is a *declaration-side* tag and
does not reach this layer. The string `"bare"` appears nowhere in
`src/compiler_rust/compiler/` or `src/compiler_rust/runtime/`; the 38 `bare`
externs live in `src/compiler_rust/lib/std/src/bare/`. The exemption is
therefore expressed as a target-class check, which is the same population.

## Regression test

`src/compiler_rust/compiler/tests/native_binary_rt_guard.rs` ::
`rejects_fabricated_weak_empty_extern_definitions` — three cases: non-`rt_`
fabricated extern must fail and name the symbol; `rt_` fabricated extern must
fail and name the symbol; and a non-vacuity control object with no fabricated
symbols must still link.

## Remaining (not fixed here)

The **codegen** still emits weak zero-size definitions for unimplemented
`@extern` declarations. This guard catches them at the link, which closes the
silent-wrong-answer hole, but the right long-term fix is for codegen to leave
such a symbol *undefined* (an `External` declaration, not a `WeakAny`
definition) so the system linker reports it natively. Sites to review:
`codegen/llvm/backend_core.rs:1051-1072` (`WeakAny` for bodied functions;
`:1461` already notes "Declarations (no body) must have External linkage, not
WeakAny") and the Cranelift `Preemptible` equivalents in
`codegen/common_backend.rs`.

Also unfixed and separate: `check_no_fake_rt_stubs`'s `starts_with("rt_")`
filter still leaves non-`rt_` symbols that *do* reach `nm -u` to be fabricated
by `gen_stub_code` with a `return 0` body. Closing that requires teaching
`real_runtime_defined_symbols()` about libc/system libraries first; see "Why the
`rt_` prefix filter exists" above.

## Related but separate

`scripts/check/check-extern-registration.shs` (report-only) gates the
*declaration* side. This bug is the *link* side.

## 2026-08-08 update: confirmed LIVE on the deployed self-hosted binary, no fence, false-green spec confirmed

Re-audited as rank-3 finding of
`doc/09_report/infra/aot_lane_regression_fence_audit_2026-08-07.md`.
**Attribution correction:** the deployed `bin/simple` in this checkout IS the
Rust seed (its `--version` prints the seed warning banner; `readlink -f
bin/simple` resolves into `bin/release/x86_64-unknown-linux-gnu/simple`) —
not the pure-Simple self-hosted binary CLAUDE.md names as the default
tooling. So the reproduction below exercises the Rust seed's own
`native-build` CLI path, and the guard's absence is NOT "the guard exists
only in the Rust seed linker, and the pure-Simple host path lacks it" as
originally framed. It is two separate failures inside the seed itself:
`native-build` routes via `driver/src/cli/native_build.rs:34,610` to
`NativeProjectBuilder` (`pipeline/native_project`), which has its own
`linker.rs` that never calls `check_no_fabricated_extern_definitions` at
all. That guard is called only from `linker/native_binary/builder.rs:95`,
reachable only via `pipeline/execution.rs:801,925` — the single-module link
pipeline, a different pipeline than the one `native-build` actually drives.
Even if that pipeline were reached, the guard's own predicate
(`*ty == 'W' && !*has_size`, `stubs.rs:551-553`) could not match the strong
(`T`), size-3 symbol reproduced below — so the guard would still miss this
case. Separately, and still true: the pure-Simple self-hosted compiler's own
host-target link path (`link_llvm_native` in
`src/compiler/70.backend/backend/llvm_native_link.spl:1045`) is untested by
this fence — the reproduction below never executes it, so this document says
nothing about whether that path has the same or a different gap.

**Empirical reproduction** (`bin/simple` = `bin/release/x86_64-unknown-linux-gnu/simple`,
2026-08-08):

```
env -u SIMPLE_BOOTSTRAP bin/simple native-build --source test/fixtures \
    --entry-closure --entry test/fixtures/native_extern_fabrication_probe/main.spl \
    --cache-dir <tmp>/cache --output <tmp>/bin
```

with `main.spl` declaring `@extern fn lane_definitely_absent_probe(x: i64) -> i64`
and no implementation anywhere in the tree:

- Build exit: **0** (no diagnostic).
- `nm -S <bin>`: `0000000000002650 0000000000000003 T lane_definitely_absent_probe`
  — a STRONG (`T`), not even weak, 3-byte defined symbol (more silent than the
  `W`-weak fabrication this doc originally described).
- `nm -u <bin>`: empty for that symbol — never undefined, so no undefined-symbol
  check can ever catch it.
- Running the binary: prints `r=0` and exits 0 — silent wrong answer, not a
  crash, not a fault.

**`SIMPLE_NO_STUB_FALLBACK=1` gates NOTHING on this path.** Re-ran with
`env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build ...`
(same fixture): identical result — exit 0, same `nm -S` line, same `r=0`
output. Root cause: `SIMPLE_NO_STUB_FALLBACK` is read in exactly one place
relevant to fabrication, `simpleos_check_no_fabricated_rt_stubs`
(`src/compiler/70.backend/backend/llvm_native_link.spl:2498`), which is wired
**only** into the four SimpleOS freestanding link branches
(`link_simpleos_x86_64/arm64/riscv64/riscv32`, lines 2674/2786/2960/3032 in the
same file). The generic hosted-C-runtime branch that `native-build` actually
takes for an x86_64-linux entry, `link_llvm_native`
(`src/compiler/70.backend/backend/llvm_native_link.spl:1045`), never calls it
— confirmed by reading the full function body (through its `hosted_cc`/
`hosted_plan` setup and onward) for any `check_no_fabricated`/`fabricat` call;
none exists. So the env var that exists specifically to make this class of
defect fail loudly has no effect for the host lane at all, regardless of
strictness setting.

**Caveat (see attribution correction above):** this paragraph's premise that
`native-build` "actually takes" the pure-Simple `link_llvm_native` is
superseded — `bin/simple` here is the Rust seed, and the seed's own
`native-build` CLI routes through `NativeProjectBuilder`/`linker.rs`
(Rust), not through this `.spl` file. `link_llvm_native` remains real
pure-Simple source with the described gap, but this reproduction does not
establish that it is the code path exercised by the seed's `native-build`.

**Codegen fabrication site**: not pinned down to an exact line this session —
searches for the stub-emission logic in `src/compiler/` under the backend/
codegen layers did not surface it directly; the original Rust-seed doc's
`codegen/llvm/backend_core.rs:1051-1072` pointer does not apply to the
pure-Simple codegen path. Left as an open item for whoever picks up the actual
fix (see "Fix needed" below).

**False-green spec confirmed**: `test/01_unit/compiler/linker/native_link_hardening_spec.spl`,
`it "makes strict SimpleOS links disable fabrication debt baselines"` (line
103) and the neighbouring WP-10 test (line 109) only assert that
`llvm_native_link.spl`'s *source text* contains
`env_get("SIMPLE_NO_STUB_FALLBACK")` and the `flight_closure` baseline-disable
line — i.e. they prove the SimpleOS-only guard's code exists, via
`rt_file_read_text` + `to_contain`, executed under the tree-walk interpreter
(`bin/simple test`, per the systemic AOT-blind-spot finding). They never
invoke `native-build`, never touch the host link path, and would stay green
through the exact defect reproduced above. Nothing here is factually wrong,
but the describe block name ("Native linker hardening") reads as broader
coverage than it provides, and there was no companion spec/fence for the host
lane before this session.

**Fence added**: `scripts/check/check-native-extern-fabrication.shs` +
`test/fixtures/native_extern_fabrication_probe/{main.spl,control.spl}`.
Asserts a control fixture (no extern) still builds/runs correctly under
`native-build` (so this gate cannot go vacuously green because native-build
itself broke), then runs the genuinely-absent-extern case **both** with and
without `SIMPLE_NO_STUB_FALLBACK=1`, hard-asserting the current fabrication
via `nm -S`/`nm -u` evidence (`KNOWN-OPEN`, not a silent pass) and printing a
loud `NOTE` if either case ever starts refusing the build (which would mean
the gap closed and this script should be promoted to a hard assertion).
Sabotage-verified 2026-08-08: mutating the control fixture's expected
output/exit flips the gate to `FAIL`/exit 1; reverting flips it back to
`PASS`/exit 0.

## Fix needed (not done this session)

Per repo rule ("Rust-seed cause -> document, do not patch"), the *documented*
fix target (`check_no_fabricated_extern_definitions` in the Rust seed) is out
of scope for pure-Simple work. But the LIVE defect here is in the pure-Simple
self-hosted compiler's host link path, which is in scope and currently has
**no fabrication guard of any kind** (not even the SimpleOS one). Two possible
fixes, not attempted this session because both require either finding the
exact pure-Simple codegen emission site (not located above) or porting/adapting
`simpleos_check_no_fabricated_rt_stubs`'s classify-by-body logic to a
hosted-ELF/Mach-O/PE-agnostic check inside `link_llvm_native` — neither is a
small, contained change:

1. Codegen should leave a truly-unimplemented `@extern fn` as an external
   declaration (no body), letting the system linker report it as unresolved
   natively — mirrors the Rust seed's stated long-term fix.
2. At minimum, port an `nm -S`-based post-link guard (reject strong OR weak
   zero/near-zero-size defined symbols matching known `@extern` declarations
   with no implementation) into `link_llvm_native`'s hosted branch, gated the
   same way the SimpleOS one is by `SIMPLE_NO_STUB_FALLBACK`/`SIMPLE_SAFETY_PROFILE`.
