# Tracked `auto_stubs.c` weak-nil-stubs 1554 `rt_*` symbols, so the x86_64 kernel link is fail-open

Date: 2026-08-31
Scope: goal item 2 (SimpleOS WM Vulkan-backed evidence). Found while running the
"a clean link is not evidence" check the goal brief calls for.

## Verdict

`examples/09_embedded/simple_os/arch/x86_64/boot/auto_stubs.c` is **git-tracked**
and defines **4020** weak stubs, of which **1554** are `rt_*` runtime symbols.
Every one has the same body:

```c
__attribute__((weak)) RuntimeValue rt_actor_send(RuntimeValue a, ...) {
    (void)a; ...; return NIL_VALUE;
}
```

A weak definition satisfies the linker. So any SimpleOS x86_64 kernel that links
this file **links clean** while up to 1554 runtime entry points silently return
nil at runtime instead of failing closed. `-fsyntax-only` cannot see this
(`check-c-runtime-compiles-push.shs` does not link), the `rt_*` symbol-set guard
counts *definitions* and these ARE definitions, and
`check-no-unresolved-runtime-symbols.shs` looks for *undefined* symbols — a weak
nil stub is defined, so it passes. Nothing on the push path flags it.

## Why this matters for the WM rows

The goal's evidence bar is "the WM composited something Vulkan-backed". The
guest submits draw IR through the ivshmem bridge; that path runs on `rt_*`
calls. If any of them resolves to a weak nil stub, the guest can report success
having done nothing, and a green link is not evidence that it did not. This is
the same defect class as the previously filed
`unregistered_extern_silent_nil_2026-08-01.md`, but at link level and at scale.

## Measured

```
$ S=examples/09_embedded/simple_os/arch/x86_64/boot/auto_stubs.c
$ git ls-files --error-unmatch $S    # tracked
$ grep -c '__attribute__((weak))' $S
4020
$ grep -oE '__attribute__\(\(weak\)\) [A-Za-z_]+ rt_[A-Za-z0-9_]+' $S | wc -l
1554
```

**Measured, not assumed: this file exists for x86_64 ONLY.** There is no
`auto_stubs.c` under the `arm64`, `riscv64`, `arm32`, `x86_32` or `riscv32` boot
directories — checked all five. So this fail-open is specific to the x86_64
freestanding link and does not currently affect the other arches' kernels. That
also means the x86_64 kernel is the one carrying 1554 nil-returning entry points
while the others are not, which is worth knowing before treating x86_64 as the
"most mature" arch lane.

## Correction to a prior finding

The hazard as previously described named `rt_closure_new` resolving to a tiny
weak nil stub. `rt_closure_new` is **not** in this file (`grep -c` = 0); it has a
real strong definition — `runtime_native.c:8042`, and `T` with size 0x97 in the
Rust runtime archive. So that specific symbol's stub came from some other
synthesis path, not `auto_stubs.c`. Both facts are worth keeping: the named
symbol is fine here, and the mechanism is real and far broader than one symbol.

Separately, the **host GPU daemon** build configuration is clean on this axis:
zero WEAK-defined `rt_*` symbols in
`build/simpleos_gpu_host/x86_64-vulkan-cuda-runtime-target/bootstrap/libsimple_runtime.a`.
The fail-open is specific to the freestanding/guest link.

## Fix direction (not attempted)

Do not bulk-delete: 1554 stubs are load-bearing for the link today, and deleting
them turns a silent wrong answer into a build that does not link at all — which
may be correct but is a large, reviewed change, exactly as Stage 2 of the
unbacked-extern bug found. The tractable first step is a ratchet in the shape of
`check-unbacked-extern-ratchet.shs`: freeze the current 1554 in a baseline and
fail any push that adds a weak nil `rt_*` stub, then burn the list down by
implementing or removing the callers. A trap body (`rt_trap()`/`__builtin_trap`)
instead of `return NIL_VALUE` would also convert silent-nil into a loud runtime
failure without changing link behaviour.

---

# Addendum: seed `run` returns EMPTY for a text step-slice, with no error

Separate defect, found in the same session, recorded here so it is not lost.

Under the Rust seed's `run` path, a step-slice of a text value evaluates to the
empty string and reports **no error**:

```
$ cat /tmp/g2_r2.spl
fn main() -> i64:
    val s = "abcdefghij"
    val once = s[::2]
    print("once=[{once}]\n")
    val twice = once[::2]
    print("twice=[{twice}]\n")
    0

$ ./simple run /tmp/g2_r2.spl
once=[]
twice=[]
```

Expected `once=[acegi]`, `twice=[aei]`. Silently returning empty is worse than
erroring: a caller cannot distinguish "no matching characters" from "this
operation is not wired". This is NOT the same bug as the StrBytes length-match
gap fixed in `f3762655e06` — that one raised a loud error on the native-build
frontend path; this one is silent on the `run` path and survives that fix. Not
diagnosed further; the two may or may not share a root cause.
