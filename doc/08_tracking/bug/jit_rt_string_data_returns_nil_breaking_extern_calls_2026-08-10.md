# jit lane: a nested extern call used as an extern ARGUMENT marshals as Nil/Bool/garbage

*(Filed as "`rt_string_data(text)` evaluates to Nil". That title named the
symptom, not the defect — `rt_string_data` is fine in isolation in both lanes.
Kept as the canonical path for inbound links.)*

- **Date:** 2026-08-10
- Status: CLOSED (not reproducible)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  **stale deployed seed** `bin/release/x86_64-unknown-linux-gnu/simple`
  (built 2026-08-09 04:50). A seed built from current `main` does not exhibit
  it in either lane. Fenced going forward by
  `scripts/check/check-jit-nested-extern-arg-marshal.shs`.
- **Lane:** `jit` only on the stale seed. `interpreter` was always correct. The
  AOT/`.smf` lane cannot reach this path at all (OPEN 2).
- **Class:** engine divergence / silent extern-call failure — plus a
  **measurement trap**, which is the more useful half of this entry.

## Reproduction (stale deployed seed only)

`rt_string_data` on its own is correct in both lanes, on every binary tested:

```
extern fn rt_string_data(value: text) -> i64
val line = "Q23B_PAYLOAD"
print "ptr_nonzero={rt_string_data(line) != 0} len={rt_string_len(line)}"
  interpreter: ptr_nonzero=true len=12
  jit:         ptr_nonzero=true len=12
```

The discriminator is **nesting an extern call inside another extern call's
argument list**:

```
val a = rt_simpleos_log_emit(3, rt_string_data(line), rt_string_len(line))  # nested
val p = rt_string_data(line); val n = rt_string_len(line)
val b = rt_simpleos_log_emit(3, p, n)                                       # hoisted
```

On `bin/simple` (the deployed seed), jit lane:

```
ERROR simple_compiler::interpreter_sffi: 806: rt_interp_call error:
  Runtime("rt_simpleos_log_emit: argument 2 must be an int, got Nil")
```

for the **nested** form only. Other fixtures of the same shape reported
`got Bool(true)`, and `argument 1` rather than `argument 2` — the decoded value
follows the bit pattern of whatever raw scalar landed in the slot, so `Nil` is
one face of one defect, not the defect.

**The same fixtures on a seed built from current `main` are clean in both
lanes.** Whatever fixed it landed between the deployed seed's build and now; it
is not in this session's changes.

## The mechanism the symptom points at

Recorded because it explains the symptom exactly and is worth knowing if this
recurs. `src/compiler_rust/compiler/src/codegen/instr/core.rs`,
`compile_interp_call`: the argv-boxing loop picks a boxing helper from
`ctx.vreg_types` and stores **raw** on a miss (`_ => {}`), while the dest block
40 lines below states in its own comment that *"call dests carry no entry in
vreg_types"*. A nested call's dest therefore has no type entry, takes the raw
arm, and `interp_call_handler`'s `runtime_to_value` decodes the plain integer as
a NaN-box pattern.

**This was NOT confirmed to be the live cause**, and the obvious repair
(recording the unboxed type on the dest) was **measured to be a no-op**: a build
with it and a build without it are both clean. It is not in `main` — see the
correction note below. If this ever reproduces again, start here, but prove it
before claiming it.

## Why it was invisible

`src/runtime/startup/common/runtime_log_hosted.c` was, verbatim:

```c
bool rt_simpleos_log_emit(int64_t level, int64_t msg_ptr, int64_t msg_len) {
    (void)level; (void)msg_ptr; (void)msg_len;
    return false;
}
```

A hard `return false` with the arguments explicitly discarded, so the hosted
path **could not distinguish** "the marshal delivered a real string and the hook
is stubbed" from "the marshal handed me garbage". Both return `false`, the
Simple side takes its fallthrough in `logger.spl`, the log line still appears,
and every logging check stays green. **That is the real defect that outlived the
marshal bug**, and it is what this change actually fixes.

## What this change does

`runtime_log_hosted.c` gains a **default-off, level-gated** probe
(`SIMPLE_LOG_HOSTED_PROBE=1`) that writes what the hook actually received to fd 2:

```
[HOSTED-LOG-PROBE] emit level=7 len=20 payload=Q23B_MARSHAL_PAYLOAD
[HOSTED-LOG-PROBE] emit level=9 len=0 payload=<UNREADABLE>      # null ptr
```

The return value is unchanged in both modes, so the hosted contract and every
existing logging check are untouched. Without it, no check can assert anything
stronger than "an error message did not appear" — and error-absence is exactly
the assertion that passes on broken code.

No compiler change ships with this. Per the repo rule against unused code, the
`core.rs` edit that could not be shown to do anything was removed rather than
left in as decoration.

## Board-runnable — SCOPE OF CLAIM

Per `.claude/rules/board-runnable.md`, stating the limit rather than implying
coverage:

- All evidence is **hosted x86_64 Linux**, `interpreter` and `jit` engines.
- **No board evidence and no QEMU evidence was collected.** No claim is made
  about the physical dev board.
- The filing's claim that this "would silently divert every log line away from
  the device" on a jit baremetal build is **withdrawn**: that configuration does
  not exist in this build graph. `src/compiler/70.backend/baremetal/` contains no
  cranelift path, so a board build is AOT-lowered and calls
  `src/runtime/startup/baremetal/runtime_log.c` as a direct C symbol, never
  through `rt_interp_call`.
- A genuine board claim needs an AOT/baremetal build that links `runtime_log.c`
  plus a serial transcript showing the payload on the UART. That is blocked
  today by OPEN 2.

## OPEN 1 — the LLVM lane does not box argv at all

`src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs:2913-2930` builds
the same argv array with `coerce_value_to_type(value, i64)` and a raw
`build_store`, with **no boxing switch at all** — not even the partial one
cranelift has. Whether that is correct depends on an LLVM-lane value
representation this session did not audit. Left OPEN and unmeasured rather than
asserted either way.

## OPEN 2 — `rt_simpleos_log_emit` is undefined in the AOT/`.smf` lane (RED)

```
$ bin/simple compile /tmp/q23/aot.spl -o /tmp/q23/aot.smf     # succeeds
$ bin/simple /tmp/q23/aot.smf
ERROR simple_common::smf::reloc: 95: Undefined symbol: rt_simpleos_log_emit
                                     (required by relocation 7)
error: load failed: relocation failed
```

The symbol is not exported to the SMF loader, so the third lane cannot execute
this path at all. Pre-existing and left RED. It is also what blocks the board
evidence path above, since the AOT lane is the one a board build uses.

## OPEN 3 — the deployed seed carries a marshal defect `main` does not (RED)

`bin/simple` reproduces this; a seed built from `main` does not. Every developer
and every check running on the deployed binary is therefore measuring a compiler
that differs from `main` in at least this behaviour. Redeploy is blocked by the
Stage 3 self-host blocker (`.claude/rules/bootstrap.md`). Filed here so the
divergence is at least written down.

## Check

`scripts/check/check-jit-nested-extern-arg-marshal.shs`, both lanes. It asserts
the **payload at the C boundary**, not a line count — a count assertion passes on
the broken code, because the Simple-side fallthrough already prints an
unlabelled line from another layer, which is precisely how this hid.

- **payload positive** — `[HOSTED-LOG-PROBE] emit level=7 len=20
  payload=Q23B_MARSHAL_PAYLOAD`, proving the `(ptr,len)` pair survived the
  marshal and points at the real bytes.
- **discriminator** — a NULL-pointer fixture must make the probe print
  `<UNREADABLE>`, or the script exits **2** (`ERROR — nothing was checked`)
  rather than PASS. Without it the payload assertion would be vacuous.
- **negative control** — `<UNREADABLE>` absent from the real probe.
- **signature controls** — `must be an int, got` and `rt_interp_call error`
  absent.
- **lane control** — interpreter must agree with jit on every value.
- **probe-off control** — no probe output without the env var.

```
PASS -- 16 assertion(s) checked across 5 probe(s)      exit 0
```

Run against the **deployed** `bin/simple`, which predates the C probe, it exits
**2** (`ERROR — nothing was checked (discriminator silent …)`) rather than
reporting PASS. That is the fail-closed design working as intended: a binary
that cannot answer the question must not be scored as if it had. The check
becomes meaningful on the deployed binary only after a redeploy, which is
blocked by OPEN 3.

## CORRECTION — how this nearly shipped as a false fix

Recorded in full because the trap is more valuable than the bug.

1. Two rebuild attempts used `-p simple_compiler`; the crate is
   `simple-compiler`. **Cargo errored and built nothing, while the wrapper still
   reported exit 0** (the trailing `echo`/`tail` masked cargo's status).
2. `src/compiler_rust/target/release/simple` nevertheless held a binary newer
   than `bin/simple`, built by a **concurrent session**. Running the fixture
   against it showed the defect absent — which reads exactly like "my fix
   works". Caught only by comparing the binary's mtime (08:39:26) with the
   source edit (08:44:43).
3. Rebuilt into a **private** `CARGO_TARGET_DIR` with a positive capability
   probe (`strings | grep -c HOSTED-LOG-PROBE` = 1) to prove the binary really
   contained the change. The check passed.
4. **The revert-proof is what caught the rest.** Rebuilding with the `core.rs`
   fix deleted, the check **still passed** (`PASS — 16 assertions`, exit 0) and
   the nested fixture was still clean. So the change was a no-op and the
   "fix" claim was false. It was removed from `main` in the following commit.

Three lessons, all previously known and all re-learned the hard way here:
a build wrapper's exit code is not cargo's; a shared `target/` can serve another
session's artifact; and **a check that has not been shown to FAIL has not been
shown to check anything.**

## Related

- `doc/08_tracking/bug/logging_surfaces_that_suppress_errors_by_default_family_2026-08-10.md`
- `doc/08_tracking/bug/eprint_in_io_runtime_module_is_rerouted_to_stdout_2026-08-10.md`
- `scripts/check/check-noalloc-log-error-reaches-stderr.shs`
