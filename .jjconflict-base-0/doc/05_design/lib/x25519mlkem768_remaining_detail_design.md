# X25519MLKEM768 acceleration — detail design for the remaining work

**Slug:** `x25519mlkem768_acceleration`
**Written:** 2026-08-05
**Companion:** `doc/03_plan/agent_tasks/x25519mlkem768_remaining_tasks.md`
(tasks T-01..T-11). This document designs the four remaining pieces that need a
design rather than a procedure. Everything else in the plan is mechanical.

Scope of this document: D-1 the GPU session layer, D-2 the coverage existence
gate, D-3 the AC-9 benchmark harness, D-4 the SIMD byte-identity harness.

---

## D-1. GPU accelerator session layer (`crypto_accel`)

### Problem

Three GPU NTT providers import a session type from a module that is not in the
repository, and use it as if it were a real handle:

| provider | lines | missing module | type | uses |
|---|---|---|---|---|
| `cuda_ntt_provider.spl` | 476 | `std.gc_async_mut.crypto_accel.cuda_session` | `CryptoCudaSession` | 4 |
| `metal_ntt_provider.spl` | 307 | `...crypto_accel.metal_session` | `CryptoMetalSession` | 5 |
| `vulkan_ntt_provider.spl` | 347 | `...crypto_accel.vulkan_session` | `CryptoVulkanSession` | 3 |

Because an unresolved `use` is only a WARN, the type erases to ANY, every field
access on it becomes field-access-on-ANY, and the seed drops the whole module
to the interpreter. Nothing fails; the provider simply never works and never
says so.

### Design decision gate

**T-01 decides which of the two designs below applies. Do not build either
until that verdict exists.** Building the wrong one wastes the larger effort of
the two.

### Design A — if the modules were LOST

Restore from history and re-validate. The contract is already implied by the
call sites; recover it rather than reinvent it. Extract the required surface by
listing every member access on the session type in each provider:

```sh
/usr/bin/grep -oE '\b(session|_session|sess)\.[a-z_]+' \
  src/os/crypto/x25519_mlkem768/cuda_ntt_provider.spl | sort -u
```

Validation bar, from AC-5 verbatim: each PASS requires **compile, submit,
completion/fence, device-origin readback, backend identity, and byte-identical
CPU-oracle output**. A restored module that merely compiles is not a pass.

### Design B — if the modules were NEVER WRITTEN

Then the three providers are aspirational, and the honest design is a
**declared capability boundary**, not a stub. AC-12 forbids placeholder GPU
artifacts, and AC-5 forbids skips and CPU-mirror passes, so the only compliant
shape is an explicit blocked row.

Shape:

```
CryptoAccelSession (trait)          <- the contract the providers already assume
  ├─ availability() -> Availability  <- Present | Blocked(reason, resume_cmd)
  ├─ submit(...)    -> Result
  └─ readback(...)  -> Result

CudaSession / MetalSession / VulkanSession
  └─ availability() -> Blocked("crypto_accel session layer not implemented",
                              "<exact command to re-check>")
```

Rules for this design:
1. `Blocked` is a **value the caller must handle**, never a silent nil. The
   whole defect here is that absence was invisible; the replacement must make
   absence loud.
2. `require <backend>` MUST fail closed against `Blocked` (see T-09).
   `suggest <backend>` records an honest fallback.
3. No method may return a plausible success value when `Blocked`. A fake
   `connected=false`-style return is exactly the failure mode already found in
   the SSH backend, where an MCP caller could not distinguish "not implemented"
   from "connection refused".
4. The blocked reason must carry a **resume command** — AC-4 and AC-5 both
   require blocked rows to be resumable, not merely annotated.

### Interaction with the known independent blockers

Even with Design A complete, two lanes stay red for unrelated reasons, and
neither is fixed by the session layer:
- **Vulkan**: the source-bound physical NTT probe remains a required row, but
  this Linux host lacks the pinned `glslangValidator` compiler.  `spirv-val`
  alone is not a substitute; the resume command must run on a host with the
  pinned compiler and a Vulkan 1.1 device.
- **Metal**: `ml_kem_ntt.metal` and its exact-metallib/readback runner are now
  present, but this is not a macOS host.  The row remains blocked until Xcode
  compiles that source, a real `MTLDevice` executes both kernels, and the
  device readback matches the canonical scalar oracle.

So AC-5 cannot reach full PASS on this host regardless. The reachable outcome
is: CUDA possibly green, Vulkan and Metal as honest blocked rows with resume
commands. Design accordingly and do not plan for three greens.

---

## D-2. Coverage manifest existence gate

### Problem

`x25519mlkem768_coverage_contract.spl` now has the canonical 30-owner / 18-spec
inventory and an existence gate.  The remaining problem is not phantom paths:
it is the absence of an admitted instrumented native receipt for all 346
critical outcomes.  A static or synthetic row is never coverage evidence.

### Design

A manifest is a **claim about the repository**. The gate makes the claim
falsifiable.

```
for each declared path P in manifest M:
    if not exists(P):
        FAIL with M, P, and "declared but absent"
```

Three properties this must have, each from a lesson already paid for here:

1. **Fail closed, and fail loudly.** The current behaviour is a silent pass.
   The gate must produce a red verdict line, not a warning — warnings exit 0
   and are invisible in 90KB of lint noise.
2. **Non-vacuous by construction.** The gate must be proven to go RED. Add a
   bogus path, capture the RED verdict line, remove it, capture GREEN. A gate
   nobody has seen fail is indistinguishable from a gate that cannot fail —
   this repo has shipped several.
3. **Explicit disposition of the three phantom entries.** Either remove them or
   retain them as declared-blocked rows. AC-8 requires that any unreachable
   item be *"justified in the coverage report rather than excluded silently"*,
   so deleting them quietly would violate the same criterion the gate exists to
   protect.

### What the gate does not do

It does not validate that a listed file is *meaningfully* covered — only that
it exists. Vacuous-example detection is T-08 and is deliberately separate: one
gate, one claim.

---

## D-3. AC-9 benchmark harness

### Problem

AC-9 requires keygen, encapsulation, decapsulation, hybrid-combine, and
end-to-end handshake latency, plus throughput and max RSS, on the same
fixtures. Today: one NTT-primitive timing, no report.

### Design constraints, all evidence-driven

These are not stylistic. Each corresponds to a retracted result in this
campaign.

| constraint | why |
|---|---|
| time wall-clock from OUTSIDE the process | in-language benchmarks here have been proven to fabricate numbers |
| RSS externally (`/usr/bin/time -v`, or `VmHWM`) | same reason |
| alternate arms INSIDE the loop | blocked A/B produced a spurious 12.7% gap and a backwards 1.6x |
| n >= 15, report median AND range | the NTT metric scatters 1.2x-2.9x; a 5-sample median was retracted |
| `SIMPLE_TIMEOUT_SECONDS=0` | else a ~60s CPU guard kills the run at exit 143 and it reads as failure |
| attribute the binary | `bin/simple` prints the Rust bootstrap-seed banner |

### Structure

```
for op in keygen encaps decaps hybrid_combine e2e_handshake:
    for i in 1..N:                  # N >= 15
        run arm A (baseline)        # alternating, not blocked
        run arm B (post-change)
    report median(A), range(A), median(B), range(B), throughput, max RSS
```

### Reporting rule

Report the **median with the range**, never a single reading and never the max.
The existing NTT metric's own spread (1.2x-2.9x) is the argument: any single
reading, including a flattering one, is noise.

If an operation cannot be measured — e2e handshake is the likely candidate,
since the H1 client is blocked on `i64.to_char()` (T-07) — the report states
the blocker. **A partial honest report beats a complete invented one.** Do not
substitute a proxy and label it e2e; a mislabelled proxy is how a campaign ends
up believing it has evidence it does not have.

---

## D-4. SIMD byte-identity harness

### Problem

The only SIMD evidence is an NTT primitive measured through a **C harness**,
whose own scope string says
`focused-primitive-mean-not-full-mlkem-promotion`. AC-4 requires the lane to go
through the **shared public interface**, on the **same fixtures as the scalar
oracle**, proving **byte-identical output**.

### Design

Two arms, one fixture set, three assertions:

```
fixtures := the scalar oracle's own fixtures     # same set, not a copy
A := run through the Simple public interface, SIMD engaged
B := run through the Simple public interface, forced scalar

assert bytes(A) == bytes(B)                      # byte-identity  (the deliverable)
assert backend(A) == 1                           # SIMD really ran
assert backend(B) == 0                           # and the control really didn't
```

**The third assertion is the one that makes the other two mean anything.** If
both arms report the same backend code, the harness proves nothing — it would
pass identically if SIMD never engaged. This is the campaign's recurring
failure mode: a probe whose output does not depend on the thing it claims to
measure.

Public surface: `mlkem_ntt_simd_backend`, `mlkem_ntt_simd_batch`,
`mlkem_ntt_simd_receipt`, `mlkem_ntt_simd_reset` in
`src/lib/nogc_sync_mut/simd.spl`; `trait MlKemNttBatchProvider`, `ntt_simd`,
`intt_simd` in `src/os/crypto/ml_kem_ntt.spl` and `ml_kem_kpke.spl`.

### Non-x86 hosts

ARM and RISC-V are unavailable on this x86_64 box. AC-4 requires them as
**explicit blocked rows with resume commands** — not skips, not CPU mirrors.
The blocked row is a first-class output of this harness, not an omission from
it.

### Contamination guard

Up to 8 agents edit this tree concurrently, and a prior `BACKEND=1` reading in
this campaign was a sibling agent's mid-run edit rather than a real result.
Every measurement stamps `md5sum` **before and after** in the same command; a
changed hash invalidates the run.

---

## Cross-cutting: what "done" means for this campaign

A criterion is met when a **third party can reproduce its evidence from the
repository**. Concretely, three things must all hold:

1. The command is recorded and runs from a clean checkout.
2. The result is a verdict line or an externally-timed number, not an exit code.
3. A negative control exists — something that makes it go red. A check that has
   never been observed failing is not evidence that anything works.

That third point is what this campaign has most often skipped, and it is why
the JIT-drop "100-1000x", the "interpreted SHA-256 bottleneck", the vacuous
`async_tcp_spec` "14 passed", and a shipped empty-digest regression all
survived as long as they did.
