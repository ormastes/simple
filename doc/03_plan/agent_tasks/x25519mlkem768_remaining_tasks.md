# X25519MLKEM768 acceleration — remaining agent tasks

**Slug:** `x25519mlkem768_acceleration`
**Written:** 2026-08-05
**Audience:** a single agent per task, working alone, with no memory of this
campaign. Every task below is self-contained: it states its own preconditions,
exact commands, exact acceptance signal, and the specific traps that have
already produced wrong answers here.
**Model guidance:** tasks marked `TIER: routine` are mechanical and safe for a
smaller model. Tasks marked `TIER: judgement` need a decision that cannot be
mechanised — they say what the decision is.

---

## 0. READ THIS FIRST — the eight traps, in priority order

These are not hypothetical. Each one has produced a published wrong conclusion
in this campaign, several of them mine.

**T1. Score the verdict line, never the exit code.**
The only authoritative result of a spec run is the final
`Results: N total, M passed, K failed` line. Exit 0 proves nothing: an
unresolved `use` is only a WARN, a probe harness with no mode selected falls
through and exits 0, and `assert 1 == 2` once reported `7 passed`.

**T2. A timed-out spec prints `Results: 1 total, 0 passed, 1 failed`.**
That `1 total` is the FILE-LEVEL wrapper counting the file as one timed-out
unit. It is NOT one example. Never report it as "1 example ran".

**T3. Five timeout ceilings, five different symptoms.**

| limit | where | symptom | knob |
|---|---|---|---|
| ~60s CPU guard | resource monitor | exit **143** at ~62s | `SIMPLE_TIMEOUT_SECONDS=0` |
| 120s child default | `test_runner_single.spl:129` | timeout at 120s | `--timeout N` |
| 600s daemon cap | `test_daemon/light_protocol.spl:1-2` | `test daemon timed out`, **no** `Results:` line | none — run detached |
| 10M operations | interpreter | aborts, **no verdict line** | `rt_fault_set_execution_limit(0)` |
| render budget 10s | `WEB_RENDER_BUDGET_MS` | `budget-break at=N of=M`, cascade silently lost | `SIMPLE_WEB_RENDER_BUDGET_MS` |

**T4. Take `$?` from the command under test, never from a pipe.**
`bin/simple` prints ~90KB of lint noise before results. `cmd | grep | head`
truncates the summary AND replaces the exit code with `head`'s. This turned
"8 examples, 4 failures, exit 1" into "zero examples, exit 0". Redirect to a
file, then grep the file.

**T5. Contamination — stamp before AND after, in the same command.**
Up to 8 agents edit this tree at once. A probe that reported `BACKEND=1` was
measuring a sibling agent's mid-run edit. Always:
```sh
md5sum <files> > /tmp/x.before
<the measurement>
md5sum <files> > /tmp/x.after
diff -q /tmp/x.before /tmp/x.after && echo SRC_STABLE || echo SRC_CHANGED
```
`SRC_CHANGED` invalidates the measurement. Re-run; do not report it.

**T6. Interleave A/B arms; never block them.**
A sequential "all of A, then all of B" comparison on this loaded 32-core box
produced a spurious 12.7% gap once and a backwards 1.6x once. Alternate the
arms inside the loop. Report a **median over >=15 repeats with the range** — a
5-sample median was already retracted here as too few.

**T7. `SIMPLE_EXECUTION_MODE=native` IS NOT A MODE.**
Only `interpret` and `jit` exist. Anything else silently means JIT. Likewise
`SIMPLE_NO_JIT=1` is a decoy with no reader in `src/compiler_rust/`.

**T8. In-language benchmarks fabricate numbers.** Time wall-clock from outside
the process. Measure RSS externally (`/usr/bin/time -v`, or `VmHWM` from
`/proc/<pid>/status`).

Two more standing rules: pin `/usr/bin/grep` (ugrep is the default `grep` here)
and anchor your patterns; and `bin/simple` currently prints the **Rust
bootstrap-seed** banner, so every result must be attributed to the seed, not to
the self-hosted binary.

---

## 1. Where the campaign actually stands

Acceptance criteria are in `.spipe/x25519mlkem768_acceleration/state.md`
(12 of them, AC-1..AC-12). Phase is still `implementation-active`.

| AC | subject | state |
|---|---|---|
| AC-1 | versioned config + evidence API | done |
| AC-2 | scalar oracle vs NIST + 3rd-party vectors | done |
| AC-3 | TLS 1.3 negotiation both sides | **done 2026-08-05** (`7e2d463431f`) |
| AC-4 | x86/ARM/RISC-V SIMD via shared interface | **partial** — T-04 |
| AC-5 | CUDA/Vulkan/Metal lanes | **blocked** — T-01, T-02 |
| AC-6 | suggest/require config matrix | believed done, unverified — T-09 |
| AC-7 | three test sets + SPipe manuals | partial — T-08 |
| AC-8 | >=98% branch coverage | **unmeasurable today** — T-03 |
| AC-9 | keygen/encaps/decaps/combine/e2e + throughput + RSS | **missing** — T-05 |
| AC-10 | constant-time / zeroization | partial (NFR-005) — T-10 |
| AC-11 | docs under the slug | mostly done — T-11 |
| AC-12 | no stubs or placeholder GPU artifacts | **fails** — depends on T-01 |

---

## 2. Task list

Dependency order: **T-01 gates T-02 and AC-12.** T-03 gates any coverage claim.
T-04, T-05, T-06, T-07 are independent and may run in parallel.

---

### T-01 — Determine whether the `crypto_accel` session layer was lost or never written
**AC:** AC-5, AC-12 · **TIER: judgement** · **Blocks:** T-02, AC-12

**Why.** All three GPU NTT providers import a session type from a module that
is not in the repo. There is no `crypto_accel` directory anywhere, and the
three types are declared zero times. This is 1,130 lines of provider code
written against types that do not exist. Full evidence:
`doc/08_tracking/bug/crypto_accel_session_modules_do_not_exist_2026-08-05.md`.

| provider | line | missing import | type uses |
|---|---|---|---|
| `src/os/crypto/x25519_mlkem768/cuda_ntt_provider.spl` | 7 | `std.gc_async_mut.crypto_accel.cuda_session.{CryptoCudaSession}` | 4 |
| `.../metal_ntt_provider.spl` | 5 | `...metal_session.{CryptoMetalSession}` | 5 |
| `.../vulkan_ntt_provider.spl` | 5 | `...vulkan_session.{CryptoVulkanSession}` | 3 |

**Precondition — confirm the defect still holds before doing anything:**
```sh
ls -d src/lib/*/crypto_accel 2>/dev/null || echo "ABSENT (expected)"
/usr/bin/grep -rcE '^\s*(class|struct|trait|type)\s+CryptoCudaSession\b' --include=*.spl src/ | /usr/bin/grep -v ':0' || echo "0 declarations (expected)"
```

**Steps.**
1. `git log --all --full-history -- '*crypto_accel*'` — `--all` is required; a
   plain log misses it.
2. For each provider, find the commit that INTRODUCED the import line
   (`git log --all -S 'crypto_accel' -- <provider>`), then check whether the
   target existed at that commit (`git cat-file -e <sha>:<target>`).
3. Search scratch worktrees under `build/worktrees/*` — the ML-KEM SIMD C
   sources were found orphaned there once, and one cleanup would have destroyed
   the campaign's only real timing.
4. If still not found, `git fsck --lost-found` (slow, >2 min here — run it
   deliberately, once).

**Decision to make (this is the judgement).** Exactly one of:
- **LOST** — report the sha and path, diff against what the providers expect,
  and state whether restoring makes them compile. Do not restore in this task.
- **NEVER WRITTEN** — prove it with the introducing commit plus the target's
  absence at that commit, and state plainly that the three GPU lanes are
  aspirational, which makes AC-12 ("no stubs or placeholder GPU artifacts")
  fail until they are either implemented or removed.

**Acceptance.** A written verdict with its evidence chain, appended to the bug
doc above. No code change.

**Traps.** `"exists on disk, but not in <sha>"` reads like ONE missing file but
can mean the whole tree is gone — confirm with `git ls-tree --name-only <sha>`.
A MISSING git object reads as a REWRITTEN history and has caused 13 false
"GONE" verdicts here.

---

### T-02 — Make the GPU lanes honest
**AC:** AC-5, AC-12 · **TIER: judgement** · **Depends on:** T-01

Do not start until T-01 has a verdict. The verdict selects the branch:

**If LOST:** restore the three session modules, then re-run the provider
admission path. A restored module must compile AND its provider must reach a
real device submit — per the campaign's own scope exclusions, *"Emulation, CPU
mirrors, emitted source alone, or cached third-party results do not count as
native SIMD/GPU execution evidence."*

**If NEVER WRITTEN:** the correct action is to make the tree stop claiming
these lanes exist. That means explicit blocked rows with resume commands, not
silent deletion and not a skip. AC-5 requires unavailable hardware to remain
*"an explicit blocked row rather than a skip or CPU-mirror PASS."*

**Known independent blockers, do not re-derive:**
- Vulkan is RED: optimised and unoptimised SPIR-V produce the SAME coefficient
  mismatch on both physical NVIDIA devices (first mismatch index 2, expected
  1970, actual 3323). Three-cycle cap reached. See
  `doc/08_tracking/bug/x25519mlkem768_vulkan_ntt_barrier_mismatch_2026-08-02.md`.
- Metal is blocked by a pure-Simple stage3 compiler crash (exit 139 before
  emitting the module).

**Acceptance.** Either a provider that reaches a real device submit with
byte-identical CPU-oracle output, or explicit blocked rows carrying resume
commands. A CPU-mirror PASS is a task failure.

---

### T-03 — Gate the coverage manifests on file existence, then re-measure AC-8
**AC:** AC-8 · **TIER: routine** · **Blocks:** any coverage claim

**Why.** Two manifests list paths that do not exist, and neither checks:
- `src/app/test/x25519mlkem768_coverage_contract.spl` — 37 listed, **3 missing**
- `src/app/test/x25519mlkem768_critical_inventory.spl` — 24 listed, **3 missing**

The missing three are the same in both:
`src/lib/gc_async_mut/crypto_accel/{cuda,metal,vulkan}_session.spl`. Every
other path resolves. A coverage number computed over a manifest with phantom
entries is untrustworthy in **both** directions.

**Precondition:**
```sh
for m in src/app/test/x25519mlkem768_coverage_contract.spl \
         src/app/test/x25519mlkem768_critical_inventory.spl; do
  tot=0; miss=0
  for f in $(/usr/bin/grep -oE '"(src|test|scripts|doc)/[^"]+"' "$m" | tr -d '"' | sort -u); do
    tot=$((tot+1)); [ -e "$f" ] || miss=$((miss+1))
  done
  echo "$m -> $tot listed, $miss missing"
done
```
Expect `37 listed, 3 missing` and `24 listed, 3 missing`.

**Steps.**
1. Add an existence gate to both manifests that fails loudly on an absent path.
2. Leave a runnable check that goes RED when a non-existent path is added.
   Prove it: add a bogus path, show the RED verdict line, remove it, show GREEN.
3. Handle the three phantom entries **explicitly** — remove them, or keep them
   as declared-blocked rows. State which and why. Silent exclusion is precisely
   what AC-8 forbids: *"any mechanically unreachable branch is justified in the
   coverage report rather than excluded silently."*
4. Re-measure coverage and state whether the 98% bar is met, missed, or
   unmeasurable. All three are acceptable answers. An invented number is not.

**Acceptance.** RED verdict line with a bogus path present; GREEN with it
removed; plus the re-measured figure and the AC-8 verdict.

**Trap.** Concurrent test runs race a shared manifest and can report
`0 total` with exit 0. Pass `--no-cache` AND `--no-cover-check`, and never run
two `bin/simple test` invocations at the same time.

---

### T-04 — Prove the x86 SIMD lane through the shared public interface
**AC:** AC-4 · **TIER: judgement**

**Why.** The only SIMD result today is an NTT-primitive benchmark inside a **C
harness** (`test/09_baselines/crypto/x25519mlkem768/mlkem_ntt_simd_c_test.c`,
built by `scripts/check/build-mlkem-simd-c-lane.shs`, ~1.6x median). Its own
emitted scope string is
`mlkem_ntt_benchmark_scope=focused-primitive-mean-not-full-mlkem-promotion`.
AC-4 requires the lane to go through **the shared public interface** with **the
exact same fixtures as the scalar oracle**, proving **byte-identical outputs**.

Byte-identity is the deliverable. The speedup number is secondary and already
exists.

**Surface under test.**
- `src/lib/nogc_sync_mut/simd.spl` — `mlkem_ntt_simd_backend`,
  `mlkem_ntt_simd_batch`, `mlkem_ntt_simd_receipt`, `mlkem_ntt_simd_reset`
- `src/os/crypto/ml_kem_ntt.spl`, `ml_kem_kpke.spl` — `trait
  MlKemNttBatchProvider`, `ntt_simd`, `intt_simd`

**Steps.**
1. Run the scalar oracle's fixtures through the Simple public interface with
   SIMD engaged; capture outputs.
2. Run the same fixtures forced scalar; capture outputs.
3. Assert byte-identity between them.
4. **Prove SIMD actually ran.** `mlkem_ntt_simd_backend` returning `1` is the
   backend-identity signal, and the forced-scalar arm MUST report `0`. If both
   arms report the same value, the probe proves nothing and the task is not
   done.
5. ARM and RISC-V are unavailable on this x86_64 host. Write them as
   **explicit blocked rows with resume commands** — not skips, not CPU-mirror
   passes.

**Acceptance.** Byte-identity evidence + a backend-identity pair (`1` with SIMD,
`0` forced scalar) + two blocked rows + a plain statement of whether AC-4 is met
for x86.

**Trap.** See T5 — a prior `BACKEND=1` reading in this campaign was a sibling
agent's mid-run edit, not a real result.

---

### T-05 — Produce the AC-9 benchmark evidence
**AC:** AC-9 · **TIER: routine** (mechanical, but T6/T8 are unforgiving)

**Why.** AC-9 requires *"keygen, encapsulation, decapsulation, hybrid-combine,
and end-to-end handshake latency plus throughput and max RSS on the same
fixtures."* Today there is one NTT-primitive timing and **no perf report under
`doc/09_report/` at all**.

**Deliverable.** A report at `doc/09_report/` using the slug
`x25519mlkem768_acceleration`, containing for each of the five operations: n,
median, min, max, throughput, and max RSS.

**Method — non-negotiable.**
- Wall-clock timed from OUTSIDE the process (T8).
- RSS via `/usr/bin/time -v` or `VmHWM`, externally (T8).
- Arms alternated within the loop, never blocked (T6).
- n >= 15, report median AND range (T6).
- `SIMPLE_TIMEOUT_SECONDS=0` (T3).
- Attribute to the seed binary.

**Acceptance.** The report exists with all five operations, or names precisely
which operation could not be measured and why. **A partial honest report beats
a complete invented one** — if e2e handshake latency needs a path that does not
run, say so; do not substitute a proxy and label it e2e.

---

### T-06 — Root-cause `rt_tls13_sha256` returning an empty digest under the JIT
**AC:** none directly; **security defect** · **TIER: judgement**

**Why.** `rt_tls13_sha256` returns a **0-length array under the Cranelift JIT**
while returning the correct 32 bytes interpreted. Since `bin/simple run`
defaults to the JIT, `sha256_text` silently returned the empty string for every
input, exit 0, no diagnostic. `sha256.spl` names this extern as the digest
channel for **std TLS 1.3 and sshd kex**.

```
SIMPLE_EXECUTION_MODE=interpret   sha256_text("abc") -> LEN=64  ba7816bf...20015ad
SIMPLE_EXECUTION_MODE=jit         sha256_text("abc") -> LEN=0   ""
```

A length-guard fallback is already landed at the `sha256_text` call site.
**Do not remove it while chasing the root cause** — its comment says to remove
it only once the extern is fixed and re-measured. Full detail:
`doc/08_tracking/bug/jit_rt_tls13_sha256_returns_empty_2026-08-05.md`.

**Strong precedent — check this shape first.** `rt_mlkem_ntt_simd_batch`
returns `SplArray*`; with no prototype, C defaulted the return to `int`, GCC
kept only `eax` and sign-extended a TRUNCATED pointer:
```
call rt_mlkem_ntt_simd_batch
test %eax,%eax      <- 32-bit null check
cltq                <- sign-extends the TRUNCATED return
cmpq $0x300,0x8(%rax)  <- SIGSEGV
```
That was found by **disassembly**, not by reading source. Consider the
analogous return-marshalling failure here; use objdump/gdb if needed.

**Steps.** Check the registration and declared signature in
`src/compiler_rust/common/src/runtime_symbols.rs`; then the array/slice return
marshalling on the Cranelift path; then pointer/length truncation.

Determine whether the pure-Simple compiler (`src/compiler/`) has the same
defect — it is the default tooling and the seed is bootstrap-only. If the fix
is only possible in the Rust seed, say so explicitly rather than editing Rust
by default.

**Acceptance.** Root cause with evidence; fix or a clear statement of why it is
seed-only; and FIPS 180-4 verification **on both engines**:
```
""       e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
"abc"    ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
56-byte  248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1
```
Do not hand-invent an expected digest — this repo has shipped a fabricated
ed25519 KAT and a fabricated BIP39 vector.

**Trap.** A spec body can NEVER reach the JIT (`describe`/`it`/`expect` are
Rust interpreter intrinsics with zero JIT lowering), so a spec cannot observe
this directly. Use a `fn main` driver under `bin/simple run`, or the sanctioned
`src/lib/nogc_sync_mut/spec/engine_probe.spl` pattern.

---

### T-07 — Implement `i64.to_char()` outside the LLVM backend
**AC:** AC-7 (blocks browser round-trip coverage) · **TIER: routine**

**Why.** `Url.request_target()` -> `_request_target_component()` calls
`i64.to_char()` at
`src/lib/gc_async_mut/gpu/browser_engine/net/entity/url_types.spl:44-48`. That
method exists **only in the LLVM backend**. Both the Cranelift JIT and the
spec-runner interpreter raise:
```
semantic: method 'to_char' not found on type 'i64' (receiver value: 47)
```
(47 is `/`.) Consequence: the browser H1 client cannot complete a request on
either runnable engine. `h1_client_request_spec.spl` is already red for this
(`Results: 11 total, 6 passed, 5 failed`), and
`browser_h1_loopback_e2e_spec.spl` carries a TODO to extend to a full round
trip once fixed.

**Two options — pick and justify.** (a) implement `to_char` for `i64` on the
interpreter and JIT paths; or (b) rewrite the three call sites to use an
existing char/text primitive. Option (b) is smaller and does not extend the
builtin surface; prefer it unless `to_char` has other callers, which you must
check first with an anchored grep.

**Acceptance.** `h1_client_request_spec.spl` goes from `11 total, 6 passed,
5 failed` to `11 total, 11 passed, 0 failed`, and the loopback spec's TODO is
discharged with a real round trip.

---

### T-08 — Sweep the spec corpus for vacuous examples in this campaign
**AC:** AC-7 · **TIER: routine**

**Why.** Two proven cases, both of which looked like coverage:
- `ws_e2e_spec.spl` reports 46 examples: **142** `rt_file_read_text`/`to_contain`
  calls, **0** socket calls. Every example reads a source file as text.
- `async_tcp_spec.spl` reports `14 total, 14 passed`: 14 example bodies that are
  the literal `0`, socket code commented out, zero uncommented `expect`s.

Repo-wide, ~15% of spec examples are vacuous and the corpus is ~46%
duplicated. Assume neither figure applies cleanly to this campaign — measure it
for the campaign's own specs.

**Steps.** For every spec matching `x25519mlkem768` or under
`test/**/crypto/x25519_mlkem768/`, detect: example bodies with no `expect`/
`assert_*`; bodies that are a bare literal; and assertions that cannot fail
(comparing a constant to itself). Report a list, not a fix.

**Acceptance.** A written inventory with counts and file:line references. Do
NOT delete or rewrite specs in this task — establishing which are vacuous is
the deliverable; changing them is a separate decision.

---

### T-09 — Verify AC-6 `suggest` / `require` semantics actually fail closed
**AC:** AC-6 · **TIER: routine**

AC-6: *"`suggest` records honest fallback and `require` fails closed when the
requested capability is absent."* Believed done but never independently
verified. With T-01 pending, `require cuda` is an excellent test: the session
module does not exist, so `require` MUST fail closed rather than fall back.

**Acceptance.** For each backend, two verdict lines: `suggest <absent>` records
a fallback and succeeds; `require <absent>` fails closed. A `require` that
silently falls back is an AC-6 failure and must be reported as one.

---

### T-10 — Close or re-scope NFR-005 (zeroization)
**AC:** AC-10 · **TIER: judgement**

Best-effort overwrite of ML-KEM secret-key slices, FO buffers/coins,
candidate/implicit secrets and provider error-path temporaries is implemented.
NFR-005 remains **partial**: it needs a canonical secure owner/runtime
primitive plus memory-erasure evidence. Limitation and closure criteria are in
`doc/08_tracking/bug/mlkem_gc_secret_zeroization_limit_2026-08-03.md`.

**Decision:** either implement the canonical primitive, or re-scope NFR-005
with the GC/compiler-copy limitation documented as accepted. AC-10 permits the
latter — it requires limitations *"documented and tested where observable"* —
but the decision must be explicit, not left implied.

---

### T-11 — Final AC-11 documentation sweep
**AC:** AC-11 · **TIER: routine** · **Do last**

AC-11 requires research, requirements, NFRs, architecture, detail design, test
plan, agent-task plan, guide, generated manuals, and performance report to all
use the `x25519mlkem768_acceleration` slug or an explicit alias. Verify each
artifact exists and carries the slug. The performance report is produced by
T-05; the detail design is
`doc/05_design/lib/x25519mlkem768_remaining_detail_design.md`.

---

## 3. Landing protocol

Do NOT commit or push from a task agent. The orchestrator lands each verified
fix separately, because up to 8 agents share this working copy and a whole-WC
snapshot would sweep in half-finished work from other lanes.

The landing script builds a tree from **origin's live tip** plus only the named
paths, runs all three pre-push guards on an explicit `<base>..<tip>` range, and
refuses to push unless each prints `PASS —`. Guards invoked with no argument
exit 0 having checked nothing, so the explicit range is mandatory.

Report back: files touched, the verdict lines for RED and GREEN, and anything
you could not measure. An unmeasurable result reported honestly is worth more
than a green one that cannot be reproduced — this campaign has had to retract
several of the latter.
