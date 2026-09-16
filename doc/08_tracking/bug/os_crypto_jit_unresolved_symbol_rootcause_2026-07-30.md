# `os.*` module JIT unresolved-symbol gate — root cause (2026-07-30)

Assignment: root-cause why every standalone probe against `os.crypto.*`
triggers a module-wide "unresolved external symbol" JIT fallback,
classify it (manifest-registration gap / weak-stub leak / structural),
and either fix+unblock the post-quantum retype batch, or document the
structural situation and propose an alternative verification lane.

Binary note (per the assignment's caution): **every result in this doc
is from `bin/simple` — the deployed Rust seed** (confirmed by its own
startup banner, "this Rust-built Simple binary is a bootstrap seed
only"). This investigation did not touch or build a candidate/fresh seed.

## Step 1 — capture the exact symbol (`SIMPLE_JIT_STRICT=1`)

```
$ SIMPLE_JIT_STRICT=1 ./bin/simple probe_hotp.spl
[jit-fallback] unresolved external symbol 'hotp_sha1_bytes': whole module
  dropped to the interpreter (expect ~100-1000x slowdown). Set
  SIMPLE_JIT_STRICT=1 to turn this into a hard error.
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT
  compile: Module error: SIMPLE_JIT_STRICT: unresolved external symbol
  'hotp_sha1_bytes' would NULL-jump in JIT; refusing to fall back to the
  interpreter
hotp(0)=755224
```

**The unresolved symbol is the called function itself**
(`hotp_sha1_bytes`, and separately `base_2b` for the
`slh_dsa_wots.spl` probe from the pass-11 doc) — not an internal `rt_*`
runtime extern it depends on. This immediately rules out classification
(a) (a missing `rt_*` manifest registration, the `5c75a1bbce0` pattern)
and (b) (a fabricated freestanding stub name leaking into host builds):
neither of those families would name the top-level Simple function being
called as the unresolved symbol.

**Side finding, minor, not this pass's focus**: `SIMPLE_JIT_STRICT=1`
does not actually hard-fail here — it prints the "refusing to fall back"
message but the process continues, falls back to the interpreter anyway,
and exits 0 with a correct result (`hotp(0)=755224`). The env var's
intended contract (turn the silent fallback into a hard error) is not
honored on this code path in the deployed seed. Not chased further this
pass (orthogonal to the root-cause question), flagged for a separate fix.

## Step 2 — classify: structural (c), proved via a byte-identical minimal pair

Located the check: `src/compiler_rust/compiler/src/codegen/jit.rs`,
`first_unresolved_import`, which scans the MIR module's function
declarations for `Linkage::Import` entries and reports any that don't
resolve via the JIT's symbol provider (registered runtime symbols +
`dlsym(RTLD_DEFAULT)`). A function ends up `Linkage::Import` when it is
*referenced* by the module being compiled but not *itself compiled into*
that same MIR/JIT unit.

**Isolated the trigger to the module's top-level namespace, not the
function's content**, via three probes:

1. `hotp_sha1_bytes` (real function, calls `hmac_sha1_bytes` internally)
   → unresolved.
2. A brand-new, zero-dependency function appended directly to
   `hotp.spl`: `fn _trivial_probe_fn() -> i64: 42` → **also unresolved**,
   identical fallback message, identical symptom.
3. The **same trivial function body**, copy-pasted verbatim into a new
   file under `src/lib/common/zzprobe/trivial.spl` (`std.common.zzprobe
   .trivial`) and called via `use std.common.zzprobe.trivial
   .{_trivial_probe_fn_lib}` → **compiles and runs under the JIT with NO
   fallback message at all.**

The only difference between (2) and (3) is the top-level module root
(`os.*` vs `std.*`/`src/os/**` vs `src/lib/**`). Content, complexity,
internal dependencies, and call shape are otherwise identical (a
zero-argument function returning a constant). This is airtight: **any
function reachable via a `use os.X` import, called from a host-compiled
entry point, is excluded from the JIT compilation unit and always ends
up as an unresolved `Linkage::Import`** — regardless of what the
function does.

This is classification **(c), structural**: it is not a registration gap
in a manifest of known symbols (the whole `os.*` MODULE — its own
compiled code — is simply never pulled into the host script's MIR/JIT
compilation unit in the first place, so there is no "missing entry" to
add; there is no entry-adding mechanism reached at all for `os.*`
functions on this path). Given the time budget for this pass, the exact
Rust-side code path that draws this `os` vs `std`/`lib` boundary during
module/dependency discovery for the `run`/JIT driver flow was **not**
pinned to a specific source line (leads followed:
`hir/lower/module_lowering/import.rs`, `interpreter_module/path_resolution.rs`,
the `native-build`-specific discovery/imports code under
`pipeline/native_project/`) — the boundary's *existence and exact extent*
are PROVED by the A/B test above; its *precise implementation mechanism*
is INFERRED (very likely: `os.*` is treated as a build target reserved
for SimpleOS/native-project compilation, and the lightweight ad hoc
script-JIT path's module discovery graph is scoped to `std`/`lib`
roots and does not walk `src/os/**`).

## Step 3 — not applicable (this was not case (a))

No manifest registration to fix. Nothing to unblock the retype batch
with a symbol-table edit.

## Step 4 — alternative verification lane (per case (c))

Confirmed `native-build` is real, existing tooling with exactly the
flags the assignment named:

```
$ ./bin/simple native-build --help
  --emit-object         Emit relocatable object output
  --emit-archive        Emit a static archive instead of an executable
  --backend <name>      Codegen backend: llvm-lib, llvm, cranelift
  --entry <file>        Entry file
  --source <dir>        Source directory to compile (repeatable)
```

`native-build` builds a real project graph (not the ad hoc single-script
JIT session), which is the plausible reason it would not hit this
`os.*` exclusion — it is designed to compile a full SimpleOS/native
target, which necessarily includes `src/os/**`. Attempted
`native-build --entry probe_trivial.spl --emit-object` to validate this
directly; it did not complete within this pass's time budget (this seed
binary's native-build path is known-slow — matches the standing
`kill_simple_monitor`/slow-seed-build pattern already on record in this
repo's memory). **Not empirically validated this pass** — proposed, not
proved, per the assignment's own case-(c) instruction ("propose the
alternative verification lane... the campaign then proceeds with that
lane instead").

**Proposed lane for future crypto retype passes touching `src/os/**`:**
1. `native-build --source src/os --emit-object -o <out>.o` (or
   `--emit-archive`) to get a real, fully-linked compilation of the
   target `os.*` file(s) — no more silent interpreter substitution.
2. `objdump -d <out>.o` around the retyped function's disassembly,
   looking for the same signature already established for the `<<3`
   family: a `sar`/arithmetic-shift-right-by-3 (or equivalent decode
   sequence) following the element-read call for a `[i64]`-typed
   parameter, versus its absence for a `list`-typed one — mirroring the
   `SIMPLE_DUMP_MIR` / `UnboxInt`-presence proof already used in the
   pass-10 seed root-cause doc, but at the object-code level instead of
   MIR, since this build path is the one that actually compiles `os.*`.
3. Cross-check against the in-repo NIST KAT spec files
   (`test/01_unit/lib/crypto/{ml_dsa,ml_kem,slh_dsa}*_spec.spl`,
   confirmed present in the pass-11 doc) for value-level correctness,
   run through whatever harness actually invokes `native-build`-compiled
   `os.*` code end-to-end (not `bin/simple test`, which is documented
   elsewhere in this repo's tracking to force
   `SIMPLE_EXECUTION_MODE=interpret` unconditionally and would not
   distinguish this bug either).
4. Budget real wall-clock time for this lane — the timeout hit in this
   pass suggests `native-build` is not a quick add-on step to an
   otherwise-fast verification loop; treat it as its own, slower phase.

## Campaign status

This closes the "why" for the `os.crypto` verification blocker flagged
in the pass-11 post-quantum-retype doc, with a PROVED, airtight
structural boundary (byte-identical trivial-function A/B) and an
INFERRED (not yet pinned to a Rust source line) implementation
mechanism. The post-quantum retype batch (`slh_dsa_wots.spl` +
`ml_dsa*`/`ml_kem*`, 160 sites, from the pass-9/11 docs) remains
unfixed and unblocked-in-practice: the structural cause is now
understood and a concrete alternative lane is proposed, but that lane
was not exercised to completion this pass, so the batch should proceed
under it in a future pass rather than being declared unblocked here.
