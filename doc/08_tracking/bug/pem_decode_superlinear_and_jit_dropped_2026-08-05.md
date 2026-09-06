# PEM/base64 decode is superlinear, and the whole module never JIT-compiles

**Status:** PARTIALLY FIXED — accumulator fixed; the "dominant cause" was
MISATTRIBUTED (see 2026-08-05 update below). PEM decode is still ~11.5 s for
16,000 base64 chars **with the module fully JIT-compiled**, so the perf bug is
open on its own terms; the JIT-drop theory is closed.
**Found:** 2026-08-05
**Component:** `src/lib/common/crypto/pem.spl`, plus HIR lowering
(`src/compiler_rust/compiler/src/hir/lower/expr/access.rs:400`)
**Impact:** x509/TLS certificate parsing. 14 s to parse a ~12 KB PEM.

## Measured

Wall clock, timed externally around separate processes (in-language benchmarks
in this repo have been shown to fabricate numbers):

| base64 chars | wall |
|---|---|
| 4,000 | 1.70 s |
| 8,000 | 4.17 s |
| 16,000 | 14.01 s |

Doubling the input more than doubles the time — superlinear.

## What was fixed

`_b64_decode_to_u8` built its filtered character string with
`clean = clean + ch` in a loop. Text is a value type, so each `+` copied the
whole accumulator, making the strip pass quadratic in body length. Replaced with
`kept.push(ch)` and a single `join("")`.

**Correctness proven, not assumed** — RFC 4648 §10 vectors, all six exact:

    Zg==     -> [102]                     f
    Zm8=     -> [102,111]                 fo
    Zm9v     -> [102,111,111]             foo
    Zm9vYg== -> [102,111,111,98]          foob
    Zm9vYmE= -> [102,111,111,98,97]       fooba
    Zm9vYmFy -> [102,111,111,98,97,114]   foobar

These are published standard vectors. No expected value was hand-invented — this
repo has shipped a fabricated ed25519 KAT and a fabricated BIP39 vector.

**Effect: ~10%.** Interleaved A/B at 16,000 chars, alternating OLD/NEW to cancel
load drift on a busy 32-core box:

| round | OLD | NEW |
|---|---|---|
| 1 | 14.78 s | 12.67 s |
| 2 | 13.29 s | 12.49 s |
| 3 | 15.20 s | 13.68 s |

NEW wins 3/3; means 14.42 s vs 12.95 s.

**A first, non-interleaved comparison suggested NEW was 1.6x SLOWER. That was
pure load artifact** — three agents were competing for cores between the before
and after runs. Never compare a before-run against an after-run taken minutes
apart on a loaded box; interleave.

## The "dominant cause" was MISATTRIBUTED — resolved 2026-08-05

The claim below was the working theory. It is now **refuted on three points**.
Keeping the original text so the reasoning error is legible:

> 10% is far too small for removing a dominant quadratic term. The reason is in
> every run log, including the original benchmark:
>
> ```
> [jit-fallback] HIR lowering error: Unsupported feature: cannot infer field type
>   while lowering <fn>: struct 'PemBlock' field 'der_bytes':
>   whole module dropped to the interpreter (expect ~100-1000x slowdown)
> ```
>
> `PemBlock` is `label: text` + `der_bytes: [u8]` (`pem.spl:15-18`). The lowering
> gives up on the `[u8]` field, so **the entire module runs interpreted** — every
> measurement above, OLD and NEW alike, was taken inside a 100-1000x penalty.

### Refutation 1 — "in every run log" is false (12 of 13 logs say something else)

Tallying the `[jit-fallback]` lines across the session's own benchmark logs:

| count | fallback kind |
|---|---|
| 12 | `unresolved external symbol 'parse_pem'` |
| 1 | `HIR lowering error: ... struct 'PemBlock' field 'der_bytes'` |

Every **timing** log (`pem_250/500/1000`, `ab_OLD/NEW_1..3`) dropped for
*unresolved external symbol*, not for the field type. The single field-type log is
`pem_kat.log` — the RFC-4648 correctness driver, which was never timed. So the
14 s measurements were never inside the field-type drop at all.

### Refutation 2 — the field-type drop is a HARNESS ARTIFACT (driver outside the repo)

The `pem_kat` driver lived in a `/tmp` scratchpad. Copied byte-identically into
the repo tree and run with the same binary, same cwd, same command, the drop
disappears:

| driver location | `jit-fallback` lines |
|---|---|
| `/tmp/.../scratchpad/pem_kat.spl` | 1 |
| `<repo>/pk_probe.spl` (identical bytes, `diff` clean) | 0 |
| `<repo>/pk_probe.spl` via absolute path | 0 |

Cause: from outside the source root `use lib.common.crypto.pem` does not resolve
(`simple compile` from that cwd says `Undefined("undefined identifier:
parse_pem")`), so `PemBlock`'s declaration is absent from `global_struct_defs`,
`blocks[0].der_bytes` becomes a field-access-on-ANY, and the module drops. The
`[u8]` type was never the trigger; the unresolvable import was.

The `X25519MlKem768KeyPair.client_key_share` instance is the **same artifact**: an
in-repo driver that calls `x25519_mlkem768_keygen` and reads `.client_key_share`
does not drop on that field; the identical file in the scratchpad does.

### Refutation 3 — the whole-module drop costs ~1.2x here, not 100-1000x

Isolated A/B: two byte-identical self-contained PEM-decode drivers
(`build/radius_probe/drop_{A_nodrop,B_drop}.spl`, 16,000 base64 chars), arm B
carrying one extra function whose field access cannot be inferred. Nothing else
differs, so the delta *is* the drop. Arms alternated inside the loop; wall clock
timed externally with `SIMPLE_TIMEOUT_SECONDS=0`; `md5sum` of both files identical
before and after the run; every run verified to emit `DER_LEN=12000`, and arm
labels verified positively (A: 0 `jit-fallback` lines, B: 1, in all 16 rounds).

| arm | n | median | range |
|---|---|---|---|
| A — JIT compiles | 16 | **11.54 s** | 9.54–17.11 s |
| B — whole module dropped | 16 | **13.66 s** | 12.94–19.95 s |

B was slower in **16/16** paired rounds; paired ratios 1.05–1.59, median ≈1.20x.
The "expect ~100-1000x slowdown" text in the diagnostic is an unmeasured
assertion baked into the message string, not a measured property. Imported
library functions run interpreted either way on this path, so dropping the entry
module changes far less than the message implies.

Diagnostic emitted at
`src/compiler_rust/compiler/src/hir/lower/expr/access.rs:400`. The neighbouring
comment at `:184` correctly attributes it to **field-access-on-ANY** — an erased
receiver at the access site, not the `[u8]` declaration.

### Blast radius — MEASURED: 16 of 295, against a bound of 298

The grep bound reproduces at **829 field declarations across 298 files** today
(was 812/297). That is a **bound**, not a count.

**Method (each candidate actually run, not grepped).** For each of the 298
candidate modules, generate an **in-repo** driver `use <module>` +
`fn main(): print("PROBE_OK")`, run it under `timeout 240 env
SIMPLE_TIMEOUT_SECONDS=0 bin/simple run <relative path>`, and grep the log.
A `use`-only driver does lower the imported module's own functions, so the probe
is not vacuous. Script: `scratchpad/radius/scan.sh`.

**Detector validated by sabotage before trusting it:** appending
`fn _radius_sabotage_probe(a) -> i64: return a.zzz_no_such_field_anywhere_12345`
to `pem.spl` made the previously-clean probe report the drop; `md5sum` of
`pem.spl` identical before and after restore.

| | |
|---|---|
| grep bound (candidate files) | **298** |
| probes run | 298 |
| conclusive (reached `PROBE_OK`) | **295** |
| inconclusive (240 s timeout) | 3 — `browser_script_render`, `browser_renderer`, `engine2d/backend_vulkan` |
| **modules that actually drop on `cannot infer field type`** | **16** (5.4% of conclusive) |
| modules dropping for *any* `jit-fallback` reason | 38 (16 field-type + 22 unresolved-external-symbol) |

`pem.spl` itself is **not** among the 16 — it does not drop when driven in-repo.

The 16: `wine/dll/{image_loader,view_import_binding,view_relocation}`,
`{nogc_async_mut,nogc_sync_mut}/engine/render/software_backend3d`,
`nogc_async_mut/http/h2/h2_server`, `os/apps/sshd/sshd`,
`os/crypto/x25519_mlkem768/{cuda,metal,vulkan}_ntt_provider`,
`os/crypto/x25519_mlkem768/hybrid`, `os/kernel/boot/http_baremetal`,
`os/port/{disk_image,initramfs_pack}`, `os/services/nvfs/core_send`,
`os/tls13/server_handshake`.

They collapse to 11 distinct failing sites and a handful of root causes, and
**the two largest are latent SOURCE defects, not compiler inference gaps**:

- `WineVmOpResult` field `region` (3 modules) — `WineVmOpResult` is
  `ok/state/space`; **no struct in the repo declares `region`**. Already tracked:
  `doc/08_tracking/bug/wine_vm_op_result_missing_region_field_2026-07-20.md`.
- `struct 'ANY' field 'module'` / `'completion_unknown'` (4 modules, all
  x25519_mlkem768 NTT providers) — `cuda_ntt_provider.spl:7` imports
  `std.gc_async_mut.crypto_accel.cuda_session.{CryptoCudaSession}`; **that module
  path does not exist and `CryptoCudaSession` is declared nowhere in the repo**.
  An unresolved `use` is only a WARN, so `self.session` erases to ANY and the
  module silently drops. NOT currently tracked — file it.
- remaining: `String.length`, `i64.generation`, and ANY-typed `ciphertext` /
  `increment` / `stdout_bytes`.

## Next step

1. The PEM perf question is **still open on its own terms**: 16,000 base64 chars
   costs ~11.5 s with the module fully JIT-compiled. The remaining
   superlinearity in `_b64_decode_to_u8` (four `clean.char_at()` per 4-char
   group plus `alphabet.index_of(ch)` per character) is now the leading
   candidate and IS worth optimising — the interpreter-penalty excuse for
   deferring it does not hold.
2. Fix the two source defects above (`region`, `CryptoCudaSession`); that alone
   removes 7 of the 16 drops without touching the compiler.
3. Correct the diagnostic string: `expect ~100-1000x slowdown` is unmeasured and
   measured ~1.2x on this workload. It has now caused one misdiagnosis.

## Not fixable in pure-Simple — the defect is seed-only

The standing rule is fix pure-Simple over Rust, so the pure-Simple compiler was
checked first. **It does not have this defect, structurally.**

- `src/compiler/` and `src/app/` contain **no** `cannot infer field type` error,
  no `[jit-fallback]` marker, and no whole-module-drop-to-interpreter path. All
  three strings exist only in the Rust seed (`hir/lower/expr/access.rs:400`,
  `driver/src/exec_core.rs:1064`).
- Pure-Simple HIR keeps the field **name**, not a resolved index:
  `src/compiler/20.hir/hir_definitions.spl:457` —
  `Field(base: HirExpr, field: text, resolved: SymbolId?)`. When the field type
  cannot be determined it emits `type_: nil` and continues
  (`20.hir/hir_lowering/expressions.spl:642`); MIR resolves late by name
  (`50.mir/_MirLoweringExpr/expr_dispatch.spl:1714`). There is no point at which
  an unknown field type can abort a function, so it cannot drop a module.

Environment note for whoever re-runs this: in this worktree **both** `bin/simple`
and `bin/release/x86_64-unknown-linux-gnu/simple` print
`WARNING: this Rust-built Simple binary is a bootstrap seed only`, so no
pure-Simple binary was available to confirm empirically; the pure-Simple finding
above is from source, at two layers. Every measurement in this document was taken
on the **Rust seed**.

Editing `access.rs` was therefore not done: it would be a Rust-seed-only change,
for a 1.2x effect, on 16 modules of which the majority are really source bugs.

## Reproduce

```
# build a PEM with N*16 base64 chars, parse it, time externally
timeout 400 env SIMPLE_TIMEOUT_SECONDS=0 ./bin/simple run <driver>.spl
grep -a 'jit-fallback' <log>   # confirms the module ran interpreted
```

Score wall clock from outside the process. `SIMPLE_TIMEOUT_SECONDS=0` is required
or a ~60 s CPU guard kills the 16,000-char run at exit 143 and it reads as a
failure.
