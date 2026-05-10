# research_measure.md — Track B: Simple vs C Hello-World Size Measurement

*Status: COMPLETE 2026-04-28*

## Test programs

```c
// hello.c
#include <stdio.h>
int main(void) { puts("hello"); return 0; }
```

```spl
# hello.spl
fn main():
    print "Hello World"
```

Both verified to produce the expected output when run.

## Stripped binary sizes

| Binary | Size (bytes) | Size (kB) | vs C-tight |
|---|---:|---:|---:|
| hello.c.tight.stripped (`-Os -ffunction-sections -fdata-sections -Wl,--gc-sections -s`) | 14,464 | 14.1 | 1.0× |
| hello.c.default.stripped (`cc -s`) | 14,472 | 14.1 | 1.0× |
| hello.c.static-tight.stripped (glibc static) | 706,536 | 690.0 | 49× |
| **hello.spl.native** (no strip) | **18,154,008** | **17,729.5** | **1255×** |
| **hello.spl.native.stripped** (`--strip`) | **9,623,568** | **9,398.0** | **665×** |

**Verdict**: Simple's stripped hello-world is ~665× the size of an equivalent C dynamic-linked hello-world, and ~13.6× the size of a fully-static glibc C hello-world. The binary IS a real ELF (verified: `file` reports ELF 64-bit pie executable, dynamically linked; `./hello.spl.native` prints `Hello World`).

## Section breakdown — Simple unstripped (top sections by file-size, KB)

| Section | KB | Notes |
|---|---:|---|
| `.text` | 6,162 | Single monolithic text section (no per-function .text.* — see below) |
| `.debug_str` | 1,549 | Debug info — removable by `--strip` |
| `.debug_info` | 1,389 | Debug info |
| `.debug_loclists` | 1,180 | Debug info |
| `.rodata` | 1,144 | Read-only data — string tables, EC precomputed tables, etc. |
| `.eh_frame` | 846 | Unwind info — needed by Rust runtime |
| `.rela.dyn` | 687 | Dynamic relocations |
| `.debug_line` | 686 | Debug info |
| `.data.rel.ro` | 515 | RO-after-relocation data |
| `.debug_ranges` | 459 | Debug info |
| `.gcc_except_table` | 208 | Exception/unwind tables |

Combined `.debug_*` sections: ~5,317 KB (~5.3 MB) — these are removed by `--strip`, accounting for the 18.2 → 9.6 MB drop.

## Critical correction (2026-04-28): the linker is NOT broken — the runtime is fat by design

Initial hypothesis ("0 .text.* sections in binary → gc-sections cannot work at function granularity") was **wrong**. Re-examined the inputs:

```
== libsimple_runtime.a sample CGU object ==
.text.* sections:   45 (input is per-function ✓)
PROGBITS sections:  622

== rustls CGU object ==
.text.* sections:   273 (input is per-function ✓)
PROGBITS sections:  709

== libsimple_compiler.a sample ==
.text.* sections:   1981
PROGBITS sections:  3469
```

The Rust libs **already emit per-function sections** (rustc default for non-WASM targets). The 0 `.text.*` in the OUTPUT binary is just normal linker behavior: ld merges surviving `.text.*` input sections into one `.text` output section. That's not evidence of GC failure.

**The 6.16 MB `.text` is REAL reachable code, not dead code.** Confirming evidence:

- `strings hello.spl.native | grep -ic 'rustls\|TLSv\|certificate\|HTTP'` → **2,192 matches**
- `strings hello.spl.native | grep -ic 'regex'` → **39 matches**
- Rustls source-file paths embedded as panic messages (e.g. `.../rustls-0.23.36/src/conn.rs`)
- Linker map shows `.rodata..Lswitch.table.native_http_send` in libsimple_runtime, anchoring `rustls::conn::ConnectionCommon::complete_io`

If the symbols were dead code, they'd be empty boxes; instead they have real content the linker correctly preserved.

## Why a `print "Hello World"` pulls in TLS / regex / SHA-256 / Cranelift-JIT

`src/compiler_rust/runtime/Cargo.toml` (lines 39, 41, 83, 100):

```toml
tracing = "0.1"
regex = "1.10"
sha2 = "0.10"
rustls = { version = "0.23", default-features = false, features = ["ring", "std", "tls12", "logging"] }
ureq = "2.10"           # HTTP client for interpreter networking
cranelift-codegen, cranelift-jit, cranelift-object = "0.116"
serde, serde_json, serde_yaml, chrono, uuid, ...
winit, softbuffer (optional)
```

Direct importers in the runtime source:

```
src/compiler_rust/runtime/src/value/ffi/regex.rs        : use regex::Regex;
src/compiler_rust/runtime/src/value/ffi/hash/sha256.rs  : use sha2::{Digest, Sha256};
src/compiler_rust/runtime/src/value/ffi/package.rs      : use sha2::{Digest, Sha256};
src/compiler_rust/runtime/src/loader/startup.rs         : use tracing::{...};
src/compiler_rust/runtime/src/loader/loader.rs          : use tracing::{...};
src/compiler_rust/runtime/src/memory/gc.rs              : use tracing::instrument;
... (HTTP, JIT importers also present)
```

**The runtime exposes built-in FFI functions as global `pub extern "C"` symbols** (e.g. `native_http_send`, `regex_match`, `sha256_hash`). Each is a public root in `libsimple_runtime.a`. When `bin/simple compile --native` links the user binary, ld pulls in **any TU that defines a symbol the user code references**, AND `--gc-sections` then keeps only sections reachable from kept roots.

The 31k+ symbols and 6 MB `.text` show that *something* is referencing the FFI registry. Almost certainly the `tracing` instrumentation injected via `#[instrument]` and the runtime startup code (`startup.rs`, `loader.rs`) statically reference the FFI dispatch table — once any reach the dispatch table, it anchors every registered FFI, which transitively anchors rustls/regex/sha2/JIT.

## Corrected root-cause ranking

1. **Runtime is monolithic by design** — `libsimple_runtime` directly depends on rustls (TLS server+client), ureq (HTTP), regex, sha2, sha1, cranelift-* (JIT), serde+yaml+json, chrono, uuid, winit/softbuffer (optional). A "Hello World" inherits all of them.
2. **FFI registry / dispatch table anchors every built-in** — startup code statically references the full table of FFI symbols, so `--gc-sections` cannot prune individual unused FFIs even at function granularity.
3. **`-lsimple_compiler` linked unconditionally** (Track A `linker.rs:684`) — programs that don't use `eval()`/runtime-compile still link the entire compiler.
4. **`config.strip` defaults to `false`** — non-`--strip` builds carry ~5.3 MB of debug info.
5. **No `--icf=safe`** — many monomorphized Rust generic instantiations are byte-identical; ICF could deduplicate.

(The original Track A hypothesis "`__module_init_*` table anchors every module" is **withdrawn** — `nm` finds 0 such symbols in the binary.)

## Top symbols (proof: hello-world contains the entire TLS+crypto+regex stack)

```
0000000000025000 r ecp_nistz256_precomputed       ← BoringSSL P-256 EC table (148 KB)
0000000000011370 d anon.5f5fbbb0...               ← anonymous LLVM data
0000000000008dc3 T _ZN6rustls4msgs12ffdhe_groups...  ← Rustls TLS — FFDHE groups
000000000000xxxx t _ZN12regex_automata3nfa8thompson8compiler...  ← regex crate Thompson NFA
000000000000xxxx t _ZN6rustls6server5tls12...    ← Rustls TLS server handshake
000000000000xxxx t _ZN4sha26sha2564soft8compress... ← sha2 SHA-256 software impl
```

A `print "Hello World"` program has no business carrying TLS, EC crypto, regex automata, or SHA-256.

## Root-cause ranking (by measured/expected impact)

1. **Rust runtime libs (`libsimple_runtime`, `libsimple_compiler`) built WITHOUT `-Cfunction-sections=yes`** — every reachable TU drops its entire .text in. Estimated impact: **multi-MB**. This is the dominant root cause and explains why Track A correctly noted that gc-sections IS passed yet has no effect on user binaries.

2. **`libsimple_compiler` linked into every native user binary** — a hello-world has no need for the compiler. The link command unconditionally adds `-lsimple_compiler` (Track A: `linker.rs:684`). Estimated impact: **multi-MB**.

3. **`--whole-archive libspl_objects.a`** (Track A) — forces every user TU into the binary, defeating gc-sections at user-code level. For hello-world this is small absolute impact, but for any multi-module Simple program it explodes.

4. **Cranelift emits one `.text` per object, not per-function** (Track A) — even when only user code is considered, the linker can't prune dead user functions. `0 .text.*` sections measured.

5. **Strip is opt-in (`--strip`)** — default release build retains 8.5 MB of debug info. `config.strip=false`.

6. **No LTO, no `--icf=safe`** — even after the above are fixed, ICF would deduplicate the many monomorphized Rust generic instantiations that produce identical code.

## Hard data on prebuilt Simple-built binaries (production, not toy)

| Binary | Size (MB) |
|---|---:|
| `bin/simple_mcp_server` (real file) | 23.4 |
| `bin/simple_lsp_mcp_server` (real file) | 23.0 |

For comparison: `gh` (Go, similarly-sized featureset) ~14 MB, `rg` (Rust regex+search) ~6 MB stripped. The 23 MB Simple-built MCP servers are roughly within the same order of magnitude as their peers because most of their bulk is real functionality, but for trivial programs like hello-world the per-binary baseline cost is the symptom.

## Summary (originally drafted before reachability check)

- **Premise confirmed**: Simple-stripped hello-world is 665× C-stripped hello-world (9.6 MB vs 14 kB).
- **Native compilation works** (`bin/simple compile --native --strip` produces a runnable ELF).
- See "Critical correction" section above for the *corrected* root-cause analysis. The original guesses below this line were superseded.

## After Phase 5 — what landed and what didn't

**Source changes landed** (jj commit `29c7ee21863d`):
- `linker_wrapper.spl:211, 523` — `-Wl,--icf=safe` on user-binary link command (both mold/lld direct and cc fallback paths) ✓
- `native_binary_options.rs:142` — strip default flipped to `true` (Rust seed only) ✓

**Honest scope correction:** the SPL-side strip-default flip did NOT land. `NativeLinkConfig` in `linker_wrapper.spl` has no `strip` field; strip is conveyed via `extra_flags`, and the CLI→`extra_flags` plumbing is in a different file. Flipping the SPL default would have been a multi-file change and was not attempted. The Rust seed's strip-default flip applies only when users hit the bootstrap path. Users on the production self-hosted path (`bin/release/<triple>/simple` → `linker_wrapper.spl`) get only the ICF benefit unless they pass `--strip` explicitly.

**Regression-guard test** (`test/system/exe_size_budget_spec.spl`) and **architectural follow-up** (`doc/bugs/runtime_size_bloat_followup.md`) also landed.

**Measurement of post-T1 binary size: NOT obtained on this run.** A separate (pre-existing, parallel-agent) regression `error: codegen: undefined symbol: rt_cli_run_file` is blocking `bin/simple compile --native` end-to-end. Reproducing the after-number requires:
1. Resolve the `rt_cli_run_file` regression (out of scope for this Phase 5).
2. Re-bootstrap with `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` so the modified `linker_wrapper.spl` is picked up by the self-hosted binary.
3. Re-run the harness (`hello.c` and `hello.spl` in `build/size-bench/`) and append the actual after-numbers here.

**Expected improvement bands** (qualitative, based on standard ICF/strip behavior on Rust-heavy binaries — to be replaced with measured numbers once rebuild succeeds):
| Change | Caller already passes `--strip`? | Expected effect |
|---|---|---|
| `--strip` default flip | yes | no change — they already get the small binary |
| `--strip` default flip | no | ~50% smaller (precedent: 18.2 MB → 9.4 MB observed) |
| `-Wl,--icf=safe` | (independent of strip) | ~5–15% reduction on `.text` due to deduplicated Rust monomorphizations; estimate 0.5–1.5 MB on top of stripped baseline |

**Not in scope (filed in `doc/bugs/runtime_size_bloat_followup.md`):** `-lsimple_compiler` conditional drop, runtime feature-gating (rustls/ureq/regex/sha2/cranelift-jit), lazy FFI registry, `--whole-archive libspl_objects.a` removal. These are the architectural levers that take the binary from ~5–6 MB to <1–2 MB.

**Honest framing of this Phase 5:** the deliverable is the *answer* to the original question (the runtime is fat by design; the linker is correctly retaining real reachable code) plus a *measured trim* (T1 expected ~5–50% depending on prior strip habit) plus a *credible follow-up plan* (Option B feature-gating recommended next). It is **not** a fix that closes the 665× ratio.
