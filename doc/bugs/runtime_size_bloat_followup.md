# Runtime Size Bloat — Architectural Follow-up Plan

*Written: 2026-04-28. Track T3 of executable-size-bloat-analysis Phase 5.*
*Evidence base: `.sstack/executable-size-bloat-analysis/research_local.md`, `research_measure.md`.*

---

## 1. Problem Statement

A `print "Hello World"` Simple binary stripped of debug info is **9,623,568 bytes (~9.4 MB)** on
x86-64 Linux. An equivalent C hello-world stripped to the same level is **14,464 bytes (~14 kB)**.
That is a **665× size ratio** — measured, not estimated (see `research_measure.md`).

The bloat is not linker misbehavior. `--gc-sections` IS passed (see `research_local.md`,
`linker_wrapper.spl:203-274`, `linker.rs:684`), and the input `.rcgu.o` objects DO carry
per-function `.text.*` sections (rustc's default). The 6.2 MB `.text` in the output is
**real reachable code** that the linker correctly retains because it is transitively referenced
from the runtime startup path.

The runtime crate (`src/compiler_rust/runtime/Cargo.toml`) directly depends on:
rustls (TLS), ureq (HTTP), regex, sha2, sha1, tracing, serde, serde_json, and more.
The FFI dispatch table in the runtime statically references every built-in
(`native_http_send`, `regex_match`, `sha256_*`, etc.) by address at startup, which anchors the
entire backing crate graph. Once the table is anchored, the linker has no choice but to keep
every crate it touches. Verification: 2,192 rustls/TLS strings and 39 regex strings appear in
the hello-world binary via `strings`; the linker map shows
`.rodata..Lswitch.table.native_http_send` → `rustls::conn::ConnectionCommon::complete_io` as a
representative anchor chain.

---

## 2. Why the Phase 5 Trim Is Not Enough

Track T1 adds `--icf=safe` (identical-code folding) and flips the strip default for release
builds. These are correct and measurable wins — expected result is roughly 9.4 MB → 5–6 MB
stripped hello-world. That is still a 350–430× ratio vs C.

The real size lever is **dependency reduction**, not link flags. Until the runtime stops
unconditionally pulling in rustls, ureq, regex, and sha2 for every linked binary, no amount of
strip/ICF/LTO will close the gap below a few megabytes.

---

## 3. Concrete Fix Paths (Ranked)

### Option B — Feature-gate optional FFIs (RECOMMENDED FIRST STEP)

**Estimated effort:** 2–3 days.
**Estimated post-fix hello-world size:** 1–2 MB.

Add Cargo features to `src/compiler_rust/runtime/Cargo.toml`:

```toml
[features]
default = []          # minimal — no TLS, no HTTP, no regex, no crypto
tls     = ["dep:rustls", "dep:base64"]
http    = ["dep:ureq", "tls"]
regex   = ["dep:regex"]
sha     = ["dep:sha2", "dep:sha1"]
full    = ["tls", "http", "regex", "sha"]
```

Wrap every use of each optional crate behind `#[cfg(feature = "...")]`. Files that need gating
(verified paths):

| File | Deps to gate |
|---|---|
| `src/compiler_rust/runtime/src/value/ffi/regex.rs` | `regex` |
| `src/compiler_rust/runtime/src/value/ffi/hash/sha256.rs` | `sha2` |
| `src/compiler_rust/runtime/src/value/ffi/hash/sha1.rs` | `sha1` |
| `src/compiler_rust/runtime/src/value/ffi/package.rs` | `sha2` |
| `src/compiler_rust/runtime/src/value/net_http.rs` | `ureq` (confirmed: `use ureq::ErrorKind::*` at line 102) |
| TLS/rustls users | `rustls` — locate with `grep -rn 'rustls' src/compiler_rust/runtime/src/` |

For each gated FFI, the runtime must provide a stub that returns a clean
`"feature not compiled in: <name>"` runtime error rather than a link-time missing symbol.
This keeps user programs that call `http_get` at runtime without TLS getting a clear error
instead of a crash.

Plumbing: the Simple compiler driver (`bin/simple compile --native`) needs a `--feature` flag
(or a project config key) that passes `--cfg feature="tls"` etc. through to the `cargo build`
invocation for the runtime crate. The simplest path: an env var
`SIMPLE_RUNTIME_FEATURES=http,regex` read by the runtime build script, translating into Cargo
feature flags.

Cross-cutting: per memory `feedback_rust_simple_parity.md`, any feature-gating in the Rust
runtime must also be reflected in the SPL hosted-layer equivalents
(`src/lib/nogc_sync_mut/net/`, `src/lib/nogc_sync_mut/crypto/`, etc.) so that interpreter-mode
and compiled-mode stay in parity.

---

### Option C — Lazy FFI registration

**Estimated effort:** 1–2 weeks.
**Estimated post-fix hello-world size:** under 1 MB.

The FFI dispatch table is currently a static structure initialized at startup, which anchors
every registered built-in and thus every backing crate. The fix: make registration lazy.
Each FFI registers itself on first call, via a runtime hashmap populated on demand.
The compiler emits explicit `ffi_register("regex_match", impl_ptr)` calls only for FFIs that
the compiled `.spl` file actually references — unreferenced FFIs generate no registration call
and their backing code is dead-stripped.

Investigation starting point: find where the switch/jump table
`.rodata..Lswitch.table.native_http_send` is generated. This is the static dispatch table in
`src/compiler_rust/runtime/src/value/ffi/` — likely in the top-level `mod.rs` or a
`bridge`/`dispatch` file. The runtime startup code that populates this table is what must
become lazy.

Note: the self-hosted linker (`src/compiler/70.backend/linker/linker_wrapper.spl`) also has an
FFI registry codepath; both the Rust seed and the self-hosted compiler must be updated in sync.

---

### Option D — Split into `simple_runtime_core` + `simple_runtime_extended` crates

**Estimated effort:** 1 week.
**Estimated post-fix hello-world size:** 1.5–2 MB.

Create two Cargo crates:
- `simple_runtime_core` — no TLS, no HTTP, no regex, no sha — only the interpreter loop,
  GC, value representation, basic I/O, and the minimal FFI table.
- `simple_runtime_extended` — everything; links `_core` plus all the optional crates.

User binaries link only `_core` by default. `bin/simple compile --full-runtime` (or a project
config flag) switches the link target to `_extended`. This is a clean split with no `#[cfg]`
sprinkled through individual files, at the cost of maintaining two crate manifests.

Prerequisite: Option B's feature-gating is the natural precursor (it clarifies which code
belongs in which crate).

---

### Option A (already shipped in Phase 5 T1) — Link-flag trim

**Estimated effort:** already done.
**Estimated post-fix size:** 5–6 MB stripped hello-world.

`--icf=safe`, release-strip-by-default. Correct and shipped, but insufficient alone.

---

## 4. Cross-Cutting Concerns

- **Hosted parity** (`feedback_rust_simple_parity.md`): feature-gating in the Rust runtime
  must be mirrored in the SPL standard library (`src/lib/nogc_sync_mut/`). If `net_http.rs`
  is gated behind `http`, the SPL `std.net.http` module must compile-error or stub-out cleanly
  when the feature is absent, not silently produce a runtime failure.

- **Self-hosted compiler sync**: the FFI registry in `linker_wrapper.spl` (self-hosted path,
  `src/compiler/70.backend/linker/linker_wrapper.spl`) must be updated in the same commit as
  the Rust seed path. The Rust seed (`src/compiler_rust/`) is the bootstrap entry point;
  the self-hosted compiler is the production path. Both must agree on which FFIs exist and
  how they are registered.

- **`--whole-archive libspl_objects.a`**: Track A noted the user-code archive is linked with
  `--whole-archive`/`--no-whole-archive`, which forces all user TUs into the binary. This is
  a separate problem from runtime bloat and can be addressed independently (remove
  `--whole-archive` once per-TU section granularity is confirmed sufficient for init-ordering).

- **`-lsimple_compiler` unconditional** (`linker.rs:684`): programs that do not use `eval()`
  still link the full compiler+JIT+parser. This is a third independent size source, addressable
  by making `-lsimple_compiler` conditional on the user program actually calling `eval`.

---

## 5. Decision Recommendation

Start with **Option B** (feature-gate optional FFIs). It has the lowest blast radius: no
structural crate changes, no new build scripts, partial wins compound (each gated crate
reduces binary size independently), and it is the natural prerequisite for Option D. Option C
(lazy FFI registration) is the architectural ideal that reaches sub-1 MB hello-worlds, but it
touches the core dispatch path shared by interpreter and compiled modes and is a significantly
larger commit. Option D is a clean end-state but benefits from B's groundwork.

Recommended sequence: **B → D → C** (gate individual crates → split crates → lazy registry),
with each step independently shippable and measurable.

---

## 6. Evidence Pointers

| Evidence | Location |
|---|---|
| Size measurements (665× ratio, section breakdown) | `.sstack/executable-size-bloat-analysis/research_measure.md` |
| Linker invocation, `--gc-sections`, `--whole-archive` | `.sstack/executable-size-bloat-analysis/research_local.md` |
| Runtime Cargo deps (rustls line 100, ureq line 47, regex line 41, sha2/sha1 lines 82-83, serde line 36, tracing line 39) | `src/compiler_rust/runtime/Cargo.toml` |
| HTTP FFI file using ureq | `src/compiler_rust/runtime/src/value/net_http.rs:102` |
| Regex FFI file | `src/compiler_rust/runtime/src/value/ffi/regex.rs` |
| SHA FFI files | `src/compiler_rust/runtime/src/value/ffi/hash/sha256.rs`, `sha1.rs` |
| Package FFI (sha2 user) | `src/compiler_rust/runtime/src/value/ffi/package.rs` |
| Linker wrapper (self-hosted) | `src/compiler/70.backend/linker/linker_wrapper.spl` |
| Rust seed linker | `src/compiler_rust/compiler/src/linker/native.rs` (line 684) |

---

## 7. Additional April 2026 Evidence

During the cross-target native link-policy follow-up, a plain native compile on
x86-64 Linux still produced an approximately **460 MB** unstripped executable.
This was observed while validating that removing unconditional `-llzma` did not
break standard native binaries.

New finding:

- `liblzma` was not only a linker-default policy issue. The runtime crate also
  exposed `compress` unconditionally, which pulled `xz2` and `lzma-sys` into
  the default runtime closure for ordinary native binaries.
- The immediate fix is to keep compression support behind an explicit runtime
  feature lane so normal native executables do not inherit `liblzma`.
- The larger binary-size problem remains open and is consistent with the
  dependency-anchoring analysis in Sections 1-5 above.

Follow-up expectation:

- keep `packaging-compression` optional in `src/compiler_rust/runtime/Cargo.toml`
- verify the default runtime archive no longer references `lzma_*`
- continue with Option B feature-gating for other heavy optional subsystems
