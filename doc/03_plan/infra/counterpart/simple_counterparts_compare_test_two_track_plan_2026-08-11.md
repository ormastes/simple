# Simple Counterparts Compare Test — Two-Track Plan

**Date:** 2026-08-11
**Program name:** Simple Counterparts Compare Test (SCCT)
**Parent plan:** `counterpart_conformance_parallel_agent_plan_2026-08-09.md` (waves, agent rules, CI matrix — still authoritative)
**Glossary:** `doc/glossary.md` — *Simple Counterparts Compare Test*, *Counterpart*, *Boundary (Counterpart)*, *Independence Group*, *Relation (Counterpart)*, *Execution Receipt*, *GPU Gate*, *Vacuity (Counterpart)*, *Conversion Loss*
**Skill:** `.claude/skills/spipe.md` § *Writing a Simple Counterparts Compare Test*
**Wiki:** `doc/00_llm_process/feature_expert/{counterpart_conformance,board_vulkan}/skill.md`

This plan splits the work in two because the two halves have *different binding
constraints*, and mixing them hides that fact. Track A is limited by hardware that
is not in this environment. Track B is limited only by engineering effort. A single
combined plan lets Track A's blockers excuse Track B's gaps.

---

## The one-paragraph honest state

SCCT infrastructure is real and its gates bite: four proven refusal classes on GPU
receipts, host-derived independence groups, an arch-substitution guard, a
command-stream canonicalizer proven in both directions, and a SPIR-V canonicalizer
that strips by explicit opcode allowlist. Three real per-SoC command-stream
encoders now exist (Adreno PKT4/PKT7, Intel Gen12 MI/GFXPIPE, IMG BXE submission
envelope). **No capability flag is set on any backend and `board_runnable_count()`
is asserted 0** — because no SoC has a proven SPIR-V stage yet, and
`board_profile_false_claim` refuses `submit` without `spirv`. Two boundaries
execute a genuinely independent counterpart (`vulkaninfo`, `dpkg -S`); the rest do
not, and each has a filed reason.

---

## Track A — Vulkan hardening

**Binding constraint: absent hardware.** Proven, not assumed, per boundary:

| Blocker | Consequence | Filed |
|---|---|---|
| No Intel GPU on this host | no real `anv` batch capture, ever, regardless of tooling | `cmdstream_boundary_no_intel_gpu_on_capture_host_2026-08-11.md` |
| No QEMU model for Adreno or IMG BXE | those in-guest device paths are board-only | `board_vulkan_cross_arch_boundary_only_x86_64_proven_2026-08-11.md` |
| No headless render binary | readback reference stays caller-supplied | `board_vulkan_no_headless_lavapipe_pixel_dump_binary_2026-08-11.md` |
| No verified PowerVR kernel UAPI | BXE envelope layout is our convention, not the real ABI | `img_bxe_submit_encoder_envelope_only_no_kernel_uapi_verification_2026-08-11.md` |

### A1 — SPIR-V stage, the only fully-unblocked Vulkan boundary
`glslangValidator` 15.1.0 is installed and needs no GPU, and Simple has a real
candidate in `spirv_builder.spl`. This is the one place a Vulkan capability flag
can be earned honestly.
- Land the exec-backed comparison using a committed glslang fixture plus a
  provenance record (command line, version, sha256). The bytes originate from
  glslang, not from Simple, which is what separates a fixture from a fabrication.
- Keep one slow exec-backed scenario as the regeneration check so the fixture
  cannot drift from what glslang actually emits.
- **Only then** may `spirv_implemented` flip — and only for backends whose emission
  path is actually exercised.

### A2 — Wire the encoders to the comparator
E3's Gen12 output is not yet adapted into the `CmdPacket` form
`boundary_cmdstream_canonicalize.spl` consumes. Build that adapter without
inventing opcode-name or field mappings for the GFXPIPE sub-fields marked
UNCERTAIN; if a mapping is unknown, the adapter must refuse rather than guess.

### A3 — Confirm the uncertain packet fields
Each encoder carries in-file UNCERTAIN markers (Adreno reserved widths, PKT7
bit-23, PKT4 regaddr width, PKT7 count width, placeholder register/draw operands;
Gen12's GFXPIPE bit split). Resolve them against authoritative documentation and
replace the marker with a cited fact, or leave the marker. Do not silently promote
a guess to a fact.

### A4 — Hardening, once there is something to harden
Sanitizers, fuzzing of the encoders with malformed input, determinism checks.
Deliberately last: hardening code that no boundary yet executes is premature.

---

## Track B — SCCT compare tests and infra hardening

**No hardware constraint.** `libcrypto.so.3`, `libz.so.1.3`, `zstd`, `liblz4-1`
are installed; `dlopen`/`dlsym` already exist in
`src/runtime/counterpart_abi_runtime.c` (declared the single place that touches
them, bootstrapping via `scf_get_api` against `scf_api_v1`). Track B can therefore
demonstrate end-to-end what Track A cannot: a real counterpart loaded, executed,
and compared.

### B1 — Common load-and-compare infra
A Simple-level helper taking (library path, symbol, input, relation) and producing
a `LogicalArtifact` + `ExecutionReceipt` + `ProvenanceReceipt` with a **measured**
`artifact_hash` of the loaded library. Fail closed: missing library, missing
symbol, or errored call ⇒ `ProviderStatus.unavailable` ⇒ rejected run. Never a
literal fallback. The open design question is whether `scf_api_v1` admits arbitrary
libraries or only purpose-built adapters exporting `scf_get_api`; if the latter,
either an SFFI binding or one tiny generic adapter is needed.

### B2 — Ciphers/digests vs OpenSSL
SHA-256 first, with **three** sources so the independence gate is satisfiable:
Simple (`self_execution_mode`), OpenSSL (`independent_reference`, group `openssl`),
published NIST vectors (`normative_vector`). Relation `byte_exact`, no tolerance
ever. **The rule this domain exists to prove:** if Simple and OpenSSL agree but
both differ from the vector, the run must FAIL — two implementations agreeing on a
wrong answer is the common-mode failure the vector authority catches.

### B3 — Compression vs zlib/zstd
Compressed output is *not* byte-comparable between correct implementations, so
`byte_exact` is the wrong relation and would produce false failures. Use
`cross_decode` (Simple compresses → zlib decompresses → equals input, and the
reverse) and `round_trip`. Hostile inputs are mandatory: empty, single byte, highly
repetitive, incompressible, and a **corrupted stream that must be rejected rather
than silently truncated**. zlib and zstd are genuinely separate upstreams — unlike
the six Mesa Vulkan ICDs, which all collapse to one group.

### B4 — Infra hardening
Vacuity and mutation suites over the framework itself; secret redaction (H4);
determinism (locale, timezone, seeds, stable ordering); bounded artifact
retention. This is where hardening effort pays off *now*, because these paths
actually execute.

---

## Rules carried into both tracks

Each was violated by a real lane and caught by review, so they are stated as rules
rather than advice:

1. **Unavailable is never a pass.** A provider that cannot run yields `unavailable`
   and the run is rejected.
2. **Never derive expected output from the candidate.** A hand-authored
   "counterpart" literal is the same defect wearing a disguise — three lanes did
   exactly this before it was caught.
3. **Canonicalize by explicit rule, never by heuristic.** A reachability filter
   deleted `OpLabel`/`OpExtInstImport`, letting a candidate emitting no
   basic-block label pass `byte_exact`. The cmdstream lane independently produced
   the same class via address-masking wide enough to erase the operand under test.
4. **Sabotage or it did not happen.** Every lane turns green to red and back, and
   the red must name the injected divergence. A lane proving only "the adapter ran"
   is rejected.
5. **`executed=0` is a parse error; `timeout=1` is a harness budget kill.** Neither
   is evidence, in either direction. Run specs with `--no-session-daemon` —
   measured ~38x faster (0.68s vs 26.08s) because the session daemon runs a
   full-tree lint pass twice per run.
6. **Independence is derived, not declared.** All six Mesa ICDs resolve to
   `mesa-vulkan-drivers` via `dpkg -S`, so any all-Mesa selection is exactly ONE
   reference. Verify against the host; a declaration alone once let a relabel
   silently inflate the count.
7. **Add a descriptor, never edit a central registry.**
8. **Flags are load-bearing.** Do not flip a capability flag to record intent;
   `board_profile_false_claim` and the asserted `board_runnable_count()` exist to
   make an over-claim a test failure.

## Sequencing

Track B first for depth, Track A1 in parallel. Track B is where a *fully real*
SCCT comparison is achievable today, which is what makes the framework
trustworthy; Track A cannot reach that on this host beyond the SPIR-V boundary.
Track A4 and B4 (hardening) both come after their track has something that
genuinely executes.
