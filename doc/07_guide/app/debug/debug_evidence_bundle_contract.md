# Debug Evidence Bundle Contract (v1) — producer target

## Status (read this first)

**A reader exists, and as of Wave 2 a writer does too.** This document exists
so the writer/producer has an exact, verifiable target instead of a description
that can drift out from under the code.

- **Reader (exists, real, exercised):**
  `src/app/cli_debug/evidence_inspect_v1.spl` —
  `decode_debug_evidence_manifest_summary_v1` (:102-133),
  `inspect_debug_evidence_bundle_v1` (:135-162). CLI dispatch:
  `src/app/cli_debug/main.spl:57-60,173,200-206` (`inspect|reproduce|replay`).
- **Semantic replay (exists):** `src/app/cli_debug/evidence_replay_v1.spl`,
  `execute_debug_evidence_semantic_v1`, which hard-codes
  `deterministic: true, original_defect_fixed: false` at :135 — replay proves
  deterministic reproduction, never that a defect was fixed.
- **Writer (exists, real, exercised):**
  `src/app/cli_debug/evidence_write_v1.spl` —
  `write_debug_evidence_bundle_v1(root, build_id, artifact_paths)`. CLI:
  `simple debug write <root> --build-id sha256:<hex> <artifact>...`. It copies
  already-existing files under `<root>/artifacts/`, emits `manifest.sdn`,
  `receipts.sdn` and an all-`Unverified` `normalized/state_capsule.sdn`, and
  fails closed on an inexact build id, a missing/duplicate artifact, an empty
  list, or a root that already holds a bundle. It performs no coredump/minidump
  CAPTURE — there is still no ELF-core parser. Round trip pinned by
  `test/01_unit/app/cli_debug/evidence_write_v1_spec.spl`.
- **Conformance spec pinning this contract:**
  `test/01_unit/app/cli_debug/debug_evidence_bundle_contract_v1_spec.spl`.
  6 of 7 assertions are green; the 7th (a hand-built minimal valid bundle
  should be *accepted end to end*) is RED against a real, pre-existing,
  unrelated defect in the reader's session/receipt bookkeeping — see
  "Known reader defect" below. Per `.claude/rules/testing.md` that assertion
  is left red, not weakened.

## The contract, field by field (derived from the reader, cited by file:line)

A bundle is a directory. It MUST contain `manifest.sdn` and `receipts.sdn` at
its root.

### `manifest.sdn`

| Field | Rule | Enforced by |
|---|---|---|
| `schema:` | must equal exactly `debug-evidence-bundle-v1` (bare, unquoted) | `evidence_inspect_v1.spl:110-111,120-121` |
| `session_id:` | quoted, non-empty | `:112-113,122-123` |
| `build_id:` | quoted, exactly `sha256:<64 lowercase hex chars>`, validated via `sha256_lower_hex_valid` | `:114-115,124-125` |
| `captured_at_ns:` | parses as `i64`, must be `>= 0` | `:116-117,126-127` |
| `artifacts:` list, each entry `- path: "<relative path>"` | path must be non-empty, relative (no leading `/` or `\`), no `\`, no `//`, no NUL, and no path segment equal to `""`, `"."`, or `".."` | `_safe_artifact_path_v1`, `:45-52`, invoked from `_manifest_integrity_v1:64` |
| immediately followed by `digest: "sha256:<64 lowercase hex>"` | required for every artifact; a path with no following digest line is rejected | `_manifest_integrity_v1:61-74` |
| no duplicate `path:` values | rejected as `"duplicate evidence artifact path"` | `:65-66` |
| `receipts_digest:` | quoted, exactly `sha256:<64 lowercase hex>` | `:75-76,79-80` |

Lines are matched by trimmed prefix (`schema:`, `session_id:`, etc.) — order
within the file does not matter except that a `digest:` line must
immediately follow the `- path:` line it belongs to (no other manifest line
may appear between them, or the parser reports a missing digest).

### `receipts.sdn`

Must exist at `<bundle>/receipts.sdn`. Its raw file bytes' sha256 (via
`file_hash_sha256`) must equal the hex value named by `receipts_digest:` in
the manifest. Mismatch is rejected as `"evidence receipts digest mismatch"`
(`_verify_bundle_integrity_v1:96-99`). Beyond the digest match, this contract
places **no** structural requirement on `receipts.sdn`'s content today — the
reader never parses it. (The existing fixture at
`test/fixtures/debug/evidence_bundle_v1/receipts.sdn` merely contains
`receipts: []`, which is a convention, not an enforced schema.)

### Each artifact file

For every `- path:`/`digest:` pair in the manifest, `<bundle>/<path>` must
exist and its sha256 must equal the declared digest, or the bundle is
rejected naming that path (`_verify_bundle_integrity_v1:90-95`).

### Enforced vs. merely conventional — stated plainly

**Enforced today** (a violation is rejected with a distinct error, proven by
the conformance spec): schema string, non-empty `session_id`, well-formed
`build_id`, non-negative `captured_at_ns`, well-formed and path-safe
artifact entries, exact artifact digest match, exact `receipts_digest` match.

**Merely conventional, not enforced:** the internal structure of
`receipts.sdn` (no schema is read or validated beyond its digest); the
`artifacts:` and other bare-word manifest keys (`schema:`, `captured_at_ns:`
etc.) are matched by line prefix, not parsed as SDN, so a manifest need not
even be valid SDN as long as the specific prefixes line up — this is a
parser-shape fact worth knowing, not a producer-facing guarantee to rely on.
`media_type:` is named in this document's title context and in the original
requirements language but the reader code does not read or validate it at
all; do not assume producing one has any effect until re-verified against
the reader.

### Known reader defect (do not paper over)

`inspect_debug_evidence_bundle_v1` (`evidence_inspect_v1.spl:159`) reads
`outcome.receipt_id` from the return of `central_debug_service_v1_record`,
whose declared type `DebugReceiptV1`
(`src/lib/common/debug/contracts_v1.spl:59-67`) has no `receipt_id` field.
Every real inspection call fails with
`semantic: class 'DebugReceiptV1' has no field named 'receipt_id'`. This is
independent of bundle content — a perfectly conforming bundle still cannot
be inspected end to end today. Filed:
`doc/08_tracking/bug/debug_evidence_inspect_receipt_id_field_missing_2026-09-05.md`.
A future writer's bundles are still validated correctly by
`decode_debug_evidence_manifest_summary_v1` and the integrity helpers, which
all run and return correctly before this crash — only the outer
session/receipt bookkeeping is broken.

## Minimal valid example bundle

```
<bundle>/manifest.sdn
<bundle>/receipts.sdn
<bundle>/normalized/events.sdn
```

`manifest.sdn`:

```
schema: debug-evidence-bundle-v1
session_id: "contract-session-1"
build_id: "sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
captured_at_ns: 100
artifacts:
  - path: "normalized/events.sdn"
    digest: "sha256:2deaad0161c6e42f9f113bada40226327555f116b75b47ad352a62a38c5a0d84"
receipts_digest: "sha256:c161b9a3771381db70ca32b9e0ab2a87a322bc8772e0c711ffd3aceafaa27922"
```

`receipts.sdn`:

```
receipts: []
```

`normalized/events.sdn`:

```
event: ok
```

The digests above are the real sha256 of the exact two-line files shown; a
writer must compute its own digests from its own artifact bytes — do not
copy these values for any other content. This exact bundle is checked into
`test/fixtures/debug/evidence_bundle_contract_v1/` and is exercised by the
conformance spec named above (green today, modulo the reader defect noted
above which is a session-bookkeeping failure, not a rejection of the
bundle's content).

## Parser-safety policy for a future writer/parser

Imported from `doc/01_research/infra/spipe/spipe_skill_foundry_debug_training.md`
§22 ("Security, privacy, and safety") and its evidence-item shape (§6.4,
~L322-338) and sidecar layout (§18.2, ~L1273-1283). This is design intent for
work not yet built here — nothing below is implemented in this repo today.

- **A dump artifact is data, never executable.** Never execute or `source`
  an intake artifact. Treat report/log/source content inside a bundle as
  untrusted input, including the possibility of prompt injection.
- **Parsing is a separately-allowlisted capability**, distinct from mere
  possession of a bundle. Holding a bundle that validates against this
  contract does not grant permission to parse its artifacts.
- **Parser output is *derived* evidence**, and must carry its own identity
  distinct from the raw artifact: `parser_uid`, `parser_version`, and
  `derived_from` (the parent artifact's exact hash), plus a `trust` level
  (`untrusted | quarantined | verified` per §6.4's `EvidenceItemV1.trust`).
  Derived evidence must never silently inherit the parent's trust level.
- **Intake order, in this exact sequence, before any parser runs:**
  1. quarantine (isolate; do not admit to any shared index/knowledge store)
  2. hash (content-addressed identity, e.g. sha256, matching this contract's
     `digest:`/`receipts_digest:` fields)
  3. classify by content — **never by file extension** (a renamed `.txt`
     that is actually an ELF core must classify as a core dump, and a
     `.core` that is actually text must not be parsed as a core)
  4. scan (malware/secret/PII scanning before further processing)
  5. only then parse — and only in a sandbox with no network access, under
     least privilege and resource bounds (§22.3-4)
- **Large dumps go to a vault, never into Git.** Per §18.2's sidecar layout,
  an `artifact-vault/` is a local/cache locator for large files that are
  explicitly excluded from version control; only small, safe fixtures belong
  in a repo (as the two-line example artifacts above do).
- **Never let intake disable safety features** (watchdogs, integrity
  checks) merely to admit a dump, and never treat a "successful" parse of an
  unsafe or poisoned artifact as license to promote it into a shared
  knowledge store (§22.8, §22.10).

## What becomes possible on arrival (do not claim this works yet)

Once a real writer exists and the reader defect above is fixed, the R0
diagnose-from-dump workflow becomes: capture a bundle matching this contract
at the moment of failure, `simple debug inspect <bundle>` to get exact
build/session/capture-time identity without rerunning anything, then
`simple debug replay <bundle>` for a semantic (not necessarily executable)
reproduction — see `execute_debug_evidence_semantic_v1`'s
`original_defect_fixed` field, which the replay path deliberately keeps
separate from "parsed successfully". None of this is available today: there
is no writer, and the reader path that would consume its output currently
crashes on a real inspection (see above).

## Related

- Requirements: `doc/02_requirements/feature/simple_unified_debugging_evidence.md`
  (REQ-014 CLI, REQ-015 embedded custom-dump slice, REQ-018 dump-first;
  clearest statement at :39-42).
- Plan: `doc/03_plan/sys_test/simple_unified_debugging_evidence.md` (a test
  matrix, zero task checkboxes).
- Operational contract text: `doc/07_guide/app/lsp_dap/debug_profile_dap.md:98-102`.
- Baremetal crash-slot gap (unimplemented):
  `doc/02_requirements/os/simpleos/simpleos_os_subsystem_feature_requests.md:303`.
- Embedded dump retention (copies an already-captured dump; no transport, no
  parser): `src/os/realtime/jtag/embedded_dump_service_v1.spl:113`
  (`retain_embedded_dump_v1`).
