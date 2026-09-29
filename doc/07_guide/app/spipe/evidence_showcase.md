# Evidence Showcase

`EVIDENCE_SHOWCASE.md` is the project-level proof index. It links each critical
feature to its authoritative generated SSpec manual and links important
subproject showcases when they exist. It aggregates links and status; it does
not duplicate captured artifacts.

## Truth and Status

The curated inventory selects rows and ordering. A validated, versioned
`ScenarioEvidenceManifest` supplies result, provenance, freshness, integrity,
artifact links, and blocker details. Human-authored descriptions may explain a
claim boundary but cannot promote evidence.

Every critical row uses exactly one status:

- `live-pass`: current provenance-bound manifest and required artifacts pass.
- `historical-pass`: retained proof exists but is not current.
- `contract-only`: executable contract exists without live target proof.
- `blocked`: proof is unavailable and includes a prerequisite and resume path.
- `unsupported`: the target or capability is explicitly unsupported.
- `planned`: no executable proof exists yet.

Only a validated current manifest may produce `live-pass`.

## Evidence Forms

- Text: retain bounded raw and normalized transcripts. Ordered matching may
  ignore spacing and declared date/version masks; failures identify the first
  missing or out-of-order line, active policy, and nearby actual lines.
- Still: use SVG or AVIF where suitable and provide alt text or a summary.
  Visual media supplements semantic assertions.
- Motion: use bounded WebP or WebM review media with at least two keyframes, an
  event transcript, and a text fallback.
- HTML: show inert source or a sandboxed artifact plus structured checks.
  Generated pages never execute captured scripts.
- Protocol/crypto: show raw bytes and a decoded offset/bitfield table.
  Highlighted fields also carry textual meaning.

Retained PASS review artifacts live under
`doc/06_spec/image/<spec-relative-path>/`. Ephemeral output and failure detail
remain under `build/test-artifacts/<spec-relative-path>/`.

## Authoring Flow

1. Write or update a modern SSpec under `test/` using `use std.spec.*`,
   `describe`, `it`, `step`, `expect`, and built-in matchers.
2. Assert direct values and fail closed when required evidence is missing.
3. Run the focused scenario so it writes and validates its manifest.
4. Generate its manual with
   `bin/simple spipe-docgen <spec> --output doc/06_spec --no-index`.
5. Review the generated page as an operator without opening the source spec.
6. Refresh the root index with `bin/simple spipe-docgen --showcase`.

Do not add executable `.spl` files under `doc/06_spec/`. Do not hand-edit a
generated PASS or suppress a blocked target. A blocked row must retain target,
prerequisite, exact resume command, artifacts, owner, and final reviewer.

Repository-wide spec-to-SSpec conversion is a later lane. Its generated region
may consume the versioned manifest/oracle contract, but it must preserve manual
tests, emit `pending(...)` for unsupported examples, and fail without writing
when generated markers are malformed or duplicated.
