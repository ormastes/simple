# Reviewed transient source-line evidence

Maintained Markdown should use stable semantic links. A reviewed transient diff or forensics report can retain one original line-link occurrence using an explicit review record. This is an authored implementation contract; runtime qualification is UNRUN.

Pass both `--semantic-exception-file <record.sdn>` and `--semantic-exception-sha256 <reviewed-record-sha256>` to `simple lint <exact-report-path>` or `simple doc check-links/fix-links`. The latter commands still require their existing explicit Markdown/source authority flags. Trusted CI or the operator supplies the digest after review. The loader never derives it from the report or record. Reviewer metadata alone is not authorization, and the tool does not authenticate a review-service identity. An actor able to replace trusted invocation arguments can replace the admitted policy.

The SDN record has exactly these fields (replace the illustrative hashes, path, offsets and review details with reviewed values):

```sdn
version: 1
rule: W-DOC-AST-001
document: "doc/09_report/incident.md"
markdown_sha256: "<64 lowercase hex digits>"
start: 8
end: 24
target: "src/sample.spl:2"
kind: transient-forensics
reason: Preserve source-line evidence from the incident revision
reviewer: compiler-owner
review_reference: incident-review-42
expires_utc: "2026-12-31"
```

`start` and `end` are the shared scanner's zero-based byte offsets, with an exclusive end, and `target` is its exact destination bytes. The example offsets are illustrative; they must match the actual report. `kind` accepts only `transient-diff` or `transient-forensics`. Review descriptions must be nonempty. Expiry is a valid calendar date and remains valid through that UTC day. The document spelling must exactly match the invocation path; paths are never normalized into a broader match. One record permits exactly one occurrence, with no directory or wildcard exemption.

Any change to the report invalidates its grant. A changed record invalidates the trusted pin. Unused, duplicate-key, unknown-field, malformed, expired, overscoped or mismatched grants fail without edits, including when the lint family is configured Allow. Semantic URI errors remain active. Fixes retain exempted bytes and may repair other line links using normal revision authority; the resulting changed report needs a fresh reviewed grant before reusing exception flags. Generic fixes with a grant require a separate edit. No record is automatically repinned.

Bounds: 16 KiB record, 1024 bytes per text field, one grant per input; ordinary lint without exception flags retains its warning/critical behavior. Process-document generation has no review-authority owner and receives no grant.
