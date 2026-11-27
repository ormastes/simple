# Nested SDN integer value changes on native diagnostic producer

Status: OPEN, report-only (not registered in bug_db). Proposed severity P1.
Observed on release/1.0.0 with unadmitted pure-Simple LLVM/core-c-bootstrap
compiler afae09d224390a57d675a128a052626c3aa665c032481928332ebdc2859d7350,
aarch64 Linux. Parser source versus native codegen attribution is not proven.

Expected `{spec: {maximumJournalEvents: 10000}}` to retain integer10000.
Observed nested parse returns1000. Larger HostConfig also returns1000 with/without
source spans. HostConfig source-tail check was true for10000}}. Identity, CPU2000,
memory4Gi, arrays and interval100 controls passed. HostConfig copies the already
wrong raw parser value. Equality against10000 fails; this is not formatting alone.

Reduced controls all return10000: literal bytes[49,48,48,48,48], text_to_bytes,
sdn_integer_from_span_v1, scalar parse("10000") and parse("{value: 10000}").
Small and full two-level mappings return1000; span collection is not required.
Reproducer: test/fixtures/compiler/sdn_integer_span_native_probe.spl.
Evidence: build/orchestrator-toolchain-20261107/sdn-integer-span/build-v2.log,
run-v2.log, source.sha256 and snapshot.sdn. HostConfig evidence is in sibling
host-config/build-v4.log and run-v4.log. Builds exit0; final runtimes exit1.
Current source hashes are retained. Check snapshot.sdn: unavailable shared SCV
snapshots cannot be retroactively claimed as matching current source.

Six-cycle cause budget exhausted: four HostConfig diagnostics localized failure;
fifth scalar/one-level reduction passed; sixth nested reduction failed. No semantic
fix applied. Require explicit revised budget or independently supplied fix/toolchain
before continuing this cause; do not reset via rename/worktree/continuation. Do
not relax expected values or change numeric config to strings to hide the failure.

## Independent literal-integrity diagnosis — 2026-11-07

Astra SDN and its Sol source-review worker inspected the retained executable
without rerunning any exhausted diagnostic. SHA-256 remains
`68279d1263e0cc7634ca0c8b9825c7f74e58b69a91dc8b3c7610c24664ff2861`.
At ELF file offset `0x1780`, the small source literal is 36 bytes and ends
with bytes `[49, 48, 48, 48, 48, 125]`, whereas the fixture source requires
37 bytes ending `[49, 48, 48, 48, 48, 125, 125]`. The full HostConfig
literal likewise has only one final closing brace. This is static data in
the original failing executable, not a new failure run.

The previous source-tail comparison is not independent evidence of compiled
input correctness: its expected ordinary literal can undergo the same brace
escape decoding. The earlier numeric result is real, but does not prove a
well-formed nested SDN input was truncated by integer parsing or MIR payload
ownership. The original report above is retained as historical evidence.

Both pure-Simple frontend owners compute rewritten text that protects rejected
interpolation regions, then mistakenly discard it in the no-placeholder path:
`convert_nodes.spl` decodes `str_val` instead of `str_regions_val`, and
`string_interpolation_expand.spl` decodes `value` instead of `rewritten`.
Thus adjacent closing braces inside a rejected SDN expression region collapse
as though they were explicit brace escapes. The repair decodes the protected
representation; deliberate doubled escapes and real interpolation retain their
existing behavior. No claim is made that the retained producer's full build
snapshot is reconstructed from the current checkout.

Separately, the SDN inline readers removed delimiters without checking balance.
The missing closer therefore led the second reader to discard the final digit.
The public parser now checks the existing delimiter-depth scanner before inline
reader dispatch and rejects incomplete/mismatched delimiters and non-delimiter
suffix text. This is structural validation, not a numeric-string workaround.
The additional scan is linear per collection; no performance improvement is
claimed.

Regression sources:
- `test/fixtures/compiler/sdn_nested_literal_integrity.spl`: ordinary source
  literal length and numeric byte oracle precede exact integer assertions.
- `flat_bridge_string_scan_spec.spl`: actual flat AST conversion and deliberate
  doubled-escape control, using independently constructed expected braces.
- `pure_simple_frontend_interpolation_promotion_spec.spl`: core frontend AST
  literal integrity and doubled-escape control; valid interpolation retained.
- `sdn_inline_collection_delimiters_spec.spl`: malformed nested input, mismatch,
  extra closer, trailing text, quoted delimiters, numeric10000 and span API.

The old six-cycle numerical-cause budget remains exhausted. Root authorized a
new bounded literal-defect lane based on this independent static evidence.
Source review is complete; runtime verification and toolchain admission are
not established by this note. No Rust seed qualification is used.
