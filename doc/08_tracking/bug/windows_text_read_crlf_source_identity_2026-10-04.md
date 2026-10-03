# Text reader removes carriage returns from admitted source

Status: runtime regression PASS; rebuilt bootstrap qualification pending.

The Windows native bootstrap producer's Rust runtime `rt_file_read_text`
removed every CR byte after UTF-8 validation. The bounded snapshot reader and
the C runtime preserve those bytes. A CRLF source therefore passed snapshot
admission but failed cold-HIR receipt capture with
`cold-hir-source-content-mismatch`.

Observed with producer SHA-256
`15bea78dd2c07858cbdbb4fc8f5ae9931e282f761729ea614cf793facfe02176`:

| Probe | Snapshot bytes | CRLF pairs | Compiler bytes |
| --- | ---: | ---: | ---: |
| baseline | 87319 | 58 | 87261 |
| candidate | 87464 | 63 | 87401 |

Both snapshots are byte-identical to their authored files. Evidence is retained
under `C:/Users/user/.simple/worktrees/simple/runtime/windows-restart-20261004/workaround-status-probes/`.

Repair: preserve the validated UTF-8 bytes in `rt_file_read_text`, including
CRLF and standalone carriage returns. Consumers interpret newlines; the I/O
provider must not silently change source hashes, lengths, or user data.
No admission check is removed. The runtime regression compares exact bytes and
lengths for initial and cached reads and the RuntimeValue ABI entrypoint.

Validation: `cargo test --offline --release -p simple-runtime --lib
test_file_read_text_preserves_crlf_and_carriage_returns --jobs 40 -- --nocapture`
passed (1 test, 0 failures, 1260 filtered). Log:
`windows-restart-20261004/cranelift-tagging-investigation/exact-text-read-test.log`.

Existing compiler binaries retain their old runtime. Rebuilding the runtime
does not repair those binaries. LF-only performance controls may isolate the
independent ordered-deduplication change, but do not qualify this CRLF repair.
