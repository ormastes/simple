# Selected abstract/external text requirements

Selection provenance: the user explicitly requested the full abstraction, separate external encoded types, physical UTF-8 internal Char, metadata-bearing I/O, strict transcode ingress and symmetric output. No new choice is required. Unchosen option drafts are not retained.

| ID | Selected behavior | Foundation evidence |
|---|---|---|
| REQ-001 | AbstractChar/AbstractText are trait contracts; Char/Text alias the existing primitives; their traits provide typed strict conversions without changing physical layout. | Generic internal/external text and char SSpec scenarios; native fixture. |
| REQ-002 | Typed Encoding, TextByteOrder and BOM policy admit supported combinations; unknown/ambiguous metadata fails before payload decoding. | Metadata admission/label scenarios. |
| REQ-003 | ExternalChar represents exactly one encoded Unicode scalar, excluding an explicitly required transport signature. | Single/empty/multiple/surrogate/BOM character scenarios. |
| REQ-004 | ExternalText retains owned encoded bytes; internal conversion strictly produces UTF-8 or an error with input-byte provenance. | Invalid UTF-8/UTF-16/truncation and BOM-offset scenarios. |
| REQ-005 | Output explicitly transcodes to the destination encoding and symmetric BOM policy; embedded NUL survives. | UTF-16 roundtrip, Char egress, BOM policy scenarios. |
| REQ-006 | External payloads have owned copies and copying accessors; raw binary remains byte APIs. | Aliasing scenario; I/O lane raw-binary regressions. |
| REQ-007 | Incremental decoder emits complete scalars, retains bounded partial input, reports absolute offsets, rejects unfinished EOF, and latches its first failure. | Split UTF-8/UTF-16/BOM, finish/failure/close scenarios. |

Physical Char's four-byte packed UTF-8 implementation and ABI migration belong to the char lane. File/TCP/SOSIX actual read/write migration belongs to the I/O lanes. Those gates are necessary for whole-feature completion and are not replaced by this foundation's evidence.

The optional bounded output cache is deferred: no measured repeated-encoding workload currently justifies a cache. This does not defer required conversion behavior. Compiler-enforced inaccessible ExternalChar constructors require a negative privacy gate; every conversion revalidates regardless.

## Whole-feature host boundary ledger

REQ-008: selected host boundaries must retain typed external encoding/order metadata inside SOSIX or explicit conversion owners and perform strict conversion on ingress and symmetric encoding on egress. Ordinary public file/network/session APIs expose internal UTF-8 text; typed external values are exposed only by explicitly selected codec/compatibility APIs. File, TCP and SOSIX migrations are owned by the corresponding implementation lanes. Environment, argv, subprocess output/input, console and path surfaces require an explicit migration or unsupported-status ledger; they are **open integration work**, not silently excluded by this foundation's seven requirement tests. Raw binary remains bytes. The root owns the complete host inventory and overall acceptance.

The public abstract contracts have actual generic-bound acceptors in executable specs/native fixtures and actual primitive/external implementations. Alias spelling alone is not completion. Safe internal text entry requires strict conversion; unchecked raw C/runtime text providers remain trusted/unsafe boundary mechanisms and must not be advertised as newly validated universal host APIs.

## Current-base source port, 2026-10-19

This is the foundation slice of `doc/03_plan/utf8_internal_sosix_plan.md`.
REQ-001/004/005 support UTF8-SOSIX-01/03/05; REQ-002/003/005 and BOM-only admission support UTF8-SOSIX-02; REQ-007 supports UTF8-SOSIX-04. These are source/spec mappings, not completed acceptance marks. UTF8-SOSIX-06/07/08 need actual resource adapters; UTF8-SOSIX-09/10 need memory/performance and admitted executable evidence. All execution is UNRUN for this port. The physical Char lane's prior three attempts remain counted toward the user-authorized six-attempt maximum; this foundation introduces no layout or compiler repair.
