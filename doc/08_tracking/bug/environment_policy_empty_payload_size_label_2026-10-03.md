# Empty policy payload reported as oversized

The policy handoff encoder and decoder rejected both an empty Base64 argument
and an argument exceeding 22,000 bytes with `Oversized`. The application owner
preserved that reason in its error label. Consequently, an encoder returning no
bytes could produce `policy-encoding-failed:oversized` even though the payload
was empty. An existing owner regression explicitly preserved this misleading
label for an empty caller argument.

The repair returns the existing `InvalidValue` reason for an empty encoded
argument, in both directions. Positive size limits, rejection behavior,
canonical checks, digest checks and UTF-8 validation are unchanged. The existing
owner regression now expects `invalid-internal-argument:invalid-value`; a typed
decoder regression distinguishes empty input from an argument of 22,001 bytes.

This diagnostic repair does not establish which condition failed in the old
Windows Cranelift candidate `340b3599731d4e16a23679a83bf3723ef0f19f94730f1b9abe5621c831daa198`.
That candidate uses source `78d5a1cd7768f70cc42a56888ef3a799823bd738`, predating
the separate linear byte-copy repair. Read-only matching against retained COFF
objects locates its encoder at `0x14048544d` and confirms that the linked wire
limit is initialized to 16,384 bytes. Actual failing branch and byte lengths
remain under independent diagnostic investigation; no limit increase is justified.

Validation: source and caller review passed. A focused 40-worker Cranelift
bootstrap diagnostic compiled 55 modules (55 fresh, zero reused or failed) and
executed five real oracles: empty decoder reason, 22,001-byte decoder reason,
empty owner-attachment reason, exact owner error label, and continued rejection
of corrupt Base64. Output: `empty-payload-regression:checks=5:failures=0`.

Evidence is retained at
`C:/Users/user/.simple/worktrees/simple-windows-phase2/build/native_probe/policy-empty-payload-regression1`.
The F177 producer and requested R777 runtime inputs were pinned before and
after the run. This entry-closure diagnostic uses the CoreC bootstrap runtime;
it does not reproduce the old full candidate's runtime composition. Native
build, executable and outer collector exited zero. Mandatory RSS monitoring
completed with peak 1,307,340 KiB below the 5,859,375 KiB cap, quiescent=1 and
observer_errors=0. The 45-byte runtime log has SHA-256
`261f7470979c6bce77cb5d4bc44903e12707accf00a032ad4613cd85830926ac`;
the 5,360,115-byte outer log has SHA-256
`a4745f4f037bcd6a78b0ae1ed03662636c12b3a9eef678e5f5e2d497960276a5`.
Both match their bounded collector receipts. Executable SHA-256 remained
`737c1db5b133ffddf2ecaa9e064a31724921bf0b668515f0c9b05ba25082616e`.
The executable collector recorded one residual job member (PID 26576,
unavailable identity) and applied job termination after the zero child exit;
the outer collector recorded no remnants. Independent inspection found neither
that PID nor supervisor PID 29960 nor another process in this diagnostic lane
remaining afterward.

The added checked-in SSpec cases remain unrun; these five native oracles are
focused bootstrap evidence. They do not force a defective encoder to return
empty output, so the encoder's empty-result branch is source-reviewed rather
than dynamically covered. Full compiler/core/MCP checks and Phase 2
qualification remain pending. This change alone does not make the old candidate
able to compile a program.
