# Windows Docker broker binary protocol foundation

This source supplies framing and bounded progress state for the future actual
broker/session consumer. It creates no process, pipe, grant, reader or effect
capability. Windows execution and all authored specifications are **NOT_RUN**.

The binary envelope reuses `process_frame_codec`: Parent/Process, Copy,
EncodedCopy, ownership token zero, source not invalidated. The retained parent
Job lease supplies region `slot + 1` with checked positive arithmetic and its
actual generation. The broker must obtain the expected correlation from its
authenticated startup context; it must never learn it from the first frame.
The child stdio lease has an independent generation. No PID becomes an identity
or capability, and envelope checksums provide integrity only.

Payloads are at most 65536 bytes: an explicit eight-byte metadata length,
canonical SDN metadata at most 4096 bytes, then raw body bytes at most 61432.
Only metadata uses UTF8; body bytes never pass through text or hex conversion.
The incremental reader checks the fixed header and advertised bounds before
allocating payload storage, consumes at most one frame, and leaves coalesced
trailing bytes with the caller. Invalid framing is sticky; EOF with a partial
frame is an error. Large output is split into ordered bounded chunks.

Input, geometry and progress carry the existing target/control correlation:
target digest, control kind, revision, nonce digest, frame sequence and immutable
payload digest/geometry. They do not encode a new lease or the nonserialized
common admission carrier. A progress reply must match the retained frame before
advancing its accepted prefix. Stale-prefix requests receive progress only;
uncertain outcomes freeze the channel without resend. Native write attempt
sequence remains separate in the actual native barrier.

Output has its own sequence and per-channel byte offsets. The output tracker
runs after the existing sole logical reader. TTY output admits only the merged
TTY channel; non-TTY output tracks stdout and stderr independently. End-of-stream
means stream EOF, never workload exit, containment teardown or charge release.

Actual positive integration still requires the completed Windows installation
and lower access factory, independent protected broker metadata reopening,
verified Host delegation and one-use effect continuation, authenticated ongoing
parent control projections, and the native revision/nonce/expiry/attempt barrier.
The GET-only Engine exchange remains guarded. A successful parse, NewFrame or
ContinueFrame disposition grants no permission to submit bytes to the Engine.
