# Network text sessions and ordinary internal UTF8 APIs

Status: source port; all executable scenarios UNRUN. Implements the network portion of the selected UTF8/SOSIX plan and REQ-UTF8-EXTERNAL-TEXT-008. No full host migration or qualification claim.

## Public API and ownership

TcpTextSession.connect(address, codec, timeout_ms) and accept(listener, codec, timeout_ms) create a transport internally. UdpTextSession.bind(address, codec, read_timeout_ms) creates its socket internally. No session factory or helper accepts a caller-owned raw stream/socket/descriptor. Codec metadata is validated before opening/accepting; subsequent timeout/decoder admission errors close the newly created transport. Existing raw descriptor compatibility APIs remain separate and do not attach a session.

The shared immutable TextSessionCodec is consumed unchanged. Public session read/write values are internal text; ExternalFormat, ExternalText and decoder values remain implementation details. TCP read_chunk(size) returns Some(empty) while collecting a scalar/signature, nil only after actual EOF passes decoder.finish; read_text(size) skips incomplete chunks and returns empty at validated EOF. It provides no protocol framing. Malformed/truncated input is latched, so consumed bytes cannot be retried as a fresh frame. Read failure does not silently close the opposite write direction; the caller closes the session explicitly.

TCP validates all output and measures exact wire size before the first send. A successful nonempty encoded write changes subsequent BOM policy to Preserve; subsequent U+FEFF is content. Empty writes preserve the start policy unless Require actually emits a signature. Partial progress advances by the reported count. Transport failure, invalid progress, or allocation failure after partial progress latches the write side; no retry can duplicate a prefix/BOM. Early validation/capacity errors permit corrected input. No network rollback is promised.

UDP treats each datagram as an independent message with fresh BOM policy. It receives the complete AF_INET datagram in a 65535-byte provider buffer, then rejects a configured input-limit violation; a smaller receive buffer would hide truncation. Invalid packets do not contaminate the next packet. Output is capped at min(configured limit,65507) and sent once without splitting. An impossible partial datagram result latches write failure. Empty datagrams are messages, not stream EOF. Closed-session operations, including local_addr, fail before accessing a potentially reused descriptor.

Ordinary class references are intended to share session state. Two real loopback cases close through an alias and check later operations/idempotent close through the original reference. These are UNRUN and do not establish native reference semantics, resource/Isolated move enforcement, clone safety, concurrent access, drop behavior, descriptor reuse, or container escape. No annotation is offered as affine enforcement.

## Existing ordinary and binary APIs

TcpStream text methods now use canonical strict UTF8 conversions. Framed reads consume exact bytes before conversion; the following frame remains untouched. Scalar legacy descriptor helpers preserve their signatures and historical empty/false error shape, but perform strict conversion directly without constructing a temporary owning TcpStream. The prior line-based Content-Length adapter delegates to exact-byte reading and cannot overread a following frame. External wrappers are not added to ordinary API signatures.

Raw binary reads remain bytes. A single binary write copies generic/packed input to a checked packed carrier and performs one send, preserving partial count. write_all uses at most 8192-byte packed windows and advances actual progress. The original TcpSocket implementation is factored into tcp_socket.spl and re-exported at the existing path; consumed methods are explicitly public, and close is a mutable receiver. No new raw-adoption factory is introduced. TCP provider and runtime C code, including the landed no-SIGPIPE implementation, are unchanged.

Legacy read_all/read_text and unbounded line compatibility calls still accumulate until their old stopping conditions; they do not inherit a TextSessionCodec limit. Callers requiring bounded selected encodings must use the owning session APIs. A session limit is per operation/chunk, not a total connection or protocol-frame budget.

## Memory and performance boundaries

The session decoder retains at most three incomplete input bytes. Config limits are 1..16 MiB. Encoding checks internal byte metadata against twice the configured output limit before extraction, validates canonical UTF8, then counts exact UTF16 bytes and required BOM before conversion. It does not build a character array or duplicate scalar decoder. UDP's receive allocation has the fixed provider ceiling even for smaller configured limits.

Logical conversion buffers are O(configured limit); this is not a bound on process RSS, allocator retention, total connection traffic or concurrency. Existing conversion may reserve up to three times input bytes and create multiple temporary copies. Repeated validate creates bounded empty-admission allocations. Session sends also pass through the ordinary packed-write copy, adding another bounded window copy. Worst-case one-byte progress repacks up to 8192 bytes per successful byte; no zero-copy or forced-short-write performance claim is made.

Provider allocation/refcount/OOM, native class/Result and packed-byte ABI, cross-platform behavior, successful short writes and late failure remain execution gates. The landed TCP SIGPIPE correction is preserved as a dependency, not requalified by this source port. No compiler, native helper, tests, benchmarks or doc generator were run.

## Authored evidence

The existing 18 loopback scenarios cover split UTF8/UTF16/BOM/surrogates, truncated EOF, malformed input, forbidden BOM, precise input/output limits, exact bytes, multiple windows, simultaneous encodings, owned factories, closed-session refusal, binary storage and UDP message isolation. Five additional loopback scenarios cover TCP/UDP shared-reference close, exact ordinary NUL/non-BMP framing, invalid ordinary input and pre-send invalid-output rejection followed by valid traffic. Five existing parser/HIR API scenarios cover the actual factory inventory, private fields/aggregate construction and a public factory positive. All 28 are UNRUN. No deterministic late-failure or affine ownership proof is claimed.
