# Checked boxed-text byte extraction prerequisite

Status: source port with actual API regression specs authored; execution UNRUN. This prerequisite does not add external-text objects or host/file/network sessions.

The native extractor can return a failed array when allocation fails. The canonical common/text_bytes.boxed_text_bytes_checked reads existing str_len byte metadata before extraction, checks supported capacity, calls the existing extractor once, then verifies the existing array data pointer and exact byte count. text_byte_extraction_checked is the production deterministic guard, also exercised with deliberately short/long arrays. The mismatch oracle is not allocator fault injection or OOM execution evidence.

The helper is encoding-neutral: malformed bytes and UTF-16 zero bytes remain payload for a later explicit charset declaration. Existing primitive wrapper bodies remain unchanged. TextByteBufferError distinguishes NegativeCapacity, CapacityOverflow and AllocationFailed. text_byte_buffer allocates empty packed storage through the existing rt_byte_array_new provider and validates its data pointer; the runtime may impose a stricter capacity limit, represented as AllocationFailed.

Native source evidence: runtime_native.c rt_string_len returns boxed RtCoreString.len; rt_text_to_bytes copies that byte count; rt_array_data_ptr returns backing pointer or zero. Successful empty arrays have minimum storage capacity. The landed pure-Simple packed-array repair supplies byte-aware push/get/set/operations, but its native qualification remains FAIL_UNQUALIFIED. Generated u8 call ABI and actual provider identity are still acceptance gates.

The scoped boxed_text_extraction_spec.spl checks multibyte UTF-8, empty, embedded NUL, deterministic short/long mismatch, range rejection and malformed raw bytes against production helpers. Its donor's external-text/session scenarios are deferred with those unlanded modules. Every byte oracle compares exact logical length and ordered bytes, without assuming array equality. No interpreter fallback is authorized: native packed layout and byte-exact raw carrier behavior require their own admitted execution.

Supported compilation, real allocation-failure injection, final text materialization failure, allocation/RSS measurements and other provider ABI qualification remain open. This establishes source dataflow, not measured performance or universal allocation safety.
