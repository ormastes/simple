# Strict host text codec prerequisite

Status: source port and real regression specs; execution UNRUN. Runtime qualification and all end-to-end host/session acceptance remain open.

The codec accepts only explicit utf-8, utf-16le and utf-16be labels. It strictly validates complete input, reports structured code/byte_offset/reason errors, preserves NUL and treats a declared-endian BOM as ordinary content. Unknown metadata is rejected first. It never guesses, replaces malformed sequences or performs IO. Raw binary identity remains separate. Legacy i64 byte arrays keep full-container invalid-byte preflight before scalar decoding; canonical u8 spans validate selected regions only.

The shared core decodes scalar locals and writes one selected output carrier; it does not allocate a whole scalar intermediate array or widen canonical byte arrays. Validation-only populates no output array. The reusable unicode_scalar_valid predicate checks scalar range without constructing char; existing unicode_scalar_to_char code is preserved exactly. This small predicate is the only added scalar dependency.

HostTextByteSpanV1 logically concatenates prefix (at most three bytes) and bytes without copying; [start,end) selects the validated region. Error offsets are absolute logical indices; truncation reports end. host_text_span_byte_v1 is an unchecked accessor requiring a validated span/index. Incomplete sequences fail; incremental carry/BOM policy belongs to future external-text/session owners.

Canonical output uses checked text_byte_buffer with capacity at most three times selected input length; arithmetic checks leave room for the existing 40-byte header. Metadata/byte preflight precedes allocation; output capacity/allocation failure precedes scalar decoding. The runtime's own smaller allocation cap remains authoritative. Resource errors map to capacity_overflow/-1 or buffer_allocation/-1. No allocation-free or measured RSS/performance claim is made.

Regression specs cover scalar limits, exact endian surrogate bytes, NUL/BOM, malformed and overlong UTF-8, lone/malformed UTF-16 surrogates, invalid integer bytes, metadata precedence, selected spans, prefix boundaries, empty ranges and absolute error positions. The packed allocator/extraction specs additionally assert physical byte basis and provider failures. Native caller raw/tagged u8 ABI, exact linked providers and all authored assertions remain UNRUN under the existing exhausted qualification campaign; source-reviewed landing does not reset it.
