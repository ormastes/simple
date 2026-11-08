# source_open unchecked request ID exceeds response budget

Status: source repair authored; verification waiting.

Release base `9e7e7a526edb43ab29171d920449367e5fd48127`, owner blob `6d3adb2238990be1220e757edc42e2d1b58832b6`: source_bounded_response_v1 checks successful wire size then echoes the same unbounded ID into its error fallback. The handler's early errors also echo it. An 18002-byte serialized ID therefore exceeds the 16 KiB ceiling even when the request is refused. This reproduction is source reasoning, not an executed protocol result.

Extracted provenance: unfinished PR7265 head `dd3444e346d436ab9bb1a3b5dc8e91e5a9a1b47e`, adapter blob `f320c8798e705bc3f61703bb79c7b4ec92a5a5ad`, already contains scalar ID admission and canonical null-ID errors. This narrow adaptation keeps the released raw owner and uses canonical str_len for the 128-byte serialized ceiling; it does not import the unlanded shared service or authenticated adapters.

ID admission runs before handler processing and at the public bounded-response/private error seams. Null/string/integer/fraction IDs remain accepted; malformed/boolean/array/object/oversized IDs get canonical -32600 errors with null ID. Direct source_open_contract_spec scenarios assert exact/adjacent byte limits, multibyte non-echo and actual parsed successful/error/fallback/body-limit envelopes.

Runtime, docgen and final-source protocol/performance evidence: NOT_RUN. Broad VIEW/SEC requirements remain open. No dedicated numeric ID-boundary ledger was found in the retained review map; this does not reset historical source-auth/static3, publication/source-authority9 or nativeFS6 limits. Current extraction review repair cycle1 replaces the private make_error import with the existing exported make_error_response wrapper. It preserves canonical null/-32600 behavior without widening provider exports or changing visibility baselines.
