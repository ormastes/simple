# GZIP legacy block parser concrete return contract

The actual Phase 3 cycle 6 HIR build rejected `deflate_block_parse` because it returned values without a return annotation. Release f9d07913dcc4ca9623445150c7b8b5e4947610aa still contained that signature. Its success array mixed an integer block kind, boolean final flag, byte array, and integer next offset; a homogeneous array annotation cannot describe those values without erasure.

The parser now returns `DeflateBlockResult?`, with named fields for those four concrete types. Error branches still return nil; stored payloads and fixed/dynamic markers retain their values. The async facade reexports the result type. Existing RFC callers unwrap the optional and inspect named fields, with assertions for all fields and malformed inputs. The old source-text negative-offset test now calls the parser and checks actual failure/success behavior.

STATUS: WARN. Source review and structural checks are recorded separately. Native/interpreter execution is UNRUN while the independent frozen Phase 3 failure collection is active. This patch neither modifies that frozen source nor disables Any diagnostics. NLEN validation, reserved-block policy, and other existing erased helpers are outside this bounded return-contract repair.
