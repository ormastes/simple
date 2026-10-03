# Confluence access findings

Baseline: release/1.0 commit `0d722af3d62e3b693af8bef475cf227d7f55d69e`.

* `adapter_confluence.confluence_search_cql` escaped quotes in the title only; backslashes and quoted space values could alter CQL structure.
* `_json_str` serialized a decoded JSON value and removed outer quotes, returning escaped quotes/newlines in storage HTML.
* `_parse_results` considered a JSON object without `results` successful, masking response-shape errors.
* `_confluence_request` redacted curl stderr but returned HTTP failure bodies unredacted.
* `config.resolve_auth_token` selected a named target and then silently fell back to the default provider's credentials.

Reuse: `std.json.json_to_string`, existing diagnostic redaction, `load_auth_token_from`, and canonical `ItfConfig`. No alternate Confluence backend or JSON parser is introduced. Domain research is unnecessary for these source-proven defects; routing behavior is covered by existing gateway specs.
