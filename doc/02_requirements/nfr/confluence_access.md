# Confluence access nonfunctional requirements

* Offline acceptance uses synthetic tokens and file fixtures; no real accounts or live writes.
* No retry or additional subprocess is added to a request. Source review verifies the single existing `process_run` call.
* Error diagnostics mask credential assignments; successful page content is not altered by diagnostic redaction.
* Phase1 evidence must name the actual executable and invocation route; interpreter evidence must not be described as native compilation.
