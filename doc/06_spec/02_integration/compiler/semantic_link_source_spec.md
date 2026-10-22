# Parsed-source semantic links specification

Authored companion; execution and docgen UNRUN.

Executable: `test/02_integration/compiler/semantic_link_source_spec.spl`. Requirements: REQ-MC-008 / B2-URI, B2-SOURCE, B2-IDENTITY, B2-REVISION.

The scenarios create actual temporary source files and invoke the production checked parser, B1 identity/index and resolver. No metadata-only or mocked source provider is used.

1. **should parse a real file and round-trip both selected URI forms through B1.** The executable asserts the production identity/location or exact typed refusal.
2. **should refuse an incorrect requested revision before indexing.** The executable asserts the production identity/location or exact typed refusal.
3. **should refuse missing revision and invalid package authority.** The executable asserts the production identity/location or exact typed refusal.
4. **should refuse a package-qualified URI for another package.** The executable asserts the production identity/location or exact typed refusal.
5. **should refuse disk edits after a snapshot was published.** The executable asserts the production identity/location or exact typed refusal.
6. **should keep identity but refresh location after a body and line change.** The executable asserts the production identity/location or exact typed refusal.
7. **should reject the old fingerprint when a signature changes.** The executable asserts the production identity/location or exact typed refusal.
8. **should not use a valid fingerprint to resolve a different declaration name.** The executable asserts the production identity/location or exact typed refusal.
9. **should refuse two parsed declarations claiming the same stable identity.** The executable asserts the production identity/location or exact typed refusal.
10. **should discriminate overload identities using the supplied fingerprint.** The executable asserts the production identity/location or exact typed refusal.
11. **should refuse real parsed identities colliding at the existing B1 test seam.** The executable asserts the production identity/location or exact typed refusal.
12. **should copy declaration facts before another parse replaces the arena.** The executable asserts the production identity/location or exact typed refusal.
13. **should reject malformed source rather than publish an empty success.** The executable asserts the production identity/location or exact typed refusal.
14. **should refuse generic unresolved and inferred signatures explicitly.** The executable asserts the production identity/location or exact typed refusal.
15. **should reject unsupported kinds through a typed resolver result.** The executable asserts the production identity/location or exact typed refusal.
16. **should reject noncanonical URI syntax without fallback.** The executable asserts the production identity/location or exact typed refusal.
17. **should refuse a file larger than the provider byte bound.** The executable asserts the production identity/location or exact typed refusal.
18. **should refuse a missing file instead of trusting a prior declaration.** The executable asserts the production identity/location or exact typed refusal.

19. **should refuse conditional source transformations without an original span map.** The executable asserts the production identity/location or exact typed refusal.

20. **should map both declaration spans to original UTF8 bytes before header lexing.** The executable asserts the production identity/location or exact typed refusal.

21. **should refuse collapsed integer type spellings instead of manufacturing i64 identity.** The executable asserts the production identity/location or exact typed refusal.

22. **should refuse richer headers until exact source provenance is implemented.** The executable asserts the production identity/location or exact typed refusal.

23. **should refuse oversized formatter results using the shared URI admission.** The executable asserts the production identity/location or exact typed refusal.

For accepted signature scope, package configuration ownership, revision behavior, parser/caching limitations and unrun performance evidence see `doc/05_design/semantic_link_parsed_source_v1.md`. Full B2 remains open.
