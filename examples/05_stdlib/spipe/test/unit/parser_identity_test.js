import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import { resolve } from "node:path";

import {
  buildIdentityIndex,
  planUidInjection,
  planUidInjections,
  proposedArtifactUid,
  resolveIdentity,
} from "../../src/core/identity.js";
import {
  parseMarkdownArtifact,
  parseSdnDocument,
  parseSspecMetadata,
  parseSourceMetadata,
} from "../../src/parser/index.js";

const fixture = (name) => readFileSync(new URL(`../fixture/wave2_parser/${name}`, import.meta.url), "utf8");

test("Markdown parser preserves artifact metadata and stable section markers", () => {
  const parsed = parseMarkdownArtifact(fixture("artifact_marked.md"), {
    path: "doc/05_design/search/core.md",
    projectUid: "P-simple",
    revision: "r1",
  });
  assert.equal(parsed.artifact.uid, "A-00000000000000000000000000000001");
  assert.equal(parsed.artifact.key, "design.search.core");
  assert.deepEqual(parsed.artifact.features, ["search", "project_knowledge"]);
  assert.equal(parsed.sections.length, 2);
  assert.equal(parsed.sections[0].uid, "S-00000000000000000000000000000001");
  assert.equal(parsed.sections[0].identity_status, "authoritative");
  assert.equal(parsed.sections[1].identity_status, "provisional");
  assert.equal(parsed.sections[0].artifact_uid, parsed.artifact.uid);
  assert.throws(() => { parsed.artifact.key = "changed"; }, TypeError);
});

test("unmarked Markdown gets provisional identity and deterministic dry-run injection", () => {
  const parsed = parseMarkdownArtifact(fixture("artifact_unmarked.md"), { path: "doc/01_research/note.md", projectUid: "P-simple" });
  assert.match(parsed.artifact.uid, /^P-P-simple-[0-9a-f]{64}$/);
  assert.equal(parsed.artifact.identity_status, "provisional");
  const first = planUidInjection(parsed);
  const second = planUidInjections(parsed);
  assert.deepEqual(first, second);
  assert.equal(first[0].canonical_mutation, false);
  assert.match(first[0].insertion, /spipe:artifact uid=A-[0-9a-f]{32}/);
  assert.ok(first.some((item) => item.kind === "section_uid"));
});

test("SDN subset handles nested maps, sequences, inline values, and duplicate keys", () => {
  const parsed = parseSdnDocument(fixture("metadata.sdn"));
  assert.equal(parsed.value.artifact.uid, "A-02");
  assert.deepEqual(parsed.value.artifact.aliases, ["search-core", "bm25"]);
  assert.deepEqual(parsed.value.artifact.features, ["search", "knowledge"]);
  const duplicate = parseSdnDocument("a: 1\na: 2\n");
  assert.equal(duplicate.diagnostics[0].code, "SPK003");
});

test("SSpec parser extracts artifact, scenario, requirements, suites, and stable metadata", () => {
  const parsed = parseSspecMetadata(fixture("scenarios.spl"), { path: "test/03_system/search_spec.spl", projectUid: "P-simple" });
  assert.equal(parsed.artifact.uid, "T-00000000000000000000000000000001");
  assert.equal(parsed.artifact.kind, "sspec");
  assert.equal(parsed.suites[0].title, "Search compiler");
  assert.equal(parsed.scenarios.length, 2);
  assert.equal(parsed.scenarios[0].uid, "SS-00000000000000000000000000000001");
  assert.deepEqual(parsed.scenarios[0].requirement_ids, ["REQ-SPKC-011"]);
  assert.equal(parsed.scenarios[1].identity_status, "provisional");
});

test("source metadata parser extracts symbols, spans, annotations, and provisional fallback", () => {
  const parsed = parseSourceMetadata(fixture("source.spl"), { path: "src/search/index.spl", projectUid: "P-simple" });
  assert.equal(parsed.symbols.length, 2);
  assert.equal(parsed.symbols[0].uid, "SY-00000000000000000000000000000001");
  assert.deepEqual(parsed.symbols[0].requirement_ids, ["REQ-SPKC-011"]);
  assert.equal(parsed.symbols[1].identity_status, "provisional");
  assert.ok(parsed.symbols[1].signature_hash.startsWith("sha256:"));
  assert.ok(parsed.symbols[0].definition_span.end_byte > parsed.symbols[0].definition_span.start_byte);
});

test("identity index rejects duplicate UIDs and ambiguous aliases without guessing", () => {
  const first = parseMarkdownArtifact("<!-- spipe:artifact uid=A-1 key=one aliases=[shared] -->\n# One\n", { path: "a.md", projectUid: "P" });
  const duplicate = parseMarkdownArtifact("<!-- spipe:artifact uid=A-1 key=duplicate -->\n# Duplicate\n", { path: "duplicate.md", projectUid: "P" });
  const second = parseMarkdownArtifact("<!-- spipe:artifact uid=A-2 key=two aliases=[shared] -->\n# Two\n", { path: "b.md", projectUid: "P" });
  const index = buildIdentityIndex([first, duplicate, second]);
  assert.ok(index.diagnostics.some((item) => item.code === "SPK001"));
  assert.ok(index.diagnostics.some((item) => item.code === "SPK002"));
  assert.equal(resolveIdentity(index, "shared").status, "ambiguous");
  assert.equal(index.resolve("missing").status, "not_found");
  assert.throws(() => { index.by_uid["A-1"] = []; }, TypeError);
});

test("proposed artifact UID is stable for the same explicit proposal tuple", () => {
  const args = { projectUid: "P-simple", canonicalPath: "doc/a.md", contentHash: "sha256:abc" };
  assert.equal(proposedArtifactUid(args), proposedArtifactUid(args));
  assert.match(proposedArtifactUid(args), /^A-[0-9a-f]{32}$/);
});
