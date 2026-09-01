import assert from "node:assert/strict";
import test from "node:test";
import { readFileSync } from "node:fs";
import { contentHash, deepFreeze } from "../../src/model/identity.js";
import { analyzePromotionCandidatesV1, PROMOTION_CANDIDATE_ANALYSIS_CONTRACT } from "../../src/promote/candidate_analysis.js";

const p = (letter) => `P-${letter.repeat(26)}`;
const a = (letter) => `A-${letter.repeat(26)}`;
const s = (letter) => `spks1-${letter.toLowerCase().repeat(64)}`;
function artifact(uid, normalized, { visibility = "public", status = "approved", features = ["search"], components = ["index"], layers = ["core"] } = {}) {
  return { uid, key: `key.${uid.slice(-1).toLowerCase()}`, title: `Title ${uid.slice(-1)}`, content_hash: contentHash(normalized), normalized_text: normalized, visibility, status, features, components, layers };
}
function snapshot(snapshot_uid, project_uid, artifacts, visibility = "public") { return { snapshot_uid, project_uid, revision: "rev-1", visibility, artifacts }; }
function request(snapshots, more = {}) { return deepFreeze({ workspace_uid: "W-00000000000000000000000000", authorization_scope_digest: "sha256:0000000000000000000000000000000000000000000000000000000000000000", snapshots, max_candidates_per_artifact: 2, minimum_shingle_jaccard_millionths: 100_000, cross_project_public_only: true, ...more }); }

test("promotion candidates are deterministic evidence only, with exact and bounded shingle results", () => {
  const first = deepFreeze(snapshot(s("a"), p("A"), [artifact(a("A"), "shared stable knowledge for search index"), artifact(a("B"), "search index lexical score ranking") ]));
  const second = deepFreeze(snapshot(s("b"), p("B"), [artifact(a("C"), "shared stable knowledge for search index"), artifact(a("D"), "different subject entirely") ]));
  const input = request(deepFreeze([first, second]));
  const one = analyzePromotionCandidatesV1(input), two = analyzePromotionCandidatesV1(input);
  assert.deepEqual(one, two);
  assert.equal(one.contract, PROMOTION_CANDIDATE_ANALYSIS_CONTRACT);
  assert.equal(one.writes_performed, 0); assert.equal(one.accepted_count, 0); assert.equal(one.promoted_count, 0);
  const exact = one.candidates.find((candidate) => candidate.source.artifact_uid === a("A") && candidate.related.artifact_uid === a("C"));
  assert.equal(exact.evidence.exact_normalized_hash, true); assert.equal(exact.accepted, false); assert.equal(exact.promoted, false);
  assert.ok(one.candidates.every((candidate) => candidate.evidence.shingle_jaccard_millionths >= 100_000 || candidate.evidence.lexical_top_k_rank !== null));
  assert.ok(one.candidates.filter((candidate) => candidate.source.artifact_uid === a("A")).length <= 2);
  assert.equal(Object.isFrozen(one), true);
});

test("cross-project non-public artifacts are denied without leaking candidates, while conflicts are reported", () => {
  const left = deepFreeze(snapshot(s("c"), p("C"), [artifact(a("E"), "same protected knowledge", { visibility: "private", status: "approved", features: ["alpha"] })]));
  const right = deepFreeze(snapshot(s("d"), p("D"), [artifact(a("F"), "same protected knowledge", { status: "stale", features: ["beta"] })]));
  const denied = analyzePromotionCandidatesV1(request(deepFreeze([left, right]), { minimum_shingle_jaccard_millionths: 0 }));
  assert.equal(denied.candidates.length, 0); assert.equal(denied.denied_cross_project_pairs, 0);
  const publicLeft = deepFreeze(snapshot(s("e"), p("E"), [artifact(a("G"), "same public knowledge", { status: "approved", features: ["alpha"] })]));
  const publicRight = deepFreeze(snapshot(s("f"), p("F"), [artifact(a("H"), "same public knowledge", { status: "stale", features: ["beta"] })]));
  const reported = analyzePromotionCandidatesV1(request(deepFreeze([publicLeft, publicRight]), { minimum_shingle_jaccard_millionths: 0 }));
  assert.ok(reported.candidates[0].conflicts.includes("status_mismatch"));
  assert.ok(reported.candidates[0].conflicts.includes("features_disjoint"));
});

test("analysis refuses mutable data, invalid content binding, and unbounded candidate policy", () => {
  const mutable = { workspace_uid: "W-00000000000000000000000000", authorization_scope_digest: "sha256:0000000000000000000000000000000000000000000000000000000000000000", snapshots: [], max_candidates_per_artifact: 1, minimum_shingle_jaccard_millionths: 0, cross_project_public_only: true };
  assert.throws(() => analyzePromotionCandidatesV1(mutable), /deeply frozen/);
  const broken = deepFreeze(snapshot(s("a"), p("A"), [{ ...artifact(a("A"), "one"), content_hash: contentHash("two") }]));
  assert.throws(() => analyzePromotionCandidatesV1(request(deepFreeze([broken]))), /must hash normalized_text/);
  assert.throws(() => analyzePromotionCandidatesV1(request(deepFreeze([]), { max_candidates_per_artifact: 101 })), /1\.\.100/);
});

test("snapshot order is canonical and lexical-only same-snapshot matches remain read-only evidence", () => {
  const one = deepFreeze(snapshot(s("a"), p("A"), [artifact(a("A"), "first lexical heading"), artifact(a("B"), "second lexical heading")]));
  const two = deepFreeze(snapshot(s("b"), p("B"), [artifact(a("C"), "unrelated isolated material")]));
  const forward = analyzePromotionCandidatesV1(request(deepFreeze([one, two]), { minimum_shingle_jaccard_millionths: 1_000_000 }));
  const reverse = analyzePromotionCandidatesV1(request(deepFreeze([two, one]), { minimum_shingle_jaccard_millionths: 1_000_000 }));
  assert.deepEqual(forward, reverse);
  assert.ok(forward.candidates.some((candidate) => candidate.evidence.lexical_top_k_rank !== null && candidate.evidence.shingle_jaccard_millionths < 1_000_000));
  assert.ok(forward.source_reports.every((report) => typeof report.visibility === "string" && typeof report.snapshot_visibility === "string"));
});

test("bounded pools exclude self, retain a late exact match, and report incomplete evidence", () => {
  const id = (index) => `A-${String(index).padStart(26, "0")}`;
  const entries = [artifact(id(0), "common canonical exact material")];
  for (let index = 1; index <= 64; index += 1) entries.push(artifact(id(index), `common canonical exact variant-${index}`));
  entries.push(artifact(id(65), "common canonical exact material"));
  const input = request(deepFreeze([deepFreeze(snapshot(s("a"), p("A"), entries))]), { max_candidates_per_artifact: 100, minimum_shingle_jaccard_millionths: 1 });
  const result = analyzePromotionCandidatesV1(input);
  const source = id(0), exact = id(65);
  const report = result.source_reports.find((entry) => entry.artifact_uid === source);
  const sourceCandidates = result.candidates.filter((entry) => entry.source.artifact_uid === source);
  assert.equal(report.candidate_pool_complete, false); assert.equal(report.candidate_pool_examined, 64);
  assert.equal(sourceCandidates.length, 64); assert.equal(sourceCandidates[0].related.artifact_uid, exact);
});

test("candidate analysis has no authority, persistence, publication, or remote semantic surface", () => {
  const source = readFileSync(new URL("../../src/promote/candidate_analysis.js", import.meta.url), "utf8");
  assert.doesNotMatch(source, /node:(?:fs|child_process|net|http|https)/);
  assert.doesNotMatch(source, /\b(?:publish|persist|writeFile|appendFile|rename|promote|accept|embedding|semantic|simhash|minhash|extends|promoted_from)\s*\(/i);
  assert.match(source, /writes_performed: 0/);
});
