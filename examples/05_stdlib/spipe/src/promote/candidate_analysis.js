import { contentHash, deepFreeze, normalizeHash, compareLexical, assertCanonicalUid } from "../model/identity.js";
import { SnapshotLexicalSearchV1 } from "../search/snapshot_lexical.js";

/**
 * Read-only, bounded discovery of possible reusable knowledge.  A result is
 * deliberately evidence, not a common-knowledge object: this module has no
 * publication, graph, alias, filesystem, provider, or authority dependency.
 */
export const PROMOTION_CANDIDATE_ANALYSIS_CONTRACT = "spipe-promotion-candidate-analysis-v1";

const SNAPSHOT = /^spks1-[a-f0-9]{64}$/;
const UID = /^A-[A-Z0-9]{26}$/;
const VISIBILITY = new Set(["public", "project", "private", "restricted"]);
const STATUS = new Set(["draft", "proposed", "approved", "implemented", "verified", "stale", "deprecated"]);
const MAX_SNAPSHOTS = 64;
const MAX_ARTIFACTS = 10_000;
const MAX_TOTAL_ARTIFACTS = 10_000;
const MAX_BUCKET_MEMBERS = 64;
const MAX_TEXT_BYTES = 64 * 1024;
const MAX_TOKENS = 512;
const MAX_SHINGLES = 256;

function fail(message) { throw new TypeError(`PromotionCandidateAnalysisV1: ${message}`); }
function plain(value, label) {
  if (!value || typeof value !== "object" || Array.isArray(value) || Object.getPrototypeOf(value) !== Object.prototype) fail(`${label} must be a plain object`);
  return value;
}
function fields(value, names, label) {
  plain(value, label);
  const actual = Object.getOwnPropertyNames(value);
  if (Object.getOwnPropertySymbols(value).length || actual.length !== names.length || actual.some((name, index) => name !== names[index])) fail(`${label} fields must be closed and ordered`);
  for (const name of names) {
    const descriptor = Object.getOwnPropertyDescriptor(value, name);
    if (!descriptor || !("value" in descriptor) || descriptor.get || descriptor.set) fail(`${label}.${name} must be data`);
  }
  return value;
}
function frozen(value, label, seen = new Set()) {
  if (value === null || typeof value !== "object") return;
  if (seen.has(value)) fail(`${label} must not contain cycles`);
  if (!Object.isFrozen(value)) fail(`${label} must be deeply frozen`);
  seen.add(value);
  for (const key of Reflect.ownKeys(value)) {
    if (typeof key === "symbol") fail(`${label} cannot have symbols`);
    const descriptor = Object.getOwnPropertyDescriptor(value, key);
    if (descriptor.get || descriptor.set) fail(`${label}.${key} must be data`);
    frozen(descriptor.value, `${label}.${key}`, seen);
  }
  seen.delete(value);
}
function text(value, label, max = 4096) {
  if (typeof value !== "string" || value.length === 0 || value !== value.normalize("NFC") || /[\u0000-\u001f\u007f]/u.test(value) || Buffer.byteLength(value, "utf8") > max) fail(`${label} must be bounded NFC text`);
  return value;
}
function list(value, label) {
  if (!Array.isArray(value) || !Object.isFrozen(value)) fail(`${label} must be a frozen array`);
  return value;
}
function sortedUnique(values, label) {
  const output = list(values, label).map((value, index) => text(value, `${label}[${index}]`));
  for (let index = 1; index < output.length; index += 1) if (compareLexical(output[index - 1], output[index]) >= 0) fail(`${label} must be sorted and unique`);
  return output;
}
function normalizeDocument(value) {
  return text(value, "artifact.normalized_text", MAX_TEXT_BYTES).toLowerCase().replace(/\s+/gu, " ").trim();
}
function tokens(normalized) {
  return normalized.match(/[\p{L}\p{N}_-]+/gu)?.slice(0, MAX_TOKENS) ?? [];
}
function shingles(normalized) {
  const words = tokens(normalized);
  const out = new Set();
  for (let index = 0; index < words.length && out.size < MAX_SHINGLES; index += 1) {
    out.add(words.slice(index, index + 3).join("\u0001"));
  }
  return out;
}
function jaccard(left, right) {
  let intersection = 0;
  for (const item of left) if (right.has(item)) intersection += 1;
  const union = left.size + right.size - intersection;
  return union === 0 ? 0 : Math.floor((intersection * 1_000_000) / union);
}
function artifact(value, snapshot) {
  fields(value, ["uid", "key", "title", "content_hash", "normalized_text", "visibility", "status", "features", "components", "layers"], "PromotionArtifactV1");
  if (!UID.test(value.uid)) fail("artifact.uid must be a canonical artifact UID");
  text(value.key, "artifact.key"); text(value.title, "artifact.title");
  const normalized = normalizeDocument(value.normalized_text);
  if (!VISIBILITY.has(value.visibility)) fail("artifact.visibility is invalid");
  if (!STATUS.has(value.status)) fail("artifact.status is invalid");
  const hash = normalizeHash(value.content_hash, "artifact.content_hash");
  if (contentHash(normalized) !== hash) fail("artifact.content_hash must hash normalized_text");
  return Object.freeze({ uid: value.uid, key: value.key, title: value.title, content_hash: hash, visibility: value.visibility, status: value.status, features: sortedUnique(value.features, "artifact.features"), components: sortedUnique(value.components, "artifact.components"), layers: sortedUnique(value.layers, "artifact.layers"), project_uid: snapshot.project_uid, revision: snapshot.revision, snapshot_uid: snapshot.snapshot_uid, normalized, shingles: shingles(normalized) });
}
function snapshot(value) {
  fields(value, ["snapshot_uid", "project_uid", "revision", "visibility", "artifacts"], "PromotionSnapshotV1");
  if (!SNAPSHOT.test(value.snapshot_uid)) fail("snapshot.snapshot_uid must be canonical");
  if (!/^P-[A-Z0-9]{26}$/.test(value.project_uid)) fail("snapshot.project_uid must be canonical");
  text(value.revision, "snapshot.revision");
  if (!VISIBILITY.has(value.visibility)) fail("snapshot.visibility is invalid");
  const artifacts = list(value.artifacts, "snapshot.artifacts").map((entry) => artifact(entry, value));
  if (artifacts.length > MAX_ARTIFACTS) fail("snapshot.artifacts exceeds bound");
  const ids = new Set();
  for (const entry of artifacts) { if (ids.has(entry.uid)) fail("snapshot contains duplicate artifact UID"); ids.add(entry.uid); }
  return Object.freeze({ snapshot_uid: value.snapshot_uid, project_uid: value.project_uid, revision: value.revision, visibility: value.visibility, artifacts: Object.freeze(artifacts) });
}
function visible(from, to, policy) {
  if (from.project_uid === to.project_uid) return true;
  return policy.cross_project_public_only && from.visibility === "public" && to.visibility === "public" && from.snapshot_visibility === "public" && to.snapshot_visibility === "public";
}
function conflict(left, right) {
  const reasons = [];
  if (left.status !== right.status) reasons.push("status_mismatch");
  for (const field of ["features", "components", "layers"]) {
    const a = new Set(left[field]), b = new Set(right[field]);
    if (a.size && b.size && ![...a].some((item) => b.has(item))) reasons.push(`${field}_disjoint`);
  }
  return reasons;
}
function lexicalScore(left, right) {
  const a = new Set(tokens(`${left.key} ${left.title}`));
  const b = new Set(tokens(`${right.key} ${right.title}`));
  return jaccard(a, b);
}
function lexicalRanksBySnapshot(snapshots, workspaceUid, scopeDigest) {
  const ranks = new Map();
  for (const snapshotEntry of snapshots) {
    const searchable = snapshotEntry.artifacts;
    if (searchable.length === 0) continue;
    const inventory = deepFreeze({ snapshot: { snapshot_uid: snapshotEntry.snapshot_uid }, artifacts: searchable.map((entry) => ({
    uid: entry.uid, key: entry.key, aliases: [], title: entry.title, kind: "guide", status: entry.status,
    features: entry.features, components: entry.components, layers: entry.layers, project_uid: entry.project_uid
    })) });
    const search = new SnapshotLexicalSearchV1({ workspace_uid: workspaceUid, snapshot_uid: snapshotEntry.snapshot_uid, authorization_scope_digest: scopeDigest, inventory });
    for (const entry of searchable) {
      const hits = search.search({ query_text: entry.title, limit: 100 }).hits;
      ranks.set(entry.uid, new Map(hits.map((hit) => [hit.uid, hit.source_rank])));
    }
  }
  return ranks;
}
function candidateBuckets(ordered) {
  const buckets = new Map();
  function add(key, index) {
    const bucket = buckets.get(key) ?? [];
    bucket.push(index); buckets.set(key, bucket);
  }
  ordered.forEach((entry, index) => {
    add(`p\0${entry.project_uid}\0h\0${entry.content_hash}`, index);
    for (const shingle of entry.shingles) add(`p\0${entry.project_uid}\0s\0${shingle}`, index);
    if (entry.visibility === "public" && entry.snapshot_visibility === "public") {
      add(`x\0h\0${entry.content_hash}`, index);
      for (const shingle of entry.shingles) add(`x\0s\0${shingle}`, index);
    }
  });
  return buckets;
}
function stableCandidate(left, right, shingleScore, lexicalScoreMilli, lexicalTopKRank, conflicts) {
  return deepFreeze({
    source: Object.freeze({ project_uid: left.project_uid, revision: left.revision, snapshot_uid: left.snapshot_uid, artifact_uid: left.uid, content_hash: left.content_hash, visibility: left.visibility, snapshot_visibility: left.snapshot_visibility }),
    related: Object.freeze({ project_uid: right.project_uid, revision: right.revision, snapshot_uid: right.snapshot_uid, artifact_uid: right.uid, content_hash: right.content_hash, visibility: right.visibility, snapshot_visibility: right.snapshot_visibility }),
    evidence: Object.freeze({ exact_normalized_hash: left.content_hash === right.content_hash, shingle_jaccard_millionths: shingleScore, lexical_title_jaccard_millionths: lexicalScoreMilli, lexical_top_k_rank: lexicalTopKRank, normalized_text_hashes: Object.freeze([left.content_hash, right.content_hash].sort(compareLexical)) }),
    conflicts: Object.freeze(conflicts),
    disposition: "candidate_only",
    accepted: false,
    promoted: false
  });
}
function candidateOrder(left, right) {
  for (const [a, b] of [
    [left.evidence.exact_normalized_hash ? 1 : 0, right.evidence.exact_normalized_hash ? 1 : 0],
    [left.evidence.shingle_jaccard_millionths, right.evidence.shingle_jaccard_millionths]
  ]) if (a !== b) return b - a;
  const leftRank = left.evidence.lexical_top_k_rank ?? Number.MAX_SAFE_INTEGER;
  const rightRank = right.evidence.lexical_top_k_rank ?? Number.MAX_SAFE_INTEGER;
  if (leftRank !== rightRank) return leftRank - rightRank;
  return compareLexical(`${left.related.project_uid}\0${left.related.artifact_uid}`, `${right.related.project_uid}\0${right.related.artifact_uid}`);
}

/** Takes immutable caller data and returns immutable analysis only; it writes nothing. */
export function analyzePromotionCandidatesV1(input) {
  fields(input, ["workspace_uid", "authorization_scope_digest", "snapshots", "max_candidates_per_artifact", "minimum_shingle_jaccard_millionths", "cross_project_public_only"], "PromotionCandidateAnalysisRequestV1");
  frozen(input, "request");
  const snapshotInputs = list(input.snapshots, "snapshots");
  if (snapshotInputs.length > MAX_SNAPSHOTS) fail("snapshots exceeds bound");
  let declaredArtifacts = 0;
  for (const entry of snapshotInputs) { fields(entry, ["snapshot_uid", "project_uid", "revision", "visibility", "artifacts"], "PromotionSnapshotV1"); declaredArtifacts += list(entry.artifacts, "snapshot.artifacts").length; }
  if (declaredArtifacts > MAX_TOTAL_ARTIFACTS) fail("total artifacts exceeds bounded analysis capacity");
  if (!Number.isSafeInteger(input.max_candidates_per_artifact) || input.max_candidates_per_artifact < 1 || input.max_candidates_per_artifact > 100) fail("max_candidates_per_artifact must be 1..100");
  if (!Number.isSafeInteger(input.minimum_shingle_jaccard_millionths) || input.minimum_shingle_jaccard_millionths < 0 || input.minimum_shingle_jaccard_millionths > 1_000_000) fail("minimum_shingle_jaccard_millionths must be 0..1000000");
  if (input.cross_project_public_only !== true) fail("cross_project_public_only must be true");
  const workspaceUid = assertCanonicalUid(input.workspace_uid, "workspace_uid", ["W"]);
  const scopeDigest = normalizeHash(input.authorization_scope_digest, "authorization_scope_digest");
  const snapshots = snapshotInputs.map(snapshot).sort((a, b) => compareLexical(`${a.project_uid}\0${a.revision}\0${a.snapshot_uid}`, `${b.project_uid}\0${b.revision}\0${b.snapshot_uid}`));
  const ids = new Set();
  const all = snapshots.flatMap((entry) => entry.artifacts.map((artifactEntry) => Object.freeze({ ...artifactEntry, snapshot_visibility: entry.visibility })));
  for (const entry of all) { if (ids.has(entry.uid)) fail("artifact UID must be unique across snapshot inputs"); ids.add(entry.uid); }
  const ordered = [...all].sort((a, b) => compareLexical(`${a.project_uid}\0${a.uid}`, `${b.project_uid}\0${b.uid}`));
  const indexByUid = new Map(ordered.map((entry, index) => [entry.uid, index]));
  const bucketIndex = candidateBuckets(ordered);
  const lexicalRanks = lexicalRanksBySnapshot(snapshots, workspaceUid, scopeDigest);
  const candidates = [];
  const sourceReports = [];
  let deniedCrossProjectPairs = 0;
  for (let index = 0; index < ordered.length; index += 1) {
    const source = ordered[index], local = [];
    const nearby = new Set(bucketIndex.get(`p\0${source.project_uid}\0h\0${source.content_hash}`) ?? []);
    for (const shingle of source.shingles) for (const otherIndex of bucketIndex.get(`p\0${source.project_uid}\0s\0${shingle}`) ?? []) nearby.add(otherIndex);
    if (source.visibility === "public" && source.snapshot_visibility === "public") {
      for (const otherIndex of bucketIndex.get(`x\0h\0${source.content_hash}`) ?? []) nearby.add(otherIndex);
      for (const shingle of source.shingles) for (const otherIndex of bucketIndex.get(`x\0s\0${shingle}`) ?? []) nearby.add(otherIndex);
    }
    const lexical = lexicalRanks.get(source.uid) ?? new Map();
    for (const relatedUid of lexical.keys()) { const otherIndex = indexByUid.get(relatedUid); if (otherIndex !== undefined) nearby.add(otherIndex); }
    const candidateIndexes = [...nearby].filter((otherIndex) => index !== otherIndex).sort((left, right) => left - right);
    for (const otherIndex of candidateIndexes) {
      const related = ordered[otherIndex];
      if (!visible(source, related, input)) { if (source.project_uid !== related.project_uid) deniedCrossProjectPairs += 1; continue; }
      const exact = source.content_hash === related.content_hash;
      const shingleScore = exact ? 1_000_000 : jaccard(source.shingles, related.shingles);
      const lexicalScoreMilli = lexicalScore(source, related);
      const lexicalTopKRank = lexical.get(related.uid) ?? null;
      if (!exact && shingleScore < input.minimum_shingle_jaccard_millionths && lexicalTopKRank === null) continue;
      local.push(stableCandidate(source, related, shingleScore, lexicalScoreMilli, lexicalTopKRank, conflict(source, related)));
    }
    local.sort(candidateOrder);
    const selected = local.slice(0, MAX_BUCKET_MEMBERS);
    candidates.push(...selected.slice(0, input.max_candidates_per_artifact));
    sourceReports.push(Object.freeze({ project_uid: source.project_uid, revision: source.revision, snapshot_uid: source.snapshot_uid, artifact_uid: source.uid, visibility: source.visibility, snapshot_visibility: source.snapshot_visibility, candidate_pool_complete: local.length <= MAX_BUCKET_MEMBERS, candidate_pool_examined: selected.length }));
  }
  // `ordered` is canonical by source and each local list is quality-ranked;
  // retain that order so a caller can consume the bounded evidence in rank order.
  return deepFreeze({ contract: PROMOTION_CANDIDATE_ANALYSIS_CONTRACT, workspace_uid: workspaceUid, authorization_scope_digest: scopeDigest, analyzed_snapshots: Object.freeze(snapshots.map((entry) => Object.freeze({ snapshot_uid: entry.snapshot_uid, project_uid: entry.project_uid, revision: entry.revision, visibility: entry.visibility }))), candidates: Object.freeze(candidates), source_reports: Object.freeze(sourceReports), denied_cross_project_pairs: deniedCrossProjectPairs, accepted_count: 0, promoted_count: 0, writes_performed: 0 });
}
