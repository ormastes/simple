import { canonicalJson, freezeDeep, sha256Hex } from "../storage/canonical.js";
import { ARTIFACT_KINDS } from "../model/artifact.js";
import { TRUST_SCOPES, VISIBILITIES, assertCanonicalUid, compareLexical, normalizeCanonicalPath, normalizeEnum, normalizeHash, normalizeSemanticKey } from "../model/identity.js";

/**
 * Read-only deterministic fallback for Wave 8.  This intentionally is not a
 * Leiden or multilevel implementation: it audits a sealed input and emits a
 * virtual-only, proposal-status grouping.  Authority, persistence, refactors,
 * filesystem access, MCP, and physical moves belong to later adapters.
 */
export const REBALANCE_ANALYSIS_V1 = "spipe-rebalance-analysis-v1";

const ROOT_KINDS = new Set(["research", "requirements", "plan", "architecture", "design", "spec", "guide", "tracking", "report"]);
const EDGE_WEIGHTS = Object.freeze({
  trace: 10000, verifies: 9000, covers: 9000, links_to: 8000, contains: 8000,
  classifies_component: 6000, classifies_feature_layer: 5000, lexical: 4000
});
const DEFAULT_CONFIG = Object.freeze({ max_nodes: 10000, max_edges: 100000, max_candidate_edges: 200000, max_edges_per_node: 16, max_cluster_size: 24, lexical_top_k: 8, direct_count_target: 24, direct_count_warning: 32, weights: Object.freeze({ cut: 1, count: 100 }) });

function fail(message) { throw new TypeError(`RebalanceAnalysisV1: ${message}`); }
function integer(value, name, { min = 0, max = Number.MAX_SAFE_INTEGER } = {}) {
  if (!Number.isSafeInteger(value) || value < min || value > max) fail(`${name} must be an integer in [${min}, ${max}]`);
  return value;
}
function plain(value, name) {
  if (!value || typeof value !== "object" || Array.isArray(value) || Object.getPrototypeOf(value) !== Object.prototype) fail(`${name} must be a plain object`);
  return value;
}
function frozen(value, name, seen = new Set()) {
  if (value === null || typeof value !== "object") return;
  if (seen.has(value)) fail(`${name} must not contain cycles`);
  seen.add(value);
  if (!Object.isFrozen(value)) fail(`${name} must be deeply frozen`);
  for (const symbol of Object.getOwnPropertySymbols(value)) fail(`${name} must not contain symbol properties`);
  for (const [key, descriptor] of Object.entries(Object.getOwnPropertyDescriptors(value))) {
    if (Array.isArray(value) && key === "length") continue;
    if (!("value" in descriptor) || descriptor.get || descriptor.set) fail(`${name}.${key} must be immutable data`);
    frozen(descriptor.value, `${name}.${key}`, seen);
  }
  seen.delete(value);
}
function dense(values, name) {
  if (!Array.isArray(values) || !Object.isFrozen(values)) fail(`${name} must be a frozen dense array`);
  const names = Object.getOwnPropertyNames(values);
  if (names.length !== values.length + 1 || names.at(-1) !== "length") fail(`${name} must be dense`);
  return values;
}
function text(value, name, { empty = false } = {}) {
  if (typeof value !== "string" || (!empty && value.length === 0) || value !== value.normalize("NFC") || value.includes("\0")) fail(`${name} must be canonical text`);
  return value;
}
function sortedUnique(values, name) {
  dense(values, name);
  const output = values.map((value, index) => text(value, `${name}[${index}]`));
  if (new Set(output).size !== output.length) fail(`${name} must be unique`);
  return [...output].sort(compareLexical);
}
function snapshot(value) {
  plain(value, "snapshot");
  const uid = text(value.snapshot_uid, "snapshot.snapshot_uid");
  if (!/^spks1-[a-f0-9]{64}$/.test(uid)) fail("snapshot.snapshot_uid must be canonical");
  return uid;
}
function rootFor(artifact) { return ROOT_KINDS.has(artifact.kind) ? artifact.kind : "other"; }
function parentPath(path) { const parts = path.split("/"); return parts.length <= 1 ? "" : parts.slice(0, -1).join("/"); }
function groupKey(artifact) { return `${rootFor(artifact)}\0${artifact.visibility}\0${artifact.trust_scope}\0${artifact.project_uid}`; }
function virtualBase(artifact) { return `view/rebalance/${rootFor(artifact)}/${artifact.visibility}/${artifact.trust_scope}/${artifact.project_uid}`; }
function safeLabel(artifact) {
  const source = artifact.components[0] ?? artifact.features[0] ?? artifact.layers[0] ?? artifact.key ?? artifact.uid;
  const label = source.toLowerCase().replace(/[^a-z0-9]+/g, "-").replace(/^-+|-+$/g, "");
  return label || artifact.uid.toLowerCase();
}

function artifactRecord(value, index) {
  plain(value, `artifacts[${index}]`);
  const uid = assertCanonicalUid(value.uid, `artifacts[${index}].uid`, ["A"]);
  const path = normalizeCanonicalPath(value.canonical_path, `artifacts[${index}].canonical_path`);
  const artifact = {
    uid, key: normalizeSemanticKey(value.key, `artifacts[${index}].key`), canonical_path: path,
    project_uid: assertCanonicalUid(value.project_uid, `artifacts[${index}].project_uid`, ["P"]),
    kind: normalizeEnum(value.kind, ARTIFACT_KINDS, `artifacts[${index}].kind`), visibility: normalizeEnum(value.visibility ?? "project", VISIBILITIES, `artifacts[${index}].visibility`),
    trust_scope: normalizeEnum(value.trust_scope ?? "untrusted_data", TRUST_SCOPES, `artifacts[${index}].trust_scope`),
    features: sortedUnique(value.features ?? Object.freeze([]), `artifacts[${index}].features`),
    components: sortedUnique(value.components ?? Object.freeze([]), `artifacts[${index}].components`),
    layers: sortedUnique(value.layers ?? Object.freeze([]), `artifacts[${index}].layers`),
    protected: value.protected === undefined ? false : (() => {
      if (typeof value.protected !== "boolean") fail(`artifacts[${index}].protected must be boolean`);
      return value.protected;
    })()
  };
  return Object.freeze(artifact);
}
function parseConfig(value) {
  if (value === undefined) return DEFAULT_CONFIG;
  plain(value, "config");
  const weights = value.weights === undefined ? DEFAULT_CONFIG.weights : plain(value.weights, "config.weights");
  const merged = {
    max_nodes: integer(value.max_nodes ?? DEFAULT_CONFIG.max_nodes, "config.max_nodes", { min: 1, max: 100000 }),
    max_edges: integer(value.max_edges ?? DEFAULT_CONFIG.max_edges, "config.max_edges", { min: 1, max: 1000000 }),
    max_candidate_edges: integer(value.max_candidate_edges ?? DEFAULT_CONFIG.max_candidate_edges, "config.max_candidate_edges", { min: 1, max: 2000000 }),
    max_edges_per_node: integer(value.max_edges_per_node ?? DEFAULT_CONFIG.max_edges_per_node, "config.max_edges_per_node", { min: 1, max: 128 }),
    max_cluster_size: integer(value.max_cluster_size ?? DEFAULT_CONFIG.max_cluster_size, "config.max_cluster_size", { min: 1, max: 1000 }),
    lexical_top_k: integer(value.lexical_top_k ?? DEFAULT_CONFIG.lexical_top_k, "config.lexical_top_k", { min: 0, max: 128 }),
    direct_count_target: integer(value.direct_count_target ?? DEFAULT_CONFIG.direct_count_target, "config.direct_count_target", { min: 1, max: 1000 }),
    direct_count_warning: integer(value.direct_count_warning ?? DEFAULT_CONFIG.direct_count_warning, "config.direct_count_warning", { min: 1, max: 1000 }),
    weights: {
      cut: integer(weights.cut ?? DEFAULT_CONFIG.weights.cut, "config.weights.cut", { min: 0, max: 1000000 }),
      count: integer(weights.count ?? DEFAULT_CONFIG.weights.count, "config.weights.count", { min: 0, max: 1000000 })
    }
  };
  if (merged.direct_count_warning < merged.direct_count_target) fail("config.direct_count_warning must be at least direct_count_target");
  return freezeDeep(merged);
}
function canonicalPair(left, right) { return left < right ? `${left}\0${right}` : `${right}\0${left}`; }
/**
 * Rebalancing uses adjacency evidence, not the directed trace semantics of
 * the graph store.  Keep the emitted endpoints in pair order as well as the
 * pair key: otherwise two equivalent accepted edges supplied in reverse
 * directions produce different proposal bytes and break snapshot determinism.
 */
function undirectedEdge(from, to, weight, source) {
  const [left, right] = from < to ? [from, to] : [to, from];
  return { pair: `${left}\0${right}`, from: left, to: right, weight, source };
}
function acceptedEdge(value, index, known) {
  plain(value, `edges[${index}]`);
  const from = assertCanonicalUid(value.from_uid, `edges[${index}].from_uid`);
  const to = assertCanonicalUid(value.to_uid, `edges[${index}].to_uid`);
  if (!known.has(from) || !known.has(to) || from === to) return null;
  if (value.status !== "accepted" || !["explicit", "generated"].includes(value.origin)) return null;
  const type = text(value.edge_type, `edges[${index}].edge_type`);
  const weight = EDGE_WEIGHTS[type];
  if (weight === undefined) return null;
  return undirectedEdge(from, to, weight, `edge:${type}`);
}
function lexicalEdge(value, index, known, lexicalTopK) {
  plain(value, `lexical_top_k[${index}]`);
  const from = assertCanonicalUid(value.from_uid, `lexical_top_k[${index}].from_uid`, ["A"]);
  const to = assertCanonicalUid(value.to_uid, `lexical_top_k[${index}].to_uid`, ["A"]);
  if (!known.has(from) || !known.has(to) || from === to) return null;
  const rank = integer(value.rank, `lexical_top_k[${index}].rank`, { min: 1, max: 1000000 });
  if (rank > lexicalTopK) return null;
  const score = integer(value.score_milli, `lexical_top_k[${index}].score_milli`, { min: 0, max: 1000 });
  const weight = Math.floor((EDGE_WEIGHTS.lexical * score) / 1000);
  return weight === 0 ? null : undirectedEdge(from, to, weight, "lexical");
}
function acceptedLink(value, index, known) {
  plain(value, `links[${index}]`);
  // Link extraction is itself explicit evidence.  When a richer edge-shaped
  // link is supplied, retain the graph authority gate instead of widening it.
  if (value.status !== undefined || value.origin !== undefined) {
    return acceptedEdge({ ...value, edge_type: "links_to" }, index, known);
  }
  const from = assertCanonicalUid(value.from_uid, `links[${index}].from_uid`);
  const to = assertCanonicalUid(value.to_uid, `links[${index}].to_uid`);
  if (!known.has(from) || !known.has(to) || from === to) return null;
  return undirectedEdge(from, to, EDGE_WEIGHTS.links_to, "link:explicit");
}
function classificationEdges(artifacts, candidateBudget) {
  const buckets = new Map();
  let memberships = 0;
  const add = (key, artifact, kind) => {
    memberships += 1; if (memberships > candidateBudget) fail("classification membership budget exceeded");
    const list = buckets.get(`${kind}\0${groupKey(artifact)}\0${key}`) ?? []; list.push(artifact); buckets.set(`${kind}\0${groupKey(artifact)}\0${key}`, list);
  };
  for (const artifact of artifacts) {
    for (const component of artifact.components) add(component, artifact, "component");
    for (const feature of artifact.features) for (const layer of artifact.layers) add(`${feature}\0${layer}`, artifact, "feature_layer");
  }
  const output = []; let candidates = 0;
  for (const [key, entries] of [...buckets.entries()].sort(([a], [b]) => compareLexical(a, b))) {
    const [kind] = key.split("\0"); const ordered = entries.sort((a, b) => compareLexical(a.uid, b.uid));
    for (let i = 0; i < ordered.length; i += 1) for (let j = i + 1; j < ordered.length; j += 1) {
      candidates += 1; if (memberships + candidates > candidateBudget) fail("classification candidate budget exceeded");
      output.push(undirectedEdge(
        ordered[i].uid,
        ordered[j].uid,
        kind === "component" ? EDGE_WEIGHTS.classifies_component : EDGE_WEIGHTS.classifies_feature_layer,
        kind === "component" ? "classification:component" : "classification:feature-layer"
      ));
    }
  }
  return output;
}
function parsePairs(values, name, known) {
  if (values === undefined) return new Set();
  dense(values, name);
  const output = new Set();
  for (let index = 0; index < values.length; index += 1) {
    const value = values[index]; plain(value, `${name}[${index}]`);
    const from = assertCanonicalUid(value.from_uid, `${name}[${index}].from_uid`, ["A"]);
    const to = assertCanonicalUid(value.to_uid, `${name}[${index}].to_uid`, ["A"]);
    if (!known.has(from) || !known.has(to) || from === to) fail(`${name}[${index}] must name distinct inventory artifacts`);
    output.add(canonicalPair(from, to));
  }
  return output;
}
function derivedMirrorPairs(artifacts) {
  const byPath = new Map();
  for (const artifact of artifacts) {
    const key = `${artifact.project_uid}\0${artifact.canonical_path}`;
    if (byPath.has(key)) fail("same-project canonical paths must be unambiguous");
    byPath.set(key, artifact.uid);
  }
  const pairs = new Set();
  for (const artifact of artifacts) if (artifact.canonical_path.startsWith("test/") && artifact.canonical_path.endsWith("_spec.spl")) {
    const manual = `doc/06_spec/${artifact.canonical_path.slice("test/".length).replace(/\.spl$/, ".md")}`;
    const target = byPath.get(`${artifact.project_uid}\0${manual}`);
    if (target) pairs.add(canonicalPair(artifact.uid, target));
  }
  return pairs;
}
function sparseEdges(input, artifacts, config) {
  if (input.constraints !== undefined) plain(input.constraints, "constraints");
  const known = new Set(artifacts.map((artifact) => artifact.uid));
  const cannot = parsePairs(input.constraints?.cannot_link_pairs, "constraints.cannot_link_pairs", known);
  const must = parsePairs(input.constraints?.must_link_pairs, "constraints.must_link_pairs", known);
  const bundles = parsePairs(input.constraints?.protected_bundle_pairs, "constraints.protected_bundle_pairs", known);
  const mirrors = derivedMirrorPairs(artifacts);
  for (const pair of must) if (cannot.has(pair)) fail("constraints cannot contain the same must-link and cannot-link pair");
  for (const pair of [...bundles, ...mirrors]) if (cannot.has(pair)) fail("cannot-link conflicts with a protected bundle or generated mirror");
  dense(input.edges ?? Object.freeze([]), "edges");
  dense(input.links ?? Object.freeze([]), "links");
  dense(input.lexical_top_k ?? Object.freeze([]), "lexical_top_k");
  const rawCandidates = (input.edges ?? []).length + (input.links ?? []).length + (input.lexical_top_k ?? []).length;
  if (rawCandidates > config.max_candidate_edges) fail("aggregate candidate budget exceeded");
  const all = [];
  for (let i = 0; i < (input.edges ?? []).length; i += 1) { const edge = acceptedEdge(input.edges[i], i, known); if (edge) all.push(edge); }
  for (let i = 0; i < (input.links ?? []).length; i += 1) { const edge = acceptedLink(input.links[i], i, known); if (edge) all.push(edge); }
  for (let i = 0; i < (input.lexical_top_k ?? []).length; i += 1) { const edge = lexicalEdge(input.lexical_top_k[i], i, known, config.lexical_top_k); if (edge) all.push(edge); }
  all.push(...classificationEdges(artifacts, Math.max(0, config.max_candidate_edges - rawCandidates)));
  if (all.length > config.max_candidate_edges) fail("candidate edge budget exceeded");
  const byPair = new Map();
  for (const edge of all.sort((a, b) => compareLexical(`${a.pair}\0${a.source}`, `${b.pair}\0${b.source}`))) {
    if (cannot.has(edge.pair)) continue;
    const prior = byPair.get(edge.pair);
    if (!prior) byPair.set(edge.pair, { ...edge, sources: [edge.source] });
    else { prior.weight = Math.min(Number.MAX_SAFE_INTEGER, prior.weight + edge.weight); prior.sources.push(edge.source); }
  }
  const degree = new Map(artifacts.map((artifact) => [artifact.uid, 0]));
  const result = [];
  for (const edge of [...byPair.values()].sort((a, b) => compareLexical(`${String(b.weight).padStart(16, "0")}\0${a.pair}`, `${String(a.weight).padStart(16, "0")}\0${b.pair}`))) {
    if (degree.get(edge.from) >= config.max_edges_per_node || degree.get(edge.to) >= config.max_edges_per_node) continue;
    degree.set(edge.from, degree.get(edge.from) + 1); degree.set(edge.to, degree.get(edge.to) + 1);
    result.push(Object.freeze({ ...edge, sources: Object.freeze([...edge.sources].sort(compareLexical)) }));
    if (result.length > config.max_edges) fail("sparse edge budget exceeded");
  }
  return { edges: result.sort((a, b) => compareLexical(a.pair, b.pair)), must, cannot, bundles, mirrors };
}
class UnionFind {
  constructor(nodes) { this.parent = new Map(nodes.map((node) => [node, node])); this.members = new Map(nodes.map((node) => [node, [node]])); }
  find(node) { let parent = this.parent.get(node); while (parent !== this.parent.get(parent)) parent = this.parent.get(parent); return parent; }
  join(left, right) { const a = this.find(left), b = this.find(right); if (a === b) return a; const winner = a < b ? a : b, loser = a < b ? b : a; this.parent.set(loser, winner); this.members.set(winner, [...this.members.get(winner), ...this.members.get(loser)].sort(compareLexical)); this.members.delete(loser); return winner; }
  group(node) { return this.members.get(this.find(node)); }
}
function conflicting(groups, left, right, cannot) {
  for (const a of left) for (const b of right) if (cannot.has(canonicalPair(a, b))) return true;
  return false;
}
function clustered(artifacts, graph, config) {
  const byUid = new Map(artifacts.map((artifact) => [artifact.uid, artifact]));
  const uf = new UnionFind(artifacts.map((artifact) => artifact.uid));
  const permitted = (a, b) => groupKey(byUid.get(a)) === groupKey(byUid.get(b));
  // Protected bundles are same-boundary hard co-location constraints. Generated
  // test/spec mirrors deliberately remain root-separated: their invariant is
  // that both canonical members remain present and unmodified, which this
  // virtual-only proposal proves with its permanently empty canonical_moves.
  for (const pair of [...new Set([...graph.must, ...graph.bundles])].sort(compareLexical)) {
    const [a, b] = pair.split("\0");
    if (uf.find(a) === uf.find(b)) continue;
    if (!permitted(a, b)) fail("must-link crosses fixed root, visibility, trust, or project boundary");
    if (conflicting(uf, uf.group(a), uf.group(b), graph.cannot)) fail("must-link transitively conflicts with cannot-link");
    if (uf.group(a).length + uf.group(b).length > config.max_cluster_size) fail("must-link exceeds max_cluster_size");
    uf.join(a, b);
  }
  for (const edge of [...graph.edges].sort((a, b) => compareLexical(`${String(b.weight).padStart(16, "0")}\0${a.pair}`, `${String(a.weight).padStart(16, "0")}\0${b.pair}`))) {
    const left = uf.group(edge.from), right = uf.group(edge.to);
    if (left === right || left.length + right.length > config.max_cluster_size || !permitted(edge.from, edge.to) || conflicting(uf, left, right, graph.cannot)) continue;
    uf.join(edge.from, edge.to);
  }
  return [...uf.members.values()].map((members) => members.sort(compareLexical)).sort((a, b) => compareLexical(a[0], b[0]));
}
function costs(artifacts, edges, clusters, config) {
  const clusterFor = new Map(); clusters.forEach((members, index) => members.forEach((uid) => clusterFor.set(uid, index)));
  let cut = 0;
  for (const edge of edges) if (clusterFor.get(edge.from) !== clusterFor.get(edge.to)) cut += edge.weight;
  const direct = clusters.reduce((total, members) => total + Math.max(0, members.length - config.direct_count_target), 0);
  const total = cut * config.weights.cut + direct * config.weights.count;
  if (!Number.isSafeInteger(total)) fail("objective overflow");
  return Object.freeze({ total_milli: total, terms_milli: Object.freeze({ cut: cut * config.weights.cut, direct_count: direct * config.weights.count }) });
}
function oldClusters(artifacts) {
  const grouped = new Map();
  for (const artifact of artifacts) { const key = `${groupKey(artifact)}\0${parentPath(artifact.canonical_path)}`; const members = grouped.get(key) ?? []; members.push(artifact.uid); grouped.set(key, members); }
  return [...grouped.values()].map((members) => members.sort(compareLexical)).sort((a, b) => compareLexical(a[0], b[0]));
}
function proposalClusters(artifacts, clusters) {
  const byUid = new Map(artifacts.map((artifact) => [artifact.uid, artifact]));
  return clusters.map((members) => {
    const first = byUid.get(members[0]); const label = safeLabel(first); const id = `RC-${sha256Hex(canonicalJson({ contract: REBALANCE_ANALYSIS_V1, root: groupKey(first), members })).slice(0, 26).toUpperCase()}`;
    return Object.freeze({ uid: id, label, root: rootFor(first), visibility: first.visibility, trust_scope: first.trust_scope, project_uid: first.project_uid,
      members: Object.freeze([...members]), virtual_path: `${virtualBase(first)}/${label}--${id.slice(3).toLowerCase()}` });
  }).sort((a, b) => compareLexical(a.uid, b.uid));
}
function metrics(artifacts, config) {
  const directories = new Map();
  for (const artifact of artifacts) {
    const path = parentPath(artifact.canonical_path);
    // Canonical paths are project-relative.  Never merge same-spelled paths
    // from separate projects into one balance metric.
    const key = `${artifact.project_uid}\0${path}`;
    const entry = directories.get(key) ?? { project_uid: artifact.project_uid, path, count: 0 };
    entry.count += 1;
    directories.set(key, entry);
  }
  const depths = artifacts.map((artifact) => artifact.canonical_path.split("/").length - 1);
  const test_spec_pairs = derivedMirrorPairs(artifacts).size;
  return Object.freeze({ artifacts: artifacts.length, directories: directories.size, max_depth: depths.length ? Math.max(...depths) : 0,
    protected_artifacts: artifacts.filter((artifact) => artifact.protected).length, test_spec_pairs,
    direct_count_warning_directories: [...directories.values()].filter((entry) => entry.count > config.direct_count_warning).length,
    direct_counts: Object.freeze(
      [...directories.entries()]
        .sort(([a], [b]) => compareLexical(a, b))
        .map(([, entry]) => Object.freeze({ ...entry }))
    ) });
}

/** Analyze one caller-supplied sealed snapshot and emit virtual-only proposals. */
export function analyzeRebalanceV1(input) {
  plain(input, "input"); frozen(input, "input");
  const snapshot_uid = snapshot(input.snapshot);
  const config = parseConfig(input.config);
  dense(input.artifacts, "artifacts");
  if (input.artifacts.length > config.max_nodes) fail("node budget exceeded");
  const artifacts = input.artifacts.map(artifactRecord).sort((a, b) => compareLexical(a.uid, b.uid));
  if (new Set(artifacts.map((artifact) => artifact.uid)).size !== artifacts.length) fail("artifact UIDs must be unique");
  const graph = sparseEdges(input, artifacts, config);
  const clusters = clustered(artifacts, graph, config);
  const old_cost = costs(artifacts, graph.edges, oldClusters(artifacts), config);
  const new_cost = costs(artifacts, graph.edges, clusters, config);
  const config_hash = normalizeHash(`sha256:${sha256Hex(canonicalJson(config))}`, "config_hash");
  const result = {
    type: "rebalance_analysis", schema_version: 1, contract: REBALANCE_ANALYSIS_V1, snapshot_uid, config_hash,
    analysis: Object.freeze({ metrics: metrics(artifacts, config), edges: Object.freeze(graph.edges), algorithm: "deterministic_components_greedy_bounded_v1", omitted_capabilities: Object.freeze(["leiden", "multilevel_partitioning", "local_refinement", "physical_moves", "depth_objective", "protected_path_objective"])}),
    proposal: Object.freeze({ type: "rebalance_proposal", schema_version: 1, status: "proposed", scope: "virtual_only", physical_apply: false,
      canonical_moves: Object.freeze([]), rollback_map: Object.freeze([]), clusters: Object.freeze(proposalClusters(artifacts, clusters)),
      old_cost_milli: old_cost.total_milli, new_cost_milli: new_cost.total_milli, objective: Object.freeze({ old: old_cost, next: new_cost }),
      constraints: Object.freeze({ fixed_roots: true, trust_visibility_project_isolation: true, must_link_pairs: graph.must.size, cannot_link_pairs: graph.cannot.size,
        protected_bundle_pairs: graph.bundles.size, generated_test_spec_pairs: graph.mirrors.size, canonical_paths_preserved: true,
        root_preserved_mirrors: Object.freeze([...graph.mirrors].sort(compareLexical).map((pair) => Object.freeze({ pair, invariant: "canonical_members_preserved_without_move" }))) }) })
  };
  return freezeDeep(result);
}

export const RebalanceAnalysisV1 = analyzeRebalanceV1;
