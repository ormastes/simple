import assert from "node:assert/strict";
import test from "node:test";

import { deepFreeze } from "../../src/model/identity.js";
import { analyzeRebalanceV1 } from "../../src/rebalance/index.js";

const SNAPSHOT = `spks1-${"a".repeat(64)}`;
const P = "P-01K3R8G3N70ZMT43W6QJ7YHX4P";
const P2 = "P-01K3R8G3N70ZMT43W6QJ7YHX4Q";
const A = [
  "A-01K3R8G3N70ZMT43W6QJ7YHX4P",
  "A-01K3R8G3N70ZMT43W6QJ7YHX4Q",
  "A-01K3R8G3N70ZMT43W6QJ7YHX4R",
  "A-01K3R8G3N70ZMT43W6QJ7YHX4S"
];

function artifact(uid, path, overrides = {}) {
  return {
    uid, key: `design.search.${uid.slice(-1).toLowerCase()}`, canonical_path: path, project_uid: P,
    kind: "design", visibility: "project", trust_scope: "reviewed_reference",
    features: ["search"], components: ["std.common.search"], layers: ["ranking"], ...overrides
  };
}
function fixture(overrides = {}) {
  return {
    snapshot: { snapshot_uid: SNAPSHOT },
    artifacts: [artifact(A[0], "doc/05_design/search/a.md"), artifact(A[1], "doc/05_design/search/b.md"), artifact(A[2], "doc/05_design/search/c.md"), artifact(A[3], "doc/05_design/other/d.md", { components: ["std.common.other"], features: ["other"] })],
    edges: [{ from_uid: A[0], to_uid: A[1], edge_type: "links_to", status: "accepted", origin: "explicit" }],
    links: [], lexical_top_k: [{ from_uid: A[1], to_uid: A[2], rank: 1, score_milli: 700 }],
    constraints: { must_link_pairs: [], cannot_link_pairs: [] },
    config: { max_cluster_size: 3, lexical_top_k: 2 }, ...overrides
  };
}
function sealed(value) { return deepFreeze(value); }

test("read-only fallback audits sealed snapshots and emits only virtual proposed paths", () => {
  const input = sealed(fixture());
  const before = JSON.stringify(input);
  const result = analyzeRebalanceV1(input);
  assert.equal(JSON.stringify(input), before, "analysis must not mutate the caller inventory");
  assert.equal(result.type, "rebalance_analysis");
  assert.equal(result.proposal.status, "proposed");
  assert.equal(result.proposal.scope, "virtual_only");
  assert.equal(result.proposal.physical_apply, false);
  assert.deepEqual(result.proposal.canonical_moves, []);
  assert.deepEqual(result.proposal.rollback_map, []);
  assert.equal(result.analysis.algorithm, "deterministic_components_greedy_bounded_v1");
  assert.ok(result.analysis.omitted_capabilities.includes("leiden"));
  assert.ok(result.proposal.clusters.every((cluster) => cluster.virtual_path.startsWith("view/rebalance/design/")));
  assert.ok(Object.isFrozen(result));
});

test("the same sealed logical graph is byte-deterministic despite input order", () => {
  const first = analyzeRebalanceV1(sealed(fixture()));
  const second = analyzeRebalanceV1(sealed(fixture({
    artifacts: [artifact(A[3], "doc/05_design/other/d.md", { components: ["std.common.other"], features: ["other"] }), artifact(A[2], "doc/05_design/search/c.md"), artifact(A[1], "doc/05_design/search/b.md"), artifact(A[0], "doc/05_design/search/a.md")],
    edges: [{ from_uid: A[1], to_uid: A[0], edge_type: "links_to", status: "accepted", origin: "explicit" }],
    lexical_top_k: [{ from_uid: A[2], to_uid: A[1], rank: 1, score_milli: 700 }]
  })));
  assert.deepEqual(second, first);
});

test("undirected accepted evidence serializes identically when endpoints are reversed", () => {
  const forward = analyzeRebalanceV1(sealed(fixture({
    links: [{ from_uid: A[0], to_uid: A[1] }],
    edges: [{ from_uid: A[1], to_uid: A[2], edge_type: "links_to", status: "accepted", origin: "explicit" }],
    lexical_top_k: [{ from_uid: A[2], to_uid: A[3], rank: 1, score_milli: 700 }]
  })));
  const reverse = analyzeRebalanceV1(sealed(fixture({
    links: [{ from_uid: A[1], to_uid: A[0] }],
    edges: [{ from_uid: A[2], to_uid: A[1], edge_type: "links_to", status: "accepted", origin: "explicit" }],
    lexical_top_k: [{ from_uid: A[3], to_uid: A[2], rank: 1, score_milli: 700 }]
  })));
  assert.deepEqual(reverse, forward);
  for (const edge of forward.analysis.edges) assert.ok(edge.from < edge.to);
});

test("fixed root, visibility, trust, project, cannot-link, and bounded-size constraints are preserved", () => {
  const result = analyzeRebalanceV1(sealed(fixture({
    artifacts: [
      artifact(A[0], "doc/05_design/search/a.md"), artifact(A[1], "doc/05_design/search/b.md"),
      artifact(A[2], "doc/01_research/search/c.md", { kind: "research" }),
      artifact(A[3], "doc/05_design/search/d.md", { visibility: "private" })
    ],
    edges: [
      { from_uid: A[0], to_uid: A[1], edge_type: "links_to", status: "accepted", origin: "explicit" },
      { from_uid: A[0], to_uid: A[2], edge_type: "links_to", status: "accepted", origin: "explicit" },
      { from_uid: A[0], to_uid: A[3], edge_type: "links_to", status: "accepted", origin: "explicit" }
    ],
    constraints: { must_link_pairs: [], cannot_link_pairs: [{ from_uid: A[0], to_uid: A[1] }] },
    config: { max_cluster_size: 1, lexical_top_k: 0 }
  })));
  assert.equal(result.proposal.clusters.length, 4);
  for (const cluster of result.proposal.clusters) assert.equal(cluster.members.length, 1);
  assert.equal(result.proposal.constraints.fixed_roots, true);
  assert.equal(result.proposal.constraints.trust_visibility_project_isolation, true);
});

test("metamorphic unrelated additions do not alter existing cluster membership", () => {
  const base = analyzeRebalanceV1(sealed(fixture({ artifacts: [artifact(A[0], "doc/05_design/search/a.md"), artifact(A[1], "doc/05_design/search/b.md")], lexical_top_k: [] })));
  const extended = analyzeRebalanceV1(sealed(fixture({ artifacts: [artifact(A[0], "doc/05_design/search/a.md"), artifact(A[1], "doc/05_design/search/b.md"), artifact(A[3], "doc/01_research/other/d.md", { kind: "research", components: ["other"], features: ["other"] })], lexical_top_k: [] })));
  const memberSet = (result, uid) => result.proposal.clusters.find((cluster) => cluster.members.includes(uid)).members;
  assert.deepEqual(memberSet(extended, A[0]), memberSet(base, A[0]));
});

test("protected entries and mirrored executable/spec pairs are inventoried without canonical relocation", () => {
  const testArtifact = artifact(A[0], "test/03_system/app/spipe/feature/rebalance_spec.spl", { kind: "test", protected: true });
  const manualArtifact = artifact(A[1], "doc/06_spec/03_system/app/spipe/feature/rebalance_spec.md", { kind: "spec", protected: true });
  const result = analyzeRebalanceV1(sealed(fixture({ artifacts: [testArtifact, manualArtifact], edges: [], lexical_top_k: [] })));
  assert.equal(result.analysis.metrics.protected_artifacts, 2);
  assert.equal(result.analysis.metrics.test_spec_pairs, 1);
  assert.equal(result.proposal.clusters.length, 2, "protected entries retain stable singleton virtual placement");
  assert.deepEqual(result.proposal.canonical_moves, []);
});

test("transitive must-link/cannot-link conflicts, generated mirrors, and protected bundles fail closed", () => {
  const common = [artifact(A[0], "doc/05_design/search/a.md"), artifact(A[1], "doc/05_design/search/b.md"), artifact(A[2], "doc/05_design/search/c.md")];
  assert.throws(() => analyzeRebalanceV1(sealed(fixture({ artifacts: common, edges: [], lexical_top_k: [], constraints: {
    must_link_pairs: [{ from_uid: A[0], to_uid: A[1] }, { from_uid: A[1], to_uid: A[2] }], cannot_link_pairs: [{ from_uid: A[0], to_uid: A[2] }]
  } }))), /transitively conflicts/);
  const testArtifact = artifact(A[0], "test/03_system/app/spipe/feature/rebalance_spec.spl", { kind: "test" });
  const manualArtifact = artifact(A[1], "doc/06_spec/03_system/app/spipe/feature/rebalance_spec.md", { kind: "spec" });
  assert.throws(() => analyzeRebalanceV1(sealed(fixture({ artifacts: [testArtifact, manualArtifact], edges: [], lexical_top_k: [], constraints: {
    must_link_pairs: [], cannot_link_pairs: [{ from_uid: A[0], to_uid: A[1] }], protected_bundle_pairs: []
  } }))), /generated mirror/);
  assert.throws(() => analyzeRebalanceV1(sealed(fixture({ artifacts: common, edges: [], lexical_top_k: [], constraints: {
    must_link_pairs: [], cannot_link_pairs: [{ from_uid: A[0], to_uid: A[1] }], protected_bundle_pairs: [{ from_uid: A[0], to_uid: A[1] }]
  } }))), /protected bundle/);
  const triangle = analyzeRebalanceV1(sealed(fixture({ artifacts: common, edges: [], lexical_top_k: [], config: { max_cluster_size: 3 }, constraints: {
    must_link_pairs: [{ from_uid: A[0], to_uid: A[1] }, { from_uid: A[1], to_uid: A[2] }, { from_uid: A[0], to_uid: A[2] }], cannot_link_pairs: []
  } })));
  assert.deepEqual(triangle.proposal.clusters.map((cluster) => cluster.members), [[A[0], A[1], A[2]]], "already-unified must links are idempotent");
  const bundle = analyzeRebalanceV1(sealed(fixture({ artifacts: common, edges: [{ from_uid: A[1], to_uid: A[2], edge_type: "links_to", status: "accepted", origin: "explicit" }], lexical_top_k: [], config: { max_cluster_size: 3 }, constraints: {
    must_link_pairs: [], cannot_link_pairs: [], protected_bundle_pairs: [{ from_uid: A[0], to_uid: A[1] }]
  } })));
  assert.deepEqual(bundle.proposal.clusters.map((cluster) => cluster.members), [[A[0], A[1], A[2]]], "same-boundary protected bundles participate in hard closure");
});

test("graph construction validates virtual segments and rejects non-sparse evidence", () => {
  assert.throws(() => analyzeRebalanceV1(sealed(fixture({ artifacts: [artifact(A[0], "doc/05_design/search/a.md", { visibility: "../../private" })] }))), /visibility/);
  assert.throws(() => analyzeRebalanceV1(sealed(fixture({ artifacts: [artifact(A[0], "doc/05_design/search/a.md", { trust_scope: "../../trusted" })] }))), /trust_scope/);
  const unknown = analyzeRebalanceV1(sealed(fixture({ edges: [{ from_uid: A[0], to_uid: A[1], edge_type: "invented", status: "accepted", origin: "explicit" }], lexical_top_k: [{ from_uid: A[1], to_uid: A[2], rank: 1, score_milli: 0 }] })));
  assert.equal(unknown.analysis.edges.some((edge) => edge.source === "edge:invented" || edge.source === "lexical"), false);
  assert.throws(() => analyzeRebalanceV1(sealed(fixture({ config: { max_candidate_edges: 2 }, artifacts: [
    artifact(A[0], "doc/05_design/search/a.md"), artifact(A[1], "doc/05_design/search/b.md"), artifact(A[2], "doc/05_design/search/c.md")
  ], edges: [], lexical_top_k: [] }))), /classification (candidate|membership) budget/);
  assert.throws(
    () => analyzeRebalanceV1(sealed(fixture({
      config: { max_candidate_edges: 1 }, artifacts: [artifact(A[0], "doc/05_design/search/a.md"), artifact(A[1], "doc/05_design/other/b.md", { components: ["other"], features: ["other"] })],
      edges: [{ from_uid: A[0], to_uid: A[1], edge_type: "invented", status: "accepted", origin: "explicit" }], lexical_top_k: [{ from_uid: A[0], to_uid: A[1], rank: 99, score_milli: 1 }]
    }))),
    /aggregate candidate budget/
  );
});

test("generated mirrors are project-scoped and canonical paths are unambiguous", () => {
  const testArtifact = artifact(A[0], "test/03_system/app/spipe/feature/rebalance_spec.spl", { kind: "test" });
  const otherProjectManual = artifact(A[1], "doc/06_spec/03_system/app/spipe/feature/rebalance_spec.md", { kind: "spec", project_uid: P2 });
  const result = analyzeRebalanceV1(sealed(fixture({ artifacts: [testArtifact, otherProjectManual], edges: [], lexical_top_k: [] })));
  assert.equal(result.analysis.metrics.test_spec_pairs, 0);
  assert.throws(() => analyzeRebalanceV1(sealed(fixture({ artifacts: [artifact(A[0], "doc/05_design/search/a.md"), artifact(A[1], "doc/05_design/search/a.md")], edges: [], lexical_top_k: [] }))), /canonical paths must be unambiguous/);
});

test("metrics honor configuration and objective only reports realized virtual grouping terms", () => {
  const result = analyzeRebalanceV1(sealed(fixture({ config: { direct_count_target: 1, direct_count_warning: 1, max_cluster_size: 1, lexical_top_k: 0 }, edges: [], lexical_top_k: [] })));
  assert.ok(result.analysis.metrics.direct_count_warning_directories >= 1);
  assert.deepEqual(Object.keys(result.proposal.objective.next.terms_milli).sort(), ["cut", "direct_count"]);
  assert.ok(result.analysis.omitted_capabilities.includes("depth_objective"));
});

test("directory metrics keep same-spelled project-relative paths separate", () => {
  const result = analyzeRebalanceV1(sealed(fixture({
    artifacts: [
      artifact(A[0], "doc/05_design/search/shared.md"),
      artifact(A[1], "doc/05_design/search/shared.md", { project_uid: P2 })
    ],
    edges: [], lexical_top_k: [], config: { direct_count_target: 1, direct_count_warning: 1 }
  })));
  assert.equal(result.analysis.metrics.directories, 2);
  assert.equal(result.analysis.metrics.direct_count_warning_directories, 0);
  assert.deepEqual(result.analysis.metrics.direct_counts, [
    { project_uid: P, path: "doc/05_design/search", count: 1 },
    { project_uid: P2, path: "doc/05_design/search", count: 1 }
  ]);
});

test("unsealed input, invalid must-link boundaries, and lexical candidates beyond top K fail closed", () => {
  assert.throws(() => analyzeRebalanceV1(fixture()), /deeply frozen/);
  assert.throws(() => analyzeRebalanceV1(sealed(fixture({ constraints: { must_link_pairs: [{ from_uid: A[0], to_uid: A[3] }], cannot_link_pairs: [] }, artifacts: [artifact(A[0], "doc/05_design/search/a.md"), artifact(A[3], "doc/05_design/search/d.md", { visibility: "private" })] }))), /must-link crosses/);
  const result = analyzeRebalanceV1(sealed(fixture({ lexical_top_k: [{ from_uid: A[1], to_uid: A[2], rank: 99, score_milli: 1000 }], config: { lexical_top_k: 1 } })));
  assert.equal(result.analysis.edges.some((edge) => edge.source === "lexical"), false);
});
