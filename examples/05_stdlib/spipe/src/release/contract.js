import { createHash } from "node:crypto";

export const releaseSchemas = Object.freeze({
  vcs_policy: "spipe-vcs/3",
  session: "spipe-session/1",
  release: "spipe-release/1",
  candidate: "spipe-candidate/1"
});

export const releaseCapabilities = Object.freeze({
  isolated_sessions: true,
  reviewed_beta_backports: true,
  immutable_release_candidates: true,
  promote_without_rebuild: true,
  operational_release_planning: true,
  main_fix_discovery_planning: true,
  release_first_forward_port_validation: true,
  external_release_mutation: false
});

export const releaseOperations = Object.freeze([
  "isolated-session",
  "beta-backport",
  "candidate",
  "promotion",
  "main-fix-discovery",
  "forward-port"
]);

const semanticRules = Object.freeze([
  ["isolated-session", /\bisolated-session\b/],
  ["reviewed-beta-backport", /\breviewed-beta-backport\b/],
  ["immutable-candidate", /\bimmutable-candidate\b/],
  ["promote-without-rebuild", /\bpromote-without-rebuild\b/],
  ["protected-ref-guard", /\bprotected-ref-guard\b/],
  ["non-destructive-release-identity", /\bnon-destructive-release-identity\b/]
]);

function stableJson(value) {
  if (Array.isArray(value)) return `[${value.map(stableJson).join(",")}]`;
  if (value && typeof value === "object") {
    return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableJson(value[key])}`).join(",")}}`;
  }
  return JSON.stringify(value);
}

export function digest(value) {
  return createHash("sha256").update(typeof value === "string" ? value : stableJson(value)).digest("hex");
}

export function releaseContractHash() {
  return digest({ schemas: releaseSchemas, capabilities: releaseCapabilities, operations: releaseOperations });
}

export function projectionSemantics(content) {
  return semanticRules.filter(([, pattern]) => pattern.test(content)).map(([name]) => name);
}

export function projectionSemanticHash(content) {
  const semantics = projectionSemantics(content);
  if (semantics.length !== semanticRules.length) {
    const missing = semanticRules.map(([name]) => name).filter((name) => !semantics.includes(name));
    throw new Error(`release projection is missing semantics: ${missing.join(", ")}`);
  }
  return digest(semantics);
}

export function canonicalProjectionSemanticHash() {
  return digest(semanticRules.map(([name]) => name));
}
