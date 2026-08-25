import { canonicalJson, freezeDeep, hashCanonicalTuple } from "../storage/canonical.js";

export const SEMANTIC_RELATIONS = Object.freeze(["independent", "dependent", "extends"]);
export const PHYSICAL_LINKAGES = Object.freeze(["none", "path", "symlink", "junction", "gitlink", "worktree", "package"]);
export const TRUST_RELATIONS = Object.freeze(["trusted", "reviewed", "untrusted"]);

function memberOf(value, values, name) {
  if (!values.includes(value)) throw new TypeError(`${name} must be one of: ${values.join(", ")}`);
  return value;
}

/**
 * Create the explicit semantic/physical relation record.  These fields are
 * intentionally separate: a gitlink can be semantically independent, and a
 * path mount can semantically extend another project.
 */
export function createProjectRelation(input) {
  if (!input || typeof input !== "object") throw new TypeError("relation must be an object");
  const fromProjectUid = String(input.fromProjectUid ?? input.from_project_uid ?? "");
  const toProjectUid = String(input.toProjectUid ?? input.to_project_uid ?? "");
  if (!fromProjectUid || !toProjectUid || fromProjectUid === toProjectUid) throw new TypeError("relation endpoints must be distinct");
  const semantic = memberOf(input.semantic ?? "independent", SEMANTIC_RELATIONS, "semantic relation");
  const physical = memberOf(input.physical ?? input.linkage ?? "none", PHYSICAL_LINKAGES, "physical linkage");
  const trust = memberOf(input.trust ?? "reviewed", TRUST_RELATIONS, "trust relation");
  const mount = input.mount === undefined || input.mount === null ? null : String(input.mount);
  const revision = input.revision === undefined || input.revision === null ? null : String(input.revision);
  const versionRelation = input.versionRelation ?? input.version_relation ?? (revision ? "pinned" : null);
  if (versionRelation !== null && !["commit", "tag", "range", "floating", "pinned"].includes(versionRelation)) {
    throw new TypeError("versionRelation is invalid");
  }
  const relation = {
    relation_uid: input.relationUid ?? input.relation_uid ?? `REL-${hashCanonicalTuple("relation_v1", [fromProjectUid, toProjectUid, semantic, physical, mount ?? "", revision ?? "", trust])}`,
    from_project_uid: fromProjectUid,
    to_project_uid: toProjectUid,
    semantic,
    physical,
    revision,
    version_relation: versionRelation,
    mount,
    trust
  };
  return freezeDeep(JSON.parse(canonicalJson(relation)));
}

export function relationKey(relation) {
  return [relation.from_project_uid, relation.to_project_uid, relation.semantic, relation.physical, relation.mount ?? "", relation.revision ?? "", relation.trust].join("\u001f");
}

export function validateProjectRelation(relation) {
  return createProjectRelation(relation);
}
