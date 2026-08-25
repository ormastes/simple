import { createAliasRecord } from "./alias.js";
import { createArtifactRecord } from "./artifact.js";
import { createEdgeRecord } from "./edge.js";
import { createProjectRecord } from "./project.js";
import { createProjectRelationRecord } from "./project_relation.js";
import { createSectionRecord } from "./section.js";
import { createSnapshotManifest } from "./snapshot.js";
import { createViewRecord } from "./view.js";

const VALIDATORS = Object.freeze({
  alias: createAliasRecord,
  artifact: createArtifactRecord,
  edge: createEdgeRecord,
  project: createProjectRecord,
  project_relation: createProjectRelationRecord,
  section: createSectionRecord,
  snapshot_manifest: createSnapshotManifest,
  view: createViewRecord
});

export function validateModelRecord(record) {
  if (!record || typeof record !== "object" || Array.isArray(record)) throw new TypeError("model record must be an object");
  const validator = VALIDATORS[record.type];
  if (!validator) throw new TypeError(`unsupported model record type: ${record.type}`);
  return validator(record);
}

export function supportedModelRecordTypes() {
  return Object.freeze(Object.keys(VALIDATORS));
}
