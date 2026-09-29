import { createUnicode17Analyzer } from "../index/analyzer.js";
import { deriveScopedSearchDocument, hashCanonical } from "../index/document.js";
import { LogicalLexicalIndex } from "../index/logical_index.js";
import { compareUtf8, searchFail } from "../index/contracts.js";
import { assertCanonicalUid, normalizeHash } from "../model/identity.js";

/**
 * Read-only metadata lexical discovery over one caller-supplied immutable
 * snapshot. This is deliberately not a full-text, authorization, provider,
 * cursor, or mutation API: only sealed identifier/title/classification
 * metadata below can be searched.
 */
const CONTRACT = "spipe-snapshot-lexical-discovery-v1";
const INVENTORY_FIELDS = Object.freeze(["snapshot", "artifacts"]);
const SNAPSHOT_FIELDS = Object.freeze(["snapshot_uid"]);
const ARTIFACT_FIELDS = Object.freeze([
  "uid", "key", "aliases", "title", "kind", "status",
  "features", "components", "layers", "project_uid"
]);
const CONTROL = /[\u0000-\u001f\u007f]/u;
const SNAPSHOT_UID = /^spks1-[a-f0-9]{64}$/;

function fail(message) { searchFail("invalid_request", message); }

function ownDataFields(value, fields, label) {
  if (!value || typeof value !== "object" || Array.isArray(value) || Object.getPrototypeOf(value) !== Object.prototype) fail(`${label} must be a plain object`);
  const names = Object.getOwnPropertyNames(value);
  const symbols = Object.getOwnPropertySymbols(value);
  if (symbols.length || names.length !== fields.length || names.some((name, index) => name !== fields[index])) fail(`${label} fields must be closed and ordered`);
  const descriptors = Object.getOwnPropertyDescriptors(value);
  for (const name of fields) {
    const descriptor = descriptors[name];
    if (!descriptor || !("value" in descriptor) || descriptor.get || descriptor.set || descriptor.configurable || descriptor.writable) fail(`${label}.${name} must be an immutable data property`);
  }
  if (!Object.isFrozen(value)) fail(`${label} must be frozen`);
  return value;
}

function requestDataFields(value, fields, label) {
  if (!value || typeof value !== "object" || Array.isArray(value) || Object.getPrototypeOf(value) !== Object.prototype) fail(`${label} must be a plain object`);
  const names = Object.getOwnPropertyNames(value);
  if (Object.getOwnPropertySymbols(value).length || names.length !== fields.length || names.some((name, index) => name !== fields[index])) fail(`${label} fields must be closed and ordered`);
  const descriptors = Object.getOwnPropertyDescriptors(value);
  for (const name of fields) {
    const descriptor = descriptors[name];
    if (!descriptor || !("value" in descriptor) || descriptor.get || descriptor.set) fail(`${label}.${name} must be a data property`);
  }
  return value;
}

function frozenData(value, label, seen = new Set()) {
  if (value === null || typeof value !== "object") return;
  if (seen.has(value)) fail(`${label} must not contain cycles`);
  seen.add(value);
  if (!Object.isFrozen(value)) fail(`${label} must be deeply frozen`);
  const descriptors = Object.getOwnPropertyDescriptors(value);
  for (const symbol of Object.getOwnPropertySymbols(value)) fail(`${label} must not contain symbol properties`);
  for (const [name, descriptor] of Object.entries(descriptors)) {
    if (Array.isArray(value) && name === "length") continue;
    if (!("value" in descriptor) || descriptor.get || descriptor.set) fail(`${label}.${name} must be a data property`);
    frozenData(descriptor.value, `${label}.${name}`, seen);
  }
  seen.delete(value);
}

function frozenDenseArray(value, label) {
  if (!Array.isArray(value) || !Object.isFrozen(value)) fail(`${label} must be a frozen array`);
  const names = Object.getOwnPropertyNames(value);
  if (names.length !== value.length + 1 || names.at(-1) !== "length") fail(`${label} must be dense and contain no extra properties`);
  const descriptors = Object.getOwnPropertyDescriptors(value);
  for (let index = 0; index < value.length; index += 1) {
    const name = String(index), descriptor = descriptors[name];
    if (!descriptor || !("value" in descriptor) || descriptor.get || descriptor.set || descriptor.configurable || descriptor.writable) fail(`${label} must contain only immutable data entries`);
  }
  const length = descriptors.length;
  if (!length || length.value !== value.length || length.writable || length.configurable || length.enumerable) fail(`${label} length must be immutable`);
  if (Object.getOwnPropertySymbols(value).length) fail(`${label} must not contain symbol properties`);
  return value;
}

function exactText(value, label, { max = 4096 } = {}) {
  if (typeof value !== "string" || value.length === 0 || value !== value.normalize("NFC") || CONTROL.test(value) || Buffer.byteLength(value, "utf8") > max) fail(`${label} must be bounded canonical text`);
  return value;
}

function sortedUniqueText(values, label) {
  frozenDenseArray(values, label);
  const output = values.map((value, index) => exactText(value, `${label}[${index}]`));
  for (let index = 1; index < output.length; index += 1) if (compareUtf8(output[index - 1], output[index]) >= 0) fail(`${label} must be unique and UTF-8 sorted`);
  return output;
}

function artifactMetadata(value) {
  ownDataFields(value, ARTIFACT_FIELDS, "SnapshotLexicalArtifactV1");
  const uid = assertCanonicalUid(value.uid, "artifact.uid", ["A"]);
  const metadata = {
    uid,
    key: exactText(value.key, "artifact.key"),
    aliases: sortedUniqueText(value.aliases, "artifact.aliases"),
    title: exactText(value.title, "artifact.title"),
    kind: exactText(value.kind, "artifact.kind"),
    status: exactText(value.status, "artifact.status"),
    features: sortedUniqueText(value.features, "artifact.features"),
    components: sortedUniqueText(value.components, "artifact.components"),
    layers: sortedUniqueText(value.layers, "artifact.layers"),
    project_uid: assertCanonicalUid(value.project_uid, "artifact.project_uid", ["P"])
  };
  return Object.freeze(metadata);
}

function metadataInventory(inventory, expectedSnapshotUid) {
  ownDataFields(inventory, INVENTORY_FIELDS, "SnapshotLexicalInventoryV1");
  frozenData(inventory, "inventory");
  ownDataFields(inventory.snapshot, SNAPSHOT_FIELDS, "SnapshotLexicalSnapshotV1");
  const snapshotUid = inventory.snapshot.snapshot_uid;
  if (typeof snapshotUid !== "string" || !SNAPSHOT_UID.test(snapshotUid)) fail("inventory.snapshot.snapshot_uid must be canonical");
  if (snapshotUid !== expectedSnapshotUid) searchFail("binding_mismatch", "snapshot_uid does not match inventory snapshot");
  frozenDenseArray(inventory.artifacts, "inventory.artifacts");
  const artifacts = inventory.artifacts.map(artifactMetadata);
  const seen = new Set();
  for (const artifact of artifacts) {
    if (seen.has(artifact.uid)) searchFail("binding_mismatch", "inventory contains duplicate artifact UID");
    seen.add(artifact.uid);
  }
  return Object.freeze(artifacts);
}

function classificationText(artifact) {
  return [artifact.kind, artifact.status, ...artifact.features, ...artifact.components, ...artifact.layers, artifact.project_uid].join(" ");
}

function documentFor(artifact, scopeDigest) {
  return deriveScopedSearchDocument({
    document_id: artifact.uid,
    revision: "snapshot-lexical-v1",
    fields: [
      { name: "identifier", value: [artifact.uid, artifact.key, ...artifact.aliases].join(" ") },
      { name: "title", value: artifact.title },
      { name: "classification", value: classificationText(artifact) }
    ],
    facets: [],
    visibility_digest: scopeDigest,
    scope_digest: scopeDigest
  });
}

function resultHit(metadata, source) {
  return Object.freeze({
    uid: metadata.uid,
    key: metadata.key,
    aliases: metadata.aliases,
    title: metadata.title,
    kind: metadata.kind,
    status: metadata.status,
    features: metadata.features,
    components: metadata.components,
    layers: metadata.layers,
    project_uid: metadata.project_uid,
    score_milli: source.score_milli,
    matched_fields: source.matched_fields,
    source_rank: source.source_rank
  });
}

export class SnapshotLexicalSearchV1 {
  #workspaceUid; #snapshotUid; #scopeDigest; #logicalRoot; #index; #artifacts;

  constructor(input = {}) {
    const { workspace_uid, snapshot_uid, authorization_scope_digest, inventory } = requestDataFields(input, ["workspace_uid", "snapshot_uid", "authorization_scope_digest", "inventory"], "SnapshotLexicalSearchInitV1");
    this.#workspaceUid = assertCanonicalUid(workspace_uid, "workspace_uid", ["W"]);
    if (typeof snapshot_uid !== "string" || !SNAPSHOT_UID.test(snapshot_uid)) fail("snapshot_uid must be canonical");
    this.#snapshotUid = snapshot_uid;
    this.#scopeDigest = normalizeHash(authorization_scope_digest, "authorization_scope_digest");
    this.#artifacts = metadataInventory(inventory, snapshot_uid);
    const analyzer = createUnicode17Analyzer();
    this.#index = new LogicalLexicalIndex({ scope_digest: this.#scopeDigest, analyzer, documents: this.#artifacts.map((artifact) => documentFor(artifact, this.#scopeDigest)), cursor_key: Buffer.alloc(32) });
    this.#logicalRoot = hashCanonical({ contract: CONTRACT, workspace_uid: this.#workspaceUid, snapshot_uid: this.#snapshotUid, authorization_scope_digest: this.#scopeDigest, metadata_root: this.#index.logical_root });
    Object.freeze(this);
  }

  search(input = {}) {
    const { query_text, limit } = requestDataFields(input, ["query_text", "limit"], "SnapshotLexicalSearchRequestV1");
    if (!Number.isSafeInteger(limit) || limit < 1 || limit > 100) searchFail("limit_exceeded", "limit must be 1..100");
    if (typeof query_text !== "string") fail("query_text must be text");
    const page = this.#index.query({ query_text, filters: [], limit, cursor: null, explain: false });
    const byUid = new Map(this.#artifacts.map((artifact) => [artifact.uid, artifact]));
    const hits = page.hits.map((hit) => resultHit(byUid.get(hit.document_id), hit));
    return Object.freeze({
      snapshot_uid: this.#snapshotUid,
      authorization_scope_digest: this.#scopeDigest,
      logical_root: this.#logicalRoot,
      hits: Object.freeze(hits),
      exhausted: page.exhausted
    });
  }
}

export const SNAPSHOT_LEXICAL_SEARCH_CONTRACT = CONTRACT;
