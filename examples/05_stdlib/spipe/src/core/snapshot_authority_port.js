/*
 * Non-admitted SnapshotAuthorityPortV1 contract.
 *
 * This deliberately contains no production composition root.  A future
 * service-owned publisher may create the private PublishedAuthorityInventoryV1
 * brand in this lexical capsule only after it has independent durability,
 * authorization, and projection evidence.  Until then every open fails
 * closed.  In particular, this module must never become a convenient local
 * inventory, manifest, filesystem, URI, cursor, or projection adapter.
 */

const PORTS = new WeakSet();
const VIEWS = new WeakSet();
const TARGET_CANDIDATES = new WeakSet();
const DIRECTORY_CANDIDATES = new WeakSet();
const EXPECTED_READ_BINDINGS = new WeakSet();
const INVENTORIES = new WeakSet();
const INVENTORY_STATES = new WeakMap();
const VIEW_STATES = new WeakMap();

const BINDING_FIELDS = Object.freeze([
  "workspaceUid", "projectUidOrNull", "worktreeUid", "baseSnapshotUid",
  "authoritySnapshotUid", "revisionId", "registryRevisionId"
]);

export class SnapshotAuthorityNonAdmissionError extends Error {
  constructor(code, message) {
    super(message);
    this.name = "SnapshotAuthorityNonAdmissionError";
    this.code = code;
  }
}

function deny(code, message) { throw new SnapshotAuthorityNonAdmissionError(code, message); }

function ownDataObject(value, label) {
  if (value == null || typeof value !== "object" || Array.isArray(value) || Object.getPrototypeOf(value) !== Object.prototype) {
    deny("SPKSA001", `${label} must be a plain closed record`);
  }
  const descriptors = Object.getOwnPropertyDescriptors(value);
  for (const descriptor of Object.values(descriptors)) {
    if (!Object.hasOwn(descriptor, "value") || descriptor.enumerable !== true || descriptor.configurable !== true || descriptor.writable !== true) {
      deny("SPKSA001", `${label} must contain ordinary enumerable data fields`);
    }
  }
  return value;
}

function closedFields(value, fields, label) {
  ownDataObject(value, label);
  const actual = Object.keys(value).sort();
  const expected = [...fields].sort();
  if (actual.length !== expected.length || actual.some((field, index) => field !== expected[index])) {
    deny("SPKSA001", `${label} has an invalid closed schema`);
  }
}

function opaqueText(value, field, { nullable = false } = {}) {
  if (nullable && value === null) return null;
  if (typeof value !== "string" || value.length === 0 || value.normalize("NFC") !== value || /[\u0000-\u001f\u007f]/.test(value)) {
    deny("SPKSA001", `${field} is not canonical opaque text`);
  }
  return value;
}

function validateBinding(binding) {
  closedFields(binding, BINDING_FIELDS, "snapshot binding");
  for (const field of BINDING_FIELDS) opaqueText(binding[field], field, { nullable: field === "projectUidOrNull" });
  return binding;
}

function requireBrand(value, brand, label) {
  if (!value || typeof value !== "object" || !brand.has(value)) deny("SPKSA002", `${label} is not a sealed SnapshotAuthorityPortV1 value`);
  return value;
}

function equalBinding(left, right) {
  return BINDING_FIELDS.every((field) => left[field] === right[field]);
}

/*
 * Future service composition reaches this only with its lexical inventory
 * brand.  The inventory itself is intentionally not a public schema: callers
 * cannot pass a manifest, a map, or a store-shaped substitute here.
 */
function openPrivatePublishedInventoryV1(inventory, binding) {
  requireBrand(inventory, INVENTORIES, "published authority inventory");
  validateBinding(binding);
  const state = INVENTORY_STATES.get(inventory);
  if (!state || !equalBinding(state.binding, binding) || state.authorityInstanceUid !== state.inventoryAuthorityInstanceUid ||
      state.authorityManifestDigest !== state.inventoryAuthorityManifestDigest) {
    deny("SPKSA004", "published authority inventory does not prove the complete sealed binding");
  }
  const view = Object.freeze({});
  VIEWS.add(view);
  VIEW_STATES.set(view, state);
  return view;
}

/*
 * These functions deliberately remain lexical.  They document the future
 * private composition shape without providing a raw-map or manifest seam.
 * The current module never mints INVENTORIES, VIEWS, candidates, or bindings.
 */
function openBoundSnapshot(binding) {
  validateBinding(binding);
  deny("SPKSA003", "SnapshotAuthorityPortV1 is non-admitted: no service-backed published authority inventory is available");
}

function resolveCanonicalTarget(view, candidate) {
  requireBrand(view, VIEWS, "authority view");
  requireBrand(candidate, TARGET_CANDIDATES, "canonical target candidate");
  deny("SPKSA003", "SnapshotAuthorityPortV1 is non-admitted");
}

function listDirectoryTarget(view, candidate) {
  requireBrand(view, VIEWS, "authority view");
  requireBrand(candidate, DIRECTORY_CANDIDATES, "directory target candidate");
  deny("SPKSA003", "SnapshotAuthorityPortV1 is non-admitted");
}

function createExpectedReadBindingV1(view, candidate, normalizedRequest) {
  requireBrand(view, VIEWS, "authority view");
  if (!TARGET_CANDIDATES.has(candidate) && !DIRECTORY_CANDIDATES.has(candidate)) {
    deny("SPKSA002", "read candidate is not a sealed SnapshotAuthorityPortV1 value");
  }
  ownDataObject(normalizedRequest, "normalized request");
  deny("SPKSA003", "SnapshotAuthorityPortV1 is non-admitted");
}

/**
 * The only public contract surface.  It has no constructor, factory,
 * installer, dependency-injection hook, raw inventory argument, or manifest
 * argument.  Opaque values can only be recognized by lexical brands.
 */
export const SnapshotAuthorityPortV1 = Object.freeze({
  openBoundSnapshot,
  resolveCanonicalTarget,
  listDirectoryTarget,
  createExpectedReadBindingV1,
  isSnapshotAuthorityViewV1: (value) => VIEWS.has(value),
  isCanonicalTargetCandidateV1: (value) => TARGET_CANDIDATES.has(value),
  isDirectoryTargetCandidateV1: (value) => DIRECTORY_CANDIDATES.has(value),
  isExpectedReadBindingV1: (value) => EXPECTED_READ_BINDINGS.has(value)
});

PORTS.add(SnapshotAuthorityPortV1);

export function isSnapshotAuthorityPortV1(value) {
  return Boolean(value && PORTS.has(value));
}

// Keep all private brands live and intentionally unconstructible in this
// non-admitted slice.  Removing this reference would tempt later code to add a
// public fixture factory merely to exercise a positive path.
void INVENTORIES;
void openPrivatePublishedInventoryV1;
