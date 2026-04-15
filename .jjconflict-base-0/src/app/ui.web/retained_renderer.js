// Retained-mode DOM reconciler for the Simple web WM.
// Keyed by canonical id "surface_id#widget_id".
//
// Patch op field names follow patch_wire.spl (snake_case "op" values, "w"/"h" for layout).
// NOTE: Protocol doc §6 Example 2 uses PascalCase "kind" + "width"/"height" — that is
// inconsistent with the encoder. We match patch_wire.spl. Flag to Agent D for resolution.

// Known prop keys applied as direct element properties (not data-* attributes).
const DIRECT_PROPS = new Set(['text', 'value', 'disabled', 'placeholder', 'title']);

// Map widget kind to element tag + class.
const KIND_MAP = {
  window:    () => { const el = document.createElement('div');    el.className = 'wm-window';  return el; },
  button:    () => { const el = document.createElement('button'); el.className = 'wm-btn';     return el; },
  input:     () => { const el = document.createElement('input');  el.className = 'wm-input';   return el; },
};

function _makeElement(kind) {
  const factory = KIND_MAP[kind];
  if (factory) return factory();
  const el = document.createElement('div');
  el.className = `wm-widget wm-kind-${kind}`;
  return el;
}

function _canonicalId(surface_id, widget_id) {
  return `${surface_id}#${widget_id}`;
}

function _applyProp(el, key, value) {
  if (DIRECT_PROPS.has(key)) {
    if (key === 'text') {
      el.textContent = value;
    } else if (key === 'disabled') {
      el.disabled = value === 'true' || value === true;
    } else {
      el[key] = value;
    }
  } else {
    el.dataset[key] = value;
  }
}

export class RetainedRenderer {
  constructor(rootEl) {
    this.root = rootEl;
    this.nodes = new Map();              // canonical_id -> HTMLElement
    this.surfaces = new Map();           // surface_id -> root HTMLElement
    this.activeSurface = null;
    this.protocolVersion = 1;
    this.snapshotRevision = 0;
    this.lastSequence = -1;
  }

  // -------------------------------------------------------------------------
  // Snapshot
  // -------------------------------------------------------------------------

  // Apply a full snapshot. Clears existing DOM for surfaces not in payload.
  applySnapshot(payload) {
    this.snapshotRevision = payload.revision ?? 0;
    this.lastSequence = payload.sequence ?? -1;

    // Collect surface ids present in this snapshot.
    const incomingSurfaces = new Set();
    const roots = Array.isArray(payload.roots) ? payload.roots
                : (payload.root ? [payload.root] : []);

    for (const nodeSpec of roots) {
      const surfaceId = nodeSpec.surface_id;
      incomingSurfaces.add(surfaceId);
      // Remove old DOM for this surface if present.
      if (this.surfaces.has(surfaceId)) {
        this.surfaces.get(surfaceId).remove();
        // Clean up node map entries for this surface.
        for (const [cid] of this.nodes) {
          if (cid.startsWith(surfaceId + '#')) this.nodes.delete(cid);
        }
        this.surfaces.delete(surfaceId);
      }
      const el = this._materializeNode(nodeSpec);
      this.surfaces.set(surfaceId, el);
      this.root.appendChild(el);
    }

    // Remove surfaces not present in this snapshot.
    for (const [surfId, el] of this.surfaces) {
      if (!incomingSurfaces.has(surfId)) {
        el.remove();
        for (const [cid] of this.nodes) {
          if (cid.startsWith(surfId + '#')) this.nodes.delete(cid);
        }
        this.surfaces.delete(surfId);
      }
    }
  }

  // -------------------------------------------------------------------------
  // Patch batch
  // -------------------------------------------------------------------------

  // Apply a patch_batch. payload shape: { snapshot_revision, from_sequence,
  // to_sequence, patches: Array<{op, ...}> }
  applyPatchBatch(payload) {
    this.snapshotRevision = payload.snapshot_revision ?? this.snapshotRevision;
    this.lastSequence = payload.to_sequence ?? this.lastSequence;

    for (const p of (payload.patches ?? [])) {
      switch (p.op) {
        case 'insert_child':     this._opInsertChild(p);     break;
        case 'remove_child':     this._opRemoveChild(p);     break;
        case 'replace_node':     this._opReplaceNode(p);     break;
        case 'update_prop':      this._opUpdateProp(p);      break;
        case 'remove_prop':      this._opRemoveProp(p);      break;
        case 'update_layout':    this._opUpdateLayout(p);    break;
        case 'update_visibility':this._opUpdateVisibility(p);break;
        case 'move_child':       this._opMoveChild(p);       break;
        default:
          console.warn('[RetainedRenderer] unknown patch op:', p.op);
      }
    }
  }

  // -------------------------------------------------------------------------
  // Patch ops — shapes from patch_wire.spl
  // -------------------------------------------------------------------------

  // { op:"insert_child", parent:"surf#wid", index:N, node:{canonical_id,...} }
  _opInsertChild(p) {
    const parentEl = this.nodes.get(p.parent);
    if (!parentEl) return;
    const el = this._materializeNode(p.node);
    const children = Array.from(parentEl.children);
    const idx = p.index ?? children.length;
    if (idx >= children.length) {
      parentEl.appendChild(el);
    } else {
      parentEl.insertBefore(el, children[idx]);
    }
  }

  // { op:"remove_child", parent:"surf#wid", index:N }
  _opRemoveChild(p) {
    const parentEl = this.nodes.get(p.parent);
    if (!parentEl) return;
    const children = Array.from(parentEl.children);
    const idx = p.index ?? -1;
    if (idx >= 0 && idx < children.length) {
      const removed = children[idx];
      const cid = removed.dataset.canonicalId;
      removed.remove();
      if (cid) this.nodes.delete(cid);
    }
  }

  // { op:"replace_node", id:"surf#wid", node:{canonical_id,...} }
  _opReplaceNode(p) {
    const old = this.nodes.get(p.id);
    if (!old) return;
    const el = this._materializeNode(p.node);
    old.replaceWith(el);
    this.nodes.delete(p.id);
  }

  // { op:"update_prop", id:"surf#wid", key:"...", value:"..." }
  _opUpdateProp(p) {
    const el = this.nodes.get(p.id);
    if (!el) return;
    _applyProp(el, p.key, p.value);
  }

  // { op:"remove_prop", id:"surf#wid", key:"..." }
  _opRemoveProp(p) {
    const el = this.nodes.get(p.id);
    if (!el) return;
    if (DIRECT_PROPS.has(p.key)) {
      if (p.key === 'text') el.textContent = '';
      else delete el[p.key];
    } else {
      delete el.dataset[p.key];
    }
  }

  // { op:"update_layout", id:"surf#wid", x:N, y:N, w:N, h:N }
  // Layout is applied as inline style on window-root elements.
  _opUpdateLayout(p) {
    const el = this.nodes.get(p.id);
    if (!el) return;
    if (p.x != null) el.style.left   = p.x + 'px';
    if (p.y != null) el.style.top    = p.y + 'px';
    if (p.w != null) el.style.width  = p.w + 'px';
    if (p.h != null) el.style.height = p.h + 'px';
  }

  // { op:"update_visibility", id:"surf#wid", visible:bool }
  _opUpdateVisibility(p) {
    const el = this.nodes.get(p.id);
    if (!el) return;
    const vis = p.visible === true || p.visible === 'true';
    el.style.display = vis ? '' : 'none';
    if (vis) {
      el.classList.remove('minimized');
    } else {
      el.classList.add('minimized');
    }
  }

  // { op:"move_child", parent:"surf#wid", from:N, to:N }
  _opMoveChild(p) {
    const parentEl = this.nodes.get(p.parent);
    if (!parentEl) return;
    const children = Array.from(parentEl.children);
    const from = p.from ?? 0;
    const to   = p.to   ?? 0;
    if (from < 0 || from >= children.length) return;
    const child = children[from];
    child.remove();
    const updated = Array.from(parentEl.children);
    if (to >= updated.length) {
      parentEl.appendChild(child);
    } else {
      parentEl.insertBefore(child, updated[to]);
    }
  }

  // -------------------------------------------------------------------------
  // Focus helper (called by wm.js on focus_changed frames)
  // -------------------------------------------------------------------------

  setFocus(surfaceId, widgetId) {
    // Remove focused class from all surface roots.
    for (const el of this.surfaces.values()) {
      el.classList.remove('focused');
    }
    const cid = _canonicalId(surfaceId, widgetId);
    const el = this.nodes.get(cid) ?? this.surfaces.get(surfaceId);
    if (el) el.classList.add('focused');
    this.activeSurface = surfaceId;
  }

  // -------------------------------------------------------------------------
  // Materialize helpers
  // -------------------------------------------------------------------------

  // Creates an element for nodeSpec. nodeSpec may be:
  //   - Full snapshot node: { surface_id, widget_id, kind, props, children }
  //   - Minimal patch node: { canonical_id } (no kind — server patches in details later)
  _materializeNode(nodeSpec) {
    if (!nodeSpec) return document.createElement('div');

    let canonicalId, surfaceId, widgetId, kind, props, children;

    if (nodeSpec.canonical_id) {
      // Minimal patch node — parse canonical_id.
      canonicalId = nodeSpec.canonical_id;
      const hash = canonicalId.indexOf('#');
      surfaceId = hash >= 0 ? canonicalId.slice(0, hash) : canonicalId;
      widgetId  = hash >= 0 ? canonicalId.slice(hash + 1) : '';
      kind = 'container';  // placeholder; will be updated via subsequent patches
      props = {};
      children = [];
    } else {
      surfaceId = nodeSpec.surface_id ?? '';
      widgetId  = nodeSpec.widget_id  ?? '';
      canonicalId = _canonicalId(surfaceId, widgetId);
      kind = nodeSpec.kind ?? 'container';
      props = nodeSpec.props ?? {};
      children = nodeSpec.children ?? [];
    }

    const el = _makeElement(kind);
    el.dataset.canonicalId = canonicalId;
    el.dataset.surfaceId   = surfaceId;
    el.dataset.widgetId    = widgetId;

    // Apply props.
    for (const [key, value] of Object.entries(props)) {
      _applyProp(el, key, value);
    }

    // Apply layout from props if present in snapshot (x/y/w/h or x/y/width/height).
    const lx = props.x;
    const ly = props.y;
    const lw = props.w ?? props.width;
    const lh = props.h ?? props.height;
    if (lx != null) el.style.left   = lx + 'px';
    if (ly != null) el.style.top    = ly + 'px';
    if (lw != null) el.style.width  = lw + 'px';
    if (lh != null) el.style.height = lh + 'px';

    if (props.visible === false || props.visible === 'false') {
      el.style.display = 'none';
    }

    // Register in node map.
    this.nodes.set(canonicalId, el);

    // Recurse children.
    for (const child of children) {
      el.appendChild(this._materializeNode(child));
    }

    return el;
  }
}
