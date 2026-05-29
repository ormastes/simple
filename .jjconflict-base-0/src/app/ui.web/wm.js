// Window Manager for Simple Language Web UI — v2 (server-authoritative)
//
// The server is the sole authority over window state (position, z-order,
// focus, visibility). This client:
//   1. Authenticates via POST /ui/login → bearer token.
//   2. Opens WebSocket at /ui/ws?token=<token>.
//   3. Sends hello → open_session (or resume_session on reconnect).
//   4. Forwards raw input events to the server.
//   5. Applies server-sent snapshot / patch_batch via RetainedRenderer.
//
// Optimistic drag/resize: a separate .wm-ghost overlay is shown during drag.
// It is removed when the next patch_batch arrives or when the drag completes.
// The server's patch_batch is the ground truth; the ghost is cosmetic only.

// RetainedRenderer is loaded via dynamic import so this file can remain a
// classic script (html.spl does not set type="module"). If html.spl gains
// type="module", replace the dynamic import with a top-level import.

const PROTOCOL_VERSION = 1;
const RECONNECT_BASE_MS = 1000;
const RECONNECT_MAX_MS  = 16000;
const ACK_INTERVAL_MS   = 500;
const HOST_NATIVE_EVENT_SOURCE = 'native_event';
const NATIVE_SUPPRESSION_TTL_MS = 500;
const NATIVE_BURST_DEBOUNCE_MS = 80;

class SimpleWindowManager {
  constructor(options = {}) {
    this.transport = options.transport || 'websocket';
    this.rendererModuleUrl = options.rendererModuleUrl || './retained_renderer.js';
    this.nativeHostWindows = !!options.nativeHostWindows;

    // DOM roots (populated from server state, not local decisions).
    this.desktop  = document.getElementById('wm-desktop');
    this.taskbar  = document.getElementById('wm-taskbar');

    // Renderer — set after dynamic import resolves.
    this.renderer = null;

    // WebSocket + session state.
    this.ws            = null;
    this.sessionId     = null;
    this.token         = null;
    this.reconnectDelay = RECONNECT_BASE_MS;
    this.reconnecting  = false;

    // Drag/resize ghost state.
    this.dragState     = null;  // { windowEl, startX, startY, origLeft, origTop, ghostEl, timer }
    this.resizeState   = null;  // { windowEl, startX, startY, origRect, ghostEl, timer, direction }

    // Periodic ack timer.
    this._ackTimer = null;
    this._nativeWindowEventSuppressions = new Map();
    this._nativeWindowBurstTimers = new Map();
    this._electronWindows = new Map();
    this._electronActiveWindowId = '';
    this._electronZCounter = 20;

    // Load renderer then begin auth.
    this._init();
  }

  // -------------------------------------------------------------------------
  // Initialisation
  // -------------------------------------------------------------------------

  async _init() {
    if (this.transport === 'electron-ipc') {
      this._bindGlobalEvents();
      if (window.simpleUI && window.simpleUI.onNativeWindowEvent) {
        window.simpleUI.onNativeWindowEvent((msg) => this._handleNativeWindowEvent(msg || {}));
      }
      this.sessionId = 'electron-ipc';
      if (window.simpleUI && typeof window.simpleUI.notifyWmReady === 'function') {
        window.simpleUI.notifyWmReady();
      }
      await this._loadRenderer(false);
      return;
    }
    await this._loadRenderer(this.transport !== 'electron-ipc');
    this._bindGlobalEvents();
    if (window.simpleUI && window.simpleUI.onNativeWindowEvent) {
      window.simpleUI.onNativeWindowEvent((msg) => this._handleNativeWindowEvent(msg || {}));
    }
    await this._authenticate();
  }

  async _loadRenderer(required) {
    try {
      const mod = await import(this.rendererModuleUrl);
      this.renderer = new mod.RetainedRenderer(this.desktop);
      return true;
    } catch (err) {
      if (required) {
        console.error('[WM] retained renderer load failed:', err);
      }
      this.renderer = null;
      return false;
    }
  }

  async _authenticate() {
    try {
      const resp = await fetch('/ui/login', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ capability_grant: 'dev' })
      });
      if (!resp.ok) throw new Error('login failed: ' + resp.status);
      const data = await resp.json();
      this.token = data.token;
      this._connect();
    } catch (err) {
      console.error('[WM] auth error:', err);
      setTimeout(() => this._authenticate(), this.reconnectDelay);
    }
  }

  // -------------------------------------------------------------------------
  // WebSocket connection
  // -------------------------------------------------------------------------

  _connect() {
    const proto = location.protocol === 'https:' ? 'wss' : 'ws';
    const url   = `${proto}://${location.host}/ui/ws?token=${encodeURIComponent(this.token)}`;
    this.ws = new WebSocket(url);

    this.ws.onopen = () => {
      this.reconnectDelay = RECONNECT_BASE_MS;
      this.reconnecting   = false;
      this._send({ t: 'hello', v: PROTOCOL_VERSION, s: null,
                   payload: { protocol_version: PROTOCOL_VERSION, client_caps: 0 } });
    };

    this.ws.onmessage = (e) => {
      let frame;
      try { frame = JSON.parse(e.data); } catch { return; }
      this._dispatch(frame);
    };

    this.ws.onclose = (e) => {
      this._stopAckTimer();
      if (e.code === 1002) {
        // Protocol mismatch — do not retry without software upgrade.
        console.error('[WM] protocol version mismatch — cannot reconnect');
        return;
      }
      this._scheduleReconnect();
    };

    this.ws.onerror = () => {
      this.ws.close();
    };
  }

  _scheduleReconnect() {
    if (this.reconnecting) return;
    this.reconnecting = true;
    setTimeout(() => {
      this.reconnecting = false;
      this._reconnect();
    }, this.reconnectDelay);
    this.reconnectDelay = Math.min(this.reconnectDelay * 2, RECONNECT_MAX_MS);
  }

  _reconnect() {
    // Send resume_session after reconnect so server can diff-patch instead of
    // sending a full snapshot whenever possible (§8 of the protocol doc).
    const rev = this.renderer ? this.renderer.snapshotRevision : 0;
    const seq = this.renderer ? this.renderer.lastSequence : -1;

    const proto = location.protocol === 'https:' ? 'wss' : 'ws';
    const url   = `${proto}://${location.host}/ui/ws?token=${encodeURIComponent(this.token)}`;
    this.ws = new WebSocket(url);

    this.ws.onopen = () => {
      this.reconnectDelay = RECONNECT_BASE_MS;
      this.reconnecting   = false;
      // hello first, then resume.
      this._send({ t: 'hello', v: PROTOCOL_VERSION, s: null,
                   payload: { protocol_version: PROTOCOL_VERSION, client_caps: 0 } });
      // After capabilities response we send resume_session — handled in _dispatch.
      // Store resume params so _dispatch can use them.
      this._pendingResume = { session_id: this.sessionId, snapshot_revision: rev, last_sequence: seq };
    };

    this.ws.onmessage = (e) => {
      let frame;
      try { frame = JSON.parse(e.data); } catch { return; }
      this._dispatch(frame);
    };

    this.ws.onclose = (e) => {
      this._stopAckTimer();
      if (e.code === 1002) {
        console.error('[WM] protocol version mismatch — cannot reconnect');
        return;
      }
      this._scheduleReconnect();
    };

    this.ws.onerror = () => { this.ws.close(); };
  }

  // -------------------------------------------------------------------------
  // Frame dispatch (S→C)
  // -------------------------------------------------------------------------

  _dispatch(frame) {
    // Update session id from any server frame that carries one.
    if (frame.s && !this.sessionId) {
      this.sessionId = frame.s;
    }

    switch (frame.t) {
      case 'capabilities':
        // Server has greeted us. Send open_session or resume_session.
        if (this._pendingResume) {
          this._send({
            t: 'resume_session', v: PROTOCOL_VERSION, s: this.sessionId, seq: null,
            payload: this._pendingResume
          });
          this._pendingResume = null;
        } else {
          const vp = { x: 0, y: 0, w: window.innerWidth, h: window.innerHeight };
          this._send({
            t: 'open_session', v: PROTOCOL_VERSION, s: null, seq: null,
            payload: { viewport: vp }
          });
        }
        this._startAckTimer();
        break;

      case 'snapshot':
        if (!this.renderer) break;
        this.sessionId = frame.s ?? this.sessionId;
        this.renderer.applySnapshot(frame.payload);
        this._cancelGhost();
        break;

      case 'patch_batch':
        if (!this.renderer) break;
        this.renderer.applyPatchBatch(frame.payload);
        this._cancelGhost();
        break;

      case 'taskbar_model':
        this.renderTaskbarModel(frame.payload || {});
        break;

      case 'host_window_command':
        this._handleHostWindowCommand(frame.payload || {});
        break;

      case 'focus_changed':
        if (!this.renderer) break;
        this.renderer.setFocus(
          frame.payload.surface_id,
          frame.payload.widget_id
        );
        break;

      case 'ping':
        this._send({ t: 'pong', v: PROTOCOL_VERSION, s: this.sessionId, seq: null,
                     payload: { nonce: frame.payload.nonce } });
        break;

      case 'error':
        console.error('[WM] server error:', frame.payload.code, frame.payload.message);
        this._showToast(frame.payload.message);
        if (frame.payload.retry_after_ms > 0) {
          this.reconnectDelay = frame.payload.retry_after_ms;
        }
        break;

      default:
        // Unknown message type — ignore silently.
        break;
    }
  }

  // -------------------------------------------------------------------------
  // Sending (C→S)
  // -------------------------------------------------------------------------

  _send(frame) {
    if (this.transport === 'electron-ipc') {
      if (window.simpleUI && typeof window.simpleUI.sendFrame === 'function') {
        window.simpleUI.sendFrame(frame);
      }
      return;
    }
    if (this.ws && this.ws.readyState === WebSocket.OPEN) {
      this.ws.send(JSON.stringify(frame));
    }
  }

  _sendInputEvent(surfaceId, widgetId, event) {
    this._send({
      t: 'input_event', v: PROTOCOL_VERSION, s: this.sessionId, seq: null,
      payload: { surface_id: surfaceId, widget_id: widgetId, event }
    });
  }

  _sendWindowCmd(kind, extra) {
    this._send({
      t: 'window_cmd', v: PROTOCOL_VERSION, s: this.sessionId, seq: null,
      payload: { cmd_type: kind, kind, ...extra }
    });
  }

  _sendLaunch(appId) {
    this._sendWindowCmd('launch', { app_id: appId });
  }

  // Install one persistent click listener on the taskbar that dispatches
  // by data-action. Idempotent — rendering can clear innerHTML without
  // losing the handler. Call once after this.taskbar is bound.
  _installTaskbarDelegation() {
    if (!this.taskbar || this._taskbarDelegationInstalled) return;
    this._taskbarDelegationInstalled = true;
    this.taskbar.addEventListener('click', (ev) => {
      const el = ev.target.closest('[data-action]');
      if (!el || !this.taskbar.contains(el)) return;
      const action = el.dataset.action;
      if (action === 'launch' && el.dataset.appId) {
        this._sendLaunch(el.dataset.appId);
      } else if (action === 'focus' && el.dataset.windowIdHint) {
        const isElectronWindow = this.transport === 'electron-ipc' && this._electronWindows.has(el.dataset.windowIdHint);
        if (this.transport === 'electron-ipc' && this._electronWindows.has(el.dataset.windowIdHint)) {
          this._electronFocusWindow(el.dataset.windowIdHint);
        }
        this._sendWindowCmd('focus', {
          window_id_hint: el.dataset.windowIdHint,
          ...(isElectronWindow ? { source: HOST_NATIVE_EVENT_SOURCE } : {})
        });
      }
    });
  }

  // Render a TaskbarModel { pinned, running, tray } into the taskbar
  // element. Click handling is via the delegated listener above, so
  // replacing innerHTML does not lose dispatch.
  renderTaskbarModel(model) {
    if (!this.taskbar) return;
    this._installTaskbarDelegation();
    this.taskbar.innerHTML = '';

    const pinned = document.createElement('div');
    pinned.className = 'wm-taskbar-section pinned';
    for (const a of (model.pinned || [])) {
      const item = document.createElement('div');
      item.className = 'wm-taskbar-item pinned';
      item.textContent = a.display_name || a.app_id;
      item.dataset.action = 'launch';
      item.dataset.appId = a.app_id;
      pinned.appendChild(item);
    }
    this.taskbar.appendChild(pinned);

    const running = document.createElement('div');
    running.className = 'wm-taskbar-section running';
    for (const w of (model.running || [])) {
      const item = document.createElement('div');
      item.className = 'wm-taskbar-item running'
        + (w.active ? ' active' : '')
        + (w.minimized ? ' minimized' : '');
      item.textContent = (w.minimized ? '[-] ' : '') + (w.title || w.window_id);
      item.dataset.action = 'focus';
      item.dataset.windowIdHint = w.window_id;
      running.appendChild(item);
    }
    this.taskbar.appendChild(running);

    const tray = document.createElement('div');
    tray.className = 'wm-taskbar-section tray';
    for (const t of (model.tray || [])) {
      const item = document.createElement('div');
      item.className = 'wm-taskbar-tray';
      item.textContent = t.label;
      tray.appendChild(item);
    }
    this.taskbar.appendChild(tray);
  }

  async _handleHostWindowCommand(payload) {
    const api = window.simpleUI;
    if (!api) return;
    const action = payload.action || '';
    const windowId = payload.window_id || '';
    try {
      if (this.transport === 'electron-ipc' && !this.nativeHostWindows) {
        this._handleEmbeddedHostWindowCommand(action, payload);
        return;
      }
      if (action === 'spawn_native_window' && api.spawnNativeWindow) {
        await this._runSuppressedNativeCommand(windowId, ['focus'], () =>
          api.spawnNativeWindow(
            windowId,
            payload.url || '',
            payload.width || 800,
            payload.height || 600,
            payload.title || ''
          )
        );
      } else if (action === 'close_native_window' && api.closeNativeWindow) {
        await this._runSuppressedNativeCommand(windowId, ['close'], () => api.closeNativeWindow(windowId));
      } else if (action === 'focus_native_window' && api.focusNativeWindow) {
        await this._runSuppressedNativeCommand(windowId, ['focus'], () => api.focusNativeWindow(windowId));
      } else if (action === 'minimize_native_window' && api.minimizeNativeWindow) {
        await this._runSuppressedNativeCommand(windowId, ['minimize'], () => api.minimizeNativeWindow(windowId));
      } else if (action === 'restore_native_window' && api.restoreNativeWindow) {
        await this._runSuppressedNativeCommand(windowId, ['restore'], () => api.restoreNativeWindow(windowId));
      } else if (action === 'move_native_window' && api.moveNativeWindow) {
        await this._runSuppressedNativeCommand(windowId, ['move'], () => api.moveNativeWindow(windowId, payload.x || 0, payload.y || 0));
      } else if (action === 'resize_native_window' && api.resizeNativeWindow) {
        await this._runSuppressedNativeCommand(windowId, ['resize'], () => api.resizeNativeWindow(windowId, payload.width || 800, payload.height || 600));
      } else if (action === 'maximize_native_window' && api.maximizeNativeWindow) {
        await this._runSuppressedNativeCommand(windowId, ['maximize'], () => api.maximizeNativeWindow(windowId));
      } else if (action === 'unmaximize_native_window' && api.unmaximizeNativeWindow) {
        await this._runSuppressedNativeCommand(windowId, ['unmaximize'], () => api.unmaximizeNativeWindow(windowId));
      } else if (action === 'set_native_window_title' && api.setNativeWindowTitle) {
        await this._runSuppressedNativeCommand(windowId, ['title'], () => api.setNativeWindowTitle(windowId, payload.title || ''));
      }
    } catch (err) {
      console.error('[WM] host window command failed:', action, err);
    }
  }

  _handleEmbeddedHostWindowCommand(action, payload) {
    const windowId = payload.window_id || payload.windowId || payload.surface_id || '';
    if (!windowId) return;
    if (action === 'spawn_native_window') {
      this._electronOpenWindow({
        windowId,
        title: payload.title || windowId,
        x: payload.x || 80,
        y: payload.y || 80,
        width: payload.width || 800,
        height: payload.height || 600,
        html: this._embeddedHostWindowHtml(payload)
      });
      this._sendWindowCmd('focus', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (action === 'close_native_window') {
      this._electronCloseWindow(windowId);
      this._sendWindowCmd('close', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (action === 'focus_native_window') {
      this._electronFocusWindow(windowId);
      this._sendWindowCmd('focus', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (action === 'minimize_native_window') {
      this._electronMinimizeWindow(windowId);
      this._sendWindowCmd('minimize', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (action === 'restore_native_window') {
      this._electronFocusWindow(windowId);
      this._sendWindowCmd('restore', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (action === 'move_native_window') {
      this._electronMoveWindow(windowId, payload.x || 0, payload.y || 0);
      this._sendWindowCmd('move', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE, x: payload.x || 0, y: payload.y || 0 });
    } else if (action === 'resize_native_window') {
      this._electronResizeWindow(windowId, payload.width || 800, payload.height || 600);
      this._sendWindowCmd('resize', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE, w: payload.width || 800, h: payload.height || 600 });
    } else if (action === 'maximize_native_window') {
      this._electronMaximizeWindow(windowId);
      this._sendWindowCmd('maximize', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (action === 'unmaximize_native_window') {
      this._electronUnmaximizeWindow(windowId);
      this._sendWindowCmd('unmaximize', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (action === 'set_native_window_title') {
      this._electronSetWindowTitle(windowId, payload.title || '');
      this._sendWindowCmd('set_title', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE, title: payload.title || '' });
    }
  }

  _embeddedHostWindowHtml(payload) {
    const url = payload.url || '';
    if (url && !url.startsWith('/')) {
      const safeUrl = _escapeAttr(url);
      return `<iframe src="${safeUrl}" style="display:block;width:100%;height:100%;border:0;background:transparent;" sandbox="allow-scripts allow-same-origin allow-forms allow-popups"></iframe>`;
    }
    const title = _escapeHtml(payload.title || payload.app_id || 'Simple App');
    const appId = _escapeHtml(payload.app_id || '');
    return `<div style="padding:20px"><h1>${title}</h1><p>${appId}</p></div>`;
  }

  _handleNativeWindowEvent(msg) {
    const type = msg.type || '';
    const windowId = msg.windowId || '';
    if (!type || !windowId) return;
    if (this._consumeNativeWindowEventSuppression(windowId, type)) return;
    if (type === 'focus') {
      this._sendWindowCmd('focus', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (type === 'minimize') {
      this._sendWindowCmd('minimize', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (type === 'restore') {
      this._sendWindowCmd('restore', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (type === 'maximize') {
      this._sendWindowCmd('maximize', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (type === 'unmaximize') {
      this._sendWindowCmd('unmaximize', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    } else if (type === 'move') {
      this._sendNativeWindowCmdDebounced(windowId, type, () => this._sendWindowCmd('move', {
        window_id_hint: windowId,
        source: HOST_NATIVE_EVENT_SOURCE,
        x: Math.round(msg.x ?? msg.bounds?.x ?? 0),
        y: Math.round(msg.y ?? msg.bounds?.y ?? 0)
      }));
    } else if (type === 'resize') {
      this._sendNativeWindowCmdDebounced(windowId, type, () => this._sendWindowCmd('resize', {
        window_id_hint: windowId,
        source: HOST_NATIVE_EVENT_SOURCE,
        w: Math.round(msg.width ?? msg.bounds?.width ?? 0),
        h: Math.round(msg.height ?? msg.bounds?.height ?? 0)
      }));
    } else if (type === 'title') {
      this._sendNativeWindowCmdDebounced(windowId, type, () => this._sendWindowCmd('set_title', {
        window_id_hint: windowId,
        source: HOST_NATIVE_EVENT_SOURCE,
        title: msg.title || ''
      }));
    } else if (type === 'close') {
      this._sendWindowCmd('close', { window_id_hint: windowId, source: HOST_NATIVE_EVENT_SOURCE });
    }
  }

  async _runSuppressedNativeCommand(windowId, types, invoke) {
    const tokens = types.map((type) => this._beginNativeWindowEventSuppression(windowId, type));
    try {
      const result = await invoke();
      const accepted = result !== false;
      for (const token of tokens) this._finishNativeWindowEventSuppression(token, accepted);
      return result;
    } catch (err) {
      for (const token of tokens) this._finishNativeWindowEventSuppression(token, false);
      throw err;
    }
  }

  _beginNativeWindowEventSuppression(windowId, type) {
    if (!windowId || !type) return null;
    const key = `${windowId}:${type}`;
    const existing = this._nativeWindowEventSuppressions.get(key);
    if (existing && existing.timer) clearTimeout(existing.timer);
    const entry = {
      key,
      expiresAt: Date.now() + NATIVE_SUPPRESSION_TTL_MS,
      timer: setTimeout(() => this._nativeWindowEventSuppressions.delete(key), NATIVE_SUPPRESSION_TTL_MS)
    };
    this._nativeWindowEventSuppressions.set(key, entry);
    return key;
  }

  _finishNativeWindowEventSuppression(token, accepted) {
    if (!token) return;
    if (accepted) return;
    const entry = this._nativeWindowEventSuppressions.get(token);
    if (entry && entry.timer) clearTimeout(entry.timer);
    this._nativeWindowEventSuppressions.delete(token);
  }

  _consumeNativeWindowEventSuppression(windowId, type) {
    const key = `${windowId}:${type}`;
    const entry = this._nativeWindowEventSuppressions.get(key);
    if (!entry) return false;
    if (Date.now() > entry.expiresAt) {
      if (entry.timer) clearTimeout(entry.timer);
      this._nativeWindowEventSuppressions.delete(key);
      return false;
    }
    return true;
  }

  _sendNativeWindowCmdDebounced(windowId, type, sendFn) {
    const key = `${windowId}:${type}`;
    const existing = this._nativeWindowBurstTimers.get(key);
    if (existing) clearTimeout(existing);
    const timer = setTimeout(() => {
      this._nativeWindowBurstTimers.delete(key);
      sendFn();
    }, NATIVE_BURST_DEBOUNCE_MS);
    this._nativeWindowBurstTimers.set(key, timer);
  }

  receiveFrame(frame) {
    if (!frame || typeof frame !== 'object') return;
    this._dispatch(frame);
  }

  receiveElectronMessage(msg) {
    if (!msg || !msg.type) return;
    switch (msg.type) {
      case 'openWindow':
        this._electronOpenWindow(msg);
        break;
      case 'renderWindow':
        this._electronRenderWindow(msg.windowId, msg.html || '');
        break;
      case 'closeWindow':
        this._electronCloseWindow(msg.windowId);
        break;
      case 'moveWindow':
        this._electronMoveWindow(msg.windowId, msg.x, msg.y);
        break;
      case 'resizeWindow':
        this._electronResizeWindow(msg.windowId, msg.width, msg.height);
        break;
      case 'focusWindow':
        this._electronFocusWindow(msg.windowId);
        break;
      case 'minimizeWindow':
        this._electronMinimizeWindow(msg.windowId);
        break;
      default:
        break;
    }
  }

  _electronOpenWindow(msg) {
    const windowId = String(msg.windowId || '');
    if (!windowId || !this.desktop) return;
    if (this._electronWindows.has(windowId)) {
      this._electronRenderWindow(windowId, msg.html || '');
      this._electronFocusWindow(windowId);
      return;
    }
    const winEl = document.createElement('div');
    winEl.className = 'wm-window';
    winEl.dataset.surfaceId = windowId;
    winEl.dataset.canonicalId = `${windowId}#root`;
    winEl.style.left = `${Number(msg.x) || 80}px`;
    winEl.style.top = `${Number(msg.y) || 80}px`;
    winEl.style.width = `${Number(msg.width) || 720}px`;
    winEl.style.height = `${Number(msg.height) || 480}px`;

    const titlebar = document.createElement('div');
    titlebar.className = 'wm-titlebar';
    const lights = document.createElement('div');
    lights.className = 'wm-traffic-lights';
    for (const [action, label] of [['close', 'x'], ['minimize', '-'], ['maximize', '+']]) {
      const btn = document.createElement('button');
      btn.dataset.action = action;
      btn.textContent = label;
      lights.appendChild(btn);
    }
    const title = document.createElement('div');
    title.className = 'wm-title';
    title.textContent = msg.title || windowId;
    titlebar.appendChild(lights);
    titlebar.appendChild(title);
    winEl.appendChild(titlebar);

    const body = document.createElement('div');
    body.className = 'wm-body';
    body.dataset.surfaceId = windowId;
    body.innerHTML = msg.html || '';
    winEl.appendChild(body);
    this.desktop.appendChild(winEl);
    this._electronWindows.set(windowId, {
      winEl,
      body,
      title,
      titleText: msg.title || windowId,
      minimized: false,
      restoreBounds: null
    });
    this._electronFocusWindow(windowId);
  }

  _electronRenderWindow(windowId, html) {
    const entry = this._electronWindows.get(String(windowId || ''));
    if (entry) entry.body.innerHTML = html;
  }

  _electronCloseWindow(windowId) {
    const key = String(windowId || '');
    const entry = this._electronWindows.get(key);
    if (!entry) return;
    entry.winEl.remove();
    this._electronWindows.delete(key);
    if (this._electronActiveWindowId === key) {
      this._electronActiveWindowId = '';
    }
    this._renderElectronTaskbar();
  }

  _electronMoveWindow(windowId, x, y) {
    const entry = this._electronWindows.get(String(windowId || ''));
    if (!entry) return;
    if (x != null) entry.winEl.style.left = `${Number(x) || 0}px`;
    if (y != null) entry.winEl.style.top = `${Number(y) || 0}px`;
  }

  _electronResizeWindow(windowId, width, height) {
    const entry = this._electronWindows.get(String(windowId || ''));
    if (!entry) return;
    if (width != null) entry.winEl.style.width = `${Number(width) || 1}px`;
    if (height != null) entry.winEl.style.height = `${Number(height) || 1}px`;
  }

  _electronFocusWindow(windowId) {
    const entry = this._electronWindows.get(String(windowId || ''));
    if (!entry) return;
    for (const item of this._electronWindows.values()) item.winEl.classList.remove('focused');
    entry.winEl.classList.add('focused');
    entry.winEl.style.display = '';
    entry.winEl.style.zIndex = String(++this._electronZCounter);
    entry.minimized = false;
    this._electronActiveWindowId = String(windowId || '');
    this._renderElectronTaskbar();
  }

  _electronMinimizeWindow(windowId) {
    const entry = this._electronWindows.get(String(windowId || ''));
    if (!entry) return;
    entry.winEl.style.display = 'none';
    entry.minimized = true;
    if (this._electronActiveWindowId === String(windowId || '')) {
      this._electronActiveWindowId = '';
    }
    this._renderElectronTaskbar();
  }

  _electronMaximizeWindow(windowId) {
    const entry = this._electronWindows.get(String(windowId || ''));
    if (!entry) return;
    if (!entry.restoreBounds) {
      entry.restoreBounds = {
        left: entry.winEl.style.left,
        top: entry.winEl.style.top,
        width: entry.winEl.style.width,
        height: entry.winEl.style.height
      };
    }
    entry.winEl.style.left = '0px';
    entry.winEl.style.top = '0px';
    entry.winEl.style.width = '100%';
    entry.winEl.style.height = '100%';
    this._electronFocusWindow(windowId);
  }

  _electronUnmaximizeWindow(windowId) {
    const entry = this._electronWindows.get(String(windowId || ''));
    if (!entry || !entry.restoreBounds) return;
    entry.winEl.style.left = entry.restoreBounds.left;
    entry.winEl.style.top = entry.restoreBounds.top;
    entry.winEl.style.width = entry.restoreBounds.width;
    entry.winEl.style.height = entry.restoreBounds.height;
    entry.restoreBounds = null;
    this._electronFocusWindow(windowId);
  }

  _electronSetWindowTitle(windowId, title) {
    const entry = this._electronWindows.get(String(windowId || ''));
    if (!entry) return;
    entry.titleText = title || String(windowId || '');
    entry.title.textContent = entry.titleText;
    this._renderElectronTaskbar();
  }

  _renderElectronTaskbar() {
    if (!this.taskbar) return;
    if (this._electronWindows.size === 0) {
      this.taskbar.innerHTML = '';
      return;
    }
    const running = [];
    for (const [windowId, entry] of this._electronWindows.entries()) {
      running.push({
        window_id: windowId,
        title: entry.titleText || windowId,
        minimized: !!entry.minimized,
        active: windowId === this._electronActiveWindowId
      });
    }
    this.renderTaskbarModel({ pinned: [], running, tray: [] });
  }

  // -------------------------------------------------------------------------
  // Ack timer
  // -------------------------------------------------------------------------

  _startAckTimer() {
    if (this._ackTimer) return;
    this._ackTimer = setInterval(() => {
      if (!this.renderer) return;
      const seq = this.renderer.lastSequence;
      if (seq >= 0) {
        this._send({
          t: 'ack', v: PROTOCOL_VERSION, s: this.sessionId, seq: null,
          payload: { last_applied_sequence: seq }
        });
      }
    }, ACK_INTERVAL_MS);
  }

  _stopAckTimer() {
    if (this._ackTimer) { clearInterval(this._ackTimer); this._ackTimer = null; }
  }

  // -------------------------------------------------------------------------
  // Ghost overlay (optimistic drag/resize)
  // -------------------------------------------------------------------------

  _createGhost(winEl) {
    const ghost = document.createElement('div');
    ghost.className = 'wm-ghost';
    const r = winEl.getBoundingClientRect();
    const dr = this.desktop.getBoundingClientRect();
    ghost.style.cssText = `
      position:absolute;
      left:${r.left - dr.left}px;top:${r.top - dr.top}px;
      width:${r.width}px;height:${r.height}px;
      border:2px dashed rgba(120,140,255,.7);
      pointer-events:none;box-sizing:border-box;z-index:99999;
    `;
    this.desktop.appendChild(ghost);
    return ghost;
  }

  _cancelGhost() {
    if (this.dragState && this.dragState.ghostEl) {
      this.dragState.ghostEl.remove();
      clearTimeout(this.dragState.timer);
      this.dragState = null;
    }
    if (this.resizeState && this.resizeState.ghostEl) {
      this.resizeState.ghostEl.remove();
      clearTimeout(this.resizeState.timer);
      this.resizeState = null;
    }
  }

  // -------------------------------------------------------------------------
  // Input / drag
  // -------------------------------------------------------------------------

  _onTitlebarMousedown(e, winEl) {
    if (e.target.closest('.wm-traffic-lights')) return;
    const surfaceId = winEl.dataset.surfaceId ?? '';
    const isElectronWindow = this.transport === 'electron-ipc' && this._electronWindows.has(surfaceId);
    if (isElectronWindow) {
      this._electronFocusWindow(surfaceId);
    }
    // Bring to front request (server decides z-order).
    this._sendWindowCmd('focus', {
      window_id_hint: surfaceId,
      ...(isElectronWindow ? { source: HOST_NATIVE_EVENT_SOURCE } : {})
    });

    const ghost = isElectronWindow ? null : this._createGhost(winEl);
    this.dragState = {
      surfaceId, ghostEl: ghost, timer: null, isElectronWindow,
      startX: e.clientX, startY: e.clientY,
      origLeft: parseFloat(winEl.style.left || 0),
      origTop:  parseFloat(winEl.style.top  || 0),
      winEl
    };
    e.preventDefault();
  }

  _onResizeMousedown(e, winEl, direction) {
    const surfaceId = winEl.dataset.surfaceId ?? '';
    const isElectronWindow = this.transport === 'electron-ipc' && this._electronWindows.has(surfaceId);
    if (isElectronWindow) {
      this._electronFocusWindow(surfaceId);
    }
    this._sendWindowCmd('focus', {
      window_id_hint: surfaceId,
      ...(isElectronWindow ? { source: HOST_NATIVE_EVENT_SOURCE } : {})
    });

    const ghost = isElectronWindow ? null : this._createGhost(winEl);
    const r = winEl.getBoundingClientRect();
    this.resizeState = {
      surfaceId, ghostEl: ghost, timer: null, direction, isElectronWindow,
      startX: e.clientX, startY: e.clientY,
      origW: r.width, origH: r.height,
      winEl
    };
    e.preventDefault();
  }

  _onMousemove(e) {
    if (this.dragState) {
      const ds = this.dragState;
      const dx = e.clientX - ds.startX;
      const dy = e.clientY - ds.startY;
      const nextX = ds.origLeft + dx;
      const nextY = ds.origTop + dy;
      if (ds.isElectronWindow) {
        this._electronMoveWindow(ds.surfaceId, Math.round(nextX), Math.round(nextY));
      } else if (ds.ghostEl) {
        // Optimistic: ghost is cosmetic; server patches or mouseup reconcile.
        ds.ghostEl.style.left = nextX + 'px';
        ds.ghostEl.style.top  = nextY + 'px';
      }
    }
    if (this.resizeState) {
      const rs = this.resizeState;
      const dx = e.clientX - rs.startX;
      const dy = e.clientY - rs.startY;
      const dir = rs.direction;
      const minW = 200, minH = 120;
      let w = rs.origW, h = rs.origH;
      if (dir.includes('e')) w = Math.max(minW, rs.origW + dx);
      if (dir.includes('s')) h = Math.max(minH, rs.origH + dy);
      if (dir.includes('w')) w = Math.max(minW, rs.origW - dx);
      if (dir === 'n' || dir.includes('n')) h = Math.max(minH, rs.origH - dy);
      if (rs.isElectronWindow) {
        this._electronResizeWindow(rs.surfaceId, Math.round(w), Math.round(h));
      } else if (rs.ghostEl) {
        rs.ghostEl.style.width  = w + 'px';
        rs.ghostEl.style.height = h + 'px';
      }
    }
  }

  _onMouseup(e) {
    if (this.dragState) {
      const ds = this.dragState;
      const dx = e.clientX - ds.startX;
      const dy = e.clientY - ds.startY;
      const newX = ds.origLeft + dx;
      const newY = ds.origTop  + dy;
      if (this.transport === 'electron-ipc' && this._electronWindows.has(ds.surfaceId)) {
        this._electronMoveWindow(ds.surfaceId, Math.round(newX), Math.round(newY));
      }
      // Send authoritative move request; server will reconcile and patch back.
      // window_id_hint is a HINT only; server resolves via UiWindowSurfaceRegistry.
      this._sendWindowCmd('move', {
        window_id_hint: ds.surfaceId,
        ...(ds.isElectronWindow ? { source: HOST_NATIVE_EVENT_SOURCE } : {}),
        x: Math.round(newX),
        y: Math.round(newY)
      });
      if (ds.ghostEl) ds.ghostEl.remove();
      clearTimeout(ds.timer);
      this.dragState = null;
    }
    if (this.resizeState) {
      const rs = this.resizeState;
      const dx = e.clientX - rs.startX;
      const dy = e.clientY - rs.startY;
      const dir = rs.direction;
      const minW = 200, minH = 120;
      let w = rs.origW, h = rs.origH;
      if (dir.includes('e')) w = Math.max(minW, rs.origW + dx);
      if (dir.includes('s')) h = Math.max(minH, rs.origH + dy);
      if (dir.includes('w')) w = Math.max(minW, rs.origW - dx);
      if (dir === 'n' || dir.includes('n')) h = Math.max(minH, rs.origH - dy);
      if (this.transport === 'electron-ipc' && this._electronWindows.has(rs.surfaceId)) {
        this._electronResizeWindow(rs.surfaceId, Math.round(w), Math.round(h));
      }
      this._sendWindowCmd('resize', {
        window_id_hint: rs.surfaceId,
        ...(rs.isElectronWindow ? { source: HOST_NATIVE_EVENT_SOURCE } : {}),
        w: Math.round(w),
        h: Math.round(h)
      });
      if (rs.ghostEl) rs.ghostEl.remove();
      clearTimeout(rs.timer);
      this.resizeState = null;
    }
  }

  // -------------------------------------------------------------------------
  // Global event binding
  // -------------------------------------------------------------------------

  _bindGlobalEvents() {
    document.addEventListener('mousemove', (e) => this._onMousemove(e));
    document.addEventListener('mouseup',   (e) => this._onMouseup(e));

    document.addEventListener('mousedown', (e) => {
      const titlebar = e.target.closest('.wm-titlebar');
      if (titlebar) {
        const winEl = titlebar.closest('.wm-window');
        if (winEl) { this._onTitlebarMousedown(e, winEl); return; }
      }
      const handle = e.target.closest('.wm-resize-handle');
      if (handle) {
        const winEl = handle.closest('.wm-window');
        if (winEl) { this._onResizeMousedown(e, winEl, handle.dataset.direction); return; }
      }
      // Click anywhere on a window — request focus.
      const win = e.target.closest('.wm-window');
      if (win) {
        const surfaceId = win.dataset.surfaceId ?? win.dataset.canonicalId ?? '';
        const isElectronWindow = this.transport === 'electron-ipc' && this._electronWindows.has(surfaceId);
        if (this.transport === 'electron-ipc' && this._electronWindows.has(surfaceId)) {
          this._electronFocusWindow(surfaceId);
        }
        if (surfaceId) {
          this._sendWindowCmd('focus', {
            window_id_hint: surfaceId,
            ...(isElectronWindow ? { source: HOST_NATIVE_EVENT_SOURCE } : {})
          });
        }
      }
    });

    // Traffic-light buttons.
    document.addEventListener('click', (e) => {
      const btn = e.target.closest('.wm-traffic-lights button');
      if (!btn) return;
      const win = btn.closest('.wm-window');
      if (!win) return;
      const surfaceId = win.dataset.surfaceId ?? '';
      const action = btn.dataset.action;
      if (this.transport === 'electron-ipc' && this._electronWindows.has(surfaceId)) {
        if (action === 'close') this._electronCloseWindow(surfaceId);
        else if (action === 'minimize') this._electronMinimizeWindow(surfaceId);
        else if (action === 'maximize') this._electronMaximizeWindow(surfaceId);
      }
      const commandPayload = {
        window_id_hint: surfaceId,
        ...(this.transport === 'electron-ipc' && this._electronWindows.has(surfaceId) ? { source: HOST_NATIVE_EVENT_SOURCE } : {})
      };
      if      (action === 'close')    this._sendWindowCmd('close', commandPayload);
      else if (action === 'minimize') this._sendWindowCmd('minimize', commandPayload);
      else if (action === 'maximize') this._sendWindowCmd('maximize', commandPayload);
    });

    // Forward pointer events inside windows as input_event frames.
    document.addEventListener('pointerdown', (e) => {
      const widget = e.target.closest('[data-canonical-id]');
      if (!widget) return;
      const cid = widget.dataset.canonicalId ?? '';
      const hash = cid.indexOf('#');
      const surfId = hash >= 0 ? cid.slice(0, hash) : cid;
      const widId  = hash >= 0 ? cid.slice(hash + 1) : '';
      const r = this.desktop ? this.desktop.getBoundingClientRect() : { left: 0, top: 0 };
      this._sendInputEvent(surfId, widId, {
        kind: 'pointer_down',
        x: Math.round(e.clientX - r.left),
        y: Math.round(e.clientY - r.top),
        button: e.button
      });
    });

    document.addEventListener('pointerup', (e) => {
      const widget = e.target.closest('[data-canonical-id]');
      if (!widget) return;
      const cid = widget.dataset.canonicalId ?? '';
      const hash = cid.indexOf('#');
      const surfId = hash >= 0 ? cid.slice(0, hash) : cid;
      const widId  = hash >= 0 ? cid.slice(hash + 1) : '';
      const r = this.desktop ? this.desktop.getBoundingClientRect() : { left: 0, top: 0 };
      this._sendInputEvent(surfId, widId, {
        kind: 'pointer_up',
        x: Math.round(e.clientX - r.left),
        y: Math.round(e.clientY - r.top),
        button: e.button
      });
    });

    document.addEventListener('pointermove', (e) => {
      // Only forward when inside a known surface.
      const widget = e.target.closest('[data-surface-id]');
      if (!widget) return;
      const surfId = widget.dataset.surfaceId ?? '';
      if (!surfId) return;
      const r = this.desktop ? this.desktop.getBoundingClientRect() : { left: 0, top: 0 };
      this._sendInputEvent(surfId, '', {
        kind: 'pointer_move',
        x: Math.round(e.clientX - r.left),
        y: Math.round(e.clientY - r.top)
      });
    });

    document.addEventListener('wheel', (e) => {
      const widget = e.target.closest('[data-canonical-id]');
      if (!widget) return;
      const cid = widget.dataset.canonicalId ?? '';
      const hash = cid.indexOf('#');
      const surfId = hash >= 0 ? cid.slice(0, hash) : cid;
      const widId  = hash >= 0 ? cid.slice(hash + 1) : '';
      this._sendInputEvent(surfId, widId, {
        kind: 'wheel',
        delta_x: Math.round(e.deltaX),
        delta_y: Math.round(e.deltaY)
      });
    });

    document.addEventListener('keydown', (e) => {
      if (!this.renderer || !this.renderer.activeSurface) return;
      const surfId = this.renderer.activeSurface;
      this._sendInputEvent(surfId, '', {
        kind: 'key_down',
        key: e.key,
        key_code: e.keyCode,
        modifiers: _modifiers(e),
        repeat: e.repeat
      });
    });

    document.addEventListener('keyup', (e) => {
      if (!this.renderer || !this.renderer.activeSurface) return;
      const surfId = this.renderer.activeSurface;
      this._sendInputEvent(surfId, '', {
        kind: 'key_up',
        key: e.key,
        key_code: e.keyCode,
        modifiers: _modifiers(e)
      });
    });

    document.addEventListener('input', (e) => {
      const widget = e.target.closest('[data-canonical-id]');
      if (!widget) return;
      const cid = widget.dataset.canonicalId ?? '';
      const hash = cid.indexOf('#');
      const surfId = hash >= 0 ? cid.slice(0, hash) : cid;
      const widId  = hash >= 0 ? cid.slice(hash + 1) : '';
      this._sendInputEvent(surfId, widId, {
        kind: 'text_input',
        text: e.target.value ?? e.data ?? ''
      });
    });
  }

  // -------------------------------------------------------------------------
  // Toast (error display)
  // -------------------------------------------------------------------------

  _showToast(msg) {
    const t = document.createElement('div');
    t.className = 'wm-toast';
    t.textContent = msg;
    document.body.appendChild(t);
    setTimeout(() => t.remove(), 4000);
  }
}

// -------------------------------------------------------------------------
// Helpers
// -------------------------------------------------------------------------

function _modifiers(e) {
  return (e.shiftKey ? 1 : 0) | (e.ctrlKey ? 2 : 0) | (e.altKey ? 4 : 0) | (e.metaKey ? 8 : 0);
}

function _escapeHtml(value) {
  return String(value || '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

function _escapeAttr(value) {
  return _escapeHtml(value).replace(/`/g, '&#96;');
}

// Global instance — initialized by inline boot script.
var simpleWM = null;
