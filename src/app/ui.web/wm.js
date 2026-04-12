// Window Manager for Simple Language Web UI
//
// Client-side multi-window management with drag, resize, z-order,
// minimize/maximize, and a taskbar dock. Controlled via WebSocket
// messages from the Simple process.

class SimpleWindowManager {
    constructor() {
        this.windows = new Map();
        this.nextZ = 10;
        this.desktop = document.getElementById('wm-desktop');
        this.taskbar = document.getElementById('wm-taskbar');
        this.activeId = null;
        this.dragState = null;
        this.resizeState = null;
        this._bindGlobalEvents();
    }

    // -- Window lifecycle ---------------------------------------------------

    addWindow(id, title, html, opts) {
        opts = opts || {};
        const x = opts.x != null ? opts.x : 100 + (this.windows.size * 40);
        const y = opts.y != null ? opts.y : 80 + (this.windows.size * 30);
        const w = opts.w || opts.width || 600;
        const h = opts.h || opts.height || 400;

        // Remove existing window with same id
        if (this.windows.has(id)) {
            this.removeWindow(id);
        }

        const el = document.createElement('div');
        el.className = 'wm-window';
        el.id = 'wm-win-' + id;
        el.dataset.windowId = id;
        el.style.left = x + 'px';
        el.style.top = y + 'px';
        el.style.width = w + 'px';
        el.style.height = h + 'px';
        el.style.zIndex = this.nextZ;

        // Title bar
        const titlebar = document.createElement('div');
        titlebar.className = 'wm-titlebar';
        titlebar.dataset.windowId = id;

        const lights = document.createElement('div');
        lights.className = 'wm-traffic-lights';
        lights.innerHTML =
            '<button class="wm-btn-close" data-action="close" data-window-id="' + id + '"></button>' +
            '<button class="wm-btn-minimize" data-action="minimize" data-window-id="' + id + '"></button>' +
            '<button class="wm-btn-maximize" data-action="maximize" data-window-id="' + id + '"></button>';

        const titleText = document.createElement('span');
        titleText.className = 'wm-title-text';
        titleText.textContent = title || id;

        titlebar.appendChild(lights);
        titlebar.appendChild(titleText);

        // Content area
        const content = document.createElement('div');
        content.className = 'wm-content';
        content.id = 'wm-content-' + id;
        if (html) {
            this._setContent(content, html);
        }

        // Resize handles
        const directions = ['n', 'ne', 'e', 'se', 's', 'sw', 'w', 'nw'];
        directions.forEach(dir => {
            const handle = document.createElement('div');
            handle.className = 'wm-resize-handle wm-resize-' + dir;
            handle.dataset.windowId = id;
            handle.dataset.direction = dir;
            el.appendChild(handle);
        });

        el.appendChild(titlebar);
        el.appendChild(content);
        this.desktop.appendChild(el);

        const state = {
            el: el,
            contentEl: content,
            titleEl: titleText,
            x: x, y: y, w: w, h: h,
            zIndex: this.nextZ,
            minimized: false,
            maximized: false,
            preMaxRect: null,
            title: title || id
        };
        this.nextZ++;
        this.windows.set(id, state);
        this.focusWindow(id);
        this.renderTaskbar();
    }

    removeWindow(id) {
        const state = this.windows.get(id);
        if (!state) return;
        state.el.remove();
        this.windows.delete(id);
        if (this.activeId === id) {
            this.activeId = null;
            // Focus topmost remaining
            let topZ = -1;
            this.windows.forEach((s, wid) => {
                if (!s.minimized && s.zIndex > topZ) {
                    topZ = s.zIndex;
                    this.activeId = wid;
                }
            });
            this._updateFocusClasses();
        }
        this.renderTaskbar();
    }

    updateContent(id, html) {
        const state = this.windows.get(id);
        if (!state) return;
        const scrollTop = state.contentEl.scrollTop;
        this._setContent(state.contentEl, html);
        state.contentEl.scrollTop = scrollTop;
    }

    // -- Focus / z-order ----------------------------------------------------

    focusWindow(id) {
        const state = this.windows.get(id);
        if (!state) return;
        if (state.minimized) {
            state.minimized = false;
            state.el.classList.remove('minimized');
        }
        state.zIndex = this.nextZ++;
        state.el.style.zIndex = state.zIndex;
        this.activeId = id;
        this._updateFocusClasses();
        this.renderTaskbar();
        this._sendEvent({ type: 'windowFocused', windowId: id });
    }

    // -- Minimize / Maximize ------------------------------------------------

    minimizeWindow(id) {
        const state = this.windows.get(id);
        if (!state) return;
        state.minimized = true;
        state.el.classList.add('minimized');
        if (this.activeId === id) {
            this.activeId = null;
            let topZ = -1;
            this.windows.forEach((s, wid) => {
                if (!s.minimized && s.zIndex > topZ) {
                    topZ = s.zIndex;
                    this.activeId = wid;
                }
            });
            this._updateFocusClasses();
        }
        this.renderTaskbar();
        this._sendEvent({ type: 'windowMinimize', windowId: id });
    }

    maximizeWindow(id) {
        const state = this.windows.get(id);
        if (!state) return;
        if (state.maximized) {
            // Restore
            state.maximized = false;
            state.el.classList.remove('maximized');
            if (state.preMaxRect) {
                state.x = state.preMaxRect.x;
                state.y = state.preMaxRect.y;
                state.w = state.preMaxRect.w;
                state.h = state.preMaxRect.h;
                state.el.style.left = state.x + 'px';
                state.el.style.top = state.y + 'px';
                state.el.style.width = state.w + 'px';
                state.el.style.height = state.h + 'px';
                state.preMaxRect = null;
            }
        } else {
            state.preMaxRect = { x: state.x, y: state.y, w: state.w, h: state.h };
            state.maximized = true;
            state.el.classList.add('maximized');
        }
        this.focusWindow(id);
    }

    // -- Taskbar ------------------------------------------------------------

    renderTaskbar() {
        if (!this.taskbar) return;
        this.taskbar.innerHTML = '';
        this.windows.forEach((state, id) => {
            const item = document.createElement('div');
            item.className = 'wm-taskbar-item';
            if (id === this.activeId) item.classList.add('active');
            if (state.minimized) item.classList.add('minimized');
            item.textContent = state.title;
            item.dataset.windowId = id;
            item.addEventListener('click', () => {
                if (state.minimized) {
                    this.focusWindow(id);
                } else if (id === this.activeId) {
                    this.minimizeWindow(id);
                } else {
                    this.focusWindow(id);
                }
            });
            this.taskbar.appendChild(item);
        });
    }

    // -- Drag handling ------------------------------------------------------

    _onTitlebarMousedown(e, windowId) {
        if (e.target.closest('.wm-traffic-lights')) return;
        const state = this.windows.get(windowId);
        if (!state || state.maximized) return;
        this.focusWindow(windowId);
        this.dragState = {
            windowId: windowId,
            startX: e.clientX,
            startY: e.clientY,
            origX: state.x,
            origY: state.y
        };
        e.preventDefault();
    }

    // -- Resize handling ----------------------------------------------------

    _onResizeMousedown(e, windowId, direction) {
        const state = this.windows.get(windowId);
        if (!state || state.maximized) return;
        this.focusWindow(windowId);
        this.resizeState = {
            windowId: windowId,
            direction: direction,
            startX: e.clientX,
            startY: e.clientY,
            origX: state.x,
            origY: state.y,
            origW: state.w,
            origH: state.h
        };
        e.preventDefault();
    }

    // -- Global mouse events ------------------------------------------------

    _onMousemove(e) {
        if (this.dragState) {
            const ds = this.dragState;
            const state = this.windows.get(ds.windowId);
            if (!state) return;
            const dx = e.clientX - ds.startX;
            const dy = e.clientY - ds.startY;
            state.x = ds.origX + dx;
            state.y = ds.origY + dy;
            state.el.style.left = state.x + 'px';
            state.el.style.top = state.y + 'px';
        }
        if (this.resizeState) {
            const rs = this.resizeState;
            const state = this.windows.get(rs.windowId);
            if (!state) return;
            const dx = e.clientX - rs.startX;
            const dy = e.clientY - rs.startY;
            const minW = 200;
            const minH = 120;
            const dir = rs.direction;

            let newX = rs.origX, newY = rs.origY;
            let newW = rs.origW, newH = rs.origH;

            if (dir.includes('e')) newW = Math.max(minW, rs.origW + dx);
            if (dir.includes('s')) newH = Math.max(minH, rs.origH + dy);
            if (dir.includes('w')) {
                newW = Math.max(minW, rs.origW - dx);
                if (newW > minW) newX = rs.origX + dx;
            }
            if (dir.includes('n') && dir !== 'ne' && dir !== 'nw') {
                newH = Math.max(minH, rs.origH - dy);
                if (newH > minH) newY = rs.origY + dy;
            }
            if (dir === 'n') {
                newH = Math.max(minH, rs.origH - dy);
                if (newH > minH) newY = rs.origY + dy;
            }
            if (dir === 'nw') {
                newW = Math.max(minW, rs.origW - dx);
                newH = Math.max(minH, rs.origH - dy);
                if (newW > minW) newX = rs.origX + dx;
                if (newH > minH) newY = rs.origY + dy;
            }
            if (dir === 'ne') {
                newW = Math.max(minW, rs.origW + dx);
                newH = Math.max(minH, rs.origH - dy);
                if (newH > minH) newY = rs.origY + dy;
            }

            state.x = newX;
            state.y = newY;
            state.w = newW;
            state.h = newH;
            state.el.style.left = newX + 'px';
            state.el.style.top = newY + 'px';
            state.el.style.width = newW + 'px';
            state.el.style.height = newH + 'px';
        }
    }

    _onMouseup(e) {
        if (this.dragState) {
            const ds = this.dragState;
            const state = this.windows.get(ds.windowId);
            if (state) {
                this._sendEvent({
                    type: 'windowMoved',
                    windowId: ds.windowId,
                    x: state.x,
                    y: state.y
                });
            }
            this.dragState = null;
        }
        if (this.resizeState) {
            const rs = this.resizeState;
            const state = this.windows.get(rs.windowId);
            if (state) {
                this._sendEvent({
                    type: 'windowResized',
                    windowId: rs.windowId,
                    width: state.w,
                    height: state.h
                });
            }
            this.resizeState = null;
        }
    }

    // -- WebSocket message dispatch -----------------------------------------

    handleMessage(data) {
        switch (data.type) {
            case 'openWindow':
                this.addWindow(
                    data.windowId || 'win_' + Date.now(),
                    data.title || 'Window',
                    data.html || '',
                    { x: data.x, y: data.y, w: data.width, h: data.height }
                );
                break;
            case 'closeWindow':
                this.removeWindow(data.windowId);
                break;
            case 'renderWindow':
                this.updateContent(data.windowId, data.html || '');
                break;
            case 'moveWindow':
                this._moveFromServer(data.windowId, data.x, data.y);
                break;
            case 'resizeWindow':
                this._resizeFromServer(data.windowId, data.width, data.height);
                break;
            case 'focusWindow':
                this.focusWindow(data.windowId);
                break;
            case 'minimizeWindow':
                this.minimizeWindow(data.windowId);
                break;
            case 'render':
                // Legacy single-window mode: create or update main window
                if (!this.windows.has('main')) {
                    this.addWindow('main', document.title || 'Simple UI', data.html, {
                        x: 100, y: 60, w: 900, h: 600
                    });
                } else {
                    this.updateContent('main', data.html);
                }
                break;
        }
    }

    // -- Internal helpers ---------------------------------------------------

    _setContent(el, html) {
        // Extract styles from the HTML and inject into content
        const parser = new DOMParser();
        const doc = parser.parseFromString(html, 'text/html');
        const styles = doc.querySelectorAll('style');
        const body = doc.body;

        // Remove existing injected styles in content
        el.querySelectorAll('style.wm-injected').forEach(s => s.remove());

        // Inject styles
        styles.forEach(style => {
            const s = document.createElement('style');
            s.className = 'wm-injected';
            s.textContent = style.textContent;
            el.appendChild(s);
        });

        // Set body content
        if (body) {
            // Check for #app wrapper
            const appDiv = body.querySelector('#app');
            el.innerHTML = '';
            styles.forEach(style => {
                const s = document.createElement('style');
                s.className = 'wm-injected';
                s.textContent = style.textContent;
                el.appendChild(s);
            });
            if (appDiv) {
                el.insertAdjacentHTML('beforeend', appDiv.innerHTML);
            } else {
                el.insertAdjacentHTML('beforeend', body.innerHTML);
            }
        } else {
            el.innerHTML = html;
        }
    }

    _updateFocusClasses() {
        this.windows.forEach((state, id) => {
            if (id === this.activeId) {
                state.el.classList.add('focused');
            } else {
                state.el.classList.remove('focused');
            }
        });
    }

    _moveFromServer(id, x, y) {
        const state = this.windows.get(id);
        if (!state) return;
        state.x = x;
        state.y = y;
        state.el.style.left = x + 'px';
        state.el.style.top = y + 'px';
    }

    _resizeFromServer(id, w, h) {
        const state = this.windows.get(id);
        if (!state) return;
        state.w = w;
        state.h = h;
        state.el.style.width = w + 'px';
        state.el.style.height = h + 'px';
    }

    _sendEvent(msg) {
        if (typeof sendEvent === 'function') {
            sendEvent(msg);
        } else if (typeof ws !== 'undefined' && ws && ws.readyState === 1) {
            ws.send(JSON.stringify(msg));
        }
    }

    _bindGlobalEvents() {
        document.addEventListener('mousemove', (e) => this._onMousemove(e));
        document.addEventListener('mouseup', (e) => this._onMouseup(e));

        // Delegate titlebar drag
        document.addEventListener('mousedown', (e) => {
            const titlebar = e.target.closest('.wm-titlebar');
            if (titlebar) {
                this._onTitlebarMousedown(e, titlebar.dataset.windowId);
                return;
            }
            // Delegate resize handle
            const handle = e.target.closest('.wm-resize-handle');
            if (handle) {
                this._onResizeMousedown(e, handle.dataset.windowId, handle.dataset.direction);
                return;
            }
            // Click on window brings to front
            const win = e.target.closest('.wm-window');
            if (win && win.dataset.windowId !== this.activeId) {
                this.focusWindow(win.dataset.windowId);
            }
        });

        // Delegate traffic light button clicks
        document.addEventListener('click', (e) => {
            const btn = e.target.closest('.wm-traffic-lights button');
            if (!btn) return;
            const windowId = btn.dataset.windowId;
            const action = btn.dataset.action;
            if (action === 'close') {
                this.removeWindow(windowId);
                this._sendEvent({ type: 'windowClose', windowId: windowId });
            } else if (action === 'minimize') {
                this.minimizeWindow(windowId);
            } else if (action === 'maximize') {
                this.maximizeWindow(windowId);
            }
        });
    }
}

// Global instance — initialized by inline boot script
var simpleWM = null;
