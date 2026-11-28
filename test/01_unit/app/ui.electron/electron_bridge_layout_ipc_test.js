const assert = require('assert');
const fs = require('fs');
const Module = require('module');
const path = require('path');
const vm = require('vm');

const { electronWmInitScript } = require('../../../../src/app/ui.electron/bridge.js');
const { renderEnvelopeScript } = require('../../../../src/app/ui.electron/bridge_envelopes.js');

// 1. bridge.js: #wm-desktop must allow pointer pass-through while .wm-window accepts events.
{
  const wmScript = electronWmInitScript();
  assert(
    wmScript.includes('#wm-desktop{position:fixed;inset:0;overflow:hidden;isolation:isolate;pointer-events:none}'),
    'expected #wm-desktop CSS rule to include pointer-events:none'
  );
  assert(
    wmScript.includes('#wm-desktop .wm-window{position:absolute;display:flex;flex-direction:column;overflow:hidden;pointer-events:auto}'),
    'expected #wm-desktop .wm-window CSS rule to include pointer-events:auto'
  );
}

// 2. bridge_envelopes.js: renderEnvelopeScript preserves focus, selection, window scroll, and per-id scrollTop.
{
  const script = renderEnvelopeScript({
    target: 'electron',
    surface_id: 'main',
    width: 1280,
    height: 720,
    css: '.widget-tabs{display:flex}',
    body_html: '<div id="scroll_area"></div><input id="search_input" value="hello" />'
  });

  let focusCalls = [];
  let selectionCalls = [];
  let windowScrollCalls = [];
  let dispatchedEvents = [];

  const oldInput = {
    id: 'search_input',
    tagName: 'INPUT',
    selectionStart: 2,
    selectionEnd: 5
  };
  const oldScroll = {
    id: 'scroll_area',
    scrollTop: 140
  };
  const newInput = {
    id: 'search_input',
    tagName: 'INPUT',
    focus() {
      focusCalls.push(this.id);
    },
    setSelectionRange(start, end) {
      selectionCalls.push([start, end]);
    }
  };
  const newScroll = {
    id: 'scroll_area',
    scrollTop: 0
  };

  let innerHtmlAssigned = false;
  const appEl = {
    id: 'app',
    scrollTop: 48,
    querySelectorAll(selector) {
      assert.strictEqual(selector, '[id]');
      return innerHtmlAssigned ? [] : [oldScroll, oldInput];
    },
    set innerHTML(val) {
      innerHtmlAssigned = true;
      this._html = val;
    },
    get innerHTML() {
      return this._html || '';
    }
  };

  const styleEl = { id: 'simple-server-css', textContent: '' };
  let styleAttached = false;

  const sandbox = {
    JSON,
    Object,
    CustomEvent: function CustomEvent(name, opts) {
      this.type = name;
      this.detail = opts ? opts.detail : undefined;
    },
    document: {
      activeElement: oldInput,
      head: {
        appendChild(node) {
          if (node === styleEl) styleAttached = true;
        }
      },
      body: { innerHTML: '' },
      createElement(tag) {
        assert.strictEqual(tag, 'style');
        return styleEl;
      },
      getElementById(id) {
        if (id === 'simple-server-css') return styleAttached ? styleEl : null;
        if (id === 'app') return appEl;
        if (id === 'search_input') return innerHtmlAssigned ? newInput : oldInput;
        if (id === 'scroll_area') return innerHtmlAssigned ? newScroll : oldScroll;
        return null;
      }
    },
    window: {
      scrollX: 12,
      scrollY: 220,
      scrollTo(x, y) {
        windowScrollCalls.push([x, y]);
      },
      dispatchEvent(ev) {
        dispatchedEvents.push(ev);
      }
    }
  };

  vm.runInNewContext(script, sandbox);

  assert.strictEqual(innerHtmlAssigned, true);
  assert.strictEqual(appEl.scrollTop, 48);
  assert.strictEqual(newScroll.scrollTop, 140);
  assert.deepStrictEqual(windowScrollCalls, [[12, 220]]);
  assert.deepStrictEqual(focusCalls, ['search_input']);
  assert.deepStrictEqual(selectionCalls, [[2, 5]]);
  assert.strictEqual(dispatchedEvents.length, 1);
  assert.strictEqual(dispatchedEvents[0].type, 'simple-render');
}

// 3. preload.js: action/list/select/input/focusin/keydown routing.
{
  const sentEnvelopes = [];
  const docListeners = {};
  const winListeners = {};
  let exposedApi = null;

  const origLoad = Module._load;
  Module._load = function(request, parent, isMain) {
    if (request === 'electron') {
      return {
        contextBridge: {
          exposeInMainWorld(name, api) {
            assert.strictEqual(name, 'simpleElectron');
            exposedApi = api;
          }
        },
        ipcRenderer: {
          send(channel, envelope) {
            assert.strictEqual(channel, 'simple-input');
            sentEnvelopes.push(envelope);
          }
        }
      };
    }
    return origLoad.apply(this, arguments);
  };

  global.window = {
    addEventListener(name, fn) {
      winListeners[name] = fn;
    }
  };
  global.document = {
    addEventListener(name, fn) {
      docListeners[name] = fn;
    }
  };

  const preloadPath = path.resolve(__dirname, '../../../../src/app/ui.electron/preload.js');
  delete require.cache[preloadPath];
  try {
    require(preloadPath);
  } finally {
    Module._load = origLoad;
  }

  assert(typeof winListeners.DOMContentLoaded === 'function');
  assert(exposedApi && typeof exposedApi.sendInput === 'function');
  winListeners.DOMContentLoaded();

  // Click on [data-action]
  docListeners.click({
    target: {
      closest(sel) {
        if (sel === '[data-action]') {
          return { getAttribute: attr => (attr === 'data-action' ? 'tab_nav_tabs_1' : '') };
        }
        return null;
      }
    }
  });
  assert.deepStrictEqual(sentEnvelopes.pop(), {
    type: 'input', target: 'electron', surface_id: 'main',
    event_type: 'action', target_id: '', key: '', value: 'tab_nav_tabs_1',
    x: 0, y: 0, dx: 0, dy: 0, button: ''
  });

  // Click on .list-item[data-index] inside .widget-list[id] (no [data-action])
  const fakeList = { id: 'sidebar_list' };
  const fakeListItem = {
    getAttribute: attr => (attr === 'data-index' ? '2' : ''),
    closest(sel) {
      return sel === '.widget-list[id]' ? fakeList : null;
    }
  };
  docListeners.click({
    target: {
      closest(sel) {
        if (sel === '[data-action]') return null;
        if (sel === '.list-item[data-index]') return fakeListItem;
        return null;
      }
    }
  });
  assert.deepStrictEqual(sentEnvelopes.pop(), {
    type: 'input', target: 'electron', surface_id: 'main',
    event_type: 'action', target_id: '', key: '', value: 'select_sidebar_list_2',
    x: 0, y: 0, dx: 0, dy: 0, button: ''
  });

  // Input event on <input id="search_input">
  const fakeInput = { tagName: 'INPUT', id: 'search_input', value: 'typed' };
  docListeners.input({
    target: {
      closest(sel) {
        return sel.includes('input[id]') ? fakeInput : null;
      }
    }
  });
  assert.deepStrictEqual(sentEnvelopes.pop(), {
    type: 'input', target: 'electron', surface_id: 'main',
    event_type: 'input', target_id: 'search_input', key: '', value: 'typed',
    x: 0, y: 0, dx: 0, dy: 0, button: ''
  });

  // Change event on <select id="mode_dropdown">
  const fakeSelect = { tagName: 'SELECT', id: 'mode_dropdown', selectedIndex: 1 };
  docListeners.change({
    target: {
      closest(sel) {
        return sel.includes('select[id]') ? fakeSelect : null;
      }
    }
  });
  assert.deepStrictEqual(sentEnvelopes.pop(), {
    type: 'input', target: 'electron', surface_id: 'main',
    event_type: 'action', target_id: '', key: '', value: 'select_mode_dropdown_1',
    x: 0, y: 0, dx: 0, dy: 0, button: ''
  });

  // Focusin on interactive control with id
  docListeners.focusin({
    target: {
      closest(sel) {
        return sel.includes('button[id]') ? { id: 'action_btn' } : null;
      }
    }
  });
  assert.deepStrictEqual(sentEnvelopes.pop(), {
    type: 'input', target: 'electron', surface_id: 'main',
    event_type: 'focus', target_id: 'action_btn', key: '', value: '',
    x: 0, y: 0, dx: 0, dy: 0, button: ''
  });

  // Keydown inside input/textarea/select: drop character keys, forward Escape and Tab
  const countBeforeFormKeys = sentEnvelopes.length;
  docListeners.keydown({
    key: 'a',
    target: { matches: sel => sel === 'input, textarea, select' }
  });
  docListeners.keydown({
    key: 'Enter',
    target: { matches: sel => sel === 'input, textarea, select' }
  });
  assert.strictEqual(sentEnvelopes.length, countBeforeFormKeys);

  docListeners.keydown({
    key: 'Escape',
    target: { matches: sel => sel === 'input, textarea, select' }
  });
  assert.strictEqual(sentEnvelopes.pop().key, 'Escape');

  docListeners.keydown({
    key: 'Tab',
    target: { matches: sel => sel === 'input, textarea, select' }
  });
  assert.strictEqual(sentEnvelopes.pop().key, 'Tab');

  // Keydown outside form control forwards character keys normally
  docListeners.keydown({
    key: 'j',
    target: { matches: () => false }
  });
  assert.strictEqual(sentEnvelopes.pop().key, 'j');

  delete global.window;
  delete global.document;
}

console.log('electron_bridge_layout_ipc_test ok');
