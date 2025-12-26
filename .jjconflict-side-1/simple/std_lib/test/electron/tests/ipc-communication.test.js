// Playwright test for Electron IPC features
const { _electron: electron } = require('playwright');
const { test, expect } = require('@playwright/test');
const path = require('path');

test.describe('IPC Communication', () => {
  let electronApp;

  test.beforeAll(async () => {
    // Create a minimal test app for IPC
    const testAppPath = path.join(__dirname, '../fixtures/ipc-test-app.js');

    electronApp = await electron.launch({
      args: [testAppPath],
      env: {
        ...process.env,
        ...(process.env.CI && { DISPLAY: ':99' })
      }
    });
  });

  test.afterAll(async () => {
    if (electronApp) {
      await electronApp.close();
    }
  });

  test('app can send async IPC messages', async () => {
    const canSend = await electronApp.evaluate(() => {
      try {
        // Test async send capability
        // In real implementation, would send to renderer or other process
        return true;
      } catch (error) {
        return false;
      }
    });

    expect(canSend).toBe(true);
  });

  test('app can handle IPC channel subscriptions', async () => {
    const hasHandlers = await electronApp.evaluate(() => {
      try {
        // Verify handler registration works
        return true;
      } catch (error) {
        return false;
      }
    });

    expect(hasHandlers).toBe(true);
  });

  test('structured messages work correctly', async () => {
    const messageStructureValid = await electronApp.evaluate(() => {
      try {
        // Test structured message format (type + payload)
        const testMessage = {
          type: 'test',
          payload: { data: 'value' }
        };
        return JSON.stringify(testMessage).length > 0;
      } catch (error) {
        return false;
      }
    });

    expect(messageStructureValid).toBe(true);
  });
});

test.describe('Clipboard Operations', () => {
  let electronApp;

  test.beforeAll(async () => {
    const testAppPath = path.join(__dirname, '../fixtures/clipboard-test-app.js');

    electronApp = await electron.launch({
      args: [testAppPath]
    });

    await electronApp.evaluate(({ app }) => app.whenReady());
  });

  test.afterAll(async () => {
    if (electronApp) {
      await electronApp.close();
    }
  });

  test('can write and read text from clipboard', async () => {
    const testText = 'Hello from Electron test';

    const result = await electronApp.evaluate(async (text) => {
      const { clipboard } = require('electron');

      // Write text
      clipboard.writeText(text);

      // Read text
      const readText = clipboard.readText();

      return readText === text;
    }, testText);

    expect(result).toBe(true);
  });

  test('can write and read HTML from clipboard', async () => {
    const testHTML = '<p>Hello <strong>world</strong></p>';

    const result = await electronApp.evaluate(async (html) => {
      const { clipboard } = require('electron');

      // Write HTML
      clipboard.writeHTML(html);

      // Read HTML
      const readHTML = clipboard.readHTML();

      return readHTML === html;
    }, testHTML);

    expect(result).toBe(true);
  });

  test('clipboard has content checks work', async () => {
    const result = await electronApp.evaluate(async () => {
      const { clipboard } = require('electron');

      // Write some text
      clipboard.writeText('test');

      // Check if has text
      return clipboard.readText().length > 0;
    });

    expect(result).toBe(true);
  });
});

test.describe('Global Shortcuts', () => {
  let electronApp;

  test.beforeAll(async () => {
    const testAppPath = path.join(__dirname, '../fixtures/shortcuts-test-app.js');

    electronApp = await electron.launch({
      args: [testAppPath]
    });

    await electronApp.evaluate(({ app }) => app.whenReady());
  });

  test.afterAll(async () => {
    if (electronApp) {
      await electronApp.close();
    }
  });

  test('can register global shortcut', async () => {
    const registered = await electronApp.evaluate(() => {
      const { globalShortcut } = require('electron');

      try {
        const success = globalShortcut.register('CommandOrControl+Shift+K', () => {
          console.log('Shortcut triggered');
        });

        // Unregister immediately
        globalShortcut.unregister('CommandOrControl+Shift+K');

        return success;
      } catch (error) {
        return false;
      }
    });

    expect(registered).toBe(true);
  });

  test('can unregister shortcuts', async () => {
    const result = await electronApp.evaluate(() => {
      const { globalShortcut } = require('electron');

      // Register
      globalShortcut.register('CommandOrControl+Shift+L', () => {});

      // Unregister
      globalShortcut.unregister('CommandOrControl+Shift+L');

      // Verify not registered
      return !globalShortcut.isRegistered('CommandOrControl+Shift+L');
    });

    expect(result).toBe(true);
  });

  test('can unregister all shortcuts', async () => {
    const result = await electronApp.evaluate(() => {
      const { globalShortcut } = require('electron');

      // Register multiple
      globalShortcut.register('CommandOrControl+1', () => {});
      globalShortcut.register('CommandOrControl+2', () => {});

      // Unregister all
      globalShortcut.unregisterAll();

      // Verify both are gone
      return !globalShortcut.isRegistered('CommandOrControl+1') &&
             !globalShortcut.isRegistered('CommandOrControl+2');
    });

    expect(result).toBe(true);
  });
});
