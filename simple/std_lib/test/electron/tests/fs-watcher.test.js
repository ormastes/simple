// Playwright test for File System Watcher
const { _electron: electron } = require('playwright');
const { test, expect } = require('@playwright/test');
const path = require('path');
const fs = require('fs').promises;
const os = require('os');

test.describe('File System Watcher', () => {
  let electronApp;
  let testDir;

  test.beforeAll(async () => {
    // Create temp directory for testing
    testDir = await fs.mkdtemp(path.join(os.tmpdir(), 'electron-fs-test-'));

    const testAppPath = path.join(__dirname, '../fixtures/fs-watcher-test-app.js');

    electronApp = await electron.launch({
      args: [testAppPath, testDir],
      env: {
        ...process.env,
        ...(process.env.CI && { DISPLAY: ':99' })
      }
    });

    await electronApp.evaluate(({ app }) => app.whenReady());
  });

  test.afterAll(async () => {
    if (electronApp) {
      await electronApp.close();
    }

    // Clean up temp directory
    if (testDir) {
      await fs.rm(testDir, { recursive: true, force: true });
    }
  });

  test('can create file system watcher', async () => {
    const watcherCreated = await electronApp.evaluate((dir) => {
      const fs = require('fs');

      try {
        // Create a watcher
        const watcher = fs.watch(dir, { recursive: false }, (eventType, filename) => {
          console.log(`Event: ${eventType}, File: ${filename}`);
        });

        watcher.close();
        return true;
      } catch (error) {
        console.error(error);
        return false;
      }
    }, testDir);

    expect(watcherCreated).toBe(true);
  });

  test('detects file creation', async () => {
    const testFile = path.join(testDir, 'test-create.txt');

    // Set up watcher and event tracking
    const watchPromise = electronApp.evaluate((dir) => {
      const fs = require('fs');

      return new Promise((resolve) => {
        const watcher = fs.watch(dir, { recursive: false }, (eventType, filename) => {
          if (filename === 'test-create.txt') {
            watcher.close();
            resolve({ eventType, filename });
          }
        });

        // Timeout after 5 seconds
        setTimeout(() => {
          watcher.close();
          resolve({ eventType: 'timeout', filename: null });
        }, 5000);
      });
    }, testDir);

    // Wait a bit for watcher to start
    await new Promise(resolve => setTimeout(resolve, 100));

    // Create file
    await fs.writeFile(testFile, 'test content');

    // Wait for event
    const result = await watchPromise;

    expect(result.eventType).not.toBe('timeout');
    expect(result.filename).toBe('test-create.txt');

    // Clean up
    await fs.unlink(testFile);
  });

  test('detects file modification', async () => {
    const testFile = path.join(testDir, 'test-modify.txt');

    // Create file first
    await fs.writeFile(testFile, 'initial content');

    // Wait a bit to ensure file is written
    await new Promise(resolve => setTimeout(resolve, 100));

    // Set up watcher
    const watchPromise = electronApp.evaluate((dir) => {
      const fs = require('fs');

      return new Promise((resolve) => {
        const watcher = fs.watch(dir, { recursive: false }, (eventType, filename) => {
          if (filename === 'test-modify.txt' && eventType === 'change') {
            watcher.close();
            resolve({ eventType, filename });
          }
        });

        setTimeout(() => {
          watcher.close();
          resolve({ eventType: 'timeout', filename: null });
        }, 5000);
      });
    }, testDir);

    // Wait for watcher to start
    await new Promise(resolve => setTimeout(resolve, 100));

    // Modify file
    await fs.appendFile(testFile, '\nmodified content');

    // Wait for event
    const result = await watchPromise;

    expect(result.eventType).not.toBe('timeout');
    expect(result.filename).toBe('test-modify.txt');

    // Clean up
    await fs.unlink(testFile);
  });

  test('detects file deletion', async () => {
    const testFile = path.join(testDir, 'test-delete.txt');

    // Create file first
    await fs.writeFile(testFile, 'to be deleted');
    await new Promise(resolve => setTimeout(resolve, 100));

    // Set up watcher
    const watchPromise = electronApp.evaluate((dir) => {
      const fs = require('fs');

      return new Promise((resolve) => {
        const watcher = fs.watch(dir, { recursive: false }, (eventType, filename) => {
          if (filename === 'test-delete.txt') {
            watcher.close();
            resolve({ eventType, filename });
          }
        });

        setTimeout(() => {
          watcher.close();
          resolve({ eventType: 'timeout', filename: null });
        }, 5000);
      });
    }, testDir);

    // Wait for watcher to start
    await new Promise(resolve => setTimeout(resolve, 100));

    // Delete file
    await fs.unlink(testFile);

    // Wait for event
    const result = await watchPromise;

    expect(result.eventType).not.toBe('timeout');
    expect(result.filename).toBe('test-delete.txt');
  });

  test('can watch multiple files', async () => {
    const watchPromise = electronApp.evaluate((dir) => {
      const fs = require('fs');
      const events = [];

      return new Promise((resolve) => {
        const watcher = fs.watch(dir, { recursive: false }, (eventType, filename) => {
          events.push({ eventType, filename });

          // Resolve when we have 2 events
          if (events.length >= 2) {
            watcher.close();
            resolve(events);
          }
        });

        setTimeout(() => {
          watcher.close();
          resolve(events);
        }, 5000);
      });
    }, testDir);

    // Wait for watcher
    await new Promise(resolve => setTimeout(resolve, 100));

    // Create multiple files
    const file1 = path.join(testDir, 'multi-1.txt');
    const file2 = path.join(testDir, 'multi-2.txt');

    await fs.writeFile(file1, 'content 1');
    await new Promise(resolve => setTimeout(resolve, 100));
    await fs.writeFile(file2, 'content 2');

    // Wait for events
    const events = await watchPromise;

    expect(events.length).toBeGreaterThanOrEqual(2);

    // Clean up
    await fs.unlink(file1).catch(() => {});
    await fs.unlink(file2).catch(() => {});
  });

  test('can stop watching', async () => {
    const stopped = await electronApp.evaluate((dir) => {
      const fs = require('fs');

      try {
        const watcher = fs.watch(dir, { recursive: false }, () => {});

        // Close immediately
        watcher.close();

        return true;
      } catch (error) {
        return false;
      }
    }, testDir);

    expect(stopped).toBe(true);
  });
});

test.describe('Recursive File System Watching', () => {
  let electronApp;
  let testDir;
  let subDir;

  test.beforeAll(async () => {
    // Create temp directory with subdirectory
    testDir = await fs.mkdtemp(path.join(os.tmpdir(), 'electron-fs-recursive-'));
    subDir = path.join(testDir, 'subdir');
    await fs.mkdir(subDir);

    const testAppPath = path.join(__dirname, '../fixtures/fs-watcher-test-app.js');

    electronApp = await electron.launch({
      args: [testAppPath, testDir]
    });

    await electronApp.evaluate(({ app }) => app.whenReady());
  });

  test.afterAll(async () => {
    if (electronApp) {
      await electronApp.close();
    }

    if (testDir) {
      await fs.rm(testDir, { recursive: true, force: true });
    }
  });

  test('detects changes in subdirectories', async () => {
    const testFile = path.join(subDir, 'nested-file.txt');

    // Set up recursive watcher
    const watchPromise = electronApp.evaluate((dir) => {
      const fs = require('fs');

      return new Promise((resolve) => {
        const watcher = fs.watch(dir, { recursive: true }, (eventType, filename) => {
          if (filename && filename.includes('nested-file.txt')) {
            watcher.close();
            resolve({ eventType, filename });
          }
        });

        setTimeout(() => {
          watcher.close();
          resolve({ eventType: 'timeout', filename: null });
        }, 5000);
      });
    }, testDir);

    // Wait for watcher
    await new Promise(resolve => setTimeout(resolve, 100));

    // Create file in subdirectory
    await fs.writeFile(testFile, 'nested content');

    // Wait for event
    const result = await watchPromise;

    expect(result.eventType).not.toBe('timeout');
    expect(result.filename).toContain('nested-file.txt');

    // Clean up
    await fs.unlink(testFile);
  });
});
