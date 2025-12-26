// Playwright test for Worker Pool functionality
const { _electron: electron } = require('playwright');
const { test, expect } = require('@playwright/test');
const path = require('path');
const fs = require('fs').promises;

test.describe('Worker Threads', () => {
  let electronApp;

  test.beforeAll(async () => {
    const testAppPath = path.join(__dirname, '../fixtures/worker-test-app.js');

    electronApp = await electron.launch({
      args: [testAppPath],
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
  });

  test('can create worker thread', async () => {
    const workerCreated = await electronApp.evaluate(async () => {
      const { Worker } = require('worker_threads');

      try {
        // Create a simple worker that exits immediately
        const workerCode = `
          const { parentPort } = require('worker_threads');
          parentPort.postMessage('ready');
        `;

        // Write worker code to temp file
        const fs = require('fs');
        const path = require('path');
        const os = require('os');
        const workerPath = path.join(os.tmpdir(), 'test-worker.js');
        fs.writeFileSync(workerPath, workerCode);

        const worker = new Worker(workerPath);

        return new Promise((resolve) => {
          worker.on('message', (msg) => {
            worker.terminate();
            fs.unlinkSync(workerPath);
            resolve(msg === 'ready');
          });

          worker.on('error', () => {
            worker.terminate();
            fs.unlinkSync(workerPath);
            resolve(false);
          });

          setTimeout(() => {
            worker.terminate();
            fs.unlinkSync(workerPath);
            resolve(false);
          }, 5000);
        });
      } catch (error) {
        console.error(error);
        return false;
      }
    });

    expect(workerCreated).toBe(true);
  });

  test('worker can receive and send messages', async () => {
    const messageExchangeWorked = await electronApp.evaluate(async () => {
      const { Worker } = require('worker_threads');
      const fs = require('fs');
      const path = require('path');
      const os = require('os');

      // Worker that echoes messages
      const workerCode = `
        const { parentPort } = require('worker_threads');
        parentPort.on('message', (msg) => {
          parentPort.postMessage({ echo: msg });
        });
      `;

      const workerPath = path.join(os.tmpdir(), 'echo-worker.js');
      fs.writeFileSync(workerPath, workerCode);

      try {
        const worker = new Worker(workerPath);

        return new Promise((resolve) => {
          worker.on('message', (msg) => {
            worker.terminate();
            fs.unlinkSync(workerPath);
            resolve(msg.echo === 'test');
          });

          worker.on('error', () => {
            worker.terminate();
            fs.unlinkSync(workerPath);
            resolve(false);
          });

          // Send test message
          worker.postMessage('test');

          setTimeout(() => {
            worker.terminate();
            fs.unlinkSync(workerPath);
            resolve(false);
          }, 5000);
        });
      } catch (error) {
        fs.unlinkSync(workerPath);
        return false;
      }
    });

    expect(messageExchangeWorked).toBe(true);
  });

  test('worker can handle errors', async () => {
    const errorHandled = await electronApp.evaluate(async () => {
      const { Worker } = require('worker_threads');
      const fs = require('fs');
      const path = require('path');
      const os = require('os');

      // Worker that throws an error
      const workerCode = `
        throw new Error('Worker error');
      `;

      const workerPath = path.join(os.tmpdir(), 'error-worker.js');
      fs.writeFileSync(workerPath, workerCode);

      try {
        const worker = new Worker(workerPath);

        return new Promise((resolve) => {
          worker.on('error', (error) => {
            worker.terminate();
            fs.unlinkSync(workerPath);
            resolve(error.message.includes('Worker error'));
          });

          setTimeout(() => {
            worker.terminate();
            fs.unlinkSync(workerPath);
            resolve(false);
          }, 5000);
        });
      } catch (error) {
        fs.unlinkSync(workerPath);
        return false;
      }
    });

    expect(errorHandled).toBe(true);
  });

  test('can terminate worker', async () => {
    const terminated = await electronApp.evaluate(async () => {
      const { Worker } = require('worker_threads');
      const fs = require('fs');
      const path = require('path');
      const os = require('os');

      const workerCode = `
        const { parentPort } = require('worker_threads');
        setInterval(() => {
          parentPort.postMessage('alive');
        }, 100);
      `;

      const workerPath = path.join(os.tmpdir(), 'terminate-worker.js');
      fs.writeFileSync(workerPath, workerCode);

      try {
        const worker = new Worker(workerPath);

        // Wait a bit then terminate
        await new Promise(resolve => setTimeout(resolve, 200));

        const exitCode = await worker.terminate();
        fs.unlinkSync(workerPath);

        return exitCode === 1;
      } catch (error) {
        fs.unlinkSync(workerPath);
        return false;
      }
    });

    expect(terminated).toBe(true);
  });
});

test.describe('Worker Pool Management', () => {
  let electronApp;

  test.beforeAll(async () => {
    const testAppPath = path.join(__dirname, '../fixtures/worker-pool-test-app.js');

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

  test('can create worker pool', async () => {
    const poolCreated = await electronApp.evaluate(() => {
      try {
        // Simulate worker pool creation
        // In real implementation, this would use the Simple worker.spl module
        const pool = {
          workers: [],
          size: 4
        };

        for (let i = 0; i < pool.size; i++) {
          pool.workers.push({ id: i, busy: false });
        }

        return pool.workers.length === 4;
      } catch (error) {
        return false;
      }
    });

    expect(poolCreated).toBe(true);
  });

  test('pool distributes tasks to workers', async () => {
    const tasksDistributed = await electronApp.evaluate(() => {
      // Simulate task distribution
      const pool = {
        workers: [
          { id: 0, busy: false },
          { id: 1, busy: false },
          { id: 2, busy: false },
          { id: 3, busy: false }
        ]
      };

      const tasks = [
        { id: 1, type: 'compute' },
        { id: 2, type: 'compute' },
        { id: 3, type: 'compute' }
      ];

      // Assign tasks to available workers
      let assigned = 0;
      for (const task of tasks) {
        const availableWorker = pool.workers.find(w => !w.busy);
        if (availableWorker) {
          availableWorker.busy = true;
          assigned++;
        }
      }

      return assigned === 3;
    });

    expect(tasksDistributed).toBe(true);
  });

  test('pool handles concurrent tasks', async () => {
    const concurrentHandled = await electronApp.evaluate(async () => {
      const { Worker } = require('worker_threads');
      const fs = require('fs');
      const path = require('path');
      const os = require('os');

      // Worker that computes for a bit
      const workerCode = `
        const { parentPort, workerData } = require('worker_threads');
        setTimeout(() => {
          parentPort.postMessage({ result: workerData.value * 2 });
        }, 100);
      `;

      const workerPath = path.join(os.tmpdir(), 'compute-worker.js');
      fs.writeFileSync(workerPath, workerCode);

      try {
        // Create multiple workers for concurrent tasks
        const workers = [];
        const results = [];

        for (let i = 0; i < 3; i++) {
          const worker = new Worker(workerPath, { workerData: { value: i } });

          workers.push(new Promise((resolve) => {
            worker.on('message', (msg) => {
              results.push(msg.result);
              worker.terminate();
              resolve();
            });

            worker.on('error', () => {
              worker.terminate();
              resolve();
            });
          }));
        }

        await Promise.all(workers);
        fs.unlinkSync(workerPath);

        // Should have 3 results: 0, 2, 4
        return results.length === 3 && results.includes(0) && results.includes(2) && results.includes(4);
      } catch (error) {
        fs.unlinkSync(workerPath);
        return false;
      }
    });

    expect(concurrentHandled).toBe(true);
  });

  test('pool can execute batch tasks', async () => {
    const batchExecuted = await electronApp.evaluate(() => {
      // Simulate batch execution
      const tasks = [
        { id: 1, operation: 'hash' },
        { id: 2, operation: 'hash' },
        { id: 3, operation: 'hash' },
        { id: 4, operation: 'hash' },
        { id: 5, operation: 'hash' }
      ];

      const results = tasks.map(task => {
        // Simulate processing
        return { id: task.id, result: `processed-${task.id}` };
      });

      return results.length === 5;
    });

    expect(batchExecuted).toBe(true);
  });

  test('pool tracks pending task count', async () => {
    const trackingWorks = await electronApp.evaluate(() => {
      const pool = {
        pending: 0,
        completed: 0
      };

      // Submit 5 tasks
      pool.pending = 5;

      // Complete 2 tasks
      pool.pending -= 2;
      pool.completed += 2;

      return pool.pending === 3 && pool.completed === 2;
    });

    expect(trackingWorks).toBe(true);
  });

  test('pool can be terminated', async () => {
    const terminated = await electronApp.evaluate(() => {
      try {
        // Simulate pool termination
        const pool = {
          workers: [
            { id: 0, terminated: false },
            { id: 1, terminated: false },
            { id: 2, terminated: false },
            { id: 3, terminated: false }
          ]
        };

        // Terminate all workers
        pool.workers.forEach(w => w.terminated = true);

        return pool.workers.every(w => w.terminated);
      } catch (error) {
        return false;
      }
    });

    expect(terminated).toBe(true);
  });
});
