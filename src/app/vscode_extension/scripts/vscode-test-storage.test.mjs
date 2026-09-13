import assert from 'node:assert/strict';
import test from 'node:test';
import path from 'node:path';
import { deriveVscodeTestStorage } from './vscode-test-storage.mjs';

test('derives a short socket session below the centralized user root', () => {
    const root = '/Users/example/Library/Caches/simple/storage';
    const result = deriveVscodeTestStorage({ SIMPLE_USER_STORAGE_ROOT: root, HOME: '/Users/example' }, '/very/long/worktree/path', 'fixed');
    assert.equal(path.relative(root, result.session).startsWith('..'), false);
    assert.ok(Buffer.byteLength(result.session, 'utf8') + 44 <= 103);
});

test('falls back to the centralized worktree root without creating a third root', () => {
    const longRoot = `/Users/example/${'x'.repeat(100)}`;
    const worktreeRoot = '/w/.simple/storage';
    const result = deriveVscodeTestStorage({
        SIMPLE_USER_STORAGE_ROOT: longRoot,
        SIMPLE_WORKTREE_STORAGE_ROOT: worktreeRoot,
        HOME: '/Users/example',
    }, '/w', 'fixed');
    assert.equal(result.root, worktreeRoot);
});

test('fails closed when both approved roots exceed the socket budget', () => {
    const longRoot = `/Users/example/${'x'.repeat(100)}`;
    assert.throws(() => deriveVscodeTestStorage({
        SIMPLE_USER_STORAGE_ROOT: longRoot,
        SIMPLE_WORKTREE_STORAGE_ROOT: `${longRoot}/worktree`,
        HOME: '/Users/example',
    }, '/w', 'fixed'), /No approved Simple storage root/);
});
