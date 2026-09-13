import * as assert from 'assert';
import * as path from 'path';
import { projectSimpleToolEnvironment, resolveVsCodeStorageRoots } from '../../services/storageRoots';

suite('centralized storage roots', () => {
    test('resolves exactly user and worktree roots from explicit authority', () => {
        const roots = resolveVsCodeStorageRoots(undefined, '/repo/simple', {
            SIMPLE_USER_STORAGE_ROOT: '/users/alice/simple-storage',
            SIMPLE_WORKTREE_STORAGE_ROOT: '/repo/simple/.simple/storage',
        });
        assert.deepStrictEqual(roots, {
            userRoot: path.resolve('/users/alice/simple-storage'),
            worktreeRoot: path.resolve('/repo/simple/.simple/storage'),
        });
    });

    test('projects caches and temporary files beneath the correct roots', () => {
        const roots = {
            userRoot: '/users/alice/simple-storage',
            worktreeRoot: '/repo/simple/.simple/storage',
        };
        const environment = projectSimpleToolEnvironment(roots, {
            HOME: '/users/alice',
            TMPDIR: '/tmp/ambient',
            TMP: '/tmp/ambient-two',
            TEMP: '/tmp/ambient-three',
        });
        assert.ok(environment.SIMPLE_CACHE?.startsWith(`${roots.userRoot}/cache/`));
        assert.ok(environment.SIMPLE_FRONTEND_CACHE_DIR?.startsWith(`${roots.userRoot}/cache/`));
        assert.ok(environment.SIMPLE_NATIVE_BUILD_CACHE_DIR?.startsWith(`${roots.worktreeRoot}/build/`));
        assert.ok(environment.TMPDIR?.startsWith(`${roots.worktreeRoot}/tmp/`));
        assert.strictEqual(environment.TMP, undefined);
        assert.strictEqual(environment.TEMP, undefined);
    });

    test('fails closed when no user authority is available', () => {
        assert.strictEqual(resolveVsCodeStorageRoots(undefined, '/repo/simple', {}), undefined);
    });
});
