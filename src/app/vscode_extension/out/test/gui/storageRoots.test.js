"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
const assert = __importStar(require("assert"));
const path = __importStar(require("path"));
const storageRoots_1 = require("../../services/storageRoots");
suite('centralized storage roots', () => {
    test('resolves exactly user and worktree roots from explicit authority', () => {
        const roots = (0, storageRoots_1.resolveVsCodeStorageRoots)(undefined, '/repo/simple', {
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
        const environment = (0, storageRoots_1.projectSimpleToolEnvironment)(roots, {
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
        assert.strictEqual((0, storageRoots_1.resolveVsCodeStorageRoots)(undefined, '/repo/simple', {}), undefined);
    });
});
//# sourceMappingURL=storageRoots.test.js.map