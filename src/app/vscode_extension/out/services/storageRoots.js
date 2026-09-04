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
exports.resolveVsCodeStorageRoots = resolveVsCodeStorageRoots;
exports.projectSimpleToolEnvironment = projectSimpleToolEnvironment;
const path = __importStar(require("path"));
function resolveVsCodeStorageRoots(context, workspaceRoot, environment = process.env) {
    const userRoot = environment.SIMPLE_USER_STORAGE_ROOT?.trim()
        || (context ? path.join(context.globalStorageUri.fsPath, 'storage') : '');
    const worktreeRoot = environment.SIMPLE_WORKTREE_STORAGE_ROOT?.trim()
        || (workspaceRoot ? path.join(workspaceRoot, '.simple', 'storage') : '');
    if (!userRoot || !worktreeRoot) {
        return undefined;
    }
    return {
        userRoot: path.resolve(userRoot),
        worktreeRoot: path.resolve(worktreeRoot),
    };
}
function projectSimpleToolEnvironment(roots, base = process.env) {
    const environment = { ...base };
    delete environment.TMP;
    delete environment.TEMP;
    environment.SIMPLE_USER_STORAGE_ROOT = roots.userRoot;
    environment.SIMPLE_WORKTREE_STORAGE_ROOT = roots.worktreeRoot;
    environment.SIMPLE_CACHE = path.join(roots.userRoot, 'cache', 'simple', 'compiler-v1');
    environment.SIMPLE_FRONTEND_CACHE_DIR = path.join(roots.userRoot, 'cache', 'simple', 'frontend-v1');
    environment.SIMPLE_HIR_CACHE_DIR = path.join(roots.userRoot, 'cache', 'simple', 'hir-v1');
    environment.SIMPLE_NATIVE_BUILD_CACHE_DIR = path.join(roots.worktreeRoot, 'build', 'simple');
    environment.SIMPLE_TEST_TMP = path.join(roots.worktreeRoot, 'tmp', 'vscode');
    environment.TMPDIR = environment.SIMPLE_TEST_TMP;
    return environment;
}
//# sourceMappingURL=storageRoots.js.map