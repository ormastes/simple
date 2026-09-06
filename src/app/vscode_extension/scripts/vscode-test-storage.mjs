import { createHash } from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';

const MACOS_UNIX_SOCKET_LIMIT = 103;
const RESERVED_SOCKET_NAME_BYTES = 44;

function defaultUserStorageRoot(environment) {
    const home = environment.HOME || os.homedir();
    if (process.platform === 'darwin') {
        return path.join(home, 'Library', 'Caches', 'simple', 'storage');
    }
    if (process.platform === 'win32') {
        return path.join(environment.LOCALAPPDATA || home, 'Simple', 'storage');
    }
    return path.join(environment.XDG_CACHE_HOME || path.join(home, '.cache'), 'simple', 'storage');
}

function isDescendant(root, candidate) {
    const relative = path.relative(path.resolve(root), path.resolve(candidate));
    return relative !== '..' && !relative.startsWith(`..${path.sep}`) && !path.isAbsolute(relative);
}

export function deriveVscodeTestStorage(environment = process.env, cwd = process.cwd(), nonce = `${process.pid}`) {
    const roots = [
        environment.SIMPLE_USER_STORAGE_ROOT || defaultUserStorageRoot(environment),
        environment.SIMPLE_WORKTREE_STORAGE_ROOT || path.join(cwd, '.simple', 'storage'),
    ];
    const key = createHash('sha256').update(`${cwd}\n${nonce}`).digest('hex').slice(0, 8);
    for (const root of roots) {
        const session = path.join(path.resolve(root), 't', 'v', key);
        if (isDescendant(root, session)
            && Buffer.byteLength(session, 'utf8') + RESERVED_SOCKET_NAME_BYTES <= MACOS_UNIX_SOCKET_LIMIT) {
            return { root: path.resolve(root), session };
        }
    }
    throw new Error('No approved Simple storage root is short enough for a macOS VS Code IPC socket; set SIMPLE_USER_STORAGE_ROOT to a shorter absolute path');
}

export function prepareVscodeTestStorage(environment = process.env, cwd = process.cwd()) {
    const storage = deriveVscodeTestStorage(environment, cwd, `${process.pid}-${Date.now()}`);
    fs.mkdirSync(storage.session, { recursive: true });
    return {
        storage,
        environment: {
            ...environment,
            SIMPLE_USER_STORAGE_ROOT: environment.SIMPLE_USER_STORAGE_ROOT || storage.root,
            SIMPLE_WORKTREE_STORAGE_ROOT: environment.SIMPLE_WORKTREE_STORAGE_ROOT || path.join(cwd, '.simple', 'storage'),
            TMPDIR: storage.session,
            TMP: storage.session,
            TEMP: storage.session,
        },
        cleanup() {
            fs.rmSync(storage.session, { recursive: true, force: true });
        },
    };
}
