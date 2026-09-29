"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.KpfWorkerClient = void 0;
exports.createKpfLspClientFacade = createKpfLspClientFacade;
const types_1 = require("./types");
class KpfWorkerClient {
    constructor(routes, launcher) {
        this.launcher = launcher;
        this.sessions = new Map();
        this.routeByLanguage = new Map(routes.map((route) => [route.languageId, route]));
    }
    async activateLanguage(languageId) {
        const route = this.routeByLanguage.get(languageId);
        if (!route) {
            return undefined;
        }
        let session = this.sessions.get(route.providerId);
        if (!session) {
            session = this.launcher.start(route.providerId).then((started) => {
                (0, types_1.validateAdmission)(started.admission);
                if (started.admission.providerId !== route.providerId) {
                    throw new Error(`Worker admitted as ${started.admission.providerId}, expected ${route.providerId}`);
                }
                if (started.admission.placement !== 'worker' && started.admission.placement !== 'wasm') {
                    throw new Error(`Invalid language worker placement ${started.admission.placement}`);
                }
                return started;
            });
            this.sessions.set(route.providerId, session);
        }
        return session;
    }
    startedProviderIds() {
        return [...this.sessions.keys()].sort();
    }
    async dispose() {
        const sessions = await Promise.allSettled(this.sessions.values());
        this.sessions.clear();
        await Promise.all(sessions.flatMap((result) => (result.status === 'fulfilled' ? [result.value.stop()] : [])));
    }
}
exports.KpfWorkerClient = KpfWorkerClient;
function createKpfLspClientFacade(routes, launcher) {
    return new KpfWorkerClient(routes, launcher);
}
//# sourceMappingURL=client.js.map