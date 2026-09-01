import CryptoKit
import Darwin
import Dispatch
import EndpointSecurity
import Foundation
import Security

// EndpointSecurity is the only production event source accepted by this
// collector. There is no ps/proc polling path and no caller-provided event
// mode. COLLECTOR_SELF_TEST is a compile-time-only executable contract; the
// production build never defines it.

private let unavailableExit = Int32(125)
private let preRootEventLimit = 1024
private let lineageEventLimit = 65_536
private let lineageProcessLimit = 32_768
private let finalizationTimeout: TimeInterval = 10.0

private struct Invocation {
    let driver: String
    let events: String
    let receipt: String
    let provenance: String
    let policy: String
    let arguments: [String]
}

private enum CollectorError: Error {
    case usage
    case invalidPath
    case endpointSecurityUnavailable
    case endpointSecurityFailure
    case launchFailure
    case incompleteHistory
    case outputFailure
}

private struct FileIdentity: Equatable {
    let device: UInt64
    let inode: UInt64
    let size: Int64
    let mode: UInt16
    let flags: UInt32
    let sha256: String
}

private struct RawEvent {
    enum Kind: Hashable {
        case exec
        case fork
        case exit

        var text: String {
            switch self {
            case .exec: return "exec"
            case .fork: return "fork"
            case .exit: return "exit"
            }
        }
    }

    let kind: Kind
    let pid: Int32
    let relatedPID: Int32
    let path: String
    let sequence: UInt64
    let globalSequence: UInt64
    let messageVersion: UInt32
}

private struct HistoryEvent {
    let sequence: Int
    let kind: String
    let pid: Int32
    let relatedPID: Int32
    let path: String

    var line: String {
        "\(sequence)|\(kind)|\(pid)|\(relatedPID)|\(path)"
    }
}

private func stderr(_ text: String) {
    FileHandle.standardError.write(Data((text + "\n").utf8))
}

private func canonicalRegularPath(_ path: String) throws -> String {
    var statBuffer = stat()
    guard lstat(path, &statBuffer) == 0,
          (statBuffer.st_mode & S_IFMT) == S_IFREG,
          let resolved = realpath(path, nil) else {
        throw CollectorError.invalidPath
    }
    defer { free(resolved) }
    return String(cString: resolved)
}

private func canonicalOutputPath(_ path: String) throws -> String {
    let url = URL(fileURLWithPath: path)
    let parent = url.deletingLastPathComponent().resolvingSymlinksInPath()
    var statBuffer = stat()
    guard lstat(parent.path, &statBuffer) == 0,
          (statBuffer.st_mode & S_IFMT) == S_IFDIR else {
        throw CollectorError.invalidPath
    }
    return parent.appendingPathComponent(url.lastPathComponent).path
}

private func hashDescriptor(_ descriptor: Int32) throws -> String {
    guard lseek(descriptor, 0, SEEK_SET) >= 0 else {
        throw CollectorError.outputFailure
    }
    var hasher = SHA256()
    var buffer = [UInt8](repeating: 0, count: 64 * 1024)
    while true {
        let count = buffer.withUnsafeMutableBytes {
            Darwin.read(descriptor, $0.baseAddress, $0.count)
        }
        if count == 0 { break }
        if count < 0 {
            if errno == EINTR { continue }
            throw CollectorError.outputFailure
        }
        hasher.update(data: Data(buffer[0..<count]))
    }
    guard lseek(descriptor, 0, SEEK_SET) >= 0 else {
        throw CollectorError.outputFailure
    }
    return hasher.finalize().map { String(format: "%02x", $0) }.joined()
}

private func openRegularDescriptor(_ path: String) throws -> Int32 {
    let descriptor = open(path, O_RDONLY | O_NOFOLLOW | O_CLOEXEC)
    guard descriptor >= 0 else { throw CollectorError.invalidPath }
    var statBuffer = stat()
    guard fstat(descriptor, &statBuffer) == 0,
          (statBuffer.st_mode & S_IFMT) == S_IFREG else {
        close(descriptor)
        throw CollectorError.invalidPath
    }
    return descriptor
}

private func descriptorIdentity(_ descriptor: Int32) throws -> FileIdentity {
    var statBuffer = stat()
    guard fstat(descriptor, &statBuffer) == 0,
          (statBuffer.st_mode & S_IFMT) == S_IFREG else {
        throw CollectorError.invalidPath
    }
    return FileIdentity(device: UInt64(statBuffer.st_dev),
                        inode: UInt64(statBuffer.st_ino),
                        size: Int64(statBuffer.st_size),
                        mode: UInt16(statBuffer.st_mode & 0o7777),
                        flags: statBuffer.st_flags,
                        sha256: try hashDescriptor(descriptor))
}

private func pathIdentity(_ path: String) throws -> FileIdentity {
    let descriptor = try openRegularDescriptor(path)
    defer { close(descriptor) }
    return try descriptorIdentity(descriptor)
}

private func removeRegularFileIfPresent(_ path: String,
                                        clearImmutable: Bool = false) throws {
    var statBuffer = stat()
    if lstat(path, &statBuffer) != 0 {
        guard errno == ENOENT else { throw CollectorError.outputFailure }
        return
    }
    guard (statBuffer.st_mode & S_IFMT) == S_IFREG else {
        throw CollectorError.invalidPath
    }
    if clearImmutable {
        guard chflags(path, 0) == 0 else { throw CollectorError.outputFailure }
    }
    guard unlink(path) == 0 else { throw CollectorError.outputFailure }
}

private func copyDescriptor(_ source: Int32, to destination: Int32) throws {
    guard lseek(source, 0, SEEK_SET) >= 0 else {
        throw CollectorError.outputFailure
    }
    var buffer = [UInt8](repeating: 0, count: 64 * 1024)
    while true {
        let readCount = buffer.withUnsafeMutableBytes {
            Darwin.read(source, $0.baseAddress, $0.count)
        }
        if readCount == 0 { break }
        if readCount < 0 {
            if errno == EINTR { continue }
            throw CollectorError.outputFailure
        }
        var written = 0
        while written < readCount {
            let writeCount = buffer.withUnsafeBytes {
                Darwin.write(destination,
                             $0.baseAddress!.advanced(by: written),
                             readCount - written)
            }
            if writeCount < 0 {
                if errno == EINTR { continue }
                throw CollectorError.outputFailure
            }
            written += writeCount
        }
    }
    guard fsync(destination) == 0, lseek(source, 0, SEEK_SET) >= 0 else {
        throw CollectorError.outputFailure
    }
}

private struct DriverSnapshot {
    let originalDescriptor: Int32
    let originalIdentity: FileIdentity
    let executedPath: String
    let executedDescriptor: Int32
    let executedIdentity: FileIdentity
}

private func createDriverSnapshot(originalPath: String,
                                  receiptPath: String) throws -> DriverSnapshot {
    let originalDescriptor = try openRegularDescriptor(originalPath)
    do {
        let originalIdentity = try descriptorIdentity(originalDescriptor)
        guard (originalIdentity.mode & 0o111) != 0 else {
            throw CollectorError.invalidPath
        }
        let executedPath = receiptPath + ".driver-snapshot"
        let temporaryPath = executedPath + ".tmp.\(getpid())"
        try removeRegularFileIfPresent(temporaryPath, clearImmutable: true)
        try removeRegularFileIfPresent(executedPath, clearImmutable: true)
        let destination = open(temporaryPath,
                               O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC,
                               mode_t(0o500))
        guard destination >= 0 else { throw CollectorError.outputFailure }
        do {
            try copyDescriptor(originalDescriptor, to: destination)
            guard fchmod(destination, mode_t(0o500)) == 0 else {
                throw CollectorError.outputFailure
            }
        } catch {
            close(destination)
            try? removeRegularFileIfPresent(temporaryPath)
            throw error
        }
        close(destination)
        guard rename(temporaryPath, executedPath) == 0 else {
            try? removeRegularFileIfPresent(temporaryPath)
            throw CollectorError.outputFailure
        }
        let executedDescriptor = try openRegularDescriptor(executedPath)
        do {
            guard fchflags(executedDescriptor, UInt32(UF_IMMUTABLE)) == 0 else {
                throw CollectorError.outputFailure
            }
            let executedIdentity = try descriptorIdentity(executedDescriptor)
            guard executedIdentity.sha256 == originalIdentity.sha256,
                  executedIdentity.size == originalIdentity.size,
                  executedIdentity.mode == 0o500,
                  (executedIdentity.flags & UInt32(UF_IMMUTABLE)) != 0 else {
                throw CollectorError.outputFailure
            }
            return DriverSnapshot(originalDescriptor: originalDescriptor,
                                  originalIdentity: originalIdentity,
                                  executedPath: executedPath,
                                  executedDescriptor: executedDescriptor,
                                  executedIdentity: executedIdentity)
        } catch {
            close(executedDescriptor)
            try? removeRegularFileIfPresent(executedPath, clearImmutable: true)
            throw error
        }
    } catch {
        close(originalDescriptor)
        throw error
    }
}

private func tokenString(_ token: es_string_token_t) -> String {
    guard let data = token.data, token.length > 0 else { return "" }
    return String(bytes: UnsafeRawBufferPointer(start: data,
                                                 count: Int(token.length)),
                  encoding: .utf8) ?? ""
}

private func processPID(_ process: UnsafePointer<es_process_t>) -> Int32 {
    Int32(audit_token_to_pid(process.pointee.audit_token))
}

private func safeEventPath(_ path: String) -> String? {
    guard path.first == "/", !path.contains("\n"), !path.contains("\r"),
          !path.contains("|") else {
        return nil
    }
    return path
}

private final class HistoryTracker: @unchecked Sendable {
    private let condition = NSCondition()
    private let preRootLimit: Int
    private let eventLimit: Int
    private let processLimit: Int
    private var lastSequence: [RawEvent.Kind: UInt64] = [:]
    private var lastGlobalSequence: UInt64?
    private var preRoot: [RawEvent] = []
    private var retained: [HistoryEvent] = []
    private var parents: [Int32: Int32] = [:]
    private var alive: Set<Int32> = []
    private var execCounts: [Int32: Int] = [:]
    private var rootPID: Int32?
    private var rootPath = ""
    private var collectorPID: Int32 = 0
    private var started = false
    private var rootExited = false
    private var failed = false

    init(preRootLimit: Int = preRootEventLimit,
         eventLimit: Int = lineageEventLimit,
         processLimit: Int = lineageProcessLimit) {
        self.preRootLimit = preRootLimit
        self.eventLimit = eventLimit
        self.processLimit = processLimit
    }

    private func reject() {
        failed = true
        condition.broadcast()
    }

    private func hasGap(previous: UInt64, current: UInt64) -> Bool {
        previous == UInt64.max || current != previous + 1
    }

    private func validateSequence(_ event: RawEvent) -> Bool {
        // Local SDK contract: seq_num exists at version >=2 and
        // global_seq_num at version >=4. This collector requires both and
        // never silently degrades to callback renumbering.
        guard event.messageVersion >= 4 else { return false }
        if let previous = lastSequence[event.kind],
           hasGap(previous: previous, current: event.sequence) {
            return false
        }
        if let previous = lastGlobalSequence,
           hasGap(previous: previous, current: event.globalSequence) {
            return false
        }
        lastSequence[event.kind] = event.sequence
        lastGlobalSequence = event.globalSequence
        return true
    }

    private func append(kind: RawEvent.Kind, pid: Int32,
                        relatedPID: Int32, path: String) {
        guard retained.count < eventLimit else {
            reject()
            return
        }
        retained.append(HistoryEvent(sequence: retained.count + 1,
                                     kind: kind.text,
                                     pid: pid,
                                     relatedPID: relatedPID,
                                     path: path))
    }

    private func processLineage(_ event: RawEvent) {
        guard !failed, let rootPID else { return }
        if !started {
            guard event.kind == .exec, event.pid == rootPID,
                  event.path == rootPath else { return }
            started = true
            parents[rootPID] = collectorPID
            alive.insert(rootPID)
            execCounts[rootPID] = 1
            append(kind: .exec, pid: rootPID,
                   relatedPID: collectorPID, path: rootPath)
            return
        }
        if rootExited {
            if alive.contains(event.pid) || alive.contains(event.relatedPID) ||
                parents[event.pid] != nil || parents[event.relatedPID] != nil {
                reject()
            }
            return
        }
        switch event.kind {
        case .fork:
            guard alive.contains(event.pid) else { return }
            guard event.pid != event.relatedPID,
                  parents[event.relatedPID] == nil,
                  parents.count < processLimit else {
                reject()
                return
            }
            parents[event.relatedPID] = event.pid
            alive.insert(event.relatedPID)
            execCounts[event.relatedPID] = 0
            append(kind: .fork, pid: event.pid,
                   relatedPID: event.relatedPID, path: "")
        case .exec:
            guard alive.contains(event.pid), let parent = parents[event.pid]
            else { return }
            guard let path = safeEventPath(event.path) else {
                reject()
                return
            }
            execCounts[event.pid, default: 0] += 1
            append(kind: .exec, pid: event.pid,
                   relatedPID: parent, path: path)
        case .exit:
            guard alive.contains(event.pid), let parent = parents[event.pid]
            else { return }
            guard execCounts[event.pid, default: 0] > 0 else {
                reject()
                return
            }
            append(kind: .exit, pid: event.pid,
                   relatedPID: parent, path: "")
            alive.remove(event.pid)
            if event.pid == rootPID {
                rootExited = true
                if !alive.isEmpty {
                    reject()
                    return
                }
            }
        }
        if rootExited && alive.isEmpty {
            condition.broadcast()
        }
    }

    func accept(_ event: RawEvent) {
        condition.lock()
        defer { condition.unlock() }
        guard !failed else { return }
        guard event.pid > 0, event.relatedPID > 0,
              validateSequence(event) else {
            reject()
            return
        }
        guard rootPID != nil else {
            guard preRoot.count < preRootLimit else {
                reject()
                return
            }
            preRoot.append(event)
            return
        }
        processLineage(event)
    }

    func bindRoot(pid: Int32, path: String, collectorPID: Int32) throws {
        condition.lock()
        defer { condition.unlock() }
        guard !failed, rootPID == nil, pid > 0, collectorPID > 0,
              safeEventPath(path) != nil else {
            throw CollectorError.incompleteHistory
        }
        rootPID = pid
        rootPath = path
        self.collectorPID = collectorPID
        let pending = preRoot
        preRoot.removeAll(keepingCapacity: false)
        for event in pending {
            processLineage(event)
            if failed { break }
        }
    }

    func waitForFinalization(timeout: TimeInterval) throws {
        condition.lock()
        defer { condition.unlock() }
        let deadline = Date(timeIntervalSinceNow: timeout)
        while !failed && !(started && rootExited && alive.isEmpty) {
            if !condition.wait(until: deadline) {
                reject()
                break
            }
        }
        guard !failed, started, rootExited, alive.isEmpty,
              retained.count >= 2 else {
            throw CollectorError.incompleteHistory
        }
    }

    func snapshot() throws -> [HistoryEvent] {
        condition.lock()
        defer { condition.unlock() }
        guard !failed, started, rootExited, alive.isEmpty,
              retained.count >= 2 else {
            throw CollectorError.incompleteHistory
        }
        return retained
    }
}

private func signingIdentity(for collector: String)
throws -> (identifier: String, team: String, entitlement: Bool, valid: Bool) {
    let url = URL(fileURLWithPath: collector) as CFURL
    var staticCode: SecStaticCode?
    guard SecStaticCodeCreateWithPath(url, SecCSFlags(), &staticCode) == errSecSuccess,
          let code = staticCode else {
        throw CollectorError.outputFailure
    }
    let valid = SecStaticCodeCheckValidity(code, SecCSFlags(), nil) == errSecSuccess
    var information: CFDictionary?
    guard SecCodeCopySigningInformation(code, SecCSFlags(), &information) == errSecSuccess,
          let values = information as? [String: Any],
          let identifier = values[kSecCodeInfoIdentifier as String] as? String,
          let team = values[kSecCodeInfoTeamIdentifier as String] as? String,
          let entitlements = values[kSecCodeInfoEntitlementsDict as String]
              as? [String: Any] else {
        throw CollectorError.outputFailure
    }
    let entitlement =
        (entitlements["com.apple.developer.endpoint-security.client"] as? Bool) == true
    return (identifier, team, entitlement, valid)
}

private func writeAtomically(_ text: String, to path: String) throws {
    let temporary = path + ".tmp.\(getpid())"
    try removeRegularFileIfPresent(temporary)
    try Data(text.utf8).write(to: URL(fileURLWithPath: temporary),
                              options: .withoutOverwriting)
    guard rename(temporary, path) == 0 else {
        try? removeRegularFileIfPresent(temporary)
        throw CollectorError.outputFailure
    }
}

private func commitPassOutputs(eventText: String, eventPath: String,
                               receiptText: String, receiptPath: String,
                               rootExitedNormally: Bool) throws {
    guard rootExitedNormally else {
        try? removeRegularFileIfPresent(receiptPath)
        throw CollectorError.incompleteHistory
    }
    try writeAtomically(eventText, to: eventPath)
    try writeAtomically(receiptText, to: receiptPath)
}

private func sha256Text(_ text: String) -> String {
    SHA256.hash(data: Data(text.utf8))
        .map { String(format: "%02x", $0) }
        .joined()
}

private func parseInvocation() throws -> Invocation {
    let arguments = Array(CommandLine.arguments.dropFirst())
    guard let separator = arguments.firstIndex(of: "--"), separator >= 10,
          separator + 1 < arguments.count else {
        throw CollectorError.usage
    }
    let options = Array(arguments[..<separator])
    guard options.count == 10,
          options[0] == "--driver", options[2] == "--events",
          options[4] == "--receipt", options[6] == "--provenance",
          options[8] == "--policy" else {
        throw CollectorError.usage
    }
    return Invocation(driver: try canonicalRegularPath(options[1]),
                      events: try canonicalOutputPath(options[3]),
                      receipt: try canonicalOutputPath(options[5]),
                      provenance: try canonicalRegularPath(options[7]),
                      policy: try canonicalRegularPath(options[9]),
                      arguments: Array(arguments[(separator + 1)...]))
}

private func clearAndValidateMuting(_ client: OpaquePointer) throws {
    guard #available(macOS 13.0, *) else {
        throw CollectorError.endpointSecurityFailure
    }
    guard es_muting_inverted(client, ES_MUTE_INVERSION_TYPE_PROCESS) ==
              ES_MUTE_NOT_INVERTED,
          es_muting_inverted(client, ES_MUTE_INVERSION_TYPE_PATH) ==
              ES_MUTE_NOT_INVERTED,
          es_muting_inverted(client, ES_MUTE_INVERSION_TYPE_TARGET_PATH) ==
              ES_MUTE_NOT_INVERTED,
          es_unmute_all_paths(client) == ES_RETURN_SUCCESS,
          es_unmute_all_target_paths(client) == ES_RETURN_SUCCESS else {
        throw CollectorError.endpointSecurityFailure
    }

    var mutedProcesses: UnsafeMutablePointer<es_muted_processes_t>?
    guard es_muted_processes_events(client, &mutedProcesses) == ES_RETURN_SUCCESS
    else {
        throw CollectorError.endpointSecurityFailure
    }
    if let mutedProcesses {
        for index in 0..<Int(mutedProcesses.pointee.count) {
            var token = mutedProcesses.pointee.processes[index].audit_token
            guard es_unmute_process(client, &token) == ES_RETURN_SUCCESS else {
                es_release_muted_processes(mutedProcesses)
                throw CollectorError.endpointSecurityFailure
            }
        }
        es_release_muted_processes(mutedProcesses)
    }

    var remainingProcesses: UnsafeMutablePointer<es_muted_processes_t>?
    guard es_muted_processes_events(client, &remainingProcesses) == ES_RETURN_SUCCESS
    else {
        throw CollectorError.endpointSecurityFailure
    }
    let processCount = remainingProcesses.map { Int($0.pointee.count) } ?? 0
    if let remainingProcesses { es_release_muted_processes(remainingProcesses) }

    let remainingPathsOut =
        UnsafeMutablePointer<UnsafeMutablePointer<es_muted_paths_t>>
            .allocate(capacity: 1)
    defer { remainingPathsOut.deallocate() }
    guard es_muted_paths_events(client, remainingPathsOut) == ES_RETURN_SUCCESS else {
        throw CollectorError.endpointSecurityFailure
    }
    let remainingPaths = remainingPathsOut.pointee
    let pathCount = Int(remainingPaths.pointee.count)
    es_release_muted_paths(remainingPaths)

    guard processCount == 0, pathCount == 0,
          es_muting_inverted(client, ES_MUTE_INVERSION_TYPE_PROCESS) ==
              ES_MUTE_NOT_INVERTED,
          es_muting_inverted(client, ES_MUTE_INVERSION_TYPE_PATH) ==
              ES_MUTE_NOT_INVERTED,
          es_muting_inverted(client, ES_MUTE_INVERSION_TYPE_TARGET_PATH) ==
              ES_MUTE_NOT_INVERTED else {
        throw CollectorError.endpointSecurityFailure
    }
}

private func withCStringArray<R>(_ strings: [String],
                                 _ body: (UnsafeMutablePointer<
                                    UnsafeMutablePointer<CChar>?>) -> R) -> R {
    var pointers: [UnsafeMutablePointer<CChar>?] = strings.map { strdup($0) }
    pointers.append(nil)
    defer {
        for pointer in pointers where pointer != nil { free(pointer) }
    }
    return pointers.withUnsafeMutableBufferPointer {
        body($0.baseAddress!)
    }
}

private func spawnProcessGroup(executable: String, argv: [String]) throws -> pid_t {
    var attributes: posix_spawnattr_t?
    guard posix_spawnattr_init(&attributes) == 0 else {
        throw CollectorError.launchFailure
    }
    defer { posix_spawnattr_destroy(&attributes) }
    guard posix_spawnattr_setflags(&attributes,
                                   Int16(POSIX_SPAWN_SETPGROUP)) == 0,
          posix_spawnattr_setpgroup(&attributes, 0) == 0 else {
        throw CollectorError.launchFailure
    }
    var child: pid_t = 0
    let processEnvironment = ProcessInfo.processInfo.environment
    let environment = processEnvironment.keys.sorted().map {
        "\($0)=\(processEnvironment[$0]!)"
    }
    let result = withCStringArray(argv) { arguments in
        withCStringArray(environment) { environmentPointers in
            executable.withCString { executablePointer in
                posix_spawn(&child, executablePointer, nil, &attributes,
                            arguments, environmentPointers)
            }
        }
    }
    guard result == 0, child > 0, getpgid(child) == child else {
        throw CollectorError.launchFailure
    }
    return child
}

private final class SignalForwarder {
    private let processGroup: pid_t
    private var sources: [DispatchSourceSignal] = []
    private let forwardedSignals = [SIGTERM, SIGINT, SIGHUP, SIGQUIT]

    init(processGroup: pid_t) {
        self.processGroup = processGroup
        for number in forwardedSignals {
            Darwin.signal(number, SIG_IGN)
            let source = DispatchSource.makeSignalSource(signal: number,
                                                         queue: .global())
            source.setEventHandler { [processGroup] in
                guard processGroup > 0, getpgid(processGroup) == processGroup
                else { return }
                _ = Darwin.kill(-processGroup, number)
            }
            source.resume()
            sources.append(source)
        }
    }

    deinit {
        for source in sources { source.cancel() }
        for number in forwardedSignals { Darwin.signal(number, SIG_DFL) }
    }
}

private func waitForRoot(_ child: pid_t) throws -> Bool {
    var status: Int32 = 0
    while true {
        let result = waitpid(child, &status, 0)
        if result == child { break }
        if result < 0 && errno == EINTR { continue }
        throw CollectorError.launchFailure
    }
    return (status & 0x7f) == 0 && ((status >> 8) & 0xff) == 0
}

private func collect(_ invocation: Invocation) throws {
    try removeRegularFileIfPresent(invocation.receipt)
    let collector = try canonicalRegularPath(CommandLine.arguments[0])
    let identity = try signingIdentity(for: collector)
    guard identity.valid, identity.entitlement, !identity.team.isEmpty else {
        throw CollectorError.endpointSecurityUnavailable
    }
    let snapshot = try createDriverSnapshot(originalPath: invocation.driver,
                                            receiptPath: invocation.receipt)
    var keepSnapshot = false
    defer {
        close(snapshot.originalDescriptor)
        close(snapshot.executedDescriptor)
        if !keepSnapshot {
            try? removeRegularFileIfPresent(snapshot.executedPath,
                                            clearImmutable: true)
        }
    }

    let tracker = HistoryTracker()
    var client: OpaquePointer?
    let result = es_new_client(&client) { _, message in
        let sourcePID = processPID(message.pointee.process)
        let version = message.pointee.version
        // Access is guarded by the exact SDK availability contract.
        guard version >= 4 else {
            tracker.accept(RawEvent(kind: .exec, pid: 0, relatedPID: 0,
                                    path: "", sequence: 0, globalSequence: 0,
                                    messageVersion: version))
            return
        }
        let sequence = message.pointee.seq_num
        let globalSequence = message.pointee.global_seq_num
        switch message.pointee.event_type {
        case ES_EVENT_TYPE_NOTIFY_EXEC:
            let target = message.pointee.event.exec.target
            tracker.accept(RawEvent(
                kind: .exec,
                pid: processPID(target),
                relatedPID: sourcePID,
                path: tokenString(target.pointee.executable.pointee.path),
                sequence: sequence,
                globalSequence: globalSequence,
                messageVersion: version))
        case ES_EVENT_TYPE_NOTIFY_FORK:
            tracker.accept(RawEvent(
                kind: .fork,
                pid: sourcePID,
                relatedPID: processPID(message.pointee.event.fork.child),
                path: "",
                sequence: sequence,
                globalSequence: globalSequence,
                messageVersion: version))
        case ES_EVENT_TYPE_NOTIFY_EXIT:
            tracker.accept(RawEvent(kind: .exit, pid: sourcePID,
                                    relatedPID: sourcePID, path: "",
                                    sequence: sequence,
                                    globalSequence: globalSequence,
                                    messageVersion: version))
        default:
            break
        }
    }
    guard result == ES_NEW_CLIENT_RESULT_SUCCESS, let client else {
        throw CollectorError.endpointSecurityUnavailable
    }
    defer { es_delete_client(client) }
    try clearAndValidateMuting(client)
    var eventTypes: [es_event_type_t] = [ES_EVENT_TYPE_NOTIFY_EXEC,
                                         ES_EVENT_TYPE_NOTIFY_FORK,
                                         ES_EVENT_TYPE_NOTIFY_EXIT]
    guard es_subscribe(client, &eventTypes, UInt32(eventTypes.count)) ==
              ES_RETURN_SUCCESS else {
        throw CollectorError.endpointSecurityFailure
    }

    let child = try spawnProcessGroup(
        executable: snapshot.executedPath,
        argv: [invocation.driver] + invocation.arguments)
    try tracker.bindRoot(pid: child, path: snapshot.executedPath,
                         collectorPID: Int32(getpid()))
    let signalForwarder = SignalForwarder(processGroup: child)
    _ = signalForwarder
    let rootExitedNormally = try waitForRoot(child)
    try tracker.waitForFinalization(timeout: finalizationTimeout)

    let finalOriginal = try pathIdentity(invocation.driver)
    let finalOriginalDescriptor = try descriptorIdentity(snapshot.originalDescriptor)
    let finalExecuted = try pathIdentity(snapshot.executedPath)
    let finalExecutedDescriptor = try descriptorIdentity(snapshot.executedDescriptor)
    guard finalOriginal == snapshot.originalIdentity,
          finalOriginalDescriptor == snapshot.originalIdentity,
          finalExecuted == snapshot.executedIdentity,
          finalExecutedDescriptor == snapshot.executedIdentity else {
        throw CollectorError.incompleteHistory
    }

    let normalized = try tracker.snapshot()
    let eventText = normalized.map(\.line).joined(separator: "\n") + "\n"
    let collectorIdentity = try pathIdentity(collector)
    let provenanceIdentity = try pathIdentity(invocation.provenance)
    let policyIdentity = try pathIdentity(invocation.policy)
    let receipt = [
        "schema=macos-es-execution-history-v3",
        "observer_kind=endpointsecurity-es-v2",
        "coverage=root-and-descendants-through-exit-gap-checked",
        "finalized=complete",
        "status=pass",
        "root_pid=\(child)",
        "root_executable_path=\(invocation.driver)",
        "root_executable_sha256=\(snapshot.originalIdentity.sha256)",
        "root_executable_device=\(snapshot.originalIdentity.device)",
        "root_executable_inode=\(snapshot.originalIdentity.inode)",
        "executed_executable_path=\(snapshot.executedPath)",
        "executed_executable_sha256=\(snapshot.executedIdentity.sha256)",
        "executed_executable_device=\(snapshot.executedIdentity.device)",
        "executed_executable_inode=\(snapshot.executedIdentity.inode)",
        "executed_executable_mode=500",
        "executed_executable_immutable_status=pass",
        "event_sequence_status=gap-free",
        "event_count=\(normalized.count)",
        "event_log_path=\(invocation.events)",
        "event_log_sha256=\(sha256Text(eventText))",
        "collector_path=\(collector)",
        "collector_sha256=\(collectorIdentity.sha256)",
        "collector_provenance_path=\(invocation.provenance)",
        "collector_provenance_sha256=\(provenanceIdentity.sha256)",
        "collector_policy_path=\(invocation.policy)",
        "collector_policy_sha256=\(policyIdentity.sha256)",
        "collector_signing_identifier=\(identity.identifier)",
        "collector_team_identifier=\(identity.team)",
        "collector_entitlement_status=pass",
        "collector_code_signature_status=pass",
    ].joined(separator: "\n") + "\n"
    try commitPassOutputs(eventText: eventText, eventPath: invocation.events,
                          receiptText: receipt, receiptPath: invocation.receipt,
                          rootExitedNormally: rootExitedNormally)
    keepSnapshot = true
}

#if COLLECTOR_SELF_TEST
private func selfTestEvent(_ kind: RawEvent.Kind, _ pid: Int32,
                           _ related: Int32, _ path: String,
                           _ sequence: UInt64, _ global: UInt64,
                           version: UInt32 = 4) -> RawEvent {
    RawEvent(kind: kind, pid: pid, relatedPID: related, path: path,
             sequence: sequence, globalSequence: global,
             messageVersion: version)
}

private func selfTestExpectFailure(_ body: () throws -> Void) throws {
    do {
        try body()
        throw CollectorError.outputFailure
    } catch CollectorError.outputFailure {
        throw CollectorError.outputFailure
    } catch {
        return
    }
}

private func runSelfTests() throws {
    try selfTestExpectFailure {
        let tracker = HistoryTracker()
        try tracker.bindRoot(pid: 100, path: "/private/root", collectorPID: 1)
        tracker.accept(selfTestEvent(.exec, 100, 100, "/private/root", 1, 10))
        tracker.accept(selfTestEvent(.exit, 100, 100, "", 1, 12))
        try tracker.waitForFinalization(timeout: 0.01)
    }
    try selfTestExpectFailure {
        let tracker = HistoryTracker()
        try tracker.bindRoot(pid: 100, path: "/private/root", collectorPID: 1)
        tracker.accept(selfTestEvent(.exec, 100, 100, "/private/root",
                                     1, 1, version: 3))
        try tracker.waitForFinalization(timeout: 0.01)
    }
    try selfTestExpectFailure {
        let tracker = HistoryTracker(preRootLimit: 2)
        tracker.accept(selfTestEvent(.exec, 20, 20, "/usr/bin/true", 1, 1))
        tracker.accept(selfTestEvent(.exec, 21, 21, "/usr/bin/true", 2, 2))
        tracker.accept(selfTestEvent(.exec, 22, 22, "/usr/bin/true", 3, 3))
        try tracker.bindRoot(pid: 100, path: "/private/root", collectorPID: 1)
    }

    let delayed = HistoryTracker()
    try delayed.bindRoot(pid: 100, path: "/private/root", collectorPID: 1)
    delayed.accept(selfTestEvent(.exec, 100, 100, "/private/root", 1, 1))
    DispatchQueue.global().asyncAfter(deadline: .now() + 0.05) {
        delayed.accept(selfTestEvent(.exit, 100, 100, "", 1, 2))
    }
    try delayed.waitForFinalization(timeout: 1.0)

    let filtered = HistoryTracker()
    try filtered.bindRoot(pid: 100, path: "/private/root", collectorPID: 1)
    filtered.accept(selfTestEvent(.exec, 999, 999, "/usr/bin/false", 1, 1))
    filtered.accept(selfTestEvent(.exec, 100, 100, "/private/root", 2, 2))
    filtered.accept(selfTestEvent(.fork, 888, 889, "", 1, 3))
    filtered.accept(selfTestEvent(.exit, 100, 100, "", 1, 4))
    try filtered.waitForFinalization(timeout: 0.1)
    guard try filtered.snapshot().count == 2 else {
        throw CollectorError.outputFailure
    }

    let execHistory = HistoryTracker()
    try execHistory.bindRoot(pid: 100, path: "/private/root", collectorPID: 1)
    execHistory.accept(selfTestEvent(.exec, 100, 100, "/private/root", 1, 1))
    execHistory.accept(selfTestEvent(.exec, 100, 100, "/usr/bin/true", 2, 2))
    execHistory.accept(selfTestEvent(.exec, 100, 100,
                                      "/tmp/src/compiler_rust/simple_seed", 3, 3))
    execHistory.accept(selfTestEvent(.exit, 100, 100, "", 1, 4))
    try execHistory.waitForFinalization(timeout: 0.1)
    let execEvents = try execHistory.snapshot()
    guard execEvents.count == 4,
          execEvents[1].path == "/usr/bin/true",
          execEvents[2].path.hasSuffix("/src/compiler_rust/simple_seed") else {
        throw CollectorError.outputFailure
    }

    let temporary = URL(fileURLWithPath: NSTemporaryDirectory())
        .appendingPathComponent("simple-es-self-test-\(getpid())")
    try FileManager.default.createDirectory(at: temporary,
                                            withIntermediateDirectories: false)
    defer { try? FileManager.default.removeItem(at: temporary) }
    let events = temporary.appendingPathComponent("events").path
    let receipt = temporary.appendingPathComponent("receipt").path
    try selfTestExpectFailure {
        try commitPassOutputs(eventText: "event\n", eventPath: events,
                              receiptText: "status=pass\n", receiptPath: receipt,
                              rootExitedNormally: false)
    }
    guard !FileManager.default.fileExists(atPath: receipt) else {
        throw CollectorError.outputFailure
    }
}

@main
struct SimpleEsHistoryCollectorSelfTest {
    static func main() {
        do {
            try runSelfTests()
            print("macOS EndpointSecurity collector self-test: PASS")
        } catch {
            stderr("macOS EndpointSecurity collector self-test: FAIL")
            exit(1)
        }
    }
}
#else
@main
struct SimpleEsHistoryCollector {
    static func main() {
        do {
            try collect(try parseInvocation())
        } catch CollectorError.endpointSecurityUnavailable {
            stderr("simple_es_history_collector: EndpointSecurity entitlement is unavailable")
            exit(unavailableExit)
        } catch CollectorError.usage {
            stderr("usage: simple_es_history_collector --driver <absolute-driver> --events <absolute-events> --receipt <absolute-receipt> --provenance <absolute-provenance> --policy <absolute-policy> -- <driver-arguments...>")
            exit(2)
        } catch {
            stderr("simple_es_history_collector: collection failed")
            exit(1)
        }
    }
}
#endif
