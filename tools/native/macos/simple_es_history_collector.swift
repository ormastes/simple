import Darwin
import Foundation

// The EndpointSecurity collector cannot be admitted until an Apple-granted
// entitlement and repository signing-team identity are provisioned. Keeping a
// checked-in executable source makes the expected build input immutable while
// ensuring an unsigned/local build can never produce live-admission evidence.
@main
struct SimpleEsHistoryCollectorUnavailable {
    static func main() {
        FileHandle.standardError.write(
            Data(
                "simple_es_history_collector: unavailable; EndpointSecurity entitlement and signing identity are not provisioned\n"
                    .utf8
            )
        )
        exit(125)
    }
}
