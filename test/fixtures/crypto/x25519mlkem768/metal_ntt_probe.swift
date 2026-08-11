import Foundation
import Metal

let q: Int32 = 3329
let fixtureId = "ntt-v1-p97-i29-c17-q3329"
let zetas: [Int32] = [
    1,1729,2580,3289,2642,630,1897,848,1062,1919,193,797,2786,3260,569,1746,
    296,2447,1339,1476,3046,56,2240,1333,1426,2094,535,2882,2393,2879,1974,821,
    289,331,3253,1756,1197,2304,2277,2055,650,1977,2513,632,2865,33,1320,1915,
    2319,1435,807,452,1438,2868,1534,2402,2647,2617,1481,648,2474,3110,1227,910,
    17,2761,583,2649,1637,723,2288,1100,1409,2662,3281,233,756,2156,3015,3050,
    1703,1651,2789,1789,1847,952,1461,2687,939,2308,2437,2388,733,2337,268,641,
    1584,2298,2037,3220,375,2549,2090,1645,1063,319,2773,757,2099,561,2466,2594,
    2804,1092,403,1026,1143,2150,2775,886,1722,1212,1874,1029,2110,2935,885,2154
]

func modq(_ value: Int64) -> Int32 {
    let reduced = value % Int64(q)
    return Int32(reduced < 0 ? reduced + Int64(q) : reduced)
}

func ntt(_ input: [Int32]) -> [Int32] {
    var f = input
    var length = 128
    var zetaBase = 1
    while length >= 2 {
        let span = length * 2
        for tid in 0..<256 where tid % span < length {
            let group = tid / span
            let product = modq(Int64(zetas[zetaBase + group]) * Int64(f[tid + length]))
            let lower = f[tid]
            f[tid] = modq(Int64(lower) + Int64(product))
            f[tid + length] = modq(Int64(lower) - Int64(product))
        }
        zetaBase <<= 1
        length >>= 1
    }
    return f
}

func intt(_ input: [Int32]) -> [Int32] {
    var f = input
    var length = 2
    var zetaTop = 127
    while length <= 128 {
        let span = length * 2
        for tid in 0..<256 where tid % span < length {
            let group = tid / span
            let lower = f[tid]
            let upper = f[tid + length]
            f[tid] = modq(Int64(lower) + Int64(upper))
            f[tid + length] = modq(Int64(zetas[zetaTop - group]) *
                Int64(modq(Int64(upper) - Int64(lower))))
        }
        zetaTop >>= 1
        length <<= 1
    }
    return f.map { modq(Int64($0) * 3303) }
}

func fail(_ message: String) -> Never {
    FileHandle.standardError.write(Data(("FAIL " + message + "\n").utf8))
    exit(1)
}

guard CommandLine.arguments.count == 3 else {
    fail("usage: metal_ntt_probe <shader.metallib> <canonical-fixture.bin>")
}
guard let device = MTLCreateSystemDefaultDevice() else { fail("no Metal device") }
let library: MTLLibrary
do { library = try device.makeLibrary(
    URL: URL(fileURLWithPath: CommandLine.arguments[1])) }
catch { fail("metallib load: \(error)") }
guard let queue = device.makeCommandQueue() else { fail("command queue") }

let batch = 3
let fixtureData: Data
do {
    fixtureData = try Data(contentsOf:
        URL(fileURLWithPath: CommandLine.arguments[2]),
        options: [.mappedIfSafe])
} catch {
    fail("canonical fixture load: \(error)")
}
guard fixtureData.count == batch * 256 * MemoryLayout<Int32>.stride else {
    fail("canonical fixture size")
}
var fixture = [Int32]()
fixture.reserveCapacity(batch * 256)
for offset in stride(from: 0, to: fixtureData.count, by: 4) {
    let bits = UInt32(fixtureData[offset]) |
        (UInt32(fixtureData[offset + 1]) << 8) |
        (UInt32(fixtureData[offset + 2]) << 16) |
        (UInt32(fixtureData[offset + 3]) << 24)
    fixture.append(Int32(bitPattern: bits))
}
var expectedForward = [Int32]()
for p in 0..<batch { expectedForward += ntt(Array(fixture[(p * 256)..<((p + 1) * 256)])) }
var expectedInverse = [Int32]()
for p in 0..<batch { expectedInverse += intt(Array(expectedForward[(p * 256)..<((p + 1) * 256)])) }

func execute(_ entry: String, _ input: [Int32]) -> [Int32] {
    guard let function = library.makeFunction(name: entry) else { fail("missing entry \(entry)") }
    let pipeline: MTLComputePipelineState
    do { pipeline = try device.makeComputePipelineState(function: function) }
    catch { fail("pipeline \(entry): \(error)") }
    let byteCount = input.count * MemoryLayout<Int32>.stride
    guard let inputBuffer = device.makeBuffer(bytes: input, length: byteCount,
            options: .storageModeShared),
          let outputBuffer = device.makeBuffer(length: byteCount,
            options: .storageModeShared),
          let command = queue.makeCommandBuffer(),
          let encoder = command.makeComputeCommandEncoder() else { fail("resource allocation") }
    var polynomialCount = UInt32(batch)
    encoder.setComputePipelineState(pipeline)
    encoder.setBuffer(inputBuffer, offset: 0, index: 0)
    encoder.setBuffer(outputBuffer, offset: 0, index: 1)
    encoder.setBytes(&polynomialCount, length: MemoryLayout<UInt32>.stride, index: 2)
    encoder.dispatchThreadgroups(MTLSize(width: batch, height: 1, depth: 1),
        threadsPerThreadgroup: MTLSize(width: 256, height: 1, depth: 1))
    encoder.endEncoding()
    command.commit()
    command.waitUntilCompleted()
    if command.status != .completed { fail("command \(entry): \(String(describing: command.error))") }
    let ptr = outputBuffer.contents().bindMemory(to: Int32.self, capacity: input.count)
    return Array(UnsafeBufferPointer(start: ptr, count: input.count))
}

let actualForward = execute("x25519_mlkem768_ntt_forward_metal", fixture)
guard actualForward == expectedForward else {
    let index = zip(actualForward, expectedForward).firstIndex { $0 != $1 } ?? -1
    fail("forward mismatch index=\(index)")
}
let actualInverse = execute("x25519_mlkem768_ntt_inverse_metal", actualForward)
guard actualInverse == expectedInverse else {
    let index = zip(actualInverse, expectedInverse).firstIndex { $0 != $1 } ?? -1
    fail("inverse mismatch index=\(index)")
}
print("PASS backend=metal device=\(device.name) binary_load=1 forward=1 inverse=1 submit=1 complete=1 readback=1 oracle_match=1 batch=3 fixture_id=\(fixtureId)")
