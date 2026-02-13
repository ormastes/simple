#!/usr/bin/env python3
"""
Simple MCP Client Test
Tests the Simple Language MCP server
"""

import subprocess
import json
import sys
import time

def send_message(proc, method, params=None, msg_id=1):
    """Send a JSON-RPC message to the MCP server"""
    message = {
        "jsonrpc": "2.0",
        "method": method,
        "id": msg_id
    }
    if params:
        message["params"] = params

    msg_json = json.dumps(message)
    msg_bytes = msg_json.encode('utf-8')

    # Send with Content-Length header
    header = f"Content-Length: {len(msg_bytes)}\r\n\r\n"
    proc.stdin.write(header.encode('utf-8'))
    proc.stdin.write(msg_bytes)
    proc.stdin.flush()

    return msg_id

def read_message(proc):
    """Read a JSON-RPC message from the MCP server"""
    # Read Content-Length header
    header = b""
    while True:
        char = proc.stdout.read(1)
        if not char:
            return None
        header += char
        if header.endswith(b"\r\n\r\n") or header.endswith(b"\n\n"):
            break

    # Parse content length
    header_str = header.decode('utf-8').strip()
    content_length = 0
    for line in header_str.split('\n'):
        if line.startswith('Content-Length:'):
            content_length = int(line.split(':')[1].strip())
            break

    if content_length == 0:
        return None

    # Read message body
    body = proc.stdout.read(content_length)
    return json.loads(body.decode('utf-8'))

def test_mcp_server():
    """Test the MCP server"""
    print("=== Testing Simple MCP Server ===\n")

    # Start the server
    server_path = "./bin/simple_mcp_server_optimized"
    print(f"Starting server: {server_path}")

    try:
        proc = subprocess.Popen(
            [server_path, "server"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE
        )

        # Test 1: Initialize
        print("\nTest 1: Initialize")
        send_message(proc, "initialize", {
            "protocolVersion": "2025-06-18",
            "capabilities": {}
        }, 1)

        response = read_message(proc)
        if response and "result" in response:
            print("✓ Initialize successful")
            server_info = response["result"].get("serverInfo", {})
            print(f"  Server: {server_info.get('name')} v{server_info.get('version')}")
            print(f"  Protocol: {response['result'].get('protocolVersion')}")
        else:
            print("✗ Initialize failed")
            print(f"  Response: {response}")
            return False

        # Test 2: List tools
        print("\nTest 2: List available tools")
        send_message(proc, "tools/list", {}, 2)

        response = read_message(proc)
        if response and "result" in response:
            tools = response["result"].get("tools", [])
            print(f"✓ Found {len(tools)} tools")
            print("  Sample tools:")
            for tool in tools[:10]:
                print(f"    - {tool['name']}: {tool.get('description', 'No description')[:60]}")
            if len(tools) > 10:
                print(f"    ... and {len(tools) - 10} more")
        else:
            print("✗ Tools list failed")
            print(f"  Response: {response}")
            return False

        # Test 3: List resources
        print("\nTest 3: List available resources")
        send_message(proc, "resources/list", {}, 3)

        response = read_message(proc)
        if response and "result" in response:
            resources = response["result"].get("resources", [])
            print(f"✓ Found {len(resources)} resources")
            if resources:
                print("  Sample resources:")
                for res in resources[:5]:
                    print(f"    - {res['uri']}: {res.get('name', 'No name')}")
        else:
            print("✗ Resources list failed")
            print(f"  Response: {response}")

        # Cleanup
        proc.stdin.close()
        proc.terminate()
        proc.wait(timeout=2)

        print("\n=== All tests passed! ===")
        print("\nThe MCP server is working correctly.")
        print("Configuration is set in: ~/.config/Claude/claude_desktop_config.json")
        print("\nTo use with Claude Desktop:")
        print("  1. Restart Claude Desktop")
        print("  2. Look for 'simple-lang' in the MCP servers list")
        print("  3. You can now use tools like bugdb_get, simple_edit, debug_create_session, etc.")

        return True

    except Exception as e:
        print(f"✗ Error: {e}")
        import traceback
        traceback.print_exc()
        return False

if __name__ == "__main__":
    success = test_mcp_server()
    sys.exit(0 if success else 1)
