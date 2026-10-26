"""Actual curl/POP3 TLS interoperability using disposable local fixtures only."""
import json
import os
from pathlib import Path
import socket
import ssl
import subprocess
import tempfile
import threading

ROOT = Path(__file__).resolve().parents[5]
CLIENT = ROOT / "tools/mail-cli/bin/mail"


def main():
    with tempfile.TemporaryDirectory(prefix="mail-pop3-loopback-") as directory:
        work = Path(directory)
        cert, key = work / "cert.pem", work / "key.pem"
        subprocess.run([
            "openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes",
            "-days", "1", "-subj", "/CN=127.0.0.1",
            "-addext", "subjectAltName=IP:127.0.0.1",
            "-keyout", str(key), "-out", str(cert),
        ], check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=15)
        context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        context.load_cert_chain(cert, key)
        listener = socket.socket()
        listener.bind(("127.0.0.1", 0))
        listener.listen()
        listener.settimeout(0.2)
        port = listener.getsockname()[1]
        stop = threading.Event()
        commands = []
        failures = []
        message = (b"From: sender@example.test\r\nTo: alice@example.test\r\n"
                   b"Subject: Loopback TLS message\r\nContent-Type: text/plain\r\n"
                   b"\r\nLoopback body.\r\n")

        def serve():
            while not stop.is_set():
                try:
                    connection, _ = listener.accept()
                except socket.timeout:
                    continue
                try:
                    with context.wrap_socket(connection, server_side=True) as tls:
                        tls.settimeout(5)
                        stream = tls.makefile("rwb", buffering=0)
                        stream.write(b"+OK disposable POP3 fixture ready\r\n")
                        authenticated = False
                        while line := stream.readline(8192):
                            pieces = line.decode().strip().split(" ", 1)
                            verb = pieces[0].upper()
                            argument = pieces[1] if len(pieces) > 1 else ""
                            commands.append(verb)  # never record credentials
                            if verb == "CAPA":
                                stream.write(b"+OK capabilities\r\nUSER\r\n.\r\n")
                            elif verb == "USER":
                                stream.write(b"+OK user\r\n")
                            elif verb == "PASS":
                                authenticated = argument == "loopback-fixture-password"
                                stream.write(b"+OK authenticated\r\n" if authenticated else b"-ERR rejected\r\n")
                            elif verb == "QUIT":
                                stream.write(b"+OK bye\r\n")
                                break
                            elif not authenticated:
                                stream.write(b"-ERR authenticate first\r\n")
                            elif verb == "LIST":
                                stream.write(f"+OK listing\r\n1 {len(message)}\r\n.\r\n".encode())
                            elif verb == "RETR" and argument == "1":
                                stream.write(b"+OK message\r\n" + message + b".\r\n")
                            elif verb == "NOOP":
                                stream.write(b"+OK\r\n")
                            else:
                                failures.append(verb)
                                stream.write(b"-ERR unsupported\r\n")
                except (ssl.SSLError, ConnectionError):
                    # Expected when testing certificate distrust and rejection.
                    connection.close()
                except Exception as error:
                    failures.append(type(error).__name__)
                    connection.close()

        server = threading.Thread(target=serve, daemon=True)
        server.start()
        home = work / "home"
        config_dir = home / ".config/devhub"
        config_dir.mkdir(parents=True)
        config = config_dir / "email.sdn"
        config.write_text(
            'default_account: "loopback"\n\naccounts:\n'
            '  loopback:\n'
            '    provider: other\n'
            '    protocol: pop3\n'
            '    email: "alice@example.test"\n'
            '    username: "alice@example.test"\n'
            '    display_name: "Fixture"\n'
            '    pop3_server: "127.0.0.1"\n'
            f'    pop3_port: "{port}"\n'
            '    tls: implicit\n'
            '    password: "loopback-fixture-password"\n'
        )
        config.chmod(0o600)
        env = {name: value for name, value in os.environ.items()
               if not name.startswith("MAIL_") and name not in ("CURL_CA_BUNDLE", "SSL_CERT_FILE", "SSL_CERT_DIR")}
        env.update(HOME=str(home), CURL_CA_BUNDLE=str(cert), MAIL_NONINTERACTIVE="1",
                   MAIL_CURL_MAX_RETRIES="1", NO_PROXY="127.0.0.1", PATH="/usr/bin:/bin")

        def run(*args, overrides=None):
            invocation_env = dict(env)
            invocation_env.update(overrides or {})
            return subprocess.run([str(CLIENT), *args], env=invocation_env,
                                  capture_output=True, text=True, timeout=15)

        try:
            result = run("inbox", "--json")
            assert result.returncode == 0, f"inbox exit {result.returncode}: {result.stderr}"
            rows = json.loads(result.stdout)
            assert len(rows) == 1 and rows[0]["uid"] == "1" and rows[0]["protocol"] == "pop3"
            assert rows[0]["subject"] == "Loopback TLS message"
            print("actual_curl_tls_pop3_list: PASS")
            result = run("read", "1", "--raw")
            assert result.returncode == 0 and "Loopback body." in result.stdout
            assert "LIST" in commands and commands.count("RETR") == 2
            assert "DELE" not in commands and "STORE" not in commands
            print("actual_curl_tls_pop3_retrieve_without_mutation: PASS")
            before = commands.count("PASS")
            password = work / "wrong-password"
            password.write_text("wrong-fixture-password\n")
            result = run("read", "1", "--raw", "--password-file", str(password))
            assert result.returncode == 67 and commands.count("PASS") == before + 1
            assert "mail auth password" in result.stderr
            print("actual_curl_authentication_rejected_once: PASS")
            result = run("read", "1", "--raw", overrides={"CURL_CA_BUNDLE": "/etc/ssl/certs/ca-certificates.crt"})
            assert result.returncode == 60, f"untrusted certificate exit {result.returncode}"
            print("actual_curl_untrusted_certificate_rejected: PASS")
            assert not failures, f"server failures: {failures}"
        finally:
            stop.set()
            server.join(timeout=6)
            listener.close()
            assert not server.is_alive(), "fixture server did not stop"


if __name__ == "__main__":
    main()
