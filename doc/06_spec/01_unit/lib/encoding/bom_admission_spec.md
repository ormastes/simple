# BOM-only transport admission

Three authored API cases, execution UNRUN: forbidden UTF16 signature retains typed offset; required UTF8 prefix is checked independently of invalid payload bytes; invalid metadata and unknown codecs are rejected. This helper deliberately does not validate/decode payload text. It reuses canonical metadata/prefix checks and is intended for file append admission after actual EOF is known. No compiler retry or full encoding qualification is claimed.
