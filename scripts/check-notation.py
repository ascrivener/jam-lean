#!/usr/bin/env python3
"""Deny-list check for Gray Paper notation that is known to be wrong in v0.8.1.

Usage:  python3 -I scripts/check-notation.py            (run from anywhere; exit 1 on a hit)

Scans the docstrings and module docs (`/-- … -/`, `/-! … -/`) of `JAM/`, `PVM/` and `JamCrypto/`,
and the whole of the book's chapters (`docs/site/Companion/*.lean`, `docs/site/Companion.lean`),
for the forms in `DENY`. Each entry records a fix already made, so the wrong form does not come
back (seeded with the v0.8.1 notation pass, PR #312). Prefer the paper's macros (see
`docs/site/README.md`, "Notation"), which make most of these impossible.

Genuine uses. A doc comment may use a denied form on purpose (e.g. to say what v0.8.0 wrote): put
`-- notation-ok: <id> <reason>` on the line just above the comment block (several ids may be given,
separated by commas). Text outside Lean comments (the book's prose) is listed in `ALLOW` instead.
"""

import glob
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# id: (pattern, message[, unless]): a hit is a line matching `pattern` and not `unless`. Backticked
# spans (Lean code) are removed before matching.
DENY = {
    "rho-ddagger2": (r"\\ddagger\s*\\ddagger|‡‡|\\ddagger\\ddagger",
                     "rho after assurances is rho^double-dagger (one), after disputes rho^dagger (v0.8.1 eqs. 10.14, 11.17)"),
    "work-item-I": (r"\\mathbb\{I\}|𝕀", "a work item is \\workitem = W (eq. workitem)"),
    "context-X": (r"(?i)(context|refine).{0,60}(\\mathbb\{X\}|𝕏)|(\\mathbb\{X\}|𝕏).{0,30}context",
                  "the refinement context is \\workcontext = C (eq. workcontext)"),
    "transfer-X": (r"(?i)transfer.{0,60}(\\mathbb\{X\}|𝕏)|(\\mathbb\{X\}|𝕏).{0,30}transfer",
                   "a deferred transfer is \\defxfer = 𝕥 (eq. defxfer)"),
    "error-J": (r"(?i)error.{0,40}(\\mathbb\{J\}|𝕁)|(\\mathbb\{J\}|𝕁).{0,30}error",
                "the work errors are \\workerror = E (eq. workerror)"),
    "report-W": (r"(?i)report.{0,40}(\\mathbb\{W\}|𝕎)|(\\mathbb\{W\}|𝕎).{0,30}report",
                 "a work report is \\workreport = R (eq. workreport)"),
    "omega-register": (r"\\omega_\{?([0-9]|[ABDX])\b|ω_\{?([0-9]|[ABD])\b|\\omega(\^\{?\\ast|\^\*)",
                       "the paper writes the registers \\registers = phi (\\varphi); keep ω only for the Lean name in backticks"),
    "s17.1-fetching": (r"(?i)§17\.1.{0,80}(bundle|data fetching|fetch)|(bundle|data fetching).{0,80}§17\.1",
                       "bundle fetching and checks are §17.2 (Data Fetching); §17.1 is the overview"),
    "erasure-E_C": (r"\\mathcal\{E\}_\{?C\}?\^|ℰ_C\^",
                    "the erasure code is \\fnerasurecode{v}{k} = C^v_k; E_C is the credential encoding"),
    "shards-R(v)": (r"\bR\(v\)", "the original-shard count is \\fnecoriginalshards(v) = D(v)"),
    "header-lowercase": (r"\\mathbf\{H\}_\{?[a-z]\b|\bH_[tirpxeows]\b(?![a-zA-Z(])",
                         "header fields are capitals in v0.8.1: H_T, H_I, H_R, H_P, …"),
    "null-key": (r"\\mathbb\{K\}\^\{?\\emptyset|𝕂\^∅", "the null key is \\nullvalkey = K_0"),
    "zero-hash": (r"(?i)(zero hash|zero-hash).{0,30}\\mathbf\{0\}|\\mathbf\{0\}.{0,30}(zero hash|32 zero)",
                  "the zero hash is \\zerohash = H_0"),
    "bs-key-H_B": (r"\\mathbb\{H\}_B\b|\\mathbb\{K\}_[BE]\b", "keys are \\bskey (Bandersnatch) and \\edkey (Ed25519)"),
    "sig-bar-B": (r"\\bar\{\\mathbb\{B\}\}|\\tilde\{\\mathbb\{V\}\}",
                  "signatures are \\bssignature, \\bsringproof, \\edsignature (accented V)"),
    "handler-F_X": (r"\\mathfrak\{F\}_\{?[X(\\]|𝔉_X", "the host-call handler type is \\contextmutator{X} = Omega<X>"),
    "request-N_L": (r"\\mathbb\{N\}_L\b|ℕ_L\b", "request lengths are \\preimagelen = N_P"),
    "chi-capitals": (r"\\chi_\{?[MAVRZ]\b|χ_[MAVRZ]\b", "the privileges are chi_m, chi_v, chi_r, chi_a, chi_z (eq. privilegesspec)"),
    "guarantee-g_w": (r"\(g_w\)|g_\{w\}", "a guarantee's report is g_r (bold r; eq. guarantee)"),
    "modified-x_m": (r"\bx_m\b|x_\{m\}", "the modified-services set is x_w (bold w; eq. implications)"),
    "credential-O(a)": (r"\bO\(a\)", "the credential encoding is \\encodecredentials{a} = E_C(a) (eq. 5.7)"),
    "ancestor-11.36": (r"(?i)(ancestor|lookup.?anchor).{0,80}11\.36|11\.36.{0,80}(ancestor|lookup)",
                       "the ancestor-set condition is eq. 11.38 in v0.8.1"),
    "gas-Z_G": (r"\\mathbb\{Z\}_G|ℤ_G", "v0.8.1 types all gas N_G (#533)", r"v0\.8\.0"),
    "readme-note": (r"README, note \d", "cite the note in docs/upstream-candidates.md#gray-paper-issues or the README section by name"),
}

# Allowed hits outside Lean comments: (path relative to the root, id, a substring of the line).
ALLOW = []

LEAN_DIRS = ["JAM", "PVM", "JamCrypto"]
BOOK_GLOBS = ["docs/site/Companion/*.lean", "docs/site/Companion.lean"]


def doc_blocks(src):
    """Yield (first line number, text, allowed ids) for each /-- and /-! block."""
    lines = src.split("\n")
    i = 0
    n = len(src)
    while True:
        m = re.search(r"/-[-!]", src[i:])
        if not m:
            return
        start = i + m.start()
        depth, j = 1, start + 3
        while j < n and depth:
            if src.startswith("/-", j):
                depth += 1
                j += 2
            elif src.startswith("-/", j):
                depth -= 1
                j += 2
            else:
                j += 1
        line0 = src.count("\n", 0, start)
        allowed = set()
        k = line0 - 1
        while k >= 0 and lines[k].strip().startswith("--"):
            mm = re.match(r"\s*--\s*notation-ok:\s*([\w.,()\-\s]+?)(\s{2,}|\s+[A-Z(]|$)", lines[k])
            if mm:
                allowed |= {x.strip() for x in mm.group(1).split(",") if x.strip()}
            k -= 1
        yield line0 + 1, src[start:j], allowed
        i = j


def scan_text(path, first_line, text, allowed, hits):
    for off, line in enumerate(text.split("\n")):
        for ident, spec in DENY.items():
            pat, msg = spec[0], spec[1]
            unless = spec[2] if len(spec) > 2 else None
            bare = re.sub(r"`[^`]*`", "", line)
            if ident in allowed or not re.search(pat, bare):
                continue
            if unless and re.search(unless, bare):
                continue
            rel = os.path.relpath(path, ROOT)
            if any(a[0] == rel and a[1] == ident and a[2] in line for a in ALLOW):
                continue
            hits.append(f"{rel}:{first_line + off}: [{ident}] {msg}\n    {line.strip()[:160]}")


def main():
    hits = []
    for d in LEAN_DIRS:
        for f in sorted(glob.glob(os.path.join(ROOT, d, "**", "*.lean"), recursive=True)):
            src = open(f, encoding="utf-8").read()
            for line0, text, allowed in doc_blocks(src):
                scan_text(f, line0, text, allowed, hits)
    for g in BOOK_GLOBS:
        for f in sorted(glob.glob(os.path.join(ROOT, g))):
            scan_text(f, 1, open(f, encoding="utf-8").read(), set(), hits)
    for h in hits:
        print(h)
    print(f"check-notation: {len(hits)} hit(s) of known-wrong v0.8.1 notation")
    sys.exit(1 if hits else 0)


if __name__ == "__main__":
    main()
