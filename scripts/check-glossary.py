#!/usr/bin/env python3
"""Check the book's glossary data, `docs/site/glossary.json` (rendered by `Companion/Glossary.lean`).

Usage:  python3 -I scripts/check-glossary.py      (exit 1 on a problem)

Needs no build. Rejects:

* a malformed file: a section or entry without its fields, a field of the wrong type, a repeated
  entry id, unbalanced `$` or backquotes in a text;
* a section that the glossary chapter (`docs/site/Companion/Glossary.lean`) does not render with
  `{glossarySection "<id>"}` exactly once, or a rendered section the file does not have;
* a `place` that is not a key of `places`, or a key of `places` that is not a section tag
  (`tag := "…"`) of the book's chapters;
* a TeX control sequence in `tex` or in a text's `$…$` that is neither one of the paper's macros
  (`docs/site/gp-macros.json`, with `\\a¬b` read as the paper writes it) nor a standard KaTeX
  command listed here;
* a `model` name that no model source declares. A name's last component must be declared
  (`def`, `structure`, … : the declaration pattern of `scripts/check-model-map.py`), or be a field
  of the structure its prefix names. The book's build checks each name against the elaborated
  environment as well.
"""

import glob
import importlib.util
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SITE = os.path.join(ROOT, "docs", "site")

# The declaration pattern and the model's sources, shared with check-model-map.py.
_spec = importlib.util.spec_from_file_location("check_model_map", os.path.join(ROOT, "scripts", "check-model-map.py"))
_cmm = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_cmm)
DECL = _cmm.DECL

# Standard KaTeX commands the glossary may use besides the paper's macros.
STANDARD = {"Phi", "Psi", "phi", "varphi", "le", "ge", "dots", "ldots", "cdot", "mathsf", "mathbb",
            "mathbf", "mathcal", "text", "prime"}

SECTION_FIELDS = {"id": str, "intro": str, "entries": list}
ENTRY_FIELDS = {"id": str, "tex": str, "name": str, "meaning": str, "model": list, "place": str}


def model_files():
    out = {}
    for d in ("JAM", "PVM", "JamCrypto"):
        for f in glob.glob(os.path.join(ROOT, d, "**", "*.lean"), recursive=True):
            out[f] = open(f, encoding="utf-8").read()
    return out


def structure_fields(texts, struct):
    """The field names of every `structure <struct>` in the sources (the indented `name :` lines
    of its body, which ends at the next line that starts in column 0)."""
    fields = set()
    head = re.compile(r"^structure\s+(?:[\w.]*\.)?" + re.escape(struct) + r"\b.*$", re.M)
    for t in texts:
        for m in head.finditer(t):
            for line in t[m.end():].split("\n")[1:]:
                if line and not line[0].isspace():
                    break
                fm = re.match(r"^\s+(\w+)\s*:", line)
                if fm:
                    fields.add(fm.group(1))
    return fields


def tex_commands(tex):
    # `\a¬b` is one command in the paper's spelling; `\¬b` too.
    return re.findall(r"\\((?:[A-Za-z]+)?(?:¬[A-Za-z]+)*|¬[A-Za-z]+)", tex)


def math_spans(text):
    parts = text.split("$")
    return parts[1::2], len(parts) % 2 == 1


def main():
    bad = []
    data = json.load(open(os.path.join(SITE, "glossary.json"), encoding="utf-8"))
    macros = json.load(open(os.path.join(SITE, "gp-macros.json"), encoding="utf-8"))["macros"]
    paper_names = {v["paper"].lstrip("\\") for v in macros.values()}
    tags = set()
    for f in glob.glob(os.path.join(SITE, "Companion", "*.lean")):
        tags |= set(re.findall(r'tag := "([^"]+)"', open(f, encoding="utf-8").read()))
    files = model_files()
    texts = list(files.values())
    declared = {m.group(1) for t in texts for m in DECL.finditer(t)}

    places = data.get("places")
    if not isinstance(places, dict):
        bad.append("places: expected an object mapping section tags to labels")
        places = {}
    for k, v in places.items():
        if k not in tags:
            bad.append(f"places: {k} is not a section tag of the book")
        if not isinstance(v, str) or not v.strip():
            bad.append(f"places: {k} needs a non-empty label")

    def check_tex(where, tex):
        for c in tex_commands(tex):
            if c not in paper_names and c not in STANDARD:
                bad.append(f"{where}: \\{c} is neither a paper macro (gp-macros.json) nor an allowed KaTeX command")

    def check_text(where, text):
        spans, balanced = math_spans(text)
        if not balanced:
            bad.append(f"{where}: unbalanced $")
        for s in spans:
            check_tex(where, s)
        outside = "".join(text.split("$")[0::2])
        if outside.count("`") % 2:
            bad.append(f"{where}: unbalanced backquote")

    ids = set()
    sections = data.get("sections")
    if not isinstance(sections, list) or not sections:
        bad.append("sections: expected a non-empty list")
        sections = []
    for si, sec in enumerate(sections):
        swhere = f"sections[{si}]"
        for k, ty in SECTION_FIELDS.items():
            if not isinstance(sec.get(k), ty):
                bad.append(f"{swhere}: \"{k}\" must be a {ty.__name__}")
        if not isinstance(sec.get("entries"), list):
            continue
        swhere = f"section {sec.get('id')}"
        if isinstance(sec.get("intro"), str):
            check_text(f"{swhere} intro", sec["intro"])
        for e in sec["entries"]:
            where = f"{swhere}, entry {e.get('id')}"
            for k, ty in ENTRY_FIELDS.items():
                if not isinstance(e.get(k), ty):
                    bad.append(f"{where}: \"{k}\" must be a {ty.__name__}")
            extra = set(e) - set(ENTRY_FIELDS) - {"modelNote"}
            if extra:
                bad.append(f"{where}: unknown field(s) {sorted(extra)}")
            i = e.get("id")
            if i in ids:
                bad.append(f"{where}: repeated id")
            ids.add(i)
            if isinstance(e.get("tex"), str):
                check_tex(where, e["tex"])
            if isinstance(e.get("meaning"), str):
                check_text(where, e["meaning"])
            if isinstance(e.get("modelNote"), str):
                check_text(where, e["modelNote"])
            if e.get("place") not in places:
                bad.append(f"{where}: place {e.get('place')!r} is not a key of places")
            model = e.get("model") if isinstance(e.get("model"), list) else []
            if not model and not e.get("modelNote"):
                bad.append(f"{where}: no model names; say why in \"modelNote\"")
            for n in model:
                if not isinstance(n, str) or "." not in n:
                    bad.append(f"{where}: model name {n!r} must be a full name")
                    continue
                parts = n.split(".")
                if parts[-1] in declared:
                    continue
                if len(parts) >= 3 and parts[-1] in structure_fields(texts, parts[-2]):
                    continue
                bad.append(f"{where}: no model source declares {n} (neither a declaration "
                           f"{parts[-1]} nor a field of a structure {parts[-2]})")
    chapter = open(os.path.join(SITE, "Companion", "Glossary.lean"), encoding="utf-8").read()
    used = re.findall(r'\{glossarySection "([^"]*)"\}', chapter)
    sids = [sec.get("id") for sec in sections if isinstance(sec, dict)]
    for sid in sids:
        if used.count(sid) != 1:
            bad.append(f"section {sid}: Companion/Glossary.lean renders it {used.count(sid)} times (expected once)")
    for u in sorted(set(used) - set(sids)):
        bad.append(f"Companion/Glossary.lean renders section {u}, which glossary.json does not have")
    for b in bad:
        print(b)
    print(f"check-glossary: {len(bad)} problem(s); {len(ids)} entries")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
