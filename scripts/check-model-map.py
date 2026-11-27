#!/usr/bin/env python3
"""Check the book's model maps: every displayed equation says where the model implements it.

Usage:  python3 -I scripts/check-model-map.py          (exit 1 on a problem)
        python3 -I scripts/check-model-map.py --counts (also print the entries per kind and chapter)

Every equation a chapter of the companion displays (`{gpeq "…"}`, or a hand display marked
`{transcribed "…" "…"}`) is followed in the book by an "In the model:" line, generated from the
chapter's map `docs/site/model-map/<Chapter>.json` (format: `docs/site/README.md` and
`docs/site/Companion/ModelMap.lean`). This check, which needs no build, rejects:

* a chapter not listed in `docs/site/model-map/unmapped.json` without a map, or whose map has no
  entry for an equation the chapter displays;
* a chapter listed there whose map is in fact complete (remove it from the list: the list only
  shrinks), or a listed name that is not a chapter;
* an entry for an equation the chapter does not display, or that the paper does not have;
* an unknown kind, a missing or unexpected field (`name` for def/inline/type/theorem, `at` for
  inline, `reason` for notModelled/notation; `note` optional);
* a `name` whose last component no model source declares, or an `at` locator that occurs in no
  model source.

The book's build checks the rest against the elaborated environment: that each `name` is a
declaration the chapter imports, and that each `at` occurs exactly once inside that declaration's
source (`Companion/ModelMap.lean`).
"""

import glob
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SITE = os.path.join(ROOT, "docs", "site")
MAPS = os.path.join(SITE, "model-map")
SKIP = ("Paper.lean", "Source.lean", "Docstring.lean", "ModelMap.lean")
KINDS = {
    "def": {"name"},
    "inline": {"name", "at"},
    "type": {"name"},
    "theorem": {"name"},
    "notModelled": {"reason"},
    "notation": {"reason"},
}
OPTIONAL = {"note"}
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
                  r"(?:def|theorem|lemma|abbrev|structure|inductive|class|instance|opaque|axiom)\s+"
                  r"(?:[^\s(:{\[]*\.)?([^\s.(:{\[]+)", re.M)


def chapters():
    return {os.path.splitext(os.path.basename(f))[0]: f
            for f in sorted(glob.glob(os.path.join(SITE, "Companion", "*.lean"))) if not f.endswith(SKIP)}


def displayed(src, labels):
    out = []
    for m in re.finditer(r'\{(?:gpeq|transcribed) "([^"]*)"', src):
        for k in m.group(1).split(","):
            k = k.strip()
            if k:
                out.append(labels.get(k, k))
    return out


def model_sources():
    texts = []
    for d in ("JAM", "PVM", "JamCrypto"):
        for f in glob.glob(os.path.join(ROOT, d, "**", "*.lean"), recursive=True):
            texts.append(open(f, encoding="utf-8").read())
    return texts


def main():
    table = json.load(open(os.path.join(SITE, "gp-equations.json"), encoding="utf-8"))
    eqs, labels = table["equations"], table["labels"]
    chs = chapters()
    bad = []
    unmapped = json.load(open(os.path.join(MAPS, "unmapped.json"), encoding="utf-8"))["unmapped"]
    for u in unmapped:
        if u not in chs:
            bad.append(f"model-map/unmapped.json: {u} is not a chapter (docs/site/Companion/{u}.lean)")
    sources = model_sources()
    declared = {m.group(1) for t in sources for m in DECL.finditer(t)}
    counts = {}
    for f in sorted(glob.glob(os.path.join(MAPS, "*.json"))):
        ch = os.path.splitext(os.path.basename(f))[0]
        if ch != "unmapped" and ch not in chs:
            bad.append(f"model-map/{ch}.json: no chapter docs/site/Companion/{ch}.lean")
    for ch, path in chs.items():
        shown = displayed(open(path, encoding="utf-8").read(), labels)
        mpath = os.path.join(MAPS, f"{ch}.json")
        rel = f"model-map/{ch}.json"
        if not os.path.exists(mpath):
            if ch not in unmapped and shown:
                bad.append(f"{rel}: missing; chapter {ch} displays {len(set(shown))} equation(s) "
                           "(or list it in model-map/unmapped.json until its map is done)")
            continue
        try:
            data = json.load(open(mpath, encoding="utf-8"))
        except ValueError as e:
            bad.append(f"{rel}: not valid JSON ({e})")
            continue
        if set(data) != {"equations"} or not isinstance(data["equations"], dict):
            bad.append(f"{rel}: expected one top-level key, \"equations\", mapping numbers to entries")
            continue
        entries = data["equations"]
        for n, e in entries.items():
            where = f"{rel}: ({n})"
            if n not in eqs:
                bad.append(f"{where}: the paper has no equation {n}")
            elif n not in shown:
                bad.append(f"{where}: chapter {ch} does not display it; remove the entry")
            if not isinstance(e, dict) or e.get("kind") not in KINDS:
                bad.append(f"{where}: kind must be one of {', '.join(KINDS)}")
                continue
            k = e["kind"]
            counts.setdefault(ch, {}).setdefault(k, 0)
            counts[ch][k] += 1
            fields = set(e) - {"kind"}
            for missing in sorted(KINDS[k] - fields):
                bad.append(f"{where}: kind {k} needs \"{missing}\"")
            for extra in sorted(fields - KINDS[k] - OPTIONAL):
                bad.append(f"{where}: kind {k} takes no \"{extra}\"")
            for fld in fields:
                if not isinstance(e[fld], str) or not e[fld].strip():
                    bad.append(f"{where}: \"{fld}\" must be a non-empty string")
            name = e.get("name")
            if isinstance(name, str) and name.split(".")[-1] not in declared:
                bad.append(f"{where}: no model source declares {name.split('.')[-1]} (for {name})")
            loc = e.get("at")
            if isinstance(loc, str) and loc and not any(loc in t for t in sources):
                bad.append(f"{where}: the locator {loc!r} occurs in no model source")
        missing = sorted(set(shown) - set(entries), key=lambda n: [int(x) if x.isdigit() else x for x in n.split(".")])
        if ch in unmapped:
            if not missing:
                bad.append(f"{rel}: complete; remove {ch} from model-map/unmapped.json")
        else:
            for n in missing:
                bad.append(f"{rel}: chapter {ch} displays ({n}) but the map has no entry for it")
    if "--counts" in sys.argv[1:]:
        for ch, c in sorted(counts.items()):
            print(f"{ch}: " + ", ".join(f"{k} {v}" for k, v in sorted(c.items())) + f" (total {sum(c.values())})")
    for b in bad:
        print(b)
    print(f"check-model-map: {len(bad)} problem(s); {len(unmapped)} chapter(s) still unmapped")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
