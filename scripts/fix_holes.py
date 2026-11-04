"""Set the number of `?_` holes in each `Name.run` call of a composition to the number of fact
hypotheses its (generated) theorem takes: `python3 scripts/fix_holes.py FILE Name...`."""
import re, sys
f, names = sys.argv[1], sys.argv[2:]
s = open(f).read()
for name in names:
    t = open(f"Services/Witness/{name}.lean").read()
    stmt = t[t.index("theorem run"):]
    stmt = stmt[:stmt.index(": ∃ ω'")]
    n = len(re.findall(r"^    \(h[a-z]", stmt, re.M))
    pat = re.compile(r"(\(%s\.run p P env (?:(?!\?_).)*?)((?: \?_)+)\)" % re.escape(name), re.S)
    m = pat.search(s)
    assert m, name
    s = s[:m.start()] + m.group(1) + " ?_" * n + ")" + s[m.end():]
    print(name, n)
open(f, "w").write(s)
