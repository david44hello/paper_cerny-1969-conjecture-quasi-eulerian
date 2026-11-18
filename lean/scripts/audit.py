#!/usr/bin/env python3
"""audit.py — the claim audit: one status per row of CernyQE/Paper/Statements.lean, from Lean's own `#print axioms`.
Version 0.10, 2026-11-05: first for this project; adapted from an earlier project's claim audit (no facts or checks
  as binders here). Freshness is asked of Lake (`lake --no-build build`), never judged by file times.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.

Usage:  scripts/audit.py           the audit: it re-runs itself as `scripts/lean_run.sh lake env python3 scripts/audit.py
                                   --locked`, so the freshness check, the one `lean` run of the generated file and the
                                   reading of the sources all happen while the shared compile lock is held
        scripts/audit.py --test    self-test (no Lean)
        (--locked is that inner step; it refuses to run unless started that way)
A reader's machine has no lock and no gate: `LEAN_RUN_LOCK=none LEAN_RUN_GATE=none scripts/audit.py`.
Needs the built .olean files of CernyQE.Paper.Statements and its imports (scripts/check.sh builds them first).
Writes, with no time stamps (a rerun on the same build rewrites every output byte for byte): AUDIT.md and CLAIMS.json
at the project root, and scripts/audit_axioms.lean (only when its content changes).
Statuses (one per row; the words of the project's rules):
  PROVED              `#print axioms` lists only propext, Classical.choice, Quot.sound
  PROVED FROM CITED   also axioms of CernyQE/Cited/ (named after the status)
  CITED               the row's whole proof is one cited axiom applied to arguments: the paper quoting a result
  not proved yet      sorryAx occurs (the row, or a row its proof uses, is still open)
  FAIL: <why>         any other axiom, or a row missing from Lean's output
Exit: 0 no FAIL row | 1 a FAIL row or a failed step | 2 usage/setup error | 3 the build is not current (Lake)
"""
import json
import os
import re
import subprocess
import sys
from pathlib import Path

LIB = "CernyQE"
ROOT_MODULE = LIB + ".Paper.Statements"
STANDARD = ("propext", "Classical.choice", "Quot.sound")
SHORT_NAMES = {"choice": "Classical.choice"}   # under `open Classical`, Lean prints `choice`
SORRY_AXIOM = "sorryAx"
NOT_PROVED = "not proved yet"
PROJECT = Path(__file__).resolve().parent.parent
SCRIPTS = PROJECT / "scripts"
RUNNER = SCRIPTS / "lean_run.sh"
STATEMENTS = PROJECT / LIB / "Paper" / "Statements.lean"
CITED_DIR = PROJECT / LIB / "Cited"
GENERATED = SCRIPTS / "audit_axioms.lean"
LOCKED_FLAG = "AUDIT_PY_LOCKED"

DECL_RE = re.compile(r"^(theorem|lemma|axiom)\s+([^\s:(\[{]+)", re.M)
SCOPE_RE = re.compile(r"^(namespace|section|end)\b[ \t]*([^\s-]*)", re.M)
TEX_RE = re.compile(r"tex:\s*([0-9]+(?:-[0-9]+)?)")
OUTPUT_RE = re.compile(r"^'(.+?)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", re.M | re.S)


def declarations(text, kinds):
    """[(full name, kind, start, end)] of the declarations of the given kinds, with their namespace prefix.
    A declaration runs to the next declaration or scope command (or the end of the file)."""
    events = sorted([(m.start(), "decl", m) for m in DECL_RE.finditer(text)] +
                    [(m.start(), "scope", m) for m in SCOPE_RE.finditer(text)], key=lambda e: e[0])
    stack, out = [], []
    for index, (start, kind, match) in enumerate(events):
        if kind == "scope":
            command, name = match.group(1), match.group(2)
            if command in ("namespace", "section"):
                stack.append((command, name))
            elif stack:
                stack.pop()
            continue
        end = events[index + 1][0] if index + 1 < len(events) else len(text)
        if match.group(1) in kinds:
            prefix = [part for command, name in stack if command == "namespace" for part in name.split(".") if part]
            out.append((".".join(prefix + [match.group(2)]), match.group(1), start, end))
    return out


def tex_pointer(text, start):
    """The tex:N pointers of the docstring just above a declaration ('' if none)."""
    before = text[:start].rstrip()
    while True:   # attributes and `open ... in` may stand between the docstring and the declaration
        last = before.rsplit("\n", 1)[-1].strip()
        if last.startswith("@[") or (last.startswith("open ") and last.endswith(" in")):
            before = before[: before.rfind(last)].rstrip()
            continue
        break
    return ", ".join(TEX_RE.findall(last_doc(before)))


def last_doc(before):
    """The docstring that ends the text `before` ('' if it does not end with one)."""
    start = before.rfind("/--")
    return before[start + 3:-2] if start >= 0 and before.endswith("-/") else ""


def body_of(text, start, end):
    """The proof text after the declaration's `:=` (the first one at bracket depth 0 that ends a line or opens `by`)."""
    span = text[start:end]
    match = re.search(r":=(?=\s*by\b|[ \t]*\n)", span)
    return span[match.end():].strip() if match else ""


def is_bare_cited(body, cited_names):
    """The row's whole proof is one cited axiom applied to arguments (`Cited.x a b` or `by exact Cited.x a b`)."""
    body = re.sub(r"^by\s+exact\s+", "", body.strip())
    head = body.split(None, 1)[0] if body else ""
    return any(head == name or name.endswith("." + head) and head.startswith("Cited.") for name in cited_names)


def read_rows(text):
    return [{"name": name, "tex": tex_pointer(text, start), "bare_cited_body": body_of(text, start, end)}
            for name, _, start, end in declarations(text, ("theorem", "lemma"))]


def read_cited(cited_dir):
    """[(full name, docstring)] of the axioms declared in the Cited/ files."""
    out = []
    for path in sorted(Path(cited_dir).glob("**/*.lean")) if Path(cited_dir).is_dir() else []:
        text = path.read_text(encoding="utf-8")
        for name, _, start, _ in declarations(text, ("axiom",)):
            out.append((name, " ".join(last_doc(text[:start].rstrip()).split())))
    return out


def audit_lean(full_names):
    lines = ["-- Generated by scripts/audit.py; do not edit.", "import " + ROOT_MODULE, ""]
    lines += ["#print axioms " + name for name in full_names]
    return "\n".join(lines) + "\n"


def write_if_changed(path, content):
    """Rewrite only when the content differs (a replay must not see a file change under it)."""
    path = Path(path)
    if path.is_file() and path.read_text(encoding="utf-8") == content:
        return False
    path.write_text(content, encoding="utf-8")
    return True


def parse_output(output):
    """{full name: [axiom, ...]} from `#print axioms` output (lists may wrap over several lines)."""
    found = {}
    for match in OUTPUT_RE.finditer(output):
        names = [] if match.group(2) is None else [" ".join(a.split()) for a in match.group(2).split(",")]
        found[match.group(1)] = [SHORT_NAMES.get(a, a) for a in names if a]
    return found


def classify(axioms, cited, bare):
    extra = [a for a in axioms if a not in STANDARD and a not in cited and a != SORRY_AXIOM]
    used = sorted(a for a in axioms if a in cited)
    if SORRY_AXIOM in axioms:
        return NOT_PROVED
    if extra:
        return "FAIL: axiom " + ", ".join(sorted(extra))
    if used:
        return "CITED" if bare and len(used) == 1 else "PROVED FROM CITED " + ", ".join(used)
    return "PROVED"


def statuses(rows, found, cited_names):
    out = []
    for row in rows:
        if row["name"] not in found:
            out.append({**row, "status": "FAIL: missing from the Lean output", "axioms": []})
            continue
        axioms = found[row["name"]]
        bare = is_bare_cited(row["bare_cited_body"], cited_names)
        out.append({**row, "status": classify(axioms, set(cited_names), bare), "axioms": axioms})
    return out


def totals(results):
    keys = ("PROVED", "PROVED FROM CITED", "CITED", NOT_PROVED, "FAIL")
    counts = {key: 0 for key in keys}
    for row in results:
        counts[next(key for key in keys if row["status"].startswith(key))] += 1
    return counts


def short(name):
    return name[len(LIB) + 1:] if name.startswith(LIB + ".") else name


def render(results, cited):
    counts = totals(results)
    lines = ["# AUDIT — the status of every row of CernyQE/Paper/Statements.lean", "",
             "Written by `scripts/audit.py` from Lean's own `#print axioms` output; do not edit.", "",
             "Totals: rows %d; " % len(results) + "; ".join(f"{k} {v}" for k, v in counts.items()) + ".", "",
             "## Cited results (axioms of CernyQE/Cited/)", ""]
    lines += [f"- `{short(name)}`: {doc}" for name, doc in cited] or ["- none"]
    lines += ["", "## Rows", "", "| row | text | status | axioms beyond propext, Classical.choice, Quot.sound |",
              "|---|---|---|---|"]
    for row in results:
        beyond = ", ".join(short(a) for a in row["axioms"] if a not in STANDARD) or "-"
        lines.append(f"| `{short(row['name'])}` | {row['tex'] or '-'} | {row['status']} | {beyond} |")
    return "\n".join(lines) + "\n", counts


def claims_json(results, cited, counts):
    rows = [{"name": short(r["name"]), "tex": r["tex"], "status": r["status"], "axioms": r["axioms"]} for r in results]
    data = {"rows": rows, "totals": counts, "cited": [{"name": short(n), "doc": d} for n, d in cited]}
    return json.dumps(data, indent=1, ensure_ascii=False) + "\n"


def run_locked():
    """Inside the lock: freshness (Lake), sources, one Lean run, reports."""
    if os.environ.get(LOCKED_FLAG) != "1":
        raise SystemExit("audit.py --locked: start it as scripts/audit.py (it takes the lock itself)")
    fresh = subprocess.run(["lake", "--no-build", "build", ROOT_MODULE], cwd=PROJECT, capture_output=True, text=True)
    if fresh.returncode != 0:
        sys.stderr.write(fresh.stdout + fresh.stderr)
        print("AUDIT: Lake says the build is not current; build first: scripts/lean_run.sh lake build", file=sys.stderr)
        raise SystemExit(3)
    text = STATEMENTS.read_text(encoding="utf-8")
    rows, cited = read_rows(text), read_cited(CITED_DIR)
    write_if_changed(GENERATED, audit_lean([row["name"] for row in rows]))
    lean = subprocess.run(["lean", str(GENERATED.relative_to(PROJECT))], cwd=PROJECT, capture_output=True, text=True)
    output = lean.stdout + lean.stderr
    if lean.returncode != 0 or re.search(r"^\S+:\d+:\d+: error", output, re.M):
        sys.stderr.write(output)
        raise SystemExit("AUDIT: the Lean run of scripts/audit_axioms.lean failed")
    results = statuses(rows, parse_output(output), [name for name, _ in cited])
    report, counts = render(results, cited)
    write_if_changed(PROJECT / "AUDIT.md", report)
    write_if_changed(PROJECT / "CLAIMS.json", claims_json(results, cited, counts))
    print(report.splitlines()[4])
    return 1 if counts["FAIL"] else 0


def run_outer():
    env = dict(os.environ, **{LOCKED_FLAG: "1"})
    command = [str(RUNNER), "lake", "env", "python3", str(Path(__file__).resolve()), "--locked"]
    return subprocess.run(command, cwd=PROJECT, env=env).returncode


def run_tests():
    text = ("namespace CernyQE\nopen Classical\nsection General\nvariable (A : Nat)\n\n"
            "/-- Lemma 1, tex:10-12. -/\ntheorem row_a (x : Nat) : x = x :=\n  row_a_proved x\n\n"
            "/-- tex:20: quoted. -/\nopen Classical in\ntheorem row_b (n : Nat) : n = n := by\n  exact Cited.c1 n\n\n"
            "/-- no pointer -/\ntheorem row_c' : True := by\n  sorry\nend General\nend CernyQE\n"
            "theorem outside : True := trivial\n")
    rows = read_rows(text)
    assert [r["name"] for r in rows] == ["CernyQE.row_a", "CernyQE.row_b", "CernyQE.row_c'", "outside"], rows
    assert [r["tex"] for r in rows] == ["10-12", "20", "", ""], [r["tex"] for r in rows]
    cited_names = ["CernyQE.Cited.c1"]
    assert not is_bare_cited(rows[0]["bare_cited_body"], cited_names)
    assert is_bare_cited(rows[1]["bare_cited_body"], cited_names)
    assert is_bare_cited("CernyQE.Cited.c1 n hn", cited_names) and not is_bare_cited("Cited.c2 n", cited_names)
    out = ("'CernyQE.row_a' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"
           "'CernyQE.row_b' depends on axioms: [propext, CernyQE.Cited.c1]\n"
           "'CernyQE.row_c'' depends on axioms: [sorryAx]\n'outside' does not depend on any axioms\n"
           "'CernyQE.x' depends on axioms: [choice, Quot.sound, Foo.bar]\n")
    found = parse_output(out)
    assert found["CernyQE.row_a"] == list(STANDARD) and found["outside"] == [] and "CernyQE.row_c'" in found
    assert found["CernyQE.x"] == ["Classical.choice", "Quot.sound", "Foo.bar"]
    cited = set(cited_names)
    assert classify(found["CernyQE.row_a"], cited, False) == "PROVED"
    assert classify(found["CernyQE.row_b"], cited, True) == "CITED"
    assert classify(found["CernyQE.row_b"], cited, False) == "PROVED FROM CITED CernyQE.Cited.c1"
    assert classify(found["CernyQE.row_c'"], cited, False) == NOT_PROVED
    assert classify(found["CernyQE.x"], cited, False) == "FAIL: axiom Foo.bar"
    assert classify(["sorryAx", "Foo.bar"], cited, False) == NOT_PROVED   # open rows are reported as open first
    results = statuses(rows[:3] + [{"name": "CernyQE.gone", "tex": "", "bare_cited_body": ""}], found, cited_names)
    assert [r["status"] for r in results] == ["PROVED", "CITED", NOT_PROVED, "FAIL: missing from the Lean output"]
    report, counts = render(results, [("CernyQE.Cited.c1", "Cerny 1964, quoted.")])
    assert counts == {"PROVED": 1, "PROVED FROM CITED": 0, "CITED": 1, NOT_PROVED: 1, "FAIL": 1}
    assert "Totals: rows 4; PROVED 1; PROVED FROM CITED 0; CITED 1; not proved yet 1; FAIL 1." in report
    assert "| `row_b` | 20 | CITED | Cited.c1 |" in report and report == render(results, [("CernyQE.Cited.c1",
           "Cerny 1964, quoted.")])[0]
    assert json.loads(claims_json(results, [], counts))["rows"][2] == {"name": "row_c'", "tex": "", "status":
           NOT_PROVED, "axioms": ["sorryAx"]}
    generated = audit_lean(["CernyQE.row_a"])
    assert generated.splitlines()[1] == "import " + ROOT_MODULE and "#print axioms CernyQE.row_a" in generated
    cited_text = "namespace CernyQE.Cited\n/-- Source, p. 1: quoted. -/\naxiom c1 (n : Nat) : n = n\nend CernyQE.Cited\n"
    assert declarations(cited_text, ("axiom",))[0][0] == "CernyQE.Cited.c1"
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "x.lean"
        assert write_if_changed(path, "a") and not write_if_changed(path, "a") and write_if_changed(path, "b")
        (Path(tmp) / "Cited").mkdir()
        (Path(tmp) / "Cited" / "C1.lean").write_text(cited_text, encoding="utf-8")
        assert read_cited(Path(tmp) / "Cited") == [("CernyQE.Cited.c1", "Source, p. 1: quoted.")]
        assert read_cited(Path(tmp) / "none") == []
    print("PASS: audit.py --test (rows and namespaces, tex pointers, cited axioms and bare CITED bodies, the wrapped "
          "axiom lists, the five statuses, report and JSON, write only on change)")


def main():
    args = sys.argv[1:]
    if args == ["--test"]:
        run_tests()
    elif args == ["--locked"]:
        raise SystemExit(run_locked())
    elif not args:
        raise SystemExit(run_outer())
    else:
        raise SystemExit(2 if print(__doc__, file=sys.stderr) is None else 2)


if __name__ == "__main__":
    main()
