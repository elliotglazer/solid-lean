#!/usr/bin/env python3
"""Regenerate Palomar/Statement.lean from Palomar/Challenge.lean, or check that it is in sync.

Statement.lean is the Challenge without its (sorried) target theorem: the shared
definitions the Solution proves things about.  The comparator requires the two
copies to be identical declarations, so this script is the only way to edit
Statement.lean.  Usage: sync_statement.py [--check]
"""
import sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
CHALLENGE = ROOT / "Palomar" / "Challenge.lean"
STATEMENT = ROOT / "Palomar" / "Statement.lean"
TARGET_MARKER = "/-- **The tower theory `H` is solid**"
END_MARKER = "end SolidLean.Palomar"

def generate() -> str:
    src = CHALLENGE.read_text(encoding="utf-8")
    i = src.index(TARGET_MARKER)
    j = src.index(END_MARKER, i)
    header = ("-- GENERATED from Palomar/Challenge.lean by scripts/sync_statement.py; do not edit.\n"
              "-- The definitions of the Challenge, without its target theorem.\n")
    return header + src[:i].rstrip("\n") + "\n\n" + src[j:]

def main() -> int:
    new = generate()
    if "--check" in sys.argv:
        old = STATEMENT.read_text(encoding="utf-8") if STATEMENT.exists() else ""
        if old != new:
            print("Palomar/Statement.lean is out of sync with Palomar/Challenge.lean; run scripts/sync_statement.py")
            return 1
        print("Palomar/Statement.lean is in sync")
        return 0
    STATEMENT.write_text(new, encoding="utf-8")
    print(f"wrote {STATEMENT}")
    return 0

if __name__ == "__main__":
    sys.exit(main())
