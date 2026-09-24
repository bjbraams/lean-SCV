#!/usr/bin/env python3
"""Replace line-ending := or := by and the following nonblank lines with sorry."""

import argparse
import re
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", help="Lean source file")
    args = parser.parse_args()

    skipping = False
    with open(args.file, encoding="utf-8") as source:
        for line in source:
            if skipping:
                if line.strip():
                    continue
                skipping = False
            line, replacements = re.subn(r":=(?: by)?[ \t]*(?=\n?\Z)", ":= by sorry", line)
            sys.stdout.write(line)
            skipping = bool(replacements)


if __name__ == "__main__":
    main()
