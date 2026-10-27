#!/usr/bin/env python3
"""Checks that README.md, PROOF.md, FOREST.md and FORS.md cite only files and Lean names that exist.

From formal/sphincs, after `lake env lean scripts/Reach.lean` (which writes reach.txt):
    python3 scripts/doc_check.py
Every relative link must point to an existing file. Every code span that looks like a Lean name or a
file must be a module of `LeanForest` or `LeanFors`, a file, or the suffix of a declaration of either
(or be listed in PROSE below). Exits 1 and lists the offenders otherwise.
"""
import glob, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DOCS = ['README.md', 'PROOF.md', 'FOREST.md', 'FORS.md']
LIBS = ['LeanForest', 'LeanFors']
# Code spans that are not Lean names: axioms, tactics, script commands, the leanVM commit, symbols.
PROSE = {'propext', 'Classical.choice', 'Quot.sound', 'sorry', 'native_decide', 'check', 'write',
         'b7a107256', 'SphincsSecurity', 'LAYERED', 'PARAMS', 'idx', 'wbar', "extractLsb'",
         'fors_log2_lifetime', 'requestedSecurity'}


def module_names(span, modules):
    """The modules a span names: `SeedElimination`, `Certificates.H24` or `H24`, or a glob `Cover*`."""
    pat = re.compile(r'(.*\.)?' + re.escape(span).replace('\\*', '[^.]*') + '$')
    return {m for m in modules if pat.match(m.split('.', 1)[-1])}


def main():
    rows = [line.split('|') for line in open(os.path.join(ROOT, 'reach.txt')).read().splitlines()]
    modules = {r[0] for r in rows}
    suffixes = set()
    for r in rows:
        parts = r[1].split('.')
        for k in range(1, len(parts) + 1):
            suffixes.add('.'.join(parts[-k:]))
    bad = []
    for doc in DOCS:
        text = open(os.path.join(ROOT, doc)).read()
        text_no_blocks = re.sub(r'```.*?```', '', text, flags=re.S)
        for link in re.findall(r'\]\(([^)\s]+)\)', text):
            if re.match(r'[a-z]+:', link) or link.startswith('#'):
                continue
            if not os.path.exists(os.path.join(ROOT, link.split('#')[0])):
                bad.append((doc, 'link', link))
        for span in set(re.findall(r'`([^`\n]+)`', text_no_blocks)):
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.'/*]*", span) or span in PROSE:
                continue
            if re.search(r'\.(lean|py|md|toml|txt)$', span) or '/' in span:
                if not any(glob.glob(os.path.join(ROOT, d, span))
                           for d in ('', *LIBS, 'scripts', '../..')):
                    bad.append((doc, 'file', span))
                continue
            if len(span) <= 2 or span in suffixes or span in LIBS or module_names(span, modules):
                continue
            # `Module.decl`: a declaration of that module
            head, _, tail = span.partition('.')
            if tail and module_names(head, modules) and any(
                    r[0] in module_names(head, modules) and r[1].endswith('.' + tail) for r in rows):
                continue
            bad.append((doc, 'name', span))
    for doc, kind, span in sorted(bad):
        print(f'{doc}: unknown {kind} `{span}`')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
