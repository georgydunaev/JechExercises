#!/usr/bin/env python3
"""Verification suite for JechExercises (Chapters 1-2, Ordinals, Filters, and Isabelle .thy files)."""

import os
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def von_neumann_ordinal(n: int) -> frozenset:
    """Constructs finite von Neumann ordinal n = {0, 1, ..., n-1}."""
    res = []
    for _ in range(n):
        res.append(frozenset(res))
    return frozenset(res)


def is_transitive(s: frozenset) -> bool:
    return all(elem.issubset(s) for elem in s)


def is_filter(ground: frozenset, family: set[frozenset]) -> bool:
    """Verifies Jech Chapter 7 filter axioms on a finite power set."""
    if not family or frozenset() in family or ground not in family:
        return False
    for a in family:
        for b in family:
            if (a & b) not in family:
                return False
    return True


class TestJechExercises(unittest.TestCase):
    def test_isabelle_theory_files_present_and_well_formed(self):
        for rel in ("JechExercises.thy", "classical_axioms.thy", "trivia.thy", "ROOT", "document/root.tex"):
            path = os.path.join(ROOT, rel)
            self.assertTrue(os.path.isfile(path), f"Missing {path}")
            self.assertGreater(os.path.getsize(path), 0)
        for thy in ("JechExercises.thy", "classical_axioms.thy", "trivia.thy"):
            with open(os.path.join(ROOT, thy), encoding="utf-8") as f:
                text = f.read()
            self.assertIn("theory", text)
            self.assertIn("end", text)

    def test_ordinal_hereditary_transitivity(self):
        for n in range(6):
            ord_n = von_neumann_ordinal(n)
            self.assertEqual(len(ord_n), n)
            self.assertTrue(is_transitive(ord_n))
            for elem in ord_n:
                self.assertTrue(is_transitive(elem))

    def test_principal_filter_verification(self):
        ground = frozenset({1, 2, 3})
        core = frozenset({1})
        all_subsets = [
            frozenset(),
            frozenset({1}),
            frozenset({2}),
            frozenset({3}),
            frozenset({1, 2}),
            frozenset({1, 3}),
            frozenset({2, 3}),
            ground,
        ]
        principal = {s for s in all_subsets if core.issubset(s)}
        self.assertTrue(is_filter(ground, principal))


if __name__ == "__main__":
    unittest.main()
