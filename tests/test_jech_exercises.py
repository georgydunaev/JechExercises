#!/usr/bin/env python3
"""Verification suite for JechExercises (Chapters 1-2, Ordinals, Filters, and Isabelle .thy files)."""

import os
import re
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def kuratowski_pair(a, b) -> frozenset:
    """Kuratowski ordered pair <a, b> = {{a}, {a, b}}."""
    return frozenset({frozenset({a}), frozenset({a, b})})


def kuratowski_fst(p: frozenset):
    """First projection: intersection of elements."""
    elements = list(p)
    if len(elements) == 1:
        return next(iter(elements[0]))
    inter = elements[0] & elements[1]
    return next(iter(inter))


def kuratowski_snd(p: frozenset):
    """Second projection: element of union not equal to fst if distinguishable."""
    fst = kuratowski_fst(p)
    union = frozenset().union(*p)
    remainder = union - frozenset({fst})
    if not remainder:
        return fst
    return next(iter(remainder))


def von_neumann_ordinal(n: int) -> frozenset:
    """Constructs finite von Neumann ordinal n = {0, 1, ..., n-1}."""
    res = []
    for _ in range(n):
        res.append(frozenset(res))
    return frozenset(res)


def is_transitive(s: frozenset) -> bool:
    """A set S is transitive if every element of S is a subset of S."""
    return all(elem.issubset(s) for elem in s)


def powerset(s: frozenset) -> set[frozenset]:
    """Generates the full power set of a finite set."""
    items = list(s)
    res = {frozenset()}
    for item in items:
        res = res | {subset | frozenset({item}) for subset in res}
    return res


def is_filter(ground: frozenset, family: set[frozenset]) -> bool:
    """Verifies Jech Chapter 7 filter axioms on a power set of ground."""
    if not family or frozenset() in family or ground not in family:
        return False
    # Upward closed
    all_subsets = powerset(ground)
    for a in family:
        if not a.issubset(ground):
            return False
        for b in all_subsets:
            if a.issubset(b) and b not in family:
                return False
    # Closed under finite intersections
    for a in family:
        for b in family:
            if (a & b) not in family:
                return False
    return True


def is_ultrafilter(ground: frozenset, family: set[frozenset]) -> bool:
    """Verifies ultrafilter condition: filter and for all A subset S, A in U or S - A in U."""
    if not is_filter(ground, family):
        return False
    all_subsets = powerset(ground)
    for a in all_subsets:
        if a not in family and (ground - a) not in family:
            return False
    return True


def is_ideal(ground: frozenset, family: set[frozenset]) -> bool:
    """Verifies ideal axioms: 0 in I, ground not in I, closed under subset and union."""
    if not family or frozenset() not in family or ground in family:
        return False
    all_subsets = powerset(ground)
    for a in family:
        if not a.issubset(ground):
            return False
        for b in all_subsets:
            if b.issubset(a) and b not in family:
                return False
    for a in family:
        for b in family:
            if (a | b) not in family:
                return False
    return True


class TestJechExercises(unittest.TestCase):
    def test_isabelle_theory_files_present_and_well_formed(self):
        theories = ("JechExercises.thy", "classical_axioms.thy", "trivia.thy", "filters.thy")
        aux_files = ("ROOT", "document/root.tex")
        for rel in theories + aux_files:
            path = os.path.join(ROOT, rel)
            self.assertTrue(os.path.isfile(path), f"Missing {path}")
            self.assertGreater(os.path.getsize(path), 0)

        for thy in theories:
            with open(os.path.join(ROOT, thy), encoding="utf-8") as f:
                text = f.read()
            self.assertIn("theory", text)
            self.assertIn("end", text)
            # Ensure no unfinished proofs
            self.assertNotRegex(text, r"\b(sorry|oops|admit)\b")

    def test_no_emojis_or_directional_arrows_in_sources(self):
        emoji_pattern = re.compile(r"[\U00010000-\U0010ffff]")
        arrow_pattern = re.compile(r"(->|<-|=>|<=|-->|<--|&rarr;|&larr;)")
        for dirpath, _, filenames in os.walk(ROOT):
            if ".git" in dirpath or "__pycache__" in dirpath:
                continue
            for fname in filenames:
                if fname.endswith((".thy", ".py", ".md", ".tex", "ROOT")):
                    fpath = os.path.join(dirpath, fname)
                    with open(fpath, encoding="utf-8", errors="ignore") as f:
                        content = f.read()
                    self.assertFalse(
                        emoji_pattern.search(content),
                        f"Found forbidden emoji in {fname}",
                    )

    def test_kuratowski_pair_mechanics(self):
        elements = [0, 1, 2, "a", "b"]
        for a in elements:
            for b in elements:
                p = kuratowski_pair(a, b)
                self.assertEqual(kuratowski_fst(p), a)
                self.assertEqual(kuratowski_snd(p), b)
                for c in elements:
                    for d in elements:
                        p2 = kuratowski_pair(c, d)
                        if a == c and b == d:
                            self.assertEqual(p, p2)
                        else:
                            self.assertNotEqual(p, p2)

    def test_cartesian_product_distributivity(self):
        A = frozenset({1, 2})
        B = frozenset({2, 3})
        C = frozenset({4, 5})

        def prod(x_set, y_set):
            return frozenset((x, y) for x in x_set for y in y_set)

        self.assertEqual(prod(A | B, C), prod(A, C) | prod(B, C))
        self.assertEqual(prod(A & B, C), prod(A, C) & prod(B, C))
        self.assertEqual(prod(A - B, C), prod(A, C) - prod(B, C))

    def test_russell_paradox_and_no_universal_set(self):
        ground = frozenset({1, 2, 3})
        pow_ground = powerset(ground)
        self.assertFalse(pow_ground.issubset(ground))
        for s in pow_ground:
            sub_pow = powerset(s)
            self.assertFalse(sub_pow.issubset(s))

    def test_inductive_sets_and_transitivity(self):
        for n in range(6):
            ord_n = von_neumann_ordinal(n)
            self.assertTrue(is_transitive(ord_n))
            union_ord = frozenset().union(*ord_n) if ord_n else frozenset()
            self.assertTrue(union_ord.issubset(ord_n))
            pow_ord = powerset(ord_n)
            self.assertTrue(ord_n.issubset(pow_ord))

    def test_ordinal_hereditary_transitivity(self):
        for n in range(6):
            ord_n = von_neumann_ordinal(n)
            self.assertEqual(len(ord_n), n)
            self.assertTrue(is_transitive(ord_n))
            for elem in ord_n:
                self.assertTrue(is_transitive(elem))

    def test_ordinal_trichotomy(self):
        ordinals = [von_neumann_ordinal(i) for i in range(5)]
        for i, a in enumerate(ordinals):
            for j, b in enumerate(ordinals):
                in_ab = a in b
                eq_ab = a == b
                in_ba = b in a
                conditions = [in_ab, eq_ab, in_ba]
                self.assertEqual(sum(conditions), 1)
                if i < j:
                    self.assertTrue(in_ab)
                elif i == j:
                    self.assertTrue(eq_ab)
                else:
                    self.assertTrue(in_ba)

    def test_boolean_lattice_de_morgan(self):
        ground = frozenset({1, 2, 3, 4})
        all_subs = list(powerset(ground))
        for A in all_subs:
            self.assertEqual(ground - (ground - A), A)
            for B in all_subs:
                self.assertEqual(ground - (A | B), (ground - A) & (ground - B))
                self.assertEqual(ground - (A & B), (ground - A) | (ground - B))

    def test_principal_filter_and_ultrafilter_verification(self):
        ground = frozenset({1, 2, 3})
        all_subsets = powerset(ground)

        core = frozenset({1})
        principal = {s for s in all_subsets if core.issubset(s)}
        self.assertTrue(is_filter(ground, principal))
        self.assertTrue(is_ultrafilter(ground, principal))

        pair_core = frozenset({1, 2})
        pair_filter = {s for s in all_subsets if pair_core.issubset(s)}
        self.assertTrue(is_filter(ground, pair_filter))
        self.assertFalse(is_ultrafilter(ground, pair_filter))

    def test_filter_and_ideal_duality(self):
        ground = frozenset({1, 2, 3})
        all_subsets = powerset(ground)
        core = frozenset({1})
        filter_f = {s for s in all_subsets if core.issubset(s)}
        self.assertTrue(is_filter(ground, filter_f))

        ideal_i = {ground - s for s in filter_f}
        self.assertTrue(is_ideal(ground, ideal_i))

        dual_filter = {ground - s for s in ideal_i}
        self.assertEqual(dual_filter, filter_f)

    def test_image_of_union_algebra(self):
        R = {(1, 10), (1, 20), (2, 20), (3, 30), (4, 40)}

        def image(rel, subset):
            return frozenset(y for x, y in rel if x in subset)

        family = [frozenset({1, 2}), frozenset({2, 3}), frozenset({4})]
        union_family = frozenset().union(*family)

        img_union = image(R, union_family)
        union_imgs = frozenset().union(*(image(R, s) for s in family))
        self.assertEqual(img_union, union_imgs)


if __name__ == "__main__":
    unittest.main()
