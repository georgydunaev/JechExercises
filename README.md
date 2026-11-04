# JechExercises — Isabelle/ZF Formalization of Exercises from Thomas Jech's *Set Theory*

## Overview
`JechExercises` contains Isabelle/ZF formalizations of selected foundational exercises and lemmas accompanying Thomas Jech's *Set Theory* (3rd Millennium Edition):

- [`JechExercises.thy`](file:///botworkspace/JechExercises/JechExercises.thy): Core exercise formalizations in Isabelle/ZF.
- [`classical_axioms.thy`](file:///botworkspace/JechExercises/classical_axioms.thy): Classical set-theoretic axiom schemas and helper rules.
- [`trivia.thy`](file:///botworkspace/JechExercises/trivia.thy): Elementary set-theoretic identities and warm-up lemmas.
- [`ROOT`](file:///botworkspace/JechExercises/ROOT) & [`document/root.tex`](file:///botworkspace/JechExercises/document/root.tex): Isabelle session build configuration and LaTeX proof document wrapper.

## Running Verification Tests
```bash
python3 -m unittest discover -s tests -p "test_*.py"
```
