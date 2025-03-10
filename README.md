# Accessibility

Postulating the function extensionality, we provide an Agda-proof for the introduction and elimination rules of the accessibility Acc, which is the accessible part of the membership relation in Aczel's interpretation of constructive Zermelo-Fraenkel set theory (CZF) in Martin-Löf type theory (MLTT).

## Outline

`Preliminaries.agda`:
We define several notions (e.g., W-types) of the core type theory. In addition, We also prove some lemmas on identity types which we will use in the proof for the introduction and elimination rules of Acc.

`CZFBasics.agda`:
Basic facts for Aczel's interpretation of CZF in MLTT are provided. For instance, the type of iterative sets is defined.

`CZFAxioms.agda`:
All axioms of CZF are validated in MLTT. Moreover, the induction principle for transitive closures of sets is proved.

`Accessibility.agda`:
The accessibility Acc is defined by using the induction principle for transitive closures of sets, so that the introduction and elimination rules of Acc are derivable.
