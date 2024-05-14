# Formal BOOK

A collaborative, work-in-progress attempt to formalize [Proofs from THE BOOK](https://link.springer.com/book/10.1007/978-3-662-57265-8) using [Lean4](https://leanprover.github.io/lean4/doc/whatIsLean.html).


![Formal Proofs from THE BOOK](formal_proofs_form_the_book.svg)

## Structure

For each chapter in the book (we follow the latest, sixth edition), there is a lean source file containing as many formalized definitions, lemmas, theorems and proofs as we can reasonably currently formalize using [Lean's mathlib4](https://github.com/leanprover-community/mathlib4).

The goal is to make the formalizations of the proofs as close as possible to the proofs in the book, even if a different proof for a theorem might already be present in mathlib or is more suitable for formalization.

We follow the [naming conventions](https://github.com/leanprover-community/mathlib4/wiki/Porting-wiki#naming-convention) and [code style](https://leanprover-community.github.io/contribute/style.html) of mathlib4.

## Installation

This project uses Lean 4. You first need to [install elan and lean](https://leanprover.github.io/lean4/doc/setup.html) and then run
```shell
lake exe cache get
lake build
code .
```
The last step only opens vscode in case you want to use that.

## Chapters

Status of the chapters:

  - :x: chapter is just a stub
  - :thought_balloon: work in progress, formalization of some statements still missing
  - :speech_balloon: work in progress, all statements formalized, some proofs still missing
  - :tada: chapter is completely formalized (possibly excluding the Appendix)

### Number Theory
  1. :speech_balloon: [Six proofs of the infinity of primes](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_01)
  2. :speech_balloon: [Bertrand's postulate](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_02)
  3. :speech_balloon: [Binomial coefficients are (almost) never powers](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_03)
  4. :x: [Representing numbers as sums of two squares](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_04)
  5. :thought_balloon: [The law of quadratic reciprocity](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_05)
  6. :thought_balloon: [Every finite division ring is a field](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_06)
  7. :thought_balloon: [The spectral theorem and Hadamard's determinant problem](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_07)
  8. :thought_balloon: [Some irrational numbers](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_08)
  9. :x: [Four times ](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_09)

### Geometry
  10. :x: [Hilbert's third problem: decomposing polyhedra](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_10)
  11. :x: [Lines in the plane and decompositions of graphs](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_11)
  12. :x: [The slope problem](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_12)
  13. :x: [Three applications of Euler's formula](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_13)
  14. :x: [Cauchy's rigidity theorem](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_14)
  15. :x: [The Borromean rings don't exist](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_15)
  16. :x: [Touching simplices](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_16)
  17. :x: [Every large point set has an obtuse angle](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_17)
  18. :x: [Borsuk's conjecture](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_18)
### Analysis
  19. :x: [Sets, functions, and the continuum hypothesis](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_19)
  20. :thought_balloon: [In praise of inequalities](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_20)
  21. :thought_balloon: [The fundamental theorem of algebra](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_21)
  22. :x: [One square and an odd number of triangles](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_22)
  23. :x: [A theorem of Pólya on polynomials](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_23)
  24. :x: [Van der Waerden's permanent conjecture](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_24)
  25. :x: [On a lemma of Littlewook and Offord](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_25)
  26. :x: [Cotangent and the Herglotz trick](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_26)
  27. :x: [Buffon's needle problem](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_27)
### Combinatorics
  28. :x: [Pigeon-hole and double counting](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_28)
  29. :x: [Tiling rectangles](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_29)
  30. :x: [Three famous theorems on finite sets](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_30)
  31. :x: [Shuffling cards](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_31)
  32. :thought_balloon: [Lattice paths and determinants](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_32)
  33. :x: [Cayley's formula for the number of trees](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_33)
  34. :x: [Identities versus bijections](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_34)
  35. :x: [The finite Kakeya problem](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_35)
  36. :x: [Completing Latin squares](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_36)
### Graph Theory
  37. :x: [Permanents and the power of entropy](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_37)
  38. :x: [The Dinitz problem](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_38)
  39. :x: [Five-coloring plane graphs](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_39)
  40. :x: [How to guard a museum](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_40)
  41. :x: [Turán's graph theorem](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_41)
  42. :x: [Communicating without errors](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_42)
  43. :x: [The chromatic number of Kneser graphs](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_43)
  44. :speech_balloon: [Of friends and politicians](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_44)
  45. :thought_balloon: [Probability makes counting (sometimes) easy](https://github.com/mo271/formal_book/blob/main/FormalBook/Chapter_45)

## Contributing

Contributions are most welcome! Feel free to
  - grab a chapter that is not yet formalized and formalize
    - definitions, (if not yet in mathlib)
    - statements and
    - proofs
  - fill in [`sorry`s](https://github.com/search?q=repo%3Amo271%2Fformal_book+sorry+path%3A*.lean&type=code)
  - suggest improvements to proofs/code golf
  - correct typos/formatting/linting

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for details.

## Authors

  - [Moritz Firsching](https://github.com/mo271)
  - [Nick Kuhn](https://github.com/nick-kuhn)
  - [Christopher Schmidt](https://github.com/C-h-r-i-s-x)

## License

Apache 2.0; see [`LICENSE`](LICENSE) for details.

## Disclaimer

This project is not an official Google project. It is not supported by
Google and Google specifically disclaims all warranties as to its quality,
merchantability, or fitness for a particular purpose.
