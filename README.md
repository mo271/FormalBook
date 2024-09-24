# Formal BOOK

A collaborative, work-in-progress attempt to formalize [Proofs from THE BOOK](https://link.springer.com/book/10.1007/978-3-662-57265-8) using [Lean4](https://leanprover.github.io/lean4/doc/whatIsLean.html).


![Formal Proofs from THE BOOK](formal_proofs_form_the_book.svg)

## Structure

For each chapter in the book (we follow the latest, sixth edition), there is a lean source file containing as many formalized definitions, lemmas, theorems and proofs as we can reasonably currently formalize using [Lean's mathlib4](https://github.com/leanprover-community/mathlib4).

The goal is to make the formalizations of the proofs as close as possible to the proofs in the book, even if a different proof for a theorem might already be present in mathlib or is more suitable for formalization.

We follow the [naming conventions](https://github.com/leanprover-community/mathlib4/wiki/Porting-wiki#naming-convention) and [code style](https://leanprover-community.github.io/contribute/style.html) of mathlib4.

## Blueprint

Checkout the [project's blueprint](https://firsching.ch/FormalBook)!

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
  1. :speech_balloon: [Six proofs of the infinity of primes](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_01.lean)
  2. :speech_balloon: [Bertrand's postulate](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_02.lean)
  3. :speech_balloon: [Binomial coefficients are (almost) never powers](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_03.lean)
  4. :x: [Representing numbers as sums of two squares](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_04.lean)
  5. :thought_balloon: [The law of quadratic reciprocity](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_05.lean)
  6. :thought_balloon: [Every finite division ring is a field](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_06.lean)
  7. :thought_balloon: [The spectral theorem and Hadamard's determinant problem](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_07.lean)
  8. :thought_balloon: [Some irrational numbers](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_08.lean)
  9. :x: [Four times ](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_09.lean)

### Geometry
  10. :x: [Hilbert's third problem: decomposing polyhedra](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_10.lean)
  11. :x: [Lines in the plane and decompositions of graphs](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_11.lean)
  12. :x: [The slope problem](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_12.lean)
  13. :x: [Three applications of Euler's formula](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_13.lean)
  14. :x: [Cauchy's rigidity theorem](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_14.lean)
  15. :x: [The Borromean rings don't exist](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_15.lean)
  16. :x: [Touching simplices](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_16.lean)
  17. :x: [Every large point set has an obtuse angle](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_17.lean)
  18. :x: [Borsuk's conjecture](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_18.lean)
### Analysis
  19. :x: [Sets, functions, and the continuum hypothesis](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_19.lean)
  20. :thought_balloon: [In praise of inequalities](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_20.lean)
  21. :thought_balloon: [The fundamental theorem of algebra](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_21.lean)
  22. :x: [One square and an odd number of triangles](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_22.lean)
  23. :x: [A theorem of Pólya on polynomials](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_23.lean)
  24. :x: [Van der Waerden's permanent conjecture](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_24.lean)
  25. :x: [On a lemma of Littlewook and Offord](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_25.lean)
  26. :x: [Cotangent and the Herglotz trick](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_26.lean)
  27. :x: [Buffon's needle problem](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_27.lean)
### Combinatorics
  28. :x: [Pigeon-hole and double counting](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_28.lean)
  29. :x: [Tiling rectangles](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_29.lean)
  30. :x: [Three famous theorems on finite sets](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_30.lean)
  31. :x: [Shuffling cards](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_31.lean)
  32. :thought_balloon: [Lattice paths and determinants](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_32.lean)
  33. :x: [Cayley's formula for the number of trees](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_33.lean)
  34. :x: [Identities versus bijections](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_34.lean)
  35. :x: [The finite Kakeya problem](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_35.lean)
  36. :x: [Completing Latin squares](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_36.lean)
### Graph Theory
  37. :x: [Permanents and the power of entropy](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_37.lean)
  38. :x: [The Dinitz problem](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_38.lean)
  39. :x: [Five-coloring plane graphs](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_39.lean)
  40. :x: [How to guard a museum](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_40.lean)
  41. :x: [Turán's graph theorem](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_41.lean)
  42. :x: [Communicating without errors](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_42.lean)
  43. :x: [The chromatic number of Kneser graphs](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_43.lean)
  44. :speech_balloon: [Of friends and politicians](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_44.lean)
  45. :thought_balloon: [Probability makes counting (sometimes) easy](https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_45.lean)

## Contributing

Contributions are most welcome! Feel free to
  - grab a chapter that is not yet formalized and formalize
    - definitions, (if not yet in mathlib)
    - statements and
    - proofs
  - fill in [`sorry`s](https://github.com/search?q=repo%3Amo271%2FFormalBook+sorry+path%3A*.lean&type=code) in lean files
  - fill in ['TODO's](https://github.com/search?q=repo%3Amo271%2FFormalBook+TODO+path%3A*.tex&type=code) in LaTeX files in the [blueprint](https://firsching.ch/FormalBook)
  - suggest improvements to proofs/code golf
  - correct typos/formatting/linting

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for details.

## Authors

A list of contributors can be found here: [AUTHORS](AUTHORS.md)
or look at the [github stats](https://github.com/mo271/FormalBook/graphs/contributors).

## License

Apache 2.0; see [`LICENSE`](LICENSE) for details.

## Disclaimer

This project is not an official Google project. It is not supported by
Google and Google specifically disclaims all warranties as to its quality,
merchantability, or fitness for a particular purpose.
