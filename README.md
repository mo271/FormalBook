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
  1. :speech_balloon: [Six proofs of the infinity of primes](./FormalBook/Ch01_Six_proofs_of_the_infinity_of_primes.lean)
  2. :speech_balloon: [Bertrand's postulate](./FormalBook/Ch02_Bertrand's_postulate.lean)
  3. :speech_balloon: [Binomial coefficients are (almost) never powers](./FormalBook/Ch03_Binomial_coefficients_are_(almost)_never_powers.lean)
  4. :x: [Representing numbers as sums of two squares](./FormalBook/Ch04_Representing_numbers_as_sums_of_two_squares.lean)
  5. :thought_balloon: [The law of quadratic reciprocity](./FormalBook/Ch05_The_law_of_quadratic_reciprocity.lean)
  6. :thought_balloon: [Every finite division ring is a field](./FormalBook/Ch06_Every_finite_division_ring_is_a_field.lean)
  7. :thought_balloon: [The spectral theorem and Hadamard's determinant problem](./FormalBook/Ch07_The_spectral_theorem_and_Hadamard's_determinant_problem.lean)
  8. :thought_balloon: [Some irrational numbers](./FormalBook/Ch08_Some_irrational_numbers.lean)
  9. :x: [Four times ](./FormalBook/Ch09_Four_times_pi²_over_6.lean)$\pi^2/6$

### Geometry
  10. :x: [Hilbert's third problem: decomposing polyhedra](./FormalBook/Ch10_Hilbert's_third_problem_decomposing_polyhedra.lean)
  11. :x: [Lines in the plane and decompositions of graphs](./FormalBook/Ch11_Lines_in_the_plane_and_decompositions_of_graphs.lean)
  12. :x: [The slope problem](./FormalBook/Ch12_The_slope_problem.lean)
  13. :x: [Three applications of Euler's formula](./FormalBook/Ch13_Three_applications_of_Euler's_formula.lean)
  14. :x: [Cauchy's rigidity theorem](./FormalBook/Ch14_Cauchy's_rigidity_theorem.lean)
  15. :x: [The Borromean rings don't exist](./FormalBook/Ch15_The_Borromean_rings_don't_exist.lean)
  16. :x: [Touching simplices](./FormalBook/Ch16_Touching_simplices.lean)
  17. :x: [Every large point set has an obtuse angle](./FormalBook/Ch17_Every_large_point_set_has_an_obtuse_angle.lean)
  18. :x: [Borsuk's conjecture](./FormalBook/Ch18_Borsuk's_conjecture.lean)
### Analysis
  19. :x: [Sets, functions, and the continuum hypothesis](./FormalBook/Ch19_Sets,_functions,_and_the_continuum_hypothesis.lean)
  20. :thought_balloon: [In praise of inequalities](./FormalBook/Ch20_In_praise_of_inequalities.lean)
  21. :thought_balloon: [The fundamental theorem of algebra](./FormalBook/Ch21_The_fundamental_theorem_of_algebra.lean)
  22. :x: [One square and an odd number of triangles](./FormalBook/Ch22_One_square_and_an_odd_number_of_triangles.lean)
  23. :x: [A theorem of Pólya on polynomials](./FormalBook/Ch23_A_theorem_of_Pólya_on_polynomials.lean)
  24. :x: [Van der Waerden's permanent conjecture](./FormalBook/Ch24_Van_der_Waerden's_permanent_conjecture.lean)
  25. :x: [On a lemma of Littlewook and Offord](./FormalBook/Ch25_On_a_lemma_of_Littlewook_and_Offord.lean)
  26. :x: [Cotangent and the Herglotz trick](./FormalBook/Ch26_Cotangent_and_the_Herglotz_trick.lean)
  27. :x: [Buffon's needle problem](./FormalBook/Ch27_Buffon's_needle_problem.lean)
### Combinatorics
  28. :x: [Pigeon-hole and double counting](./FormalBook/Ch28_Pigeon-hole_and_double_counting.lean)
  29. :x: [Tiling rectangles](./FormalBook/Ch29_Tiling_rectangles.lean)
  30. :x: [Three famous theorems on finite sets](./FormalBook/Ch30_Three_famous_theorems_on_finite_sets.lean)
  31. :x: [Shuffling cards](./FormalBook/Ch31_Shuffling_cards.lean)
  32. :thought_balloon: [Lattice paths and determinants](./FormalBook/Ch32_Lattice_paths_and_determinants.lean)
  33. :x: [Cayley's formula for the number of trees](./FormalBook/Ch33_Cayley's_formula_for_the_number_of_trees.lean)
  34. :x: [Identities versus bijections](./FormalBook/Ch34_Identities_versus_bijections.lean)
  35. :x: [The finite Kakeya problem](./FormalBook/Ch35_The_finite_Kakeya_problem.lean)
  36. :x: [Completing Latin squares](./FormalBook/Ch36_Completing_Latin_squares.lean)
### Graph Theory
  37. :x: [Permanents and the power of entropy](./FormalBook/Ch37_Permanents_and_the_power_of_entropy.lean)
  38. :x: [The Dinitz problem](./FormalBook/Ch38_The_Dinitz_problem.lean)
  39. :x: [Five-coloring plane graphs](./FormalBook/Ch39_Five-coloring_plane_graphs.lean)
  40. :x: [How to guard a museum](./FormalBook/Ch40_How_to_guard_a_museum.lean)
  41. :x: [Turán's graph theorem](./FormalBook/Ch41_Turán's_graph_theorem.lean)
  42. :x: [Communicating without errors](./FormalBook/Ch42_Communicating_without_errors.lean)
  43. :x: [The chromatic number of Kneser graphs](./FormalBook/Ch43_The_chromatic_number_of_Kneser_graphs.lean)
  44. :speech_balloon: [Of friends and politicians](./FormalBook/Ch44_Of_friends_and_politicians.lean)
  45. :thought_balloon: [Probability makes counting (sometimes) easy](./FormalBook/Ch45_Probability_makes_counting_(sometimes)_easy.lean)

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
