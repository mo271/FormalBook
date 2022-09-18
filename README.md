# Formal BOOK

A collaborative, work-in-progress attempt to formalize [Proofs from THE BOOK](https://link.springer.com/book/10.1007/978-3-662-57265-8) using [Lean](https://leanprover-community.github.io/).


![Formal Proofs from THE BOOK](formal_proofs_form_the_book.svg)

## Structure

For each chapter in the book (we follow the latest, sixth edition), there is a lean source file containing as many formalized definitions, lemmas, theorems and proofs as we can reasonably currently formalize using [Lean's mathlib](https://github.com/leanprover-community/mathlib).

The goal is to make the formalizations of the proofs as close as possible to the proofs in the book, even if a different proof for a theorem might already be present in mathlib or is more suitable for formalization.

We follow the [naming conventions](https://leanprover-community.github.io/contribute/naming.html) and [code style](https://leanprover-community.github.io/contribute/style.html) of mathlib.

## Installation

This is a leanproject currently using Lean 3. You first need to [install Lean](https://leanprover-community.github.io/get_started.html#regular-install) and then run
```shell
leanproject get mo271/formal_book
cd formal_book
code .
```
The last step only opens vscode in case you want to use that.

## Chapters

Status of the chapters:

  - :x: chapter is just a stub
  - :thought_balloon: work in progress
  - :tada: chapter is completely formalized

### Number Theory
  1. :thought_balloon: [Six proofs of the infinity of primes](./src/chapters/01_Six_proofs_of_the_infinity_of_primes.lean)
  2. :thought_balloon: [Bertrand's postulate](./src/chapters/02_Bertrand's_postulate.lean)
  3. :thought_balloon: [Binomial coefficients are (almost) never powers](./src/chapters/03_Binomial_coefficients_are_(almost)_never_powers.lean)
  4. :x: [Representing numbers as sums of two squares](./src/chapters/04_Representing_numbers_as_sums_of_two_squares.lean)
  5. :thought_balloon: [The law of quadratic reciprocity](./src/chapters/05_The_law_of_quadratic_reciprocity.lean)
  6. :x: [Every finite division ring is a field](./src/chapters/06_Every_finite_division_ring_is_a_field.lean)
  7. :x: [The spectral theorem and Hadamard's determinant problem](./src/chapters/07_The_spectral_theorem_and_Hadamard's_determinant_problem.lean)
  8. :x: [Some irrational numbers](./src/chapters/08_Some_irrational_numbers.lean)
  9. :x: [Four times ](./src/chapters/09_Four_times_pi²_over_6.lean)$\pi^2/6$

### Geometry
  10. :x: [Hilbert's third problem: decomposing polyhedra](./src/chapters/10_Hilbert's_third_problem_decomposing_polyhedra.lean)
  11. :x: [Lines in the plane and decompositions of graphs](./src/chapters/11_Lines_in_the_plane_and_decompositions_of_graphs.lean)
  12. :x: [The slope problem](./src/chapters/12_The_slope_problem.lean)
  13. :x: [Three applications of Euler's formula](./src/chapters/13_Three_applications_of_Euler's_formula.lean)
  14. :x: [Cauchy's rigidity theorem](./src/chapters/14_Cauchy's_rigidity_theorem.lean)
  15. :x: [The Borromean rings don't exist](./src/chapters/15_The_Borromean_rings_don't_exist.lean)
  16. :x: [Touching simplices](./src/chapters/16_Touching_simplices.lean)
  17. :x: [Every large point set has an obtuse angle](./src/chapters/17_Every_large_point_set_has_an_obtuse_angle.lean)
  18. :x: [Borsuk's conjecture](./src/chapters/18_Borsuk's_conjecture.lean)
### Analysis
  19. :x: [Sets, functions, and the continuum hypothesis](./src/chapters/19_Sets,_functions,_and_the_continuum_hypothesis.lean)
  20. :thought_balloon: [In praise of inequalities](./src/chapters/20_In_praise_of_inequalities.lean)
  21. :thought_balloon: [The fundamental theorem of algebra](./src/chapters/21_The_fundamental_theorem_of_algebra.lean)
  22. :x: [One square and an odd number of triangles](./src/chapters/22_One_square_and_an_odd_number_of_triangles.lean)
  23. :x: [A theorem of Pólya on polynomials](./src/chapters/23_A_theorem_of_Pólya_on_polynomials.lean)
  24. :x: [Van der Waerden's permanent conjecture](./src/chapters/24_Van_der_Waerden's_permanent_conjecture.lean)
  25. :x: [On a lemma of Littlewook and Offord](./src/chapters/25_On_a_lemma_of_Littlewook_and_Offord.lean)
  26. :x: [Cotangent and the Herglotz trick](./src/chapters/26_Cotangent_and_the_Herglotz_trick.lean)
  27. :x: [Buffon's needle problem](./src/chapters/27_Buffon's_needle_problem.lean)
### Combinatorics
  28. :x: [Pigeon-hole and double counting](./src/chapters/28_Pigeon-hole_and_double_counting.lean)
  29. :x: [Tiling rectangles](./src/chapters/29_Tiling_rectangles.lean)
  30. :x: [Three famous theorems on finite sets](./src/chapters/30_Three_famous_theorems_on_finite_sets.lean)
  31. :x: [Shuffling cards](./src/chapters/31_Shuffling_cards.lean)
  32. :x: [Lattice paths and determinants](./src/chapters/32_Lattice_paths_and_determinants.lean)
  33. :x: [Cayley's formula for the number of trees](./src/chapters/33_Cayley's_formula_for_the_number_of_trees.lean)
  34. :x: [Identities versus bijections](./src/chapters/34_Identities_versus_bijections.lean)
  35. :x: [The finite Kakeya problem](./src/chapters/35_The_finite_Kakeya_problem.lean)
  36. :x: [Completing Latin squares](./src/chapters/36_Completing_Latin_squares.lean)
### Graph Theory
  37. :x: [Permanents and the power of entropy](./src/chapters/37_Permanents_and_the_power_of_entropy.lean)
  38. :x: [The Dinitz problem](./src/chapters/38_The_Dinitz_problem.lean)
  39. :x: [Five-coloring plane graphs](./src/chapters/39_Five-coloring_plane_graphs.lean)
  40. :x: [How to guard a museum](./src/chapters/40_How_to_guard_a_museum.lean)
  41. :x: [Turán's graph theorem](./src/chapters/41_Turán's_graph_theorem.lean)
  42. :x: [Communicating without errors](./src/chapters/42_Communicating_without_errors.lean)
  43. :x: [The chromatic number of Kneser graphs](./src/chapters/43_The_chromatic_number_of_Kneser_graphs.lean)
  44. :thought_balloon: [Of friends and politicians](./src/chapters/44_Of_friends_and_politicians.lean)
  45. :x: [Probability makes counting (sometimes) easy](./src/chapters/45_Probability_makes_counting_(sometimes)_easy.lean)

## Contributing

Contributions are most welcome! Feel free to
  - grab a chapter that is not yet formalized and formalize
    - definitions, (if not yet in mathlib)
    - statements and
    - proofs
  - fill in [`sorry`s](https://github.com/mo271/formal_book/search?q=sorry+extension%3Alean)
  - suggest improvements to proofs/code golf
  - correct typos/formatting/linting

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for details.

## License

Apache 2.0; see [`LICENSE`](LICENSE) for details.

## Disclaimer

This project is not an official Google project. It is not supported by
Google and Google specifically disclaims all warranties as to its quality,
merchantability, or fitness for a particular purpose.
