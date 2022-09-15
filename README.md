# Formal BOOK

A work-in-progress attempt to formalize [Proofs from the BOOK](https://link.springer.com/book/10.1007/978-3-662-57265-8) using [Lean](https://leanprover-community.github.io/).


![Formal Proofs from THE BOOK](formal_proofs_form_the_book.svg)

## Structure

For each chapter in the book (we follow the latest, sixth edition), there is a lean source file containing as many formalized definitions, lemmas, theorems and proofs as we can reasonably currently formalize using [Lean's mathlib](https://github.com/leanprover-community/mathlib).

The goal is to make the formalizations of the proofs as close as possible to the proofs in the book, even if a different proof for a theorem might already be present in mathlib or is more suitable for formalization.

We follow the [naming conventions](https://leanprover-community.github.io/contribute/naming.html) and [code style](https://leanprover-community.github.io/contribute/style.html) of mathlib.

## Chapters

Status of the chapters:
  - :x: not yet started
  - :white_check_mark: work in progress
  - :heavy_check_mark: chapter is completely formalized

  1.  :white_check_mark: [Six proofs of the infinity of primes](./src/chapters/01_Six_proofs_of_the_infinity_of_primes.lean)
  2. :x: [Bertrand's_postulate](./src/chapters/02_Bertrand's_postulate.lean)
  3. :x: [Binomial_coefficients_are_(almost)_never_powers](./src/chapters/03_Binomial_coefficients_are_(almost)_never_powers.lean)
  4. :x: [Representing_numbers_as_sums_of_two_squares](./src/chapters/04_Representing_numbers_as_sums_of_two_squares.lean)
  5. :x: [The_law_of_quadratic_reciprocity](./src/chapters/05_The_law_of_quadratic_reciprocity.lean)
  6. :x: [Every_finite_division_ring_is_a_field](./src/chapters/06_Every_finite_division_ring_is_a_field.lean)
  7. :x: [The_spectral_theorem_and_Hadamard's_determinant_problem](./src/chapters/07_The_spectral_theorem_and_Hadamard's_determinant_problem.lean)
  8. :x: [Some_irrational_numbers](./src/chapters/08_Some_irrational_numbers.lean)
  9. :x: [Four_times_$π^2/6$](./src/chapters/09_Four_times_pi²_over_6.lean)
  10. :x: [Hilbert's_third_problem:_decomposing_polyhedra](./src/chapters/10_Hilbert's_third_problem:_decomposing_polyhedra.lean)
  11. :x: [Lines_in_the_plane_and_decompositions_of_graphs](./src/chapters/11_Lines_in_the_plane_and_decompositions_of_graphs.lean)
  12. :x: [The_slope_problem](./src/chapters/12_The_slope_problem.lean)
  13. :x: [Three_applications_of_Euler's_formula](./src/chapters/13_Three_applications_of_Euler's_formula.lean)
  14. :x: [Cauchy's_rigidity_theorem](./src/chapters/14_Cauchy's_rigidity_theorem.lean)
  15. :x: [The_Borromean_rings_don't_exist](./src/chapters/15_The_Borromean_rings_don't_exist.lean)
  16. :x: [Touching_simplices](./src/chapters/16_Touching_simplices.lean)
  17. :x: [Every_large_point_set_has_an_obtuse_angle](./src/chapters/17_Every_large_point_set_has_an_obtuse_angle.lean)
  18. :x: [Borsuk's_conjecture](./src/chapters/18_Borsuk's_conjecture.lean)
  19. :x: [Sets,_functions,_and_the_continuum_hypothesis](./src/chapters/19_Sets,_functions,_and_the_continuum_hypothesis.lean)
  20. :x: [In_praise_of_inequalities](./src/chapters/20_In_praise_of_inequalities.lean)
  21. :x: [The_fundamental_theorem_of_algebra](./src/chapters/21_The_fundamental_theorem_of_algebra.lean)
  22. :x: [One_square_and_an_odd_number_of_triangles](./src/chapters/22_One_square_and_an_odd_number_of_triangles.lean)
  23. :x: [A_theorem_of_Pólya_on_polynomials](./src/chapters/23_A_theorem_of_Pólya_on_polynomials.lean)
  24. :x: [Van_der_Waerden's_permanent_conjecture](./src/chapters/24_Van_der_Waerden's_permanent_conjecture.lean)
  25. :x: [On_a_lemma_of_Littlewook_and_Offord](./src/chapters/25_On_a_lemma_of_Littlewook_and_Offord.lean)
  26. :x: [Cotangent_and_the_Herglotz_trick](./src/chapters/26_Cotangent_and_the_Herglotz_trick.lean)
  27. :x: [Buffon's_needle_problem](./src/chapters/27_Buffon's_needle_problem.lean)
  28. :x: [Pigeon-hole_and_double_counting](./src/chapters/28_Pigeon-hole_and_double_counting.lean)
  29. :x: [Tiling_rectangles](./src/chapters/29_Tiling_rectangles.lean)
  30. :x: [Three_famous_theorems_on_finite_sets](./src/chapters/30_Three_famous_theorems_on_finite_sets.lean)
  31. :x: [Shuffling_cards](./src/chapters/31_Shuffling_cards.lean)
  32. :x: [Lattice_paths_and_determinants](./src/chapters/32_Lattice_paths_and_determinants.lean)
  33. :x: [Cayley's_formula_for_the_number_of_trees](./src/chapters/33_Cayley's_formula_for_the_number_of_trees.lean)
  34. :x: [Identities_versus_bijections](./src/chapters/34_Identities_versus_bijections.lean)
  35. :x: [The_finite_Kakeya_problem](./src/chapters/35_The_finite_Kakeya_problem.lean)
  36. :x: [Completing_Latin_squares](./src/chapters/36_Completing_Latin_squares.lean)
  37. :x: [Permanents_and_the_power_of_entropy](./src/chapters/37_Permanents_and_the_power_of_entropy.lean)
  38. :x: [The_Dinitz_problem](./src/chapters/38_The_Dinitz_problem.lean)
  39. :x: [Five-coloring_plane_graphs](./src/chapters/39_Five-coloring_plane_graphs.lean)
  40. :x: [How_to_guard_a_museum](./src/chapters/40_How_to_guard_a_museum.lean)
  41. :x: [Turán's_graph_theorem](./src/chapters/41_Turán's_graph_theorem.lean)
  42. :x: [Communicating_without_errors](./src/chapters/42_Communicating_without_errors.lean)
  43. :x: [The_chromatic_number_of_Kneser_graphs](./src/chapters/43_The_chromatic_number_of_Kneser_graphs.lean)
  44. :x: [Of_friends_and_politicians](./src/chapters/44_Of_friends_and_politicians.lean)
  45. :x: [Probability_makes_counting_(sometimes)_easy](./src/chapters/45_Probability_makes_counting_(sometimes)_easy.lean)

## Contributing

Contributions are most welcome! Feel free to
  - grab a chapter that is not yet formalized and formalize
    - definitions, (if not yet in mathlib)
    - statements and
    - proofs
  - fill in `sorry`s
  - suggest improvements to proofs/code golf
  - correct typos/formatting/linting

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for details.

## License

Apache 2.0; see [`LICENSE`](LICENSE) for details.

## Disclaimer

This project is not an official Google project. It is not supported by
Google and Google specifically disclaims all warranties as to its quality,
merchantability, or fitness for a particular purpose.
