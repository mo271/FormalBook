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

## Contributing

Contributions are most welcome! Feel free to
  - grab a chapter that is not yet formalized and formalize
    - definitions, (if not yet in mathlib)
    - statements and
    - proofs
  - partial proofs with new `sorry` are also great!
  - fill in [`sorry`s](https://github.com/search?q=repo%3Amo271%2FFormalBook+sorry+path%3A*.lean&type=code) in lean files
  - fill in ['TODO's](https://github.com/search?q=repo%3Amo271%2FFormalBook+TODO+path%3A*.tex&type=code) in LaTeX files in the [blueprint](https://firsching.ch/FormalBook)
  - suggest improvements to proofs/code golf
  - correct typos/formatting/linting

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for details.

## Authors

A list of contributors can be found here: [AUTHORS](AUTHORS.md)
or look at the [github stats](https://github.com/mo271/FormalBook/graphs/contributors).


Some contributions come the repo
[FordUniver/thebook.lean](https://github.com/FordUniver/thebook.lean),
which also has a nice [blog](https://thebook.zib.de/) on the proofs formalized there.


## License

Apache 2.0; see [`LICENSE`](LICENSE) for details.

## Disclaimer

This project is not an official Google project. It is not supported by
Google and Google specifically disclaims all warranties as to its quality,
merchantability, or fitness for a particular purpose.
