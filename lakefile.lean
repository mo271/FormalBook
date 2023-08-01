import Lake
open Lake DSL

package formal_book {
  -- add any package configuration options here
}


@[default_target]
lean_lib «FormalBook» {
  -- add any library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "6c5ad83c2ca4a6e03ae9e33fa52220712b8a9faf"
