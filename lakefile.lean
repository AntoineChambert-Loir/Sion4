import Lake
open Lake DSL

package Sion {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib Sion {
  -- add library configuration options here
}
