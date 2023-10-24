import Lake
open Lake DSL

package leanBackend {
  -- add package configuration options here
}

lean_lib LeanBackend {
  -- add library configuration options here
}

@[default_target]
lean_exe leanBackend {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
