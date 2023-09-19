import Lake
open Lake DSL

package «mv-divide» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.0.0"



@[default_target]
lean_lib «MvDivide» {
  -- add any library configuration options here
}
