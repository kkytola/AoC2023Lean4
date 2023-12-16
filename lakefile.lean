import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

package «AoC2023Lean4» where
  -- add package configuration options here

lean_lib «AoC2023Lean4» where
  -- add library configuration options here

@[default_target]
lean_exe «aoc2023lean4» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
