import Lake
open Lake DSL

package SumSq where
  -- add package configuration options here
leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require mdgen from git
  "https://github.com/Seasawher/mdgen" @ "main"

lean_lib SumSq where
  -- add library configuration options here

lean_lib MathlibVersions where
  -- add library configuration options here

@[default_target]
lean_exe «example» where
  root := `Example
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
