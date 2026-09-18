import Lake
open Lake DSL

package «Googology» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

require repl from git
  "https://github.com/leanprover-community/repl" @ "v4.33.0"

@[default_target]
lean_lib «Googology» where
  -- add any library configuration options here
