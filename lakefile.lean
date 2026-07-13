import Lake
open Lake DSL

package «central-binomial-lean» where
  -- Tracks the deterministic proof in `../erdos728.pdf`.

@[default_target]
lean_lib CentralBinomialLean

/-
Mathlib dependency.

Default (portable, reproducible): the pinned release matching `lean-toolchain`
(`v4.30.0`). Run `lake exe cache get` to download prebuilt `.olean`s instead of
compiling Mathlib from source.

Local override: to reuse an already-built Mathlib and skip the download, point
Lake at an existing checkout, e.g.

    lake build -K mathlibDir=/path/to/.lake/packages/mathlib

This is how the development machine builds against its shared Mathlib; it keeps
no machine-specific path in the committed configuration.
-/
@[package_dep]
def mathlib : Dependency :=
  if let some dir := get_config? mathlibDir then
    { name := `mathlib, scope := "", version? := none,
      src? := some (.path dir), opts := {} }
  else
    { name := `mathlib, scope := "", version? := some "git#v4.30.0",
      src? := some (.git "https://github.com/leanprover-community/mathlib4.git"
        (some "v4.30.0") none), opts := {} }
