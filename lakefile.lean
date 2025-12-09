import Lake
open Lake DSL

package «ice-nine» where
  version := v!"0.1.0"
  keywords := #["cryptography", "formal-verification", "protocols"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «IceNine» where
  srcDir := "lean"
  roots := #[`IceNine]

lean_lib «IceNine.Crypto» where
  srcDir := "lean"
  roots := #[`IceNine.Crypto]

lean_lib «IceNine.Protocol» where
  srcDir := "lean"
  roots := #[`IceNine.Protocol]

lean_lib «IceNine.Security» where
  srcDir := "lean"
  roots := #[`IceNine.Security]
