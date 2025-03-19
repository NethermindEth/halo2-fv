import Lake
open Lake DSL

package «examples» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`debug.skipKernelTC, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  moreServerOptions := #[
    ⟨`debug.skipKernelTC, true⟩
  ]

  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require LeanCrypto from git
  "https://github.com/NethermindEth/LeanCrypto.git"

@[default_target]
lean_lib «Examples» where
  -- add any library configuration options here
