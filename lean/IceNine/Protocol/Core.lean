/-
# Protocol Core

Core algebraic definitions for the lattice-style threshold Schnorr/Dilithium
protocol: scheme record, DKG and signing types, and verification.
-/

import Mathlib
import IceNine.Crypto

namespace IceNine.Protocol

open List

universe u

structure Scheme where
  PartyId   : Type u
  Message   : Type u
  Secret    : Type u
  Public    : Type u
  Challenge : Type u
  Scalar    : Type u

  [scalarSemiring : Semiring Scalar]
  [secretAdd    : AddCommGroup Secret]
  [publicAdd    : AddCommGroup Public]

  [secretModule : Module Scalar Secret]
  [publicModule : Module Scalar Public]

  [challengeSMulSecret : SMul Challenge Secret]
  [challengeSMulPublic : SMul Challenge Public]

  -- Linear map A : Secret →ₗ Scalar Public
  A : Secret →ₗ[Scalar] Public

  Commitment : Type u
  Opening    : Type u
  commit     : Public → Opening → Commitment

  -- Binding property of commitments (abstract).
  commitBinding :
    ∀ {x₁ x₂ : Public} {o₁ o₂ : Opening},
      commit x₁ o₁ = commit x₂ o₂ → x₁ = x₂

  -- Hash assumptions (abstract, to be provided per instance).
  hashCollisionResistant : Prop

  hash :
    Message →
    Public →                    -- global public key
    List PartyId →              -- participant set S
    List Commitment →           -- commitments Com_i
    Public →                    -- aggregated w
    Challenge

  normOK : Secret → Prop

attribute [instance] Scheme.scalarSemiring Scheme.secretAdd Scheme.publicAdd
attribute [instance] Scheme.secretModule Scheme.publicModule
attribute [instance] Scheme.challengeSMulSecret Scheme.challengeSMulPublic

/-- State of a party after DKG. -/
structure KeyShare (S : Scheme) :=
  (pid  : S.PartyId)
  (sk_i : S.Secret)
  (pk_i : S.Public)
  (pk   : S.Public)
deriving Repr

/-- DKG round-1 message: commitment to pk_i. -/
structure DkgCommitMsg (S : Scheme) :=
  (from    : S.PartyId)
  (commitPk : S.Commitment)
deriving Repr

/-- DKG round-2 message: reveal pk_i and opening. -/
structure DkgRevealMsg (S : Scheme) :=
  (from    : S.PartyId)
  (pk_i    : S.Public)
  (opening : S.Opening)
deriving Repr

/-- Local state for DKG after round 1. -/
structure DkgLocalState (S : Scheme) :=
  (pid    : S.PartyId)
  (sk_i   : S.Secret)
  (pk_i   : S.Public)
  (openPk : S.Opening)
deriving Repr

end IceNine.Protocol
