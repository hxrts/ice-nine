/-
# Protocol Core

Core algebraic definitions for the Ice Nine threshold signature protocol.
Defines the abstract Scheme record and basic message types for DKG.
-/

import Mathlib
import IceNine.Crypto

namespace IceNine.Protocol

open List

universe u

/-!
## Scheme Record

The Scheme bundles all algebraic and cryptographic parameters:
- Secret/Public modules connected by linear map A
- Commitment scheme for hiding values until reveal
- Hash function for Fiat-Shamir challenges
- Norm predicate for lattice signature security
-/
structure Scheme where
  -- Party identifiers (e.g., Nat or a finite type)
  PartyId   : Type u
  -- Messages to be signed (e.g., ByteArray)
  Message   : Type u
  -- Secret key space (e.g., short lattice vectors)
  Secret    : Type u
  -- Public key space (e.g., lattice points)
  Public    : Type u
  -- Challenge space from hash (e.g., small polynomials)
  Challenge : Type u
  -- Scalar ring for module operations
  Scalar    : Type u

  -- Algebraic structure: scalars form a semiring
  [scalarSemiring : Semiring Scalar]
  -- Secrets form an additive group (for share combination)
  [secretAdd    : AddCommGroup Secret]
  -- Public values form an additive group (for key aggregation)
  [publicAdd    : AddCommGroup Public]

  -- Module structures enable scalar multiplication
  [secretModule : Module Scalar Secret]
  [publicModule : Module Scalar Public]

  -- Challenges can scale secrets/publics (for z = y + c·s)
  [challengeSMulSecret : SMul Challenge Secret]
  [challengeSMulPublic : SMul Challenge Public]

  -- The one-way linear map: pk = A(sk). Security relies on
  -- hardness of inverting A (SIS/LWE in lattice setting).
  A : Secret →ₗ[Scalar] Public

  /-
  ## Commitment Scheme

  We abstract the commitment scheme via `commit` and `commitBinding`. This models
  a computationally binding, perfectly hiding commitment scheme.

  ### Security Properties

  A commitment scheme has two security properties:

  1. **Binding**: Once committed, the committer cannot open to a different value.
     Formalized as: commit(x₁, o₁) = commit(x₂, o₂) → x₁ = x₂
     We include this as `commitBinding` in the Scheme structure.

  2. **Hiding**: The commitment reveals nothing about the committed value.
     Formalized as: ∀ x₁ x₂, {commit(x₁, o) : o ← random} ≈ {commit(x₂, o) : o ← random}
     (distributions are computationally/statistically indistinguishable)

  **IMPORTANT**: We only formalize binding, not hiding. Hiding is assumed but not
  enforced in the type system. The demo instances in `Instances.lean` do NOT
  satisfy hiding (they store the value in plaintext). This is acceptable because:
  - Protocol correctness proofs only need binding
  - Hiding is needed for security proofs (simulation-based arguments)
  - Formal hiding would require probabilistic reasoning infrastructure

  ### Concrete Instantiations

  | Scheme | Hiding | Binding | Assumption |
  |--------|--------|---------|------------|
  | Pedersen | Perfect | Computational | DLog hardness |
  | Hash-based H(x‖r) | Computational | Computational | ROM |
  | ElGamal-style | Perfect | Computational | DDH |

  **Design Choice**: We axiomatize binding rather than instantiating a concrete
  scheme (e.g., Pedersen, hash-based) because:
  1. The protocol correctness is independent of commitment instantiation
  2. Different deployment contexts may require different schemes
  3. Formal verification of concrete schemes would require additional crypto assumptions

  **Reference**: Halevi & Micali, "Practical and Provably-Secure Commitment Schemes
  from Collision-Free Hashing", CRYPTO 1996. Shows binding ↔ collision resistance.

  In practice, use Pedersen commitments (perfectly hiding, computationally binding
  under DLog) or hash-based commitments (computationally hiding/binding under ROM).
  -/

  -- Commitment scheme types
  Commitment : Type u
  Opening    : Type u
  -- Com(value, randomness) → commitment
  commit     : Public → Opening → Commitment

  -- Binding: can't open same commitment to different values.
  -- Prevents adversary from changing committed value after commit phase.
  -- This is the computational binding property - we axiomatize it here.
  --
  -- NOTE: Hiding is NOT formalized. See documentation above.
  -- Demo instances do NOT satisfy hiding - they are for correctness proofs only.
  commitBinding :
    ∀ {x₁ x₂ : Public} {o₁ o₂ : Opening},
      commit x₁ o₁ = commit x₂ o₂ → x₁ = x₂

  /-
  ## Hash Function (Random Oracle)

  The hash function is used for Fiat-Shamir transformation: converting interactive
  proofs to non-interactive by hashing the transcript to derive challenges.

  **Design Choice**: We model hash as a deterministic function with axiomatized
  collision resistance. This is the Random Oracle Model (ROM) - we assume the hash
  behaves like a random function that all parties can query.

  **Reference**: Bellare & Rogaway, "Random Oracles are Practical", CCS 1993.
  Also: Pointcheval & Stern, "Security Proofs for Signature Schemes", EUROCRYPT 1996.

  In practice, instantiate with SHA-3/SHAKE or domain-separated SHA-256.
  The ROM assumption is standard for Schnorr-style signatures.
  -/

  -- Collision resistance assumption (axiomatized for security proofs)
  -- In ROM, this holds with overwhelming probability.
  hashCollisionResistant : Prop

  -- Fiat-Shamir hash: binds challenge to full transcript.
  -- Inputs: message, public key, signers, commitments, nonce sum.
  hash :
    Message →
    Public →                    -- global public key
    List PartyId →              -- participant set S
    List Commitment →           -- nonce commitments
    Public →                    -- aggregated nonce w = Σ w_i
    Challenge

  -- Norm bound predicate for lattice security.
  -- Rejects signatures with large z to prevent leakage.
  normOK : Secret → Prop

  -- Decidability of normOK for runtime checking.
  -- Default: trivially decidable (True or compute-based).
  [normOKDecidable : DecidablePred normOK]

attribute [instance] Scheme.scalarSemiring Scheme.secretAdd Scheme.publicAdd
attribute [instance] Scheme.secretModule Scheme.publicModule
attribute [instance] Scheme.challengeSMulSecret Scheme.challengeSMulPublic
attribute [instance] Scheme.normOKDecidable

/-!
## Key and Message Types

After DKG, each party holds a KeyShare. During DKG, parties exchange
commit and reveal messages to jointly generate the threshold key.
-/

/-- A party's credential after DKG completes. Contains the secret share
    sk_i, public share pk_i = A(sk_i), and global key pk = Σ pk_i. -/
structure KeyShare (S : Scheme) where
  pid  : S.PartyId    -- this party's identifier
  sk_i : S.Secret     -- secret share (never shared)
  pk_i : S.Public     -- public share = A(sk_i)
  pk   : S.Public     -- global public key = Σ pk_j


/-- DKG round 1: party broadcasts commitment to its public share.
    Hiding pk_i until all parties commit prevents adaptive attacks. -/
structure DkgCommitMsg (S : Scheme) where
  sender   : S.PartyId
  commitPk : S.Commitment


/-- DKG round 2: party reveals pk_i and opening to verify commitment.
    Others check: commit(pk_i, opening) = commitPk from round 1. -/
structure DkgRevealMsg (S : Scheme) where
  sender  : S.PartyId
  pk_i    : S.Public
  opening : S.Opening


/-- Party's local state during DKG. The secret sk_i is sampled locally
    and never transmitted. Only the commitment/reveal are broadcast. -/
structure DkgLocalState (S : Scheme) where
  pid    : S.PartyId
  sk_i   : S.Secret     -- locally sampled secret share
  pk_i   : S.Public     -- pk_i = A(sk_i)
  openPk : S.Opening    -- randomness for commitment


/-!
## Signing Message Types

These are placed in Core to break circular dependencies between Phase and Sign.
-/

/-- Round 2 signing message: partial signature z_i = y_i + c·sk_i.
    Ephemeral nonce y_i masks the secret share contribution. -/
structure SignShareMsg (S : Scheme) where
  sender  : S.PartyId
  session : Nat
  z_i     : S.Secret
deriving Repr


end IceNine.Protocol
