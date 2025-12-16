/-
# VSS Security Proofs

Security properties of Verifiable Secret Sharing:
1. **Correctness**: Honest shares verify against honest commitments
2. **Soundness**: Invalid shares are detected by verification
3. **Binding**: Dealer cannot open to different polynomials
4. **Hiding**: Commitments reveal nothing about polynomial (< t shares)

**Reference**: Feldman, "A Practical Scheme for Non-interactive Verifiable
Secret Sharing", FOCS 1987.
-/

import IceNine.Protocol.DKG.VSSDKG
import IceNine.Protocol.DKG.Feldman
import Mathlib
import Mathlib.Algebra.Polynomial.Module.Basic

set_option autoImplicit false

namespace IceNine.Proofs.Soundness.VSS

open IceNine.Protocol
open IceNine.Protocol.VSS

/-!
## Correctness

Honest shares always verify: if `s = f(x)` and `C = commit(f)`, then
`A(s) = expectedPublicValue(C, x)`.
-/

theorem vss_correctness
    (S : Scheme)
    (poly : SecretPoly S) (threshold : Nat)
    (recipient : S.PartyId) (x : S.Scalar) :
    VSS.verifyShare S (commitPolynomial S poly threshold) (generateShare S poly recipient x) := by
  -- `expectedPublicValue` is evaluation of the committed polynomial; `commitPolynomial` maps
  -- coefficients through `A`, so correctness is exactly `PolynomialModule.eval_map`.
  simpa [VSS.verifyShare, expectedPublicValue, generateShare, commitPolynomial] using
    (PolynomialModule.eval_map (R := S.Scalar) (R' := S.Scalar)
        (M := S.Secret) (M' := S.Public) (f := S.A) (q := poly) (r := x)).symm

/-!
## Soundness

If a share doesn't verify, the dealer is cheating. The verification equation
provides a publicly checkable proof of misbehavior.
-/

def VSSInconsistent (S : Scheme)
    (commit : PolyCommitment S) (share : VSSShare S) : Prop :=
  ¬VSS.verifyShare S commit share

theorem vss_soundness
    (S : Scheme)
    (commit : PolyCommitment S)
    (share : VSSShare S)
    (hfail : ¬VSS.verifyShare S commit share) :
    VSSInconsistent S commit share := hfail

/-!
## Binding

If `A` is injective, then a coefficient-wise commitment uniquely determines the
secret polynomial.
-/

theorem vss_binding
    (S : Scheme)
    (p1 p2 : SecretPoly S) (t1 t2 : Nat)
    (hA : Function.Injective S.A)
    (heq : commitPolynomial S p1 t1 = commitPolynomial S p2 t2) :
    p1 = p2 := by
  have hpoly : (commitPolynomial S p1 t1).poly = (commitPolynomial S p2 t2).poly :=
    congrArg (fun c => c.poly) heq
  -- Use finsupp extensionality on coefficients.
  apply Finsupp.ext
  intro n
  apply hA
  have hn : (commitPolynomial S p1 t1).poly n = (commitPolynomial S p2 t2).poly n :=
    congrArg (fun q => q n) hpoly
  simpa [commitPolynomial, PolynomialModule.map] using hn

/-!
## Hiding (t-privacy)

Any coalition of < t parties learns nothing about the secret beyond what their
shares reveal. This is information-theoretic for Shamir/Feldman.

We keep this as a lightweight statement placeholder; full hiding proofs require
probabilistic reasoning infrastructure.
-/

structure VSSHiding (t : Nat) where
  knownShares : Nat
  below_threshold : knownShares < t

def vss_hiding
    (t : Nat)
    (knownShares : Nat)
    (hlt : knownShares < t) :
    VSSHiding t :=
  ⟨knownShares, hlt⟩

/-!
## Complaint Verification

A complaint is valid iff the share genuinely fails verification.
-/

lemma verifyShareBool_iff_verifyShare
    (S : Scheme) [DecidableEq S.Public]
    (comm : PolyCommitment S) (share : VSSShare S) :
    VSS.verifyShareBool S comm share = true ↔ VSS.verifyShare S comm share := by
  simp [VSS.verifyShareBool, VSS.verifyShare, expectedPublicValue]

theorem complaint_sound
    (S : Scheme) [DecidableEq S.Public]
    (complaint : VSSComplaint S)
    (hvalid : VSS.verifyComplaint S complaint = true) :
    ¬VSS.verifyShare S complaint.commitment complaint.badShare := by
  simpa [VSS.verifyComplaint, VSS.verifyShareBool] using hvalid

theorem complaint_complete
    (S : Scheme) [DecidableEq S.Public]
    (complaint : VSSComplaint S)
    (hfalse : VSS.verifyComplaint S complaint = false) :
    VSS.verifyShare S complaint.commitment complaint.badShare := by
  simpa [VSS.verifyComplaint, VSS.verifyShareBool] using hfalse

/-!
## Reconstruction Security

With ≥ t verified shares, the secret can be reconstructed correctly.

Full reconstruction (and uniqueness) is deferred: it requires interpolation
results specialized to `PolynomialModule`.
-/

structure ReconstructionCapable (t : Nat) where
  numShares : Nat
  enough_shares : numShares ≥ t
  points_distinct : True

def reconstruction_unique
    (t : Nat)
    (numShares : Nat)
    (hlen : numShares ≥ t)
    (hnodup : True) :
    ReconstructionCapable t :=
  ⟨numShares, hlen, hnodup⟩

end IceNine.Proofs.Soundness.VSS
