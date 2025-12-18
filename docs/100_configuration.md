# Local Rejection Signing

Ice Nine implements restart-free threshold Dilithium signing with local rejection sampling. Each signer applies rejection sampling locally before sending their partial signature. The bounds are chosen so that any valid combination of partials automatically satisfies global bounds.

The key invariant is that if each of T signers produces z_i with ‖z_i‖∞ ≤ B_local, then the aggregate z = Σz_i satisfies ‖z‖∞ ≤ T · B_local ≤ B_global. This eliminates global rejection as a distributed control-flow path. Given sufficient honest parties at or above threshold, signing does not trigger a distributed restart due to rejection sampling.

## ThresholdConfig Structure

The `ThresholdConfig` structure bundles all parameters for threshold signing with local rejection.

```lean
structure ThresholdConfig where
  totalParties : Nat      -- n: total parties in the scheme
  threshold : Nat         -- t: minimum parties for reconstruction
  maxSigners : Nat        -- T: maximum partials aggregated (usually = t)
  globalBound : Nat       -- B_global: Dilithium bound (γ₁ - β)
  localBound : Nat        -- B_local: per-signer bound (B_global / T)
  maxLocalAttempts : Nat  -- maximum rejection attempts before failure
```

The `localBound` is derived automatically as `globalBound / maxSigners`. This ensures that when T signers each produce a partial with norm at most B_local, the aggregate stays within B_global.

## Creating Configurations

Use `ThresholdConfig.create` for custom configurations or the preset constructors for standard security levels.

```lean
-- Custom configuration for 5 parties with default threshold
let cfg := ThresholdConfig.create 5 130994

-- Custom threshold (3-of-5 instead of default 4-of-5)
let cfg := ThresholdConfig.create 5 130994 (t := 3) (maxSigners := 3)

-- Standard Dilithium configurations
let cfg2 := ThresholdConfig.dilithium2 5  -- 128-bit security
let cfg3 := ThresholdConfig.dilithium3 5  -- 192-bit security
let cfg5 := ThresholdConfig.dilithium5 5  -- 256-bit security
```

The `create` constructor fills validity proofs automatically using omega. If proof obligations fail, the configuration parameters are inconsistent.

## Default Threshold

The default threshold uses the 2/3+1 rule for Byzantine fault tolerance.

| Parties (n) | Threshold (t) | Max Faulty (f) |
|-------------|---------------|----------------|
| 3 | 3 | 0 |
| 4 | 3 | 1 |
| 5 | 4 | 1 |
| 6 | 5 | 1 |
| 7 | 5 | 2 |
| 10 | 7 | 3 |

The formula is `t = 2n/3 + 1` (integer division). This ensures honest majority for BFT protocols.

## Dilithium Security Levels

Ice Nine supports the three NIST-standardized Dilithium parameter sets.

| Level | γ₁ | β | B_global (γ₁ - β) | Security |
|-------|-----|-----|-------------------|----------|
| Dilithium2 | 2¹⁷ (131072) | 78 | 130994 | 128-bit |
| Dilithium3 | 2¹⁹ (524288) | 196 | 524092 | 192-bit |
| Dilithium5 | 2¹⁹ (524288) | 120 | 524168 | 256-bit |

The global bound is γ₁ - β where γ₁ is the nonce coefficient range and β = τ · η (challenge weight times secret coefficient bound).

## Local Bound Calculation

The local bound is computed as B_local = B_global / T where T is `maxSigners`. This creates headroom for aggregation.

| Signers (T) | B_local (Dilithium2) | B_local (Dilithium3) |
|-------------|----------------------|----------------------|
| 3 | 43664 | 174697 |
| 4 | 32748 | 131023 |
| 5 | 26198 | 104818 |
| 7 | 18713 | 74870 |
| 10 | 13099 | 52409 |

Smaller local bounds mean tighter rejection sampling. More signers require each signer to produce smaller partials.

## Rejection Rate Estimation

The `expectedLocalAttempts` accessor estimates how many sampling attempts each signer needs on average.

```lean
def ThresholdConfig.expectedLocalAttempts (cfg : ThresholdConfig) : Nat :=
  if cfg.globalBound > 2 * cfg.localBound then
    cfg.globalBound / (cfg.globalBound - 2 * cfg.localBound)
  else
    cfg.maxLocalAttempts
```

The formula approximates 1 / (1 - 2·B_local/B_global). Tighter local bounds increase rejection rates.

| Signers (T) | Ratio (B_local/B_global) | Expected Attempts |
|-------------|--------------------------|-------------------|
| 3 | 0.33 | ~3 |
| 4 | 0.25 | ~2 |
| 5 | 0.20 | ~1.7 |
| 7 | 0.14 | ~1.4 |
| 10 | 0.10 | ~1.25 |

For typical configurations, signers need 1-4 attempts on average. The `maxLocalAttempts` parameter (default 256) provides a safety bound for pathological cases.

## Parameter Tuning Guidelines

When tuning parameters, consider these tradeoffs.

### Threshold vs Rejection Rate

Lower thresholds mean fewer signers aggregate their partials. Fewer signers means larger local bounds and lower rejection rates. However, lower thresholds reduce fault tolerance.

### Security Level vs Performance

Higher security levels (Dilithium3, Dilithium5) have larger global bounds. Larger bounds mean more headroom for local rejection, so rejection rates decrease. The tradeoff is larger signatures and keys.

### maxLocalAttempts Setting

The default of 256 attempts is conservative. In practice, signers rarely need more than 10 attempts. Lower values fail faster on misconfigured systems. Higher values handle edge cases but delay failure detection.

For latency-sensitive applications, consider setting `maxLocalAttempts` to 32 or 64. For maximum reliability, keep the default.

## Configuration Validation

The `validate` method checks configuration consistency.

```lean
def ThresholdConfig.validate (cfg : ThresholdConfig) : ConfigValidation

-- Returns .ok for valid configurations, or a specific error:
-- .noParties, .thresholdZero, .thresholdExceedsParties,
-- .maxSignersBelowThreshold, .globalBoundZero, .localBoundZero,
-- .localBoundTooLarge
```

Always validate configurations from untrusted sources before use. The structure proofs guarantee consistency for configurations created through `create`, but deserialized configurations should be validated.

## Abort Threshold

The abort threshold determines how many parties must agree to abort a session.

```lean
def ThresholdConfig.abortThreshold (cfg : ThresholdConfig) : Nat :=
  cfg.maxFaulty + 1
```

This equals f + 1 where f = n - t is the maximum faulty parties. The +1 ensures at least one honest party agreed to abort. This prevents a coalition of f malicious parties from forcing spurious aborts.

## Threshold and Security Margins

Increasing the number of signers T reduces each signer's local bound proportionally. This affects security margins in two ways.

First, smaller local bounds increase the precision required for norm checking. Production implementations must use exact arithmetic or verified bounds.

Second, the aggregate bound T · B_local approaches B_global as T increases. At the limit, there is no margin for rounding errors. Keep T well below the theoretical maximum.

For most deployments, use the default threshold (2/3+1) with the matching maxSigners value. This provides good fault tolerance with comfortable rejection rates.
