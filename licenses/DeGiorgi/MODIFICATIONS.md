# Modifications Log

Tracks modifications to the vendored DeGiorgi code (https://github.com/scottnarmstrong/DeGiorgi,
commit `4c1b307`) per Apache License 2.0 §4(b).

## Format

```
### <YYYY-MM-DD> — <short tag>

**Files**: <list of modified files, relative to this directory>
**Change**: <short description>
```

## Entries

### 2026-04-23 — initial vendoring

**Files**: (none modified)
**Change**: Repository vendored verbatim at commit 4c1b307.

### 2026-04-28 — import-path rewire

**Files**: all `.lean` files under this directory
**Change**: rewrote internal `import DeGiorgi.…` statements as `import DifferentialGeometry.External.DeGiorgi.…` to fit the project's module path layout.

### 2026-05-16 — style-warning cleanup

**Files**:
- `BallExtension.lean`
- `BallExtension/ApproximationControl.lean`
- `BallExtension/SmoothApproximation.lean`
- `BallExtension/SmoothCore.lean`
- `BallExtensionEstimates.lean`
- `BallScaling.lean`
- `DeGiorgiIteration/Linfty.lean`
- `DeGiorgiIteration/PreIteration.lean`
- `Harnack.lean`
- `Holder/Representative.lean`
- `Localization.lean`
- `LpFunctionToolkit.lean`
- `MoserIteration/CutoffPrep/Profiles.lean`
- `MoserIteration/CutoffPrep/RegularizedEnergy.lean`
- `MoserIteration/CutoffPrep/RegularizedWitnesses.lean`
- `MoserIteration/CutoffPrep/WitnessConstruction.lean`
- `MoserIteration/Iteration.lean`
- `Oscillation/BMO.lean`
- `Oscillation/Campanato.lean`
- `Oscillation/LocalJohnNirenberg.lean`
- `Poincare.lean`
- `PositivePart.lean`
- `SobolevChainRule.lean`
- `SobolevPoincare.lean`
- `SobolevSpace/Approximation.lean`
- `SobolevSpace/WeakDerivatives.lean`
- `SobolevSpace/Witnesses.lean`
- `StampacchiaTruncation.lean`
- `Supersolutions/Caccioppoli.lean`
- `Supersolutions/ForwardIteration/Basics.lean`
- `Supersolutions/ForwardIteration/Energy.lean`
- `Supersolutions/InverseEnergy.lean`
- `Supersolutions/RegularizationSupport.lean`
- `Supersolutions/TestFunctions.lean`
- `Support/MeasureBounds.lean`
- `UnitBallApproximationCore/Profiles.lean`
- `UnitBallApproximationCore/Rescaling.lean`
- `WeakFormulation/ExistenceTheory.lean`
- `WeakHarnack.lean`

**Change**: addressed all Lean linter style warnings flagged by `lake build` under this directory. Changes are semantic-preserving and consist of:
- `show <goal>` rewritten to `change <goal>` at sites the linter flagged as goal-modifying;
- `simp [...]` rewritten to `simp only [...]` at sites flagged as flexible (lemma lists adjusted as needed to keep the next tactic step closing);
- `push_neg` replaced with `push Not`;
- isolated `·` bullets merged with the following line;
- `set_option maxHeartbeats N` and `set_option synthInstance.maxHeartbeats N` scoped via `... in` and given an inline comment describing the elaboration that needs the extended budget; a small number of declarations additionally use a narrow `set_option linter.style.setOption false in` so that the `... in`-scoped form is not itself flagged;
- one tactic call in `StampacchiaTruncation.lean` made unification-explicit (`(s := Ioo a b)`) to satisfy the "tactic operates on only one of multiple goals" linter.

### 2026-07-24 — linter cleanup under the project's final Lean options

**Files**:
- `BallExtension/ApproximationControl.lean`
- `BallExtension/Geometry.lean`
- `BallExtension/RoughInput.lean`
- `BallExtension/SmoothApproximation.lean`
- `BallExtensionEstimates.lean`
- `Crossover/ExponentialIntegrability.lean`
- `Crossover/LocalIntegrability.lean`
- `Crossover/LogGradient.lean`
- `Crossover/ProductBound.lean`
- `DeGiorgiIteration/Energy.lean`
- `DeGiorgiIteration/Linfty.lean`
- `DeGiorgiIteration/PreIteration.lean`
- `FiniteCover.lean`
- `Harnack.lean`
- `Holder/LocalBounds.lean`
- `Holder/OscillationDecay.lean`
- `Holder/Representative.lean`
- `Localization.lean`
- `LpFunctionToolkit.lean`
- `MoserIteration/CutoffPrep/Basics.lean`
- `MoserIteration/CutoffPrep/ExactRegularization.lean`
- `MoserIteration/CutoffPrep/PreEstimate.lean`
- `MoserIteration/CutoffPrep/Profiles.lean`
- `MoserIteration/CutoffPrep/RegularizedEnergy.lean`
- `MoserIteration/CutoffPrep/RegularizedWitnesses.lean`
- `MoserIteration/CutoffPrep/WitnessConstruction.lean`
- `MoserIteration/Iteration.lean`
- `Oscillation/BMO.lean`
- `Oscillation/Campanato.lean`
- `Oscillation/LocalJohnNirenberg.lean`
- `Poincare.lean`
- `SobolevChainRule.lean`
- `SobolevPoincare.lean`
- `SobolevSpace/Approximation.lean`
- `SobolevSpace/WeakDerivatives.lean`
- `SobolevSpace/Witnesses.lean`
- `StampacchiaTruncation.lean`
- `Supersolutions/Caccioppoli.lean`
- `Supersolutions/ForwardIteration/Energy.lean`
- `Supersolutions/ForwardIteration/Iteration.lean`
- `Supersolutions/InverseEnergy.lean`
- `Supersolutions/InverseIteration.lean`
- `Supersolutions/RegularizationSupport.lean`
- `Supersolutions/StageOne.lean`
- `Supersolutions/TestFunctions.lean`
- `Support/MeasureBounds.lean`
- `UnitBallApproximationCore/Approximation.lean`
- `UnitBallApproximationCore/Dilation.lean`
- `UnitBallApproximationCore/Rescaling.lean`
- `WeakFormulation/CoefficientOperator.lean`
- `WeakFormulation/ExistenceTheory.lean`
- `WeakFormulation/WeightedEstimates.lean`
- `WeakHarnack.lean`

**Change**: the project's `lakefile.toml` now enables the full Mathlib standard linter set
(`weak.linter.mathlibStandardSet`) with no per-linter opt-outs, so this directory was brought
to zero warnings as well. All changes are semantic-preserving; no statement, proof or
declaration was added, removed or weakened:

- the `set_option linter.style.setOption false in` opt-outs added on 2026-05-16 were **removed**
  (the project no longer permits suppressing a linter anywhere). The underlying diagnostic is
  now avoided instead: a `set_option maxHeartbeats N in` is placed *outermost*, ahead of any
  `omit … in` modifier — Lean's `withSetOptionIn` only strips a leading `set_option`, and an
  `omit … in` in front of it made the option look unscoped — and is followed by a comment line
  explaining the raised budget, as `linter.style.maxHeartbeats` requires;
- source lines longer than 100 columns were re-flowed (`linter.style.longLine`); breaks are at
  existing token boundaries with the continuation indented past the enclosing construct;
- over-long prose lines inside `/-! … -/` module docstrings were re-wrapped;
- blank lines inside a command were removed (`linter.style.emptyLine`);
- binders unused by their declaration were renamed `x` → `_x`, which keeps the binder — and so
  the statement — unchanged (`linter.unusedVariables`);
- simp arguments the linter proved redundant were dropped (`linter.unusedSimpArgs`);
- spacing inside declaration binders was normalised (`linter.style.whitespace`);
- in `BallExtension/ApproximationControl.lean`, two `rw [abs_of_nonneg (by linarith […])]` steps
  were rewritten as a named `have hle : 0 ≤ …` followed by `rw [abs_of_nonneg hle]`, so the
  proof term fits the line limit without an inline nested tactic block. The proof is unchanged.

The original `LICENSE`, `README.md` and `CITATION.cff` remain unmodified.

### 2026-07-28 — heartbeat-free elaboration

**Files**:
- `BallExtension/ApproximationControl.lean`
- `BallExtension/SmoothApproximation.lean`
- `BallExtensionEstimates.lean`
- `Crossover/ExponentialIntegrability.lean`
- `FiniteCover.lean`
- `Harnack.lean`
- `Localization.lean`
- `LpFunctionToolkit.lean`
- `MoserIteration/CutoffPrep/RegularizedEnergy.lean`
- `MoserIteration/CutoffPrep/RegularizedWitnesses.lean`
- `MoserIteration/CutoffPrep/WitnessConstruction.lean`
- `Oscillation/LocalJohnNirenberg.lean`
- `Poincare.lean`
- `SobolevChainRule.lean`
- `SobolevPoincare.lean`
- `SobolevSpace/Approximation.lean`
- `Supersolutions/Caccioppoli.lean`
- `Supersolutions/ForwardIteration/Energy.lean`
- `Supersolutions/InverseEnergy.lean`
- `Supersolutions/StageOne.lean`
- `WeakFormulation/ExistenceTheory.lean`
- `WeakFormulation/WeightedEstimates.lean`
- `WeakHarnack.lean`

**Change**: removed the remaining heartbeat-budget overrides and refactored the affected proof
bodies into explicit integrability, measurability, nonnegativity, monotonicity, and witness-
construction steps that elaborate under the project defaults.

### 2026-08-12 — isolated tactic-bullet cleanup

**Files**:
- `WeakHarnack.lean`

**Change**: merged two isolated tactic bullets with their following tactic lines. This is a
semantic-preserving source-style change; no statement, proof term or declaration was changed.

### 2026-08-17 — namespace-opening cleanup

**Files**:
- `BallExtension.lean`
- `BallExtension/ApproximationControl.lean`
- `BallExtension/Core.lean`
- `BallExtension/Geometry.lean`
- `BallExtension/RoughInput.lean`
- `BallExtension/SmoothApproximation.lean`
- `BallExtension/SmoothCore.lean`
- `BallExtensionEstimates.lean`
- `Common.lean`
- `Crossover/ExponentialIntegrability.lean`
- `Crossover/LocalIntegrability.lean`
- `Crossover/LogGradient.lean`
- `Crossover/ProductBound.lean`
- `Crossover/PublicEstimate.lean`
- `DeGiorgiIteration/CutoffAdmissibility.lean`
- `DeGiorgiIteration/Energy.lean`
- `DeGiorgiIteration/Linfty.lean`
- `DeGiorgiIteration/PreIteration.lean`
- `DeGiorgiIteration/Recurrence.lean`
- `Holder/LocalBounds.lean`
- `Holder/OscillationDecay.lean`
- `Holder/PublicEstimate.lean`
- `LpFunctionToolkit.lean`
- `MoserIteration/Constants.lean`
- `MoserIteration/CutoffPrep/PreEstimate.lean`
- `MoserIteration/CutoffPrep/Profiles.lean`
- `MoserIteration/CutoffPrep/RegularizedEnergy.lean`
- `MoserIteration/CutoffPrep/RegularizedWitnesses.lean`
- `MoserIteration/Iteration.lean`
- `MoserIteration/Linfty.lean`
- `MoserIteration/Sequences.lean`
- `Oscillation/BMO.lean`
- `Oscillation/Campanato.lean`
- `Oscillation/LocalJohnNirenberg.lean`
- `Poincare.lean`
- `PositivePart.lean`
- `SobolevChainRule.lean`
- `SobolevPoincare.lean`
- `SobolevSpace/Approximation.lean`
- `SobolevSpace/PositivePartPrelude.lean`
- `SobolevSpace/WeakDerivatives.lean`
- `SobolevSpace/Witnesses.lean`
- `StampacchiaTruncation.lean`
- `Supersolutions/Caccioppoli.lean`
- `Supersolutions/ForwardIteration/Basics.lean`
- `Supersolutions/ForwardIteration/Energy.lean`
- `Supersolutions/ForwardIteration/Iteration.lean`
- `Supersolutions/ForwardIteration/OneStep.lean`
- `Supersolutions/InverseEnergy.lean`
- `Supersolutions/InverseIteration.lean`
- `Supersolutions/InverseOneStep.lean`
- `Supersolutions/RegularizationSupport.lean`
- `Supersolutions/TestFunctions.lean`
- `Support/MeasureBounds.lean`
- `UnitBallApproximationCore/Approximation.lean`
- `UnitBallApproximationCore/Dilation.lean`
- `UnitBallApproximationCore/Profiles.lean`
- `UnitBallApproximationCore/Rescaling.lean`
- `WeakFormulation/BilinearForm.lean`
- `WeakFormulation/SmoothTests.lean`
- `WeakFormulation/SolutionInterfaces.lean`
- `WeakFormulation/WeightedEstimates.lean`
- `WholeSpaceSobolev.lean`

**Change**: removed namespace and notation-scope tokens that were not used by their files,
retaining each opening whose removal prevented elaboration. This is a semantic-preserving lexical
scope cleanup; no declaration, statement, or proof was changed.

### 2026-08-18 — explicit weak-Harnack chain estimates

**Files**:
- `WeakHarnack.lean`

**Change**: replaced broad simplification and nonlinear arithmetic in the weak-Harnack chain
constant estimates with explicit ring equalities, multiplication monotonicity, and a precise
simplification set. The theorem statements and mathematical inequalities are unchanged.

### 2026-08-18 — explicit crossover measurability

**Files**:
- `Crossover/ExponentialIntegrability.lean`

**Change**: supplied the measurable real exponential integrand and its almost-everywhere
measurability explicitly before applying the constant-multiple lintegral identity, and made a
nearby additive simplification precise. The theorem statements are unchanged.

### 2026-08-20 — explicit small-ball average estimate

**Files**:
- `Crossover/ExponentialIntegrability.lean`

**Change**: replaced a broad additive `simpa` in the small-ball average triangle estimate with
an explicit equality followed by `abs_add_le`. The theorem statement and mathematical argument
are unchanged.

### 2026-08-20 — explicit iteration inequalities

**Files**:
- `DeGiorgiIteration/Linfty.lean`
- `DeGiorgiIteration/PreIteration.lean`
- `MoserIteration/CutoffPrep/RegularizedEnergy.lean`
- `Supersolutions/ForwardIteration/OneStep.lean`
- `Supersolutions/InverseOneStep.lean`
- `Supersolutions/StageOne.lean`
- `WeakFormulation/ExistenceTheory.lean`

**Change**: replaced slow nonlinear arithmetic, broad simplification, and multi-rewrite steps
with direct nonnegativity products, monotonicity lemmas for squares and exponents, explicit factor
rearrangements, and an explicit inner-product congruence. The theorem statements and mathematical
arguments are unchanged.

### 2026-08-21 — declaration-linter cleanup

**Files**:
- `BallExtension/ApproximationControl.lean`
- `BallExtension/RoughInput.lean`
- `BallExtension/SmoothApproximation.lean`
- `Crossover/ExponentialIntegrability.lean`
- `Crossover/LocalIntegrability.lean`
- `Crossover/LogGradient.lean`
- `DeGiorgiIteration/CutoffAdmissibility.lean`
- `DeGiorgiIteration/Energy.lean`
- `DeGiorgiIteration/PreIteration.lean`
- `EllipticCoefficients.lean`
- `FiniteCover.lean`
- `Harnack.lean`
- `Holder/OscillationDecay.lean`
- `Holder/Representative.lean`
- `Localization.lean`
- `LpFunctionToolkit.lean`
- `MoserIteration/Constants.lean`
- `MoserIteration/CutoffPrep/Basics.lean`
- `MoserIteration/CutoffPrep/ExactRegularization.lean`
- `MoserIteration/CutoffPrep/Profiles.lean`
- `MoserIteration/CutoffPrep/RegularizedEnergy.lean`
- `MoserIteration/CutoffPrep/RegularizedWitnesses.lean`
- `MoserIteration/Sequences.lean`
- `Oscillation/BMO.lean`
- `Oscillation/Campanato.lean`
- `Oscillation/LocalJohnNirenberg.lean`
- `Poincare.lean`
- `PositivePart.lean`
- `Supersolutions/ForwardIteration/Energy.lean`
- `Supersolutions/InverseEnergy.lean`
- `Supersolutions/RegularizationSupport.lean`
- `Supersolutions/TestFunctions.lean`
- `Support/MeasureBounds.lean`
- `UnitBallApproximationCore/Dilation.lean`
- `UnitBallApproximationCore/Rescaling.lean`
- `WeakFormulation/ExistenceTheory.lean`
- `WholeSpaceSobolev.lean`

**Change**: resolved Mathlib declaration-linter findings by classifying a proposition-valued
definition as a theorem, removing redundant hypotheses and typeclass assumptions, simplifying a
cast expression to its normal form, retaining a useful ellipticity-ratio theorem without a
redundant simp attribute, and making compatibility-preserving hypotheses explicit dependencies of
their proof terms. The affected mathematical conclusions are unchanged or generalized.

### 2026-08-21 — divergence-data uniqueness generality

**Files**:
- `WeakFormulation/ExistenceTheory.lean`

**Change**: removed a redundant `MemLp` hypothesis from the uniqueness theorem for the
inhomogeneous Dirichlet problem and updated its callers. Existence still requires the integrability
hypothesis; uniqueness now states only the assumptions used by its mathematical argument.

### 2026-08-23 — Mathlib 4.33 API migration

**Files**:
- `Crossover/ExponentialIntegrability.lean`
- `Crossover/ProductBound.lean`
- `ScaledBallEstimates.lean`
- `WeakHarnack.lean`

**Change**: migrated renamed Mathlib APIs and made restriction coercions, rescaling identities,
measurability bridges, the John--Nirenberg level-set identification, the finite-dimensional volume
equivalence, affine ball rescaling, and the Fatou lemma indexing explicit. The theorem statements
and mathematical arguments are unchanged.

### 2026-08-24 — Mathlib 4.33 Lipschitz constant elaboration

**Files**:
- `Crossover/LogGradient.lean`

**Change**: made the nonnegative real type of a Lipschitz constant explicit after Mathlib's
subtype elaboration changed. The theorem statement and mathematical argument are unchanged.

### 2026-08-28 — Mathlib 4.33 migration and warning cleanup

**Files**:
- `BallExtension.lean`
- `BallExtension/ApproximationControl.lean`
- `BallExtension/RoughInput.lean`
- `BallExtension/SmoothApproximation.lean`
- `BallExtension/SmoothCore.lean`
- `BallExtensionEstimates.lean`
- `BallScaling.lean`
- `Crossover/ExponentialIntegrability.lean`
- `Crossover/LocalIntegrability.lean`
- `Crossover/LogGradient.lean`
- `Crossover/ProductBound.lean`
- `DeGiorgiIteration/CutoffAdmissibility.lean`
- `DeGiorgiIteration/Energy.lean`
- `DeGiorgiIteration/Linfty.lean`
- `DeGiorgiIteration/PreIteration.lean`
- `FiniteCover.lean`
- `Harnack.lean`
- `Holder/LocalBounds.lean`
- `Holder/OscillationDecay.lean`
- `Holder/Representative.lean`
- `Localization.lean`
- `LpFunctionToolkit.lean`
- `MoserIteration/CutoffPrep/Basics.lean`
- `MoserIteration/CutoffPrep/ExactRegularization.lean`
- `MoserIteration/CutoffPrep/PreEstimate.lean`
- `MoserIteration/CutoffPrep/Profiles.lean`
- `MoserIteration/CutoffPrep/RegularizedEnergy.lean`
- `MoserIteration/CutoffPrep/WitnessConstruction.lean`
- `MoserIteration/Iteration.lean`
- `MoserIteration/Linfty.lean`
- `Oscillation/BMO.lean`
- `Oscillation/Campanato.lean`
- `Oscillation/LocalJohnNirenberg.lean`
- `Poincare.lean`
- `PositivePart.lean`
- `ScaledBallEstimates.lean`
- `SobolevChainRule.lean`
- `SobolevPoincare.lean`
- `SobolevSpace/Approximation.lean`
- `SobolevSpace/WeakDerivatives.lean`
- `SobolevSpace/Witnesses.lean`
- `StampacchiaTruncation.lean`
- `Supersolutions/Caccioppoli.lean`
- `Supersolutions/ForwardIteration/Basics.lean`
- `Supersolutions/ForwardIteration/Energy.lean`
- `Supersolutions/ForwardIteration/Iteration.lean`
- `Supersolutions/ForwardIteration/OneStep.lean`
- `Supersolutions/InverseEnergy.lean`
- `Supersolutions/InverseIteration.lean`
- `Supersolutions/InverseOneStep.lean`
- `Supersolutions/RegularizationSupport.lean`
- `Supersolutions/StageOne.lean`
- `Supersolutions/TestFunctions.lean`
- `Support/MeasureBounds.lean`
- `UnitBallApproximationCore/Approximation.lean`
- `UnitBallApproximationCore/Dilation.lean`
- `UnitBallApproximationCore/Profiles.lean`
- `UnitBallApproximationCore/Rescaling.lean`
- `WeakFormulation/BilinearForm.lean`
- `WeakFormulation/CoefficientOperator.lean`
- `WeakFormulation/ExistenceTheory.lean`
- `WeakFormulation/SmoothTests.lean`
- `WeakFormulation/WeightedEstimates.lean`
- `WeakHarnack.lean`
- `WholeSpaceSobolev.lean`

**Change**: completed the remaining Mathlib 4.33 API and elaboration migration and brought the
vendored modules to the project's zero-warning standard. The semantic-preserving changes update
renamed or deprecated APIs and import paths, remove redundant simp arguments and obsolete tactic
steps, replace proof-valued local instances with ordinary local facts, repair declaration-linter
findings by removing genuinely unused assumptions, and make dependent casts and coercions explicit
where the newer elaborator no longer infers them. The affected conclusions and mathematical
arguments are unchanged or generalized. The original `LICENSE`, `README.md`, and `CITATION.cff`
remain unmodified.

### 2026-08-29 — definition-name normalization

**Files**:
- `BallExtension/RoughInput.lean`
- `BallExtension/SmoothApproximation.lean`
- `BallExtensionEstimates.lean`
- `BallScaling.lean`
- `Crossover/ExponentialIntegrability.lean`
- `Crossover/LocalIntegrability.lean`
- `Crossover/LogGradient.lean`
- `Crossover/ProductBound.lean`
- `Crossover/PublicEstimate.lean`
- `DeGiorgiIteration/CutoffAdmissibility.lean`
- `DeGiorgiIteration/Energy.lean`
- `DeGiorgiIteration/Linfty.lean`
- `DeGiorgiIteration/PreIteration.lean`
- `Harnack.lean`
- `Holder/LocalBounds.lean`
- `Holder/OscillationDecay.lean`
- `Holder/PublicEstimate.lean`
- `Holder/Representative.lean`
- `Localization.lean`
- `MoserIteration/Constants.lean`
- `MoserIteration/CutoffPrep/Basics.lean`
- `MoserIteration/CutoffPrep/ExactRegularization.lean`
- `MoserIteration/CutoffPrep/PreEstimate.lean`
- `MoserIteration/CutoffPrep/RegularizedEnergy.lean`
- `MoserIteration/CutoffPrep/RegularizedWitnesses.lean`
- `MoserIteration/Iteration.lean`
- `MoserIteration/Linfty.lean`
- `Oscillation/BMO.lean`
- `Oscillation/Campanato.lean`
- `Oscillation/LocalJohnNirenberg.lean`
- `Poincare.lean`
- `PositivePart.lean`
- `ScaledBallEstimates.lean`
- `SobolevChainRule.lean`
- `SobolevPoincare.lean`
- `SobolevSpace/Approximation.lean`
- `SobolevSpace/Witnesses.lean`
- `Supersolutions/Caccioppoli.lean`
- `Supersolutions/ForwardIteration/Iteration.lean`
- `Supersolutions/ForwardIteration/OneStep.lean`
- `Supersolutions/InverseIteration.lean`
- `Supersolutions/InverseOneStep.lean`
- `Supersolutions/StageOne.lean`
- `Supersolutions/TestFunctions.lean`
- `Support/IterationConstants.lean`
- `UnitBallApproximationCore/Approximation.lean`
- `UnitBallApproximationCore/Dilation.lean`
- `UnitBallApproximationCore/Rescaling.lean`
- `WeakFormulation/WeightedEstimates.lean`
- `WeakHarnack.lean`
- `WholeSpaceSobolev.lean`

**Change**: renamed definition, abbreviation, and structure-field identifiers from theorem-style
snake case to Mathlib camel case, and updated every internal reference. Two witness constructors
whose short source names also name Mathlib declarations were migrated only at their project-owned
declarations and qualified references. This is an API-only, semantic-preserving migration; theorem
statements and proof bodies are unchanged.

<!-- Add entries below as modifications occur. -->

### 2026-09-04 — theorem-name normalization

**Files**:
- `BallExtension/ApproximationControl.lean`
- `BallExtension/RoughInput.lean`

**Change**: renamed the equality theorem for `exactUnitBallExtensionGradApply` so that its
declaration name identifies the `smoothUnitBallExtensionGradCandidate` on its right-hand side.
Also removed the redundant `generic` suffix from a private norm-bound helper. The theorem
statements and proofs are unchanged.

### 2026-09-07 — positive-test density extension

**Files**:
- `SobolevSpace/PositiveTestDensity.lean`

**Change**: added the nonnegative smooth density theorem for pointwise nonnegative `H₀¹`
functions and the resulting smooth-test criterion for weak supersolutions, and adapted their
proofs to Mathlib 4.33 elaboration and indicator APIs. The density construction uses exact-support
smooth positive-part regularizations and preserves the limit witness's weak gradient.

### 2026-09-07 — strong minimum principle extension

**Files**:
- `StrongMinimum.lean`

**Change**: added the strong minimum principle on Euclidean balls from the weak Harnack
inequality, migrated renamed definitions and coefficient-rescaling elaboration to Mathlib 4.33,
and placed the two public conclusions in the `IsSupersolution` namespace with descriptive names.

### 2026-09-07 — homogeneous weak-solution equivalence

**Files**:
- `WeakFormulation/ExistenceTheory.lean`

**Change**: proved that a function which is simultaneously a weak subsolution and weak
supersolution satisfies the equality-form homogeneous weak identity against arbitrary signed
`H₀¹` tests. The proof decomposes smooth compactly supported tests into nonnegative tests and then
uses the existing Sobolev approximation and bilinear-continuity argument. Exposed that shared
extension as `bilinFormOfCoeff_eq_of_isSmoothTestOn`, the conversion in the `IsSolution` namespace,
the equivalence of the two solution interfaces, and vanishing of the bilinear form on signed
`H₀¹` tests. These additions migrate the source branch's smooth-test and homogeneous-solution
APIs without changing the established existence and uniqueness conclusions.

### 2026-09-07 — weak divergence pairing extension

**Files**:
- `WeakFormulation/BilinearForm.lean`
- `WeakFormulation/WeakDivergence.lean`

**Change**: added assembly of weak divergence from the componentwise weak partial derivatives
and the equality of the divergence-form functional with its scalar `L²` pairing on `H₀¹` tests.
Migrated finite-sum names and function-space elaboration to Mathlib 4.33, clarified the public
declaration names, and removed the redundant supplied Sobolev witness from the pairing theorem.
The witness-independence identity and the new pairing theorem hold in every finite dimension,
including dimension zero; removed their unnecessary `NeZero` assumption. The weak gradient used
in the proof remains the witness tied to the `H₀¹` approximation.
