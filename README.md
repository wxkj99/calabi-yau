# Calabi–Yau

A formalization in [Lean 4](https://lean-lang.org/) and [Mathlib](https://github.com/leanprover-community/mathlib4)
of Yau's solution of the Calabi conjecture.

## Main results

All statements are in [`Comparator/Challenge.lean`](Comparator/Challenge.lean). Throughout, `M` is a
compact connected complex manifold of complex dimension `n` and `ω₀` is a Kähler form on `M`.

| Theorem | Statement |
| --- | --- |
| `CalabiYau.complexMongeAmpere` | For smooth `F` with `∫ e^F ω₀ⁿ = ∫ ω₀ⁿ`, the complex Monge–Ampère equation `(ω₀ + i∂∂̄φ)ⁿ = e^F ω₀ⁿ` has a smooth solution with `ω₀ + i∂∂̄φ > 0`, unique up to an additive constant. |
| `CalabiYau.calabiConjecture_of_sub_eq_mddbar` | If `ρ - Ric(ω₀) = i∂∂̄F`, there is a unique Kähler form `ω₀ + i∂∂̄φ` with Ricci form `ρ`. |
| `CalabiYau.ricciFlat_of_ricciForm_eq_mddbar` | If `Ric(ω₀) = i∂∂̄F`, there is a unique Ricci-flat Kähler form `ω₀ + i∂∂̄φ`. |
| `CalabiYau.calabiConjecture` | If `ρ` is a smooth closed real `(1,1)`-form with `[ρ] = 2π c₁(M)`, the Kähler class `[ω₀]` contains a unique Kähler form with Ricci form `ρ`. |
| `CalabiYau.ricciFlat_of_firstChernClass_eq_zero` | If `c₁(M) = 0` in `H²(M; ℝ)`, every Kähler class contains a unique Ricci-flat Kähler form. |

Each of these theorems depends only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain (`leanprover/lean4:v4.33.1`) and
Mathlib version are pinned in `lean-toolchain` and `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

To check the axioms, run `lake env lean` on a file containing

```lean
import Comparator.Challenge
#print axioms CalabiYau.calabiConjecture
```

## Authors

Jiatong Yang, Qiuzhen College, Tsinghua University

Jinfeng Xu, Guangzhou University

## License

Apache License 2.0; see [`LICENSE`](LICENSE). Parts of this repository are adapted from
[differential-geometry](https://github.com/qinz1yang/differential-geometry) and
[DeGiorgi](https://github.com/scottnarmstrong/DeGiorgi); see [`NOTICE`](NOTICE) and
[`licenses/`](licenses/).
