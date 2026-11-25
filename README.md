# Algebraic Quotient Duality — Certification Formelle en Lean 4 Pur (v1.6.0)

[![Lean 4 CI](https://github.com)](https://github.com)
[![DOI](https://zenodo.org)](https://doi.org)
[![ORCID](https://shields.io)](https://orcid.org)

Architecture modulaire de preuve formelle écrite en **Lean 4 pur** (zéro dépendance externe, zéro `sorryAx`), dédiée à l'analyse des projections d'anneaux quotients, des cribles primoriels et aux bornes de couverture constructive sur les conjectures d'Erdős–Straus et de Collatz.

## Résultats Formels Certifiés

| Module | Théorème principal | Couverture certifiée | Axiomes utilisés |
| :--- | :--- | :--- | :--- |
| `UnifiedAlgebraicDuality.lean` | `erdosStrausUnifiedCoverage` | **97,14 %** (1 632 / 1 680 classes mod 1 680) | `[propext, Quot.sound]` |
| `UnifiedAlgebraicDuality.lean` | `collatzHighOrderDescent` | **90,23 %** (231 / 256 classes mod 256) | `[propext, Quot.sound]` |
| `UltraHighCoverage.lean` | `erdosStrausPrimeDivCoverage` | **99,99991 %** (facteurs premiers $p \le 73$) | `[propext, Quot.sound]` |
| `UltraHighCoverage.lean` | `collatzMod16384Eq*` | **> 97,5 %** (descente dyadique mod $2^{14}$) | `[propext, Quot.sound]` |

## Architecture du Dépôt

- `theorems/UnifiedAlgebraicDuality.lean` : 40 théorèmes fondateurs sur les projections d'anneaux (`RingProj`), l'inversibilité modulaire, le théorème des restes chinois et les couvertures modulaires de base.
- `scripts/generate_999999_lean.py` : Générateur déterministe produisant automatiquement les témoins rationnels constructifs $(a, b, c)$ et les descentes dyadiques pas à pas.
- `.github/workflows/lean_verify.yml` : Pipeline d'intégration continue compilant et auditant automatiquement les axiomes (`#print axioms`) à chaque commit.

## Reproductibilité

```bash
python3 scripts/generate_999999_lean.py
lean theorems/UnifiedAlgebraicDuality.lean
lean theorems/UltraHighCoverage.lean
```

## Références & Citation

- **Auteur :** Mohamed Ghali — ORCID : `0009-0006-3364-5341`
- **Archive Zenodo :** `10.5281/zenodo.24424556`
- **Publications HAL :** `hal-05856178`, `hal-05860758`
