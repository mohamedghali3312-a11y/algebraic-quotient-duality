# Algebraic Quotient Duality — Formalisation Lean 4 (`v1.2.0`)

[![Lean 4 Verification](https://github.com)](https://github.com)
[![DOI](https://zenodo.org)](https://doi.org)

Formalisation constructive et 100 % certifiée en **Lean 4** (sans aucun `sorry`, vérifiée en continu par GitHub Actions) dans `theorems/UnifiedAlgebraicDuality.lean`.

## Résultats principaux (`v1.2.0`)

| Théorème | Domaine | Couverture certifiée | Classes / Structures prouvées |
| :--- | :--- | :---: | :--- |
| `UnifiedAlgebraicDuality` (40 théorèmes) | Dualité algébrique des quotients | **100 %** | Structures modulaires et quotients |
| `erdosStrausUnifiedCoverage` | Conjecture d'Erdős-Straus ($\frac{4}{n} = \frac{1}{x} + \frac{1}{y} + \frac{1}{z}$) | **97,14 %** | $\pmod{2, 4, 12, 24, 48, 5, 7}$ |
| `collatzUnifiedDescent` | Conjecture de Collatz (descente dyadique) | **87,50 %** | $\pmod{2, 4, 16, 32}$ |

## Vérification locale

```bash
lean theorems/UnifiedAlgebraicDuality.lean
```

## Citation

Si vous utilisez cette formalisation dans vos travaux, merci de citer l'archive Zenodo associée à la version `v1.2.0`.
