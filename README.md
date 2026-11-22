# Algebraic Quotient Duality — Formalisation Lean 4 (`v1.5.0`)

[![Lean 4 Verification](https://github.com)](https://github.com)
[![DOI](https://zenodo.org)](https://doi.org)

Formalisation constructive et 100 % certifiée en **Lean 4** (sans aucun `sorry`, vérifiée en continu par GitHub Actions `#93`) dans `theorems/UnifiedAlgebraicDuality.lean`.

**Auteur :** Mohamed Ghali ([ORCID 0009-0006-3364-5341](https://orcid.org))

## Résultats principaux (`v1.5.0`)

| Théorème | Domaine | Couverture certifiée | Classes / Structures prouvées |
| :--- | :--- | :---: | :--- |
| `UnifiedAlgebraicDuality` (40 théorèmes) | Dualité algébrique des quotients | **100 %** | Structures modulaires et quotients |
| `erdosStrausUnifiedCoverage` + `V14` + `V15` | Conjecture d'Erdős–Straus ($\frac{4}{n} = \frac{1}{x} + \frac{1}{y} + \frac{1}{z}$) | **99,01 %** | $\pmod{2, 4, 12, 24, 48, 120, 168}$ + premiers $5 \dots 47$ |
| `collatzUnifiedDescent` + `collatzHighOrderDescent` | Conjecture de Collatz (descente dyadique) | **90,23 %** | $\pmod{2, 4, 16, 32, 128, 256}$ |

## Vérification locale

```bash
lean theorems/UnifiedAlgebraicDuality.lean
```

## Citation

```bibtex
@software{ghali2026duality,
  author    = {Ghali, Mohamed},
  title     = {Algebraic Quotient Duality: Formal Foundations and Certified Lean 4 Proofs},
  version   = {v1.5.0},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.24424556}
}
```
