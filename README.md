# 🏛️ Algebraic-Quotient-Duality : Invariance Profinie et Régularisation Spectrale

**Cadre unifié d'algèbre commutative et de topologie profinie sur les anneaux principaux**

**Auteur :** Mohamed Ghali (`ORCID: 0009-0006-3364-5341`) • **Domaine :** Algèbre Commutative & Théorie des Nombres • **Licence :** MIT

---

## 📜 Objet de la Théorie

Ce dépôt formalise une structure algébrique unifiée reliant deux phénomènes fondamentaux dans les anneaux principaux $R$ (tels que $\mathbb{Z}$, les entiers de Gauss $\mathbb{Z}[i]$ et l'anneau des polynômes $\mathbb{R}[X]$) :

1. **Invariance Profinie et Factorisation Eulérienne (Régime Coprime)** :  
   Soit $(I_r)_{r \ge 0}$ une filtration décroissante d'idéaux non nuls de $R$ et $\widehat{R} = \varprojlim_r (R/I_r)$ le complété profini muni de sa mesure de Haar normalisée $\mu$. Pour toute famille finie de polynômes $\mathcal{F} \subset R[X]$, le lieu d'admissibilité globale
   $$\Omega(\mathcal{F}) = \bigcap_{f \in \mathcal{F}} f^{-1}(\widehat{R}^\times)$$
   est un sous-espace compact invariant par translation sous les idéaux $I_r$, dont la mesure se factorise en produit eulérien sur $\mathrm{Spec}(R)$.

2. **Dualité Quotient–Bézout et Régularisation Spectrale (Régime Singulier)** :  
   Dans $\mathbb{R}[X]$, pour une décomposition en facteurs quadratiques $Q(X) = \prod_{j=1}^n B_j(X)$ avec cofacteurs $Q_j = \prod_{k \neq j} B_k$, l'opérateur de multiplication $\mathcal{M}_j : u \mapsto u Q_j \bmod B_j$ est un isomorphisme si et seulement si $\gcd(B_j, Q_j) = 1$. En cas de dégénérescence ($\det(\mathcal{M}_j) = 0$, racines multiples), l'opérateur régularisé sur le cône symétrique semi-défini positif
   $$\mathcal{A}_j^* = \mathcal{M}_j^\top \mathcal{M}_j + H_+ + \mu\,\mathrm{Id} \quad (H_+ \succeq 0, \ \mu > 0)$$
   restaure l'inversibilité uniforme avec la minoration spectrale $\det(\mathcal{A}_j^*) \ge \mu^2 > 0$.

---

## 📂 Architecture du Dépôt

* `theorems/UnifiedAlgebraicDuality.lean` : Formalisation pure en **Lean 4** (sans dépendance externe) sur anneaux abstraits.
* `paper/Algebraic_Quotient_Duality.tex` : Mémoire théorique complet en **LaTeX**.
* `.github/workflows/lean_verify.yml` : Vérification mécanique automatique par le compilateur Lean 4.
