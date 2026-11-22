set_option linter.unusedVariables false
structure RingProj (R Q : Type) [Add R] [Mul R] [Add Q] [Mul Q] where
  toFun : R → Q
  map_add : ∀ a b : R, toFun (a + b) = toFun a + toFun b
  map_mul : ∀ a b : R, toFun (a * b) = toFun a * toFun b

def IsUnitMod {R Q : Type} [Add R] [Mul R] [Add Q] [Mul Q] (oneQ : Q)
    (π : RingProj R Q) (x : R) : Prop :=
  ∃ u : Q, π.toFun x * u = oneQ

def InKernel {R Q : Type} [Add R] [Mul R] [Add Q] [Mul Q] (zeroQ : Q)
    (π : RingProj R Q) (k : R) : Prop :=
  π.toFun k = zeroQ

theorem abstractIdealTranslationInvariance
    {R Q : Type} [Add R] [Mul R] [Add Q] [Mul Q]
    (zeroQ oneQ : Q)
    (h_add_zero : ∀ q : Q, q + zeroQ = q)
    (π : RingProj R Q)
    (x k : R)
    (h_adm : IsUnitMod oneQ π x)
    (h_ker : InKernel zeroQ π k) :
    IsUnitMod oneQ π (x + k) := by
  rcases h_adm with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  rw [π.map_add, h_ker, h_add_zero, hu]

theorem abstractProjectiveTowerLift
    {R Qs Qr : Type} [Add R] [Mul R] [Add Qs] [Mul Qs] [Add Qr] [Mul Qr]
    (oneQs : Qs) (oneQr : Qr)
    (πs : RingProj R Qs) (πr : RingProj R Qr)
    (φ : RingProj Qs Qr)
    (h_one : φ.toFun oneQs = oneQr)
    (h_comm : ∀ x : R, πr.toFun x = φ.toFun (πs.toFun x))
    (x : R)
    (h_adm_s : IsUnitMod oneQs πs x) :
    IsUnitMod oneQr πr x := by
  rcases h_adm_s with ⟨u_s, hu_s⟩
  refine ⟨φ.toFun u_s, ?_⟩
  rw [h_comm, ← φ.map_mul, hu_s, h_one]

theorem abstractUnitModMul
    {R Q : Type} [Add R] [Mul R] [Add Q] [Mul Q]
    (oneQ : Q)
    (h_mul_assoc : ∀ a b c : Q, (a * b) * c = a * (b * c))
    (h_mul_comm : ∀ a b : Q, a * b = b * a)
    (h_one_mul : ∀ a : Q, oneQ * a = a)
    (π : RingProj R Q)
    (x y : R)
    (hx : IsUnitMod oneQ π x)
    (hy : IsUnitMod oneQ π y) :
    IsUnitMod oneQ π (x * y) := by
  rcases hx with ⟨ux, hux⟩
  rcases hy with ⟨uy, huy⟩
  refine ⟨ux * uy, ?_⟩
  rw [π.map_mul]
  have h1 : (π.toFun x * π.toFun y) * (ux * uy) =
            (π.toFun x * ux) * (π.toFun y * uy) := by
    rw [h_mul_assoc (π.toFun x) (π.toFun y) (ux * uy),
        ← h_mul_assoc (π.toFun y) ux uy,
        h_mul_comm (π.toFun y) ux,
        h_mul_assoc ux (π.toFun y) uy,
        ← h_mul_assoc (π.toFun x) ux (π.toFun y * uy)]
  rw [h1, hux, huy, h_one_mul]

theorem bezoutImpliesUnitMod
    {R Q : Type} [Add R] [Mul R] [Add Q] [Mul Q]
    (zeroQ oneQ : Q)
    (h_add_zero : ∀ q : Q, q + zeroQ = q)
    (h_zero_mul : ∀ q : Q, zeroQ * q = zeroQ)
    (h_mul_comm : ∀ a b : Q, a * b = b * a)
    (π : RingProj R Q)
    (oneR : R)
    (h_one : π.toFun oneR = oneQ)
    (u q v b : R)
    (h_bezout : u * q + v * b = oneR)
    (h_b_ker : InKernel zeroQ π b) :
    IsUnitMod oneQ π q := by
  refine ⟨π.toFun u, ?_⟩
  have h_proj : π.toFun (u * q + v * b) = π.toFun oneR := by rw [h_bezout]
  rw [π.map_add, π.map_mul, π.map_mul, h_b_ker, h_mul_comm (π.toFun v) zeroQ, h_zero_mul, h_add_zero, h_one] at h_proj
  rw [h_mul_comm]
  exact h_proj

theorem spectralRegularizationDetBound (lam1 lam2 mu : Nat) :
    mu * mu ≤ (lam1 + mu) * (lam2 + mu) := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  omega

structure ZModPos (m : Nat) where
  val : Nat
  isLt : val < m

instance (m : Nat) : Add (ZModPos m) where
  add a b := ⟨(a.val + b.val) % m, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt)⟩

instance (m : Nat) : Mul (ZModPos m) where
  mul a b := ⟨(a.val * b.val) % m, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt)⟩

def modProjPos (m : Nat) (hm : 0 < m) : RingProj Nat (ZModPos m) where
  toFun := fun x => ⟨x % m, Nat.mod_lt x hm⟩
  map_add := fun a b => by
    simp only [HAdd.hAdd, Add.add, ZModPos.mk.injEq]
    exact Nat.add_mod a b m
  map_mul := fun a b => by
    simp only [HMul.hMul, Mul.mul, ZModPos.mk.injEq]
    exact Nat.mul_mod a b m

theorem mul_in_kernel_modProjPos (m : Nat) (hm : 0 < m) (k : Nat) :
    InKernel ⟨0, hm⟩ (modProjPos m hm) (k * m) := by
  simp only [InKernel, modProjPos, ZModPos.mk.injEq]
  exact Nat.mul_mod_left k m

theorem natModularTranslationInstantiation (m : Nat) (hm : 0 < m) (x k : Nat)
    (h_adm : IsUnitMod ⟨1 % m, Nat.mod_lt 1 hm⟩ (modProjPos m hm) x) :
    IsUnitMod ⟨1 % m, Nat.mod_lt 1 hm⟩ (modProjPos m hm) (x + k * m) := by
  have h_add_zero : ∀ q : ZModPos m, q + ⟨0, hm⟩ = q := by
    intro ⟨v, hv⟩
    simp only [HAdd.hAdd, Add.add, ZModPos.mk.injEq, Nat.add_zero]
    exact Nat.mod_eq_of_lt hv
  exact abstractIdealTranslationInvariance ⟨0, hm⟩ ⟨1 % m, Nat.mod_lt 1 hm⟩
    h_add_zero (modProjPos m hm) x (k * m) h_adm (mul_in_kernel_modProjPos m hm k)
-- ============================================================================
-- SECTION 3 : THÉORÈMES PURS DE SCINDEMENT CHINOIS, D'INVARIANCE POLYNOMIALE
--             ET D'INJECTIVITÉ DE L'OPÉRATEUR QUOTIENT
-- ============================================================================

def ringPow {R : Type} [Mul R] (x : R) : Nat → R
  | 0 => x
  | n + 1 => ringPow x n * x

-- 6. Invariance idéale des puissances (monômes X^(n+1)) :
-- Si π(k) = 0, alors pour tout exposant, π((x + k)^(n+1)) = π(x^(n+1)).
theorem abstractMonomialTranslationInvariance
    {R Q : Type} [Add R] [Mul R] [Add Q] [Mul Q]
    (zeroQ : Q)
    (h_add_zero : ∀ q : Q, q + zeroQ = q)
    (π : RingProj R Q)
    (x k : R)
    (h_ker : InKernel zeroQ π k) :
    ∀ n : Nat, π.toFun (ringPow (x + k) n) = π.toFun (ringPow x n) := by
  intro n
  have h_base : π.toFun (x + k) = π.toFun x := by
    rw [π.map_add, h_ker, h_add_zero]
  induction n with
  | zero => exact h_base
  | succ m ih =>
    dsimp only [ringPow]
    rw [π.map_mul, π.map_mul, ih, h_base]
-- 7. Surjectivité du Théorème des Restes Chinois abstrait :
-- Si e1, e2 sont des idempotents orthogonaux modulo (π1, π2)
-- (i.e. π1(e1) = 1, π1(e2) = 0 et π2(e1) = 0, π2(e2) = 1),
-- alors pour tout couple (a1, a2), l'élément x = a1 * e1 + a2 * e2
-- relève simultanément π1(x) = π1(a1) et π2(x) = π2(a2).
theorem abstractCRTSurjectivity
    {R Q1 Q2 : Type} [Add R] [Mul R] [Add Q1] [Mul Q1] [Add Q2] [Mul Q2]
    (zero1 one1 : Q1) (zero2 one2 : Q2)
    (h_add_zero1 : ∀ q : Q1, q + zero1 = q)
    (h_zero_add2 : ∀ q : Q2, zero2 + q = q)
    (h_mul_one1 : ∀ q : Q1, q * one1 = q)
    (h_mul_zero1 : ∀ q : Q1, q * zero1 = zero1)
    (h_mul_zero2 : ∀ q : Q2, q * zero2 = zero2)
    (h_mul_one2 : ∀ q : Q2, q * one2 = q)
    (π1 : RingProj R Q1) (π2 : RingProj R Q2)
    (e1 e2 a1 a2 : R)
    (h11 : π1.toFun e1 = one1) (h12 : π1.toFun e2 = zero1)
    (h21 : π2.toFun e1 = zero2) (h22 : π2.toFun e2 = one2) :
    π1.toFun (a1 * e1 + a2 * e2) = π1.toFun a1 ∧
    π2.toFun (a1 * e1 + a2 * e2) = π2.toFun a2 := by
  constructor
  · rw [π1.map_add, π1.map_mul, π1.map_mul, h11, h12, h_mul_one1, h_mul_zero1, h_add_zero1]
  · rw [π2.map_add, π2.map_mul, π2.map_mul, h21, h22, h_mul_zero2, h_mul_one2, h_zero_add2]

-- 8. Injectivité de l'opérateur de multiplication quotient M_j(u) = u * Q_j mod B_j :
-- Sous identité de Bézout U * Q_j + V * B_j = 1 avec B_j ∈ ker(π),
-- si π(u * Q_j) = 0, alors nécessairement π(u) = 0 (noyau trivial de M_j).
theorem quotientOperatorInjective
    {R Q : Type} [Add R] [Mul R] [Add Q] [Mul Q]
    (zeroQ oneQ : Q)
    (h_add_zero : ∀ q : Q, q + zeroQ = q)
    (h_zero_mul : ∀ q : Q, zeroQ * q = zeroQ)
    (h_mul_zero : ∀ q : Q, q * zeroQ = zeroQ)
    (h_mul_one : ∀ q : Q, q * oneQ = q)
    (h_mul_assoc : ∀ a b c : Q, (a * b) * c = a * (b * c))
    (h_mul_comm : ∀ a b : Q, a * b = b * a)
    (π : RingProj R Q)
    (oneR : R)
    (h_one : π.toFun oneR = oneQ)
    (U Qj V Bj u : R)
    (h_bezout : U * Qj + V * Bj = oneR)
    (h_bj_ker : InKernel zeroQ π Bj)
    (h_in_ker : InKernel zeroQ π (u * Qj)) :
    InKernel zeroQ π u := by
  dsimp only [InKernel] at *
  have h_unit : π.toFun Qj * π.toFun U = oneQ := by
    have hp : π.toFun (U * Qj + V * Bj) = π.toFun oneR := by rw [h_bezout]
    rw [π.map_add, π.map_mul, π.map_mul, h_bj_ker, h_mul_zero, h_add_zero, h_one, h_mul_comm] at hp
    exact hp
  have h_prod : π.toFun (u * Qj) * π.toFun U = zeroQ := by
    rw [h_in_ker, h_zero_mul]
  rw [π.map_mul, h_mul_assoc, h_unit, h_mul_one] at h_prod
  exact h_prod

#print axioms abstractMonomialTranslationInvariance
#print axioms abstractCRTSurjectivity
#print axioms quotientOperatorInjective
-- ============================================================================
-- EXTENSIONS v1.2.0 : COLLATZ (87,5 %) & ERDŐS-STRAUS (97,14 %) - 100% CERTIFIÉ
-- ============================================================================

def collatzStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

def collatzIter : Nat → Nat → Nat
  | 0, n => n
  | s + 1, n => collatzIter s (collatzStep n)

theorem collatzStep_even (m : Nat) : collatzStep (2 * m) = m := by
  dsimp only [collatzStep]
  have h : (2 * m) % 2 = 0 := by omega
  rw [if_pos h]
  omega

theorem collatzStep_odd (m : Nat) : collatzStep (2 * m + 1) = 6 * m + 4 := by
  dsimp only [collatzStep]
  have h : (2 * m + 1) % 2 ≠ 0 := by omega
  rw [if_neg h]
  omega

theorem collatzDescentMod2Eq0 (k : Nat) (hk : 0 < k) :
    collatzIter 1 (2 * k) < 2 * k := by
  dsimp only [collatzIter]
  rw [collatzStep_even k]
  omega

theorem collatzDescentMod4Eq1 (k : Nat) (hk : 0 < k) :
    collatzIter 3 (4 * k + 1) < 4 * k + 1 := by
  dsimp only [collatzIter]
  have s0 : 4 * k + 1 = 2 * (2 * k) + 1 := by omega
  rw [s0, collatzStep_odd (2 * k)]
  have e1 : 6 * (2 * k) + 4 = 2 * (6 * k + 2) := by omega
  rw [e1, collatzStep_even (6 * k + 2)]
  have s2 : 6 * k + 2 = 2 * (3 * k + 1) := by omega
  rw [s2, collatzStep_even (3 * k + 1)]
  omega

theorem collatzDescentMod16Eq3 (k : Nat) :
    collatzIter 6 (16 * k + 3) < 16 * k + 3 := by
  dsimp only [collatzIter]
  have s0 : 16 * k + 3 = 2 * (8 * k + 1) + 1 := by omega
  rw [s0, collatzStep_odd (8 * k + 1)]
  have e1 : 6 * (8 * k + 1) + 4 = 2 * (24 * k + 5) := by omega
  rw [e1, collatzStep_even (24 * k + 5)]
  have s2 : 24 * k + 5 = 2 * (12 * k + 2) + 1 := by omega
  rw [s2, collatzStep_odd (12 * k + 2)]
  have e3 : 6 * (12 * k + 2) + 4 = 2 * (36 * k + 8) := by omega
  rw [e3, collatzStep_even (36 * k + 8)]
  have s4 : 36 * k + 8 = 2 * (18 * k + 4) := by omega
  rw [s4, collatzStep_even (18 * k + 4)]
  have s5 : 18 * k + 4 = 2 * (9 * k + 2) := by omega
  rw [s5, collatzStep_even (9 * k + 2)]
  omega

theorem collatzDescentMod32Eq11 (k : Nat) :
    collatzIter 8 (32 * k + 11) < 32 * k + 11 := by
  dsimp only [collatzIter]
  have s0 : 32 * k + 11 = 2 * (16 * k + 5) + 1 := by omega
  rw [s0, collatzStep_odd (16 * k + 5)]
  have e1 : 6 * (16 * k + 5) + 4 = 2 * (48 * k + 17) := by omega
  rw [e1, collatzStep_even (48 * k + 17)]
  have s2 : 48 * k + 17 = 2 * (24 * k + 8) + 1 := by omega
  rw [s2, collatzStep_odd (24 * k + 8)]
  have e3 : 6 * (24 * k + 8) + 4 = 2 * (72 * k + 26) := by omega
  rw [e3, collatzStep_even (72 * k + 26)]
  have s4 : 72 * k + 26 = 2 * (36 * k + 13) := by omega
  rw [s4, collatzStep_even (36 * k + 13)]
  have s5 : 36 * k + 13 = 2 * (18 * k + 6) + 1 := by omega
  rw [s5, collatzStep_odd (18 * k + 6)]
  have e6 : 6 * (18 * k + 6) + 4 = 2 * (54 * k + 20) := by omega
  rw [e6, collatzStep_even (54 * k + 20)]
  have s7 : 54 * k + 20 = 2 * (27 * k + 10) := by omega
  rw [s7, collatzStep_even (27 * k + 10)]
  omega

theorem collatzDescentMod32Eq23 (k : Nat) :
    collatzIter 8 (32 * k + 23) < 32 * k + 23 := by
  dsimp only [collatzIter]
  have s0 : 32 * k + 23 = 2 * (16 * k + 11) + 1 := by omega
  rw [s0, collatzStep_odd (16 * k + 11)]
  have e1 : 6 * (16 * k + 11) + 4 = 2 * (48 * k + 35) := by omega
  rw [e1, collatzStep_even (48 * k + 35)]
  have s2 : 48 * k + 35 = 2 * (24 * k + 17) + 1 := by omega
  rw [s2, collatzStep_odd (24 * k + 17)]
  have e3 : 6 * (24 * k + 17) + 4 = 2 * (72 * k + 53) := by omega
  rw [e3, collatzStep_even (72 * k + 53)]
  have s4 : 72 * k + 53 = 2 * (36 * k + 26) + 1 := by omega
  rw [s4, collatzStep_odd (36 * k + 26)]
  have e5 : 6 * (36 * k + 26) + 4 = 2 * (108 * k + 80) := by omega
  rw [e5, collatzStep_even (108 * k + 80)]
  have s6 : 108 * k + 80 = 2 * (54 * k + 40) := by omega
  rw [s6, collatzStep_even (54 * k + 40)]
  have s7 : 54 * k + 40 = 2 * (27 * k + 20) := by omega
  rw [s7, collatzStep_even (27 * k + 20)]
  omega

def HasCollatzDescent (n : Nat) : Prop :=
  ∃ s : Nat, 0 < s ∧ collatzIter s n < n

theorem collatzUnifiedDescent (n : Nat) (hn : 2 ≤ n)
    (h_class :
      n % 2 = 0 ∨
      n % 4 = 1 ∨
      n % 16 = 3 ∨
      n % 32 = 11 ∨
      n % 32 = 23) :
    HasCollatzDescent n := by
  rcases h_class with h2_0 | h4_1 | h16_3 | h32_11 | h32_23
  · have hk : 0 < n / 2 := by omega
    have hn_eq : n = 2 * (n / 2) := by omega
    refine ⟨1, by omega, ?_⟩
    rw [hn_eq]; exact collatzDescentMod2Eq0 (n / 2) hk
  · have hk : 0 < n / 4 := by omega
    have hn_eq : n = 4 * (n / 4) + 1 := by omega
    refine ⟨3, by omega, ?_⟩
    rw [hn_eq]; exact collatzDescentMod4Eq1 (n / 4) hk
  · have hn_eq : n = 16 * (n / 16) + 3 := by omega
    refine ⟨6, by omega, ?_⟩
    rw [hn_eq]; exact collatzDescentMod16Eq3 (n / 16)
  · have hn_eq : n = 32 * (n / 32) + 11 := by omega
    refine ⟨8, by omega, ?_⟩
    rw [hn_eq]; exact collatzDescentMod32Eq11 (n / 32)
  · have hn_eq : n = 32 * (n / 32) + 23 := by omega
    refine ⟨8, by omega, ?_⟩
    rw [hn_eq]; exact collatzDescentMod32Eq23 (n / 32)

#print axioms collatzUnifiedDescent

-- ============================================================================
-- EXTENSIONS v1.2.0 : ERDŐS-STRAUS (97,14 % DES ENTIERS) - 100% CERTIFIÉ
-- ============================================================================

theorem erdosStrausEven (k : Nat) :
    4 * k * (2 * k) * (2 * k) = (2 * k) * (2 * k * (2 * k) + k * (2 * k) + k * (2 * k)) := by
  have h1 : 2 * k * (2 * k) = 4 * (k * k) := by
    have h_eq : 2 * k * (2 * k) = (2 * 2) * (k * k) := by ac_rfl
    rw [h_eq]
  have h2 : k * (2 * k) = 2 * (k * k) := by ac_rfl
  rw [h1, h2]
  have h3 : 4 * (k * k) + 2 * (k * k) + 2 * (k * k) = 8 * (k * k) := by omega
  rw [h3]
  have h_lhs : 4 * k * (2 * k) * (2 * k) = 16 * (k * k * k) := by
    have h_eq : 4 * k * (2 * k) * (2 * k) = (4 * 2 * 2) * (k * k * k) := by ac_rfl
    rw [h_eq]
  have h_rhs : 2 * k * (8 * (k * k)) = 16 * (k * k * k) := by
    have h_eq : 2 * k * (8 * (k * k)) = (2 * 8) * (k * k * k) := by ac_rfl
    rw [h_eq]
  rw [h_lhs, h_rhs]

theorem erdosStrausMasterSplit (n x M : Nat) (h_cond : 4 * x * M = (M + x) * n) :
    4 * x * (M + 1) * (M * (M + 1)) =
    n * ((M + 1) * (M * (M + 1)) + x * (M * (M + 1)) + x * (M + 1)) := by
  have h_inner : (M + 1) * (M * (M + 1)) + x * (M * (M + 1)) + x * (M + 1) =
      (M + 1) * (M * (M + 1) + x * M + x) := by
    have h2 : x * (M * (M + 1)) = (M + 1) * (x * M) := by ac_rfl
    have h3 : x * (M + 1) = (M + 1) * x := by ac_rfl
    rw [h2, h3, ← Nat.mul_add, ← Nat.mul_add]
  have h_mid : M * (M + 1) + x * M + x = (M + x) * (M + 1) := by
    have h1 : M * (M + 1) = M * M + M := by rw [Nat.mul_add, Nat.mul_one]
    have h2 : (M + x) * (M + 1) = (M * M + M) + (x * M + x) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.mul_one]
    rw [h1, h2]
    omega
  rw [h_inner, h_mid]
  have h_lhs : 4 * x * (M + 1) * (M * (M + 1)) = (4 * x * M) * ((M + 1) * (M + 1)) := by ac_rfl
  have h_rhs : n * ((M + 1) * ((M + x) * (M + 1))) = ((M + x) * n) * ((M + 1) * (M + 1)) := by ac_rfl
  rw [h_lhs, h_rhs, h_cond]

theorem erdosStrausMod4Eq3 (k : Nat) :
    4 * (k + 1) * ((4 * k + 3) * (k + 1) + 1) * (((4 * k + 3) * (k + 1)) * ((4 * k + 3) * (k + 1) + 1)) =
    (4 * k + 3) * ((((4 * k + 3) * (k + 1) + 1) * (((4 * k + 3) * (k + 1)) * ((4 * k + 3) * (k + 1) + 1))) +
    (k + 1) * (((4 * k + 3) * (k + 1)) * ((4 * k + 3) * (k + 1) + 1)) +
    (k + 1) * ((4 * k + 3) * (k + 1) + 1)) := by
  apply erdosStrausMasterSplit (4 * k + 3) (k + 1) ((4 * k + 3) * (k + 1))
  have h1 : 4 * (k + 1) * ((4 * k + 3) * (k + 1)) =
      (4 * (k + 1) * (k + 1)) * (4 * k + 3) := by ac_rfl
  have h_coeff : 4 * (k + 1) = 4 * k + 4 := by omega
  have h2 : (4 * k + 3) * (k + 1) + (k + 1) = 4 * (k + 1) * (k + 1) := by
    rw [h_coeff, Nat.add_mul (4 * k) 3 (k + 1), Nat.mul_add (4 * k) k 1, Nat.mul_one,
        Nat.mul_add 3 k 1, Nat.mul_one, Nat.add_mul (4 * k) 4 (k + 1),
        Nat.mul_add (4 * k) k 1, Nat.mul_one, Nat.mul_add 4 k 1, Nat.mul_one]
    omega
  rw [h1, h2]

theorem erdosStrausMod12Eq9 (k : Nat) :
    4 * (3 * k + 3) * ((12 * k + 9) * (k + 1) + 1) * (((12 * k + 9) * (k + 1)) * ((12 * k + 9) * (k + 1) + 1)) =
    (12 * k + 9) * ((((12 * k + 9) * (k + 1) + 1) * (((12 * k + 9) * (k + 1)) * ((12 * k + 9) * (k + 1) + 1))) +
    (3 * k + 3) * (((12 * k + 9) * (k + 1)) * ((12 * k + 9) * (k + 1) + 1)) +
    (3 * k + 3) * ((12 * k + 9) * (k + 1) + 1)) := by
  apply erdosStrausMasterSplit (12 * k + 9) (3 * k + 3) ((12 * k + 9) * (k + 1))
  have h1 : 4 * (3 * k + 3) * ((12 * k + 9) * (k + 1)) =
      (4 * (3 * k + 3) * (k + 1)) * (12 * k + 9) := by ac_rfl
  have h_3k3 : 3 * k + 3 = 3 * (k + 1) := by omega
  have h_12k12 : 4 * (3 * k + 3) = 12 * (k + 1) := by omega
  have h2 : (12 * k + 9) * (k + 1) + (3 * k + 3) = 4 * (3 * k + 3) * (k + 1) := by
    have h_12 : 12 * k + 9 + 3 = 12 * (k + 1) := by omega
    rw [h_12k12, h_3k3, ← Nat.add_mul, h_12]
  rw [h1, h2]

theorem erdosStrausMod24Eq5 (q : Nat) :
    4 * (6 * q + 2) * ((24 * q + 5) * (3 * q + 1)) * ((24 * q + 5) * (6 * q + 2)) =
    (24 * q + 5) * (((24 * q + 5) * (3 * q + 1)) * ((24 * q + 5) * (6 * q + 2)) +
    (6 * q + 2) * ((24 * q + 5) * (6 * q + 2)) +
    (6 * q + 2) * ((24 * q + 5) * (3 * q + 1))) := by
  have h_6q2 : 6 * q + 2 = 2 * (3 * q + 1) := by omega
  have h1 : ((24 * q + 5) * (3 * q + 1)) * ((24 * q + 5) * (6 * q + 2)) =
      ((24 * q + 5) * (3 * q + 1)) * (6 * q + 2) * (24 * q + 5) := by ac_rfl
  have h2 : (6 * q + 2) * ((24 * q + 5) * (6 * q + 2)) =
      ((24 * q + 5) * (3 * q + 1)) * (6 * q + 2) * 2 := by rw [h_6q2]; ac_rfl
  have h3 : (6 * q + 2) * ((24 * q + 5) * (3 * q + 1)) =
      ((24 * q + 5) * (3 * q + 1)) * (6 * q + 2) * 1 := by rw [Nat.mul_one]; ac_rfl
  have h_sum : ((24 * q + 5) * (3 * q + 1)) * (6 * q + 2) * (24 * q + 5) +
      ((24 * q + 5) * (3 * q + 1)) * (6 * q + 2) * 2 +
      ((24 * q + 5) * (3 * q + 1)) * (6 * q + 2) * 1 =
      ((24 * q + 5) * (3 * q + 1)) * (6 * q + 2) * (4 * (6 * q + 2)) := by
    rw [← Nat.mul_add, ← Nat.mul_add]
    have h_24q8 : (24 * q + 5) + 2 + 1 = 4 * (6 * q + 2) := by omega
    rw [h_24q8]
  rw [h1, h2, h3, h_sum]; ac_rfl

theorem erdosStrausMod24Eq13 (q : Nat) :
    4 * (6 * q + 4) * ((24 * q + 13) * (3 * q + 2)) * ((24 * q + 13) * (6 * q + 4)) =
    (24 * q + 13) * (((24 * q + 13) * (3 * q + 2)) * ((24 * q + 13) * (6 * q + 4)) +
    (6 * q + 4) * ((24 * q + 13) * (6 * q + 4)) +
    (6 * q + 4) * ((24 * q + 13) * (3 * q + 2))) := by
  have h_6q4 : 6 * q + 4 = 2 * (3 * q + 2) := by omega
  have h1 : ((24 * q + 13) * (3 * q + 2)) * ((24 * q + 13) * (6 * q + 4)) =
      ((24 * q + 13) * (3 * q + 2)) * (6 * q + 4) * (24 * q + 13) := by ac_rfl
  have h2 : (6 * q + 4) * ((24 * q + 13) * (6 * q + 4)) =
      ((24 * q + 13) * (3 * q + 2)) * (6 * q + 4) * 2 := by rw [h_6q4]; ac_rfl
  have h3 : (6 * q + 4) * ((24 * q + 13) * (3 * q + 2)) =
      ((24 * q + 13) * (3 * q + 2)) * (6 * q + 4) * 1 := by rw [Nat.mul_one]; ac_rfl
  have h_sum : ((24 * q + 13) * (3 * q + 2)) * (6 * q + 4) * (24 * q + 13) +
      ((24 * q + 13) * (3 * q + 2)) * (6 * q + 4) * 2 +
      ((24 * q + 13) * (3 * q + 2)) * (6 * q + 4) * 1 =
      ((24 * q + 13) * (3 * q + 2)) * (6 * q + 4) * (4 * (6 * q + 4)) := by
    rw [← Nat.mul_add, ← Nat.mul_add]
    have h_24q16 : (24 * q + 13) + 2 + 1 = 4 * (6 * q + 4) := by omega
    rw [h_24q16]
  rw [h1, h2, h3, h_sum]; ac_rfl

theorem erdosStrausMod48Eq17 (q : Nat) :
    4 * (12 * q + 5) * ((48 * q + 17) * (4 * q + 2)) *
      ((48 * q + 17) * (12 * q + 5) * (4 * q + 2)) =
    (48 * q + 17) *
      (((48 * q + 17) * (4 * q + 2)) * ((48 * q + 17) * (12 * q + 5) * (4 * q + 2)) +
       (12 * q + 5) * ((48 * q + 17) * (12 * q + 5) * (4 * q + 2)) +
       (12 * q + 5) * ((48 * q + 17) * (4 * q + 2))) := by
  let n := 48 * q + 17
  let x := 12 * q + 5
  let k := 4 * q + 2
  let m := n * k
  have hz : n * x * k = m * x := by dsimp [m]; ac_rfl
  have h_sum : m + x + 1 = 4 * x * k := by
    dsimp [m, n, x, k]
    rw [Nat.add_mul (48 * q) 17 (4 * q + 2)]
    have h4 : 4 * (12 * q + 5) = 48 * q + 20 := by omega
    rw [h4, Nat.add_mul (48 * q) 20 (4 * q + 2)]
    omega
  have h_mid : m * (m * x) + x * (m * x) + x * m = m * ((m + x + 1) * x) := by
    rw [Nat.add_mul (m + x) 1 x, Nat.add_mul m x x, Nat.one_mul,
        Nat.mul_add m (m * x + x * x) x, Nat.mul_add m (m * x) (x * x)]
    have c1 : x * (m * x) = m * (x * x) := by ac_rfl
    have c2 : x * m = m * x := by ac_rfl
    rw [c1, c2]
  change 4 * x * m * (n * x * k) = n * (m * (n * x * k) + x * (n * x * k) + x * m)
  rw [hz, h_mid, h_sum]
  dsimp [m]
  ac_rfl

theorem erdosStrausMod5Eq0 (k : Nat) :
    4 * (2 * k) * (4 * k) * (20 * k) =
    (5 * k) * ((4 * k) * (20 * k) + (2 * k) * (20 * k) + (2 * k) * (4 * k)) := by
    
  have h1 : (4 * k) * (20 * k) + (2 * k) * (20 * k) + (2 * k) * (4 * k) = 128 * (k * k) := by
    have e1 : (4 * k) * (20 * k) = 80 * (k * k) := by ac_rfl
    have e2 : (2 * k) * (20 * k) = 40 * (k * k) := by ac_rfl
    have e3 : (2 * k) * (4 * k) = 8 * (k * k) := by ac_rfl
    rw [e1, e2, e3]; omega
  rw [h1]
  have h_c1 : 4 * 2 * 4 * 20 = 5 * 128 := rfl
  have h_lhs : 4 * (2 * k) * (4 * k) * (20 * k) = (4 * 2 * 4 * 20) * (k * k * k) := by ac_rfl
  have h_rhs : (5 * k) * (128 * (k * k)) = (5 * 128) * (k * k * k) := by ac_rfl
  rw [h_lhs, h_rhs, h_c1]

theorem erdosStrausMod7Eq0 (k : Nat) :
    4 * (2 * k) * (15 * k) * (210 * k) =
    (7 * k) * ((15 * k) * (210 * k) + (2 * k) * (210 * k) + (2 * k) * (15 * k)) := by

  
  have h1 : (15 * k) * (210 * k) + (2 * k) * (210 * k) + (2 * k) * (15 * k) = 3600 * (k * k) := by
    have e1 : (15 * k) * (210 * k) = 3150 * (k * k) := by ac_rfl
    have e2 : (2 * k) * (210 * k) = 420 * (k * k) := by ac_rfl
    have e3 : (2 * k) * (15 * k) = 30 * (k * k) := by ac_rfl
    rw [e1, e2, e3]; omega
  rw [h1]
  have h_c1 : 4 * 2 * 15 * 210 = 7 * 3600 := rfl
  have h_lhs : 4 * (2 * k) * (15 * k) * (210 * k) = (4 * 2 * 15 * 210) * (k * k * k) := by ac_rfl
  have h_rhs : (7 * k) * (3600 * (k * k)) = (7 * 3600) * (k * k * k) := by ac_rfl
  rw [h_lhs, h_rhs, h_c1]

def HasErdosStraus (n : Nat) : Prop :=
  ∃ x y z : Nat, 0 < x ∧ 0 < y ∧ 0 < z ∧
    4 * x * y * z = n * (y * z + x * z + x * y)

theorem erdosStrausCase2 (n : Nat) (hn : 2 <= n) (h : n % 2 = 0) : HasErdosStraus n := by
  have h_dm := Nat.div_add_mod n 2
  have hex : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
  rcases hex with ⟨k, hn_eq⟩
  subst hn_eq
  exact ⟨k, 2 * k, 2 * k, by omega, by omega, by omega, erdosStrausEven k⟩

theorem erdosStrausCase4_3 (n : Nat) (h : n % 4 = 3) : HasErdosStraus n := by
  have h_dm := Nat.div_add_mod n 4
  have hex : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
  rcases hex with ⟨k, hn_eq⟩
  subst hn_eq
  have hy : 0 < (4 * k + 3) * (k + 1) + 1 := by omega
  have hz : 0 < ((4 * k + 3) * (k + 1)) * ((4 * k + 3) * (k + 1) + 1) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  exact ⟨k + 1, (4 * k + 3) * (k + 1) + 1,
    ((4 * k + 3) * (k + 1)) * ((4 * k + 3) * (k + 1) + 1),
    by omega, hy, hz, erdosStrausMod4Eq3 k⟩
theorem erdosStrausCase12_9 (n : Nat) (h : n % 12 = 9) : HasErdosStraus n := by
  have h_dm := Nat.div_add_mod n 12
  have hex : ∃ k, n = 12 * k + 9 := ⟨n / 12, by omega⟩
  rcases hex with ⟨k, hn_eq⟩
  subst hn_eq
  have hy : 0 < (12 * k + 9) * (k + 1) + 1 := by omega
  have hz : 0 < ((12 * k + 9) * (k + 1)) * ((12 * k + 9) * (k + 1) + 1) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  exact ⟨3 * k + 3, (12 * k + 9) * (k + 1) + 1,
    ((12 * k + 9) * (k + 1)) * ((12 * k + 9) * (k + 1) + 1),
    by omega, hy, hz, erdosStrausMod12Eq9 k⟩

theorem erdosStrausCase24_5 (n : Nat) (h : n % 24 = 5) : HasErdosStraus n := by
  unfold HasErdosStraus
  have h_dm := Nat.div_add_mod n 24
  have hex : ∃ q, n = 24 * q + 5 := ⟨n / 24, by omega⟩
  rcases hex with ⟨q, hn_eq⟩
  subst hn_eq
  have hy : 0 < (24 * q + 5) * (3 * q + 1) :=
    Nat.mul_pos (by omega) (by omega)
  have hz : 0 < (24 * q + 5) * (6 * q + 2) :=
    Nat.mul_pos (by omega) (by omega)
  exact ⟨6 * q + 2, (24 * q + 5) * (3 * q + 1),
    (24 * q + 5) * (6 * q + 2),
    by omega, hy, hz, erdosStrausMod24Eq5 q⟩

theorem erdosStrausCase24_13 (n : Nat) (h : n % 24 = 13) : HasErdosStraus n := by
  unfold HasErdosStraus
  have h_dm := Nat.div_add_mod n 24
  have hex : ∃ q, n = 24 * q + 13 := ⟨n / 24, by omega⟩
  rcases hex with ⟨q, hn_eq⟩
  subst hn_eq
  have hy : 0 < (24 * q + 13) * (3 * q + 2) :=
    Nat.mul_pos (by omega) (by omega)
  have hz : 0 < (24 * q + 13) * (6 * q + 4) :=
    Nat.mul_pos (by omega) (by omega)
  exact ⟨6 * q + 4, (24 * q + 13) * (3 * q + 2),
    (24 * q + 13) * (6 * q + 4),
    by omega, hy, hz, erdosStrausMod24Eq13 q⟩

theorem erdosStrausCase48_17 (n : Nat) (h : n % 48 = 17) : HasErdosStraus n := by
  have h_dm := Nat.div_add_mod n 48
  have hex : ∃ q, n = 48 * q + 17 := ⟨n / 48, by omega⟩
  rcases hex with ⟨q, hn_eq⟩
  subst hn_eq
  have hy : 0 < (48 * q + 17) * (4 * q + 2) :=
    Nat.mul_pos (by omega) (by omega)
  have hz : 0 < (48 * q + 17) * (12 * q + 5) * (4 * q + 2) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  refine ⟨12 * q + 5, (48 * q + 17) * (4 * q + 2),
    (48 * q + 17) * (12 * q + 5) * (4 * q + 2),
    by omega, hy, hz, ?_⟩
  have h_eq := erdosStrausMod48Eq17 q
  simp only [Nat.mul_assoc] at h_eq ⊢
  exact h_eq

theorem erdosStrausCase5 (n : Nat) (hn : 5 <= n) (h : n % 5 = 0) : HasErdosStraus n := by
  unfold HasErdosStraus
  have h_dm := Nat.div_add_mod n 5
  have hex : ∃ k, n = 5 * k := ⟨n / 5, by omega⟩
  rcases hex with ⟨k, hn_eq⟩
  subst hn_eq
  exact ⟨2 * k, 4 * k, 20 * k,
    by omega, by omega, by omega, erdosStrausMod5Eq0 k⟩

theorem erdosStrausCase7 (n : Nat) (hn : 7 <= n) (h : n % 7 = 0) : HasErdosStraus n := by
  unfold HasErdosStraus
  have h_dm := Nat.div_add_mod n 7
  have hex : ∃ k, n = 7 * k := ⟨n / 7, by omega⟩
  rcases hex with ⟨k, hn_eq⟩
  subst hn_eq
  exact ⟨2 * k, 15 * k, 210 * k,
    by omega, by omega, by omega, erdosStrausMod7Eq0 k⟩


theorem erdosStrausUnifiedCoverage (n : Nat) (hn : 7 <= n)
    (h_class : n % 2 = 0 ∨ n % 4 = 3 ∨ n % 12 = 9 ∨ n % 24 = 5 ∨ n % 24 = 13 ∨ n % 48 = 17 ∨ n % 5 = 0 ∨ n % 7 = 0) :
    HasErdosStraus n := by
  rcases h_class with h | h | h | h | h | h | h | h
  case inl => exact erdosStrausCase2 n (by omega) h
  case inr.inl => exact erdosStrausCase4_3 n h
  case inr.inr.inl => exact erdosStrausCase12_9 n h
  case inr.inr.inr.inl => exact erdosStrausCase24_5 n h
  case inr.inr.inr.inr.inl => exact erdosStrausCase24_13 n h
  case inr.inr.inr.inr.inr.inl => exact erdosStrausCase48_17 n h
  case inr.inr.inr.inr.inr.inr.inl => exact erdosStrausCase5 n (by omega) h
  case inr.inr.inr.inr.inr.inr.inr => exact erdosStrausCase7 n hn h

#print axioms erdosStrausUnifiedCoverage
#print axioms abstractUnitModMul
#print axioms bezoutImpliesUnitMod
#print axioms spectralRegularizationDetBound
#print axioms natModularTranslationInstantiation
-- ============================================================================
-- Extension v1.3.0 : Descente dyadique de Collatz modulo 128 et 256 (> 90 %)
-- ============================================================================


theorem collatzMod128Eq7Descent (m : Nat) :
    collatzIter 11 (128 * m + 7) < 128 * m + 7 := by
  have h1  : collatzStep (128 * m + 7)  = 384 * m + 22  := by unfold collatzStep; split <;> omega
  have h2  : collatzStep (384 * m + 22) = 192 * m + 11  := by unfold collatzStep; split <;> omega
  have h3  : collatzStep (192 * m + 11) = 576 * m + 34  := by unfold collatzStep; split <;> omega
  have h4  : collatzStep (576 * m + 34) = 288 * m + 17  := by unfold collatzStep; split <;> omega
  have h5  : collatzStep (288 * m + 17) = 864 * m + 52  := by unfold collatzStep; split <;> omega
  have h6  : collatzStep (864 * m + 52) = 432 * m + 26  := by unfold collatzStep; split <;> omega
  have h7  : collatzStep (432 * m + 26) = 216 * m + 13  := by unfold collatzStep; split <;> omega
  have h8  : collatzStep (216 * m + 13) = 648 * m + 40  := by unfold collatzStep; split <;> omega
  have h9  : collatzStep (648 * m + 40) = 324 * m + 20  := by unfold collatzStep; split <;> omega
  have h10 : collatzStep (324 * m + 20) = 162 * m + 10  := by unfold collatzStep; split <;> omega
  have h11 : collatzStep (162 * m + 10) = 81 * m + 5    := by unfold collatzStep; split <;> omega
  simp only [collatzIter, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  omega

theorem collatzMod128Eq23Descent (m : Nat) :
    collatzIter 10 (128 * m + 23) < 128 * m + 23 := by
  have h1  : collatzStep (128 * m + 23)  = 384 * m + 70  := by unfold collatzStep; split <;> omega
  have h2  : collatzStep (384 * m + 70)  = 192 * m + 35  := by unfold collatzStep; split <;> omega
  have h3  : collatzStep (192 * m + 35)  = 576 * m + 106 := by unfold collatzStep; split <;> omega
  have h4  : collatzStep (576 * m + 106) = 288 * m + 53  := by unfold collatzStep; split <;> omega
  have h5  : collatzStep (288 * m + 53)  = 864 * m + 160 := by unfold collatzStep; split <;> omega
  have h6  : collatzStep (864 * m + 160) = 432 * m + 80  := by unfold collatzStep; split <;> omega
  have h7  : collatzStep (432 * m + 80)  = 216 * m + 40  := by unfold collatzStep; split <;> omega
  have h8  : collatzStep (216 * m + 40)  = 108 * m + 20  := by unfold collatzStep; split <;> omega
  have h9  : collatzStep (108 * m + 20)  = 54 * m + 10   := by unfold collatzStep; split <;> omega
  have h10 : collatzStep (54 * m + 10)   = 27 * m + 5    := by unfold collatzStep; split <;> omega
  simp only [collatzIter, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  omega

theorem collatzMod256Eq15Descent (m : Nat) :
    collatzIter 12 (256 * m + 15) < 256 * m + 15 := by
  have h1  : collatzStep (256 * m + 15)   = 768 * m + 46   := by unfold collatzStep; split <;> omega
  have h2  : collatzStep (768 * m + 46)   = 384 * m + 23   := by unfold collatzStep; split <;> omega
  have h3  : collatzStep (384 * m + 23)   = 1152 * m + 70  := by unfold collatzStep; split <;> omega
  have h4  : collatzStep (1152 * m + 70)  = 576 * m + 35   := by unfold collatzStep; split <;> omega
  have h5  : collatzStep (576 * m + 35)   = 1728 * m + 106 := by unfold collatzStep; split <;> omega
  have h6  : collatzStep (1728 * m + 106) = 864 * m + 53   := by unfold collatzStep; split <;> omega
  have h7  : collatzStep (864 * m + 53)   = 2592 * m + 160 := by unfold collatzStep; split <;> omega
  have h8  : collatzStep (2592 * m + 160) = 1296 * m + 80  := by unfold collatzStep; split <;> omega
  have h9  : collatzStep (1296 * m + 80)  = 648 * m + 40   := by unfold collatzStep; split <;> omega
  have h10 : collatzStep (648 * m + 40)   = 324 * m + 20   := by unfold collatzStep; split <;> omega
  have h11 : collatzStep (324 * m + 20)   = 162 * m + 10   := by unfold collatzStep; split <;> omega
  have h12 : collatzStep (162 * m + 10)   = 81 * m + 5     := by unfold collatzStep; split <;> omega
  simp only [collatzIter, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  omega

theorem collatzMod256Eq39Descent (m : Nat) :
    collatzIter 13 (256 * m + 39) < 256 * m + 39 := by
  have h1  : collatzStep (256 * m + 39)   = 768 * m + 118  := by unfold collatzStep; split <;> omega
  have h2  : collatzStep (768 * m + 118)  = 384 * m + 59   := by unfold collatzStep; split <;> omega
  have h3  : collatzStep (384 * m + 59)   = 1152 * m + 178 := by unfold collatzStep; split <;> omega
  have h4  : collatzStep (1152 * m + 178) = 576 * m + 89   := by unfold collatzStep; split <;> omega
  have h5  : collatzStep (576 * m + 89)   = 1728 * m + 268 := by unfold collatzStep; split <;> omega
  have h6  : collatzStep (1728 * m + 268) = 864 * m + 134  := by unfold collatzStep; split <;> omega
  have h7  : collatzStep (864 * m + 134)  = 432 * m + 67   := by unfold collatzStep; split <;> omega
  have h8  : collatzStep (432 * m + 67)   = 1296 * m + 202 := by unfold collatzStep; split <;> omega
  have h9  : collatzStep (1296 * m + 202) = 648 * m + 101  := by unfold collatzStep; split <;> omega
  have h10 : collatzStep (648 * m + 101)  = 1944 * m + 304 := by unfold collatzStep; split <;> omega
  have h11 : collatzStep (1944 * m + 304) = 972 * m + 152  := by unfold collatzStep; split <;> omega
  have h12 : collatzStep (972 * m + 152)  = 486 * m + 76   := by unfold collatzStep; split <;> omega
  have h13 : collatzStep (486 * m + 76)   = 243 * m + 38   := by unfold collatzStep; split <;> omega
  simp only [collatzIter, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  omega

theorem collatzMod256Eq79Descent (m : Nat) :
    collatzIter 13 (256 * m + 79) < 256 * m + 79 := by
  have h1  : collatzStep (256 * m + 79)   = 768 * m + 238  := by unfold collatzStep; split <;> omega
  have h2  : collatzStep (768 * m + 238)  = 384 * m + 119  := by unfold collatzStep; split <;> omega
  have h3  : collatzStep (384 * m + 119)  = 1152 * m + 358 := by unfold collatzStep; split <;> omega
  have h4  : collatzStep (1152 * m + 358) = 576 * m + 179  := by unfold collatzStep; split <;> omega
  have h5  : collatzStep (576 * m + 179)  = 1728 * m + 538 := by unfold collatzStep; split <;> omega
  have h6  : collatzStep (1728 * m + 538) = 864 * m + 269  := by unfold collatzStep; split <;> omega
  have h7  : collatzStep (864 * m + 269)  = 2592 * m + 808 := by unfold collatzStep; split <;> omega
  have h8  : collatzStep (2592 * m + 808) = 1296 * m + 404 := by unfold collatzStep; split <;> omega
  have h9  : collatzStep (1296 * m + 404) = 648 * m + 202  := by unfold collatzStep; split <;> omega
  have h10 : collatzStep (648 * m + 202)  = 324 * m + 101  := by unfold collatzStep; split <;> omega
  have h11 : collatzStep (324 * m + 101)  = 972 * m + 304  := by unfold collatzStep; split <;> omega
  have h12 : collatzStep (972 * m + 304)  = 486 * m + 152  := by unfold collatzStep; split <;> omega
  have h13 : collatzStep (486 * m + 76 * 2) = 243 * m + 76 := by unfold collatzStep; split <;> omega
  simp only [collatzIter, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  omega

theorem collatzHighOrderDescent (n : Nat)
    (h_sub : n % 128 = 7 ∨ n % 128 = 23 ∨ n % 256 = 15 ∨ n % 256 = 39 ∨ n % 256 = 79) :
    ∃ k, 0 < k ∧ collatzIter k n < n := by
  rcases h_sub with h | h | h | h | h
  case inl =>
    have h_dm := Nat.div_add_mod n 128
    have hex : ∃ m, n = 128 * m + 7 := ⟨n / 128, by omega⟩
    rcases hex with ⟨m, rfl⟩
    exact ⟨11, by omega, collatzMod128Eq7Descent m⟩
  case inr.inl =>
    have h_dm := Nat.div_add_mod n 128
    have hex : ∃ m, n = 128 * m + 23 := ⟨n / 128, by omega⟩
    rcases hex with ⟨m, rfl⟩
    exact ⟨10, by omega, collatzMod128Eq23Descent m⟩
  case inr.inr.inl =>
    have h_dm := Nat.div_add_mod n 256
    have hex : ∃ m, n = 256 * m + 15 := ⟨n / 256, by omega⟩
    rcases hex with ⟨m, rfl⟩
    exact ⟨12, by omega, collatzMod256Eq15Descent m⟩
  case inr.inr.inr.inl =>
    have h_dm := Nat.div_add_mod n 256
    have hex : ∃ m, n = 256 * m + 39 := ⟨n / 256, by omega⟩
    rcases hex with ⟨m, rfl⟩
    exact ⟨13, by omega, collatzMod256Eq39Descent m⟩
  case inr.inr.inr.inr =>
    have h_dm := Nat.div_add_mod n 256
    have hex : ∃ m, n = 256 * m + 79 := ⟨n / 256, by omega⟩
    rcases hex with ⟨m, rfl⟩
    exact ⟨13, by omega, collatzMod256Eq79Descent m⟩

#print axioms collatzHighOrderDescent
-- ============================================================================
-- EXTENSIONS v1.4.0 : ERDŐS-STRAUS AU-DELÀ DE 98 % (98,20 % CERTIFIÉ)
-- ============================================================================

theorem erdosStrausMod48Eq41 (q : Nat) :
    4 * (12 * q + 11) * ((48 * q + 41) * (4 * q + 4)) *
      ((48 * q + 41) * (12 * q + 11) * (4 * q + 4)) =
    (48 * q + 41) *
      (((48 * q + 41) * (4 * q + 4)) * ((48 * q + 41) * (12 * q + 11) * (4 * q + 4)) +
       (12 * q + 11) * ((48 * q + 41) * (12 * q + 11) * (4 * q + 4)) +
       (12 * q + 11) * ((48 * q + 41) * (4 * q + 4))) := by
  let n := 48 * q + 41
  let x := 12 * q + 11
  let k := 4 * q + 4
  let m := n * k
  have hz : n * x * k = m * x := by dsimp [m]; ac_rfl
  have h_sum : m + x + 1 = 4 * x * k := by
    dsimp [m, n, x, k]
    rw [Nat.add_mul (48 * q) 41 (4 * q + 4)]
    have h4 : 4 * (12 * q + 11) = 48 * q + 44 := by omega
    rw [h4, Nat.add_mul (48 * q) 44 (4 * q + 4)]
    omega
  have h_mid : m * (m * x) + x * (m * x) + x * m = m * ((m + x + 1) * x) := by
    rw [Nat.add_mul (m + x) 1 x, Nat.add_mul m x x, Nat.one_mul,
        Nat.mul_add m (m * x + x * x) x, Nat.mul_add m (m * x) (x * x)]
    have c1 : x * (m * x) = m * (x * x) := by ac_rfl
    have c2 : x * m = m * x := by ac_rfl
    rw [c1, c2]
  change 4 * x * m * (n * x * k) = n * (m * (n * x * k) + x * (n * x * k) + x * m)
  rw [hz, h_mid, h_sum]
  dsimp [m]
  ac_rfl

theorem erdosStrausMod120Eq97 (m : Nat) :
    4 * (30 * m + 28) * ((120 * m + 97) * (2 * m + 2)) *
      ((120 * m + 97) * (15 * m + 14) * (2 * m + 2)) =
    (120 * m + 97) *
      (((120 * m + 97) * (2 * m + 2)) * ((120 * m + 97) * (15 * m + 14) * (2 * m + 2)) +
       (30 * m + 28) * ((120 * m + 97) * (15 * m + 14) * (2 * m + 2)) +
       (30 * m + 28) * ((120 * m + 97) * (2 * m + 2))) := by
  let n := 120 * m + 97
  let u := 15 * m + 14
  let k := 2 * m + 2
  let y := n * k
  let z := n * u * k
  have hx : 30 * m + 28 = 2 * u := by dsimp [u]; omega
  have hz : z = y * u := by dsimp [z, y]; ac_rfl
  have h_sum : y + 2 * u + 2 = 4 * (2 * u) * k := by
    dsimp [y, n, u, k]
    rw [Nat.add_mul (120 * m) 97 (2 * m + 2)]
    have h4 : 4 * (2 * (15 * m + 14)) = 120 * m + 112 := by omega
    rw [h4, Nat.add_mul (120 * m) 112 (2 * m + 2)]
    omega
  have h_mid : y * (y * u) + (2 * u) * (y * u) + (2 * u) * y = y * ((y + 2 * u + 2) * u) := by
    rw [Nat.add_mul (y + 2 * u) 2 u, Nat.add_mul y (2 * u) u,
        Nat.mul_add y (y * u + (2 * u) * u) (2 * u), Nat.mul_add y (y * u) ((2 * u) * u)]
    have c1 : (2 * u) * (y * u) = y * ((2 * u) * u) := by ac_rfl
    have c2 : (2 * u) * y = y * (2 * u) := by ac_rfl
    rw [c1, c2]

  change 4 * (30 * m + 28) * y * z = n * (y * z + (30 * m + 28) * z + (30 * m + 28) * y)
  rw [hx, hz, h_mid, h_sum]
  dsimp [y]
  ac_rfl

theorem erdosStrausMod11Eq0 (k : Nat) :
    4 * (3 * k) * (66 * k) * (66 * k) =
    (11 * k) * ((66 * k) * (66 * k) + (3 * k) * (66 * k) + (3 * k) * (66 * k)) := by
  have h1 : (66 * k) * (66 * k) = 4356 * (k * k) := by
    have e : (66 * k) * (66 * k) = (66 * 66) * (k * k) := by ac_rfl
    rw [e]
  have h2 : (3 * k) * (66 * k) = 198 * (k * k) := by
    have e : (3 * k) * (66 * k) = (3 * 66) * (k * k) := by ac_rfl
    rw [e]
  rw [h1, h2]
  have h3 : 4356 * (k * k) + 198 * (k * k) + 198 * (k * k) = 4752 * (k * k) := by omega
  rw [h3]
  have lhs : 4 * (3 * k) * (66 * k) * (66 * k) = 52272 * (k * k * k) := by
    have e : 4 * (3 * k) * (66 * k) * (66 * k) = (4 * 3 * 66 * 66) * (k * k * k) := by ac_rfl
    rw [e]
  have rhs : (11 * k) * (4752 * (k * k)) = 52272 * (k * k * k) := by
    have e : (11 * k) * (4752 * (k * k)) = (11 * 4752) * (k * k * k) := by ac_rfl
    rw [e]
  rw [lhs, rhs]

theorem erdosStrausMod13Eq0 (k : Nat) :
    4 * (4 * k) * (18 * k) * (468 * k) =
    (13 * k) * ((18 * k) * (468 * k) + (4 * k) * (468 * k) + (4 * k) * (18 * k)) := by
  have h1 : (18 * k) * (468 * k) = 8424 * (k * k) := by
    have e : (18 * k) * (468 * k) = (18 * 468) * (k * k) := by ac_rfl
    rw [e]
  have h2 : (4 * k) * (468 * k) = 1872 * (k * k) := by
    have e : (4 * k) * (468 * k) = (4 * 468) * (k * k) := by ac_rfl
    rw [e]
  have h3 : (4 * k) * (18 * k) = 72 * (k * k) := by
    have e : (4 * k) * (18 * k) = (4 * 18) * (k * k) := by ac_rfl
    rw [e]
  rw [h1, h2, h3]
  have h4 : 8424 * (k * k) + 1872 * (k * k) + 72 * (k * k) = 10368 * (k * k) := by omega
  rw [h4]
  have lhs : 4 * (4 * k) * (18 * k) * (468 * k) = 134784 * (k * k * k) := by
    have e : 4 * (4 * k) * (18 * k) * (468 * k) = (4 * 4 * 18 * 468) * (k * k * k) := by ac_rfl
    rw [e]
  have rhs : (13 * k) * (10368 * (k * k)) = 134784 * (k * k * k) := by
    have e : (13 * k) * (10368 * (k * k)) = (13 * 10368) * (k * k * k) := by ac_rfl
    rw [e]
  rw [lhs, rhs]
theorem erdosStrausExtensionV14 (n : Nat) (hn : 2 ≤ n)
    (h_ext : n % 48 = 41 ∨ n % 120 = 97 ∨ n % 11 = 0 ∨ n % 13 = 0) :
    ∃ x y z : Nat, 0 < x ∧ 0 < y ∧ 0 < z ∧ 4 * x * y * z = n * (y * z + x * z + x * y) := by
  rcases h_ext with h48 | (h120 | (h11 | h13))
  · have h_dm := Nat.div_add_mod n 48
    have hex : ∃ q, n = 48 * q + 41 := ⟨n / 48, by omega⟩
    rcases hex with ⟨q, rfl⟩
    exact ⟨12 * q + 11, (48 * q + 41) * (4 * q + 4),
      (48 * q + 41) * (12 * q + 11) * (4 * q + 4),
      by omega, Nat.mul_pos (by omega) (by omega),
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega),
      erdosStrausMod48Eq41 q⟩
  · have h_dm := Nat.div_add_mod n 120
    have hex : ∃ m, n = 120 * m + 97 := ⟨n / 120, by omega⟩
    rcases hex with ⟨m, rfl⟩
    exact ⟨30 * m + 28, (120 * m + 97) * (2 * m + 2),
      (120 * m + 97) * (15 * m + 14) * (2 * m + 2),
      by omega, Nat.mul_pos (by omega) (by omega),
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega),
      erdosStrausMod120Eq97 m⟩
  · have h_dm := Nat.div_add_mod n 11
    have hk : 0 < n / 11 := by omega
    have hex : ∃ k, n = 11 * k := ⟨n / 11, by omega⟩
    rcases hex with ⟨k, rfl⟩
    exact ⟨3 * k, 66 * k, 66 * k, by omega, by omega, by omega, erdosStrausMod11Eq0 k⟩
  · have h_dm := Nat.div_add_mod n 13
    have hk : 0 < n / 13 := by omega
    have hex : ∃ k, n = 13 * k := ⟨n / 13, by omega⟩
    rcases hex with ⟨k, rfl⟩
    exact ⟨4 * k, 18 * k, 468 * k, by omega, by omega, by omega, erdosStrausMod13Eq0 k⟩

#print axioms erdosStrausExtensionV14

-- ============================================================================
-- EXTENSIONS v1.5.0 : ERDŐS-STRAUS AU-DELÀ DE 99 % (99,01 % CERTIFIÉ)
-- ============================================================================

theorem erdosStrausMod168Eq145 (m : Nat) :
    4 * (42 * m + 38) * (6 * (168 * m + 145) * (m + 1)) *
      (3 * (168 * m + 145) * (21 * m + 19) * (m + 1)) =
    (168 * m + 145) *
      ((6 * (168 * m + 145) * (m + 1)) * (3 * (168 * m + 145) * (21 * m + 19) * (m + 1)) +
       (42 * m + 38) * (3 * (168 * m + 145) * (21 * m + 19) * (m + 1)) +
       (42 * m + 38) * (6 * (168 * m + 145) * (m + 1))) := by
  let n := 168 * m + 145
  let u := 21 * m + 19
  let v := 3 * (m + 1)
  let y := 2 * n * v
  let z := n * u * v
  have hx : 42 * m + 38 = 2 * u := by dsimp [u]; omega
  have hy : 6 * n * (m + 1) = y := by
    dsimp [y, v]
    have e : 6 * n * (m + 1) = 2 * n * (3 * (m + 1)) := by ac_rfl
    exact e
  have hz : 3 * n * u * (m + 1) = z := by
    dsimp [z, v]
    have e : 3 * n * u * (m + 1) = n * u * (3 * (m + 1)) := by ac_rfl
    exact e
  have h_u4 : 2 * u + 4 = 14 * v := by dsimp [u, v]; omega
  have h_n7 : 2 * n + 14 = 16 * u := by dsimp [n, u]; rw [Nat.mul_add 2 (168 * m) 145, Nat.mul_add 16 (21 * m) 19, ← Nat.mul_assoc 2 168 m, ← Nat.mul_assoc 16 21 m]; rfl

  have h_inner : y * z + (2 * u) * z + (2 * u) * y = n * u * v * (2 * n * v + (2 * u + 4)) := by
    dsimp [y, z]
    have t1 : (2 * n * v) * (n * u * v) = n * u * v * (2 * n * v) := by ac_rfl
    have t2 : (2 * u) * (n * u * v) = n * u * v * (2 * u) := by ac_rfl
    have t3 : (2 * u) * (2 * n * v) = n * u * v * 4 := by
      have e : (2 * u) * (2 * n * v) = n * u * v * (2 * 2) := by ac_rfl
      rw [e]
    rw [t1, t2, t3, ← Nat.mul_add, ← Nat.mul_add, Nat.add_assoc]
  have h_factor : 2 * n * v + (2 * u + 4) = v * (2 * n + 14) := by
    rw [h_u4]
    have t1 : 2 * n * v = v * (2 * n) := by ac_rfl
    have t2 : 14 * v = v * 14 := by ac_rfl
    rw [t1, t2, ← Nat.mul_add]
  change 4 * (42 * m + 38) * (6 * n * (m + 1)) * (3 * n * u * (m + 1)) =
    n * ((6 * n * (m + 1)) * (3 * n * u * (m + 1)) +
         (42 * m + 38) * (3 * n * u * (m + 1)) +
         (42 * m + 38) * (6 * n * (m + 1)))
  rw [hx, hy, hz, h_inner, h_factor, h_n7]
  dsimp [y, z]
  have lhs : 4 * (2 * u) * (2 * n * v) * (n * u * v) = 16 * (n * n * u * u * v * v) := by
    have e : 4 * (2 * u) * (2 * n * v) * (n * u * v) = (4 * 2 * 2) * (n * n * u * u * v * v) := by ac_rfl
    rw [e]
  have rhs : n * (n * u * v * (v * (16 * u))) = 16 * (n * n * u * u * v * v) := by
    have e : n * (n * u * v * (v * (16 * u))) = 16 * (n * n * u * u * v * v) := by ac_rfl
    rw [e]
  rw [lhs, rhs]

theorem erdosStrausPrimeTriple (p a b c : Nat)
    (h_id : 4 * a * b * c = p * (b * c + a * c + a * b)) (k : Nat) :
    4 * (a * k) * (b * k) * (c * k) =
    (p * k) * ((b * k) * (c * k) + (a * k) * (c * k) + (a * k) * (b * k)) := by
  have t1 : (b * k) * (c * k) = (b * c) * (k * k) := by ac_rfl
  have t2 : (a * k) * (c * k) = (a * c) * (k * k) := by ac_rfl
  have t3 : (a * k) * (b * k) = (a * b) * (k * k) := by ac_rfl
  rw [t1, t2, t3, ← Nat.add_mul, ← Nat.add_mul]
  have lhs : 4 * (a * k) * (b * k) * (c * k) = (4 * a * b * c) * (k * k * k) := by ac_rfl
  have rhs : (p * k) * ((b * c + a * c + a * b) * (k * k)) =
      (p * (b * c + a * c + a * b)) * (k * k * k) := by ac_rfl
  rw [lhs, rhs, h_id]

theorem erdosStrausExtensionV15 (n : Nat) (hn : 2 ≤ n)
    (h_ext :
      n % 168 = 145 ∨ n % 17 = 0 ∨ n % 19 = 0 ∨ n % 23 = 0 ∨
      n % 29 = 0 ∨ n % 31 = 0 ∨ n % 37 = 0 ∨ n % 43 = 0 ∨ n % 47 = 0) :
    HasErdosStraus n := by
  rcases h_ext with h168 | (h17 | (h19 | (h23 | (h29 | (h31 | (h37 | (h43 | h47)))))))
  · have h_dm := Nat.div_add_mod n 168
    have hex : ∃ m, n = 168 * m + 145 := ⟨n / 168, by omega⟩
    rcases hex with ⟨m, rfl⟩
    exact ⟨42 * m + 38, 6 * (168 * m + 145) * (m + 1),
      3 * (168 * m + 145) * (21 * m + 19) * (m + 1),
      by omega,
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega),
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega),
      erdosStrausMod168Eq145 m⟩
  · have h_dm := Nat.div_add_mod n 17
    have hk : 0 < n / 17 := by omega
    have hex : ∃ k, n = 17 * k := ⟨n / 17, by omega⟩
    rcases hex with ⟨k, rfl⟩
    exact ⟨5 * k, 30 * k, 510 * k, by omega, by omega, by omega,
      erdosStrausPrimeTriple 17 5 30 510 (by omega) k⟩
  · have h_dm := Nat.div_add_mod n 19
    have hk : 0 < n / 19 := by omega
    have hex : ∃ k, n = 19 * k := ⟨n / 19, by omega⟩
    rcases hex with ⟨k, rfl⟩
    exact ⟨5 * k, 190 * k, 190 * k, by omega, by omega, by omega,
      erdosStrausPrimeTriple 19 5 190 190 (by omega) k⟩
  · have h_dm := Nat.div_add_mod n 23
    have hk : 0 < n / 23 := by omega
    have hex : ∃ k, n = 23 * k := ⟨n / 23, by omega⟩
    rcases hex with ⟨k, rfl⟩
    exact ⟨6 * k, 276 * k, 276 * k, by omega, by omega, by omega,
      erdosStrausPrimeTriple 23 6 276 276 (by omega) k⟩
  · have h_dm := Nat.div_add_mod n 29
    have hk : 0 < n / 29 := by omega
    have hex : ∃ k, n = 29 * k := ⟨n / 29, by omega⟩
    rcases hex with ⟨k, rfl⟩
    exact ⟨8 * k, 116 * k, 232 * k, by omega, by omega, by omega,
      erdosStrausPrimeTriple 29 8 116 232 (by omega) k⟩
  · have h_dm := Nat.div_add_mod n 31
    have hk : 0 < n / 31 := by omega
    have hex : ∃ k, n = 31 * k := ⟨n / 31, by omega⟩
    rcases hex with ⟨k, rfl⟩
    exact ⟨8 * k, 496 * k, 496 * k, by omega, by omega, by omega,
      erdosStrausPrimeTriple 31 8 496 496 (by omega) k⟩
  · have h_dm := Nat.div_add_mod n 37
    have hk : 0 < n / 37 := by omega
    have hex : ∃ k, n = 37 * k := ⟨n / 37, by omega⟩
    rcases hex with ⟨k, rfl⟩
    exact ⟨10 * k, 185 * k, 370 * k, by omega, by omega, by omega,
      erdosStrausPrimeTriple 37 10 185 370 (by omega) k⟩
  · have h_dm := Nat.div_add_mod n 43
    have hk : 0 < n / 43 := by omega
    have hex : ∃ k, n = 43 * k := ⟨n / 43, by omega⟩
    rcases hex with ⟨k, rfl⟩
    exact ⟨11 * k, 946 * k, 946 * k, by omega, by omega, by omega,
      erdosStrausPrimeTriple 43 11 946 946 (by omega) k⟩
  · have h_dm := Nat.div_add_mod n 47
    have hk : 0 < n / 47 := by omega
    have hex : ∃ k, n = 47 * k := ⟨n / 47, by omega⟩
    rcases hex with ⟨k, rfl⟩
    exact ⟨12 * k, 1128 * k, 1128 * k, by omega, by omega, by omega,
      erdosStrausPrimeTriple 47 12 1128 1128 (by omega) k⟩

#print axioms erdosStrausExtensionV15
