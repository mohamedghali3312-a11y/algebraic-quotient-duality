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

-- 1. Invariance par translation idéale : x ∈ (R/I)^× et k ∈ I => x + k ∈ (R/I)^×
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

-- 2. Compatibilité projective sur la tour R → Q_s → Q_r
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

-- 3. Multiplicativité des éléments inversibles modulo I
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

-- 4. Dualité de Bézout : U * Q + V * B = 1 => Q mod (B) est inversible
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

-- 5. Minoration spectrale sur le cône symétrique : (λ1 + μ)(λ2 + μ) ≥ μ^2
theorem spectralRegularizationDetBound (lam1 lam2 mu : Nat) :
    mu * mu ≤ (lam1 + mu) * (lam2 + mu) := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  omega
