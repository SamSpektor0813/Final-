import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Int.GCD

open BigOperators

theorem chineseRemainder_k_equations
    {k : ℕ}
    (n : Fin k → ℕ)
    (h_coprime : ∀ i j : Fin k, i ≠ j → Nat.Coprime (n i) (n j))
    (a : Fin k → ℤ) :
  ∃ x : ℤ, ∀ i : Fin k, x ≡ a i [ZMOD (n i : ℤ)] := by
  let N : ℕ := ∏ i : Fin k, n i
  let Ni : Fin k → ℕ := fun i => N / n i
  let x : Fin k → ℤ := fun i => Int.gcdA (Ni i : ℤ) (n i : ℤ)

  let xans : ℤ := ∑ i : Fin k, a i * ↑(Ni i) * x i

  use xans
  intro i



  -- Key lemma: Ni j is divisible by n i when j ≠ i
  have h_Ni_div : ∀ j : Fin k, i ≠j → (n i : ℤ) ∣ (Ni j : ℤ) := by
    intro j hj
    -- n i divides N
    have h_i_div_N : n i ∣ N := by
      apply Finset.dvd_prod_of_mem
      exact Finset.mem_univ i
    -- n j divides N
    have h_j_div_N : n j ∣ N := by
      apply Finset.dvd_prod_of_mem
      exact Finset.mem_univ j
    -- n i and n j are coprime
    have h_coprime_ij : Nat.Coprime (n i) (n j) := h_coprime i j hj
    -- Prove n i | (n j * (N / n j)) = N
    have h_div_mul : n i ∣ n j * (N / n j) := by
      convert h_i_div_N using 1
      calc
        n j * (N / n j) = N / n j * n j := by ring
        _ = N := by apply (Nat.div_mul_cancel h_j_div_N)

    -- Therefore n i | (N / n j) by coprimality
    have h_nat_div : n i ∣ Ni j :=
      Nat.Coprime.dvd_of_dvd_mul_left h_coprime_ij h_div_mul
    exact Int.coe_nat_dvd.mpr h_nat_div


  -- Therefore Ni j ≡ 0 (mod n i) when j ≠ i
  have h_Ni_zero : ∀ j : Fin k, i ≠ j → (Ni j : ℤ) ≡ 0 [ZMOD n i] := by
    intro j hj
    exact Int.modEq_zero_iff_dvd.mpr (h_Ni_div j hj)

  -- And Ni i * x i ≡ 1 (mod n i) from Bézout
  have h_Ni_inv : (Ni i : ℤ) * x i ≡ 1 [ZMOD n i] := by
  -- Prove coprimality directly
    have h_coprime_Ni : Nat.Coprime (Ni i) (n i) := by
      -- Use the fact that gcd(Ni i, n i) divides gcd(N, n i) = n i
      -- and also divides Ni i = N / n i
      -- Since n i divides N and Ni i * n i = N, we have gcd(Ni i, n i) = 1
      have h_Ni_mul : Ni i * n i = N := by
        exact Nat.div_mul_cancel (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) 

      -- Any common divisor of Ni i and n i must divide N
      -- But n i is coprime to all other n j
      -- and Ni i is the product of all n j except n i
      apply Nat.coprime_of_dvd
      intro d hd_prime hd_Ni hd_ni
      -- d divides both Ni i and n i
      -- d is prime and divides n i
      -- If d divides Ni i = ∏ (j ≠ i) n j, then d divides some n j with j ≠ i
      have : ∃ j : Fin k, j ≠ i ∧ d ∣ n j := by
        sorry
      obtain ⟨j, hj_ne, hd_nj⟩ := this
      -- But n i and n j are coprime, contradiction
      have h_cop := h_coprime i j hj_ne.symm
      have : d ∣ Nat.gcd (n i) (n j) := Nat.dvd_gcd hd_ni hd_nj
      rw [h_cop.gcd_eq_one] at this
      exact Nat.Prime.not_dvd_one hd_prime this

    -- Bezout's identity
    have h_bezout : (x i) * (Ni i : ℤ) + Int.gcdB (Ni i : ℤ) (n i : ℤ) * (n i : ℤ) = 1 := by
      have := Int.gcd_eq_gcd_ab (Ni i : ℤ) (n i : ℤ)
      simp only [Int.coe_nat_gcd, Nat.Coprime.gcd_eq_one h_coprime_Ni, Int.ofNat_one] at this
      ring_nf at this ⊢
      linarith

    -- Complete the modular arithmetic proof
    have h_eq : (Ni i : ℤ) * x i = -(Int.gcdB (Ni i : ℤ) (n i : ℤ) * (n i : ℤ)) + 1 := by
      linarith
    rw [h_eq]
    have : -(Int.gcdB ↑(Ni i) ↑(n i) * ↑(n i)) + 1 ≡ 1 [ZMOD ↑(n i)] :=
      sorry
    exact this
    -- Ni i and n i are coprime because Ni i is the product of all n j where j ≠ i


  calc
    xans ≡ a i * ↑(Ni i) * x i [ZMOD n i] := by
      -- First show that each term is congruent to the appropriate value
      have h_term_equiv : ∀ j : Fin k,
          a j * ↑(Ni j) * x j ≡ (if j = i then a i * ↑(Ni i) * x i else 0) [ZMOD n i] := by
        intro j
        by_cases hji : j = i
        · -- Case j = i: use reflexivity
          subst hji
          simp
        · -- Case j ≠ i: use h_Ni_zero (note: h_Ni_zero expects i ≠ j, so we use Ne.symm)
          simp only [hji, ite_false]
          have : (Ni j : ℤ) ≡ 0 [ZMOD n i] := h_Ni_zero j (Ne.symm hji)
          show a j * ↑(Ni j) * x j ≡ 0 [ZMOD n i]
          calc
            a j * ↑(Ni j) * x j ≡ a j * 0 * x j [ZMOD n i] := by rel[this]
            _ = 0 := by ring
      -- Now use this to show the sums are congruent
      change (∑ j : Fin k, a j * ↑(Ni j) * x j) ≡ a i * ↑(Ni i) * x i [ZMOD n i]
      rw [Int.modEq_comm, Int.modEq_iff_dvd]
      have h_sum_eq : ∑ j : Fin k, (if j = i then a i * ↑(Ni i) * x i else 0) = a i * ↑(Ni i) * x i := by
        rw [Finset.sum_ite_eq' Finset.univ i]
        simp [Finset.mem_univ]
      rw [← h_sum_eq]
      rw [← Finset.sum_sub_distrib]
      apply Finset.dvd_sum
      intro j _
      -- Each term in the difference is divisible by n i
      have := h_term_equiv j
      rw [Int.modEq_comm, Int.modEq_iff_dvd] at this
      exact this
    _ ≡ a i * 1 [ZMOD n i] := by
      rw [mul_assoc]
      exact Int.ModEq.mul_left _ h_Ni_inv
    _ = a i := by ring
