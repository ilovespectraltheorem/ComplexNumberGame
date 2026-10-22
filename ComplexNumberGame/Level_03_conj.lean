/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
-- Thanks: Imperial College London, leanprover-community

-- import levels 1 and 2
import ComplexNumberGame.Level_02_I

/-! # Level 3: Complex conjugation -/

namespace Complex

-- First complete the definition using `Complex.mk` or `⟨x, y⟩` notation

/-- The complex conjugate of a complex number -/
def conj (z : ℂ) : ℂ := Complex.mk z.re (-z).im

-- Now prove how it interacts with everything else

/-! ## Real and imaginary parts -/

@[simp] lemma conj_re (z : ℂ) : re (conj z) = re z := rfl
@[simp] lemma conj_im (z : ℂ) : im (conj z) = -im z := rfl

/-! ## Behaviour with respect to 0, 1 and I -/

@[simp] lemma conj_zero : conj 0 = 0 := by
  ext
  simp
  simp

@[simp] lemma conj_one : conj 1 = 1 := by
  ext
  simp
  simp

@[simp] lemma conj_I : conj I = -I := by
  ext
  simp
  simp
@[simp] lemma conj_neg_I : conj (-I) = I := by
  ext
  simp
  simp
/-! ## Behaviour with respect to +, - and * -/

@[simp] lemma conj_add (z w : ℂ) : conj (z + w) = conj z + conj w := by
  ext
  simp
  rw [conj_im]
  simp
  rw [add_comm]


@[simp] lemma conj_neg (z : ℂ) : conj (-z) = -conj z := by
  ext
  simp
  simp


@[simp] lemma conj_mul (z w : ℂ) : conj (z * w) = conj z * conj w := by
  ext
  simp
  simp
  ring

/-! ## Behaviour with respect to real numbers -/

@[simp] lemma conj_ofReal (r : ℝ) : conj r = r := by
  ext
  norm_cast
  norm_cast
  simp

lemma im_eq_zero_of_eq_conj {z : ℂ} : conj z = z → im z = 0 := by
  intro h
  rw [ext_iff] at h
  rcases h with ⟨hre, him⟩
  simp at him
  linarith

lemma eq_conj_iff_real {z : ℂ} : conj z = z ↔ ∃ r : ℝ, z = r := by
  constructor
  · intro h
    use z.re
    apply im_eq_zero_of_eq_conj at h
    ext
    simp
    simp
    exact h
  · intro h
    rcases h with ⟨r, hr⟩
    rw[hr]
    simp


lemma eq_conj_iff_re {z : ℂ} : conj z = z ↔ (z.re : ℂ) = z := by
  constructor
  intro h
  ext
  simp
  apply im_eq_zero_of_eq_conj at h
  simp
  symm
  exact h
  intro h
  apply eq_conj_iff_real.mpr
  use z.re
  simp_all

theorem add_conj (z : ℂ) : z + conj z = (2 * z.re : ℝ) := by
  ext
  simp
  rw[← one_add_one_eq_two]
  simp
  ring
  simp
  left
  rw[← one_add_one_eq_two]
  simp

/-! ## Properties of the `conj` map -/

@[simp] lemma conj_conj (z : ℂ) : conj (conj z) = z := by
  ext
  simp
  simp

lemma conj_inj {z w : ℂ} : conj z = conj w ↔ z = w := by
  constructor
  intro h
  ext
  rw[ext_iff] at h
  rcases h with ⟨hre, him⟩
  simp at hre
  exact hre
  rw[ext_iff] at h
  rcases h with ⟨hre, him⟩
  simp at him
  exact him
  intro h
  ext
  rw[conj_re, conj_re]
  rw[ext_iff] at h
  rcases h with ⟨hre, him⟩
  exact hre
  rw[ext_iff] at h
  rcases h with ⟨hre, him⟩
  rw[conj_im, conj_im]
  simp
  exact him

@[simp] lemma conj_eq_zero {z : ℂ} : conj z = 0 ↔ z = 0 := by
  constructor
  intro h
  rw[ext_iff] at h
  rcases h with ⟨hre, him⟩
  simp at hre
  simp at him
  ext
  simp
  exact hre
  simp
  exact him
  intro h
  ext
  simp
  rw[ext_iff] at h
  rcases h with ⟨hre, him⟩
  simp at hre
  exact hre
  simp
  rw[ext_iff] at h
  rcases h with ⟨hre, him⟩
  simp at him
  exact him
/-

A ring homomorphism in Lean is the following collection
of data: a map, and the proof that it commutes with
the ring structures in the obvious way. Here we observe
that the work we've done is enough to define the
ring homomorphism complex conjugation.

-/

/-- the ring homomorphism complex conjugation -/
def conjHom : ℂ →+* ℂ where
  toFun := conj
  map_zero' := conj_zero
  map_one' := conj_one
  map_add' := conj_add
  map_mul' := conj_mul

-- Two optional lemmas which computer scientists like,
-- giving us easy access to some basic properties
-- of conj

open Function

lemma conj_involutive : Involutive conj := by
  intro h
  rw[conj_conj]

lemma conj_bijective : Bijective conj := by
  constructor
  intro z w h
  rw [conj_inj] at h
  exact h
  intro z
  use z.conj
  rw[conj_conj]

end Complex
