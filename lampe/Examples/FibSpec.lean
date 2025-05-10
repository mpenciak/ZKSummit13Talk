import Lampe
import Examples.Extracted

open Lampe

variable {p : Prime}

def fib : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => fib (n + 1) + fib n

namespace Spec

def fib (p) (N : U 32) : Fp p :=
  _root_.fib N.toNat

@[simp]
lemma fib_induction (i : U 32) (hhi : i < (2 ^ 32 : Nat) - 2)
    : Spec.fib p (i + 2) = Spec.fib _ (i + 1) + Spec.fib _ i := by
  simp only [Spec.fib, fib]
  repeat rw [BitVec.toNat_add]
  simp
  have h2 : i.toNat + 2 < 4294967296 := by
    have : i.toNat < 2 ^32 - 2 := by change i < (2 ^ 32 : Nat) - 2; assumption
    omega
  have h1 : i.toNat + 1 < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h1]
  simp [_root_.fib]

theorem fib_spec {N : U 32} (h : N < (2 ^ 32 : Nat) - 2) :
    STHoare p Extracted.env ⟦⟧ (Extracted.fib.call h![N] h![])
      fun output => output = fib p N := by
  enter_decl
  steps
  loop_inv fun i _ _ => ([a ↦ ⟨Tp.field, fib p i⟩] ⋆ [b ↦ ⟨Tp.field, fib p (i + 1)⟩])
  · change 0 ≤ N; bv_decide
  · intros i _ _
    steps
    · intros
      congr
      simp_all
    · congr
      simp_all
      rw [add_comm]
      calc fib p (i + 1) + fib p i = fib p (i + 2) := by rw [fib_induction (p := p) i (by bv_decide)]
        _ = fib p (i + (1 + 1)) := by rfl
        _ = fib p (i + 1 + 1) := by rw [BitVec.add_assoc]
  · steps
    subst_vars
    rfl

