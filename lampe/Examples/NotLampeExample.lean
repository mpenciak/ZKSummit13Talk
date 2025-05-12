namespace hidden

inductive Nat
  | zero : Nat
  | succ : Nat → Nat

def Nat.add : Nat → Nat → Nat
  | zero, y => y
  | succ x, y => succ (Nat.add x y)

infixl:65 " + " => Nat.add

theorem Nat.add_zero : ∀ (x : Nat), x + Nat.zero = x := by
  intro x
  induction x with
  | zero => rfl
  | succ x ih => simp [Nat.add, ih]

theorem Nat.add_succ : ∀ (x y : Nat), x + y.succ = (x + y).succ := by
  intro x y
  induction x with
  | zero => rfl
  | succ x ih => simp [Nat.add, ih]

theorem Nat.add_comm : ∀ (x y : Nat), x + y = y + x := by
  intro x y
  induction x with
  | zero => simp [Nat.add, Nat.add_zero]
  | succ x ih =>
    have : y + x = x + y := ih.symm
    simp [Nat.add, this, Nat.add_succ]
