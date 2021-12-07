-- #1
def sum_to_sqr : ℕ → ℕ 
| (nat.zero)    := nat.zero 
| (nat.succ n')  := (sum_to_sqr n') + (n'.succ * n'.succ)

def P : ℕ → Prop :=
  λ n, 6 * sum_to_sqr n = n * (1 + n) * (1 + 2 * n)

def conjecture_sts := ∀ n, P n

theorem sum_to_sqr_opt : conjecture_sts :=
begin
  unfold conjecture_sts,
  assume n,
  unfold P,

  induction n with n' ih_n',
  
  apply rfl,

  simp [sum_to_sqr],
  rw mul_add,

  rw ih_n',
  rw nat.succ_eq_add_one,
  ring,
end

-- #2
-- 2.10

-- 2.11

-- 2.12

-- 2.13

-- #3
def fib : ℕ → ℕ
| 0 := 0
| 1 := 1
| (n + 2) := fib n + fib (n + 1)

def P : ℕ → Prop :=
  λ n, (fib n.succ) ^ 2 - (fib n.succ.succ) * (fib n) = (-1) ^ n