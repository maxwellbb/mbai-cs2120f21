import algebra.algebra.basic tactic.ring

namespace hidden

inductive nat : Type
| zero : nat
| succ (n' : nat) : nat

def z := nat.zero

#check z
#reduce z

def o := nat.succ z
def t := nat.succ o

def f : nat :=
begin
  exact nat.succ (nat.succ t),
end

#check o
#reduce o

def inc' : nat → nat :=
begin
  assume n,
  exact nat.succ n,
end

def inc : nat → nat
| n := nat.succ n

#reduce inc f

def dec : nat → nat
| (nat.zero) := nat.zero
| (nat.succ n') := n'

def add : nat → nat → nat
| (nat.zero) (m) := m
| (nat.succ n') (m) := nat.succ (add n' m)

def mul : nat → nat → nat
| (nat.zero) (m) := nat.zero
| (nat.succ n') (m) := add (m) (mul n' m)

def sum_to :nat → nat
| (nat.zero) := nat.zero
| (nat.succ n') := add (sum_to n') (nat.succ n')

#reduce sum_to nat.zero.succ.succ.succ.succ

#reduce mul f f
#reduce add f f

end hidden

def P : nat → Prop
| n := hidden.sum_to n = n * (n + 1)