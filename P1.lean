namespace Pranav
def dist(v t : Nat): Nat := v*t
def mom(m v : Nat) : Nat := m*v

theorem dist_zero_time (v : Nat) :
dist v 0 = 0 := by simp[dist]

theorem mom_zero_velocity (m : Nat) :
mom m 0 = 0 := by simp[mom]

theorem dist_comm (v t: Nat):
dist v t = dist t v := by
simp[dist]
rw[Nat.mul_comm]
