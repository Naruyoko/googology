import Mathlib.Data.List.Intervals

def finIco {k : ℕ} (m n : Fin (k + 1)) : List (Fin k) :=
  (List.Ico m n).pmap Fin.mk fun _ h =>
    Nat.lt_of_lt_of_le (List.Ico.mem.mp h).right (Nat.le_of_lt_succ n.isLt)

#reduce finIco (k := 3) 0 2
#reduce finIco (k := 3) 1 3
#reduce finIco (k := 3) 2 2
#reduce finIco (k := 3) 3 2
#reduce finIco (k := 3) 1 (Fin.last _)
-- #reduce finIco (k := 100) 3 100
