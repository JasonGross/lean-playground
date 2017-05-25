set_option profiler true
def some_lets : ℕ → ℕ → ℕ
| 0            v := v
| (nat.succ n) v := let k := some_lets n v + some_lets n v in some_lets n k

def some_unfolded_lets (n : ℕ) : ∃ v : ℕ , v = some_lets 5 n :=
begin
  unfold some_lets; constructor; constructor
end

#print some_unfolded_lets
