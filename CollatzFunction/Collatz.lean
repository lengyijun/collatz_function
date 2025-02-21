def collatz (n : Nat) : Nat :=
if n % 2 = 0 then
  n/2
else
  n + (n+1)/2
