# collatz_function

This repo propose two non-halting turing machines which simulates the iteration of the Collatz 3x + 1 function.

Both of them are better than preivous results.

9-state, 2-symbol turing machine in branch [9](https://github.com/lengyijun/collatz_function/tree/9_10) 
- Not maintained any more
- The tape is cleaner: useless 1 will be zeroed again
- calculate collatz n, n >= 1

8-state, 2-symbol turing machine in branch [8](https://github.com/lengyijun/collatz_function/tree/8_9) 
- Optimized based on preivous one
- The tape is dirty: useless 1 will not be zeroed
- calculate collatz n, n >= 0

We verify their behaviour in lean4.

## Motivation

When reading [^Mi2014], I notice [^Bai1998] is lost. So I want to reproduce the lost `10*2` and `2*8` turing machine.

I spent one morning to design and got a better turing machine (9*2).

I know noboby will ever verify the behaviour by hand, so I spend 24 hours to verify everything in lean4.

Several days later, when research `2*8` turing machine, I find some techiques and apply it to `9*2`, got `8*2` turing machine.

## Design

This `8*2` turing machine is bases on `9*2` turing machine in branch `9_10`

In `9*2` turing machine, we notice that the input is always cut into two halves: the left half is always abandoned.

If input is even, the left half is abandoned directly.

If input is odd, the left half is appended to both ends of right half.

In `9*2` turing machine, state E and F are used to zeroing the left half.

Actually, we don't need to zero the left half: write one zero is enough to make the boundary.


## Open question

- Reproduce the 2-state, 8-symbol machine in [^Bai1998].
- Is 7 states enough ?


[^Bai1998]: C. Baiocchi, 3N+1, UTM e Tag-systems (Italian), Dipartimento di Matematica dell’Università “La Sapienza” di Roma 98/38, 1998.
[^Mi2014]: https://arxiv.org/abs/1409.7322
