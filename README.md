# collatz_function

We propose a 8-state, 2-symbol turing machine, which simulates the iteration of the Collatz 3x + 1 function.

This turing machine never halt.

We verify this behaviour in lean4.

## Represtation

symbols: 0 1

0 is default symbol on tape.

A B C D E G H J  are 8 states.

- 4 states (A, B, C, D) for 2 pointers: check even or odd
    - 1 states (E) for even cases
    - 3 states (G, H, J) for odd cases

`V 0(0G)  000` denotes 0, V is arbitrary list

`V 0(0G)1^n 000` denotes n, V is arbitrary list

let b = collatz n

`V 0(0G)1^n 000` -> `W 0(0G)1^b 000` , V W are arbitrary list

## Comparsion to previous results

See [pdf](./table.pdf)

## Main result

CollatzFunction/Tm8/Main.lean

```
# verify all theorems
lake build
```

## Run simulator

```
# NonHalt
lake exe Sim8 21
```

```
lake exe SearchUnvisitedBranch
lake exe Yaml
lake exe Latex
```

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
