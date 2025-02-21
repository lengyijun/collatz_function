# collatz_function

We propose a 9-state, 2-symbol turing machine, which simulates the iteration of the Collatz 3x + 1 function.

We verify this behaviour in lean4.

## Represtation

0 is default symbol on tape.

A B C D E F G H J  are 9 states.

- 4 states (A, B, C, D) for 2 pointers: check even or odd
    - 2 states (E, F) for even cases
    - 3 states (G, H, J) for odd cases

`000 (1F)1^n 000` denotes (n+1)

`000 (0F)    000` denotes 0

let b = (collatz (n+1)) - 1

`000 (1F)1^n 000` -> `000 (1F)1^b 000`

## Comparsion to previous results

See [pdf](./table.pdf)

## Main result

CollatzFunction/NonHalt/Main.lean

```
# verify all theorems
lake build
```

## Run simulator

```
# NonHalt
lake exe Sim9 21

# Halt
lake exe Sim10 21
```

Or copy tm_yaml/9_non_halting.yaml to https://turingmachine.io

```
lake exe SearchUnvisitedBranch
lake exe SearchUnvisitedBranch10
```

## Motivation

When reading [^Mi2014], I notice [^Bai1998] is lost. So I want to reproduce the lost 10*2 and 2*8 turing machine.

I spent one morning to design and got a better turing machine (9*2).

I know noboby will ever verify the behaviour by hand, so I spend 24 hours to verify everything in lean4.

## Open question

Reproduce the 2-state, 8-symbol machine in [^Bai1998].


[^Bai1998]: C. Baiocchi, 3N+1, UTM e Tag-systems (Italian), Dipartimento di Matematica dell’Università “La Sapienza” di Roma 98/38, 1998.
[^Mi2014]: https://arxiv.org/abs/1409.7322
