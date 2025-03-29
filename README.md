# AMM Model Checker

### Requirements:

* cabal
* haskell (tested with compiler version: ghc 9.6.1 & 9.10.1)
* Z3: https://github.com/Z3Prover/z3

### building project:

```
cabal build
```

### using tool:
```
cabal run amm-check < [input_file]
```

see examples folder for example queries. 

### clean up again:

```
cabal clean
```
