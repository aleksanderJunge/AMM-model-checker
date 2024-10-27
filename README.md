# Liquidity saving mechanism for AMMs inspired by netting

### Requirements:

* cabal
* haskell (tested with compiler version: ghc 9.6.1)
  

### building project:

```

cabal build

```

### to run the examples from the paper (as tests):

```
cabal run test:tests
```

This will output a short log displaying the trace of transactions from the example, and in the case of an error the expected vs. actual final configuration.

### clean up again:

```
cabal clean
```
