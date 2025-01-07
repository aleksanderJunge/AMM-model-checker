# AMM Model Checker

### Requirements:

* cabal
* haskell (tested with compiler version: ghc 9.6.1)

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

### dependencies:
```
cabal new-install --lib split
```