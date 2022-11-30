Ref:
- https://github.com/ralexstokes/kzg
- https://github.com/dusk-network/plonk

Implemented:
- [X] Single polynomial commit and single point opening.
- [X] Fast Fourier Transform and its inverse.
- [X] Optimized version for batch-evaluate, multiply, zerofier and interpolate
- [X] Single polynomial and multiple points opening.

Run:
```
git submodule init
git submodule update
cargo test
```
