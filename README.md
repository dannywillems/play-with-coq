## Play with Coq

```
opam switch create ./ 4.14.2 --no-install
opam install coq -y
```

To use Coq in an interactive environment, use `coqtop`.

To use Coq in VScode: `opam install coq-lsp vscoq-language-server`
Compile using `dune build`.

## References

- [coq in a hurry](https://cel.hal.science/inria-00001173)
- [Coq en Coq](http://pauillac.inria.fr/~barras/coq_work-eng.html)
- [Reference Manual](https://coq.inria.fr/doc/V8.20.0/refman/)
