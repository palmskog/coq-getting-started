OPAM Installation and Configuration
===================================

OPAM is a package manager for OCaml and Coq.

OPAM (version 1.2) allows having several versions of Coq (and Coq packages) installed simultaneously. One can even have several instances of the same version of packages and switch between them at will.

General OPAM installation instructions: https://opam.ocaml.org/doc/Install.html

To install on Ubuntu Trusty and Precise:

```
$ add-apt-repository ppa:avsm/ppa
$ apt-get update
$ apt-get install ocaml ocaml-native-compilers camlp4-extra opam
```

Be sure to also install a dependency solver such as `aspcud`.

After installation, OPAM must be initialized for the current user:

```
$ opam init
```

After this is done, make sure to run the following command in the shell:

```
$ eval `opam config env`
```
