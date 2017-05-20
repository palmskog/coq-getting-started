Interfaces for Coq
==================

There are two primary Coq interface alternatives: CoqIDE and ProofGeneral via emacs.

First, make sure a stable version of Coq is installed; the current stable version is 8.6. It is usually a good idea to lock OPAM  to that version to avoid surprises while upgrading:

```
$ opam pin add coq 8.6
```

Then, to get access to various Coq-related OPAM packages, run the following:
```
$ opam repo add coq-released http://coq.inria.fr/opam/released
```


Installing and Running CoqIDE
-----------------------------

CoqIDE is a graphical editor for Coq written in OCaml by the Coq team. See https://coq.inria.fr/refman/Reference-Manual018.html

The OPAM package for CoqIDE (`coqide`), depends on the OPAM package for the OCaml GTK interface, `lablgtk`. In turn, `lablgtk` requires 

In Ubuntu or Debian:

```
$ sudo apt-get install libgtksourceview2.0-dev
$ opam install coqide
```

Now, to edit a Coq file `Alternate.v` in CoqIDE, simply run
```
$ coqide Alternate.v
```

Installing and Using ProofGeneral
---------------------------------

ProofGeneral is an emacs extension that adds an emacs mode for Coq files and facilities for communicating with a Coq backend. See https://proofgeneral.github.io

First, make sure emacs is installed and the directory `~/.emacs.d/lisp` exists. Then run:
```
$ git clone https://github.com/ProofGeneral/PG ~/.emacs.d/lisp/PG
$ cd ~/.emacs.d/lisp/PG
$ make
```

Then add the following to your `.emacs`:
```
;; Open .v files with Proof General's Coq mode
(load "~/.emacs.d/lisp/PG/generic/proof-site")
```

ProofGeneral has various options that can be set in `.emacs` via `custom-set-variables`. The following options are recommended:

```
(custom-set-variables
 '(coq-token-symbol-map (quote (("~>" "⤳") ("~" "¬") ("Qed" "∎") ("::" "∷") ("forall" "∀") ("exists" "∃") ("false" "false" bold sans) ("true" "true" bold sans) ("False" "⊥") ("True" "⊤") ("<=" "≤") (">=" "≥") ("=>" "⇒") ("->" "→") ("<-" "←") ("<->" "↔") ("++" "⧺") ("<<" "《") (">>" "》") ("===" "≡") (":=" "≔") ("|-" "⊢") ("<>" "≠") ("-|" "⊣") ("\\/" "∨") ("/\\" "∧") ("============================" "⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯" bold tactical))))
 '(coq-unicode-tokens-enable t)
 '(proof-splash-enable nil)
 '(proof-strict-read-only t)
)
```
