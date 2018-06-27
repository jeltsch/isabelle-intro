Introduction
============

This is some code that I used for an introduction to Isabelle/HOL in
summer 2018.


Building
========

When looking at the source code outside some Isabelle IDE, you will not
see all the non-ASCII symbols but only encodings of them. However, it is
possible to turn the source code into a PDF file that gives you a
properly rendered presentation of the code.

Running `make` builds this PDF file and places it in
`$ISABELLE_BROWSER_INFO/Wolfgang Jeltsch/Isabelle_Intro/document.pdf`.
You can find out the value of `$ISABELLE_BROWSER_INFO` by running the
following command:

    isabelle getenv ISABELLE_BROWSER_INFO
