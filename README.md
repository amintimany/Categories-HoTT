# README #

This is an implementation of category theory in Coq.

This branch is being **migrated** to HoTT/Coq.
Many files still **don't** compile.

The file ```ToDo.txt``` mentions the parts that still need work in the files that do compile.

## Coq version and compilation ##

* It has been tested on Debian with HoTT/Coq on top of Coq8.5-beta2
* To compile simply type
    * ``` ./configure ``` to produce the Makefile [1] and then
    * ``` make ``` to compile

[1] you will need to have coq_makefile to be on the path