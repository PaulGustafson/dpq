# Dependently Typed Proto-Quipper (DPQ)




To build dpqi
============
Set the environment variable DPQ to the dpq directory.
e.g. add `export DPQ=<path-to-dpq-directory>` to your `.bashrc` file.

Via stack.
---------
`stack install`

Via cabal.
---------
TODO: I have yet to figure out how cabal 3.0 works.


For your convenient
====================
You may want to add `<path-to-dpqi>` to your `PATH` variable. 


To use dpq-mode and run dpqi
============
add the following to your `.emacs` file
```
(load "<path>/dpq-mode.el")

(require 'dpq-mode)
```
You should now be able to use `C-c C-l` to type check your dpq file.


Syntax and examples
=================
see the `lib/` and `test/` directory for syntax and examples.

FAQ
=========
1. Why `export DPQ="~/dpq"` does not work?

   The '~' symbol in double quotes will not get expanded, so if the dpq installation
   directory is under you home directory, you may want to use `export DPQ=~/dpq` instead.

2. How does the `import` work? Can I try `import "~/lib/Prelude.dpq"` ?

   The importing mechanism we implemented is not very polished. When you want
   to import another dpq file, you can either use the absolute path, or
   a relative path relative to the DPQ environment variable. For example,
   `import "lib/Prelude.dpq"` will import the file at `$DPQ/lib/Prelude.dpq`.
   On the other hand, `import "/home/username/lib/Prelude.dpq"` will import the file at
   `/home/username/lib/Prelude.dpq`.
