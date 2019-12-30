# Dependently Typed Proto-Quipper (DPQ)




Installation
============

1. Set the environment variable DPQ.
-------
Set the environment variable DPQ to the dpq project directory.
e.g. add `export DPQ=<path-to-dpq-directory>` to your `.bashrc` file.

2.1 Install via stack.
---------
`stack install`

2.2 Or, Install via cabal (>= 3.0.0.0).
---------
`cabal v1-sandbox init`

`cabal v1-install --only-dependencies`

`cabal v1-build`


3. Set the environment variable PATH
-------------------
Add `<path-to-dpqi>` to your `PATH` variable. 


4. Enable dpq-mode in emacs
----------------------------
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
