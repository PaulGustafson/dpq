# Dependently Typed Proto-Quipper (Proto-Quipper-D)




Installation
============


1. Set the environment variable DPQ to the dpq project directory.
E.g. add `export DPQ=<path-to-dpq-directory>` to your `.bashrc` file.


2. Install via stack: `stack install`. Please see [here](https://docs.haskellstack.org/en/stable/README/#how-to-install) for instructions on installing stack. We recommend using stack.   


2. Or install via cabal (>= 3.0.0.0):

   `cabal v1-sandbox init`

   `cabal v1-install --only-dependencies`

   `cabal v1-build`

3. Once 2 is done, you should have two executables, i.e., `dpq` and `dpqi` somewhere in
   you computer. Add `<path-to-dpqi>, <path-to-dpq>` to your `PATH` variable. 


4. Optional: if you are an emacs user, you may want to add the following to your `.emacs` file

   ```
   (load "<path>/dpq-mode.el")

   (require 'dpq-mode)
   ```
   You should now be able to use `C-c C-l` to type check your dpq file.

5. Test your installation. Just type `dpqi` in the terminal to invoke
   the interpretor. In the dpqi interpretor, type `:h` to see a list of options.  





Upgrade dpq
===========
Assuming you have managed to install dpqi and dpq. run `git pull` first, then redo the second
step in the installation guide.

Using dpq executable
===========
In command line, run `dpq` to see further instructions. 

Syntax and examples
=================
see the `lib/` and `test/` directory for syntax and examples.

FAQ
=========
1. Why `export DPQ="~/dpq"` does not work?

   The '\~' symbol in double quotes will not get expanded, so if the dpq installation
   directory is under you home directory, you may want to use `export DPQ=~/dpq` instead.

2. How does the `import` work? Can I try `import "~/lib/Prelude.dpq"` ?

   The importing mechanism we implemented is not very polished. When you want
   to import another dpq file, you can either use the absolute path, or
   a relative path relative to the DPQ environment variable. For example,
   `import "lib/Prelude.dpq"` will import the file at `$DPQ/lib/Prelude.dpq`.
   On the other hand, `import "/home/username/lib/Prelude.dpq"` will import the file at
   `/home/username/lib/Prelude.dpq`.

3. Why `C-c C-l` does not work for my emacs?

   One possible reason is that you forget to restart emacs if you just modified your
   `.emacs` file, or restart the terminal if you just modified your `.bashrc` file. 