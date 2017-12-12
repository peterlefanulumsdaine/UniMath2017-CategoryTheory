UniMath2017-CategoryTheory
============

Category theory group projects at UniMath workshop, Birmingham, Dec 2017


Compilation
------------

### Prerequisites

The Coq code depends on the UniMath library, available from http://github.com/UniMath/UniMath, and the UniMath/TypeTheory library, http://github.com/UniMath/TypeTheory

To compile these, follow the installation instructions given for those libraries, including `make install` to install the compiled `.vo` files into the `user-contrib` directory of UniMath’s Coq.

You will also need to make UniMath’s Coq available for working on this library.  The simplest way is to install it globally as the default Coq on your system, by adding its location to your `$PATH`.  To do this for just your current session, navigate to your copy of the UniMath repository, and call
```
$ PATH=$PATH:`pwd`/sub/coq/bin/
```
or to make it persistent, modify your shell configuration file (usually `~/.bash_profile` or similar) by calling
```
echo "export PATH=\"`pwd`/sub/coq/bin/:\$PATH\"" >> ~/.bash_profile
```

Alternatively, if you do not want to make UniMath’s Coq your default, you can add an alias for its directory to your shell config file by calling (from within the UniMath toplevel directory)
```
echo "export UNIBIN=\"`pwd`/sub/coq/bin/\"" >> ~/.bash_profile
```

### Compilation of the current library.

If you have UniMath’s Coq installed in your `$PATH` (as per the first suggestion above), then our library can be built just with `make` from within the toplevel directory of the repository.

Otherwise, you need to pass the location of the UniMath `coqc` binary by hand, as e.g. `make COQBIN="~/src/UniMath/sub/coq/bin/"`, or `make COQBIN=$UNIBIN` if you have added an alias as suggested above.

To install these files in `user-contrib` for further import in other libraries, issue `make install` (again, specifying `COQBIN` if necessary).

Similarly, to use these files in Proof General, you must make sure the correct `coqtop` is called.  If UniMath’s Coq is installed globally, this will be automatic.  Otherwise, it may be either permanently set in the option `coq-prog-name`, or prompted for at each invocation by setting `proof-prog-name-ask` to true in the Proof General customisation options.

# Group members:

- Peter LeFanu Lumsdaine
- Tim Baumann
- Brandon Doherty
- Cory Knapp
- Tamara von Glehn
- Noam Zeilberger
- Jonathan Weinberger
- Chaitanya Leena Subramaniam
